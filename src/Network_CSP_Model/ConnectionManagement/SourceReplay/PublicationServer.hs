{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- Actual Server/IG/CM/handler; single synthetic accept and injected failures.
module Main where

import Control.Concurrent (ThreadId)
import Control.Concurrent.Class.MonadSTM.Strict
import Control.Exception (throw)
import Control.Monad (unless, when)
import Control.Monad.Class.MonadAsync
import Control.Monad.Class.MonadFork (myThreadId, throwTo)
import Control.Monad.Class.MonadThrow
import Control.Monad.Class.MonadTimer.SI (threadDelay, timeout)
import Control.Tracer (mkTracer, nullTracer)
import qualified Data.ByteString.Lazy as BL
import Data.List (nub)
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.Map.Strict as Map
import Data.Proxy (Proxy (..))
import GHC.Conc (ThreadStatus (..), BlockReason (BlockedOnSTM), threadStatus)
import System.Random (mkStdGen)
import qualified Network.Mux as Mx
import Network.Mux.Bearer (MakeBearer (..), makeQueueChannelBearer)
import Network.Mux.Bearer.Queues (QueueChannel (..))
import qualified Network.Mux.Trace as Trace
import qualified Ouroboros.Network.ConnectionHandler as H
import Ouroboros.Network.ConnectionId (ConnectionId (..))
import qualified Ouroboros.Network.ConnectionManager.Core as Core
import qualified Ouroboros.Network.ConnectionManager.ConnMap as ConnMap
import qualified Ouroboros.Network.ConnectionManager.State as State
import qualified Ouroboros.Network.ConnectionManager.Types as CM
import Ouroboros.Network.Context (ResponderContext)
import qualified Ouroboros.Network.InboundGovernor as IG
import Ouroboros.Network.InboundGovernor.InformationChannel (newInformationChannel)
import Ouroboros.Network.Mux
import Ouroboros.Network.MuxMode (InResponderMode (..), WithMuxMode (..))
import Ouroboros.Network.Protocol.Handshake hiding (Accept)
import Ouroboros.Network.Protocol.Handshake.Unversioned
import qualified Ouroboros.Network.Server as Server
import Ouroboros.Network.Server.RateLimiting (AcceptedConnectionsLimit (..))
import Ouroboros.Network.Snocket (Snocket (..), Accept (..), Accepted (..), TestAddress (..), AddressFamily (TestFamily))

data Socket = Listening | Connection (QueueChannel IO)
data Site = SuccessTrace | NewMuxTrace | Allocation | SuccessAsync | NewMuxAsync | EarlyPayload
  deriving (Eq, Show)
data Fault = Injected deriving (Eq, Show)
instance Exception Fault

type Addr = TestAddress Int
type App = OuroborosBundle Mx.InitiatorResponderMode () (ResponderContext Addr) BL.ByteString IO () ()
type Handle = H.Handle Mx.InitiatorResponderMode () (ResponderContext Addr) UnversionedProtocolData BL.ByteString IO () ()
type HandlerFn = CM.ConnectionHandlerFn
  (H.ConnectionHandlerTrace UnversionedProtocol UnversionedProtocolData)
  Socket Addr Handle (H.HandlerError UnversionedProtocol) UnversionedProtocol UnversionedProtocolData IO

arguments :: HandshakeArguments (ConnectionId Addr) UnversionedProtocol UnversionedProtocolData IO
arguments = HandshakeArguments nullTracer nullTracer unversionedHandshakeCodec
  unversionedProtocolDataCodec acceptableVersion queryVersion timeLimitsHandshake

decorate :: StrictTVar IO [Bool] -> StrictTVar IO Int -> StrictTVar IO (Maybe ThreadId) -> HandlerFn -> HandlerFn
decorate writes forces handlerId fn update socket writer tracer conn bearer buffer = CM.MaskedAction $ \unmask -> do
  tid <- myThreadId
  atomically $ writeTVar handlerId (Just tid)
  let observed = CM.PromiseWriter
        { CM.writePromise = \value -> modifyTVar writes (++ [either (const False) (const True) value]) >> CM.writePromise writer value
        , CM.forcePromise = \value -> modifyTVar forces (+1) >> CM.forcePromise writer value }
  CM.runWithUnmask (fn update socket observed tracer conn bearer buffer) unmask

await :: IO Bool -> IO ()
await ready = ready >>= \done -> unless done (threadDelay 0.001 >> await ready)

-- No original PromiseWriter/Reader is retained by instrumentation. GHC's
-- BlockedIndefinitelyOnSTM/GC recovery is not excluded by this finite probe.
run :: Site -> IO ()
run site = do
  result <- timeout 10 $ do
    q1 <- newTBQueueIO 16
    q2 <- newTBQueueIO 16
    writes <- newTVarIO []
    forces <- newTVarIO 0
    closes <- newTVarIO (0 :: Int)
    listeners <- newTVarIO (0 :: Int)
    handlerId <- newTVarIO Nothing
    counters <- newTVarIO []
    seen <- newTVarIO []
    classified <- newTVarIO False
    tracerEntered <- newEmptyTMVarIO
    let local = QueueChannel q1 q2
        remote = QueueChannel q2 q1
        conn = ConnectionId (TestAddress 0) (TestAddress 1)
        queueBearer = getBearer makeQueueChannelBearer
        bearer = MakeBearer $ \delay socket buffer -> case socket of
          Connection channel -> queueBearer delay channel buffer
          Listening -> throwIO (userError "bearer requested for listener")
        next = Accept (atomically retry)
        socketApi = Snocket
          { getLocalAddr = \_ -> pure (TestAddress 0)
          , getRemoteAddr = \_ -> pure (TestAddress 1)
          , addrFamily = const TestFamily
          , open = \_ -> throwIO (userError "unexpected open")
          , openToConnect = \_ -> throwIO (userError "unexpected outbound open")
          , connect = \_ _ -> throwIO (userError "unexpected connect")
          , bind = \_ _ -> pure ()
          , listen = \_ -> pure ()
          , accept = \_ -> pure $ Accept (pure (Accepted (Connection local) (TestAddress 1), next))
          , close = \socket -> atomically $ case socket of
              Listening -> modifyTVar listeners (+1)
              Connection _ -> modifyTVar closes (+1) }
        note event = atomically $ modifyTVar seen (++ [event])
        blockTracer = do
          masking <- getMaskingState
          unless (masking == MaskedInterruptible) (throwIO (userError "unexpected tracer mask"))
          tid <- myThreadId
          atomically $ putTMVar tracerEntered tid
          atomically retry
        muxTrace = mkTracer $ \(Trace.WithBearer _ event) -> case event of
          Trace.TraceNewMux _ -> do
            note "newMux"
            when (site == NewMuxTrace) (throwIO Injected)
            when (site == NewMuxAsync) blockTracer
          _ -> pure ()
        cmTrace = mkTracer $ \event -> case event of
          Core.TrConnectionHandler _ (H.TrHandshakeSuccess _ _) -> do
            note "success"
            when (site == SuccessTrace) (throwIO Injected)
            when (site == SuccessAsync) blockTracer
          Core.TrConnectionHandler _ (H.TrConnectionHandlerError _ err _) ->
            atomically $ writeTVar classified (fromException err == Just Injected)
          Core.TrConnectionManagerCounters _ -> do
            tid <- myThreadId
            atomically $ modifyTVar counters (++ [tid])
          _ -> pure ()
        app = case site of
          EarlyPayload -> throw Injected
          Allocation -> TemperatureBundle (WithHot [throw Injected]) (WithWarm []) (WithEstablished [])
          _ -> mempty :: App
    parent <- myThreadId
    supply <- atomically $ State.newConnStateIdSupply Proxy
    info <- newInformationChannel
    let limits = AcceptedConnectionsLimit maxBound maxBound 0
        cmArgs = Core.Arguments
          { Core.tracer = cmTrace, Core.trTracer = nullTracer
          , Core.ipv4Address = Nothing, Core.ipv6Address = Nothing
          , Core.addressType = const (Just CM.IPv4Address)
          , Core.snocket = socketApi, Core.makeBearer = bearer
          , Core.withBuffer = \f -> f Nothing, Core.configureSocket = \_ _ -> pure ()
          , Core.timeWaitTimeout = 1, Core.outboundIdleTimeout = 1
          , Core.connectionDataFlow = const CM.Duplex, Core.prunePolicy = CM.simplePrunePolicy
          , Core.stdGen = mkStdGen 0, Core.connectionsLimits = limits
          , Core.updateVersionData = \value _ -> value
          , Core.connStateIdSupply = supply, Core.classifyHandlerError = H.classifyHandlerError }
        makeHandler igTracer =
          let production :: H.MuxConnectionHandler Mx.InitiatorResponderMode Socket () (ResponderContext Addr) Addr
                            UnversionedProtocol UnversionedProtocolData BL.ByteString IO () ()
              production = H.makeConnectionHandler
                (Mx.nullTracers { Mx.tracer = muxTrace }) noBindForkPolicy arguments
                (unversionedProtocol app) (parent, mempty)
                (H.MuxInitiatorResponderConnectionHandler (const CM.Duplex) igTracer)
          in case CM.connectionHandler production of
            WithInitiatorResponderMode outbound inbound -> CM.ConnectionHandler $ WithInitiatorResponderMode
              (decorate writes forces handlerId outbound) (decorate writes forces handlerId inbound)
        igArgs = IG.Arguments
          { IG.transitionTracer = nullTracer, IG.tracer = nullTracer, IG.debugTracer = nullTracer
          , IG.connectionDataFlow = const CM.Duplex, IG.idleTimeout = Nothing, IG.infoChannel = info
          , IG.withConnectionManager = Core.with cmArgs (InResponderMode info)
          , IG.mkConnectionHandler = makeHandler }
        serverArgs = Server.Arguments (Listening :| []) socketApi nullTracer limits igArgs
        remoteBody = do
          rb <- queueBearer 10 remote Nothing
          runHandshakeClient rb conn arguments (unversionedProtocol ())
    withAsync remoteBody $ \remoteThread -> do
      -- Observe the private admission thread through the real CM counter tracer;
      -- Server itself discards the Async handle. No replacement caller is forked.
      callerId <- Server.with serverArgs $ \_ _ cm -> do
        remoteResult <- wait remoteThread
        case remoteResult of
          Right _ -> pure ()
          Left err -> throwIO (userError ("remote handshake failed: " ++ show err))
        when (site `elem` [SuccessAsync, NewMuxAsync]) $ do
          tid <- atomically $ readTMVar tracerEntered
          await $ (== ThreadBlocked BlockedOnSTM) <$> threadStatus tid
          throwTo tid AsyncCancelled
        await $ do
          mhid <- readTVarIO handlerId
          maybe (pure False) (fmap (== ThreadFinished) . threadStatus) mhid
        mhid <- readTVarIO handlerId
        hid <- maybe (throwIO (userError "missing handler")) pure mhid
        await $ do
          tids <- nub . filter (/= hid) <$> readTVarIO counters
          pure (length tids == 1)
        tids <- nub . filter (/= hid) <$> readTVarIO counters
        tid <- case tids of [one] -> pure one; _ -> throwIO (userError "ambiguous admission identity")
        let expected = if site == EarlyPayload then ThreadFinished else ThreadBlocked BlockedOnSTM
        await $ (== expected) <$> threadStatus tid
        states <- atomically $ CM.readState cm
        ws <- readTVarIO writes
        fs <- readTVarIO forces
        cs <- readTVarIO closes
        ls <- readTVarIO listeners
        events <- readTVarIO seen
        classifiedFault <- readTVarIO classified
        counterCount <- length . filter (== tid) <$> readTVarIO counters
        let expectedEvents = case site of
              EarlyPayload -> []
              SuccessTrace -> ["success"]
              SuccessAsync -> ["success"]
              _ -> ["success", "newMux"]
            expectedWrites = if site == EarlyPayload then [False] else []
            expectedClose = if site == EarlyPayload then 2 else 1
        unless (Map.null (ConnMap.getConnMap states) && ws == expectedWrites && fs == 0
                && cs == expectedClose && ls == 0 && events == expectedEvents
                && classifiedFault == (site `notElem` [SuccessAsync, NewMuxAsync])
                && counterCount == (if site == EarlyPayload then 2 else 1))
          (throwIO (userError ("bad open-scope state " ++ show (ws, fs, cs, ls))))
        pure tid
      status <- threadStatus callerId
      ls <- readTVarIO listeners
      cs <- readTVarIO closes
      let expected = if site == EarlyPayload then ThreadFinished else ThreadBlocked BlockedOnSTM
      unless (status == expected && ls == 1 && cs == (if site == EarlyPayload then 2 else 1))
        (throwIO (userError ("bad post-Server state " ++ show (status, ls, cs))))
      putStrLn (show site ++ ": Server.with returned; admission=" ++ show status ++ "; connection/listener closes=" ++ show (cs, ls))
      -- Explicit test cleanup of an unowned worker, after recording the finding.
      -- This is not an action performed by Server.with in the reviewed source.
      when (site /= EarlyPayload) $ do
        throwTo callerId AsyncCancelled
        await $ (== ThreadFinished) <$> threadStatus callerId
  maybe (fail "Server replay timed out") pure result

main :: IO ()
main = mapM_ run [SuccessTrace, NewMuxTrace, Allocation, SuccessAsync, NewMuxAsync, EarlyPayload]
