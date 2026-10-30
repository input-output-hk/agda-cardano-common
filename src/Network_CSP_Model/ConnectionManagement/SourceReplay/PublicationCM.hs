{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- Real CM + production handler replay; synthetic transport and injected faults.
module Main where

import Control.Concurrent.Class.MonadSTM.Strict
import Control.Exception (throw)
import Control.Concurrent (ThreadId)
import GHC.Conc (ThreadStatus (..), BlockReason (BlockedOnSTM), threadStatus)
import Control.Monad (unless, when)
import Control.Monad.Class.MonadAsync
import Control.Monad.Class.MonadFork (myThreadId, labelThisThread, throwTo)
import Control.Monad.Class.MonadThrow
import Control.Monad.Class.MonadTimer.SI (threadDelay, timeout)
import Control.Tracer (mkTracer, nullTracer)
import qualified Data.ByteString.Lazy as BL
import qualified Data.Map.Strict as Map
import Data.Proxy (Proxy (..))
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
import Ouroboros.Network.DiffusionMode (DiffusionMode (InitiatorAndResponderDiffusionMode))
import Ouroboros.Network.InboundGovernor.InformationChannel (newInformationChannel)
import Ouroboros.Network.Mux
import Ouroboros.Network.MuxMode
import Ouroboros.Network.Protocol.Handshake
import Ouroboros.Network.Protocol.Handshake.Unversioned
import Ouroboros.Network.Server.RateLimiting (AcceptedConnectionsLimit (..))
import Ouroboros.Network.Snocket (Snocket (..), TestAddress (..), AddressFamily (TestFamily))


-- Exercise both CM acquisition entry points with an otherwise fresh map.
data Role = Outbound | Inbound deriving (Eq, Show)
data Site = SuccessTrace | NewMuxTrace | Allocation | EarlyPayload | StartingTrace | SuccessAsync | NewMuxAsync | SuccessCMShutdown | NewMuxCMShutdown
  deriving (Eq, Show)
data Fault = Injected deriving (Eq, Show)
instance Exception Fault

type Addr = TestAddress Int
type App = OuroborosBundle Mx.InitiatorResponderMode () () BL.ByteString IO () ()
type Handle = H.Handle Mx.InitiatorResponderMode () () UnversionedProtocolData BL.ByteString IO () ()
type HandlerFn = CM.ConnectionHandlerFn
  (H.ConnectionHandlerTrace UnversionedProtocol UnversionedProtocolData)
  (QueueChannel IO) Addr (Handle) (H.HandlerError UnversionedProtocol)
  UnversionedProtocol UnversionedProtocolData IO

arguments :: HandshakeArguments (ConnectionId Addr) UnversionedProtocol UnversionedProtocolData IO
arguments = HandshakeArguments nullTracer nullTracer unversionedHandshakeCodec
  unversionedProtocolDataCodec acceptableVersion queryVersion timeLimitsHandshake

-- Delegate both operations to the actual writer; observations share its STM.
decorate :: StrictTVar IO [Bool] -> StrictTVar IO Int -> StrictTVar IO (Maybe ThreadId) -> HandlerFn -> HandlerFn
decorate writes forces handlerId fn update socket writer tracer conn bearer buffer = CM.MaskedAction $ \unmask -> do
  tid <- myThreadId
  atomically $ writeTVar handlerId (Just tid)
  let observed = CM.PromiseWriter
        { CM.writePromise = \value -> do
            modifyTVar writes (++ [either (const False) (const True) value])
            CM.writePromise writer value
        , CM.forcePromise = \value -> modifyTVar forces (+1) >> CM.forcePromise writer value }
  CM.runWithUnmask (fn update socket observed tracer conn bearer buffer) unmask

-- Report is observed before harness cancellation/CM scope exit. ClosedReport
-- observes completion afterward without using a CM API outside that scope.
-- caller outcome, ordinary writes (False=Left/True=Right), force count, close
-- count, entire map empty, callback order, classified injected fault, handler
-- and caller GHC statuses, caller counter callbacks before observation.
data Report = Report String [Bool] Int Int Bool [String] Bool ThreadStatus ThreadStatus Int deriving Show

-- Only OS thread ids and instrumentation escape CM.with; no CM API does.
data ClosedReport = ClosedReport [Bool] Int Int Bool ThreadStatus [String] deriving Show

cmOwned :: Site -> Bool
cmOwned site = site `elem` [SuccessCMShutdown, NewMuxCMShutdown]

-- Bounded by the enclosing timeout; completion is checked rather than inferred
-- from a fixed delay. io-classes SI delays are in seconds.
await :: IO Bool -> IO ()
await ready = do
  done <- ready
  unless done (threadDelay 0.001 >> await ready)

experiment :: Role -> Site -> IO (Report, Maybe ClosedReport)
experiment role site = do
  labelThisThread "replay-main"
  q1 <- newTBQueueIO 16
  q2 <- newTBQueueIO 16
  writes <- newTVarIO []
  forces <- newTVarIO 0
  closes <- newTVarIO 0
  lifecycle <- newTVarIO []
  handlerId <- newTVarIO Nothing
  counterThreads <- newTVarIO []
  tracerEntered <- newEmptyTMVarIO
  seen <- newTVarIO []
  classified <- newTVarIO False
  let local = QueueChannel q1 q2
      remote = QueueChannel q2 q1
      conn = ConnectionId (TestAddress 0) (TestAddress 1)
      provenance = case role of Outbound -> CM.Outbound; Inbound -> CM.Inbound
      expectedLive = Map.singleton (TestAddress 1)
        (Map.singleton (ConnMap.LocalAddr (TestAddress 0)) (CM.UnnegotiatedSt provenance))
      bearer = getBearer makeQueueChannelBearer
      mark text = atomically $ modifyTVar lifecycle (++ [text])
      socketApi = Snocket
        { getLocalAddr = \_ -> pure (TestAddress 0)
        , getRemoteAddr = \_ -> pure (TestAddress 1)
        , addrFamily = const TestFamily
        , open = \_ -> throwIO (userError "unexpected open")
        , openToConnect = \_ -> pure local
        , connect = \_ _ -> pure ()
        , bind = \_ _ -> pure ()
        , listen = \_ -> throwIO (userError "unexpected listen")
        , accept = \_ -> throwIO (userError "unexpected accept")
        , close = \_ -> atomically (modifyTVar closes (+1)) >> mark "socket-close" }
      note text = atomically (modifyTVar seen (++ [text]))
      blockTracer = do
        masking <- getMaskingState
        unless (masking == MaskedInterruptible) (throwIO (userError "tracer not masked interruptibly"))
        tid <- myThreadId
        atomically $ putTMVar tracerEntered tid
        atomically retry
      muxTrace = mkTracer $ \(Trace.WithBearer _ event) -> case event of
        Trace.TraceNewMux _ -> do
          note "newMux"
          when (site == NewMuxTrace) (throwIO Injected)
          when (site `elem` [NewMuxAsync, NewMuxCMShutdown]) blockTracer
        Trace.TraceStarting -> note "starting" >> when (site == StartingTrace) (throwIO Injected)
        _ -> pure ()
      cmTrace = mkTracer $ \event -> case event of
        Core.TrShutdown -> mark "cm-shutdown"
        Core.TrConnectionHandler _ (H.TrHandshakeSuccess _ _) -> do
          note "success"
          when (site == SuccessTrace) (throwIO Injected)
          when (site `elem` [SuccessAsync, SuccessCMShutdown]) blockTracer
        Core.TrConnectionHandler _ (H.TrConnectionHandlerError _ err _) ->
          atomically (writeTVar classified (fromException err == Just Injected))
        Core.TrConnectionManagerCounters _ -> do
          tid <- myThreadId
          atomically $ modifyTVar counterThreads (++ [tid])
        _ -> pure ()
      app = case site of
        EarlyPayload -> throw Injected
        Allocation -> TemperatureBundle (WithHot [throw Injected]) (WithWarm []) (WithEstablished [])
        _ -> mempty :: App
  parent <- myThreadId
  let production :: H.MuxConnectionHandler Mx.InitiatorResponderMode (QueueChannel IO) () () Addr
                    UnversionedProtocol UnversionedProtocolData BL.ByteString IO () ()
      production = H.makeConnectionHandler
        (Mx.nullTracers { Mx.tracer = muxTrace }) noBindForkPolicy arguments
        (unversionedProtocol app) (parent, mempty)
        (H.MuxInitiatorResponderConnectionHandler (const CM.Duplex) (const nullTracer))
      wrapped = CM.ConnectionHandler $ WithInitiatorResponderMode
        (decorate writes forces handlerId (withInitiatorMode (CM.connectionHandler production)))
        (decorate writes forces handlerId (withResponderMode (CM.connectionHandler production)))
  supply <- atomically $ State.newConnStateIdSupply Proxy
  info <- newInformationChannel
  let args = Core.Arguments
        { Core.tracer = cmTrace, Core.trTracer = nullTracer
        , Core.ipv4Address = Nothing, Core.ipv6Address = Nothing
        , Core.addressType = const (Just CM.IPv4Address)
        , Core.snocket = socketApi, Core.makeBearer = makeQueueChannelBearer
        , Core.withBuffer = \f -> f Nothing, Core.configureSocket = \_ _ -> pure ()
        , Core.timeWaitTimeout = 1, Core.outboundIdleTimeout = 1
        , Core.connectionDataFlow = const CM.Duplex
        , Core.prunePolicy = CM.simplePrunePolicy, Core.stdGen = mkStdGen 0
        , Core.connectionsLimits = AcceptedConnectionsLimit maxBound maxBound 0
        , Core.updateVersionData = \value _ -> value
        , Core.connStateIdSupply = supply, Core.classifyHandlerError = H.classifyHandlerError }
  bounded <- timeout 10 $ do
    report <- Core.with args (InResponderMode info) wrapped $ \cm -> do
      let remoteBody = do
            rb <- bearer 10 remote Nothing
            case role of
              Outbound -> runHandshakeServer rb conn arguments (unversionedProtocol ())
              Inbound -> runHandshakeClient rb conn arguments (unversionedProtocol ())
          callerBody = do
            labelThisThread "replay-caller"
            result <- case role of
              Outbound -> CM.acquireOutboundConnection cm InitiatorAndResponderDiffusionMode (TestAddress 1) CM.Outbound
              Inbound -> CM.includeInboundConnection cm maxBound local conn
            pure result
      withAsync remoteBody $ \remoteThread -> withAsync callerBody $ \caller -> do
        remoteResult <- wait remoteThread
        case remoteResult of
          Right _ -> pure ()
          Left err -> throwIO (userError ("remote handshake failed: " ++ show err))
        when (site `elem` [SuccessAsync, NewMuxAsync]) $ do
          tid <- atomically $ readTMVar tracerEntered
          await $ (== ThreadBlocked BlockedOnSTM) <$> threadStatus tid
          -- External harness delivery at a real blocked callback. This is not
          -- claimed as a replay of CM's snapshot/send shutdown traversal.
          throwTo tid AsyncCancelled
        when (cmOwned site) $ do
          tid <- atomically $ readTMVar tracerEntered
          await $ (== ThreadBlocked BlockedOnSTM) <$> threadStatus tid
        unless (cmOwned site) $ await $ do
          mhid <- readTVarIO handlerId
          maybe (pure False) (fmap (== ThreadFinished) . threadStatus) mhid
        let callerId = asyncThreadId caller
            expectedCounters = case role of Outbound -> 2; Inbound -> 1
            prepublication = site `elem` [SuccessTrace, NewMuxTrace, Allocation, SuccessAsync, NewMuxAsync, SuccessCMShutdown, NewMuxCMShutdown]
        await $ if prepublication then do
          status <- threadStatus callerId
          counters <- readTVarIO counterThreads
          pure (status == ThreadBlocked BlockedOnSTM
                && length (filter (== callerId) counters) == expectedCounters)
          else maybe False (const True) <$> poll caller
        callerResult <- poll caller
        states <- atomically $ CM.readState cm
        ws <- readTVarIO writes
        fs <- readTVarIO forces
        cs <- readTVarIO closes
        events <- readTVarIO seen
        ok <- readTVarIO classified
        mhid <- readTVarIO handlerId
        hid <- maybe (throwIO (userError "missing handler id")) pure mhid
        handlerStatus <- threadStatus hid
        callerStatus <- threadStatus (asyncThreadId caller)
        counters <- readTVarIO counterThreads
        when (cmOwned site) $ do
          unless (ConnMap.getConnMap states == expectedLive)
            (throwIO (userError "CM shutdown must start from exact live handler entry"))
          mark "observed-open"
        let callerCounterCount = length (filter (== asyncThreadId caller) counters)
        let outcome = case callerResult of
              Nothing -> "pending"
              Just (Left err) -> "exception:" ++ displayException err
              Just (Right CM.Connected {}) -> "connected"
              Just (Right CM.Disconnected {}) -> "disconnected"
            report = Report outcome ws fs cs (Map.null (ConnMap.getConnMap states)) events ok handlerStatus callerStatus callerCounterCount
        -- Cancellation belongs to the harness and follows the observation marker.
        cancel caller
        _ <- waitCatch caller
        when (cmOwned site) $ do
          status <- threadStatus hid
          count <- readTVarIO closes
          afterCancel <- atomically $ CM.readState cm
          unless (status == ThreadBlocked BlockedOnSTM && count == 0
                  && ConnMap.getConnMap afterCancel == expectedLive)
            (throwIO (userError "caller cancellation changed blocked handler"))
          mark "caller-cancelled"
        pure report
    if cmOwned site then do
      mark "after-with"
      mhid <- readTVarIO handlerId
      hid <- maybe (throwIO (userError "missing handler id")) pure mhid
      await $ (== ThreadFinished) <$> threadStatus hid
      ws <- readTVarIO writes
      fs <- readTVarIO forces
      cs <- readTVarIO closes
      ok <- readTVarIO classified
      status <- threadStatus hid
      life <- readTVarIO lifecycle
      pure (report, Just (ClosedReport ws fs cs ok status life))
      else pure (report, Nothing)
  maybe (throwIO (userError "CM replay timed out")) pure bounded

verifyCase :: Role -> Site -> IO ()
verifyCase role site = do
  (report, after) <- experiment role site
  let Report outcome writes forces closes empty events classified handlerStatus callerStatus counterCount = report
      expectedWrites = case site of EarlyPayload -> [False]; StartingTrace -> [True]; _ -> []
      expectedEvents = case site of
        EarlyPayload -> []
        SuccessTrace -> ["success"]
        SuccessAsync -> ["success"]
        SuccessCMShutdown -> ["success"]
        StartingTrace -> ["success", "newMux", "starting"]
        _ -> ["success", "newMux"]
      goodOutcome = case site of
        EarlyPayload -> outcome == "disconnected"
        StartingTrace -> outcome `elem` ["connected", "disconnected"]
        _ -> outcome == "pending"
      physical = handlerStatus == (if cmOwned site then ThreadBlocked BlockedOnSTM else ThreadFinished)
      waiting = outcome /= "pending" ||
        (counterCount == (case role of Outbound -> 2; Inbound -> 1) && callerStatus == ThreadBlocked BlockedOnSTM)
  unless (writes == expectedWrites && forces == 0 && closes == (if cmOwned site then 0 else 1)
          && empty == not (cmOwned site) && events == expectedEvents
          && classified == (site `notElem` [SuccessAsync, NewMuxAsync, SuccessCMShutdown, NewMuxCMShutdown]) && goodOutcome && physical && waiting)
    (fail (show (role, site, report, physical, waiting)))
  case (cmOwned site, after) of
    (False, Nothing) -> pure ()
    (True, Just (ClosedReport ws fs cs ok status life)) ->
      unless (null ws && fs == 0 && cs == 1 && not ok && status == ThreadFinished
              && life == ["observed-open", "caller-cancelled", "cm-shutdown", "socket-close", "after-with"])
        (fail (show (role, site, after)))
    _ -> fail "wrong scope completion observation"
  putStrLn (show role ++ "/" ++ show site ++ ": " ++ show report ++ "; after CM scope=" ++ show after)

main :: IO ()
main = mapM_ (\role -> mapM_ (verifyCase role)
  [SuccessTrace, NewMuxTrace, Allocation, EarlyPayload, StartingTrace, SuccessAsync, NewMuxAsync, SuccessCMShutdown, NewMuxCMShutdown]) [Outbound, Inbound]
