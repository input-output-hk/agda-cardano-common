{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- Scheduled-egress setup probe (network 2f1c154, ConnectionHandler newMux).
-- The handler builds a scheduled mux, asks the egress rule, installs its rank
-- source and charge sink in one STM transaction, and traces the rank, all
-- before the promise write. A failure at any of the three is classified and
-- writes no promise. CM's external finally and governors are absent.
module Main where

import Control.Concurrent (myThreadId)
import Control.Concurrent.Async (withAsync, wait, waitCatch)
import Control.Concurrent.Class.MonadSTM.Strict
import Control.Exception (Exception, fromException, mask, throwIO)
import Control.Monad (unless, when)
import Control.Tracer (mkTracer, nullTracer)
import qualified Data.ByteString.Lazy as BL
import Data.IORef
import Network.Socket (SockAddr (SockAddrInet))
import System.Timeout (timeout)
import qualified Network.Mux as Mx
import Network.Mux.Bearer (MakeBearer (..), makeQueueChannelBearer)
import Network.Mux.Bearer.Queues (QueueChannel (..))
import qualified Network.Mux.Trace as Trace
import qualified Ouroboros.Network.ConnectionHandler as H
import Ouroboros.Network.ConnectionId (ConnectionId (..))
import qualified Ouroboros.Network.ConnectionManager.Types as CM
import Ouroboros.Network.Mux
import Ouroboros.Network.MuxMode (withInitiatorMode, withResponderMode)
import Ouroboros.Network.Protocol.Handshake
import Ouroboros.Network.Protocol.Handshake.Unversioned

-- Exact fault identity is checked at the production classifier tracer.
data Fault = Injected deriving (Eq, Show)
instance Exception Fault

data Role = Outbound | Inbound deriving (Eq, Show)

data Site = RuleCall | RankInstall | RankTrace | StartingTrace
  deriving (Eq, Show)

type App = OuroborosBundle Mx.InitiatorResponderMode () () BL.ByteString IO () ()

arguments :: HandshakeArguments (ConnectionId SockAddr) UnversionedProtocol UnversionedProtocolData IO
arguments = HandshakeArguments nullTracer nullTracer unversionedHandshakeCodec
  unversionedProtocolDataCodec acceptableVersion queryVersion timeLimitsHandshake

bounded :: String -> IO a -> IO a
bounded label action = timeout 10000000 action >>= maybe (fail (label ++ " timed out")) pure

run :: Role -> Site -> IO ()
run role site = do
  q1 <- newTBQueueIO 16
  q2 <- newTBQueueIO 16
  let local = QueueChannel q1 q2
      remote = QueueChannel q2 q1
      conn = ConnectionId (SockAddrInet 3000 0) (SockAddrInet 3001 0)
      bearer = getBearer makeQueueChannelBearer
      app = mempty :: App
  seen <- newIORef []
  classified <- newIORef False
  let note event = modifyIORef' seen (++ [event])
      muxTrace = mkTracer $ \(Trace.WithBearer _ event) -> case event of
        Trace.TraceNewMux _ -> note "newMux"
        Trace.TraceEgressRank rank -> note ("rank " ++ show rank) >> when (site == RankTrace) (throwIO Injected)
        Trace.TraceStarting -> note "starting" >> when (site == StartingTrace) (throwIO Injected)
        _ -> pure ()
      muxTracers = Mx.nullTracers { Mx.tracer = muxTrace }
      handlerTrace = mkTracer $ \event -> case event of
        H.TrHandshakeSuccess _ _ -> note "success"
        H.TrConnectionHandlerError _ err _ -> writeIORef classified (fromException err == Just Injected)
        _ -> pure ()
  budget <- Mx.newBucket 1e15 (1024 * 1024) Nothing
  let policy = Mx.EgressPolicy budget Nothing Mx.directionSplit
      rule :: H.EgressPolicyRule IO SockAddr
      rule _ _ _ = do
        note "rule"
        when (site == RuleCall) (throwIO Injected)
        return (\_ -> if site == RankInstall then throwSTM Injected else return (Mx.Rank 7), \_ _ _ -> return ())
  parent <- myThreadId
  let handler :: H.MuxConnectionHandler Mx.InitiatorResponderMode (QueueChannel IO) () () SockAddr
                   UnversionedProtocol UnversionedProtocolData BL.ByteString IO () ()
      handler = H.makeConnectionHandler muxTracers noBindForkPolicy Nothing (Just policy) rule arguments
        (unversionedProtocol app) (parent, mempty)
        (H.MuxInitiatorResponderConnectionHandler (const CM.Duplex) (const nullTracer))
  (reader, writer) <- CM.newEmptyPromiseIO
  writes <- newTVarIO ([] :: [Bool])
  forces <- newTVarIO (0 :: Int)
  let recordWrite value = modifyTVar writes (++ [either (const False) (const True) value])
      observedWriter = CM.PromiseWriter
        { CM.writePromise = \value -> recordWrite value >> CM.writePromise writer value
        , CM.forcePromise = \value -> modifyTVar forces (+1) >> CM.forcePromise writer value }
      handlerFn = case role of
        Outbound -> withInitiatorMode (CM.connectionHandler handler)
        Inbound -> withResponderMode (CM.connectionHandler handler)
      body = CM.runWithUnmask
        (handlerFn id local observedWriter
          handlerTrace conn bearer (\f -> f Nothing))
      remoteBody = do
        rb <- bearer 10 remote Nothing
        case role of
          Outbound -> runHandshakeServer rb conn arguments (unversionedProtocol ())
          Inbound -> runHandshakeClient rb conn arguments (unversionedProtocol ())
  bounded (show site) $ withAsync remoteBody $ \remoteThread ->
    withAsync (mask body) $ \handlerThread -> do
      remoteResult <- wait remoteThread
      case remoteResult of
        Right _ -> pure ()
        Left err -> fail ("remote handshake failed: " ++ show err)
      outcome <- waitCatch handlerThread
      case outcome of
        Left _ -> pure ()
        Right _ -> fail "handler unexpectedly returned normally"
      values <- atomically $ readTVar writes
      forced <- atomically $ readTVar forces
      promise <- atomically $ (Just <$> CM.readPromise reader) `orElse` pure Nothing
      events <- readIORef seen
      didClassify <- readIORef classified
      let expectedWrites = case site of StartingTrace -> [True]; _ -> []
          expectedEvents = case site of
            RuleCall -> ["success", "newMux", "rule"]
            RankInstall -> ["success", "newMux", "rule"]
            RankTrace -> ["success", "newMux", "rule", "rank Rank 7"]
            StartingTrace -> ["success", "newMux", "rule", "rank Rank 7", "starting"]
      unless (values == expectedWrites && forced == 0 && events == expectedEvents && didClassify)
        (fail ("unexpected observations: " ++ show (values, forced, events, didClassify)))
      case (expectedWrites, promise) of
        ([], Nothing) -> pure ()
        ([False], Just (Left (H.HandlerError _))) -> pure ()
        ([True], Just (Right (CM.HandshakeConnectionResult _ _))) -> pure ()
        _ -> fail "wrong promise observation"
      putStrLn (show role ++ "/" ++ show site ++ ": handler joined; writes=" ++ show values ++ "; events=" ++ show events)

main :: IO ()
main = mapM_ (\role -> mapM_ (run role)
  [RuleCall, RankInstall, RankTrace, StartingTrace]) [Outbound, Inbound]
