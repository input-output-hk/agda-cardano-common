{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- Contract probe only: the real driver Done branch, not a wire handshake/CM replay.
module Main where

import Control.Exception (Exception, evaluate, throw, try)
import Control.Concurrent.Class.MonadSTM.Strict (newTVarIO)
import Control.Monad (unless)
import Control.Tracer (mkTracer)
import Data.Functor.Identity (Identity (..))
import Data.IORef
import Network.TypedProtocol.Core
import Network.TypedProtocol.Driver
import Network.TypedProtocol.Peer
import qualified Network.Mux as Mx
import qualified Network.Mux.Trace as Trace
import qualified Ouroboros.Network.ConnectionHandler as H
import Ouroboros.Network.ControlMessage (ControlMessage (Continue))
import Ouroboros.Network.Mux
import Ouroboros.Network.Protocol.Handshake.Type

type App = OuroborosBundle Mx.InitiatorMode () () () IO () ()

-- Done does not use transport. Fail explicitly if that assumption changes.
driver :: Driver (Handshake Int Int) AsClient () IO
driver = Driver { sendMessage = \_ _ -> fail "unexpected send"
                , recvMessage = \_ _ -> fail "unexpected receive"
                , initialDState = () }

finish :: HandshakeResult App Int Int -> IO (HandshakeResult App Int Int)
finish result = fst <$> runPeerWithDriver driver
  (Done ReflNobodyAgency result :: Peer (Handshake Int Int) AsClient NonPipelined StDone IO (HandshakeResult App Int Int))

data Fault = BadVersionData | BadApplication | BadProtocol | BadList
  deriving (Eq, Show)
instance Exception Fault

expectFault :: Fault -> String -> IO a -> IO ()
expectFault expected name action = do
  result <- try action
  case result of
    Left actual -> do
      unless (actual == expected) (fail (name ++ ": wrong fault " ++ show actual))
      putStrLn (name ++ ": caught " ++ show actual)
    Right _ -> fail (name ++ ": unexpectedly returned")

main :: IO ()
main = do
  expectFault BadVersionData "version data forced before return" $
    finish (HandshakeNegotiationResult mempty 1 (throw BadVersionData))
  expectFault BadApplication "application forced before return" $
    finish (HandshakeNegotiationResult (throw BadApplication) 1 2)
  expectFault BadList "list spine forced before return" $
    finish (HandshakeNegotiationResult
      (TemperatureBundle (WithHot (throw BadList)) (WithWarm []) (WithEstablished [])) 1 2)
  -- TemperatureBundle AND its temperature wrappers have strict fields. The list
  -- spine must be non-bottom; its element is still lazy until protocol allocation.
  let app = TemperatureBundle (WithHot [throw BadProtocol])
                              (WithWarm []) (WithEstablished []) :: App
  result <- finish (HandshakeNegotiationResult app 1 2)
  putStrLn "lazy protocol element survived driver return"
  seen <- newIORef False
  let tracers = Mx.nullTracers { Mx.tracer = mkTracer $ \(Identity event) ->
        case event of
          Trace.TraceNewMux _ -> writeIORef seen True
          _ -> pure () }
  case result of
    HandshakeNegotiationResult forcedApp _ _ ->
      expectFault BadProtocol "lazy protocol element forced inside Mux.new" $
        Mx.new tracers (mkMiniProtocolInfos (runForkPolicy noBindForkPolicy ()) forcedApp)
    _ -> fail "unexpected query result"
  readIORef seen >>= \traced -> unless traced (fail "TraceNewMux not reached")
  -- Ordinary non-bottom inputs can subsequently be re-forced to WHNF.
  good <- finish (HandshakeNegotiationResult mempty 1 2)
  case good of
    HandshakeNegotiationResult app' _ data' -> do
      mux <- Mx.new Mx.nullTracers
        (mkMiniProtocolInfos (runForkPolicy noBindForkPolicy ()) app')
      controls <- TemperatureBundle <$> (WithHot <$> newTVarIO Continue)
                                    <*> (WithWarm <$> newTVarIO Continue)
                                    <*> (WithEstablished <$> newTVarIO Continue)
      _ <- evaluate (H.Handle mux app' controls data' :: H.Handle Mx.InitiatorMode () () Int () IO () ())
      putStrLn "real strict Handle construction returned"
    _ -> fail "unexpected query result"
  putStrLn "all forcing controls passed"
