{-# LANGUAGE ScopedTypeVariables #-}

-- GHC IO exception-boundary probe, not a replay of Network.Mux or IOSim.
-- io-classes 1.8.0.1 delegates its IO catch to Control.Exception.catch.
-- Run: runghc ConnectionManagement/SourceReplay/CatchMaskProbe.hs
import Control.Concurrent
import Control.Exception
import Control.Monad (unless, void)
import Data.IORef
import System.Timeout (timeout)

main :: IO ()
main = do
  events <- newIORef []
  entered <- newEmptyMVar
  blocked <- newEmptyMVar
  completed <- newEmptyMVar
  let record event = atomicModifyIORef' events (\xs -> (xs ++ [event], ()))
      caught (_ :: SomeAsyncException) = do
        state <- getMaskingState
        record ("catch:" ++ show state)
        putMVar entered ()
        takeMVar blocked
        record "unreachable-catch-return"
      body = bracket (pure ()) (\() -> record "pool-close")
                     (\() -> throwIO ThreadKilled)
  tid <- forkIO $ do
    result <- try ((body `catch` caught) `finally` record "outer-finally")
    putMVar completed (result :: Either SomeException ())
  outcome <- timeout 5000000 $ do
    takeMVar entered
    throwTo tid UserInterrupt
    takeMVar completed
  history <- readIORef events
  let escaped = case outcome of
        Just (Left e) -> fromException e == Just UserInterrupt
        _ -> False
      expected = ["pool-close", "catch:MaskedInterruptible", "outer-finally"]
  unless (escaped && history == expected) $
    error ("unexpected boundary behavior: " ++ show outcome ++ " " ++ show history)
  putStrLn ("PASS " ++ show history ++ "; replacement UserInterrupt escaped")
  void (tryPutMVar blocked ())
