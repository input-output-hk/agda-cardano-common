{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- Synchronous LeiosDB write waits (consensus 2e44d98, M5). The fetch
-- collector awaits each write inline (LeiosDemoLogic 1006, 1007 and 1455:
-- `await =<< writeEbPoint ...`). This probe runs the production SQLite
-- LeiosDB and its single writer, and checks the contract the model states:
--   1. a completed write lets the await return, after the row is readable;
--   2. an await blocks while the write is held up, and cancelling the
--      awaiting thread does not retract the queued write, which lands later;
--   3. a failed write stops and seals the writer: the failed job's awaiter and
--      a job queued behind it both throw, and a later submission throws.
-- The writer is held up by another connection's write lock; SQLite's
-- busy_timeout is 1000 ms, so a 200 ms hold delays and a 2500 ms hold fails.
module Main where

import Control.Concurrent (threadDelay)
import Control.Concurrent.Async (AsyncCancelled (..), async, cancel, waitCatch)
import Control.Concurrent.MVar
import Control.Exception
import Control.Monad (forever, unless)
import Control.Tracer (nullTracer)
import qualified Data.ByteString as BS
import qualified Data.Text as T
import Data.IORef
import qualified Database.SQLite3 as Sql
import System.Directory (createDirectoryIfMissing, removePathForcibly)
import System.Environment (getArgs)
import System.FilePath ((</>))
import Cardano.Slotting.Slot (SlotNo (..))
import Ouroboros.Consensus.Leios.Types (EbHash, LeiosPoint (..), mkEbHash)
import Ouroboros.Consensus.Storage.LeiosDB.API
import Ouroboros.Consensus.Storage.LeiosDB.Exception (LeiosDbException (..), LeiosDbWriteFailure (..))
import Ouroboros.Consensus.Storage.LeiosDB.Impl.SQLite (withLeiosDBSQLite)

point :: Int -> IO LeiosPoint
point n = MkLeiosPoint (SlotNo (fromIntegral n)) <$> mkEbHash (BS.replicate 32 (fromIntegral n))

key :: LeiosPoint -> (SlotNo, EbHash)
key (MkLeiosPoint s h) = (s, h)

check :: String -> Bool -> IO ()
check label ok = unless ok (fail ("check failed: " ++ label))

-- A fresh pair of partition files for one case.
paths :: FilePath -> String -> IO (FilePath, FilePath)
paths root name = do
  let dir = root </> name
  removePathForcibly dir
  createDirectoryIfMissing True dir
  pure (dir </> "vol.db", dir </> "imm.db")

-- Hold the volatile partition's write lock from another connection.
holdLock :: FilePath -> IO Sql.Database
holdLock vol = do
  conn <- Sql.open (T.pack vol)
  Sql.exec conn (T.pack "BEGIN IMMEDIATE")
  pure conn
release :: Sql.Database -> IO ()
release conn = Sql.exec conn (T.pack "ROLLBACK") >> Sql.close conn

isWriteFailure :: SomeException -> Bool
isWriteFailure e = case fromException e of
  Just (LeiosDbWriteException _) -> True
  _ -> False

completed :: FilePath -> IO ()
completed root = do
  (vol, imm) <- paths root "completed"
  withLeiosDBSQLite nullTracer vol imm $ \h -> do
    w <- openWriter h
    r <- openReader h
    p <- point 1
    done <- await =<< writeEbPoint w p 100
    rows <- testScanEbPoints r
    check "row readable when the await returns" (key p `elem` rows)
    putStrLn ("completed: await returned " ++ show (length done) ++ " completed EBs; row present")

cancelled :: FilePath -> IO ()
cancelled root = do
  (vol, imm) <- paths root "cancelled"
  withLeiosDBSQLite nullTracer vol imm $ \h -> do
    w <- openWriter h
    r <- openReader h
    p <- point 2
    conn <- holdLock vol
    returned <- newIORef False
    submitted <- newEmptyMVar
    collector <- async $ do
      promise <- writeEbPoint w p 100
      putMVar submitted ()
      _ <- await promise
      writeIORef returned True
    takeMVar submitted
    threadDelay 200000
    blocked <- not <$> readIORef returned
    before <- testScanEbPoints r
    cancel collector
    outcome <- waitCatch collector
    release conn
    closeWriter w
    after <- testScanEbPoints r
    let wasCancelled = case outcome of
          Left e -> fromException e == Just AsyncCancelled
          Right _ -> False
    check "await blocked while the write was held up" blocked
    check "row absent before the write" (key p `notElem` before)
    check "collector cancelled" wasCancelled
    check "queued write landed after cancellation" (key p `elem` after)
    putStrLn "cancelled: await blocked; collector cancelled; queued write landed afterwards"

failed :: FilePath -> IO ()
failed root = do
  (vol, imm) <- paths root "failed"
  writerVar <- newEmptyMVar
  scope <- async $ withLeiosDBSQLite nullTracer vol imm $ \h -> do
    openWriter h >>= putMVar writerVar
    forever (threadDelay 1000000)
  w <- takeMVar writerVar
  p3 <- point 3
  p4 <- point 4
  p5 <- point 5
  conn <- holdLock vol
  first <- async (await =<< writeEbPoint w p3 100)
  threadDelay 100000
  second <- async (await =<< writeEbPoint w p4 100)
  firstOutcome <- waitCatch first
  secondOutcome <- waitCatch second
  scopeOutcome <- waitCatch scope
  release conn
  late <- try (writeEbPoint w p5 100)
  let failure = either isWriteFailure (const False)
      lateRefused = case late of
        Left (LeiosDbWriteException _) -> True
        _ -> False
  check "failed job's await throws" (failure firstOutcome)
  check "queued job's await throws" (failure secondOutcome)
  check "writer failure reached its linked owner" (either (const True) (const False) scopeOutcome)
  check "submission after the seal throws" lateRefused
  let cause = case firstOutcome of
        Left e | Just (LeiosDbWriteException f) <- fromException e -> takeWhile (/= '\n') (displayException (ldwfWriteFailure f))
        _ -> "?"
  putStrLn "failed: both awaits threw LeiosDbWriteException; owner took the linked failure; later submission refused"
  putStrLn ("failed: cause of the first: " ++ cause)

main :: IO ()
main = do
  root <- getArgs >>= \case
    [dir] -> pure dir
    _ -> fail "usage: LeiosDbWaits <scratch directory>"
  completed root
  cancelled root
  failed root
