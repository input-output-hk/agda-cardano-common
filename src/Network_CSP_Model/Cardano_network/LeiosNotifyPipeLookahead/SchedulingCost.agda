{-# OPTIONS --safe #-}

-- A finite potential pays for callbacks, scheduling, transport and delayed trace hooks.
module Cardano_network.LeiosNotifyPipeLookahead.SchedulingCost
  (Notification Return : Set) where

open import Data.Nat using (ℕ; _+_; _*_)
open import Data.List using (length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (true; false)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.SchedulingArithmetic as Arithmetic

-- Main-thread credits pay for registration and for the marker's later Send/count increment.
mainCost : C.Main → ℕ
mainCost C.poll = 13
mainCost C.issue = 4
mainCost C.stopPending = 12
mainCost C.registerQuit = 11
mainCost (C.writingQuit false) = 3
mainCost (C.writingQuit true) = 7
mainCost C.collectingMaybe = 12
mainCost C.collectingWait = 12
mainCost C.adjustCollected = 14
mainCost C.draining = 1
mainCost _ = 0

-- Pending packet energy pays for the receive-to-inspect increase at the visible hook.
receiverCost : C.Receiver → ℕ
receiverCost (C.inspect _) = 5
receiverCost (C.handling _) = 4
receiverCost C.bumpArrival = 3
receiverCost (C.publish _) = 2
receiverCost _ = 0

-- Counts and control credits make every hidden client operation strictly decreasing.
clientCost : C.State → ℕ
clientCost c = Arithmetic.client (C.inFlight c) (length (C.jobs c)) (length (C.results c))
  (mainCost (C.main c)) (receiverCost (C.receiver c))

-- Reader credits pay for new registered jobs and for delayed Send-Done publication.
readerCost : S.Reader → ℕ
readerCost S.admit = 16
readerCost S.register = 15
readerCost S.signalQuit = 12
readerCost S.flushing = 11
readerCost S.doneReady = 10
readerCost S.raising = 1
readerCost _ = 0

-- Selection pays for packet commit, Send publication, retirement and one completion token.
senderCost : S.Sender → ℕ
senderCost S.claimed = 13
senderCost (S.selected _) = 12
senderCost S.sent = 2
senderCost S.idle = 0

-- Owed jobs and accumulated completion tokens remain separate terms of the potential.
serverCost : S.State → ℕ
serverCost s = Arithmetic.server (readerCost (S.reader s)) (S.waiting s) (senderCost (S.sender s)) (S.completed s)

-- An empty Send slot reserves energy for a later commit that leaves source control unchanged.
sendBudget : ∀ {a} {A : Set a} → ℕ → Maybe A → ℕ
sendBudget budget nothing = budget
sendBudget budget (just _) = 0

-- A decoded packet retains energy for its later visible Receive and peer continuation.
receiveBudget : ∀ {a} {A : Set a} → Maybe A → ℕ
receiveBudget nothing = 0
receiveBudget (just _) = 7

-- Queue energy transfers into pending Receive; Send credits pay for FIFO append.
transportCost : D.State → ℕ
transportCost raw = Arithmetic.transport (length (D.clientToServer raw)) (length (D.serverToClient raw))
  (sendBudget 2 (D.pendingClientSend raw)) (sendBudget 9 (D.pendingServerSend raw))
  (receiveBudget (D.pendingClientRecv raw))

-- Residual credits may remain in a blocked or completed state; this is a bound, not a clock.
rank : D.State → ℕ
rank raw = clientCost (D.clientState raw) + (serverCost (D.serverState raw) + transportCost raw)
