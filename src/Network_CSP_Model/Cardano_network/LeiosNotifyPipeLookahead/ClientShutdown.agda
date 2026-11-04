{-# OPTIONS --safe #-}

-- Client shutdown is a persistent control path, independent of receiver progress.
module Cardano_network.LeiosNotifyPipeLookahead.ClientShutdown
  (Notification Return : Set) where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return

-- Termination's main-thread path never returns to poll, issue or collection-for-continue.
stopping : Main → Bool
stopping stopPending = true
stopping registerQuit = true
stopping (writingQuit _) = true
stopping draining = true
stopping awaitDone = true
stopping closed = true
stopping _ = false

-- Accepting the termination callback enters shutdown even before the Quit flag write.
terminate-starts : ∀ {s x t} → Step s (terminate x) t → stopping (main t) ≡ true
terminate-starts stopRequested = refl

-- Both idle and pipelined Quit send continuations remain on that same shutdown path.
quit-starts : ∀ {s t} → Step s sendQuit t → stopping (main t) ≡ true
quit-starts sentQuitIdle = refl
quit-starts sentQuitBusy = refl

-- Visible receiver processing cannot reopen main-thread request issuance.
step-stopping : ∀ {s a t} → Step s a t → stopping (main s) ≡ true → stopping (main t) ≡ true
step-stopping continueZero ()
step-stopping (continueBelow _) ()
step-stopping (continueFull _ _) ()
step-stopping stopRequested ()
step-stopping sentRequest ()
step-stopping sentQuitIdle _ = refl
step-stopping sentQuitBusy _ = refl
step-stopping (receivedReply _) stopping = stopping
step-stopping (delivered _) stopping = stopping
step-stopping receivedDone _ = refl

-- Registration, draining and receiver publication preserve shutdown as well.
tau-stopping : ∀ {s t} → Tau s t → stopping (main s) ≡ true → stopping (main t) ≡ true
tau-stopping registerResponse ()
tau-stopping setStopIdle _ = refl
tau-stopping setStopBusy _ = refl
tau-stopping registerMarker _ = refl
tau-stopping optionalEmpty ()
tau-stopping optionalResult ()
tau-stopping blockingResult ()
tau-stopping adjustArrival ()
tau-stopping drainResult _ = refl
tau-stopping drained _ = refl
tau-stopping (startResponse _) stopping = stopping
tau-stopping (startMarker _) stopping = stopping
tau-stopping (keepReply _) stopping = stopping
tau-stopping (discardReply _) stopping = stopping
tau-stopping (countArrival _) stopping = stopping
tau-stopping (publishResponse _) stopping = stopping
tau-stopping (publishMarker _) stopping = stopping

-- Every finite continuation of shutdown stays outside the request-issuance path.
run-stopping : ∀ {s actions t} → Run s actions t → stopping (main s) ≡ true → stopping (main t) ≡ true
run-stopping stop stopping = stopping
run-stopping (internal pr run) stopping = run-stopping run (tau-stopping pr stopping)
run-stopping (visible pr run) stopping = run-stopping run (step-stopping pr stopping)

-- A new RequestNext record is impossible once termination has been selected.
no-request : ∀ {s t} → stopping (main s) ≡ true → Step s sendRequest t → ⊥
no-request () sentRequest
