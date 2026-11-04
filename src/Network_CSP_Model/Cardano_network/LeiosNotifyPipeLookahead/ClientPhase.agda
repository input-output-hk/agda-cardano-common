{-# OPTIONS --safe #-}

-- Fresh client control retains the selected return and the counter guards for Quit/Done.
module Cardano_network.LeiosNotifyPipeLookahead.ClientPhase
  (Notification Return : Set) where

open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ-syntax; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import Cardano_network.LeiosNotifyPipeLookahead.ClientShutdown Notification Return as Shutdown
import Cardano_network.LeiosNotifyPipeLookahead.ClientAccounting Notification Return as Accounting
open import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return

-- These are exactly the main-thread phases before termination acceptance.
data Before : Main → Set where
  poll : Before poll
  issue : Before issue
  writing : Before writingRequest
  maybeCollect : Before collectingMaybe
  waitCollect : Before collectingWait
  adjust : Before adjustCollected

-- Counter guards distinguish idle Quit, marker registration and the final Done wait.
data Published : Main → ℕ → Set where
  register : ∀ {n} → Published registerQuit (suc n)
  writeIdle : Published (writingQuit false) 0
  writeBusy : ∀ {n} → Published (writingQuit true) (suc n)
  drain : ∀ {n} → Published draining n
  await : Published awaitDone 0
  closed : Published closed 0

-- Receiver resources are deliberately left to the separate work/reply accounting invariants.
data Phase : State → Set where
  before : ∀ {m r js rs n a} → Before m → Phase (client m r js rs n a false nothing)
  accepted : ∀ {r js rs n a x} → Phase (client stopPending r js rs n a false (just x))
  published : ∀ {m r js rs n a x} → Published m n → Phase (client m r js rs n a true (just x))

-- Receiver activity can change jobs/results/arrived while retaining all main control guards.
retarget : ∀ {m n q v r js rs a r′ js′ rs′ a′} →
  Phase (client m r js rs n a q v) → Phase (client m r′ js′ rs′ n a′ q v)
retarget (before pre) = before pre
retarget accepted = accepted
retarget (published post) = published post

-- Every visible source rule preserves the main-thread phase and its stored value.
step-phase : ∀ {s a t} → Step s a t → Phase s → Phase t
step-phase continueZero (before _) = before issue
step-phase (continueBelow _) (before _) = before maybeCollect
step-phase (continueFull _ _) (before _) = before waitCollect
step-phase stopRequested (before _) = accepted
step-phase sentRequest (before _) = before poll
step-phase sentQuitIdle (published writeIdle) = published await
step-phase sentQuitBusy (published writeBusy) = published drain
step-phase (receivedReply _) phase = retarget phase
step-phase (delivered _) phase = retarget phase
step-phase receivedDone (published await) = published closed

-- Registration, collection and draining retain the exact source counter guards.
tau-phase : ∀ {s t} → Tau s t → Phase s → Phase t
tau-phase registerResponse (before _) = before writing
tau-phase setStopIdle accepted = published writeIdle
tau-phase setStopBusy accepted = published register
tau-phase registerMarker (published register) = published writeBusy
tau-phase optionalEmpty (before _) = before issue
tau-phase optionalResult (before _) = before adjust
tau-phase blockingResult (before _) = before adjust
tau-phase adjustArrival (before _) = before poll
tau-phase drainResult (published drain) = published drain
tau-phase drained (published drain) = published await
tau-phase (startResponse _) phase = retarget phase
tau-phase (startMarker _) phase = retarget phase
tau-phase (keepReply _) phase = retarget phase
tau-phase (discardReply _) phase = retarget phase
tau-phase (countArrival _) phase = retarget phase
tau-phase (publishResponse _) phase = retarget phase
tau-phase (publishMarker _) phase = retarget phase

-- Arbitrary finite source schedules preserve this main-control invariant.
run-phase : ∀ {s actions t} → Run s actions t → Phase s → Phase t
run-phase stop phase = phase
run-phase (internal pr run) phase = run-phase run (tau-phase pr phase)
run-phase (visible pr run) phase = run-phase run (step-phase pr phase)

-- Every fresh client run has the claimed flag, return and counter shape.
initial-phase : ∀ {actions t} → Run initial actions t → Phase t
initial-phase run = run-phase run (before poll)

-- Ordinary request/collection phases cannot already be on the termination path.
before-not-stopping : ∀ {m} → Before m → Shutdown.stopping m ≡ true → ⊥
before-not-stopping poll ()
before-not-stopping issue ()
before-not-stopping writing ()
before-not-stopping maybeCollect ()
before-not-stopping waitCollect ()
before-not-stopping adjust ()

-- A fresh shutdown state always retains an actual selected return value.
stored-return : ∀ {s} → Phase s → Shutdown.stopping (main s) ≡ true →
  Σ[ x ∈ Return ] returnValue s ≡ just x
stored-return (before pre) stopping = ⊥-elim (before-not-stopping pre stopping)
stored-return (accepted {x = x}) stopping = x , refl
stored-return (published {x = x} post) stopping = x , refl

-- Await-Done never has a residual main-thread inFlight count in fresh executions.
await-zero : ∀ {s} → Phase s → main s ≡ awaitDone → inFlight s ≡ 0
await-zero (before ()) refl
await-zero (published await) refl = refl

-- Closed control similarly retains zero count without an extra Done-event premise.
closed-zero : ∀ {s} → Phase s → main s ≡ closed → inFlight s ≡ 0
closed-zero (before ()) refl
closed-zero (published closed) refl = refl

-- Fresh Await-Done means all receiver jobs and results are empty, not just the counter.
await-empty : ∀ {actions s} → Run initial actions s → main s ≡ awaitDone → Accounting.Empty s
await-empty run waiting = Accounting.empty-at-zero (Accounting.initial-accounted run)
  (await-zero (initial-phase run) waiting) (cong Accounting.registered waiting)

-- The same inventory conclusion persists at arbitrary fresh closed source states.
closed-empty : ∀ {actions s} → Run initial actions s → main s ≡ closed → Accounting.Empty s
closed-empty run finished = Accounting.empty-at-zero (Accounting.initial-accounted run)
  (closed-zero (initial-phase run) finished) (cong Accounting.registered finished)

-- A fresh writing-Quit phase has every local guard required by its actual send rule.
writing-quit-enabled : ∀ {s b} → Phase s → main s ≡ writingQuit b →
  Σ[ t ∈ State ] Step s sendQuit t
writing-quit-enabled (before ()) refl
writing-quit-enabled (published writeIdle) refl = _ , sentQuitIdle
writing-quit-enabled (published writeBusy) refl = _ , sentQuitBusy
