{-# OPTIONS --safe #-}

-- Source-model properties, not a refinement theorem for the Haskell runtime.
module Cardano_network.LeiosNotifyPipeLookahead.Properties
  (Notification : Set) where

open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties using (≤-refl)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Empty using (⊥)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Cardano_network.LeiosNotifyPipeLookahead.Model Notification

-- Reader shutdown is observed before the shared flag is necessarily written.
stopping : Reader → Bool
stopping signalQuit = true
stopping flushing = true
stopping doneReady = true
stopping closed = true
stopping _ = false

-- A visible reader Quit starts shutdown immediately at its local observation.
quit-starts-shutdown : ∀ {p s t} → Step p s recvQuit t → stopping (reader t) ≡ true
quit-starts-shutdown (receiveQuit atFirst) = refl
quit-starts-shutdown (receiveQuit atNext) = refl

-- Once the reader stops accepting commands, visible actions cannot reopen it.
step-stopping : ∀ {p s a t} → Step p s a t → stopping (reader s) ≡ true →
  stopping (reader t) ≡ true
step-stopping (receiveRequest atFirst) ()
step-stopping (receiveRequest atNext) ()
step-stopping (receiveQuit atFirst) ()
step-stopping (receiveQuit atNext) ()
step-stopping (choose _ _) pr = pr
step-stopping (send _) pr = pr
step-stopping finish _ = refl

-- Scheduling and completion also preserve a reader's shutdown status.
tau-stopping : ∀ {s t} → Tau s t → stopping (reader s) ≡ true →
  stopping (reader t) ≡ true
tau-stopping admitted ()
tau-stopping excessive ()
tau-stopping registered ()
tau-stopping setQuit _ = refl
tau-stopping (claim _) pr = pr
tau-stopping (cancel _) pr = pr
tau-stopping (retire _) pr = pr
tau-stopping flush _ = refl
tau-stopping drained _ = refl
tau-stopping abort ()

-- Shutdown persists throughout every finite operational continuation.
run-stopping : ∀ {p s es t} → Run p s es t → stopping (reader s) ≡ true →
  stopping (reader t) ≡ true
run-stopping stop pr = pr
run-stopping (internal st run) pr = run-stopping run (tau-stopping st pr)
run-stopping (visible st run) pr = run-stopping run (step-stopping st pr)

-- New RequestNext receives are impossible after reader shutdown begins.
no-request-after-quit : ∀ {p s t} → stopping (reader s) ≡ true →
  Step p s recvRequest t → ⊥
no-request-after-quit () (receiveRequest atFirst)
no-request-after-quit () (receiveRequest atNext)

-- Repeated Quit receives are also unavailable after the first one.
no-repeated-quit : ∀ {p s t} → stopping (reader s) ≡ true →
  Step p s recvQuit t → ⊥
no-repeated-quit () (receiveQuit atFirst)
no-repeated-quit () (receiveQuit atNext)

-- Application-selected replies are chosen before the shared flag is set.
selection-before-flag : ∀ {p s m t} → Step p s (nextReply m) t → quitFlag s ≡ false
selection-before-flag (choose _ _) = refl

-- The production callback contract never selects cancellation itself.
node-callback-normal : ∀ {s m t} → Step nodeNext s (nextReply m) t →
  Σ[ a ∈ Notification ] m ≡ normal a
node-callback-normal (choose {m = normal a} _ _) = a , refl
node-callback-normal (choose {m = canceled} _ ())

-- A later wire send retains the exact payload chosen earlier.
selected-payload-retained : ∀ {p s m t} → Step p s (sendReply m) t →
  sender s ≡ selected m
selected-payload-retained (send _) = refl

-- Done requires a true flag, no waiting/active jobs and no unflushed completions.
done-only-drained : ∀ {p s t} → Step p s sendDone t →
  s ≡ state doneReady 0 idle 0 true
done-only-drained finish = refl

-- Normal-operation quiescence can retain arbitrarily many completed jobs.
ready : ℕ → State
ready n = state awaitNext 0 idle n false

-- Such bookkeeping is independent of the unanswered request count.
ready-owes-nothing : ∀ n → owed (ready n) ≡ 0
ready-owes-nothing n = refl

-- One ordinary request/reply exchange has one explicit callback-readiness action.
roundActions : Notification → List Action
roundActions a = recvRequest ∷ nextReply (normal a) ∷ sendReply (normal a) ∷ []

-- A sequential exchange increments completed without issuing a second request.
round-run : ∀ {p r c} (a : Notification) → Reading r →
  Run p (state r 0 idle c false) (roundActions a) (ready (suc c))
round-run a canRead =
  visible (receiveRequest canRead) $
  internal admitted $
  internal registered $
  internal (claim refl) $
  visible (choose refl refl) $
  visible (send refl) $
  internal (retire refl) stop

-- Every positive number of completed-but-unflushed jobs is reachable at zero owed.
completed-reachable : (a : Notification) (n : ℕ) →
  Σ[ es ∈ List Action ] Run nodeNext initial es (ready (suc n))
completed-reachable a zero = roundActions a , round-run a atFirst
completed-reachable a (suc n) with completed-reachable a n
... | es , run = es ++ roundActions a , append run (round-run a atNext)

-- No bound on completed bookkeeping follows from having zero outstanding requests.
completion-bound-counterexample : (a : Notification) (bound : ℕ) →
  Σ[ es ∈ List Action ]
    (Run nodeNext initial es (ready (suc bound)) ×
     owed (ready (suc bound)) ≡ 0 × bound < completed (ready (suc bound)))
completion-bound-counterexample a bound with completed-reachable a bound
... | es , run = es , run , refl , ≤-refl

-- Draining these already completed jobs needs one FlushSender step per token.
drain-completed : ∀ {p} (n : ℕ) →
  Run p (state flushing 0 idle n true) (sendDone ∷ []) (state closed 0 idle 0 true)
drain-completed zero = internal drained (visible finish stop)
drain-completed (suc n) = internal flush (drain-completed n)

-- A reader with no unanswered requests still flushes its accumulated completions.
shutdown : ∀ {p} (n : ℕ) →
  Run p (ready n) (recvQuit ∷ sendDone ∷ []) (state closed 0 idle 0 true)
shutdown n = visible (receiveQuit atNext) (internal setQuit (drain-completed n))

-- Count actual flush rules in a supplied operational witness.
flushCount : ∀ {p s es t} → Run p s es t → ℕ
flushCount stop = 0
flushCount (internal flush run) = suc (flushCount run)
flushCount (internal _ run) = flushCount run
flushCount (visible _ run) = flushCount run

-- The constructed drain performs exactly n completion-token flushes.
drain-count : ∀ {p} n → flushCount (drain-completed {p} n) ≡ n
drain-count zero = refl
drain-count (suc n) = cong suc (drain-count n)

-- Shutdown bookkeeping scales with prior completed exchanges in this execution.
shutdown-count : ∀ {p} n → flushCount (shutdown {p} n) ≡ n
shutdown-count n = drain-count n
