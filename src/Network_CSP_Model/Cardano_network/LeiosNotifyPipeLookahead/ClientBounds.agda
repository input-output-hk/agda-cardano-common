{-# OPTIONS --safe #-}

-- Resource bounds require the pinned fixed-depth client, including its Quit marker.
module Cardano_network.LeiosNotifyPipeLookahead.ClientBounds
  (Notification Return : Set) where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_; length)
open import Data.Nat using (ℕ; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤n⇒m≤1+n; ≤-pred; m≤m+n; m≤n+m; +-mono-≤)
open import Data.Integer using (+_)
import Data.Integer.Properties as Int
open import Data.Integer.Properties using () renaming (_<?_ to compareInteger)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary.Decidable using (Dec; does; yes; no)
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
import Cardano_network.LeiosNotifyPipeLookahead.ClientAccounting Notification Return as A
import Cardano_network.LeiosNotifyPipeLookahead.ClientReplyAccounting Notification Return as R
open import Cardano_network.LeiosNotifyPipeLookahead.NodeClientModel Notification Return

-- Issuance reserves room for its next request; shutdown additionally counts one marker.
cap : C.Main → ℕ
cap C.issue = 999
cap C.writingRequest = 999
cap C.collectingMaybe = 999
cap C.draining = 1001
cap _ = 1000

-- Phase-sensitive bounds exclude the otherwise possible send from a full pipe.
Bound : C.State → Set
Bound c = C.inFlight c ≤ cap (C.main c)

-- Boolean comparison evidence retains its proof-bearing decision.
decision-witness : ∀ {A : Set} (d : Dec A) → does d ≡ true → A
decision-witness (yes pr) refl = pr
decision-witness (no _) ()

-- The pinned signed comparison gives the natural strict bound used by optional collect.
below-bound : ∀ n → C.below n (+ 1000) ≡ true → n ≤ 999
below-bound n comparison = ≤-pred (Int.drop‿+<+
  (decision-witness (compareInteger (+ n) (+ 1000)) comparison))

-- Generic internal receiver transfers preserve the phase-sensitive scalar bound.
tau-bound : ∀ {s t} → C.Tau s t → Bound s → Bound t
tau-bound C.registerResponse bound = bound
tau-bound C.setStopIdle bound = z≤n
tau-bound C.setStopBusy bound = bound
tau-bound C.registerMarker bound = bound
tau-bound C.optionalEmpty bound = bound
tau-bound C.optionalResult bound = m≤n⇒m≤1+n (m≤n⇒m≤1+n (≤-pred bound))
tau-bound C.blockingResult bound = ≤-trans (≤-pred bound) (m≤n⇒m≤1+n ≤-refl)
tau-bound C.adjustArrival bound = bound
tau-bound C.drainResult bound = ≤-trans (≤-pred bound) (m≤n⇒m≤1+n ≤-refl)
tau-bound C.drained bound = z≤n
tau-bound (C.startResponse _) bound = bound
tau-bound (C.startMarker _) bound = bound
tau-bound (C.keepReply _) bound = bound
tau-bound (C.discardReply _) bound = bound
tau-bound (C.countArrival _) bound = bound
tau-bound (C.publishResponse _) bound = bound
tau-bound (C.publishMarker _) bound = bound

-- Only the fixed-depth continuation supplies the extra issuance premise.
continue-bound : ∀ {s t} → C.Step s (C.continue (+ 1000)) t → Bound s → Bound t
continue-bound C.continueZero bound = z≤n
continue-bound (C.continueBelow {n = n} comparison) bound = below-bound (suc n) comparison
continue-bound (C.continueFull _ _) bound = bound

-- Wire records use the reserved request room or the one additional Quit marker.
wire-bound : ∀ {s t a} → Wire a → C.Step s a t → Bound s → Bound t
wire-bound request C.sentRequest bound = s≤s bound
wire-bound quit C.sentQuitIdle bound = z≤n
wire-bound quit C.sentQuitBusy bound = s≤s bound
wire-bound reply (C.receivedReply _) bound = bound
wire-bound done C.receivedDone bound = z≤n

-- A failed handler freezes the same client resources instead of resetting them.
raw : State → C.State
raw (running c) = c
raw (unexpectedCancel c) = c

-- Keep the exact inventory equation alongside the scalar bound at abnormal exits too.
Invariant : State → Set
Invariant s = Bound (raw s) × A.Accounted (raw s)

-- All node-policy observations preserve both the bound and the corrected inventory.
step : ∀ {s a t} → Step s a t → Invariant s → Invariant t
step (wireRecord classification pr) (bound , eq) = wire-bound classification pr bound , A.step-accounted pr eq
step (continueAtDepth pr) (bound , eq) = continue-bound pr bound , A.step-accounted pr eq
step (terminate C.stopRequested) (bound , eq) = bound , eq
step (handled (C.delivered _)) inv = inv
step (rejectedCancel _ _) inv = inv

-- Scheduling preserves the same invariant before and after stop publication.
tau : ∀ {s t} → Tau s t → Invariant s → Invariant t
tau (schedule pr) (bound , eq) = tau-bound pr bound , A.tau-accounted pr eq

-- Every finite node-client history retains its starting invariant.
run : ∀ {s es t} → Run s es t → Invariant s → Invariant t
run stop inv = inv
run (internal pr rest) inv = run rest (tau pr inv)
run (visible pr rest) inv = run rest (step pr inv)

-- Freshness discharges both resource premises without assumptions about scheduling.
initial-invariant : ∀ {es t} → Run initial es t → Invariant t
initial-invariant trace = run trace (z≤n , refl)

-- Every phase cap, including registration correction, fits in depth plus one.
cap-corrected : ∀ m → cap m + A.registered m ≤ 1001
cap-corrected C.poll = m≤n⇒m≤1+n ≤-refl
cap-corrected C.issue = m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)
cap-corrected C.writingRequest = m≤n⇒m≤1+n ≤-refl
cap-corrected C.stopPending = m≤n⇒m≤1+n ≤-refl
cap-corrected C.registerQuit = m≤n⇒m≤1+n ≤-refl
cap-corrected C.collectingMaybe = m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)
cap-corrected C.collectingWait = m≤n⇒m≤1+n ≤-refl
cap-corrected C.adjustCollected = m≤n⇒m≤1+n ≤-refl
cap-corrected C.draining = ≤-refl
cap-corrected C.awaitDone = m≤n⇒m≤1+n ≤-refl
cap-corrected C.closed = m≤n⇒m≤1+n ≤-refl
cap-corrected (C.writingQuit false) = m≤n⇒m≤1+n ≤-refl
cap-corrected (C.writingQuit true) = ≤-refl

-- The scalar pipeline index also fits depth plus one in every retained phase.
counter-bound : ∀ {c} → Bound c → C.inFlight c ≤ 1001
counter-bound {c} bound = ≤-trans bound (≤-trans
  (m≤m+n (cap (C.main c)) (A.registered (C.main c))) (cap-corrected (C.main c)))

-- Total queued, active and completed receiver work has the same uniform bound.
work-bound : ∀ {c} → Bound c → A.Accounted c → A.work c ≤ 1001
work-bound {c} bound eq = subst (_≤ 1001) eq
  (≤-trans (+-mono-≤ bound ≤-refl) (cap-corrected (C.main c)))

-- Counting only response jobs never exceeds the full job queue.
responses-bound : ∀ js → R.responses js ≤ length js
responses-bound [] = z≤n
responses-bound (C.responseJob ∷ js) = s≤s (responses-bound js)
responses-bound (C.quitMarker ∷ js) = m≤n⇒m≤1+n (responses-bound js)

-- An awaited wire reply is one of the possible active receiver jobs.
awaiting-bound : ∀ r → R.awaitingReply r ≤ A.busy r
awaiting-bound C.idle = z≤n
awaiting-bound C.awaiting = ≤-refl
awaiting-bound (C.inspect _) = z≤n
awaiting-bound (C.handling _) = z≤n
awaiting-bound C.bumpArrival = z≤n
awaiting-bound (C.publish _) = z≤n

-- Reply obligations are a subset of unfinished receiver work.
owed≤work : ∀ c → R.owed c ≤ A.work c
owed≤work c = +-mono-≤ (responses-bound (C.jobs c))
  (≤-trans (awaiting-bound (C.receiver c)) (m≤m+n _ _))

-- Each actual client queue is bounded without confusing inFlight with inventory.
queue-bounds : ∀ {c} → Bound c → A.Accounted c →
  (length (C.jobs c) ≤ 1001) × (length (C.results c) ≤ 1001) × (R.owed c ≤ 1001)
queue-bounds {c} bound eq =
  ≤-trans (m≤m+n _ _) total ,
  ≤-trans (≤-trans (m≤n+m (length (C.results c)) (A.busy (C.receiver c)))
    (m≤n+m (A.busy (C.receiver c) + length (C.results c)) (length (C.jobs c)))) total ,
  ≤-trans (owed≤work c) total
  where
  -- The accounting equation bounds the sum, not only its individual summands.
  total : A.work c ≤ 1001
  total = work-bound {c = c} bound eq
