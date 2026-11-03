{-# OPTIONS --safe #-}

-- Executable client transitions certified against the independent source rules.
open import Relation.Binary.Definitions using (DecidableEquality)
module Cardano_network.LeiosNotifyPipeLookahead.ClientExecution
  (Notification Return : Set) (notificationEq : DecidableEquality Notification) where

open import Data.Nat using (zero; suc)
open import Data.Bool using (true; false)
import Data.Bool.Properties as Bool
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Properties as List
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Product using (Σ-syntax; _,_; proj₁)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (_×-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
module ServerExecution = S.Executable notificationEq

-- A guard returns the independently specified target and its transition evidence.
checked : ∀ {s a t} {P : Set} → Dec P → (P → Step s a t) →
  Maybe (Σ[ u ∈ State ] Step s a u)
checked {t = t} (yes pr) build = just (t , build pr)
checked (no _) _ = nothing

-- Target computation ignores the particular proof of a successful guard.
checked-target : ∀ {s a t} {P : Set} (dec : Dec P) {build : P → Step s a t} →
  P → Maybe.map proj₁ (checked dec build) ≡ just t
checked-target (yes _) _ = refl
checked-target (no noP) pr = ⊥-elim (noP pr)

-- Visible execution preserves the Zero branch, exact selected reply and active guard.
lookup : (a : Action) (s : State) → Maybe (Σ[ t ∈ State ] Step s a t)
lookup (continue k) (client poll r js rs zero a q v) = just (_ , continueZero)
lookup (continue k) (client poll r js rs (suc n) a q v)
  with below (suc n) k Bool.≟ true
... | yes bound = just (_ , continueBelow bound)
... | no _ = checked ((below (suc n) k Bool.≟ false) ×-dec (positive a Bool.≟ true))
  (λ { (bound , arrived) → continueFull bound arrived })
lookup (terminate x) (client poll r js rs n a q v) = just (_ , stopRequested)
lookup sendRequest (client writingRequest r js rs n a q v) = just (_ , sentRequest)
lookup sendQuit (client (writingQuit false) r js rs zero a true (just x)) =
  just (_ , sentQuitIdle)
lookup sendQuit (client (writingQuit true) r js rs n a true (just x)) =
  just (_ , sentQuitBusy)
lookup (recvReply reply) (client m awaiting js rs n a q v) =
  checked (active m Bool.≟ true) receivedReply
lookup (handled reply) (client m (handling selected) js rs n a q v) =
  checked ((active m Bool.≟ true) ×-dec ServerExecution.replyEq selected reply)
    (λ { (am , refl) → delivered am })
lookup recvDone (client awaitDone r js rs zero a true (just x)) =
  just (_ , receivedDone)
lookup _ _ = nothing

-- Erase the certificate only after a successful certified lookup.
next : State → Action → Maybe State
next s a = Maybe.map proj₁ (lookup a s)

-- Boolean guard inconsistency cannot justify a source transition.
true-not-false : true ≡ false → Data.Empty.⊥
true-not-false ()

-- Lookup completeness retains the original guards instead of inventing new ones.
next-complete : ∀ {s a t} → Step s a t → next s a ≡ just t
next-complete continueZero = refl
next-complete (continueBelow {n = n} {k = k} bound) with below (suc n) k Bool.≟ true
... | yes _ = refl
... | no neq = ⊥-elim (neq bound)
next-complete (continueFull {n = n} {a = a} {k = k} bound arrived)
  with below (suc n) k Bool.≟ true
... | yes eq = ⊥-elim (true-not-false (trans (sym eq) bound))
... | no _ = checked-target ((below (suc n) k Bool.≟ false) ×-dec (positive a Bool.≟ true))
  (bound , arrived)
next-complete stopRequested = refl
next-complete sentRequest = refl
next-complete sentQuitIdle = refl
next-complete sentQuitBusy = refl
next-complete (receivedReply {m = m} pr) = checked-target (active m Bool.≟ true) pr
next-complete (delivered {m = m} {reply = reply} pr) =
  checked-target ((active m Bool.≟ true) ×-dec ServerExecution.replyEq reply reply) (pr , refl)
next-complete receivedDone = refl

-- Internal successors carry evidence rather than trusting a state-only interpreter.
Internal : State → Set
Internal s = Σ[ t ∈ State ] Tau s t

-- Independent main-thread effects are listed without serializing the receiver.
mainMoves : (s : State) → List (Internal s)
mainMoves (client issue r js rs n a q v) = (_ , registerResponse) ∷ []
mainMoves (client stopPending r js rs zero a q (just x)) = (_ , setStopIdle) ∷ []
mainMoves (client stopPending r js rs (suc n) a q (just x)) = (_ , setStopBusy) ∷ []
mainMoves (client registerQuit r js rs n a true (just x)) = (_ , registerMarker) ∷ []
mainMoves (client collectingMaybe r js [] (suc n) a q v) = (_ , optionalEmpty) ∷ []
mainMoves (client collectingMaybe r js (responseToken ∷ rs) (suc n) a q v) =
  (_ , optionalResult) ∷ []
mainMoves (client collectingWait r js (responseToken ∷ rs) (suc n) a q v) =
  (_ , blockingResult) ∷ []
mainMoves (client adjustCollected r js rs n a q v) = (_ , adjustArrival) ∷ []
mainMoves (client draining r js rs zero a true (just x)) = (_ , drained) ∷ []
mainMoves (client draining r js (token ∷ rs) (suc n) a true (just x)) =
  (_ , drainResult) ∷ []
mainMoves _ = []

-- A successful active-state guard retains its independent receiver transition.
internalWhen : ∀ {s t} {P : Set} → Dec P → (P → Tau s t) → List (Internal s)
internalWhen {t = t} (yes pr) build = (t , build pr) ∷ []
internalWhen (no _) _ = []

-- Receiver work remains available while the main thread is collecting or sending.
receiverMoves : (s : State) → List (Internal s)
receiverMoves (client m idle (responseJob ∷ js) rs n a q v) =
  internalWhen (active m Bool.≟ true) startResponse
receiverMoves (client m idle (quitMarker ∷ js) rs n a q v) =
  internalWhen (active m Bool.≟ true) startMarker
receiverMoves (client m (inspect reply) js rs n a false v) =
  internalWhen (active m Bool.≟ true) keepReply
receiverMoves (client m (inspect reply) js rs n a true v) =
  internalWhen (active m Bool.≟ true) discardReply
receiverMoves (client m bumpArrival js rs n a q v) =
  internalWhen (active m Bool.≟ true) countArrival
receiverMoves (client m (publish false) js rs n a q v) =
  internalWhen (active m Bool.≟ true) publishResponse
receiverMoves (client m (publish true) js rs n a q v) =
  internalWhen (active m Bool.≟ true) publishMarker
receiverMoves _ = []

-- The joint menu preserves both threads' enabled choices.
internalMoves : (s : State) → List (Internal s)
internalMoves s = mainMoves s ++ receiverMoves s

-- Erased targets are useful to both replay and finite native tree branching.
targets : State → List State
targets s = map proj₁ (internalMoves s)

-- Every enumerated target has independent source-model transition evidence.
target-sound : ∀ {s t} → t ∈ targets s → Tau s t
target-sound mem with ∈-map⁻ proj₁ mem
... | (u , pr) , member , refl = pr

-- Main targets embed in the combined menu irrespective of receiver work.
main-listed : ∀ {s t} → t ∈ map proj₁ (mainMoves s) → t ∈ targets s
main-listed {s} {t} mem =
  subst (t ∈_) (sym (List.map-++ proj₁ (mainMoves s) (receiverMoves s))) (∈-++⁺ˡ mem)

-- Receiver targets embed without imposing artificial main-thread priority.
receiver-listed : ∀ {s t} → t ∈ map proj₁ (receiverMoves s) → t ∈ targets s
receiver-listed {s} {t} mem =
  subst (t ∈_) (sym (List.map-++ proj₁ (mainMoves s) (receiverMoves s)))
    (∈-++⁺ʳ (map proj₁ (mainMoves s)) mem)

-- Guarded enumeration retains the target independently of proof identity.
guarded-listed : ∀ {s t} {P : Set} (dec : Dec P) {build : P → Tau s t} →
  P → t ∈ map proj₁ (internalWhen dec build)
guarded-listed (yes _) _ = here refl
guarded-listed (no noP) pr = ⊥-elim (noP pr)

-- No independent hidden client rule is omitted by the finite menu.
target-complete : ∀ {s t} → Tau s t → t ∈ targets s
target-complete {s = s} registerResponse = main-listed {s = s} (here refl)
target-complete {s = s} setStopIdle = main-listed {s = s} (here refl)
target-complete {s = s} setStopBusy = main-listed {s = s} (here refl)
target-complete {s = s} registerMarker = main-listed {s = s} (here refl)
target-complete {s = s} optionalEmpty = main-listed {s = s} (here refl)
target-complete {s = s} optionalResult = main-listed {s = s} (here refl)
target-complete {s = s} blockingResult = main-listed {s = s} (here refl)
target-complete {s = s} adjustArrival = main-listed {s = s} (here refl)
target-complete {s = s} drainResult = main-listed {s = s} (here refl)
target-complete {s = s} drained = main-listed {s = s} (here refl)
target-complete {s = s} (startResponse {m = m} pr) =
  receiver-listed {s = s} (guarded-listed (active m Bool.≟ true) pr)
target-complete {s = s} (startMarker {m = m} pr) =
  receiver-listed {s = s} (guarded-listed (active m Bool.≟ true) pr)
target-complete {s = s} (keepReply {m = m} pr) =
  receiver-listed {s = s} (guarded-listed (active m Bool.≟ true) pr)
target-complete {s = s} (discardReply {m = m} pr) =
  receiver-listed {s = s} (guarded-listed (active m Bool.≟ true) pr)
target-complete {s = s} (countArrival {m = m} pr) =
  receiver-listed {s = s} (guarded-listed (active m Bool.≟ true) pr)
target-complete {s = s} (publishResponse {m = m} pr) =
  receiver-listed {s = s} (guarded-listed (active m Bool.≟ true) pr)
target-complete {s = s} (publishMarker {m = m} pr) =
  receiver-listed {s = s} (guarded-listed (active m Bool.≟ true) pr)
