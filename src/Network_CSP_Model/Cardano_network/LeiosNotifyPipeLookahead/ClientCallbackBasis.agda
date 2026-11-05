{-# OPTIONS --safe #-}

-- Finite exact targets for erased successful client callbacks, at unit return.
module Cardano_network.LeiosNotifyPipeLookahead.ClientCallbackBasis
  (Notification : Set) where

open import Data.Bool using (true; false)
import Data.Bool.Properties as Bool
open import Data.Empty using (⊥-elim)
open import Data.Integer using (+_; +<+)
open import Data.Integer.Properties using () renaming (_<?_ to compareInteger)
open import Data.List using (List; []; _∷_; _++_; map)
import Data.List.Properties as List
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (does)
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S

-- Callback labels are existentially hidden, while their target state is exact.
Callback : C.State → C.State → Set
Callback s t = Σ[ action ∈ C.Action ] (D.ClientCallback action × C.Step s action t)

-- A true proposition makes the boolean component of its decision true.
decision-true : ∀ {A : Set} (decision : Dec A) → A → does decision ≡ true
decision-true (yes _) _ = refl
decision-true (no absent) proof = ⊥-elim (absent proof)

-- One above the current counter always selects the below-bound branch.
below-high : ∀ n → C.below n (+ (suc n)) ≡ true
below-high n = decision-true (compareInteger (+ n) (+ (suc n))) (+<+ ≤-refl)

-- Zero never exceeds the nonnegative pipeline counter.
below-low : ∀ n → C.below n (+ zero) ≡ false
below-low n = refl

-- Every enumerated callback retains its independent source rule.
Move : C.State → Set
Move s = Σ[ target ∈ C.State ] Callback s target

-- An arbitrary signed depth has only Zero, below-bound and full target shapes.
continueMoves : (s : C.State) → List (Move s)
continueMoves (C.client C.poll r js rs zero a q v) =
  (_ , C.continue (+ zero) , D.continue , C.continueZero) ∷ []
continueMoves (C.client C.poll r js rs (suc n) a q v)
  with C.positive a Bool.≟ true
... | yes arrived =
  (_ , C.continue (+ (suc (suc n))) , D.continue , C.continueBelow (below-high (suc n))) ∷
  (_ , C.continue (+ zero) , D.continue , C.continueFull (below-low (suc n)) arrived) ∷ []
... | no _ =
  (_ , C.continue (+ (suc (suc n))) , D.continue , C.continueBelow (below-high (suc n))) ∷ []
continueMoves _ = []

-- The named unit-return profile has exactly one termination value to retain.
terminateMoves : (s : C.State) → List (Move s)
terminateMoves (C.client C.poll r js rs n a q v) =
  (_ , C.terminate tt , D.terminate , C.stopRequested) ∷ []
terminateMoves _ = []

-- A successful handler returns only the exact currently selected reply.
handledMoves : (s : C.State) → List (Move s)
handledMoves (C.client m (C.handling reply) js rs n a q v)
  with C.active m Bool.≟ true
... | yes active = (_ , C.handled reply , D.handled , C.delivered active) ∷ []
... | no _ = []
handledMoves _ = []

-- The callback menu preserves concurrent main-thread and receiver alternatives.
moves : (s : C.State) → List (Move s)
moves s = continueMoves s ++ (terminateMoves s ++ handledMoves s)

-- Erase certificates only after retaining a finite list of actual source moves.
targets : C.State → List C.State
targets s = map proj₁ (moves s)

-- Every listed target is an actual erased callback successor.
sound : ∀ {s t} → t ∈ targets s → Callback s t
sound member with ∈-map⁻ proj₁ member
... | (_ , proof) , _ , refl = proof

-- Main continuation alternatives embed without excluding handler progress.
continue-listed : ∀ {s t} → t ∈ map proj₁ (continueMoves s) → t ∈ targets s
continue-listed {s} {t} member =
  subst (t ∈_) (sym (List.map-++ proj₁ (continueMoves s) (terminateMoves s ++ handledMoves s)))
    (∈-++⁺ˡ member)

-- Termination alternatives remain available beside both other callback menus.
terminate-listed : ∀ {s t} → t ∈ map proj₁ (terminateMoves s) → t ∈ targets s
terminate-listed {s} {t} member =
  subst (t ∈_) (sym (List.map-++ proj₁ (continueMoves s) (terminateMoves s ++ handledMoves s)))
    (∈-++⁺ʳ (map proj₁ (continueMoves s))
      (subst (t ∈_) (sym (List.map-++ proj₁ (terminateMoves s) (handledMoves s)))
        (∈-++⁺ˡ member)))

-- Receiver callback progress does not impose an artificial main-thread priority.
handled-listed : ∀ {s t} → t ∈ map proj₁ (handledMoves s) → t ∈ targets s
handled-listed {s} {t} member =
  subst (t ∈_) (sym (List.map-++ proj₁ (continueMoves s) (terminateMoves s ++ handledMoves s)))
    (∈-++⁺ʳ (map proj₁ (continueMoves s))
      (subst (t ∈_) (sym (List.map-++ proj₁ (terminateMoves s) (handledMoves s)))
        (∈-++⁺ʳ (map proj₁ (terminateMoves s)) member)))

-- The always-enabled positive-counter branch is listed for either arrival decision.
below-listed : ∀ {r js rs n a q v} →
  C.client C.collectingMaybe r js rs (suc n) a q v ∈
    map proj₁ (continueMoves (C.client C.poll r js rs (suc n) a q v))
below-listed {a = a} with C.positive a Bool.≟ true
... | yes _ = here refl
... | no _ = here refl

-- A true arrival guard includes the full-collection target as the second choice.
full-listed : ∀ {r js rs n a q v} → C.positive a ≡ true →
  C.client C.collectingWait r js rs (suc n) a q v ∈
    map proj₁ (continueMoves (C.client C.poll r js rs (suc n) a q v))
full-listed {a = a} arrived with C.positive a Bool.≟ true
... | yes _ = there (here refl)
... | no absent = ⊥-elim (absent arrived)

-- Active handler completion contributes precisely its selected source target.
handler-listed : ∀ {m reply js rs n a q v} → C.active m ≡ true →
  C.client m C.bumpArrival js rs n a q v ∈
    map proj₁ (handledMoves (C.client m (C.handling reply) js rs n a q v))
handler-listed {m = m} active with C.active m Bool.≟ true
... | yes _ = here refl
... | no absent = ⊥-elim (absent active)

-- Every arbitrary signed callback choice reaches one of the listed exact states.
complete : ∀ {s t} → Callback s t → t ∈ targets s
complete {s} (_ , D.continue , C.continueZero) = continue-listed {s} (here refl)
complete {s} (_ , D.continue , C.continueBelow _) = continue-listed {s} below-listed
complete {s} (_ , D.continue , C.continueFull _ arrived) = continue-listed {s} (full-listed arrived)
complete {s} (C.terminate tt , D.terminate , C.stopRequested) = terminate-listed {s} (here refl)
complete {s} (_ , D.handled , C.delivered active) = handled-listed {s} (handler-listed active)

-- Embedding a callback changes only the paired driver's client component.
lift : (contract : S.Contract) (s : D.State) → Move (D.clientState s) →
  Σ[ target ∈ D.State ] D.Tau contract s target
lift contract (D.pair c server cs sc pc ps rc rs) (target , action , classification , step) =
  D.pair target server cs sc pc ps rc rs , D.clientCallback classification step

-- The paired product has a finite exact menu for its clientCallback rule family.
driverMoves : (contract : S.Contract) (s : D.State) →
  List (Σ[ target ∈ D.State ] D.Tau contract s target)
driverMoves contract s = map (lift contract s) (moves (D.clientState s))

-- These are callback targets only; server callbacks and other hidden moves stay separate.
driverTargets : S.Contract → D.State → List D.State
driverTargets contract s = map proj₁ (driverMoves contract s)

-- Every enumerated paired target is backed by an actual hidden driver step.
driver-sound : ∀ {contract s t} → t ∈ driverTargets contract s → D.Tau contract s t
driver-sound member with ∈-map⁻ proj₁ member
... | (_ , step) , _ , refl = step

-- No arbitrary client callback target of the unit-return driver is omitted.
driver-complete : ∀ {contract c target server cs sc pc ps rc rs action} →
  D.ClientCallback action → C.Step c action target →
  D.pair target server cs sc pc ps rc rs ∈
    driverTargets contract (D.pair c server cs sc pc ps rc rs)
driver-complete {contract} {c} {target} {server} {cs} {sc} {pc} {ps} {rc} {rs} {action}
  classification step with ∈-map⁻ proj₁ (complete (action , classification , step))
... | (_ , proof) , member , refl = ∈-map⁺ proj₁
  (∈-map⁺ (lift contract (D.pair c server cs sc pc ps rc rs)) member)
