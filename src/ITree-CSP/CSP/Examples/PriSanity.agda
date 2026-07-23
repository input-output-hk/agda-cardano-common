{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Priority sanity: `Pri` is NOT ⊑T-/⊑FD-monotone — BY DESIGN.
--
-- This certifies the RT/FL congruence floor: prioritisation is a
-- congruence for STRONG bisimulation (see CSP/Laws/Bisim/PriCong.agda) but
-- does NOT preserve trace/failures-divergences REFINEMENT.  Concretely, with
-- the order `a <ᵖ b` (b dominates a):
--   P = a→Stop □ b→Stop ,  Q = a→Stop
-- We have `P ⊑T Q` (Q's traces ⊆ P's traces — Q is just a □-branch of P), yet
-- `Pri O P` prunes the dominated `a` (b is offered alongside) and behaves as
-- `b→Stop`, while `Pri O Q` keeps `a` (b is NOT offered), so `Pri O Q` still
-- offers `a`.  Hence `¬ (Pri O P ⊑T Pri O Q)` — refinement is destroyed.
------------------------------------------------------------------------

open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; _×_; Σ-syntax; proj₁)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Level using (0ℓ) renaming (suc to lsuc)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Class.DecEq using (DecEq; DecEq-⊥)

open import Process_Trees

module CSP.Examples.PriSanity where

-- event alphabet: two ⊤-carried channels `a`, `b` (⊤ carrier ⇒ they fire)
data Ch : Set → Set where
  a : Ch ⊤
  b : Ch ⊤

-- decidable equality on the (channel) events
Ch-≟ : (x y : AnyTypes Ch) → Dec (x ≡ y)
Ch-≟ (_ , a) (_ , a) = yes refl
Ch-≟ (_ , b) (_ , b) = yes refl
Ch-≟ (_ , a) (_ , b) = no λ ()
Ch-≟ (_ , b) (_ , a) = no λ ()

open import Semantics.PriOrder {0ℓ} {0ℓ} {Ch}
open import Semantics.LTS      {E = Ch} {I = ExtI Ch}
open import Semantics.Failures {E = Ch} {I = ExtI Ch}
open import CSP.Priority.Base       {0ℓ} {0ℓ} {Ch}
open import CSP.Priority.Closure Ch-≟
open import CSP.Operators Ch-≟
open import CSP.Laws.Traces.TraceLawsExtChoice Ch-≟ using (⊑ᵀ-□-L)

------------------------------------------------------------------------
-- The priority order  a <ᵖ b  (b strictly dominates a; nothing else).
------------------------------------------------------------------------

-- strict order: only `a ◃ b`
_◃_ : Ev → Ev → Set
((_ , a) ∙ _) ◃ ((_ , b) ∙ _) = ⊤
_             ◃ _             = ⊥

◃-irrefl : ∀ {e} → ¬ (e ◃ e)
◃-irrefl {(_ , a) ∙ _} ()
◃-irrefl {(_ , b) ∙ _} ()

◃-trans : ∀ {x y z} → x ◃ y → y ◃ z → x ◃ z
◃-trans {(_ , b) ∙ _}               ()
◃-trans {(_ , a) ∙ _} {(_ , a) ∙ _} ()
◃-trans {(_ , a) ∙ _} {(_ , b) ∙ _} _ ()

-- strict dominators: `above a = [b]`, everything else maximal (`[]`)
above′ : Ev → List Ev
above′ ((_ , a) ∙ _) = ((⊤ , b) ∙ tt) ∷ []
above′ _             = []

above′-sound : ∀ {e b′} → b′ ∈ above′ e → e ◃ b′
above′-sound {(_ , a) ∙ _} (here refl) = tt
above′-sound {(_ , b) ∙ _} ()

above′-complete : ∀ {e b′} → e ◃ b′ → b′ ∈ above′ e
above′-complete {(_ , a) ∙ _} {(_ , b) ∙ _} _ = here refl

-- the finitary priority order
O : PriOrder 0ℓ
O = record
  { prop  = record { _<ᵖ_ = _◃_ ; <ᵖ-irrefl = ◃-irrefl ; <ᵖ-trans = ◃-trans }
  ; above = above′
  ; above-sound = above′-sound
  ; above-complete = above′-complete
  }

------------------------------------------------------------------------
-- The two processes and their finite-branching certificates.
------------------------------------------------------------------------

-- P offers BOTH a and b; Q offers only a
P : PTree Ch (ExtI Ch) ⊥
P = _□_ ⦃ DecEq-⊥ ⦄ (a ⟶₀ Stop) (b ⟶₀ Stop)

Q : PTree Ch (ExtI Ch) ⊥
Q = a ⟶₀ Stop

fbP : FinBr P
fbP = finBr-□ ⦃ DecEq-⊥ ⦄ (finBr-prefix₀ finBr-Stop) (finBr-prefix₀ finBr-Stop)

fbQ : FinBr Q
fbQ = finBr-prefix₀ finBr-Stop

------------------------------------------------------------------------
-- (1) The refinement holds BEFORE prioritising: `P ⊑T Q`  (Q ⊆ P as a □-branch).
------------------------------------------------------------------------

refines : P ⊑T Q
refines = ⊑ᵀ-□-L ⦃ DecEq-⊥ ⦄ (a ⟶₀ Stop) (b ⟶₀ Stop)

------------------------------------------------------------------------
-- (2) Prioritisation DESTROYS the refinement: ¬ (Pri O P ⊑T Pri O Q).
------------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Function using (case_of_)

-- the visible label `a`, and the singleton trace ⟨a⟩
ℓa : Event√ ⊥
ℓa = evl (evLabel ⊤ a tt)

sa : List (Event√ ⊥)
sa = ℓa ∷ []

-- Pri O Q fires `a` (a is NOT dominated — Q does not offer b)
PriQ-fires-a : Σ[ u ∈ PTree Ch (ExtI Ch) ⊥ ] (Pri O Q fbQ ─[ ev ℓa ]─► u)
PriQ-fires-a = _ , sVis refl refl

-- Pri O P does NOT fire `a` (a IS dominated — P offers b alongside, so
-- `priVis` prunes it: `force (Pri O P fbP)` computes to a react whose vis-map
-- is `nothing` at `a`).  `eqf` exposes that map, then `br` is refuted.
PriP-no-a : ¬ (Σ[ u ∈ PTree Ch (ExtI Ch) ⊥ ] (Pri O P fbP ─[ ev ℓa ]─► u))
PriP-no-a (_ , sVis {v = v} eqf br) with react-injective eqf
... | veq , _ = case subst (λ w → w (⊤ , a) tt ≡ just _) (sym veq) br of λ ()

-- Pri O P is stable: no τ-step (react node with everywhere-`nothing` τc)
PriP-no-τ : ¬ (Σ[ u ∈ PTree Ch (ExtI Ch) ⊥ ] (Pri O P fbP ─[ τ ]─► u))
PriP-no-τ (_ , sSil eqf)                    = sil≢react (sym eqf)
PriP-no-τ (_ , sTau {i = i} {a = a′} eqf br) with react-injective eqf
... | _ , τceq = case subst (λ w → w i a′ ≡ just _) (sym τceq) br of λ ()

-- ⟨a⟩ IS a trace of Pri O Q
traces-PriQ-a : traces (Pri O Q fbQ) sa
traces-PriQ-a with PriQ-fires-a
... | u , st = u , ⟹-ev st ⟹-refl

-- ⟨a⟩ is NOT a trace of Pri O P (stable ⇒ no leading τ; `a` pruned ⇒ no a-step)
¬traces-PriP-a : ¬ traces (Pri O P fbP) sa
¬traces-PriP-a (_ , ⟹-ev step _) = PriP-no-a (_ , step)
¬traces-PriP-a (_ , ⟹-τ  step _) = PriP-no-τ (_ , step)

-- MAIN: the pre-Pri refinement `P ⊑T Q` is NOT preserved by prioritisation.
not-mono : ¬ (Pri O P fbP ⊑T Pri O Q fbQ)
not-mono h = ¬traces-PriP-a (h sa traces-PriQ-a)
