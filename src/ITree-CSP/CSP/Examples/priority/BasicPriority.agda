{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Priority "hello world": the POSITIVE demonstration of `Pri`.
--
-- With the order `a <ᵖ b` (b dominates a) and `P = a→Stop □ b→Stop`,
-- prioritisation PRUNES the dominated `a` and KEEPS the ≤-maximal `b`, so
-- `Pri O P` behaves exactly like `b→Stop` (strong bisimulation).  The same
-- `a` SURVIVES in `Pri O (a→Stop)` — where `b` is not on offer — showing that
-- `Pri` prunes context-sensitively (this is the flip side of PriSanity, the
-- NEGATIVE result: prioritisation is not refinement-monotone).
------------------------------------------------------------------------

open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; _×_; Σ-syntax; proj₁)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Level using (0ℓ)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Function using (case_of_)
open import Class.DecEq using (DecEq; DecEq-⊥)

open import Process_Trees

module CSP.Examples.priority.BasicPriority where

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
open import Semantics.Bisim    {E = Ch} {I = ExtI Ch}
open import Semantics.Refusals {E = Ch} {I = ExtI Ch} using (Offers)
open import CSP.Priority.Base       {0ℓ} {0ℓ} {Ch}
open import CSP.Priority.Closure Ch-≟
open import CSP.Operators Ch-≟
open import CSP.Priority.Tau {0ℓ} {0ℓ} {Ch}
  using (react-menu-∼; MaybeRel; mnothing; mjust)
open import CSP.Priority.Adequacy {0ℓ} {0ℓ} {Ch} using (no-steps-∼)

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
-- The two visible labels we observe.
------------------------------------------------------------------------

-- the visible label `a`
ℓa : Event√ ⊥
ℓa = evl (evLabel ⊤ a tt)

-- the visible label `b`
ℓb : Event√ ⊥
ℓb = evl (evLabel ⊤ b tt)

------------------------------------------------------------------------
-- A `Stop` node has no transition of any kind (stable, offers nothing).
------------------------------------------------------------------------

-- `Stop` is stuck: no √, no τ, no visible offer
Stop-stuck : ∀ {l} {t′ : PTree Ch (ExtI Ch) ⊥} → ¬ (Stop {R = ⊥} ─[ l ]─► t′)
Stop-stuck (sRet ())
Stop-stuck (sSil ())
Stop-stuck (sVis refl ())
Stop-stuck (sTau refl ())

------------------------------------------------------------------------
-- (1) CENTREPIECE — `Pri` keeps the maximal `b`, prunes the dominated `a`.
--
-- `Pri O P` offers ONLY `b` (its `a`-offer is pruned by the dominating `b`),
-- and after `b` it deadlocks — exactly `b→Stop`.  The residual bisimulation
-- `Pri O Stop ∼ Stop` holds because both are stuck.
------------------------------------------------------------------------

pri-picks-b : Pri O P fbP ∼ (b ⟶₀ Stop)
pri-picks-b = react-menu-∼ refl refl λ where
    (_ , a) tt → mnothing                                        -- a pruned on the left, ≠b on the right
    (_ , b) tt → mjust (no-steps-∼ pri-Stop-stuck Stop-stuck)    -- both fire b, residuals both stuck
  where
    -- the `b`-residual `Pri O Stop _` is stuck too (Stop offers nothing)
    pri-Stop-stuck : ∀ {l t′} → ¬ (_ ─[ l ]─► t′)
    pri-Stop-stuck (sRet ())
    pri-Stop-stuck (sSil ())
    pri-Stop-stuck (sVis refl ())
    pri-Stop-stuck (sTau refl ())

------------------------------------------------------------------------
-- (2) `Pri O P` KEEPS the maximal `b`.
------------------------------------------------------------------------

pri-keeps-b : Offers (Pri O P fbP) ℓb
pri-keeps-b = _ , sVis refl refl

------------------------------------------------------------------------
-- (3) `Pri O P` DROPS the dominated `a` (b is offered alongside).
------------------------------------------------------------------------

pri-drops-a : ¬ Offers (Pri O P fbP) ℓa
pri-drops-a (_ , sVis {v = v} eqf br) with react-injective eqf
... | veq , _ = case subst (λ w → w (⊤ , a) tt ≡ just _) (sym veq) br of λ ()

------------------------------------------------------------------------
-- (4) CONTEXT-SENSITIVITY — the SAME `a` SURVIVES when `b` is absent.
--
-- `Q = a→Stop` does not offer `b`, so `a` is ≤-maximal there and `Pri O Q`
-- keeps it.  Prioritisation prunes relative to the CURRENT menu.
------------------------------------------------------------------------

pri-Q-keeps-a : Offers (Pri O Q fbQ) ℓa
pri-Q-keeps-a = _ , sVis refl refl
