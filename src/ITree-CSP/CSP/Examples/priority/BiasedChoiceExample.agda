{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Demonstration of LEFT-biased external choice `_⊲_` (from CSP.Priority.BiasedChoice).
--
-- Two disjoint ⊤-channels `hi` (P's) and `lo` (Q's); `P = hi→Stop`,
-- `Q = lo→Stop`, preferred set `Hchs = [hi]`.  Then `P ⊲ Q`:
--   * PRUNES `lo` — Q's offer is suppressed because P concurrently offers the
--     dominating `hi`;
--   * KEEPS `hi` — the preferred side's event survives.
-- Context-sensitivity punchline: `Stop ⊲ Q` (P offers nothing) STILL offers
-- `lo` — the bias only suppresses Q when P actually competes.
------------------------------------------------------------------------

open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; proj₁; Σ-syntax)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Level using (0ℓ)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Function using (case_of_)
open import Class.DecEq using (DecEq; DecEq-⊥)

open import Process_Trees

module CSP.Examples.priority.BiasedChoiceExample where

-- event alphabet: preferred channel `hi`, non-preferred `lo` (both ⊤-carried)
data Ch : Set → Set where
  hi : Ch ⊤
  lo : Ch ⊤

-- decidable equality on the (channel) events
Ch-≟ : (x y : AnyTypes Ch) → Dec (x ≡ y)
Ch-≟ (_ , hi) (_ , hi) = yes refl
Ch-≟ (_ , lo) (_ , lo) = yes refl
Ch-≟ (_ , hi) (_ , lo) = no λ ()
Ch-≟ (_ , lo) (_ , hi) = no λ ()

open import Semantics.LTS       {E = Ch} {I = ExtI Ch}
open import Semantics.Refusals  {E = Ch} {I = ExtI Ch} using (Offers)
open import CSP.Priority.Base        {0ℓ} {0ℓ} {Ch} using (FinBr)
open import CSP.Priority.Closure Ch-≟
open import CSP.Priority.Channel Ch-≟
open import CSP.Operators Ch-≟
open import CSP.Priority.BiasedChoice Ch-≟

------------------------------------------------------------------------
-- Preferred channel set and processes.
------------------------------------------------------------------------

-- P prefers `hi`
Hchs : List (AnyTypes Ch)
Hchs = (⊤ , hi) ∷ []

-- the preferred channel `hi` carries ⊤, hence inhabited
Hchs-inh : ∀ {c} → c ∈ Hchs → proj₁ c
Hchs-inh (here refl) = tt

-- P offers hi, Q offers lo (disjoint channels)
P Q : PTree Ch (ExtI Ch) ⊥
P = hi ⟶₀ Stop
Q = lo ⟶₀ Stop

fbP : FinBr P
fbP = finBr-prefix₀ finBr-Stop
fbQ : FinBr Q
fbQ = finBr-prefix₀ finBr-Stop

-- the LEFT-biased choice (prefer P)
P⊲Q : PTree Ch (ExtI Ch) ⊥
P⊲Q = _⊲_ ⦃ DecEq-⊥ ⦄ {Pchs = Hchs} {Pchs-inh = Hchs-inh} P Q {fbP = fbP} {fbQ = fbQ}

------------------------------------------------------------------------
-- The two visible labels.
------------------------------------------------------------------------

-- the preferred label `hi`
ℓhi : Event√ ⊥
ℓhi = evl (evLabel ⊤ hi tt)

-- the non-preferred label `lo`
ℓlo : Event√ ⊥
ℓlo = evl (evLabel ⊤ lo tt)

------------------------------------------------------------------------
-- LEFT-BIAS demonstrations.
------------------------------------------------------------------------

-- `lo` is pruned: P concurrently offers the dominating `hi`
bias-prunes-lo : ¬ Offers P⊲Q ℓlo
bias-prunes-lo (_ , sVis {v = v} eqf br) with react-injective eqf
... | veq , _ = case subst (λ w → w (⊤ , lo) tt ≡ just _) (sym veq) br of λ ()

-- the preferred `hi` survives
bias-keeps-hi : Offers P⊲Q ℓhi
bias-keeps-hi = _ , sVis refl refl

-- CONTEXT-SENSITIVITY: with `Stop` on the left (no competition), `lo` survives
Stop⊲Q : PTree Ch (ExtI Ch) ⊥
Stop⊲Q = _⊲_ ⦃ DecEq-⊥ ⦄ {Pchs = Hchs} {Pchs-inh = Hchs-inh} Stop Q {fbP = finBr-Stop} {fbQ = fbQ}

bias-Stop-keeps-lo : Offers Stop⊲Q ℓlo
bias-Stop-keeps-lo = _ , sVis refl refl
