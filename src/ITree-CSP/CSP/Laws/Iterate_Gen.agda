{-# OPTIONS --guardedness #-}

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; if_then_else_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Interaction_Trees
open import CSP.Definitions.Basic_Processes using (Ret)

module CSP.Laws.Iterate_Gen
  {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where

import CSP.Definitions.Operators {ℓ} {ℓe} {E} as CSPOps
open CSPOps E-≟ using (iter; iter-bind; _>>=_)

-- Iteration step generic in the result-tag function `h : A → A ⊎ R`.
genStep : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
        → (A → A ⊎ R) → HKTree E (ExtI I) A → A → ITree E (ExtI I) (A ⊎ R)
genStep h body a = body a >>= λ a' → Ret (h a')

genIter : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
        → (A → A ⊎ R) → HKTree E (ExtI I) A → A → ITree E (ExtI I) R
genIter h body a = iter (genStep h body) a

-- while's tag function.
whileTag : ∀ {A : Set ℓ} → (A → Bool) → A → A ⊎ A
whileTag cond a' = if cond a' then inj₁ a' else inj₂ a'
