{-# OPTIONS --guardedness #-}

-- open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
-- open import Data.Fin using (Fin; remQuot) renaming (zero to fzero; suc to fsuc)
-- open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
open import Data.Empty using (⊥)
-- open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; _×_)
-- open import Relation.Unary
open import Function using (case_of_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
-- open import Class.DecEq
open import Level using (Level)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Bool using (Bool; true; false; if_then_else_)

open import Interaction_Trees
open import CSP.Basic_Processes

module CSP.Iterate {ℓ ℓe} {E : Set ℓ → Set ℓe} (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where
open ITree

import CSP.Operators {ℓ} {ℓe} {E} as CSPOps
open CSPOps E-≟

-------------------------------------------------------------------------------------
-- Forever stateful loop
loop : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
  → HKTree E (ExtI I) A → KTree E (ExtI I) A R
loop {I = I} {A = A} {R = R} body a = iter step a
  where
    step : A → ITree E (ExtI I) (A ⊎ R)
    step a = body a >>= λ a' → Ret (inj₁ a')

-- Forever non-stateful loop
loop0 : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} 
  → (ITree E (ExtI I) ⊤) → ITree E (ExtI I) R
loop0 body = loop (λ _ → body) tt

-- Conditional loop
loopc : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (ITree E (ExtI I) ⊤) → ITree E (ExtI I) R
loopc body = loop (λ _ → body) tt

-- while loop
while : ∀ {ℓi} {I : Set ℓ → Set ℓi} {A : Set ℓ}
  → (A → Bool) → HKTree E (ExtI I) A → HKTree E (ExtI I) A
while {I = I} {A = A} cond body a = iter step a
  where
    step : A → ITree E (ExtI I) (A ⊎ A)
    step a = body a >>= λ a' → Ret (if cond a' then inj₁ a' else inj₂ a')
