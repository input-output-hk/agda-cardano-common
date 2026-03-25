{-# OPTIONS --guardedness #-}

open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
open import Data.Empty using (⊥)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; _×_)
open import Relation.Unary using (∅)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no)
-- open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Bool using (Bool; true; false; if_then_else_)

open import Interaction_Trees

module CSP.Basic_Processes where
open ITree
Stop : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi}
     → ITree E I (⊤ {ℓr})
force Stop = vis (λ _ _ → nothing)

Stop' : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      → ITree E I R
force Stop' = vis (λ _ _ → nothing)

Ret : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    → R → ITree E I R
force (Ret r) = ret r

Skip : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi}
     → ITree E I (⊤ {ℓr})
Skip = Ret tt

-- Tau: silent step
Tau : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    → ITree E I R → ITree E I R
force (Tau P) = sil P

{-
-- Divergent process: spins silently forever
div : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    → ITree E I R
force div = sil div
-}

guard : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi}
      → Bool → ITree E I (⊤ {ℓr})
guard b = if b then Skip else Stop

-- Accepts any visible event and loops
Run : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    → ITree E I R
force Run = vis (λ _ _ → just Run)

-- Accepts only visible events satisfying predicate es, loops on those
Run′ : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
     → (es  : AnyTypes E → Set)
     → (dec : (at : AnyTypes E) → Dec (es at))
     → ITree E I R
force (Run′ es dec) = vis λ at _ →
  case dec at of λ where
    (yes _) → just (Run′ es dec)
    (no  _) → nothing
