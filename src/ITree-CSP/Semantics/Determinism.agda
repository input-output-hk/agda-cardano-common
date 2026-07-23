{-# OPTIONS --guardedness #-}

-- Determinism of a process: no reachable state both accepts and (stably)
-- refuses the same event after the same trace.  Standard CSP failures
-- characterisation, over the existing `traces`/`failures` machinery.

open import Level using (_⊔_) renaming (suc to lsuc)
open import Data.List using (List; _∷ʳ_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Process_Trees

module Semantics.Determinism {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where

open import Semantics.LTS      {ℓ} {ℓe} {ℓi} {E} {I} using (Event√)
open import Semantics.Failures {ℓ} {ℓe} {ℓi} {E} {I} using (traces; failures)

-- P is deterministic iff there is no trace s and event a such that
-- s ⌢ ⟨a⟩ is a trace AND some stable state reached by s refuses a.
Deterministic : ∀ {ℓr} {R : Set ℓr} → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
Deterministic {R = R} P =
  ∀ {s : List (Event√ R)} {a : Event√ R}
  → traces P (s ∷ʳ a)
  → ¬ failures P s (λ e → e ≡ a)
