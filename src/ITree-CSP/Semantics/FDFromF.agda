{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- `⊑F→⊑FD-df`: a stable-failures refinement plus divergence-freedom of
-- the implementation upgrades to failures-divergences refinement.
--
-- `_⊑FD_` is `_⊇F⊥_ × _⊇D_` (`Semantics/FailuresDivergences`:85-86) and
-- `failures⊥ Q s B` is `failures Q s B ⊎ divergences Q s` (:76).  So when the
-- REFINED / RIGHT (implementation) operand `Q` cannot diverge, the `inj₂`
-- disjunct of every `failures⊥ Q` is refutable and the whole `_⊇D_` component
-- is vacuous: both halves fall out of the `_⊑F_` hypothesis plus `⊥-elim`.
-- Fully constructive: no classical input, nothing assumed.
--
-- Kept OUT of `FailuresDivergences.agda` so its ~58 consumers stay untouched.
------------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_)

open import Process_Trees

module Semantics.FDFromF
  {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where

open import Semantics.Failures            {ℓ} {ℓe} {ℓi} {E} {I}
  using (_⊑F_)
open import Semantics.FailuresDivergences {ℓ} {ℓe} {ℓi} {E} {I}
  using (divergences; failures⊥; _⊇F⊥_; _⊇D_; _⊑FD_)

-- a divergence-free RHS makes the `⊇D` component of `⊑FD` vacuous
df→⊇D : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R}
      → (∀ {s} → ¬ divergences Q s) → P ⊇D Q
df→⊇D nd dQ = ⊥-elim (nd dQ)

-- with a divergence-free RHS, `failures⊥ Q` collapses to plain failures of `Q`
-- (the `inj₂` divergence disjunct is refuted), so `⊑F` gives the `⊇F⊥` component.
-- Only the FAILURES half (`proj₂`) of the `⊑F` hypothesis is consumed — `_⊇F⊥_` has no
-- trace component for the `⊑T` half to feed.
⊑F→⊇F⊥-df : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R}
          → P ⊑F Q → (∀ {s} → ¬ divergences Q s) → P ⊇F⊥ Q
⊑F→⊇F⊥-df f nd (inj₁ fQ) = inj₁ (proj₂ f _ _ fQ)
⊑F→⊇F⊥-df f nd (inj₂ dQ) = ⊥-elim (nd dQ)

-- a `⊑F` refinement whose RHS (implementation) cannot diverge is a `⊑FD` refinement
⊑F→⊑FD-df : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R}
          → P ⊑F Q → (∀ {s} → ¬ divergences Q s) → P ⊑FD Q
⊑F→⊑FD-df f nd = ⊑F→⊇F⊥-df f nd , df→⊇D nd
