{-# OPTIONS --guardedness #-}

-- CERTIFICATION-ONLY axiom — DO NOT IMPORT outside the ClassicalFromLEM
-- soundness witnesses.
--
-- `dne` is double-negation elimination, equivalently the law of excluded
-- middle. Importing this module makes the importing module classical. It
-- exists ONLY so the ClassicalFromLEM certifier modules
-- (CSP.Laws.ClassicalFromLEM and Semantics.LTL.ClassicalFromLEM) can share a
-- single LEM axiom while proving their targeted postulates are "just classical
-- logic". Nothing in the actual development imports it, and nothing should.
--
-- Phrased with explicit `→ ⊥` (not `¬ ¬ A`) so it is robust to modules that
-- shadow stdlib `¬_` — e.g. the LTLᵗ `¬_` constructor in
-- Semantics.LTL.Traces_Based. Note `((A → ⊥) → ⊥) → A` is definitionally equal
-- to the stdlib `¬ ¬ A → A`, so existing `dne` uses need no change.

module Classical where

open import Level using (Level)
open import Data.Empty using (⊥)

postulate
  dne : ∀ {ℓa} {A : Set ℓa} → ((A → ⊥) → ⊥) → A
