{-# OPTIONS --guardedness #-}

------------------------------------------------------------
-- Concrete `Realisable` witnesses + hypothesis-free corollaries.
--
-- `⊨-DRWB-invariant→` (WBisimInvariant) is gated by a `Realisable R`
-- record (decidable τ-progress + convergence-at-stuck).  This module
-- shows the record is genuinely dischargeable — it is not a vacuous
-- side-condition — by exhibiting a witness for the τ-free model class
-- and deriving an invariance corollary that carries no `Realisable`
-- premise.
--
-- τ-FREE class: a model where no state has a τ-transition (e.g. the
-- deterministic external-choice / prefix fragment: no internal choice,
-- no hiding, no sil).  There both `Realisable` fields are immediate:
--   • τprog s = inj₂ (no τ-step) — τ-progress is trivially decided;
--   • conv    = cvg (absurd on the impossible τ-step) — every state
--     converges because it cannot even start a τ-run.
------------------------------------------------------------

open import Level using (Level)
open import Data.Sum using (inj₂)
open import Data.Empty using (⊥; ⊥-elim)

open import Process_Trees

module Semantics.LTL.RealisableInstances
  {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where

open PTree

open import Semantics.LTS              {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.DRBisim          {ℓ} {ℓe} {ℓi} {E} {I} using (_≈DR_)
open import Semantics.LTL.FrameSim     {ℓ} {ℓe} {ℓi} {E} {I} using (BisimStable)
open import Semantics.LTL.Convergence  {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.LTL.WTrace       {ℓ} {ℓe} {ℓi} {E} {I} using (_⊨ᵂ_)
open import Semantics.LTL.WBisimInvariant {ℓ} {ℓe} {ℓi} {E} {I} using (⊨-DRWB-invariant→)

open import Semantics.LTL.Traces_Based {ℓ} {ℓe} {ℓi} {E} {I} using (LTLᵗ)

------------------------------------------------------------
-- §1 τ-free models are Realisable.
------------------------------------------------------------

-- A model on result type `R` is τ-free when no state ever offers a τ.
TauFree : ∀ {ℓr} (R : Set ℓr) → Set _
TauFree R = ∀ {s t′ : PTree E I R} → s ─[ τ ]─► t′ → ⊥

τfree-Realisable : ∀ {ℓr} {R : Set ℓr} → TauFree R → Realisable R
τprog (τfree-Realisable tf) s   = inj₂ (λ st → tf st)
conv  (τfree-Realisable tf) _ _ = cvg (λ st → ⊥-elim (tf st))

------------------------------------------------------------
-- §2 Hypothesis-free invariance corollary for τ-free models.
--
-- No `Realisable` premise: the τ-freeness of the model discharges it.
------------------------------------------------------------

⊨-DRWB-invariant-τfree→ : ∀ {ℓr ℓa} {R : Set ℓr}
                            {t₁ t₂ : PTree E I R} {φ : LTLᵗ ℓa R}
                          → TauFree R → t₁ ≈DR t₂ → BisimStable φ
                          → t₁ ⊨ᵂ φ → t₂ ⊨ᵂ φ
⊨-DRWB-invariant-τfree→ tf = ⊨-DRWB-invariant→ (τfree-Realisable tf)
