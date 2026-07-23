{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- Constructive accessibility under τ-steps.
--
-- `τ-Acc t` is the (inductive) accessibility predicate for the *backwards*
-- τ-transition relation: `t` is τ-accessible iff every τ-successor is.  It is
-- the well-foundedness certificate that τ-normalisation of a process
-- TERMINATES; unlike a postulated divergence-freedom hypothesis it REDUCES, so
-- it can drive well-founded recursion (this is Layer 3's whole point).
--
-- Generic: depends only on `Process_Trees` and `Semantics.LTS`.  `--safe`, 0
-- postulates.
------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Product using (Σ; _,_)
open import Relation.Nullary using (¬_)
open import Process_Trees

module Semantics.TauAcc {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where

open import Semantics.LTS {ℓ} {ℓe} {ℓi} {E} {I}

-- τ-accessibility: every τ-successor is again τ-accessible (backwards WF).
data τ-Acc {ℓr} {R : Set ℓr} (t : PTree E I R) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  acc : (∀ {t′} → t ─[ τ ]─► t′ → τ-Acc t′) → τ-Acc t

-- follow a τ-step into the sub-accessibility (the accessor)
accSub : ∀ {ℓr} {R : Set ℓr} {t t′ : PTree E I R} → τ-Acc t → t ─[ τ ]─► t′ → τ-Acc t′
accSub (acc f) st = f st

-- τ-accessible ⇒ no infinite τ-sequence (`Diverges` imported from LTS);
-- well-foundedness rules out divergence
τ-Acc→¬Div : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R} → τ-Acc t → ¬ Diverges t
τ-Acc→¬Div (acc f) d = τ-Acc→¬Div (f (Diverges.step d)) (Diverges.rest d)
