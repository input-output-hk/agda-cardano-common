{-# OPTIONS --guardedness #-}

-- Postulate 2 of the FD layer, the "König step", stated DIRECTLY (not via `dne`):
-- a divergence of an external choice is a divergence of one operand.
--
-- This is the second (and only other) classical postulate of the development; the
-- failures half of the ≈DR ⟹ ≈FD bridge already admits the first
-- (`¬-divergent→normal`, in Semantics.DRImpliesFD).  Both are CERTIFIED sound —
-- derivable from a single double-negation-elimination axiom — in the standalone module
-- CSP.Laws.ClassicalFromLEM (which nothing imports, so no axiom leaks here).
--
-- It is the foundation for the external-choice FD/divergence laws (□-idem, □-assoc,
-- □-over-⊓, □-monotonicity-⊇D, …); deciding which operand carries an infinite τ-livelock
-- is the classical infinite-pigeonhole step (see docs/notes/fd-classical-postulates.md).

open import Data.Sum using (_⊎_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Class.DecEq using (DecEq)

open import Process_Trees

module CSP.Laws.FD.ExtChoiceDivergence {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open import CSP.Operators E-≟ using (_□_; _▷_)
open import Semantics.DRBisim {E = E} {I = ExtI E} using (Diverges)

postulate
  □-Diverges→ : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R}
              → Diverges (P □ Q) → Diverges P ⊎ Diverges Q
  -- the sliding-choice analogue, needed for the ▷-slide states that appear when an
  -- operand of □ terminates; certified sound (from `dne`, via `▷-no-inf`) in ClassicalFromLEM
  ▷-Diverges→ : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E (ExtI E) R}
              → Diverges (P ▷ Q) → Diverges P ⊎ Diverges Q
