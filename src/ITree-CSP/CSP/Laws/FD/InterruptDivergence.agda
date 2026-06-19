{-# OPTIONS --guardedness #-}

-- Direct postulate (the interrupt König step).  Certified sound from `dne` in
-- CSP.Laws.ClassicalFromLEM (`△-Diverges→`); kept as a direct postulate here,
-- mirroring □-/▷-Diverges→ in ExtChoiceDivergence.
--
-- A divergence (infinite τ-livelock) of an interrupt P △ Q is a divergence of one of
-- the two operands.  The interrupt has the SAME silent structure as external choice
-- (both operands run concurrently, τ-steps are interleaved), so the same classical
-- infinite-pigeonhole step that justifies □-Diverges→ / ▷-Diverges→ justifies this:
-- an infinite τ-chain of P △ Q projects, by König's lemma, to an infinite τ-chain of P
-- or of Q.  Stated DIRECTLY here (not via `dne`), exactly as ExtChoiceDivergence does.

open import Data.Sum using (_⊎_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Process_Trees

module CSP.Laws.FD.InterruptDivergence {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open import CSP.Operators E-≟ using (_△_)
open import Semantics.DRBisim {E = E} {I = ExtI E} using (Diverges)

postulate
  △-Diverges→ : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E (ExtI E) R}
              → Diverges (P △ Q) → Diverges P ⊎ Diverges Q
