{-# OPTIONS --guardedness #-}

-- FD-equivalence algebraic laws for internal choice ⊓.
--   • ⊓-comm  is a STRONG-bisim law  ⇒ lift via sbisim→drbisim ∘ drbisim→≈FD.
--   • ⊓-idem  is only a WEAK law (the τ to the operand must be absorbed) ⇒ proved
--     directly on DRbisim, then to ≈FD.
-- (⊓-assoc is neither a strong NOR a weak bisim law — the intermediate (P⊓Q) node
--  has no bisimilar partner on the P⊓(Q⊓R) side — so it needs the FD-direct route
--  via failures/divergences set-equality; not done here.)

open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Process_Trees

module CSP.Laws.FD.FDLawsIChoice {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators            E-≟
open import Semantics.LTS                 {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.WeakBisim           {E = E} {I = ExtI E}
open import Semantics.DRBisim             {E = E} {I = ExtI E}
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_≈FD_)
open import Semantics.DRImpliesFD     {E = E} {I = ExtI E} using (drbisim→≈FD)
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import CSP.Laws.Bisim.Laws         E-≟ using (⊓-comm; ⊓-τ-inv; ⊓-stepL; ⊓-stepR)

-------------------------------------------------------------------------------------
-- Commutativity:  P ⊓ Q ≈FD Q ⊓ P   (lifted from the strong-bisim law)
-------------------------------------------------------------------------------------

⊓-comm-FD : ∀ {ℓr} {R : Set ℓr} (P Q : PTree E (ExtI E) R) → (P ⊓ Q) ≈FD (Q ⊓ P)
⊓-comm-FD P Q = drbisim→≈FD (sbisim→drbisim (⊓-comm P Q))

-------------------------------------------------------------------------------------
-- Idempotence:  P ⊓ P ≈FD P   (a genuinely weak law — proved on DRbisim)
-------------------------------------------------------------------------------------

⊓-idem-DR : ∀ {ℓr} {R : Set ℓr} (P : PTree E (ExtI E) R) → DRbisim R (P ⊓ P) P
-- fwd : the choice's only moves are the two τ's, both landing on P
⊓-idem-DR P .DRbisim.fwd .WSimF.on-ev (sRet ())
⊓-idem-DR P .DRbisim.fwd .WSimF.on-ev (sVis refl ())
⊓-idem-DR P .DRbisim.fwd .WSimF.on-tau step with ⊓-τ-inv P P step
... | inj₁ refl = P , wτ τ*-refl , drbisim-refl P
... | inj₂ refl = P , wτ τ*-refl , drbisim-refl P
-- bwd : P's move is matched after absorbing one τ (P ⊓ P ─[τ]─► P)
⊓-idem-DR P .DRbisim.bwd .WSimF.on-ev step =
  _ , wev (τ*-step (⊓-stepL P P) τ*-refl) step τ*-refl , drbisim-refl _
⊓-idem-DR P .DRbisim.bwd .WSimF.on-tau step =
  _ , wτ (τ*-step (⊓-stepL P P) (τ*-step step τ*-refl)) , drbisim-refl _
-- divergence: P ⊓ P diverges iff P does
⊓-idem-DR P .DRbisim.div→ d with ⊓-τ-inv P P (d .Diverges.step)
... | inj₁ eq = subst Diverges eq (d .Diverges.rest)
... | inj₂ eq = subst Diverges eq (d .Diverges.rest)
⊓-idem-DR P .DRbisim.div← d = record { step = ⊓-stepL P P ; rest = d }

⊓-idem-FD : ∀ {ℓr} {R : Set ℓr} (P : PTree E (ExtI E) R) → (P ⊓ P) ≈FD P
⊓-idem-FD P = drbisim→≈FD (⊓-idem-DR P)
