{-# OPTIONS --guardedness #-}

-- SPIKE: a law that strong bisimulation CANNOT prove (it changes the τ-count),
-- but weak bisimulation can: internal-choice idempotence  P ⊓ P ≈ P.

open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Laws.Bisim.WeakLaws {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS      {E = E} {I = ExtI E}
open import Semantics.WeakBisim {E = E} {I = ExtI E}
open import CSP.Laws.Bisim.Laws E-≟ using (⊓-τ-inv; ⊓-stepL)   -- reuse LTS facts about ⊓

-- internal choice is idempotent (up to weak bisimulation)
⊓-idem : ∀ {ℓr} {R : Set ℓr} (P : PTree E (ExtI E) R) → (P ⊓ P) ≈ P
-- P⊓P offers nothing visible
⊓-idem P .Wbisim.fwd .WSimF.on-ev (sRet ())
⊓-idem P .Wbisim.fwd .WSimF.on-ev (sVis refl ())
-- P⊓P's only τ-move lands on P; match with zero τ's on the right
⊓-idem P .Wbisim.fwd .WSimF.on-tau step with ⊓-τ-inv P P step
... | inj₁ refl = P , wτ τ*-refl , wbisim-refl P
... | inj₂ refl = P , wτ τ*-refl , wbisim-refl P
-- P's moves are matched by P⊓P after first doing its τ to P
⊓-idem P .Wbisim.bwd .WSimF.on-ev  step =
  _ , wev (τ*-step (⊓-stepL P P) τ*-refl) step τ*-refl , wbisim-refl _
⊓-idem P .Wbisim.bwd .WSimF.on-tau step =
  _ , wτ (τ*-step (⊓-stepL P P) (τ*-step step τ*-refl)) , wbisim-refl _

-- chaining law instances via transitivity:  ((P ⊓ P) ⊓ (P ⊓ P)) ≈ P
⊓-idem² : ∀ {ℓr} {R : Set ℓr} (P : PTree E (ExtI E) R)
        → ((P ⊓ P) ⊓ (P ⊓ P)) ≈ P
⊓-idem² P = wbisim-trans (⊓-idem (P ⊓ P)) (⊓-idem P)
