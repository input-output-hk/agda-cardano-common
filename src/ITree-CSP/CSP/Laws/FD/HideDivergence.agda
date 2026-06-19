{-# OPTIONS --guardedness #-}

-- Hiding divergence: the foundational divergence lemma for the hiding FD laws —
-- the companion of CSP.Laws.FD.ParallelDivergence's `Par-Diverges→`.
--
--   • DivModA A P : an infinite path of P-steps each a τ OR a hidden A-event
--     (re-used from CSP.Laws.Bisim.DRCongruence; `div∖→modA` / `modA→div∖` are the
--     constructive bridges proven there: Diverges (P ∖ A) ⇔ DivModA A P).
--   • MAcc A t : accessibility of the modulo-A step relation `ModAStep` (τ ∪ hidden-A).
--   • ¬DivModA→MAcc : ¬ DivModA A t → MAcc A t — the König step, POSTULATED here
--     (mirror of Par-Diverges→).  CERTIFIED sound from the single `dne` in
--     ClassicalFromLEM (Derivation 9, `¬DivModAC→MAccC` — a MAcc well-founded recursion
--     over the modulo-A step relation, exactly the DAcc route of Par-no-inf).
--   • MAcc→¬DivModA : an accessible state has no infinite modulo-A path — CONSTRUCTIVE.
--   • Hide-Diverges→ / Hide-noDiv-from-MAcc : the headline corollaries used to refute
--     divergence under hiding by a well-founded `MAcc` descent.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Process_Trees

module CSP.Laws.FD.HideDivergence {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS     {E = E} {I = ExtI E}
open import Semantics.DRBisim {E = E} {I = ExtI E} using (Diverges)
open import CSP.Laws.Bisim.DRCongruence E-≟
  using (ModAStep; maτ; maE; DivModA; div∖→modA; modA→div∖)
open DivModA
open EventSet

private
  variable
    ℓr : Level
    R  : Set ℓr

-------------------------------------------------------------------------------------
-- accessibility of the modulo-A step relation (the DAcc analogue over ModAStep)
-------------------------------------------------------------------------------------
data MAcc {ℓr} {R : Set ℓr} (A : EventSet) (t : PTree E (ExtI E) R)
     : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  macc : (∀ {t′} → ModAStep A t t′ → MAcc A t′) → MAcc A t

accSubM : (A : EventSet) {t t′ : PTree E (ExtI E) R}
        → MAcc A t → ModAStep A t t′ → MAcc A t′
accSubM A (macc rs) step = rs step

-------------------------------------------------------------------------------------
-- the König step (postulated, certified from dne — like Par-Diverges→)
-------------------------------------------------------------------------------------
postulate
  ¬DivModA→MAcc : (A : EventSet) {t : PTree E (ExtI E) R} → ¬ DivModA A t → MAcc A t

-------------------------------------------------------------------------------------
-- constructive: an accessible state has no infinite modulo-A path
-------------------------------------------------------------------------------------
MAcc→¬DivModA : (A : EventSet) {t : PTree E (ExtI E) R} → MAcc A t → ¬ DivModA A t
MAcc→¬DivModA A (macc rs) dm = MAcc→¬DivModA A (rs (dm .maStep)) (dm .maRest)

-------------------------------------------------------------------------------------
-- HEADLINE: divergence under hiding reflects to an infinite modulo-A path of P
-- (constructive, = DRCongruence's `div∖→modA`), and an accessible P cannot diverge
-- when hidden.  Together these refute `Diverges (P ∖ A)` from `MAcc A P`.
-------------------------------------------------------------------------------------

-- a divergence of `P ∖ A` is an infinite modulo-A path of P (constructive bridge)
Hide-Diverges→ : (A : EventSet) (P : PTree E (ExtI E) R)
               → Diverges (P ∖ A) → DivModA A P
Hide-Diverges→ A P = div∖→modA A P

-- if P is modulo-A accessible then `P ∖ A` cannot diverge.
Hide-noDiv-from-MAcc : (A : EventSet) (P : PTree E (ExtI E) R)
                     → MAcc A P → ¬ Diverges (P ∖ A)
Hide-noDiv-from-MAcc A P acc d = MAcc→¬DivModA A acc (Hide-Diverges→ A P d)
