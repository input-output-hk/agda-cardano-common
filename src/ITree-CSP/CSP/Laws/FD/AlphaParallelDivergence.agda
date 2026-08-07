{-# OPTIONS --guardedness #-}

-- DIVERGENCE lemmas for the BINARY ALPHABETISED PARALLEL `_⟦ A ∥ B ⟧_`
-- (= `αpar A B _,_`) — the αpar counterpart of `CSP.Laws.FD.ParallelDivergence`'s
-- `Par-Diverges→` / `Par-Diverges-L` / `-R`, i.e. the `div→` ingredients of an FSim
-- congruence for `⟦A∥B⟧`.
--
--   • αpar-Diverges→   : Diverges (P ⟦A∥B⟧ Q) → Diverges P ⊎ Diverges Q  — the König
--     step, POSTULATED here (mirror of `Par-Diverges→` / `□-Diverges→`).  CERTIFIED
--     sound from the single `dne` of `CSP.Laws.ClassicalFromLEM` (Derivation 11,
--     `αpar-no-inf` — a `DAcc` well-founded recursion: by the 2-way `αpar-τ-step-inv`
--     a composite τ is one operand's τ, so the chain stays in `⟦A∥B⟧` form and an
--     infinite composite τ-chain forces an infinite one in P or in Q).  The αpar
--     argument is STRICTLY SIMPLER than `Par`'s: there is no both-offer overlap node,
--     hence no third τ-shape to dispatch.
--   • αpar-Diverges-L / -R : an operand's livelock lifts to the composite —
--     CONSTRUCTIVE (coinductive, the operand's τ's threaded through the single-step
--     lift `αpar-τ-lift-L` / `-R` of `CSP.Laws.AlphaParallelLift`).
--
-- WHY THE LIFTS CARRY `NoSil`.  `αpar` gives a `sil`-headed operand ABSOLUTE priority
-- (`react _ _ | sil Q′ → sil (αpar P Q′)`), so while `Q` is `sil`-headed the composite
-- cannot perform ANY step of `P`.  `Diverges P → Diverges (P ⟦A∥B⟧ Q)` is still TRUE
-- for an arbitrary `Q` — if `Q`'s leading `sil`s are infinite the composite diverges on
-- THOSE instead — but deciding which of the two happens is exactly a classical
-- (König) step.  The lifts below stay CONSTRUCTIVE by requiring the standing-still
-- operand to be non-`sil`-headed, which every stable and every terminated state is
-- (`noSil-stable` / `noSil-ret`), and which is what a stable composite gives on both
-- sides (`αpar-stable-noSil-L` / `-R`).

open import Level using (Level)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Laws.FD.AlphaParallelDivergence {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open EventSet
open import Semantics.LTS {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.DRBisim {E = E} {I = ExtI E} using (Diverges)
open import CSP.Laws.AlphaParallelLift E-≟
  using (NoSil; noSil-ret; noSil-stable; αpar-τ-lift-L; αpar-τ-lift-R)

private
  variable
    ℓr ℓs : Level
    R : Set ℓr
    S : Set ℓs

-------------------------------------------------------------------------------------
-- the König step (postulated, certified from `dne` in CSP.Laws.ClassicalFromLEM,
-- Derivation 11 — exactly as `Par-Diverges→` is by Derivation 5)
-------------------------------------------------------------------------------------
postulate
  αpar-Diverges→ : (A B : EventSet)
                   {P : PTree E (ExtI E) R} {Q : PTree E (ExtI E) S}
                 → Diverges (P ⟦ A ∥ B ⟧ Q) → Diverges P ⊎ Diverges Q

-------------------------------------------------------------------------------------
-- constructive divergence lifting (no König): an operand's livelock is the
-- composite's, provided the OTHER operand is not `sil`-headed (its head shape never
-- changes along the run, so ONE `NoSil` covers the whole infinite chain)
-------------------------------------------------------------------------------------

-- the LEFT operand's divergence lifts to the composite
αpar-Diverges-L : (A B : EventSet)
                  {P : PTree E (ExtI E) R} (Q : PTree E (ExtI E) S)
                → NoSil Q → Diverges P → Diverges (P ⟦ A ∥ B ⟧ Q)
αpar-Diverges-L A B Q nsQ d .Diverges.next =
  (d .Diverges.next) ⟦ A ∥ B ⟧ Q
αpar-Diverges-L A B {P = P} Q nsQ d .Diverges.step =
  αpar-τ-lift-L A B {P = P} {P′ = d .Diverges.next} {Q = Q} nsQ (d .Diverges.step)
αpar-Diverges-L A B Q nsQ d .Diverges.rest =
  αpar-Diverges-L A B Q nsQ (d .Diverges.rest)

-- the RIGHT operand's divergence lifts to the composite
αpar-Diverges-R : (A B : EventSet)
                  (P : PTree E (ExtI E) R) {Q : PTree E (ExtI E) S}
                → NoSil P → Diverges Q → Diverges (P ⟦ A ∥ B ⟧ Q)
αpar-Diverges-R A B P nsP d .Diverges.next =
  P ⟦ A ∥ B ⟧ (d .Diverges.next)
αpar-Diverges-R A B P {Q = Q} nsP d .Diverges.step =
  αpar-τ-lift-R A B {P = P} {Q = Q} {Q′ = d .Diverges.next} nsP (d .Diverges.step)
αpar-Diverges-R A B P nsP d .Diverges.rest =
  αpar-Diverges-R A B P nsP (d .Diverges.rest)

-- convenience: the standing-still operand is STABLE (the shape an FSim `div→` meets
-- when the composite's stability has been classified by `αpar-stable-normal`)
αpar-Diverges-L-stable : (A B : EventSet)
                         {P : PTree E (ExtI E) R} (Q : PTree E (ExtI E) S)
                       → isStable Q → Diverges P → Diverges (P ⟦ A ∥ B ⟧ Q)
αpar-Diverges-L-stable A B Q stQ = αpar-Diverges-L A B Q (noSil-stable {t = Q} stQ)

-- mirror of `αpar-Diverges-L-stable`
αpar-Diverges-R-stable : (A B : EventSet)
                         (P : PTree E (ExtI E) R) {Q : PTree E (ExtI E) S}
                       → isStable P → Diverges Q → Diverges (P ⟦ A ∥ B ⟧ Q)
αpar-Diverges-R-stable A B P stP = αpar-Diverges-R A B P (noSil-stable {t = P} stP)

-- convenience: the standing-still operand has TERMINATED (`ret`-headed)
αpar-Diverges-L-ret : (A B : EventSet)
                      {P : PTree E (ExtI E) R} (Q : PTree E (ExtI E) S) {s : S}
                    → Q .force ≡ ret s → Diverges P → Diverges (P ⟦ A ∥ B ⟧ Q)
αpar-Diverges-L-ret A B Q eqQ = αpar-Diverges-L A B Q (noSil-ret {t = Q} eqQ)

-- mirror of `αpar-Diverges-L-ret`
αpar-Diverges-R-ret : (A B : EventSet)
                      (P : PTree E (ExtI E) R) {Q : PTree E (ExtI E) S} {r : R}
                    → P .force ≡ ret r → Diverges Q → Diverges (P ⟦ A ∥ B ⟧ Q)
αpar-Diverges-R-ret A B P eqP = αpar-Diverges-R A B P (noSil-ret {t = P} eqP)
