{-# OPTIONS --guardedness #-}

-- Internal-choice ZERO law (TPC 11.2 / UCS 13.23): in the divergence-strict FD model,
-- Div is a ZERO of ⊓ — `div ⊓ P ≈FD div`.  (In divergence-IGNORING models Div is a
-- UNIT of ⊓ instead; that tension is what separates the model hierarchy.)
--
-- The proof is immediate: `div ⊓ P` can τ-step to `div` (⊓-stepL) which loops, so it
-- diverges at the empty trace; by extension-closure both `div ⊓ P` and `div` diverge at
-- EVERY trace — i.e. both are ⊥ (chaos) — so every failures⊥/divergences obligation is
-- discharged by producing that divergence, ignoring the hypothesis.

open import Level using (Level)
open import Data.Product using (_,_)
open import Data.Sum using (inj₂)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Process_Trees

module CSP.Laws.FD.FDLawsIChoiceZero {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS     {E = E} {I = ExtI E}
open import Semantics.DRBisim {E = E} {I = ExtI E} using (Diverges; div-diverges)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (divergences; _≈FD_; empty-div; div-extension-closed; div-divergence)
open import CSP.Laws.Bisim.Laws E-≟ using (⊓-stepL)

private
  variable
    ℓr : Level
    R  : Set ℓr

-- div ⊓ P diverges: one τ to div (⊓-stepL), then div loops.
⊓-div-diverges : (P : PTree E (ExtI E) R) → Diverges (div ⊓ P)
⊓-div-diverges P .Diverges.next = div
⊓-div-diverges P .Diverges.step = ⊓-stepL div P
⊓-div-diverges P .Diverges.rest = div-diverges

-- both processes are ⊥: divergent at EVERY trace (extension-closure of the []-divergence).
⊓div-all : {P : PTree E (ExtI E) R} {s : _} → divergences (div ⊓ P) s
⊓div-all {P = P} = div-extension-closed (empty-div (⊓-div-diverges P))

div-all : {s : _} → divergences (div {E = E} {I = ExtI E} {R = R}) s
div-all = div-extension-closed div-divergence

⊓-zero-FD : (P : PTree E (ExtI E) R) → (div ⊓ P) ≈FD div
⊓-zero-FD P =
    ( (λ _ → inj₂ (⊓div-all {P = P})) , (λ _ → ⊓div-all {P = P}) )
  , ( (λ _ → inj₂ div-all)            , (λ _ → div-all)          )
