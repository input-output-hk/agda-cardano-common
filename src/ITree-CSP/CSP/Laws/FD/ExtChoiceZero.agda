{-# OPTIONS --guardedness #-}

-- External-choice ZERO / divergence-strictness (T11.3): in the FD model 𝒩, Div is a ZERO
-- of □ —  Div □ P ≈FD Div.
--
-- Immediate, mirroring ⊓-zero / ∥-zero: `□-Diverges-L` lifts div's divergence into the
-- composite ⇒ `div □ P` diverges at the empty trace, so by extension-closure both
-- `div □ P` and `div` diverge at EVERY trace (both = ⊥/chaos); every failures⊥/divergences
-- obligation is discharged by producing that divergence.

open import Level using (Level)
open import Data.Product using (_,_)
open import Data.Sum using (inj₂)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Class.DecEq using (DecEq)

open import Process_Trees

module CSP.Laws.FD.ExtChoiceZero {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS     {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.DRBisim {E = E} {I = ExtI E} using (Diverges; div-diverges)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (divergences; _≈FD_; empty-div; div-extension-closed; div-divergence)
open import CSP.Laws.FD.ExtChoiceFD E-≟ using (□-Diverges-L)

private
  variable
    ℓr : Level
    R  : Set ℓr

-- both processes are ⊥: divergent at EVERY trace (extension-closure of []-divergence).
□-div-all : ⦃ _ : DecEq R ⦄ {P : PTree E (ExtI E) R} {s : _} → divergences (div □ P) s
□-div-all {P = P} = div-extension-closed (empty-div (□-Diverges-L div-diverges))

div-all : {s : _} → divergences (div {E = E} {I = ExtI E} {R = R}) s
div-all = div-extension-closed div-divergence

-- □-zero (T11.3):  Div □ P ≈FD Div
□-zero-FD : ⦃ _ : DecEq R ⦄ (P : PTree E (ExtI E) R) → (div □ P) ≈FD div
□-zero-FD P =
    ( (λ _ → inj₂ (□-div-all {P = P})) , (λ _ → □-div-all {P = P}) )
  , ( (λ _ → inj₂ div-all)            , (λ _ → div-all)           )
