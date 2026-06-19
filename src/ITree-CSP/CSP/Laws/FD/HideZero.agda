{-# OPTIONS --guardedness #-}

-- Hiding ZERO / divergence-strictness (T11.7 / U13.2):  Div ∖ X ≈FD Div.
--
-- Immediate, mirroring the other zeros (⊓/□/∥/;): force(div) = sil div, so
-- force(div ∖ X) = sil (div ∖ X) — `div ∖ X` is an infinite silent loop, hence diverges at
-- the empty trace.  By extension-closure both `div ∖ X` and `div` are ⊥ at every trace, so
-- all four refinements produce that divergence.

open import Level using (Level)
open import Data.Product using (_,_)
open import Data.Sum using (inj₂)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Laws.FD.HideZero {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS     {E = E} {I = ExtI E}
open import Semantics.DRBisim {E = E} {I = ExtI E} using (Diverges; div-diverges)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (divergences; _≈FD_; empty-div; div-extension-closed; div-divergence)

private
  variable
    ℓr : Level
    R  : Set ℓr

-- div ∖ X loops silently (force = sil (div ∖ X)).
hide-div-diverges : (A : EventSet) → Diverges (div {E = E} {I = ExtI E} {R = R} ∖ A)
hide-div-diverges A .Diverges.next = div ∖ A
hide-div-diverges A .Diverges.step = sSil refl
hide-div-diverges A .Diverges.rest = hide-div-diverges A

-- both processes are ⊥ at every trace.
hide-div-all : {A : EventSet} {s : _} → divergences (div {E = E} {I = ExtI E} {R = R} ∖ A) s
hide-div-all {A = A} = div-extension-closed (empty-div (hide-div-diverges A))

div-all : {s : _} → divergences (div {E = E} {I = ExtI E} {R = R}) s
div-all = div-extension-closed div-divergence

-- hide-zero (T11.7):  Div ∖ X ≈FD Div
hide-zero-FD : (A : EventSet) → (div {E = E} {I = ExtI E} {R = R} ∖ A) ≈FD div
hide-zero-FD A =
    ( (λ _ → inj₂ hide-div-all) , (λ _ → hide-div-all) )
  , ( (λ _ → inj₂ div-all)      , (λ _ → div-all)      )
