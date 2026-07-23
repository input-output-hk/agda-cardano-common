{-# OPTIONS --guardedness #-}

-- Rename ZERO / divergence-strictness (T11.8 / U13.5):  Div ⟦ inv ⟧ⁱ ≈FD Div.
--
-- Immediate, mirroring the other zeros (⊓/□/∥/;/∖): force(div) = sil div, so
-- force(div ⟦ inv ⟧ⁱ) = sil (div ⟦ inv ⟧ⁱ) — `div ⟦ inv ⟧ⁱ` is an infinite silent loop,
-- hence diverges at the empty trace.  By extension-closure both `div ⟦ inv ⟧ⁱ` and `div`
-- are ⊥ at every trace, so all four refinements produce that divergence.

open import Level using (Level)
open import Data.Maybe using (Maybe; just)
open import Data.Product using (_,_; proj₁)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Laws.FD.RenameZero {ℓ ℓe} {E : Set ℓ → Set ℓe} where
open PTree

open import CSP.Rename {E₁ = E} {E₂ = E} (λ e → e) (λ e → just e) (λ _ → refl)
  using (renameInv; ConcEvent₁)
open import Semantics.LTS     {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.DRBisim {E = E} {I = ExtI E} using (Diverges; div-diverges)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (divergences; _≈FD_; empty-div; div-extension-closed; div-divergence)

private
  variable
    ℓr : Level
    R  : Set ℓr

-- the injective (same-alphabet) renaming wrapper, as in TraceLawsRename.
_⟦_⟧ⁱ : PTree E (ExtI E) R → ((bt : AnyTypes E) → proj₁ bt → Maybe ConcEvent₁) → PTree E (ExtI E) R
P ⟦ inv ⟧ⁱ = renameInv P inv

-- div ⟦ inv ⟧ⁱ loops silently (force = sil (div ⟦ inv ⟧ⁱ)).
rename-div-diverges : (inv : _) → Diverges ((div {E = E} {I = ExtI E} {R = R}) ⟦ inv ⟧ⁱ)
rename-div-diverges inv .Diverges.next = div ⟦ inv ⟧ⁱ
rename-div-diverges inv .Diverges.step = sSil refl
rename-div-diverges inv .Diverges.rest = rename-div-diverges inv

-- both processes are ⊥ at every trace.
rename-div-all : {inv : _} {s : _} → divergences ((div {E = E} {I = ExtI E} {R = R}) ⟦ inv ⟧ⁱ) s
rename-div-all {inv = inv} = div-extension-closed (empty-div (rename-div-diverges inv))

div-all : {s : _} → divergences (div {E = E} {I = ExtI E} {R = R}) s
div-all = div-extension-closed div-divergence

-- rename-zero (T11.8):  Div ⟦ inv ⟧ⁱ ≈FD Div
rename-zero-FD : (inv : _) → ((div {E = E} {I = ExtI E} {R = R}) ⟦ inv ⟧ⁱ) ≈FD div
rename-zero-FD inv =
    ( (λ _ → inj₂ rename-div-all) , (λ _ → rename-div-all) )
  , ( (λ _ → inj₂ div-all)        , (λ _ → div-all)        )
