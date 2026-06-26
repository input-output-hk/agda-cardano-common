{-# OPTIONS --guardedness #-}

-- Parallel ZERO / divergence-strictness (T11.4 interface, T11.5 alphabetised, T11.6
-- interleaving — the spike's single `Par A merge` covers all three): in the
-- divergence-strict FD model 𝒩, Div is a ZERO of ∥ —
--   Div ∥[X] P ≈FD Div.
--
-- Immediate, mirroring ⊓-zero (FDLawsIChoiceZero): div is already divergent, so
-- `Par div P` diverges at the empty trace (Par-Diverges-L lifts div's divergence to the
-- composite); by extension-closure both `Par div P` and `div` diverge at EVERY trace
-- (both = ⊥/chaos), so every failures⊥/divergences obligation is discharged by producing
-- that divergence, ignoring the hypothesis.  Confirms parallel is divergence-strict.

open import Level using (Level)
open import Data.Product using (_,_)
open import Data.Sum using (inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; no)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Process_Trees

module CSP.Laws.FD.ParallelZero {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS     {E = E} {I = ExtI E}
open import Semantics.DRBisim {E = E} {I = ExtI E} using (Diverges; div-diverges)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (divergences; _≈FD_; empty-div; div-extension-closed; div-divergence)
open import CSP.Laws.Traces.TraceLawsParallel E-≟ using (Mg)
open import CSP.Laws.FD.ParallelDivergence E-≟ using (Par-Diverges-L)

private
  variable
    ℓ₁ ℓ₂ ℓr : Level
    R₁ : Set ℓ₁
    R₂ : Set ℓ₂
    R  : Set ℓr

module _ (A : EventSet) (merge : Mg R₁ R₂ R) where

  -- Par div P diverges: div's divergence lifts to the composite (Par-Diverges-L).
  Par-div-diverges : (P : PTree E (ExtI E) R₂) → Diverges (Par A merge div P)
  Par-div-diverges P = Par-Diverges-L A merge {P = div} P div-diverges

  -- both processes are ⊥: divergent at EVERY trace (extension-closure of []-divergence).
  Par-div-all : {P : PTree E (ExtI E) R₂} {s : _} → divergences (Par A merge div P) s
  Par-div-all {P = P} = div-extension-closed (empty-div (Par-div-diverges P))

  div-all : {s : _} → divergences (div {E = E} {I = ExtI E} {R = R}) s
  div-all = div-extension-closed div-divergence

  -- ∥-zero (T11.4/5/6):  Div ∥ P ≈FD Div
  Par-zero-FD : (P : PTree E (ExtI E) R₂) → (Par A merge div P) ≈FD div
  Par-zero-FD P =
      ( (λ _ → inj₂ (Par-div-all {P = P})) , (λ _ → Par-div-all {P = P}) )
    , ( (λ _ → inj₂ div-all)               , (λ _ → div-all)             )

-------------------------------------------------------------------------------------
-- instances: ⊤-merge (Par⊤) and interleaving (⦀, cs = ∅)
-------------------------------------------------------------------------------------
Par⊤-zero-FD : (A : EventSet) (P : PTree E (ExtI E) (⊤ {ℓr}))
             → (div ∥⇘ A ⇙ P) ≈FD div
Par⊤-zero-FD A P = Par-zero-FD A (λ _ _ → tt) P

⦀-zero-FD : (P : PTree E (ExtI E) (⊤ {ℓr})) → (div ⦀ P) ≈FD div
⦀-zero-FD P = Par⊤-zero-FD ∅ES P
