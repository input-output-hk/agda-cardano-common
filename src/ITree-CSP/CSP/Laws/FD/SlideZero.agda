{-# OPTIONS --guardedness #-}

-- Divergence-strict sliding laws (UCS Ch.13):
--   • Div ▷ Q  ≈FD  Div            — the slide's timeout-state inherits Div's silent loop
--     (the (sil Div)-τ slides as (Div ▷ Q) ⇒ an infinite τ-path), so Div ▷ Q diverges at
--     ⟨⟩ and is ⊥ everywhere (the model 𝒩 is divergence-strict).
--   • Div ▷ Q  ≈FD  Div ⊓ Q        — Div-slide (U13.13): both sides are Div (via ⊓-zero).
--
-- Same trivial div-strict pattern as the zero laws (⊓-zero / □-zero / ∥-zero): a single
-- root divergence ⇒ `div-extension-closed (empty-div …)` answers every failures⊥/div query.

open import Level using (Level)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (_,_)
open import Data.Sum using (inj₂)
open import Relation.Nullary using (Dec; yes)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq)

open import Process_Trees

module CSP.Laws.FD.SlideZero {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS     {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.DRBisim {E = E} {I = ExtI E} using (Diverges; div-diverges)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (divergences; _≈FD_; ≈FD-setoid; empty-div; div-extension-closed; div-divergence)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import CSP.Laws.Traces.TraceLaws E-≟ using (▷-τ-L)
open import CSP.Laws.Traces.TraceLawsExtChoice     E-≟ using (NonRet)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟ using (▷-timeout)
open import CSP.Laws.FD.FDLawsIChoiceZero E-≟ using (⊓-zero-FD)
open import CSP.Laws.FD.ExtChoiceComm     E-≟ using (□-comm-FD)
open import CSP.Laws.FD.ExtChoiceZero     E-≟ using (□-zero-FD)

private
  variable
    ℓr : Level
    R  : Set ℓr

-- the slide's timeout state Div ▷ Q loops on Div's silent τ (▷-τ-L slides it).
▷-div-diverges : (Q : PTree E (ExtI E) R) → Diverges (div ▷ Q)
▷-div-diverges Q .Diverges.next = div ▷ Q
▷-div-diverges Q .Diverges.step = ▷-τ-L (div-diverges .Diverges.step)
▷-div-diverges Q .Diverges.rest = ▷-div-diverges Q

▷div-all : {Q : PTree E (ExtI E) R} {s : _} → divergences (div ▷ Q) s
▷div-all {Q = Q} = div-extension-closed (empty-div (▷-div-diverges Q))

div-all : {s : _} → divergences (div {E = E} {I = ExtI E} {R = R}) s
div-all = div-extension-closed div-divergence

-- Div ▷ Q  ≈FD  Div     (slide left-zero — Div ▷ Q diverges immediately)
slide-Div-L-FD : (Q : PTree E (ExtI E) R) → (div ▷ Q) ≈FD div
slide-Div-L-FD Q =
    ( (λ _ → inj₂ ▷div-all) , (λ _ → ▷div-all) )
  , ( (λ _ → inj₂ div-all)  , (λ _ → div-all)  )

-- Div-slide (U13.13):  Div ▷ Q  ≈FD  Div ⊓ Q     (both are Div)
slide-Div-FD : (Q : PTree E (ExtI E) R) → (div ▷ Q) ≈FD (div ⊓ Q)
slide-Div-FD {R = R} Q = begin
  div ▷ Q   ≈⟨ slide-Div-L-FD Q ⟩
  div       ≈⟨ ⊓-zero-FD Q ⟨
  div ⊓ Q   ∎
  where open SetoidReasoning (≈FD-setoid R)

-- a non-terminating P ▷ Div times out to Div, hence diverges (slide right-zero).
▷-Div-R-diverges : {P : PTree E (ExtI E) R} → NonRet (PTree.force P) → Diverges (P ▷ div)
▷-Div-R-diverges {P = P} nt .Diverges.next = div
▷-Div-R-diverges {P = P} nt .Diverges.step = ▷-timeout P div refl nt
▷-Div-R-diverges         nt .Diverges.rest = div-diverges

▷divR-all : {P : PTree E (ExtI E) R} → NonRet (PTree.force P) → {s : _} → divergences (P ▷ div) s
▷divR-all nt = div-extension-closed (empty-div (▷-Div-R-diverges nt))

slide-Div-R-FD : (P : PTree E (ExtI E) R) → NonRet (PTree.force P) → (P ▷ div) ≈FD div
slide-Div-R-FD P nt =
    ( (λ _ → inj₂ (▷divR-all nt)) , (λ _ → ▷divR-all nt) )
  , ( (λ _ → inj₂ div-all)        , (λ _ → div-all)      )

-- □-div (U13.16):  P □ Div  ≈FD  P ▷ Div     (both are Div; needs P non-terminating)
□-div-FD : ⦃ _ : DecEq R ⦄ (P : PTree E (ExtI E) R) → NonRet (PTree.force P)
         → (P □ div) ≈FD (P ▷ div)
□-div-FD {R = R} P nt = begin
  P □ div   ≈⟨ □-comm-FD P div ⟩
  div □ P   ≈⟨ □-zero-FD P ⟩
  div       ≈⟨ slide-Div-R-FD P nt ⟨
  P ▷ div   ∎
  where open SetoidReasoning (≈FD-setoid R)

-- ⊤'s unique element makes equality trivially decidable (needed for `□` at R = ⊤).
private instance
  DecEq-⊤ : ∀ {ℓr} → DecEq (⊤ {ℓr})
  DecEq-⊤ = record { _≟_ = λ _ _ → yes refl }

-- extc-Div-SKIP-red (U13.19):  Div □ SKIP  ≈FD  Div ⊓ SKIP     (both reduce to Div by
-- divergence-strictness — Div's root divergence makes either composite ⊥ everywhere).
□-Div-SKIP-red-FD : ∀ {ℓr} → (div {R = ⊤ {ℓr}} □ Skip) ≈FD (div {R = ⊤ {ℓr}} ⊓ Skip)
□-Div-SKIP-red-FD {ℓr = ℓr} = begin
  div □ Skip   ≈⟨ □-zero-FD Skip ⟩
  div          ≈⟨ ⊓-zero-FD Skip ⟨
  div ⊓ Skip   ∎
  where open SetoidReasoning (≈FD-setoid (⊤ {ℓr}))
