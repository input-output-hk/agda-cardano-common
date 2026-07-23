{-# OPTIONS --guardedness #-}

-- Sequential ZERO-left / divergence-strictness (T11.9 / U13.7): in the FD model 𝒩, Div is
-- a left ZERO of ; —  Div ; P ≈FD Div.  (Spike `;` = `>>` = `>>= λ_→·`.)
--
-- Immediate, mirroring ⊓-zero / □-zero / ∥-zero: div is already divergent, and a left
-- divergence lifts through `>> P` (every τ of div lifts via bind-τ), so `div >> P` diverges
-- at the empty trace ⇒ both `div >> P` and `div` are ⊥ at every trace.

open import Level using (Level)
open import Data.Product using (_,_)
open import Data.Sum using (inj₂)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Process_Trees

module CSP.Laws.FD.SeqZero {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS     {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.DRBisim {E = E} {I = ExtI E} using (Diverges; div-diverges)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (divergences; _≈FD_; empty-div; div-extension-closed; div-divergence)
open import CSP.Laws.Bisim.LoopCong E-≟ using (bind-τ)

private
  variable
    ℓr ℓs : Level
    R  : Set ℓr
    S  : Set ℓs

-- a left divergence lifts through `>> X` (every τ of P lifts via bind-τ; coinductive)
bind-div : {P : PTree E (ExtI E) R} (X : PTree E (ExtI E) S) → Diverges P → Diverges (P >> X)
bind-div X d .Diverges.next = d .Diverges.next >> X
bind-div X d .Diverges.step = bind-τ (λ _ → X) _ (d .Diverges.step)
bind-div X d .Diverges.rest = bind-div X (d .Diverges.rest)

-- both processes are ⊥: divergent at EVERY trace (extension-closure of []-divergence).
seq-div-all : {P : PTree E (ExtI E) S} {s : _}
            → divergences ((div {E = E} {I = ExtI E} {R = R}) >> P) s
seq-div-all {P = P} = div-extension-closed (empty-div (bind-div P div-diverges))

div-all : {s : _} → divergences (div {E = E} {I = ExtI E} {R = S}) s
div-all = div-extension-closed div-divergence

-- seq-zero-l / ;-zero-l (T11.9):  Div ; P ≈FD Div
seq-zero-FD : (P : PTree E (ExtI E) S) → ((div {E = E} {I = ExtI E} {R = R}) >> P) ≈FD div
seq-zero-FD P =
    ( (λ _ → inj₂ (seq-div-all {P = P})) , (λ _ → seq-div-all {P = P}) )
  , ( (λ _ → inj₂ div-all)              , (λ _ → div-all)             )
