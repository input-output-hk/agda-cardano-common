{-
  Failures/Divergences (F⊥ / FD) monotonicity for `loop`, `while`, and
  friends, re-exported and assembled from `CSP.Laws.Iterate_Bisim`:

    * `loop-mono-⊑F⊥-via-bisim`  / `loop-mono-⊑D-via-bisim`
    * `while-mono-⊑F⊥-via-bisim` / `while-mono-⊑D-via-bisim`

  all built on the iteration-tag-generic bisimulation
  (`bF⊑+bD⊑→Iter-Sim {h}`: loop = `h := inj₁`, while =
  `h := whileTag cond`).  Every one is postulate-free w.r.t. the
  iterate monotonicity family — the `Loop-Sim.on-div` field is the real
  `tail-on-div-lift` construction — so this aggregator discharges the
  former `loop-mono-⊑D` / `while-mono-⊑F⊥` / `while-mono-⊑D` postulates.
  (They still rest, like `loop-mono-⊑F⊥`, on the single classical
  postulate `ev-step-closure-⊑F⊥` in `Iterate_Bisim`.)

  This aggregator exists to break a dependency cycle: `Iterate_Bisim`
  imports `Iterate`, so `Iterate` cannot import the bisim versions
  directly.  Downstream consumers (e.g. `FailuresDivergences`) pull the
  F⊥/D/FD mono names from here, and the FD pairs (`*-mono-⊑FD`) are
  assembled here from the F⊥ and D components.
-}

{-# OPTIONS --guardedness #-}

open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Bool using (Bool)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Interaction_Trees
open import ITree_Relations.FailuresDivergences

module CSP.Laws.Iterate_FD
  {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where

import CSP.Definitions.Iterate {ℓ} {ℓe} {E} as CSPIter
open CSPIter E-≟

-----------------------------------------------------------------------------------------
-- Re-export the bisim-based F⊥/D monotonicity lemmas from
-- `CSP.Laws.Iterate_Bisim`, renamed to the canonical public names
-- (`loop-mono-⊑F⊥` / `loop-mono-⊑D`).  Both are now postulate-free:
-- the `Loop-Sim.on-div` field is built from the real `tail-on-div-lift`
-- construction, so `loop-mono-⊑D-via-bisim` discharges the former
-- `loop-mono-⊑D` postulate.  `loop-mono-⊑D` is consumed below to
-- assemble `loop-mono-⊑FD`.
-----------------------------------------------------------------------------------------

import CSP.Laws.Iterate_Bisim {ℓ} {ℓe} {E} as Bisim
open Bisim E-≟ public using ()
  renaming ( loop-mono-⊑F⊥-via-bisim  to loop-mono-⊑F⊥
           ; loop-mono-⊑D-via-bisim   to loop-mono-⊑D
           ; while-mono-⊑F⊥-via-bisim to while-mono-⊑F⊥
           ; while-mono-⊑D-via-bisim  to while-mono-⊑D )

-----------------------------------------------------------------------------------------
-- Derived FD monotonicity for `loop`.  Pairs F⊥ and ⊑D components from
-- the supplied ⊑FD hypothesis at the body.
-----------------------------------------------------------------------------------------

loop-mono-⊑FD : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
   {body body′ : HKTree E (ExtI I) A}
   → (∀ a → _⊑FD_ {ℓB = ℓB} (body a) (body′ a))
   → ∀ a → _⊑FD_ {ℓB = ℓB} (loop {R = R} body a) (loop body′ a)
loop-mono-⊑FD bFD a =
    loop-mono-⊑F⊥ (λ a → proj₁ (bFD a)) (λ a → proj₂ (bFD a)) a
  , loop-mono-⊑D  (λ a → proj₁ (bFD a)) (λ a → proj₂ (bFD a)) a

-----------------------------------------------------------------------------------------
-- Derived FD monotonicity for `while`.  Pairs the F⊥ and ⊑D components
-- (both re-exported above from the generic iter bisim) from the
-- supplied ⊑FD hypothesis at the body.
-----------------------------------------------------------------------------------------

while-mono-⊑FD : ∀ {ℓi ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ}
   (cond : A → Bool) {body body′ : HKTree E (ExtI I) A}
   → (∀ a → _⊑FD_ {ℓB = ℓB} (body a) (body′ a))
   → ∀ a → _⊑FD_ {ℓB = ℓB} (while cond body a) (while cond body′ a)
while-mono-⊑FD cond bFD a =
    while-mono-⊑F⊥ cond (λ a → proj₁ (bFD a)) (λ a → proj₂ (bFD a)) a
  , while-mono-⊑D  cond (λ a → proj₁ (bFD a)) (λ a → proj₂ (bFD a)) a

-----------------------------------------------------------------------------------------
-- Specialisations for `loop0` (constant-body loop) and `loopc` (alias
-- of `loop0`).
-----------------------------------------------------------------------------------------

loop0-mono-⊑F⊥ : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   {body body′ : ITree E (ExtI I) ⊤}
   → _⊑F⊥_ {ℓB = ℓB} body body′
   → body ⊑D body′
   → _⊑F⊥_ {ℓB = ℓB} (loop0 {R = R} body) (loop0 body′)
loop0-mono-⊑F⊥ b⊑b′ b⊑bD = loop-mono-⊑F⊥ (λ _ → b⊑b′) (λ _ → b⊑bD) tt

loop0-mono-⊑FD : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   {body body′ : ITree E (ExtI I) ⊤}
   → _⊑FD_ {ℓB = ℓB} body body′
   → _⊑FD_ {ℓB = ℓB} (loop0 {R = R} body) (loop0 body′)
loop0-mono-⊑FD b⊑b′ = loop-mono-⊑FD (λ _ → b⊑b′) tt

loopc-mono-⊑F⊥ : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   {body body′ : ITree E (ExtI I) ⊤}
   → _⊑F⊥_ {ℓB = ℓB} body body′
   → body ⊑D body′
   → _⊑F⊥_ {ℓB = ℓB} (loopc {R = R} body) (loopc body′)
loopc-mono-⊑F⊥ = loop0-mono-⊑F⊥

loopc-mono-⊑FD : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   {body body′ : ITree E (ExtI I) ⊤}
   → _⊑FD_ {ℓB = ℓB} body body′
   → _⊑FD_ {ℓB = ℓB} (loopc {R = R} body) (loopc body′)
loopc-mono-⊑FD = loop0-mono-⊑FD
