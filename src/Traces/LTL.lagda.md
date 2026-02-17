---
title: Linear Temproal Logic
layout: page
---

```
{-# OPTIONS --type-in-type --guardedness #-}
module Traces.LTL where
```
## Imports

```
open import abstract-set-theory.Prelude using (Type; Maybe; nothing; just; DecEq; _≡_; _≟_; refl)
open import Traces.CSP using (Trace; Process; traces; ⟨⟩)
open import Data.Bool as Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Bool.ListAction using (all)
open import Relation.Nullary as Null using (yes; no; Dec; contradiction)

```
## Propositions and Operators
```
data Prop (A : Type) : Type where
  ¬_ : Prop A → Prop A
  _∧_ : Prop A → Prop A → Prop A
  _∨_ : Prop A → Prop A → Prop A
  _⇒_ : Prop A → Prop A → Prop A
  X_ : Prop A → Prop A
  G_ : Prop A → Prop A
  F_ : Prop A → Prop A
  _U_ : Prop A → Prop A → Prop A
```
## Evaluation over Traces
```
data Holds {A : Type} {✓ : A} {{DEA : DecEq A}} : Prop A → Trace A → Type where
  ¬_ : {P : Prop A}
    → {t : Trace A}
    → Null.¬ (Holds {A} {✓} P t)
    → Holds (¬ P) t
  _∧_ : {P Q : Prop A}
    → {t : Trace A}
    → Holds {A} {✓} P t
    → Holds {A} {✓} Q t
    → Holds (P ∧ Q) t
  ∨₁_ : {P Q : Prop A}
    → {t : Trace A}
    → Holds {A} {✓} P t
    → Holds (P ∨ Q) t
  ∨₂_ : {P Q : Prop A}
    → {t : Trace A}
    → Holds {A} {✓} Q t
    → Holds (P ∨ Q) t
  ⇒₁ : {P Q : Prop A}
    → {t : Trace A}
    → Null.¬ (Holds {A} {✓} P t)
    → Holds (P ⇒ Q) t
  _⇒₂_ : {P Q : Prop A}
    → {t : Trace A}
    → Holds {A} {✓} P t
    → Holds {A} {✓} Q t
    → Holds (P ⇒ Q) t
  X_ : {P : Prop A}
    → {x : A}
    → {t : Trace A}
    → Holds {A} {✓} P t
    → Holds (X P) (x ∷ t)
  G₁ : {P : Prop A}
    → Holds (G P) ⟨⟩
  G₂ : {P : Prop A}
    → {x : A}
    → {t : Trace A}
    → Holds P (x ∷ t)
    → Holds P t
    → Holds (G P) (x ∷ t)
  F₁ : {P : Prop A}
    → {t : Trace A}
    → Holds P t
    → Holds (F P) t
  F₂ : {P : Prop A}
    → {x : A}
    → {t : Trace A}
    → Holds (F P) t
    → Holds (F P) (x ∷ t)
  U₁_ : {P Q : Prop A}
    → {t : Trace A}
    → Holds Q t
    → Holds (P U Q) t
  _U₂_ : {P Q : Prop A}
    → {x : A}
    → {t : Trace A}
    → Holds P (x ∷ t)
    → Holds (P U Q) t
    → Holds (P U Q) (x ∷ t)
  U₃_ : {P Q : Prop A}
    → Holds P []
    → Holds (P U Q) []
```
## Decision procedure
```
holds? : {A : Type} {✓ : A} {{DEA : DecEq A}} → (P : Prop A) → (t : Trace A) → Dec (Holds P t)
holds? {A} {✓} (¬ P) t with holds? {A} {✓} P t
... | yes pt = no λ { (¬ x) → contradiction pt x }
... | no ¬pt = yes (¬ ¬pt)
holds? (P ∧ Q) t with holds? P t | holds? Q t
... | yes pt | yes qt = yes (pt ∧ qt)
... | no ¬pt | _ = no λ { (xp ∧ xq) → ¬pt xp}
... | _ | no ¬qt = no λ { (xp ∧ xq) → ¬qt xq}
holds? (P ∨ Q) t with holds? P t | holds? Q t
... | no ¬pt | no ¬qt = no λ { (∨₁_ x) → ¬pt x ; (∨₂_ x) → ¬qt x }
... | yes pt  | _          = yes (∨₁ pt)
... | _          | yes qt  = yes (∨₂ qt)
holds? (P ⇒ Q) t with holds? P t
... | no ¬pt = yes (⇒₁ ¬pt)
... | yes pt with holds? Q t
...   | yes qt = yes (pt ⇒₂ qt)
...   | no ¬qt = no (λ { (⇒₁ x) → x pt ; (xp ⇒₂ xq) → ¬qt xq} )
holds? (X P) [] = no (λ () )
holds? (X P) (x ∷ t) with holds? P t
... | yes pt = yes (X pt)
... | no ¬pt = no (λ { (X x) → ¬pt x })
holds? (G P) [] = yes G₁
holds? (G P) (x ∷ t) with holds? P (x ∷ t) | holds? P t
... | yes pxt | yes pt = yes (G₂ pxt pt)
... | no ¬pxt | _ = no λ { (G₂ x₁ x₂) → ¬pxt x₁ }
... | _           | no ¬pt = no λ { (G₂ x₁ x₂) → ¬pt x₂ }
holds? (F P) t with holds? P t
... | yes pt = yes (F₁ pt)
holds? (F P) [] | no ¬pt = no (λ { (F₁ x) → ¬pt x} )
holds? (F P) (x ∷ t) | no ¬pt with holds? (F P) t
... | yes fpt = yes (F₂ fpt)
... | no ¬fpt = no λ { (F₁ xx) → ¬pt xx ; (F₂ xx) → ¬fpt xx }
holds? (P U Q) t with holds? Q t
... | yes qt = yes (U₁ qt)
... | no ¬qt with holds? P t
...   | no ¬pt = no λ { (U₁ x) → ¬qt x ; (x U₂ x₁) → ¬pt x; (U₃ x) → ¬pt x }
holds? (P U Q) [] | no ¬qt | yes pt = yes (U₃ pt)
holds? (P U Q) (x ∷ t) | no ¬qt | yes pt with holds? (P U Q) t
... | yes pqt = yes (pt U₂ pqt)
... | no ¬pqt = no (λ { (U₁ xx) → ¬qt xx ; (xx U₂ xx₁) → ¬pqt xx₁ })

```
## Boolean evaluation
```
holds?ᵇ : {A : Type} {✓ : A} {{_ : DecEq A}} → Prop A → Trace {A} {✓} A → Bool
holds?ᵇ {A} {✓} (¬ P) t with holds?ᵇ {A} {✓} P t
... | true = false
... | false = true
holds?ᵇ {A} {✓} (P ∧ Q) t = (holds?ᵇ {A} {✓} P t) Bool.∧ (holds?ᵇ {A} {✓} Q t)
holds?ᵇ {A} {✓} (P ∨ Q) t = (holds?ᵇ {A} {✓} P t) Bool.∨ (holds?ᵇ {A} {✓} Q t)
holds?ᵇ {A} {✓} (P ⇒ Q) t with holds?ᵇ {A} {✓} P t
... | false = true
... | true = holds?ᵇ {A} {✓} Q t
holds?ᵇ {A} {✓} (X P) [] = false
holds?ᵇ {A} {✓} (X P) (_ ∷ t) = holds?ᵇ {A} {✓} P t
holds?ᵇ {A} {✓} (G P) [] = true
holds?ᵇ {A} {✓} (G P) (x ∷ t) = (holds?ᵇ {A} {✓} P (x ∷ t)) Bool.∧ (holds?ᵇ {A} {✓} P t)
holds?ᵇ {A} {✓} (F P) [] = holds?ᵇ {A} {✓} P []
holds?ᵇ {A} {✓} (F P) (x ∷ t) = (holds?ᵇ {A} {✓} P (x ∷ t)) Bool.∨ (holds?ᵇ {A} {✓} (F P) t)
holds?ᵇ {A} {✓} (P U Q) t with holds?ᵇ {A} {✓} Q t
holds?ᵇ {A} {✓} (P U Q) t | true = true
holds?ᵇ {A} {✓} (P U Q) [] | false = holds?ᵇ {A} {✓} P []
holds?ᵇ {A} {✓} (P U Q) (x ∷ t) | false = (holds?ᵇ {A} {✓} P (x ∷ t)) Bool.∧ (holds?ᵇ {A} {✓} (P U Q) t)

```
## LTLs over Processes
```
holds?ᵖ : {A : Type} {✓ : A} {{_ : DecEq A}} → Prop A → Process A ✓ → Bool
holds?ᵖ {A} {✓} Prop P = all (holds?ᵇ {A} {✓} Prop) (traces P)
```
## Examples
```


```
