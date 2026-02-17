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
open import Traces.CSP using (Trace)
open import Data.Bool as Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
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
holds? : {A : Type} {✓ : A} {{_ : DecEq A}} → Prop A → Trace {A} {✓} A → Bool
holds? {A} {✓} (¬ P) t with holds? {A} {✓} P t
... | true = false
... | false = true
holds? {A} {✓} (P ∧ Q) t = (holds? {A} {✓} P t) Bool.∧ (holds? {A} {✓} Q t)
holds? {A} {✓} (P ∨ Q) t = (holds? {A} {✓} P t) Bool.∨ (holds? {A} {✓} Q t)
holds? {A} {✓} (P ⇒ Q) t with holds? {A} {✓} P t
... | false = true
... | true = holds? {A} {✓} Q t
holds? {A} {✓} (X P) [] = false
holds? {A} {✓} (X P) (_ ∷ t) = holds? {A} {✓} P t
holds? {A} {✓} (G P) [] = true
holds? {A} {✓} (G P) (x ∷ t) = (holds? {A} {✓} P (x ∷ t)) Bool.∧ (holds? {A} {✓} P t)
holds? {A} {✓} (F P) [] = holds? {A} {✓} P []
holds? {A} {✓} (F P) (x ∷ t) = (holds? {A} {✓} P (x ∷ t)) Bool.∨ (holds? {A} {✓} P t)
holds? {A} {✓} (P U Q) t with holds? {A} {✓} Q t
holds? {A} {✓} (P U Q) t | true = true
holds? {A} {✓} (P U Q) [] | false = holds? {A} {✓} P []
holds? {A} {✓} (P U Q) (x ∷ t) | false = (holds? {A} {✓} P (x ∷ t)) Bool.∧ (holds? {A} {✓} (P U Q) t)

```
