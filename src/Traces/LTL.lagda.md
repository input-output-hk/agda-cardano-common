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
open import Data.Bool as Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Bool.ListAction using (all)
open import Relation.Nullary as Null using (yes; no; Dec; contradiction)

open import Traces.CSP using (Trace; Process; Alphabet)
```
## Propositions and Operators
```
data Prop (α : Alphabet) : Type where
  ¬_ : Prop α → Prop α
  _∧_ : Prop α → Prop α → Prop α
  _∨_ : Prop α → Prop α → Prop α
  _⇒_ : Prop α → Prop α → Prop α
  X_ : Prop α → Prop α
  G_ : Prop α → Prop α
  F_ : Prop α → Prop α
  _U_ : Prop α → Prop α → Prop α
```
## Evaluation over Traces
```
module TraceLTL {α : Alphabet} where
  open Traces.CSP.TraceSemantics {α}

  {-# NO_POSITIVITY_CHECK #-}
  data Holds : Prop α → Trace α → Type where
    ¬_ : {P : Prop α}
      → {t : Trace α}
      → Null.¬ (Holds P t)
      → Holds (¬ P) t
    _∧_ : {P Q : Prop α}
      → {t : Trace α}
      → Holds P t
      → Holds Q t
      → Holds (P ∧ Q) t
    ∨₁_ : {P Q : Prop α}
      → {t : Trace α}
      → Holds P t
      → Holds (P ∨ Q) t
    ∨₂_ : {P Q : Prop α}
      → {t : Trace α}
      → Holds Q t
      → Holds (P ∨ Q) t
    ⇒₁ : {P Q : Prop α}
      → {t : Trace α}
      → Null.¬ (Holds P t)
      → Holds (P ⇒ Q) t
    _⇒₂_ : {P Q : Prop α}
      → {t : Trace α}
      → Holds P t
      → Holds Q t
      → Holds (P ⇒ Q) t
    X_ : {P : Prop α}
      → {x : Alphabet.A α}
      → {t : Trace α}
      → Holds P t
      → Holds (X P) (x ∷ t)
    G₁ : {P : Prop α}
      → Holds (G P) ⟨⟩
    G₂ : {P : Prop α}
      → {x : Alphabet.A α}
      → {t : Trace α}
      → Holds P (x ∷ t)
      → Holds P t
      → Holds (G P) (x ∷ t)
    F₁ : {P : Prop α}
     → {t : Trace α}
      → Holds P t
      → Holds (F P) t
    F₂ : {P : Prop α}
     → {x : Alphabet.A α}
      → {t : Trace α}
      → Holds (F P) t
      → Holds (F P) (x ∷ t)
    U₁_ : {P Q : Prop α}
      → {t : Trace α}
      → Holds Q t
      → Holds (P U Q) t
    _U₂_ : {P Q : Prop α}
       → {x : Alphabet.A α}
      → {t : Trace α}
      → Holds P (x ∷ t)
      → Holds (P U Q) t
      → Holds (P U Q) (x ∷ t)
    U₃_ : {P Q : Prop α}
      → Holds P []
      → Holds (P U Q) []
```
## Decision procedure
```
  holds? : (P : Prop α) → (t : Trace α) → Dec (Holds P t)
  holds? (¬ P) t with holds? P t
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
  holds?ᵇ : {α : Alphabet} → Prop α → Trace α → Bool
  holds?ᵇ (¬ P) t with holds?ᵇ P t
  ... | true = false
  ... | false = true
  holds?ᵇ (P ∧ Q) t = (holds?ᵇ P t) Bool.∧ (holds?ᵇ Q t)
  holds?ᵇ (P ∨ Q) t = (holds?ᵇ P t) Bool.∨ (holds?ᵇ Q t)
  holds?ᵇ (P ⇒ Q) t with holds?ᵇ P t
  ... | false = true
  ... | true = holds?ᵇ Q t
  holds?ᵇ (X P) [] = false
  holds?ᵇ (X P) (_ ∷ t) = holds?ᵇ P t
  holds?ᵇ (G P) [] = true
  holds?ᵇ (G P) (x ∷ t) = (holds?ᵇ P (x ∷ t)) Bool.∧ (holds?ᵇ P t)
  holds?ᵇ (F P) [] = holds?ᵇ P []
  holds?ᵇ (F P) (x ∷ t) = (holds?ᵇ P (x ∷ t)) Bool.∨ (holds?ᵇ (F P) t)
  holds?ᵇ (P U Q) t with holds?ᵇ Q t
  holds?ᵇ (P U Q) t | true = true
  holds?ᵇ (P U Q) [] | false = holds?ᵇ P []
  holds?ᵇ (P U Q) (x ∷ t) | false = (holds?ᵇ P (x ∷ t)) Bool.∧ (holds?ᵇ (P U Q) t)

```
## LTLs over Processes
```
  holds?ᵖ : Prop α → Process α → Bool
  holds?ᵖ Prop P = all (holds?ᵇ Prop) (traces P)
```
## Examples
```


```
