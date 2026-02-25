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
open import abstract-set-theory.FiniteSetTheory using (ℙ_; mapˢ) renaming (❴_❵ˢ to ⟪_⟫; setToList to toList)

open import Traces.CSP using (Trace; Process; Alphabet; STOP; SKIP; _➔_; _□_; _⊓_; _∥⦅_⦆_)
```
## Propositions and Operators

LTL propositions can use the conventional boolean operators, and four temporal operators:
* X - "NeXt" requires the trace to have the subordinate property from the next event.
* G - "Globally" requires the property to be true for the trace, and all tails.
* F - Eventually ("Future") requires the subordinate property to either be true now or later in the trace.
* U - "Until" - the first property must hold until the second property holds.
b
We also add an operator to inspect the current head event.
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
  `_ : (Alphabet.A α) → Prop α
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
      → Holds (X P) (⟨ x ⟩ ^ t)
    G₁ : {P : Prop α}
      → Holds P ⟨⟩
      → Holds (G P) ⟨⟩
    G₂ : {P : Prop α}
      → {x : Alphabet.A α}
      → {t : Trace α}
      → Holds P (⟨ x ⟩ ^ t)
      → Holds P t
      → Holds (G P) (⟨ x ⟩ ^ t)
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
    hd : {a : Alphabet.A α}
      → {t : Trace α}
      → Holds (` a) (a ∷ t)
```
## Decision procedure
```
  -- trace ⊢ property
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
  holds? (G P) [] with holds? P []
  ... | yes pt = yes (G₁ pt)
  ... | no ¬pt = no λ { (G₁ x) → ¬pt x }
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
  holds? (` a) [] = no λ ()
  holds? (` a) (x ∷ t) with a ≟ x
  ... | yes refl = yes hd
  ... | no a≠x = no λ { hd → a≠x refl }

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
  holds?ᵇ (` a) [] = false
  holds?ᵇ (` a) (x ∷ t) with a ≟ x
  ... | yes refl = true
  ... | no a≠x = false
```
## LTLs over Processes
```
  open import Data.List.Relation.Unary.All using (All; all?)

  Holdsᵖ : Prop α → Process α → Type
  Holdsᵖ P p = All (Holds P) (toList (traces p))

  holds?ᵖ : (P : Prop α) → (p : Process α) → Dec (Holdsᵖ P p)
  holds?ᵖ P p = all? (λ t → holds? P t) (toList (traces p))

  holds?ᵖᵇ : Prop α → Process α → Bool
  holds?ᵖᵇ Prop P = all (holds?ᵇ Prop) (toList (traces P))
```
## Examples
```
  module _ {a b c : Alphabet.A α} where
    open Data.List using (_∷_; [])

    P : Process α
    P = a ➔ (b ➔ (c ➔ SKIP))

    Q : Process α
    Q = a ➔ (c ➔ SKIP)

    R : Process α
    R = P ∥⦅ (a ∷ (c ∷ [])) ⦆ Q

    -- Agda tries to unroll the traces...
    -- This is why the structural approach is needed.
    --a-Before-c : Holdsᵖ ((¬ (` c)) U (` a)) R
    --a-Before-c = (U₃ (¬ (λ ()))) All.∷ {!!}
```
# Structural Satisfaction

The definition above, over the traces of a process, is natural and relevant to the
testing framework, but it requires expanding all the possible traces to do a proof.
As well as being annoying, that is impossible for infinite traces. Instead we can
take a structural induction approach.

```

module Satisfaction (α : Alphabet) where
  open Alphabet α

  infix 1 _⊨_
  {-# NO_POSITIVITY_CHECK #-}
  data _⊨_ : Process α → Prop α → Type where
    _∧_ : {P : Process α} {p q : Prop α}
      → P ⊨ p
      → P ⊨ q
      → P ⊨ p ∧ q
    _∨₁_ : {P : Process α} {p q : Prop α}
      → P ⊨ p
      → P ⊨ p ∨ q
    _∨₂_ : {P : Process α} {p q : Prop α}
      → P ⊨ q
      → P ⊨ p ∨ q
    ¬_ : {P : Process α} {p : Prop α}
      → Null.¬ (P ⊨ p)
      → P ⊨ ¬ p
    imp₁ : {P : Process α} {p q : Prop α}
      → Null.¬ (P ⊨ p)
      → P ⊨ p ⇒ q
    imp₂ : {P : Process α} {p q : Prop α}
      → P ⊨ p
      → P ⊨ q
      → P ⊨ p ⇒ q
    `_ : {P : Process α} {a : A} → a Process.➔ P ⊨ ` a
    F-now : {P : Process α} {p : Prop α}
      → P ⊨ p
      → P ⊨ F p
    F➔ : {P : Process α} {p : Prop α} {a : A}
      → P ⊨ F p
      → a ➔ P ⊨ F p
    -- Since either path is possible, they must both satisfy p
    F□ : {P Q : Process α} {p : Prop α}
      → P ⊨ F p
      → Q ⊨ F p
      → P □ Q ⊨ F p
    F⊓ : {P Q : Process α} {p : Prop α}
      → P ⊨ F p
      → Q ⊨ F p
      → P ⊓ Q ⊨ F p
    -- FIXME: I can't think how to define this without expanding both sides again?
    -- Or we could do something with the head of the trace?...
    -- Or we need a small step reduction semantics?!?
    -- F∥ :
```

We can build a decision procedure for this.

FIXME: Building this raises lots of interesting questions - what propositions can ever be true about
STOP for example? Negative ones, certainly...
```
  _⊨?_ : (P : Process α) → (p : Prop α) → Dec (P ⊨ p)
  STOP ⊨? p = {!!}
  SKIP ⊨? p = {!!}
  (x ➔ P) ⊨? p = {!!}
  (P □ P₁) ⊨? p = {!!}
  (P ⊓ P₁) ⊨? p = {!!}
  (P ∥⦅ x ⦆ P₁) ⊨? p = {!!}
```
