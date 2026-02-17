---
title: Communicating Sequential Processes
layout: page
---

```
{-# OPTIONS --type-in-type --guardedness #-}
module Traces.CSP where
```
## Imports

```
open import abstract-set-theory.Prelude using (Type; Maybe; nothing; just; DecEq; _≡_; _≟_; refl)
open import Axiom.Set renaming (Theoryᵈ to AbSet)
open import Data.List as List using (List; []; _∷_; [_]; _++_; map; concatMap; filter; take; find)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_; yes; no; Dec)
open import Relation.Binary.Definitions using (DecidableEquality)
```

## Processes

This is the standard definition of CSP processes. It is parameterised over an alphabet, and a
success element of that alphabet that is added to a traces if the process terminates successfully.

Processes can be infinite, so this type isn't "positive" in Agda's terms.
```
{-# NO_POSITIVITY_CHECK #-}
data Process (A : Type) (✓ : A) : Type where
  STOP SKIP : Process A ✓
  _➔_ : A → Process A ✓ → Process A ✓
  _□_ _⊓_ : Process A ✓ → Process A ✓ → Process A ✓
  _∥⦅_⦆_ : Process A ✓ → List A → Process A ✓ → Process A ✓
--  fix : (Process A ✓ → Process A ✓) → Process A ✓
```
## Trace Semantics

Traces are potentially infinite, but also potentially finite (or very finite, in the case of `⟨⟩`). We can
define them as a coninductive record, but we will just use lists since this work is intended to support
trace based testing, which is necessarily finite.
```
module _ {A : Type} {✓ : A} {{DEA : DecEq A}} where

  open import Data.List.Membership.DecPropositional (DecEq._≟_ DEA) using (_∈_; _∈?_; _∉?_)

  Trace : Type → Type
  Trace A = List A

  ⟨⟩ : Trace A
  ⟨⟩ = []

  ⟨_⟩ : A → Trace A
  ⟨ a ⟩ = [ a ]
```
The posibility of the empty trace makes some of the concatenation co-patterns a bit intricate.

Also, if the first trace is infinite then expanding the concatenation will never terminate.
```
  {-# NON_TERMINATING #-}
  _^_ : Trace A → Trace A → Trace A
  _^_ = _++_
```

## Trace Semantics

Synchronisation limits the two sides to synchronise over the given set of events. A process cannot continue
its trace if the head element needs to synchronise, and isn't the head element of the partner process.

For finite traces this will terminate, although the interleavings can get large quickly.
```
  {-# TERMINATING #-}
  _∥ᵗ⦅_⦆_ : Trace A → List A → Trace A → List (Trace A)
  [] ∥ᵗ⦅ As ⦆ [] = [ ⟨⟩ ]
  [] ∥ᵗ⦅ As ⦆ (q ∷ Qt) with q ∈? As
  ... | yes m = [ ⟨⟩ ]
  ... | no ¬m = ⟨⟩ ∷ (map (λ t → ⟨ q ⟩ ^ t) ([] ∥ᵗ⦅ As ⦆ Qt))
  (p ∷ Pt) ∥ᵗ⦅ As ⦆ [] with p ∈? As
  ... | yes m = [ ⟨⟩ ]
  ... | no ¬m = ⟨⟩ ∷ (map (λ t → ⟨ p ⟩ ^ t) (Pt ∥ᵗ⦅ As ⦆ []))
  (p ∷ Pt) ∥ᵗ⦅ As ⦆ (q ∷ Qt) with p ≟ q | p ∈? As | q ∈? As
  ... | yes refl | yes pin | _ = ⟨⟩ ∷ (map (λ t → ⟨ p ⟩ ^ t) (Pt ∥ᵗ⦅ As ⦆ Qt))
  ... | yes refl | no ¬pin | _ = ⟨⟩ ∷ ((map (λ t → ⟨ p ⟩ ^ t) (Pt ∥ᵗ⦅ As ⦆ (q ∷ Qt))) ++ (map (λ t → ⟨ q ⟩ ^ t) ((p ∷ Pt) ∥ᵗ⦅ As ⦆ Qt)))
  ... | no ¬p=q | pin | qin = ⟨⟩ ∷ ((pfirst pin) ++ (qfirst qin))
    where
      pfirst : Dec (p ∈ As) → List (Trace A)
      pfirst (yes pin) = [ ⟨⟩ ]
      pfirst (no ¬pin) = ⟨⟩ ∷ (map (λ t → ⟨ p ⟩ ^ t) (Pt ∥ᵗ⦅ As ⦆ (q ∷ Qt)))
      qfirst : Dec (q ∈ As) → List (Trace A)
      qfirst (yes qin) = [ ⟨⟩ ]
      qfirst (no ¬qin) = ⟨⟩ ∷ (map (λ t → ⟨ q ⟩ ^ t) ((p ∷ Pt) ∥ᵗ⦅ As ⦆ Qt))

```

The trace semantics of the other constructors follows the original book, with the addition of the termination
success element when we reach `SKIP`.
```
  traces : Process A ✓ → List (Trace A)
  traces STOP = [ ⟨⟩ ]
  traces SKIP = ⟨⟩ ∷ (⟨ ✓ ⟩) ∷ []
  traces (a ➔ P) = [ ⟨⟩ ] ++ map (λ t → ⟨ a ⟩ ^ t ) (traces P)
  traces (P □ Q) = traces P ++ traces Q
  traces (P ⊓ Q) = traces P ++ traces Q
  traces (P ∥⦅ As ⦆ Q) = concatMap (λ s → concatMap (λ t → s ∥ᵗ⦅ As ⦆ t) (traces Q)) (traces P)
--  traces (fix Px) = {!!}
```
## Examples
```
  module Example (a : A) (b : A) (c : A) where
    P : Process A ✓
    P = SKIP □ (a ➔ SKIP)

    ex1 : traces P ≡ [] ∷ (✓ ∷ []) ∷ [] ∷ ((a ∷ []) ^ []) ∷ ((a ∷ []) ^ (✓ ∷ [])) ∷ []
    ex1 = refl

    R : Process A ✓
    R = a ➔ (c ➔ (b ➔ SKIP))

    S : Process A ✓
    S = b ➔ (c ➔ (a ➔ SKIP))

    P2 : Process A ✓
    P2 = R ∥⦅ [ c ] ⦆ S

    -- with c synchronising and a and b not synchronising, we should get several interleavings before and after c
    -- You can expand this in emacs, but its a bit long to list here!
    -- ex2 : traces P2 ≡ {!!}
    -- ex2 = refl

-- You can express infinite recursion, but Agda gets upset!
--    Q : Process A ✓
--    Q = SKIP □ (a ➔ Q)
```
