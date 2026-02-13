---
title: Communicating Sequential Processes
layout: page
---

```
{-# OPTIONS --type-in-type #-}
module Traces.CSP where
```
## Imports

```
open import abstract-set-theory.Prelude using (Type)

open import Data.List as List using (List; []; _∷_; [_]; _++_; map; concatMap; filter; take)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_)
```

## Processes

This is the standard definition of CSP processes. It is parameterised over an alphabet, and a
success element of that alphabet that is added to a traces if the process terminates successfully.
```
data Process (A : Type) (✓ : A) : Type where
  STOP SKIP : Process A ✓
  _➔_ : A → Process A ✓ → Process A ✓
  _□_ _⊓_ : Process A ✓ → Process A ✓ → Process A ✓
  _∥⦅_⦆_ : Process A ✓ → (A → Set) → Process A ✓ → Process A ✓
-- TODO: leave fixpoints and hiding for now!
--  fix : (Process A ✓ → Process A ✓) → Process A ✓
--  _-_ : Process A ✓ → (A → Set) → Process A ✓
```
## Trace Semantics
```
module _ {A : Type} {✓ : A} where

```
Synchronisation limits the two sides to synchronise over the given set of events. A process cannot continue
its trace if the head element needs to synchronise, and isn't the head element of the partner process.
```
  _∥ᵗ⦅_⦆_ : List A → (A → Set) → List A → List (List A)
  Pt ∥ᵗ⦅ A ⦆ Qt = {!!}

  traces : Process A ✓ → List (List A)
  traces STOP = [ [] ]
  traces SKIP = [] ∷ [ ✓ ] ∷ []
  traces (a ➔ P) = [ [] ] ++ map (λ t → a ∷ t) (traces P)
  traces (P □ Q) = traces P ++ traces Q
  traces (P ⊓ Q) = traces P ++ traces Q
  traces (P ∥⦅ A ⦆ Q) = concatMap (λ s → concatMap (λ t → s ∥ᵗ⦅ A ⦆ t) (traces Q)) (traces P)

```
## Examples
```
  module Example (a : A) where
    P : Process A ✓
    P = SKIP □ (a ➔ SKIP)

    ex1 : List (List A)
    ex1 = take 10 (traces P) -- [ [] , [ ✓ ] , [ a ] , [ a , ✓ ] ]

-- You can express infinite recursion, but Agda gets upset!
--    Q : Process A ✓
--    Q = SKIP □ (a ➔ Q)
```
