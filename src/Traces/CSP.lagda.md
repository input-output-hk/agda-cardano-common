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
open import abstract-set-theory.Prelude using (Type; Maybe; nothing; just)
open import Data.List as List using (List; []; _∷_; [_]; _++_; map; concatMap; filter; take)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_)
```

## Processes

This is the standard definition of CSP processes. It is parameterised over an alphabet, and a
success element of that alphabet that is added to a traces if the process terminates successfully.
```
{-# NO_POSITIVITY_CHECK #-}
data Process (A : Type) (✓ : A) : Type where
  STOP SKIP : Process A ✓
  _➔_ : A → Process A ✓ → Process A ✓
  _□_ _⊓_ : Process A ✓ → Process A ✓ → Process A ✓
  _∥⦅_⦆_ : Process A ✓ → List A → Process A ✓ → Process A ✓
  fix : (Process A ✓ → Process A ✓) → Process A ✓
```
## Trace Semantics

Traces are potentially infinite, but also potentially finite (or very finite, in the case of `⟨⟩`). We can
define them as a coninductive record.
```
module _ {A : Type} {✓ : A} where

  record Trace (A : Type) : Type where
    coinductive
    field
      hd : Maybe A
      tl : Maybe (Trace A)

  ⟨⟩ : Trace A
  ⟨⟩ = record { hd = nothing ; tl = nothing }

  ⟨_⟩ : A → Trace A
  ⟨ a ⟩ = record { hd = just a ; tl = nothing }
```
The posibility of the empty trace makes some of the concatenation co-patterns a bit intricate.

Also, if the first trace is infinite then expanding the concatenation will never terminate.
```
  {-# NON_TERMINATING #-}
  _^_ : Trace A → Trace A → Trace A
  Trace.hd (t₁ ^ t₂) with Trace.hd t₁
  ... | just a = just a
  ... | nothing with Trace.tl t₁
  ...   | nothing = Trace.hd t₂
  ...   | just tl = Trace.hd (tl ^ t₂)
  Trace.tl (t₁ ^ t₂) with Trace.tl t₁
  ... | just tl = just (tl ^ t₂)
  ... | nothing with Trace.hd t₁
  ...   | just a = just t₂
  ...   | nothing = Trace.tl t₂
```

## Trace Semantics

Synchronisation limits the two sides to synchronise over the given set of events. A process cannot continue
its trace if the head element needs to synchronise, and isn't the head element of the partner process.
```
  _∥ᵗ⦅_⦆_ : Trace A → List A → Trace A → List (Trace A)
  Pt ∥ᵗ⦅ As ⦆ Qt = {!!}
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
  traces (fix P) = {!!}
```
## Examples
```
  module Example (a : A) where
    P : Process A ✓
    P = SKIP □ (a ➔ SKIP)

    ex1 : List (Trace A)
    ex1 = {!traces P!}

-- You can express infinite recursion, but Agda gets upset!
--    Q : Process A ✓
--    Q = SKIP □ (a ➔ Q)
```
