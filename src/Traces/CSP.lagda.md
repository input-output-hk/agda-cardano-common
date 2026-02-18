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
Alphabets contain a set of events, a "success event", and an instance of decidable equality for the events.
```
record Alphabet : Type where
  field A : Type
        ✓ : A
        all : List A
        {{ DecEq-A }} : DecEq A

```

## Processes

This is the standard definition of CSP processes. It is parameterised over an alphabet, and a
success element of that alphabet that is added to a traces if the process terminates successfully.

Processes can be infinite, so this type isn't "positive" in Agda's terms.
```
{-# NO_POSITIVITY_CHECK #-}
data Process (α : Alphabet) : Type where
  STOP SKIP : Process α
  _➔_ : (Alphabet.A α) → Process α → Process α
  _□_ _⊓_ : Process α → Process α → Process α
  _∥⦅_⦆_ : Process α → List (Alphabet.A α) → Process α → Process α
--  fix : (Process α → Process α) → Process α
```
## Trace Semantics

Traces are potentially infinite, but also potentially finite (or very finite, in the case of `⟨⟩`). We can
define them as a coninductive record, but we will just use lists since this work is intended to support
trace based testing, which is necessarily finite.

Traces need Alphabets, even if they only use the elements at the moment.
```
Trace : Alphabet → Type
Trace 𝕒 = List (Alphabet.A 𝕒)

```
Trace sets ought to be proper sets with uniqueness, but we can use `List` for now to make
mechanisation easier.
```
TraceSet : Alphabet → Type
TraceSet 𝕒 = List (Trace 𝕒)
```
## Trace Semantics

This section defines the traces possible for a given `Process` using a particular `Alphabet`.
```
module TraceSemantics {α : Alphabet} where
  open Alphabet α
  open import Data.List.Membership.DecPropositional (DecEq._≟_ DecEq-A) using (_∈_; _∈?_; _∉?_)

  ⟨⟩ : Trace α
  ⟨⟩ = []

  ⟨_⟩ : A → Trace α
  ⟨ a ⟩ = [ a ]

  _^_ : Trace α → Trace α → Trace α
  _^_ = _++_

  _∪_ : TraceSet α → TraceSet α → TraceSet α
  _∪_ = _++_
```

## Trace Semantics

Synchronisation limits the two sides to synchronise over the given set of events. A process cannot continue
its trace if the head element needs to synchronise, and isn't the head element of the partner process. Events
not in the synchronisation set are available to synchronise with the environment (or outer parallel compositions).

For finite traces this will terminate, although the interleavings can get large quickly.
```

  {-# TERMINATING #-}
  _∥ᵗ⦅_⦆_ : Trace α → List A → Trace α → TraceSet α
  [] ∥ᵗ⦅ As ⦆ [] = [ ⟨⟩ ]
  [] ∥ᵗ⦅ As ⦆ (q ∷ Qt) with q ∈? As
  ... | yes m = [ ⟨⟩ ]
  ... | no ¬m = ⟨⟩ ∷ (map (λ t → ⟨ q ⟩ ^ t) ([] ∥ᵗ⦅ As ⦆ Qt))
  (p ∷ Pt) ∥ᵗ⦅ As ⦆ [] with p ∈? As
  ... | yes m = [ ⟨⟩ ]
  ... | no ¬m = ⟨⟩ ∷ (map (λ t → ⟨ p ⟩ ^ t) (Pt ∥ᵗ⦅ As ⦆ []))
  (p ∷ Pt) ∥ᵗ⦅ As ⦆ (q ∷ Qt) with p ≟ q | p ∈? As | q ∈? As
  ... | yes refl | yes pin | _ = ⟨⟩ ∷ (map (λ t → ⟨ p ⟩ ^ t) (Pt ∥ᵗ⦅ As ⦆ Qt))
  ... | yes refl | no ¬pin | _ = ⟨⟩ ∷ ((map (λ t → ⟨ p ⟩ ^ t) (Pt ∥ᵗ⦅ As ⦆ (q ∷ Qt))) ∪ (map (λ t → ⟨ q ⟩ ^ t) ((p ∷ Pt) ∥ᵗ⦅ As ⦆ Qt)))
  ... | no ¬p=q | pin | qin = ⟨⟩ ∷ ((pfirst pin) ∪ (qfirst qin))
    where
      pfirst : Dec (p ∈ As) → TraceSet α
      pfirst (yes pin) = [ ⟨⟩ ]
      pfirst (no ¬pin) = ⟨⟩ ∷ (map (λ t → ⟨ p ⟩ ^ t) (Pt ∥ᵗ⦅ As ⦆ (q ∷ Qt)))
      qfirst : Dec (q ∈ As) → TraceSet α
      qfirst (yes qin) = [ ⟨⟩ ]
      qfirst (no ¬qin) = ⟨⟩ ∷ (map (λ t → ⟨ q ⟩ ^ t) ((p ∷ Pt) ∥ᵗ⦅ As ⦆ Qt))

```

The trace semantics of the other constructors follows the original book, with the addition of the termination
success element when we reach `SKIP`.
```
  traces : Process α → TraceSet α
  traces STOP = [ ⟨⟩ ]
  traces SKIP = ⟨⟩ ∷ (⟨ ✓ ⟩) ∷ []
  traces (a ➔ P) = [ ⟨⟩ ] ∪ map (λ t → ⟨ a ⟩ ^ t ) (traces P)
  traces (P □ Q) = traces P ∪ traces Q
  traces (P ⊓ Q) = traces P ∪ traces Q
  traces (P ∥⦅ As ⦆ Q) = concatMap (λ s → concatMap (λ t → s ∥ᵗ⦅ As ⦆ t) (traces Q)) (traces P)
--  traces (fix Px) = {!!}
```
## Examples
```
  module Example (a : A) (b : A) (c : A) where
    P : Process α
    P = SKIP □ (a ➔ SKIP)

    ex1 : traces P ≡ [] ∷ (✓ ∷ []) ∷ [] ∷ ((a ∷ []) ^ []) ∷ ((a ∷ []) ^ (✓ ∷ [])) ∷ []
    ex1 = refl

    R : Process α
    R = a ➔ (c ➔ (b ➔ SKIP))

    S : Process α
    S = b ➔ (c ➔ (a ➔ SKIP))

    P2 : Process α
    P2 = R ∥⦅ [ c ] ⦆ S

    -- With c synchronising and a and b not synchronising, we get several interleavings before and after c
    -- You can expand this in emacs, but its a bit long to list here!
    --ex2 : traces P2 ≡ {!!}
    --ex2 = refl

  -- You can express infinite recursion, but Agda gets upset!
  --    Q : Process α
  --    Q = SKIP □ (a ➔ Q)
```
## Failure Semantics

"Failures" are really the lists of events that are rejected at each step along a trace. This is not automatically the
rest of the alphabet, since it may be that this is the trace of one path, but others are available. Consequently, this is
a richer and more useful definition of what is and isn't possible in a system.
```
open import Data.Product using (_×_; _,_)

Failure : Alphabet → Type
Failure 𝕒 = Trace 𝕒 × (List (Alphabet.A 𝕒))

-- FIXME: This might need to be a Map
FailureSet : Alphabet → Type
FailureSet 𝕒 = List (Failure 𝕒)

module FailureSemantics {α : Alphabet} where
  open TraceSemantics {α}
  open Alphabet α
  open import Data.List.Membership.DecPropositional (DecEq._≟_ DecEq-A) using (_∈_; _∈?_; _∉?_)

  _excluding_ : List A → List A → List A
  a excluding as = filter (λ x → x ∉? as) a

{-
  failures : Process α → FailureSet α
  failures STOP = [ (⟨⟩ , all) ]
  failures SKIP = (⟨⟩ , all excluding [ ✓ ]) ∷ (⟨ ✓ ⟩ , all) ∷ []
  failures (x ➔ P) = [ (⟨⟩ , (all excluding [ x ])) ] ++ (concatMap (λ { (t , f) → (⟨ x ⟩ ^ t , f) ∷ [] }) (failures P))
  failures (P □ Q) = {!!} -- (concatMap (λ { (t , f) → {![ (t , f excluding  ]!}} ) (failures P)) ++ ()
  failures (P ⊓ Q) = (failures P) ++ (failures Q) -- FIXME: is this right?
  failures (P ∥⦅ x ⦆ Q) = {!!}
  -}
```
