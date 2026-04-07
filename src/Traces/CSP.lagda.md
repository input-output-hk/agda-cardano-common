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
open import abstract-set-theory.FiniteSetTheory using (ℙ_; ∅; mapˢ; concatMapˢ; fromList; _⇀_; fromListᵐ; _∪_; _∪ˡ_; _∩_; _＼_; lookupᵐ?) renaming (❴_❵ˢ to ⟪_⟫; insert to insertᵐ; setToList to toList)
open import Data.List as List using (List; []; _∷_; [_]; _++_; map; concatMap; filter; take; find)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_; yes; no; Dec; contradiction)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Product using (_×_; _,_; Σ; ∃)
open import Relation.Binary.PropositionalEquality using (cong)
open import Function.Base using (_$_)

-- FIXME: This is buried in FiniteSetTheory but I don't
-- want to spend the morning trying to get the import to work!
postulate
  toListᵐ : {X Y : Type} → X ⇀ Y → List (X × Y)

```
Alphabets contain a set of events, a "success event", and an instance of decidable equality for the events.
```
--open import Tactic.Derive.DecEq

record Alphabet : Type where
  field A : Type
        ✓ : A
        all : ℙ A
        {{ DecEq-A }} : DecEq A
  data A⁺ : Type where
    τ : A⁺
    `_ : A → A⁺

  instance
    DecEq-A⁺ : DecEq A⁺
    DecEq-A⁺ ._≟_ (` a) (` b) with a ≟ b
    ... | yes a≡b = yes $ cong `_ a≡b
    ... | no a≢b = no λ{ refl → a≢b refl }
    DecEq-A⁺ ._≟_ τ τ = yes refl
    DecEq-A⁺ ._≟_ τ (` _) = no λ ()
    DecEq-A⁺ ._≟_ (` _) τ = no λ ()

--unquoteDecl DecEq-A⁺ = derive-DecEq [ (quote Alphabet.A⁺ , DecEq-A⁺) ]
```

## Processes

This is the standard definition of CSP processes. It is parameterised over an alphabet, and a
success element of that alphabet that is added to a traces if the process terminates successfully.

Processes can be infinite, so this type isn't "positive" in Agda's terms.
```
infixr 20 _➔_
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

```
Trace : Alphabet → Type
Trace 𝕒 = List (Alphabet.A 𝕒)
```
Trace sets ought to be proper sets with uniqueness, but we can use `List` for now to make
mechanisation easier.
```
TraceSet : Alphabet → Type
TraceSet 𝕒 = ℙ (Trace 𝕒)
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

```

## Trace Semantics

Synchronisation limits the two sides to synchronise over the given set of events. A process cannot continue
its trace if the head element needs to synchronise, and isn't the head element of the partner process. Events
not in the synchronisation set are available to synchronise with the environment (or outer parallel compositions).

For finite traces this will terminate, although the interleavings can get large quickly.
```
  {-# TERMINATING #-}
  _∥ᵗ⦅_⦆_ : Trace α → List A → Trace α → TraceSet α
  [] ∥ᵗ⦅ As ⦆ [] = ⟪ ⟨⟩ ⟫
  [] ∥ᵗ⦅ As ⦆ (q ∷ Qt) with q ∈? As
  ... | yes m = ⟪ ⟨⟩ ⟫
  ... | no ¬m = fromList (⟨⟩ ∷ (map (λ t → ⟨ q ⟩ ^ t) (toList ([] ∥ᵗ⦅ As ⦆ Qt))))
  (p ∷ Pt) ∥ᵗ⦅ As ⦆ [] with p ∈? As
  ... | yes m = ⟪ ⟨⟩ ⟫
  ... | no ¬m = fromList (⟨⟩ ∷ (map (λ t → ⟨ p ⟩ ^ t) (toList (Pt ∥ᵗ⦅ As ⦆ []))))
  (p ∷ Pt) ∥ᵗ⦅ As ⦆ (q ∷ Qt) with p ≟ q | p ∈? As | q ∈? As
  ... | yes refl | yes pin | _ = ⟪ ⟨⟩ ⟫ ∪ (mapˢ (λ t → ⟨ p ⟩ ^ t) (Pt ∥ᵗ⦅ As ⦆ Qt))
  ... | yes refl | no ¬pin | _ = ⟪ ⟨⟩ ⟫ ∪ (mapˢ (λ t → ⟨ p ⟩ ^ t) (Pt ∥ᵗ⦅ As ⦆ (q ∷ Qt))) ∪ (mapˢ (λ t → ⟨ q ⟩ ^ t) ((p ∷ Pt) ∥ᵗ⦅ As ⦆ Qt))
  ... | no ¬p=q | pin | qin = ⟪ ⟨⟩ ⟫ ∪ (pfirst pin) ∪ (qfirst qin)
    where
      pfirst : Dec (p ∈ As) → TraceSet α
      pfirst (yes pin) = ⟪ ⟨⟩ ⟫
      pfirst (no ¬pin) = ⟪ ⟨⟩ ⟫ ∪ (mapˢ (λ t → ⟨ p ⟩ ^ t) (Pt ∥ᵗ⦅ As ⦆ (q ∷ Qt)))
      qfirst : Dec (q ∈ As) → TraceSet α
      qfirst (yes qin) = ⟪ ⟨⟩ ⟫
      qfirst (no ¬qin) = ⟪ ⟨⟩ ⟫ ∪ (mapˢ (λ t → ⟨ q ⟩ ^ t) ((p ∷ Pt) ∥ᵗ⦅ As ⦆ Qt))
```

The trace semantics of the other constructors follows the original book, with the addition of the termination
success element when we reach `SKIP`.
```
  traces : Process α → TraceSet α
  traces STOP = ⟪ ⟨⟩ ⟫
  traces SKIP = ⟪ ⟨⟩ ⟫ ∪ ⟪ ⟨ ✓ ⟩ ⟫
  traces (a ➔ P) = ⟪ ⟨⟩ ⟫ ∪ mapˢ (λ t → ⟨ a ⟩ ^ t ) (traces P)
  traces (P □ Q) = traces P ∪ traces Q
  traces (P ⊓ Q) = traces P ∪ traces Q
  traces (P ∥⦅ As ⦆ Q) = concatMapˢ (λ s → concatMapˢ (λ t → s ∥ᵗ⦅ As ⦆ t) (traces Q)) (traces P)
-- traces (fix Px) = {!!}
-- Hiding
-- Renaming
```
[Brookes et al.](https://www.cs.cmu.edu/~brookes/papers/OperationalSemanticsCSP.pdf) include some other helpful definitions.
```
  initials : Process α → ℙ A
  initials STOP = ∅
  initials SKIP = ⟪ ✓ ⟫
  initials (x ➔ P) = ⟪ x ⟫
  initials (P □ Q) = initials P ∪ initials Q
  initials (P ⊓ Q) = initials P ∪ initials Q
  initials (P ∥⦅ As ⦆ Q) with initials P | initials Q | fromList As
  ... | ip | iq | as = (ip ∩ iq ∩ as) ∪ (ip ＼ as) ∪ (iq ＼ as)
```
## Examples
```
  module Example (a : A) (b : A) (c : A) where
    P : Process α
    P = SKIP □ (a ➔ SKIP)

    -- This is hard to prove because the union operator applies some
    -- opaque or not unrolled operations.
    --ex1 : traces P ≡ (⟪ ⟨⟩ ⟫ ∪ ⟪ ⟨ ✓ ⟩ ⟫ ∪ ⟪ ⟨⟩ ⟫ ∪ ⟪ ⟨ a ⟩ ⟫ ∪ ⟪ ⟨ a ⟩ ^ ⟨ ✓ ⟩ ⟫)
    --ex1 = {!!}

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

## Reduction Semantics

For infinite traces and inductive proofs, a small step reduction semantics is useful.

```
module Reduction (α : Alphabet) where
  open Alphabet α

  open import Data.List.Membership.DecPropositional (DecEq._≟_ DecEq-A) using (_∈_; _∉_; _∈?_; _∉?_)

  data _─_⟶_ : Process α → A⁺ → Process α → Type where
    prefix : {a : A} {P : Process α}
      → (a ➔ P) ─ ` a ⟶ P
    □₁ : {a : A} {P Q P' : Process α}
      → P ─ ` a ⟶ P'
      → (P □ Q) ─ ` a ⟶ P'
    □₂ : {a : A} {P Q Q' : Process α}
      → Q ─ ` a ⟶ Q'
      → (P □ Q) ─ ` a ⟶ Q'
    □₃ : {P Q P' : Process α}
      → P ─ τ ⟶ P'
      → (P □ Q) ─ τ ⟶ P
    □₄ : {P Q P' : Process α}
      → P ─ τ ⟶ P'
      → (P □ Q) ─ τ ⟶ (P' □ Q)
    □₅ : {P Q Q' : Process α}
      → Q ─ τ ⟶ Q'
      → (P □ Q) ─ τ ⟶ (P □ Q')
    ⊓₁ : {P Q : Process α}
      → (P ⊓ Q) ─ τ ⟶ P
    ⊓₂ : {P Q : Process α}
      → (P ⊓ Q) ─ τ ⟶ Q
    ∥₁ : {a : A} {P Q P' Q' : Process α} {As : List A}
      → a ∈ As
      → P ─ ` a ⟶ P'
      → Q ─ ` a ⟶ Q'
      → (P ∥⦅ As ⦆ Q) ─ ` a ⟶ (P' ∥⦅ As ⦆ Q')
    ∥₂ : {a : A} {P Q P' : Process α} {As : List A}
      → a ∉ As
      → P ─ ` a ⟶ P'
      → (P ∥⦅ As ⦆ Q) ─ ` a ⟶ (P' ∥⦅ As ⦆ Q)
    ∥₃ : {a : A} {P Q Q' : Process α} {As : List A}
      → a ∉ As
      → Q ─ ` a ⟶ Q'
      → (P ∥⦅ As ⦆ Q) ─ ` a ⟶ (P ∥⦅ As ⦆ Q')
    ∥₄ : {P Q P' : Process α} {As : List A}
      → P ─ τ ⟶ P'
      → (P ∥⦅ As ⦆ Q) ─ τ ⟶ (P' ∥⦅ As ⦆ Q)
    ∥₅ : {P Q Q' : Process α} {As : List A}
      → Q ─ τ ⟶ Q'
      → (P ∥⦅ As ⦆ Q) ─ τ ⟶ (P ∥⦅ As ⦆ Q')
    SKIP : SKIP ─ ` ✓ ⟶ STOP
```
Since CSP is deliberatley non-deterministic, especially with parallel composition, we can't do a simple, decidable decision procedure.
We can decide whether, for a particular event, a process will reduce and synchronise with that event.
```
  reduces? : (P : Process α) → (a : A) → Dec (∃ (λ (P' : Process α) → P ─ ` a ⟶ P'))
  reduces? STOP a = no (λ ())
  reduces? SKIP a with a ≟ ✓
  ... | no a≠✓ = no λ { (STOP , SKIP) → a≠✓ refl }
  ... | yes refl = yes (STOP , SKIP)
  reduces? (x ➔ P) a with x ≟ a
  ... | yes refl = yes (P , prefix)
  ... | no x≠a = no (λ { (P' , prefix) → x≠a refl} )
  reduces? (P □ Q) a with reduces? P a | reduces? Q a
  ... | yes (P' , pr) | _ = yes (P' , □₁ pr)
  ... | _ | yes (Q' , qr) = yes (Q' , □₂ qr)
  ... | no ¬pr | no ¬qr = no λ { (PQ' , □₁ pr) → ¬pr (PQ' , pr) ; (PQ' , □₂ pr) → ¬qr (PQ' , pr) }
  reduces? (P ⊓ Q) a = no (λ ())
  reduces? (P ∥⦅ As ⦆ Q) a with a ∈? As
  reduces? (P ∥⦅ As ⦆ Q) a | no a∉As with reduces? P a | reduces? Q a
  ... | yes (P' , pr) | _ = yes ((P' ∥⦅ As ⦆ Q) , ∥₂ a∉As pr)
  ... | _ | yes (Q' , qr) = yes ((P ∥⦅ As ⦆ Q') , ∥₃ a∉As qr)
  ... | no ¬pr | no ¬qr = no (λ { (PQ' , ∥₁ x pr pr₁) → a∉As x ; (PQ' , ∥₂ x pr) → ¬pr (_ , pr) ; (PQ' , ∥₃ x pr) → ¬qr (_ , pr) })
  reduces? (P ∥⦅ As ⦆ Q) a | yes a∈As with reduces? P a | reduces? Q a
  ... | yes (P' , pr) | yes (Q' , qr) = yes ((P' ∥⦅ As ⦆ Q') , ∥₁ a∈As pr qr)
  ... | no ¬pr        | _ = no (λ { (PQ' , ∥₁ x pr pr₁) → ¬pr (_ , pr) ; (PQ' , ∥₂ x pr) → x a∈As ; (PQ' , ∥₃ x pr) → x a∈As })
  ... | _                 | no ¬qr = no (λ { (PQ' , ∥₁ x pr pr₁) → ¬qr (_ , pr₁) ; (PQ' , ∥₂ x pr) → x a∈As ; (PQ' , ∥₃ x pr) → x a∈As })

```
## Failure Semantics

"Failures" are really the lists of events that are rejected at each step along a trace. This is not automatically the
rest of the alphabet, since it may be that this is the trace of one path, but others are available. Consequently, this is
a richer and more useful definition of what is and isn't possible in a system.
```

FailureSet : Alphabet → Type
FailureSet 𝕒 = (Trace 𝕒) ⇀ ℙ Alphabet.A 𝕒

module FailureSemantics {α : Alphabet} where
  open TraceSemantics {α}
  open Alphabet α
  open import Data.List.Membership.DecPropositional (DecEq._≟_ DecEq-A) using (_∈_; _∈?_; _∉?_)

  _excluding_ : ℙ A → List A → ℙ A
  a excluding as = fromList (filter (λ x → x ∉? as) (toList a))
{-
-- FIXME: Actually, this probably can't be a map because the internal choice will have two failure elements for ⟨⟩
  failures : Process α → FailureSet α
  failures STOP = fromListᵐ [ (⟨⟩ , all) ]
  failures SKIP = fromListᵐ ((⟨⟩ , all excluding [ ✓ ]) ∷ (⟨ ✓ ⟩ , all) ∷ [])
  failures (x ➔ P) = fromListᵐ ([ (⟨⟩ , (all excluding [ x ])) ] ++ (concatMap (λ { (t , f) → (⟨ x ⟩ ^ t , f) ∷ [] }) (toListᵐ (failures P))))
  failures (P □ Q) with failures P | failures Q
  ... | fP | fQ with lookupᵐ? fP ⟨⟩ | lookupᵐ? fQ ⟨⟩
  ... | just fp | just fq = (insertᵐ fP ⟨⟩ (fp excluding (toList (all excluding (toList fq))))) ∪ˡ (insertᵐ fQ ⟨⟩ (fq excluding (toList (all excluding (toList fp)))))
  ... | _ | nothing = fP ∪ˡ fQ
  ... | nothing | _ = fP ∪ˡ fQ
  failures (P ⊓ Q) = {!!} -- (failures P) ++ (failures Q) -- FIXME: is this right?
  failures (P ∥⦅ x ⦆ Q) = {!!}
  -}
```
