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
open import abstract-set-theory.FiniteSetTheory using (ℙ_; ∅; mapˢ; concatMapˢ; fromList; _⇀_; fromListᵐ; _∪_; _∪ˡ_; _∩_; _＼_; ∈-∩; lookupᵐ?) renaming (❴_❵ˢ to ⟪_⟫; insert to insertᵐ; setToList to toList)
open import Data.List as List using (List; []; _∷_; [_]; _++_; map; concatMap; filter; take; find)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ˡ_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_; yes; no; Dec; contradiction)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Product using (_×_; _,_; Σ; ∃; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym)
open import Function.Base using (_$_)

toListᵐ : {X Y : Type} → X ⇀ Y → List (X × Y)
toListᵐ m = toList (proj₁ m)

```
Alphabets contain a set of events, a "success event", and an instance of decidable equality for the events.
```
--open import Tactic.Derive.DecEq

record Alphabet : Type where
  field A : Type
        ✓ : A
        all : ℙ A
        {{ DecEq-A }} : DecEq A
        all-∈ : ∀ (a : A) → a ∈ˡ toList all
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
      → (P □ Q) ─ τ ⟶ (P' □ Q)
    □₄ : {P Q Q' : Process α}
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

  -- One-step τ-successors. Mirrors the τ rules of _─_⟶_. Used alongside
  -- observable followups to reason about weak-step properties: a process is
  -- stable iff τ-followups is empty.
  τ-followups : Process α → List (Process α)
  τ-followups STOP = []
  τ-followups SKIP = []
  τ-followups (_ ➔ _) = []
  τ-followups (P □ Q) = map (_□ Q) (τ-followups P) ++ map (P □_) (τ-followups Q)
  τ-followups (P ⊓ Q) = P ∷ Q ∷ []
  τ-followups (P ∥⦅ As ⦆ Q) =
    map (_∥⦅ As ⦆ Q) (τ-followups P) ++ map (P ∥⦅ As ⦆_) (τ-followups Q)

  -- Observable one-step successors, tagged with the event that drove the step.
  -- Mirrors the ` a ⟶ rules of _─_⟶_ (τ-steps are NOT included — τ-progress
  -- is handled by a separate relation if/when needed).
  followups : Process α → List (A × Process α)
  followups STOP = []
  followups SKIP = (✓ , STOP) ∷ []
  followups (x ➔ P) = (x , P) ∷ []
  followups (P □ Q) = followups P ++ followups Q
  followups (P ⊓ Q) = []  -- ⊓ has only τ-steps; no observable successors
  followups (P ∥⦅ As ⦆ Q) =
      -- P steps alone: event must NOT be in As
      concatMap (λ (a , P') → if does (a ∈? As) then [] else (a , P' ∥⦅ As ⦆ Q) ∷ [])
                (followups P)
    ++
      -- Q steps alone: event must NOT be in As
      concatMap (λ (a , Q') → if does (a ∈? As) then [] else (a , P ∥⦅ As ⦆ Q') ∷ [])
                (followups Q)
    ++
      -- Synchronised step: event must be in As AND match on both sides
      concatMap (λ (a , P') →
        concatMap (λ (b , Q') →
          if does (a ∈? As) ∧ does (a ≟ b) then (a , P' ∥⦅ As ⦆ Q') ∷ [] else [])
          (followups Q))
        (followups P)
    where
      open import Data.Bool using (if_then_else_; _∧_)
      open import Relation.Nullary using (does)
```
## Failure Semantics

"Failures" are really the lists of events that are rejected at each step along a trace. This is not automatically the
rest of the alphabet, since it may be that this is the trace of one path, but others are available. Consequently, this is
a richer and more useful definition of what is and isn't possible in a system.

A failure of a process is a pair `(trace , refusal-set)`: the observed trace together with
a set of events the process can then stably refuse. The type follows Roscoe's failures model.
```

FailureSet : Alphabet → Type
FailureSet 𝕒 = ℙ (Trace 𝕒 × ℙ Alphabet.A 𝕒)

module FailureSemantics {α : Alphabet} where
  open TraceSemantics {α}
  open Alphabet α
  open import Data.List.Membership.DecPropositional (DecEq._≟_ DecEq-A) using (_∈_; _∈?_; _∉?_)
  open import Data.List.Relation.Unary.Any using (here; there)

  _excluding_ : ℙ A → List A → ℙ A
  a excluding as = fromList (filter (λ x → x ∉? as) (toList a))
```

### Structural failure relation

Rather than define `failures` as a set-valued function that eagerly expands all traces,
we give the failure semantics as an inductive relation. `P ⊢ᶠ (s , X)` reads:
"after observable trace `s`, `P` reaches a stable state that refuses every event in `X`".

Internal choice `⊓` has no direct constructor: it is unstable (has a pending τ), so
stepwise reasoning must resolve the τ via the reduction semantics first. This matches
`reduces?`, which also returns `no` for `⊓`. Each base constructor stores the maximal
refusal set; `⊆ᶠ` provides downward closure.

```
  infix 1 _⊢ᶠ_
  data _⊢ᶠ_ : Process α → Trace α × ℙ A → Type where
    STOPᶠ :
        STOP ⊢ᶠ (⟨⟩ , all)
    SKIP⟨⟩ :
        SKIP ⊢ᶠ (⟨⟩ , all ＼ ⟪ ✓ ⟫)
    SKIP✓ :
        SKIP ⊢ᶠ (⟨ ✓ ⟩ , all)
    ➔⟨⟩ : {x : A} {P : Process α}
      → (x ➔ P) ⊢ᶠ (⟨⟩ , all ＼ ⟪ x ⟫)
    ➔step : {x : A} {P : Process α} {s : Trace α} {X : ℙ A}
      → P ⊢ᶠ (s , X)
      → (x ➔ P) ⊢ᶠ (⟨ x ⟩ ^ s , X)
    □⟨⟩ : {P Q : Process α} {X Y : ℙ A}
      → P ⊢ᶠ (⟨⟩ , X)
      → Q ⊢ᶠ (⟨⟩ , Y)
      → P □ Q ⊢ᶠ (⟨⟩ , X ∩ Y)
    □₁ : {P Q : Process α} {s : Trace α} {X : ℙ A}
      → ¬ (s ≡ ⟨⟩)
      → P ⊢ᶠ (s , X)
      → P □ Q ⊢ᶠ (s , X)
    □₂ : {P Q : Process α} {s : Trace α} {X : ℙ A}
      → ¬ (s ≡ ⟨⟩)
      → Q ⊢ᶠ (s , X)
      → P □ Q ⊢ᶠ (s , X)
    ⊆ᶠ : {P : Process α} {s : Trace α} {X Y : ℙ A}
      → (∀ a → a ∈ toList Y → a ∈ toList X)
      → P ⊢ᶠ (s , X)
      → P ⊢ᶠ (s , Y)
    -- Internal choice: the process can τ-pick either branch and inherit its failures.
    -- failures(P ⊓ Q) = failures(P) ∪ failures(Q).
    ⊓₁ᶠ : {P Q : Process α} {s : Trace α} {X : ℙ A}
      → P ⊢ᶠ (s , X)
      → P ⊓ Q ⊢ᶠ (s , X)
    ⊓₂ᶠ : {P Q : Process α} {s : Trace α} {X : ℙ A}
      → Q ⊢ᶠ (s , X)
      → P ⊓ Q ⊢ᶠ (s , X)
    -- ∥ constructors: to add when we tackle parallel failures.
```

### rejects?

Dual to `reduces?`: "does `P` stably refuse `a` right now?". Both return `no` for
unstable processes (pending τ) — τ-progress lives outside this relation. The `{!!}`
holes are small subset / refutation proofs to be filled in.

```
  open import abstract-set-theory.FiniteSetTheory using (List-Model; setToList)
  open import Axiom.Set.Properties List-Model using (∈-filter⁺'; ∈-filter⁻')
  opaque
    unfolding setToList

    ⟪⟫⊆all : ∀ (a b : A) → b ∈ toList ⟪ a ⟫ → b ∈ toList all
    ⟪⟫⊆all a .a (here refl) = all-∈ a

    ⟪⟫⊆all＼ : ∀ (a c : A) → ¬ (a ≡ c) → ∀ b → b ∈ toList ⟪ a ⟫ → b ∈ toList (all ＼ ⟪ c ⟫)
    ⟪⟫⊆all＼ a c a≢c .a (here refl) =
      ∈-filter⁺' ((λ { (here a≡c) → a≢c a≡c }) , all-∈ a)

    ＼-∉ : ∀ {c b : A} → b ∈ toList (all ＼ ⟪ c ⟫) → ¬ (b ∈ toList ⟪ c ⟫)
    ＼-∉ {c} {b} b∈＼ =
      proj₁ (∈-filter⁻' {X = all} {P = λ x → ¬ (x ∈ toList ⟪ c ⟫)} b∈＼)

    ⟪⟫⊆⟪⟫∩⟪⟫ : ∀ (a b : A) → b ∈ toList ⟪ a ⟫ → b ∈ toList (⟪ a ⟫ ∩ ⟪ a ⟫)
    ⟪⟫⊆⟪⟫∩⟪⟫ a .a (here refl) = abstract-set-theory.Prelude.Equivalence.to ∈-∩ (here refl , here refl)

    -- A ➔-process never stably refuses its own head event. Exposed so LTL
    -- (and any other consumer) can discharge the `Null.¬ (a ➔ P ⊢ᶠ (⟨⟩ , ⟪a⟫))`
    -- side-condition without reaching inside `rejects?`.
    ¬➔-refuses-self : ∀ {a : A} {P : Process α} → ¬ ((a ➔ P) ⊢ᶠ (⟨⟩ , ⟪ a ⟫))
    ¬➔-refuses-self = go
      where
        go-gen : ∀ {y : A} {Q : Process α} {X : ℙ A}
          → (y ➔ Q) ⊢ᶠ (⟨⟩ , X) → ¬ (y ∈ toList X)
        go-gen ➔⟨⟩ y∈X = ＼-∉ y∈X (here refl)
        go-gen (⊆ᶠ sub p) y∈Y = go-gen p (sub _ y∈Y)

        go : ∀ {a : A} {P : Process α} → ¬ ((a ➔ P) ⊢ᶠ (⟨⟩ , ⟪ a ⟫))
        go p = go-gen p (here refl)

    -- A ➔-process is never deadlocked: `all` includes its head event, which
    -- is ruled out of the refusal just as in ¬➔-refuses-self.
    ¬➔-deadlocked : ∀ {a : A} {P : Process α} → ¬ ((a ➔ P) ⊢ᶠ (⟨⟩ , all))
    ¬➔-deadlocked = go-all
      where
        go-gen : ∀ {y : A} {Q : Process α} {X : ℙ A}
          → (y ➔ Q) ⊢ᶠ (⟨⟩ , X) → ¬ (y ∈ toList X)
        go-gen ➔⟨⟩ y∈X = ＼-∉ y∈X (here refl)
        go-gen (⊆ᶠ sub p) y∈Y = go-gen p (sub _ y∈Y)

        go-all : ∀ {a : A} {P : Process α} → ¬ ((a ➔ P) ⊢ᶠ (⟨⟩ , all))
        go-all {a} p = go-gen p (all-∈ a)

  rejects? : (P : Process α) → (a : A) → Dec (P ⊢ᶠ (⟨⟩ , ⟪ a ⟫))
  rejects? STOP        a = yes (⊆ᶠ (⟪⟫⊆all a) STOPᶠ)
  rejects? SKIP        a with a ≟ ✓
  ... | yes refl          = no ¬skip✓
    where
      opaque
        unfolding setToList
        -- Anything derivable for SKIP at ⟨⟩ excludes ✓ from its refusal (directly
        -- via SKIP⟨⟩, or by chained ⊆ᶠ composition). Hence ✓ can't appear.
        ¬skip-at-⟨⟩ : ∀ {X : ℙ A} → SKIP ⊢ᶠ (⟨⟩ , X) → ¬ (✓ ∈ toList X)
        ¬skip-at-⟨⟩ SKIP⟨⟩ ✓∈X = ＼-∉ ✓∈X (here refl)
        ¬skip-at-⟨⟩ (⊆ᶠ sub p) ✓∈Y = ¬skip-at-⟨⟩ p (sub ✓ ✓∈Y)

        ¬skip✓ : ¬ (SKIP ⊢ᶠ (⟨⟩ , ⟪ ✓ ⟫))
        ¬skip✓ p = ¬skip-at-⟨⟩ p (here refl)
  ... | no  a≠✓           = yes (⊆ᶠ (⟪⟫⊆all＼ a ✓ a≠✓) SKIP⟨⟩)
  rejects? (x ➔ P)     a with x ≟ a
  ... | yes refl          = no ¬➔a
    where
      opaque
        unfolding setToList
        ¬➔-at-⟨⟩ : ∀ {y} {Q : Process α} {X : ℙ A} → (y ➔ Q) ⊢ᶠ (⟨⟩ , X) → ¬ (y ∈ toList X)
        ¬➔-at-⟨⟩ ➔⟨⟩ y∈X = ＼-∉ y∈X (here refl)
        ¬➔-at-⟨⟩ (⊆ᶠ sub p) y∈Y = ¬➔-at-⟨⟩ p (sub _ y∈Y)

        ¬➔a : ¬ ((a ➔ P) ⊢ᶠ (⟨⟩ , ⟪ a ⟫))
        ¬➔a p = ¬➔-at-⟨⟩ p (here refl)
  ... | no  x≠a           = yes (⊆ᶠ (⟪⟫⊆all＼ a x (λ a≡x → x≠a (sym a≡x))) ➔⟨⟩)
  rejects? (P □ Q)     a with rejects? P a | rejects? Q a
  ... | yes rp | yes rq   = yes (⊆ᶠ (⟪⟫⊆⟪⟫∩⟪⟫ a) (□⟨⟩ rp rq))
  ... | no ¬rp | _        = no (¬□₁-gen ¬rp)
    where
      opaque
        unfolding setToList
        ¬□₁-gen : ∀ {Z : ℙ A} → ¬ (P ⊢ᶠ (⟨⟩ , Z)) → ¬ ((P □ Q) ⊢ᶠ (⟨⟩ , Z))
        ¬□₁-gen ¬rp' (□⟨⟩ {X = X} {Y = Y} rp _) =
          ¬rp' (⊆ᶠ (λ b b∈ → proj₂ (∈-filter⁻' {X = X} {P = λ x → x ∈ toList Y} b∈)) rp)
        ¬□₁-gen ¬rp' (□₁ s≢⟨⟩ _) = s≢⟨⟩ refl
        ¬□₁-gen ¬rp' (□₂ s≢⟨⟩ _) = s≢⟨⟩ refl
        ¬□₁-gen ¬rp' (⊆ᶠ sub p) = ¬□₁-gen (λ rp'' → ¬rp' (⊆ᶠ sub rp'')) p
  ... | _      | no ¬rq   = no (¬□₂-gen ¬rq)
    where
      opaque
        unfolding setToList
        ¬□₂-gen : ∀ {Z : ℙ A} → ¬ (Q ⊢ᶠ (⟨⟩ , Z)) → ¬ ((P □ Q) ⊢ᶠ (⟨⟩ , Z))
        ¬□₂-gen ¬rq' (□⟨⟩ {X = X} {Y = Y} _ rq) =
          ¬rq' (⊆ᶠ (λ b b∈ → proj₁ (∈-filter⁻' {X = X} {P = λ x → x ∈ toList Y} b∈)) rq)
        ¬□₂-gen ¬rq' (□₁ s≢⟨⟩ _) = s≢⟨⟩ refl
        ¬□₂-gen ¬rq' (□₂ s≢⟨⟩ _) = s≢⟨⟩ refl
        ¬□₂-gen ¬rq' (⊆ᶠ sub p) = ¬□₂-gen (λ rq'' → ¬rq' (⊆ᶠ sub rq'')) p
  rejects? (P ⊓ Q)     a with rejects? P a | rejects? Q a
  ... | yes rp | _      = yes (⊓₁ᶠ rp)
  ... | _      | yes rq = yes (⊓₂ᶠ rq)
  ... | no ¬rp | no ¬rq = no (¬⊓-gen ¬rp ¬rq)
    where
      ¬⊓-gen : ∀ {X} → ¬ (P ⊢ᶠ (⟨⟩ , X)) → ¬ (Q ⊢ᶠ (⟨⟩ , X)) → ¬ ((P ⊓ Q) ⊢ᶠ (⟨⟩ , X))
      ¬⊓-gen ¬p ¬q (⊓₁ᶠ p') = ¬p p'
      ¬⊓-gen ¬p ¬q (⊓₂ᶠ q') = ¬q q'
      ¬⊓-gen ¬p ¬q (⊆ᶠ sub p') = ¬⊓-gen (λ r → ¬p (⊆ᶠ sub r)) (λ r → ¬q (⊆ᶠ sub r)) p'
  rejects? (P ∥⦅ As ⦆ Q) a = rejects?-∥-TODO
    where postulate rejects?-∥-TODO : Dec ((P ∥⦅ As ⦆ Q) ⊢ᶠ (⟨⟩ , ⟪ a ⟫))

  -- A process is deadlocked at ⟨⟩ iff it stably refuses every event.
  -- This is the strongest stable refusal: _⊢ᶠ (⟨⟩ , all).
  deadlocked? : (P : Process α) → Dec (P ⊢ᶠ (⟨⟩ , all))
  deadlocked? STOP = yes STOPᶠ
  deadlocked? SKIP = no ¬SKIP-dead
    where
      opaque
        unfolding setToList
        ¬SKIP-dead-at-⟨⟩ : ∀ {X : ℙ A} → SKIP ⊢ᶠ (⟨⟩ , X) → ¬ (✓ ∈ toList X)
        ¬SKIP-dead-at-⟨⟩ SKIP⟨⟩ ✓∈X = ＼-∉ ✓∈X (here refl)
        ¬SKIP-dead-at-⟨⟩ (⊆ᶠ sub p) ✓∈Y = ¬SKIP-dead-at-⟨⟩ p (sub ✓ ✓∈Y)

        ¬SKIP-dead : ¬ (SKIP ⊢ᶠ (⟨⟩ , all))
        ¬SKIP-dead p = ¬SKIP-dead-at-⟨⟩ p (all-∈ ✓)
  deadlocked? (x ➔ P) = no ¬➔-dead
    where
      opaque
        unfolding setToList
        ¬➔-dead-at-⟨⟩ : ∀ {y : A} {Q : Process α} {X : ℙ A}
          → (y ➔ Q) ⊢ᶠ (⟨⟩ , X) → ¬ (y ∈ toList X)
        ¬➔-dead-at-⟨⟩ ➔⟨⟩ y∈X = ＼-∉ y∈X (here refl)
        ¬➔-dead-at-⟨⟩ (⊆ᶠ sub p) y∈Y = ¬➔-dead-at-⟨⟩ p (sub _ y∈Y)

        ¬➔-dead : ¬ ((x ➔ P) ⊢ᶠ (⟨⟩ , all))
        ¬➔-dead p = ¬➔-dead-at-⟨⟩ p (all-∈ x)
  deadlocked? (P □ Q) with deadlocked? P | deadlocked? Q
  ... | yes dp | yes dq = yes (⊆ᶠ all⊆all∩all (□⟨⟩ dp dq))
    where
      opaque
        unfolding setToList
        all⊆all∩all : ∀ a → a ∈ toList all → a ∈ toList (all ∩ all)
        all⊆all∩all a a∈ = ∈-∩ .Equivalence.to (a∈ , a∈)
          where open import Function.Bundles using (Equivalence)
  ... | no ¬dp | _ = no (¬□₁-dead ¬dp)
    where
      opaque
        unfolding setToList
        ¬□₁-dead : {Z : ℙ A} → ¬ (P ⊢ᶠ (⟨⟩ , Z)) → ¬ ((P □ Q) ⊢ᶠ (⟨⟩ , Z))
        ¬□₁-dead ¬dp (□⟨⟩ {X = X} {Y = Y} dpX _) =
          ¬dp (⊆ᶠ (λ a a∈ → proj₂ (∈-filter⁻' {X = X} {P = λ x → x ∈ toList Y} a∈)) dpX)
        ¬□₁-dead ¬dp (□₁ s≢⟨⟩ _) = s≢⟨⟩ refl
        ¬□₁-dead ¬dp (□₂ s≢⟨⟩ _) = s≢⟨⟩ refl
        ¬□₁-dead ¬dp (⊆ᶠ sub p) = ¬□₁-dead (λ r → ¬dp (⊆ᶠ sub r)) p
  ... | _ | no ¬dq = no (¬□₂-dead ¬dq)
    where
      opaque
        unfolding setToList
        ¬□₂-dead : {Z : ℙ A} → ¬ (Q ⊢ᶠ (⟨⟩ , Z)) → ¬ ((P □ Q) ⊢ᶠ (⟨⟩ , Z))
        ¬□₂-dead ¬dq (□⟨⟩ {X = X} {Y = Y} _ dqY) =
          ¬dq (⊆ᶠ (λ a a∈ → proj₁ (∈-filter⁻' {X = X} {P = λ x → x ∈ toList Y} a∈)) dqY)
        ¬□₂-dead ¬dq (□₁ s≢⟨⟩ _) = s≢⟨⟩ refl
        ¬□₂-dead ¬dq (□₂ s≢⟨⟩ _) = s≢⟨⟩ refl
        ¬□₂-dead ¬dq (⊆ᶠ sub p) = ¬□₂-dead (λ r → ¬dq (⊆ᶠ sub r)) p
  deadlocked? (P ⊓ Q) with deadlocked? P | deadlocked? Q
  ... | yes dp | _ = yes (⊓₁ᶠ dp)
  ... | _ | yes dq = yes (⊓₂ᶠ dq)
  ... | no ¬dp | no ¬dq = no (¬⊓-dead-gen ¬dp ¬dq)
    where
      ¬⊓-dead-gen : {Z : ℙ A} → ¬ (P ⊢ᶠ (⟨⟩ , Z)) → ¬ (Q ⊢ᶠ (⟨⟩ , Z)) → ¬ ((P ⊓ Q) ⊢ᶠ (⟨⟩ , Z))
      ¬⊓-dead-gen ¬dp ¬dq (⊓₁ᶠ p) = ¬dp p
      ¬⊓-dead-gen ¬dp ¬dq (⊓₂ᶠ q) = ¬dq q
      ¬⊓-dead-gen ¬dp ¬dq (⊆ᶠ sub p) = ¬⊓-dead-gen (λ r → ¬dp (⊆ᶠ sub r)) (λ r → ¬dq (⊆ᶠ sub r)) p
  deadlocked? (P ∥⦅ As ⦆ Q) = deadlocked?-∥-TODO
    where postulate deadlocked?-∥-TODO : Dec ((P ∥⦅ As ⦆ Q) ⊢ᶠ (⟨⟩ , all))
```

### Old set-valued sketch

Retained for reference while the relation-based definition is fleshed out; to be
deleted once `_⊢ᶠ_` is complete.

```
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
