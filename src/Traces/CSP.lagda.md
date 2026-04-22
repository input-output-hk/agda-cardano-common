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
open import Data.Nat using (ℕ; zero; suc; _+_)
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
infixl 15 _∖_
data Process (α : Alphabet) : Type where
  STOP SKIP : Process α
  _➔_ : (Alphabet.A α) → Process α → Process α
  _□_ _⊓_ : Process α → Process α → Process α
  _∥⦅_⦆_ : Process α → ℙ (Alphabet.A α) → Process α → Process α
  _∖_ : Process α → ℙ (Alphabet.A α) → Process α
--  fix : (Process α → Process α) → Process α
```

A structural size measure on processes. Used to justify termination of
recursions (e.g. the F decision procedure in LTL) that descend through
`followups` / `τ-followups` into subprocesses sitting under `∥` or `∖`,
where the result is syntactically *larger* than the input but semantically
smaller (the nested subprocess has shrunk).
```
processSize : {α : Alphabet} → Process α → ℕ
processSize STOP          = 0
processSize SKIP          = 1  -- must exceed STOP since followups SKIP = [(✓, STOP)]
processSize (_ ➔ P)       = suc (processSize P)
processSize (P □ Q)       = suc (processSize P + processSize Q)
processSize (P ⊓ Q)       = suc (processSize P + processSize Q)
processSize (P ∥⦅ _ ⦆ Q)  = suc (processSize P + processSize Q)
processSize (P ∖ _)       = suc (processSize P)
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
  _∥ᵗ⦅_⦆_ : Trace α → ℙ A → Trace α → TraceSet α
  [] ∥ᵗ⦅ As ⦆ [] = ⟪ ⟨⟩ ⟫
  [] ∥ᵗ⦅ As ⦆ (q ∷ Qt) with q ∈? toList As
  ... | yes m = ⟪ ⟨⟩ ⟫
  ... | no ¬m = fromList (⟨⟩ ∷ (map (λ t → ⟨ q ⟩ ^ t) (toList ([] ∥ᵗ⦅ As ⦆ Qt))))
  (p ∷ Pt) ∥ᵗ⦅ As ⦆ [] with p ∈? toList As
  ... | yes m = ⟪ ⟨⟩ ⟫
  ... | no ¬m = fromList (⟨⟩ ∷ (map (λ t → ⟨ p ⟩ ^ t) (toList (Pt ∥ᵗ⦅ As ⦆ []))))
  (p ∷ Pt) ∥ᵗ⦅ As ⦆ (q ∷ Qt) with p ≟ q | p ∈? toList As | q ∈? toList As
  ... | yes refl | yes pin | _ = ⟪ ⟨⟩ ⟫ ∪ (mapˢ (λ t → ⟨ p ⟩ ^ t) (Pt ∥ᵗ⦅ As ⦆ Qt))
  ... | yes refl | no ¬pin | _ = ⟪ ⟨⟩ ⟫ ∪ (mapˢ (λ t → ⟨ p ⟩ ^ t) (Pt ∥ᵗ⦅ As ⦆ (q ∷ Qt))) ∪ (mapˢ (λ t → ⟨ q ⟩ ^ t) ((p ∷ Pt) ∥ᵗ⦅ As ⦆ Qt))
  ... | no ¬p=q | pin | qin = ⟪ ⟨⟩ ⟫ ∪ (pfirst pin) ∪ (qfirst qin)
    where
      pfirst : Dec (p ∈ toList As) → TraceSet α
      pfirst (yes pin) = ⟪ ⟨⟩ ⟫
      pfirst (no ¬pin) = ⟪ ⟨⟩ ⟫ ∪ (mapˢ (λ t → ⟨ p ⟩ ^ t) (Pt ∥ᵗ⦅ As ⦆ (q ∷ Qt)))
      qfirst : Dec (q ∈ toList As) → TraceSet α
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
  -- Hiding projects events in As out of each trace (τ-steps aren't
  -- observable, so the trace set is just the visible-event projection).
  traces (P ∖ As) = mapˢ (filter (_∉? toList As)) (traces P)
-- traces (fix Px) = {!!}
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
  initials (P ∥⦅ As ⦆ Q) with initials P | initials Q
  ... | ip | iq = (ip ∩ iq ∩ As) ∪ (ip ＼ As) ∪ (iq ＼ As)
  -- Visible initials of P ∖ As: drop any hidden events (they become τs).
  initials (P ∖ As) = initials P ＼ As
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
    P2 = R ∥⦅ ⟪ c ⟫ ⦆ S

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
  open TraceSemantics {α} using (initials)

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
    ∥₁ : {a : A} {P Q P' Q' : Process α} {As : ℙ A}
      → a ∈ toList As
      → P ─ ` a ⟶ P'
      → Q ─ ` a ⟶ Q'
      → (P ∥⦅ As ⦆ Q) ─ ` a ⟶ (P' ∥⦅ As ⦆ Q')
    ∥₂ : {a : A} {P Q P' : Process α} {As : ℙ A}
      → a ∉ toList As
      → P ─ ` a ⟶ P'
      → (P ∥⦅ As ⦆ Q) ─ ` a ⟶ (P' ∥⦅ As ⦆ Q)
    ∥₃ : {a : A} {P Q Q' : Process α} {As : ℙ A}
      → a ∉ toList As
      → Q ─ ` a ⟶ Q'
      → (P ∥⦅ As ⦆ Q) ─ ` a ⟶ (P ∥⦅ As ⦆ Q')
    ∥₄ : {P Q P' : Process α} {As : ℙ A}
      → P ─ τ ⟶ P'
      → (P ∥⦅ As ⦆ Q) ─ τ ⟶ (P' ∥⦅ As ⦆ Q)
    ∥₅ : {P Q Q' : Process α} {As : ℙ A}
      → Q ─ τ ⟶ Q'
      → (P ∥⦅ As ⦆ Q) ─ τ ⟶ (P ∥⦅ As ⦆ Q')
    -- Hiding: events in As become τ-steps; others pass through.
    ∖₁ : {a : A} {P P' : Process α} {As : ℙ A}
      → a ∈ toList As
      → P ─ ` a ⟶ P'
      → (P ∖ As) ─ τ ⟶ (P' ∖ As)
    ∖₂ : {a : A} {P P' : Process α} {As : ℙ A}
      → a ∉ toList As
      → P ─ ` a ⟶ P'
      → (P ∖ As) ─ ` a ⟶ (P' ∖ As)
    ∖τ : {P P' : Process α} {As : ℙ A}
      → P ─ τ ⟶ P'
      → (P ∖ As) ─ τ ⟶ (P' ∖ As)
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
  reduces? (P ∥⦅ As ⦆ Q) a with a ∈? toList As
  reduces? (P ∥⦅ As ⦆ Q) a | no a∉As with reduces? P a | reduces? Q a
  ... | yes (P' , pr) | _ = yes ((P' ∥⦅ As ⦆ Q) , ∥₂ a∉As pr)
  ... | _ | yes (Q' , qr) = yes ((P ∥⦅ As ⦆ Q') , ∥₃ a∉As qr)
  ... | no ¬pr | no ¬qr = no (λ { (PQ' , ∥₁ x pr pr₁) → a∉As x ; (PQ' , ∥₂ x pr) → ¬pr (_ , pr) ; (PQ' , ∥₃ x pr) → ¬qr (_ , pr) })
  reduces? (P ∥⦅ As ⦆ Q) a | yes a∈As with reduces? P a | reduces? Q a
  ... | yes (P' , pr) | yes (Q' , qr) = yes ((P' ∥⦅ As ⦆ Q') , ∥₁ a∈As pr qr)
  ... | no ¬pr        | _ = no (λ { (PQ' , ∥₁ x pr pr₁) → ¬pr (_ , pr) ; (PQ' , ∥₂ x pr) → x a∈As ; (PQ' , ∥₃ x pr) → x a∈As })
  ... | _                 | no ¬qr = no (λ { (PQ' , ∥₁ x pr pr₁) → ¬qr (_ , pr₁) ; (PQ' , ∥₂ x pr) → x a∈As ; (PQ' , ∥₃ x pr) → x a∈As })
  -- Hiding: visible step on `a` requires a ∉ As AND P steps on a.
  reduces? (P ∖ As) a with a ∈? toList As
  ... | yes a∈As = no (λ { (P' , ∖₂ a∉As _) → a∉As a∈As })
  ... | no a∉As with reduces? P a
  ...   | yes (P' , pr) = yes ((P' ∖ As) , ∖₂ a∉As pr)
  ...   | no ¬pr        = no (λ { (P' , ∖₂ _ pr) → ¬pr (_ , pr) })

  open import Data.Bool using (if_then_else_; _∧_)
  open import Relation.Nullary using (does)

  -- One-step τ-successors. Mirrors the τ rules of _─_⟶_. Used alongside
  -- observable followups to reason about weak-step properties: a process is
  -- stable iff τ-followups is empty. Mutually recursive with `followups`
  -- because hiding turns observable steps on hidden events into τs.
  τ-followups : Process α → List (Process α)
  followups   : Process α → List (A × Process α)

  τ-followups STOP = []
  τ-followups SKIP = []
  τ-followups (_ ➔ _) = []
  τ-followups (P □ Q) = map (_□ Q) (τ-followups P) ++ map (P □_) (τ-followups Q)
  τ-followups (P ⊓ Q) = P ∷ Q ∷ []
  τ-followups (P ∥⦅ As ⦆ Q) =
    map (_∥⦅ As ⦆ Q) (τ-followups P) ++ map (P ∥⦅ As ⦆_) (τ-followups Q)
  -- Hiding: τ-successors come from inner τ-steps AND from obs-steps on
  -- hidden events (∖₁ turns a visible `a ∈ As` into a τ).
  τ-followups (P ∖ As) =
      map (_∖ As) (τ-followups P)
    ++
      concatMap (λ (a , P') → if does (a ∈? toList As) then (P' ∖ As) ∷ [] else [])
                (followups P)

  -- Observable one-step successors, tagged with the event that drove the step.
  -- Mirrors the ` a ⟶ rules of _─_⟶_ (τ-steps are NOT included — τ-progress
  -- is handled by a separate relation if/when needed).
  followups STOP = []
  followups SKIP = (✓ , STOP) ∷ []
  followups (x ➔ P) = (x , P) ∷ []
  followups (P □ Q) = followups P ++ followups Q
  followups (P ⊓ Q) = []  -- ⊓ has only τ-steps; no observable successors
  followups (P ∥⦅ As ⦆ Q) =
      -- P steps alone: event must NOT be in As
      concatMap (λ (a , P') → if does (a ∈? toList As) then [] else (a , P' ∥⦅ As ⦆ Q) ∷ [])
                (followups P)
    ++
      -- Q steps alone: event must NOT be in As
      concatMap (λ (a , Q') → if does (a ∈? toList As) then [] else (a , P ∥⦅ As ⦆ Q') ∷ [])
                (followups Q)
    ++
      -- Synchronised step: event must be in As AND match on both sides
      concatMap (λ (a , P') →
        concatMap (λ (b , Q') →
          if does (a ∈? toList As) ∧ does (a ≟ b) then (a , P' ∥⦅ As ⦆ Q') ∷ [] else [])
          (followups Q))
        (followups P)
  -- Hiding: observable steps only on events NOT in As (∖₂ rule).
  followups (P ∖ As) =
      concatMap (λ (a , P') → if does (a ∈? toList As) then [] else (a , P' ∖ As) ∷ [])
                (followups P)
```

### Shrinkage of followups / τ-followups

Both `followups P` and `τ-followups P` produce processes that are
semantically (not syntactically) smaller than `P` — under `∥` and `∖`
the result shares the wrapper (e.g. `P' ∥⦅ As ⦆ Q`) which is structurally
larger than `P`, but the size measure `processSize` strictly decreases.
These lemmas justify wf-recursion on `processSize` for decision procedures
that walk successors (e.g. the `F` case of LTL satisfiability).

```
  open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ˡ_; find to find∈)
  open import Data.List.Relation.Unary.Any using (Any; here; there)
  open import Data.List.Membership.Propositional.Properties
    using (∈-map⁻; ∈-++⁻; ∈-concatMap⁻)
  open import Data.List.Relation.Unary.Any.Properties using (concat⁻)
  open import Data.Nat using (s≤s; z≤n; _<_)
  open import Data.Nat.Properties
    using (≤-refl; ≤-trans; <-trans; ≤-<-trans; <-≤-trans
         ; m≤m+n; m≤n+m; +-monoˡ-<; +-monoʳ-<; n<1+n)
  open import Data.Sum using (inj₁; inj₂)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  -- Local membership alias that matches the list-of-pairs types used above.
  -- (`_∈_` here is propositional list membership imported right above.)

  -- `followups` and `τ-followups` are mutually recursive via the ∖ case,
  -- so these shrinkage lemmas must be proved mutually.
  followup-< :
    ∀ {P : Process α} {a : A} {P' : Process α}
    → (a , P') ∈ˡ followups P
    → processSize P' Data.Nat.< processSize P
  τ-followup-< :
    ∀ {P : Process α} {P' : Process α}
    → P' ∈ˡ τ-followups P
    → processSize P' Data.Nat.< processSize P
```

Proofs — by induction on `P`. The `if does _ then [] else (_ ∷ [])`
branches are handled by case-splitting on the decision.

```
  -- Helper: membership in `if does c then [] else [y]` forces y ≡ x (and c = no).
  if-cons-∈ : ∀ {B : Type} {P : Type} {x y : B} {c : Dec P}
    → x ∈ˡ (if does c then [] else (y ∷ []))
    → x ≡ y
  if-cons-∈ {c = yes _} ()
  if-cons-∈ {c = no _}  (here refl) = refl
  if-cons-∈ {c = no _}  (there ())

  -- Helper: membership in `if does c then [y] else []` forces y ≡ x (and c = yes).
  if-cons-∈′ : ∀ {B : Type} {P : Type} {x y : B} {c : Dec P}
    → x ∈ˡ (if does c then (y ∷ []) else [])
    → x ≡ y
  if-cons-∈′ {c = no _}  ()
  if-cons-∈′ {c = yes _} (here refl) = refl
  if-cons-∈′ {c = yes _} (there ())

  followup-< {STOP} ()
  followup-< {SKIP} (here refl) = s≤s Data.Nat.z≤n
  followup-< {SKIP} (there ())
  followup-< {a ➔ P} (here refl) = ≤-refl
  followup-< {a ➔ P} (there ())
  followup-< {P □ Q} p∈ with ∈-++⁻ (followups P) p∈
  ... | inj₁ inP = <-≤-trans (followup-< inP)
                             (≤-trans (m≤m+n (processSize P) (processSize Q))
                                      (n≤1+n (processSize P + processSize Q)))
      where open import Data.Nat.Properties using (n≤1+n)
  ... | inj₂ inQ = <-≤-trans (followup-< inQ)
                             (≤-trans (m≤n+m (processSize Q) (processSize P))
                                      (n≤1+n (processSize P + processSize Q)))
      where open import Data.Nat.Properties using (n≤1+n)
  followup-< {P ⊓ Q} ()
  followup-< {P ∥⦅ As ⦆ Q} {a} {P'} p∈
    with ∈-++⁻ (concatMap (λ (x , P'') → if does (x ∈? toList As) then [] else (x , P'' ∥⦅ As ⦆ Q) ∷ []) (followups P)) p∈
  ... | inj₁ inL₁ =
        ∥-walkL (followups P) (∈-concatMap⁻ _ inL₁) (λ {_} z → z)
    where
      ∥-walkL : ∀ (xs : List (A × Process α)) →
          Any (λ (b , P'') → (a , P') ∈ˡ (if does (b ∈? toList As) then [] else (b , P'' ∥⦅ As ⦆ Q) ∷ [])) xs
        → (∀ {bP''} → bP'' ∈ˡ xs → bP'' ∈ˡ followups P)
        → processSize P' < processSize (P ∥⦅ As ⦆ Q)
      ∥-walkL ((b , P'') ∷ xs) (here inIf) emb with if-cons-∈ {c = b ∈? toList As} inIf
      ... | refl = s≤s (+-monoˡ-< (processSize Q) (followup-< {P} (emb (here refl))))
      ∥-walkL (_ ∷ xs) (there rest) emb = ∥-walkL xs rest (λ m → emb (there m))
  followup-< {P ∥⦅ As ⦆ Q} {a} {P'} p∈ | inj₂ rest
    with ∈-++⁻ (concatMap (λ (x , Q'') → if does (x ∈? toList As) then [] else (x , P ∥⦅ As ⦆ Q'') ∷ []) (followups Q)) rest
  ... | inj₁ inL₂ =
        ∥-walkR (followups Q) (∈-concatMap⁻ _ inL₂) (λ {_} z → z)
    where
      ∥-walkR : ∀ (ys : List (A × Process α)) →
          Any (λ (b , Q'') → (a , P') ∈ˡ (if does (b ∈? toList As) then [] else (b , P ∥⦅ As ⦆ Q'') ∷ [])) ys
        → (∀ {bQ''} → bQ'' ∈ˡ ys → bQ'' ∈ˡ followups Q)
        → processSize P' < processSize (P ∥⦅ As ⦆ Q)
      ∥-walkR ((b , Q'') ∷ ys) (here inIf) emb with if-cons-∈ {c = b ∈? toList As} inIf
      ... | refl = s≤s (+-monoʳ-< (processSize P) (followup-< {Q} (emb (here refl))))
      ∥-walkR (_ ∷ ys) (there rest) emb = ∥-walkR ys rest (λ m → emb (there m))
  followup-< {P ∥⦅ As ⦆ Q} {a} {P'} p∈ | inj₂ _ | inj₂ inL₃ =
        ∥-walkS (followups P) (∈-concatMap⁻ _ inL₃) (λ {_} z → z)
    where
      -- Helper for `if (x ∧ y) then [z] else []` with both x and y booleans.
      if-and-cons-∈ : ∀ {B : Type} {x y : B} {c d : Data.Bool.Bool}
        → x ∈ˡ (if c ∧ d then (y ∷ []) else [])
        → x ≡ y
      if-and-cons-∈ {c = Data.Bool.false} ()
      if-and-cons-∈ {c = Data.Bool.true} {d = Data.Bool.false} ()
      if-and-cons-∈ {c = Data.Bool.true} {d = Data.Bool.true} (here refl) = refl
      if-and-cons-∈ {c = Data.Bool.true} {d = Data.Bool.true} (there ())

      ∥-walkS-inner : ∀ {b : A} {P'' : Process α} (ys : List (A × Process α)) →
          Any (λ (c , Q'') → (a , P') ∈ˡ (if does (b ∈? toList As) ∧ does (b ≟ c) then (b , P'' ∥⦅ As ⦆ Q'') ∷ [] else [])) ys
        → (∀ {cQ''} → cQ'' ∈ˡ ys → cQ'' ∈ˡ followups Q)
        → (b , P'') ∈ˡ followups P
        → processSize P' < processSize (P ∥⦅ As ⦆ Q)
      ∥-walkS-inner {b} ((c , Q'') ∷ ys) (here inIf) emb bP''∈
        with if-and-cons-∈ {c = does (b ∈? toList As)} {d = does (b ≟ c)} inIf
      ... | refl = s≤s (+-mono-< (followup-< {P} bP''∈) (followup-< {Q} (emb (here refl))))
        where open import Data.Nat.Properties using (+-mono-<)
      ∥-walkS-inner (_ ∷ ys) (there rest) emb bP''∈ = ∥-walkS-inner ys rest (λ m → emb (there m)) bP''∈

      ∥-walkS : ∀ (xs : List (A × Process α)) →
          Any (λ (b , P'') →
            (a , P') ∈ˡ concatMap (λ (c , Q'') →
              if does (b ∈? toList As) ∧ does (b ≟ c) then (b , P'' ∥⦅ As ⦆ Q'') ∷ [] else [])
              (followups Q)) xs
        → (∀ {bP''} → bP'' ∈ˡ xs → bP'' ∈ˡ followups P)
        → processSize P' < processSize (P ∥⦅ As ⦆ Q)
      ∥-walkS ((b , P'') ∷ xs) (here innerIn) emb =
        ∥-walkS-inner (followups Q) (∈-concatMap⁻ _ innerIn) (λ {_} z → z) (emb (here refl))
      ∥-walkS (_ ∷ xs) (there rest) emb = ∥-walkS xs rest (λ m → emb (there m))
  followup-< {P ∖ As} {a} {P'} p∈ =
        ∖-walk (followups P) (∈-concatMap⁻ _ p∈) (λ {_} z → z)
    where
      ∖-walk : ∀ (xs : List (A × Process α)) →
          Any (λ (b , P'') → (a , P') ∈ˡ (if does (b ∈? toList As) then [] else (b , P'' ∖ As) ∷ [])) xs
        → (∀ {bP''} → bP'' ∈ˡ xs → bP'' ∈ˡ followups P)
        → processSize P' < processSize (P ∖ As)
      ∖-walk ((b , P'') ∷ xs) (here inIf) emb with if-cons-∈ {c = b ∈? toList As} inIf
      ... | refl = s≤s (followup-< {P} (emb (here refl)))
      ∖-walk (_ ∷ xs) (there rest) emb = ∖-walk xs rest (λ m → emb (there m))

  τ-followup-< {STOP} ()
  τ-followup-< {SKIP} ()
  τ-followup-< {a ➔ P} ()
  τ-followup-< {P □ Q} p∈ with ∈-++⁻ (map (_□ Q) (τ-followups P)) p∈
  ... | inj₁ inP with ∈-map⁻ (_□ Q) inP
  ...   | (P'' , P''∈ , refl) = s≤s (+-monoˡ-< (processSize Q) (τ-followup-< {P} P''∈))
  τ-followup-< {P □ Q} p∈ | inj₂ inQ with ∈-map⁻ (P □_) inQ
  ...   | (Q'' , Q''∈ , refl) = s≤s (+-monoʳ-< (processSize P) (τ-followup-< {Q} Q''∈))
  τ-followup-< {P ⊓ Q} (here refl) = s≤s (m≤m+n _ _)
  τ-followup-< {P ⊓ Q} (there (here refl)) = s≤s (m≤n+m _ _)
  τ-followup-< {P ⊓ Q} (there (there ()))
  τ-followup-< {P ∥⦅ As ⦆ Q} p∈ with ∈-++⁻ (map (_∥⦅ As ⦆ Q) (τ-followups P)) p∈
  ... | inj₁ inP with ∈-map⁻ (_∥⦅ As ⦆ Q) inP
  ...   | (P'' , P''∈ , refl) = s≤s (+-monoˡ-< (processSize Q) (τ-followup-< {P} P''∈))
  τ-followup-< {P ∥⦅ As ⦆ Q} p∈ | inj₂ inQ with ∈-map⁻ (P ∥⦅ As ⦆_) inQ
  ...   | (Q'' , Q''∈ , refl) = s≤s (+-monoʳ-< (processSize P) (τ-followup-< {Q} Q''∈))
  τ-followup-< {P ∖ As} p∈ with ∈-++⁻ (map (_∖ As) (τ-followups P)) p∈
  ... | inj₁ inτ with ∈-map⁻ (_∖ As) inτ
  ...   | (P'' , P''∈ , refl) = s≤s (τ-followup-< {P} P''∈)
  τ-followup-< {P ∖ As} {P'} p∈ | inj₂ inObs = τ∖-walk (followups P) (∈-concatMap⁻ _ inObs) (λ {_} z → z)
    where
      τ∖-walk : ∀ (xs : List (A × Process α)) →
          Any (λ (b , P'') → P' ∈ˡ (if does (b ∈? toList As) then (P'' ∖ As) ∷ [] else [])) xs
        → (∀ {bP'} → bP' ∈ˡ xs → bP' ∈ˡ followups P)
        → processSize P' < processSize (P ∖ As)
      τ∖-walk ((b , P'') ∷ xs) (here inIf) emb rewrite if-cons-∈′ {c = b ∈? toList As} inIf =
          s≤s (followup-< {P} (emb (here refl)))
      τ∖-walk (_ ∷ xs) (there rest) emb = τ∖-walk xs rest (λ mem → emb (there mem))
```

### Weak initials

Milner-style **weak** initials: the union of structural initials across all
τ-reachable processes. `initials*` captures "events the process might
offer after zero-or-more silent steps", which is the right notion for
τ-closed observational reasoning (e.g. LTL atomic satisfaction).

Terminates for non-recursive fragments because `τ-followups` strictly
shrinks process size (⊓ drops the ⊓; ∖ drops prefixes or descends into
structural τ-steps).  Recursive processes will diverge — handled when
we add proper fixpoint support.

```
  -- Helper `initials*∖ P As` computes the weak initials of `P ∖ As`
  -- and recurses structurally on `P`, so Agda's termination checker
  -- accepts the hidden-➔ descent into the inner process.
  initials*∖ : Process α → ℙ A → ℙ A

  initials* : Process α → ℙ A
  initials* STOP           = ∅
  initials* SKIP           = ⟪ ✓ ⟫
  initials* (x ➔ P)        = ⟪ x ⟫
  initials* (P □ Q)        = initials* P ∪ initials* Q
  initials* (P ⊓ Q)        = initials* P ∪ initials* Q
  initials* (P ∥⦅ As ⦆ Q)  = (initials* P ∩ initials* Q ∩ As)
                             ∪ (initials* P ＼ As)
                             ∪ (initials* Q ＼ As)
  initials* (P ∖ As)        = initials*∖ P As

  initials*∖ STOP          As = ∅
  initials*∖ SKIP          As = ⟪ ✓ ⟫ ＼ As
  initials*∖ (x ➔ P)       As with x ∈? toList As
  ... | yes _                 = initials*∖ P As
  ... | no  _                 = ⟪ x ⟫ ＼ As
  initials*∖ (P □ Q)       As = initials*∖ P As ∪ initials*∖ Q As
  initials*∖ (P ⊓ Q)       As = initials*∖ P As ∪ initials*∖ Q As
  initials*∖ (P ∥⦅ Bs ⦆ Q) As = (initials*∖ P As ∩ initials*∖ Q As ∩ Bs)
                                ∪ (initials*∖ P As ＼ Bs)
                                ∪ (initials*∖ Q As ＼ Bs)
  initials*∖ (P ∖ Bs)      As = initials*∖ P Bs ＼ As
```

### Stability

A process is *stable* when it has no pending τ-steps: its `τ-followups` is
empty, or equivalently every τ-rule of `_─_⟶_` is inapplicable. Stability
is the CSP equivalent of a normal form / value — observable steps are still
possible, but no silent reduction can fire first.

`⊓` is always unstable (⊓₁/⊓₂ give it two τ-successors). Hiding is the
other source of instability: `P ∖ As` τ-reduces via `∖₁` whenever `P` can
take an observable step on any event in `As`, so `P ∖ As` is stable only if
`P` is stable AND `P` has no observable step into `As`.

```
  data NoStepIn : Process α → ℙ A → Type where
    no-step : ∀ {P As}
      → (∀ (a : A) (P' : Process α) → a ∈ toList As → ¬ (P ─ ` a ⟶ P'))
      → NoStepIn P As

  data Stable : Process α → Type where
    STOP : Stable STOP
    SKIP : Stable SKIP
    pref : ∀ {a : A} {P : Process α} → Stable (a ➔ P)
    _□_  : ∀ {P Q} → Stable P → Stable Q → Stable (P □ Q)
    _∥_  : ∀ {P Q As} → Stable P → Stable Q → Stable (P ∥⦅ As ⦆ Q)
    _∖_  : ∀ {P As} → Stable P → NoStepIn P As → Stable (P ∖ As)
    -- Notably, no case for P ⊓ Q.
```

**TDD case:** the canonical unstable hiding example — forced sync on a
hidden event.

```
  module Stable-TDD where
    open import Relation.Nullary using (¬_)
    open import Data.List.Relation.Unary.Any using (here; there)
    open import abstract-set-theory.FiniteSetTheory using (setToList)

    -- ((a ➔ P) ∥⦅⟪a⟫⦆ (a ➔ Q)) ∖ ⟪a⟫ is UNSTABLE: the sync fires as a τ.
    opaque
      unfolding setToList

      ∥-hide-unstable : ∀ {a : A} {P Q : Process α}
        → ¬ (Stable (((a ➔ P) ∥⦅ ⟪ a ⟫ ⦆ (a ➔ Q)) ∖ ⟪ a ⟫))
      ∥-hide-unstable {a} {P} {Q} ((pref ∥ pref) ∖ no-step ¬stepIn) =
        ¬stepIn a (P ∥⦅ ⟪ a ⟫ ⦆ Q) (here refl) (∥₁ (here refl) prefix prefix)
```

The proof destructures: the top-level `_∖_` case of `Stable` gives us
`NoStepIn ((a ➔ P) ∥⦅⟪a⟫⦆ (a ➔ Q)) ⟪a⟫`. We then feed it the
observable step `a ∈ toList ⟪a⟫` paired with the sync entry in
`followups` — which is the (a , P ∥⦅⟪a⟫⦆ Q) head, since the sync branch
fires first in the concatMap.

The decision procedure: straightforward structural recursion. `NoStepIn`
is itself decidable via `followups`.

```
  -- Uniform decision via the pointwise reduction oracle `reduces?`.
  -- `NoStepIn P As` is "every a ∈ toList As is unreachable as an
  -- observable step from P", which is exactly `All (λ a → ¬ reduces? P a)`
  -- over `toList As`.
  noStepIn? : (P : Process α) (As : ℙ A) → Dec (NoStepIn P As)
  noStepIn? P As =
    Dec.map′ wrap unwrap (all? noReduce? (toList As))
    where
      open import Data.List.Relation.Unary.All using (All; []; _∷_; all?; lookup)
      open import Data.List.Relation.Unary.Any using (here; there)
      open import Relation.Nullary as Dec using (Dec; yes; no)

      NoR : A → Type
      NoR a = ¬ (∃ λ P' → P ─ ` a ⟶ P')

      noReduce? : (a : A) → Dec (NoR a)
      noReduce? a with reduces? P a
      ... | yes r = no λ ¬r → ¬r r
      ... | no ¬r = yes ¬r

      wrap : All NoR (toList As) → NoStepIn P As
      wrap all¬ = no-step λ a P' a∈ p → lookup all¬ a∈ (P' , p)

      unwrap : NoStepIn P As → All NoR (toList As)
      unwrap (no-step f) = all-from-f (toList As) (λ a a∈ P' → f a P' a∈)
        where
          all-from-f : (xs : List A)
            → (∀ a → a ∈ˡ xs → ∀ P' → ¬ (P ─ ` a ⟶ P'))
            → All NoR xs
          all-from-f []       _ = []
          all-from-f (x ∷ xs) g =
            (λ { (P' , p) → g x (here refl) P' p })
              ∷ all-from-f xs (λ a a∈ P' → g a (there a∈) P')

  stable? : (P : Process α) → Dec (Stable P)
  stable? STOP = yes STOP
  stable? SKIP = yes SKIP
  stable? (a ➔ P) = yes pref
  stable? (P □ Q) with stable? P | stable? Q
  ... | yes sP | yes sQ = yes (sP □ sQ)
  ... | no ¬sP | _      = no λ { (sP □ _) → ¬sP sP }
  ... | _      | no ¬sQ = no λ { (_ □ sQ) → ¬sQ sQ }
  stable? (P ⊓ Q) = no (λ ())
  stable? (P ∥⦅ As ⦆ Q) with stable? P | stable? Q
  ... | yes sP | yes sQ = yes (sP ∥ sQ)
  ... | no ¬sP | _      = no λ { (sP ∥ _) → ¬sP sP }
  ... | _      | no ¬sQ = no λ { (_ ∥ sQ) → ¬sQ sQ }
  stable? (P ∖ As) with stable? P | noStepIn? P As
  ... | yes sP | yes ns  = yes (sP ∖ ns)
  ... | no ¬sP | _       = no λ { (sP ∖ _)  → ¬sP sP }
  ... | _      | no ¬ns  = no λ { (_  ∖ ns) → ¬ns ns }
  -- Decidability bottoms out on `noStepIn?`.
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
  open Reduction α using (Stable; NoStepIn; STOP; SKIP; pref; _□_; _∥_; _∖_; no-step; noStepIn?; stable?)
  open import Data.List.Membership.DecPropositional (DecEq._≟_ DecEq-A) using (_∈_; _∈?_; _∉?_)
  open import Data.List.Relation.Unary.Any using (here; there)
  open import Data.Sum using (inj₁; inj₂)
  open import Function.Bundles using (Equivalence)

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
    -- No ⊓ constructors: `_⊢ᶠ_` is *stable* failures. `P ⊓ Q` always has
    -- a pending τ to either branch, so no stable refusal exists at ⟨⟩ on
    -- the composite itself. LTL rules that care about "might-refuse"
    -- (demonic liveness) should use `rejects?` / τ-followups, not `_⊢ᶠ_`.
    -- Parallel composition at ⟨⟩ combines refusals per Roscoe UCS §2.4:
    --   sync events (∈ As) are refused if *either* side refuses;
    --   async events (∉ As) are refused only if *both* sides refuse.
    -- Encoded as `(X ∩ Y) ∪ ((X ∪ Y) ∩ fromList As)`.
    ∥⟨⟩ : {P Q : Process α} {X Y : ℙ A} {As : ℙ A}
      → P ⊢ᶠ (⟨⟩ , X)
      → Q ⊢ᶠ (⟨⟩ , Y)
      → P ∥⦅ As ⦆ Q ⊢ᶠ (⟨⟩ , (X ∩ Y) ∪ ((X ∪ Y) ∩ As))
    -- Synchronised step: both sides fire `a` together, `a ∈ As`, and the
    -- composite inherits the post-step failure.
    ∥-sync : {a : A} {P Q : Process α} {s : Trace α} {X : ℙ A} {As : ℙ A}
      → a ∈ toList As
      → P ∥⦅ As ⦆ Q ⊢ᶠ (s , X)
      → (a ➔ P) ∥⦅ As ⦆ (a ➔ Q) ⊢ᶠ (⟨ a ⟩ ^ s , X)
    -- Async step on the left: P fires `a` with `a ∉ As`, Q unchanged.
    ∥-async₁ : {a : A} {P Q : Process α} {s : Trace α} {X : ℙ A} {As : ℙ A}
      → ¬ (a ∈ toList As)
      → P ∥⦅ As ⦆ Q ⊢ᶠ (s , X)
      → (a ➔ P) ∥⦅ As ⦆ Q ⊢ᶠ (⟨ a ⟩ ^ s , X)
    -- Async step on the right: symmetric.
    ∥-async₂ : {a : A} {P Q : Process α} {s : Trace α} {X : ℙ A} {As : ℙ A}
      → ¬ (a ∈ toList As)
      → P ∥⦅ As ⦆ Q ⊢ᶠ (s , X)
      → P ∥⦅ As ⦆ (a ➔ Q) ⊢ᶠ (⟨ a ⟩ ^ s , X)
    -- Hiding at ⟨⟩: if P stably refuses X *and* can't observable-step into
    -- As (so ∖₁ is inapplicable and the hiding bubble doesn't τ-evolve),
    -- then P ∖ As stably refuses X ∪ As. Events in As are refused because
    -- they'd be τ under hiding (∖₁); events in X are refused inherited from P.
    ∖ᶠ : {P : Process α} {X As : ℙ A}
      → P ⊢ᶠ (⟨⟩ , X)
      → NoStepIn P As
      → (P ∖ As) ⊢ᶠ (⟨⟩ , X ∪ As)
```

### rejects?

Dual to `reduces?`: "does `P` stably refuse `a` right now?". Both return `no` for
unstable processes (pending τ) — τ-progress lives outside this relation. Now a thin
wrapper over the generalised `refuses? P Z` (defined below).

```
  open import abstract-set-theory.FiniteSetTheory using (List-Model; setToList)
  open import Axiom.Set.Properties List-Model using (∈-filter⁺'; ∈-filter⁻'; ∈-∪⁺; ∈-∪⁻)
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

    -- Generalised refutation: a ➔-process's head event `y` can never
    -- appear in any refusal set derivable at ⟨⟩ (whether the refusal is
    -- ⟪y⟫ directly or some larger set reached via ⊆ᶠ).
    ¬➔-refuses-head : ∀ {y : A} {Q : Process α} {Z : ℙ A}
      → (y ➔ Q) ⊢ᶠ (⟨⟩ , Z) → ¬ (y ∈ toList Z)
    ¬➔-refuses-head ➔⟨⟩ y∈X = ＼-∉ y∈X (here refl)
    ¬➔-refuses-head (⊆ᶠ sub p) y∈Y = ¬➔-refuses-head p (sub _ y∈Y)

    -- A ➔-process never stably refuses its own head event. Exposed so LTL
    -- (and any other consumer) can discharge the `Null.¬ (a ➔ P ⊢ᶠ (⟨⟩ , ⟪a⟫))`
    -- side-condition without reaching inside `rejects?`.
    ¬➔-refuses-self : ∀ {a : A} {P : Process α} → ¬ ((a ➔ P) ⊢ᶠ (⟨⟩ , ⟪ a ⟫))
    ¬➔-refuses-self p = ¬➔-refuses-head p (here refl)

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

  -- Canonical refusal witness for a stable process. Every stable P has
  -- SOME stable refusal at ⟨⟩; this bridge produces one so decision
  -- procedures on composites (∥, later ∖) can feed both sides' witnesses
  -- into ∥⟨⟩-style constructors.
  Stable→⊢ᶠ : ∀ (P : Process α) → Stable P → ∃ λ X → P ⊢ᶠ (⟨⟩ , X)
  Stable→⊢ᶠ STOP           STOP           = all , STOPᶠ
  Stable→⊢ᶠ SKIP           SKIP           = all ＼ ⟪ ✓ ⟫ , SKIP⟨⟩
  Stable→⊢ᶠ (a ➔ P)        pref           = all ＼ ⟪ a ⟫ , ➔⟨⟩
  Stable→⊢ᶠ (P □ Q)        (sP □ sQ)      =
    let X , pP = Stable→⊢ᶠ P sP
        Y , pQ = Stable→⊢ᶠ Q sQ
    in  (X ∩ Y) , □⟨⟩ pP pQ
  Stable→⊢ᶠ (P ∥⦅ As ⦆ Q)  (sP ∥ sQ)      =
    let X , pP = Stable→⊢ᶠ P sP
        Y , pQ = Stable→⊢ᶠ Q sQ
    in  (X ∩ Y) ∪ ((X ∪ Y) ∩ As) , ∥⟨⟩ pP pQ
  Stable→⊢ᶠ (P ∖ As)       (sP ∖ ns)      =
    let X , pP = Stable→⊢ᶠ P sP
    in  X ∪ As , ∖ᶠ pP ns

  -- Completeness: every ⟨⟩-failure witnesses structural stability. Since
  -- `_⊢ᶠ_` has no ⊓ constructor, the only way to derive a ⟨⟩-refusal is
  -- through structurally stable pieces.
  ⟨⟩⊢ᶠ→Stable : ∀ {P : Process α} {X : ℙ A} → P ⊢ᶠ (⟨⟩ , X) → Stable P
  ⟨⟩⊢ᶠ→Stable STOPᶠ          = STOP
  ⟨⟩⊢ᶠ→Stable SKIP⟨⟩         = SKIP
  ⟨⟩⊢ᶠ→Stable ➔⟨⟩            = pref
  ⟨⟩⊢ᶠ→Stable (□⟨⟩ p q)      = ⟨⟩⊢ᶠ→Stable p □ ⟨⟩⊢ᶠ→Stable q
  ⟨⟩⊢ᶠ→Stable (□₁ s≢⟨⟩ _)    with s≢⟨⟩ refl
  ...                                    | ()
  ⟨⟩⊢ᶠ→Stable (□₂ s≢⟨⟩ _)    with s≢⟨⟩ refl
  ...                                    | ()
  ⟨⟩⊢ᶠ→Stable (∥⟨⟩ p q)      = ⟨⟩⊢ᶠ→Stable p ∥ ⟨⟩⊢ᶠ→Stable q
  ⟨⟩⊢ᶠ→Stable (∖ᶠ p ns)      = ⟨⟩⊢ᶠ→Stable p ∖ ns
  ⟨⟩⊢ᶠ→Stable (⊆ᶠ _ p)       = ⟨⟩⊢ᶠ→Stable p

  -- Corollary: if P is not `Stable`, no `P ⊢ᶠ (⟨⟩, X)` derivation exists
  -- for any X. This collapses the remaining ∥/∖ decision residuals.
  ¬Stable→¬⊢ᶠ : ∀ {P : Process α} → ¬ Stable P → ∀ {X} → ¬ (P ⊢ᶠ (⟨⟩ , X))
  ¬Stable→¬⊢ᶠ ¬sP p = ¬sP (⟨⟩⊢ᶠ→Stable p)

  -- Maximality: every ⟨⟩-refusal is contained in the canonical refusal
  -- given by `Stable→⊢ᶠ`. This absorbs all partition cleverness for ∥:
  -- any derivable refusal for `P ∥⦅As⦆ Q` is ⊆ the canonical one, so
  -- deciding refusal reduces to a single subset check.
  opaque
    unfolding setToList

    ∩-mono : ∀ {X X' Y Y' : ℙ A}
      → (∀ a → a ∈ toList X → a ∈ toList X')
      → (∀ a → a ∈ toList Y → a ∈ toList Y')
      → ∀ a → a ∈ toList (X ∩ Y) → a ∈ toList (X' ∩ Y')
    ∩-mono {X} {X'} {Y} {Y'} subX subY a a∈ =
      let (a∈X , a∈Y) = ∈-∩ {X = X} {Y = Y} .Equivalence.from a∈
      in ∈-∩ {X = X'} {Y = Y'} .Equivalence.to (subX a a∈X , subY a a∈Y)
      where open import Function.Bundles using (Equivalence)

    ∪-mono : ∀ {X X' Y Y' : ℙ A}
      → (∀ a → a ∈ toList X → a ∈ toList X')
      → (∀ a → a ∈ toList Y → a ∈ toList Y')
      → ∀ a → a ∈ toList (X ∪ Y) → a ∈ toList (X' ∪ Y')
    ∪-mono {X} {X'} {Y} {Y'} subX subY a a∈ with ∈-∪⁻ {X = X} {Y = Y} a∈
    ... | inj₁ a∈X = ∈-∪⁺ {X = X'} {Y = Y'} (inj₁ (subX a a∈X))
    ... | inj₂ a∈Y = ∈-∪⁺ {X = X'} {Y = Y'} (inj₂ (subY a a∈Y))

    ∥-mono : ∀ {X X' Y Y' As : ℙ A}
      → (∀ a → a ∈ toList X → a ∈ toList X')
      → (∀ a → a ∈ toList Y → a ∈ toList Y')
      → ∀ a
      → a ∈ toList ((X  ∩ Y ) ∪ ((X  ∪ Y ) ∩ As))
      → a ∈ toList ((X' ∩ Y') ∪ ((X' ∪ Y') ∩ As))
    ∥-mono {X} {X'} {Y} {Y'} {As} subX subY =
      ∪-mono {X = X ∩ Y} {X' = X' ∩ Y'}
             {Y = (X ∪ Y) ∩ As} {Y' = (X' ∪ Y') ∩ As}
             (∩-mono {X = X} {X' = X'} {Y = Y} {Y' = Y'} subX subY)
             (∩-mono {X = X ∪ Y} {X' = X' ∪ Y'} {Y = As} {Y' = As}
                     (∪-mono {X = X} {X' = X'} {Y = Y} {Y' = Y'} subX subY)
                     (λ _ a∈ → a∈))

    ∪-mono-left : ∀ {X X' As : ℙ A}
      → (∀ a → a ∈ toList X → a ∈ toList X')
      → ∀ a → a ∈ toList (X ∪ As) → a ∈ toList (X' ∪ As)
    ∪-mono-left {X} {X'} {As} sub =
      ∪-mono {X = X} {X' = X'} {Y = As} {Y' = As} sub (λ _ a∈ → a∈)

  ⟨⟩⊢ᶠ-maximal : ∀ {P : Process α} (sP : Stable P) {X : ℙ A}
    → P ⊢ᶠ (⟨⟩ , X)
    → ∀ a → a ∈ toList X → a ∈ toList (proj₁ (Stable→⊢ᶠ P sP))
  ⟨⟩⊢ᶠ-maximal STOP       STOPᶠ                    a a∈ = a∈
  ⟨⟩⊢ᶠ-maximal SKIP       SKIP⟨⟩                   a a∈ = a∈
  ⟨⟩⊢ᶠ-maximal pref       ➔⟨⟩                      a a∈ = a∈
  ⟨⟩⊢ᶠ-maximal (sP □ sQ)  (□⟨⟩ p q)                a a∈ =
    ∩-mono {X = _} {X' = proj₁ (Stable→⊢ᶠ _ sP)}
           {Y = _} {Y' = proj₁ (Stable→⊢ᶠ _ sQ)}
           (⟨⟩⊢ᶠ-maximal sP p) (⟨⟩⊢ᶠ-maximal sQ q) a a∈
  ⟨⟩⊢ᶠ-maximal _          (□₁ s≢⟨⟩ _)              a a∈ with s≢⟨⟩ refl
  ...                                                   | ()
  ⟨⟩⊢ᶠ-maximal _          (□₂ s≢⟨⟩ _)              a a∈ with s≢⟨⟩ refl
  ...                                                   | ()
  ⟨⟩⊢ᶠ-maximal (sP ∥ sQ)  (∥⟨⟩ p q)                a a∈ =
    ∥-mono {X = _} {X' = proj₁ (Stable→⊢ᶠ _ sP)}
           {Y = _} {Y' = proj₁ (Stable→⊢ᶠ _ sQ)}
           (⟨⟩⊢ᶠ-maximal sP p) (⟨⟩⊢ᶠ-maximal sQ q) a a∈
  ⟨⟩⊢ᶠ-maximal (sP ∖ _)   (∖ᶠ {X = X} p _)         a a∈ =
    ∪-mono-left {X = X} {X' = proj₁ (Stable→⊢ᶠ _ sP)}
                (⟨⟩⊢ᶠ-maximal sP p) a a∈
  ⟨⟩⊢ᶠ-maximal sP         (⊆ᶠ sub p)               a a∈ =
    ⟨⟩⊢ᶠ-maximal sP p a (sub a a∈)

  -- `rejects?` and `deadlocked?` are specialisations of `refuses? P Z`
  -- (defined below) and live at the end of the `refuses?` block.
```

### refuses? (generalised stable refusal decision)

Generalises `rejects?` (refuse `⟪a⟫`) and `deadlocked?` (refuse `all`)
to arbitrary refusal sets `Z`. `rejects? P a = refuses? P ⟪a⟫` and
`deadlocked? P = refuses? P all`.

Stage 1 covers every constructor except the genuinely hard ∥ residual,
where neither side refuses all of `Z` but the sync events in `Z ∩ As`
can be split across the two sides. That partition search is Stage 2.

```
  -- Small lemma kit: shape refusals to feed ⊆ᶠ.
  opaque
    unfolding setToList

    Z⊆all : ∀ {Z : ℙ A} a → a ∈ toList Z → a ∈ toList all
    Z⊆all a _ = all-∈ a

    Z⊆Z∩Z : ∀ {Z : ℙ A} a → a ∈ toList Z → a ∈ toList (Z ∩ Z)
    Z⊆Z∩Z a a∈ = ∈-∩ .Equivalence.to (a∈ , a∈)
      where open import Function.Bundles using (Equivalence)

    -- If x ∉ Z then Z ⊆ all ＼ ⟪x⟫: every element of Z is in all (trivial)
    -- and not ≡ x (else it would be in Z ∋ x, contradicting x ∉ Z).
    Z⊆all＼⟪⟫ : ∀ {x : A} {Z : ℙ A} → ¬ (x ∈ toList Z)
              → ∀ a → a ∈ toList Z → a ∈ toList (all ＼ ⟪ x ⟫)
    Z⊆all＼⟪⟫ {x = x} x∉Z a a∈Z = ∈-filter⁺' (a∉⟪x⟫ , all-∈ a)
      where
        a∉⟪x⟫ : ¬ (a ∈ toList ⟪ x ⟫)
        a∉⟪x⟫ (here a≡x) rewrite a≡x = x∉Z a∈Z

    -- Z ⊆ (Z ＼ As) ∪ As: every element of Z is either in As or not.
    Z⊆Z＼As∪As : ∀ {As Z : ℙ A} a → a ∈ toList Z → a ∈ toList ((Z ＼ As) ∪ As)
    Z⊆Z＼As∪As {As} {Z} a a∈Z with a ∈? toList As
    ... | yes a∈As = ∈-∪⁺ {X = Z ＼ As} {Y = As} (inj₂ a∈As)
    ... | no a∉As  = ∈-∪⁺ {X = Z ＼ As} {Y = As} (inj₁ (∈-filter⁺' (a∉As , a∈Z)))
      where open import Data.Sum using (inj₁)

    -- Z ⊆ (Z ∩ Z) ∪ ((Z ∪ Z) ∩ As): trivial via the Z ∩ Z summand.
    Z⊆∥Z : ∀ {As Z : ℙ A} a → a ∈ toList Z
          → a ∈ toList ((Z ∩ Z) ∪ ((Z ∪ Z) ∩ As))
    Z⊆∥Z a a∈Z = ∈-∪⁺ (inj₁ (∈-∩ .Equivalence.to (a∈Z , a∈Z)))
      where
        open import Function.Bundles using (Equivalence)
        open import Data.Sum using (inj₁)

  refuses? : (P : Process α) (Z : ℙ A) → Dec (P ⊢ᶠ (⟨⟩ , Z))
  refuses? STOP        Z = yes (⊆ᶠ Z⊆all STOPᶠ)
  refuses? SKIP        Z with ✓ ∈? toList Z
  ... | yes ✓∈Z = no ¬SKIP-Z
    where
      opaque
        unfolding setToList
        ¬SKIP-at-⟨⟩ : ∀ {X : ℙ A} → SKIP ⊢ᶠ (⟨⟩ , X) → ¬ (✓ ∈ toList X)
        ¬SKIP-at-⟨⟩ SKIP⟨⟩ ✓∈X = ＼-∉ ✓∈X (here refl)
        ¬SKIP-at-⟨⟩ (⊆ᶠ sub p) ✓∈Y = ¬SKIP-at-⟨⟩ p (sub ✓ ✓∈Y)

        ¬SKIP-Z : ¬ (SKIP ⊢ᶠ (⟨⟩ , Z))
        ¬SKIP-Z p = ¬SKIP-at-⟨⟩ p ✓∈Z
  ... | no ✓∉Z = yes (⊆ᶠ (Z⊆all＼⟪⟫ ✓∉Z) SKIP⟨⟩)
  refuses? (x ➔ P)     Z with x ∈? toList Z
  ... | yes x∈Z = no (λ p → ¬➔-refuses-head p x∈Z)
  ... | no x∉Z  = yes (⊆ᶠ (Z⊆all＼⟪⟫ x∉Z) ➔⟨⟩)
  refuses? (P □ Q)     Z with refuses? P Z | refuses? Q Z
  ... | yes rP | yes rQ = yes (⊆ᶠ Z⊆Z∩Z (□⟨⟩ rP rQ))
  ... | no ¬rP | _      = no (¬□-P ¬rP)
    where
      opaque
        unfolding setToList
        ¬□-P : ∀ {Z' : ℙ A} → ¬ (P ⊢ᶠ (⟨⟩ , Z')) → ¬ ((P □ Q) ⊢ᶠ (⟨⟩ , Z'))
        ¬□-P ¬rP' (□⟨⟩ {X = X} {Y = Y} pP _) =
          ¬rP' (⊆ᶠ (λ a a∈ → proj₂ (∈-filter⁻' {X = X} {P = λ x → x ∈ toList Y} a∈)) pP)
        ¬□-P _ (□₁ s≢⟨⟩ _) = s≢⟨⟩ refl
        ¬□-P _ (□₂ s≢⟨⟩ _) = s≢⟨⟩ refl
        ¬□-P ¬rP' (⊆ᶠ sub p) = ¬□-P (λ r → ¬rP' (⊆ᶠ sub r)) p
  ... | yes _  | no ¬rQ = no (¬□-Q ¬rQ)
    where
      opaque
        unfolding setToList
        ¬□-Q : ∀ {Z' : ℙ A} → ¬ (Q ⊢ᶠ (⟨⟩ , Z')) → ¬ ((P □ Q) ⊢ᶠ (⟨⟩ , Z'))
        ¬□-Q ¬rQ' (□⟨⟩ {X = X} {Y = Y} _ pQ) =
          ¬rQ' (⊆ᶠ (λ a a∈ → proj₁ (∈-filter⁻' {X = X} {P = λ x → x ∈ toList Y} a∈)) pQ)
        ¬□-Q _ (□₁ s≢⟨⟩ _) = s≢⟨⟩ refl
        ¬□-Q _ (□₂ s≢⟨⟩ _) = s≢⟨⟩ refl
        ¬□-Q ¬rQ' (⊆ᶠ sub p) = ¬□-Q (λ r → ¬rQ' (⊆ᶠ sub r)) p
  refuses? (P ⊓ Q)     Z = no ¬⊓
    where
      ¬⊓ : ∀ {Z' : ℙ A} → ¬ ((P ⊓ Q) ⊢ᶠ (⟨⟩ , Z'))
      ¬⊓ (⊆ᶠ _ p) = ¬⊓ p
  -- ∥ Stage 1: easy yes when both sides refuse Z. Stage 2 covers the
  -- hard case where neither side alone refuses Z but the sync events
  -- split across the two. The old deadlocked? branches on stable/dead
  -- are subsumed (Stable→⊢ᶠ provides the witness; ¬Stable→¬⊢ᶠ refutes).
  refuses? (P ∥⦅ As ⦆ Q) Z with refuses? P Z | refuses? Q Z | stable? P | stable? Q
  ... | yes rP | yes rQ | _      | _      = yes (⊆ᶠ Z⊆∥Z (∥⟨⟩ rP rQ))
  ... | _      | _      | no ¬sP | _      = no ¬∥-P-unstable
    where
      ¬∥-P-unstable : ∀ {Z' : ℙ A} → ¬ ((P ∥⦅ As ⦆ Q) ⊢ᶠ (⟨⟩ , Z'))
      ¬∥-P-unstable (∥⟨⟩ pP _) = ¬Stable→¬⊢ᶠ ¬sP pP
      ¬∥-P-unstable (⊆ᶠ _ p)   = ¬∥-P-unstable p
  ... | _      | _      | _      | no ¬sQ = no ¬∥-Q-unstable
    where
      ¬∥-Q-unstable : ∀ {Z' : ℙ A} → ¬ ((P ∥⦅ As ⦆ Q) ⊢ᶠ (⟨⟩ , Z'))
      ¬∥-Q-unstable (∥⟨⟩ _ pQ) = ¬Stable→¬⊢ᶠ ¬sQ pQ
      ¬∥-Q-unstable (⊆ᶠ _ p)   = ¬∥-Q-unstable p
  ... | _      | _      | yes sP | yes sQ = ∥-residual
    where
      open import Data.List.Relation.Unary.All as All using (All; []; _∷_; all?; lookup)
      open import Function.Bundles using (Equivalence)

      -- Canonical maximal refusals for the two stable sides.
      XP = proj₁ (Stable→⊢ᶠ P sP)
      pP = proj₂ (Stable→⊢ᶠ P sP)
      YQ = proj₁ (Stable→⊢ᶠ Q sQ)
      pQ = proj₂ (Stable→⊢ᶠ Q sQ)

      -- The largest refusal derivable for P ∥⦅As⦆ Q at ⟨⟩.
      W : ℙ A
      W = (XP ∩ YQ) ∪ ((XP ∪ YQ) ∩ As)

      opaque
        unfolding setToList

        ∈?∥ : ∀ a → Dec (a ∈ toList W)
        ∈?∥ a with a ∈? toList XP | a ∈? toList YQ | a ∈? toList As
        ... | yes aXP | yes aYQ | _ =
              yes (∈-∪⁺ {X = XP ∩ YQ} {Y = (XP ∪ YQ) ∩ As}
                        (inj₁ (∈-∩ {X = XP} {Y = YQ} .Equivalence.to (aXP , aYQ))))
        ... | yes aXP | _       | yes aAs =
              yes (∈-∪⁺ {X = XP ∩ YQ} {Y = (XP ∪ YQ) ∩ As}
                        (inj₂ (∈-∩ {X = XP ∪ YQ} {Y = As} .Equivalence.to
                                 (∈-∪⁺ {X = XP} {Y = YQ} (inj₁ aXP) , aAs))))
        ... | _       | yes aYQ | yes aAs =
              yes (∈-∪⁺ {X = XP ∩ YQ} {Y = (XP ∪ YQ) ∩ As}
                        (inj₂ (∈-∩ {X = XP ∪ YQ} {Y = As} .Equivalence.to
                                 (∈-∪⁺ {X = XP} {Y = YQ} (inj₂ aYQ) , aAs))))
        ... | no ¬XP  | no ¬YQ  | _ = no ¬W
          where
            ¬W : ¬ (a ∈ toList W)
            ¬W a∈W with ∈-∪⁻ {X = XP ∩ YQ} {Y = (XP ∪ YQ) ∩ As} a∈W
            ... | inj₁ a∈∩ = ¬XP (proj₁ (∈-∩ {X = XP} {Y = YQ} .Equivalence.from a∈∩))
            ... | inj₂ a∈∩As
                with ∈-∪⁻ {X = XP} {Y = YQ}
                           (proj₁ (∈-∩ {X = XP ∪ YQ} {Y = As} .Equivalence.from a∈∩As))
            ...    | inj₁ a∈XP = ¬XP a∈XP
            ...    | inj₂ a∈YQ = ¬YQ a∈YQ
        ... | yes _   | no ¬YQ  | no ¬As = no ¬W
          where
            ¬W : ¬ (a ∈ toList W)
            ¬W a∈W with ∈-∪⁻ {X = XP ∩ YQ} {Y = (XP ∪ YQ) ∩ As} a∈W
            ... | inj₁ a∈∩ = ¬YQ (proj₂ (∈-∩ {X = XP} {Y = YQ} .Equivalence.from a∈∩))
            ... | inj₂ a∈∩As = ¬As (proj₂ (∈-∩ {X = XP ∪ YQ} {Y = As} .Equivalence.from a∈∩As))
        ... | no ¬XP  | yes _   | no ¬As = no ¬W
          where
            ¬W : ¬ (a ∈ toList W)
            ¬W a∈W with ∈-∪⁻ {X = XP ∩ YQ} {Y = (XP ∪ YQ) ∩ As} a∈W
            ... | inj₁ a∈∩ = ¬XP (proj₁ (∈-∩ {X = XP} {Y = YQ} .Equivalence.from a∈∩))
            ... | inj₂ a∈∩As = ¬As (proj₂ (∈-∩ {X = XP ∪ YQ} {Y = As} .Equivalence.from a∈∩As))

        ⊆?W : Dec (∀ a → a ∈ toList Z → a ∈ toList W)
        ⊆?W = Relation.Nullary.map′ wrap unwrap (all? ∈?∥ (toList Z))
          where
            wrap : All (λ a → a ∈ toList W) (toList Z)
                 → ∀ a → a ∈ toList Z → a ∈ toList W
            wrap allW a a∈Z = lookup allW a∈Z

            unwrap : (∀ a → a ∈ toList Z → a ∈ toList W)
                   → All (λ a → a ∈ toList W) (toList Z)
            unwrap f = All.tabulate (λ {a} a∈Z → f a a∈Z)

      ∥-residual : Dec ((P ∥⦅ As ⦆ Q) ⊢ᶠ (⟨⟩ , Z))
      ∥-residual with ⊆?W
      ... | yes sub = yes (⊆ᶠ sub (∥⟨⟩ pP pQ))
      ... | no ¬sub = no ¬res
        where
          ¬res : ¬ ((P ∥⦅ As ⦆ Q) ⊢ᶠ (⟨⟩ , Z))
          ¬res p = ¬sub λ a a∈Z → ⟨⟩⊢ᶠ-maximal (sP ∥ sQ) p a a∈Z
  refuses? (P ∖ As)    Z with noStepIn? P As | refuses? P (Z ＼ As) | stable? P
  ... | yes ns | yes rP | _      = yes (⊆ᶠ Z⊆Z＼As∪As (∖ᶠ rP ns))
  ... | no ¬ns | _      | _      = no ¬∖-nostep
    where
      ¬∖-nostep : ∀ {Z' : ℙ A} → ¬ ((P ∖ As) ⊢ᶠ (⟨⟩ , Z'))
      ¬∖-nostep (∖ᶠ _ ns) = ¬ns ns
      ¬∖-nostep (⊆ᶠ _ p)  = ¬∖-nostep p
  ... | _      | _      | no ¬sP = no ¬∖-unstable
    where
      ¬∖-unstable : ∀ {Z' : ℙ A} → ¬ ((P ∖ As) ⊢ᶠ (⟨⟩ , Z'))
      ¬∖-unstable (∖ᶠ pP _) = ¬Stable→¬⊢ᶠ ¬sP pP
      ¬∖-unstable (⊆ᶠ _ p)  = ¬∖-unstable p
  ... | yes _  | no ¬rP | yes _  = no (¬∖-refusal ¬rP)
    where
      opaque
        unfolding setToList
        -- If Z' ⊆ W then Z' ＼ As ⊆ W ＼ As.
        ＼-mono : ∀ {Z' W : ℙ A}
          → (∀ a → a ∈ toList Z' → a ∈ toList W)
          → ∀ a → a ∈ toList (Z' ＼ As) → a ∈ toList (W ＼ As)
        ＼-mono {Z'} Z'⊆W a a∈
          with ∈-filter⁻' {X = Z'} {P = λ x → ¬ (x ∈ toList As)} a∈
        ... | a∉As , a∈Z' = ∈-filter⁺' (a∉As , Z'⊆W a a∈Z')

        -- (X ∪ As) ＼ As ⊆ X: if a is in the union and not in As, it's in X.
        ∪＼-⊆ : ∀ {X : ℙ A} a → a ∈ toList ((X ∪ As) ＼ As) → a ∈ toList X
        ∪＼-⊆ {X} a a∈
          with ∈-filter⁻' {X = X ∪ As} {P = λ x → ¬ (x ∈ toList As)} a∈
        ... | a∉As , a∈∪ with ∈-∪⁻ {X = X} {Y = As} a∈∪
        ...   | inj₁ a∈X  = a∈X
        ...   | inj₂ a∈As = contradiction a∈As a∉As

        -- If (P ∖ As) ⊢ᶠ (⟨⟩, Z') then P ⊢ᶠ (⟨⟩, Z' ＼ As). Any derivation
        -- bottoms out at ∖ᶠ with refusal X ∪ As; then Z' ＼ As ⊆ X via
        -- ⊆ᶠ composition, so P ⊢ᶠ (⟨⟩, Z' ＼ As).
        ∖-refuses⇒P-refuses : ∀ {Z' : ℙ A}
          → (P ∖ As) ⊢ᶠ (⟨⟩ , Z')
          → P ⊢ᶠ (⟨⟩ , Z' ＼ As)
        ∖-refuses⇒P-refuses (∖ᶠ {X = X} pP _) = ⊆ᶠ (∪＼-⊆ {X = X}) pP
        ∖-refuses⇒P-refuses (⊆ᶠ sub p) =
          ⊆ᶠ (＼-mono sub) (∖-refuses⇒P-refuses p)

        ¬∖-refusal : ¬ (P ⊢ᶠ (⟨⟩ , Z ＼ As)) → ¬ ((P ∖ As) ⊢ᶠ (⟨⟩ , Z))
        ¬∖-refusal ¬rP' p = ¬rP' (∖-refuses⇒P-refuses p)

  -- Thin wrappers over `refuses?`. `rejects? P a` decides "P stably
  -- refuses `a`"; `deadlocked? P` decides "P stably refuses every event".
  rejects?    : (P : Process α) → (a : A) → Dec (P ⊢ᶠ (⟨⟩ , ⟪ a ⟫))
  rejects?    P a = refuses? P ⟪ a ⟫

  deadlocked? : (P : Process α) → Dec (P ⊢ᶠ (⟨⟩ , all))
  deadlocked? P   = refuses? P all
```

### TDD for ∥ failures

Before we add `∥` constructors to `_⊢ᶠ_`, write the target theorems.
Each forces a specific shape of constructor. The goal is that when all
of these compile with plain constructor applications (no clever
embedding), the constructor set is complete.

**Standard failure rule for `P ∥⦅As⦆ Q` at ⟨⟩** (Roscoe UCS §2.4):
if `P ⊢ᶠ (⟨⟩, X)` and `Q ⊢ᶠ (⟨⟩, Y)`, then
`P ∥⦅As⦆ Q ⊢ᶠ (⟨⟩, (X ∩ Y) ∪ ((X ∪ Y) ∩ fromList As))`.

Sync events in As are refused when *either* side refuses. Async events
are refused only when *both* sides refuse. `⊆ᶠ` then closes the
refusal downward.

**After an observable step** the constructor must track which branch
moved (synced or async), mirroring the `∥₁`/`∥₂`/`∥₃` reduction rules.

```
  module ∥-TDD where
    open import Function.Bundles using (Equivalence)
    open import Data.Sum using (inj₁; inj₂)

    opaque
      unfolding setToList

      -- `all` is contained in the parallel refusal (X ∩ Y) ∪ ((X ∪ Y) ∩ As)
      -- when both sides offer `all`, via the first (X ∩ Y) summand.
      -- Shaped to feed `⊆ᶠ`.
      all⊆∥-all : ∀ {As : ℙ A}
        → ∀ x → x ∈ toList all
        → x ∈ toList ((all ∩ all) ∪ ((all ∪ all) ∩ As))
      all⊆∥-all x x∈ = ∈-∪⁺ (inj₁ (∈-∩ .Equivalence.to (x∈ , x∈)))

    -- Test 1: STOP ∥ STOP is deadlocked.
    ∥-STOPSTOP-dead : ∀ {As : ℙ A} → STOP ∥⦅ As ⦆ STOP ⊢ᶠ (⟨⟩ , all)
    ∥-STOPSTOP-dead = ⊆ᶠ all⊆∥-all (∥⟨⟩ STOPᶠ STOPᶠ)

    -- Test 2: synced a with both sides ready: the composite can step a
    -- and reach STOP ∥ STOP which is then dead.
    ∥-sync-step : ∀ {a : A} {As : ℙ A}
      → a ∈ toList As
      → (a ➔ STOP) ∥⦅ As ⦆ (a ➔ STOP) ⊢ᶠ (⟨ a ⟩ , all)
    ∥-sync-step a∈As = ∥-sync a∈As ∥-STOPSTOP-dead

    opaque
      unfolding setToList

      -- If a ≠ b and a ≠ c, then a ∈ (all ＼ ⟪b⟫) ∩ (all ＼ ⟪c⟫), hence in
      -- the first summand of the ∥⟨⟩ refusal. Shaped to feed `⊆ᶠ`.
      ⟪⟫⊆∥-refuse₃ : ∀ {a b c : A} {As : ℙ A}
        → ¬ (a ≡ b) → ¬ (a ≡ c)
        → ∀ x → x ∈ toList ⟪ a ⟫
        → x ∈ toList (((all ＼ ⟪ b ⟫) ∩ (all ＼ ⟪ c ⟫)) ∪
                       (((all ＼ ⟪ b ⟫) ∪ (all ＼ ⟪ c ⟫)) ∩ As))
      ⟪⟫⊆∥-refuse₃ {a} {b} {c} a≠b a≠c .a (here refl) =
        ∈-∪⁺ (inj₁ (∈-∩ .Equivalence.to
          ( ⟪⟫⊆all＼ a b a≠b a (here refl)
          , ⟪⟫⊆all＼ a c a≠c a (here refl) )))

    -- Test 3: no-sync case, P refuses a (since P = b ➔ STOP), Q refuses a
    -- (Q = c ➔ STOP), a ∉ As.  Combined refuses a.
    ∥-async-refuse : ∀ {a b c : A} {As : ℙ A}
      → ¬ (a ≡ b) → ¬ (a ≡ c)
      → (b ➔ STOP) ∥⦅ As ⦆ (c ➔ STOP) ⊢ᶠ (⟨⟩ , ⟪ a ⟫)
    ∥-async-refuse a≠b a≠c = ⊆ᶠ (⟪⟫⊆∥-refuse₃ a≠b a≠c) (∥⟨⟩ ➔⟨⟩ ➔⟨⟩)

    opaque
      unfolding setToList

      -- If a ∈ As and a ≠ b, then a ∈ all ＼ ⟪b⟫ (so a ∈ X ∪ Y for
      -- X = all ＼ ⟪a⟫, Y = all ＼ ⟪b⟫) and a ∈ As, so a is in the
      -- sync summand of the ∥⟨⟩ refusal.
      ⟪⟫⊆∥-refuse₄ : ∀ {a b : A} {As : ℙ A}
        → a ∈ toList As → ¬ (b ∈ toList As)
        → ∀ x → x ∈ toList ⟪ a ⟫
        → x ∈ toList (((all ＼ ⟪ a ⟫) ∩ (all ＼ ⟪ b ⟫)) ∪
                       (((all ＼ ⟪ a ⟫) ∪ (all ＼ ⟪ b ⟫)) ∩ As))
      ⟪⟫⊆∥-refuse₄ {a} {b} {As} a∈As b∉As .a (here refl) =
        ∈-∪⁺ {X = (all ＼ ⟪ a ⟫) ∩ (all ＼ ⟪ b ⟫)}
             {Y = ((all ＼ ⟪ a ⟫) ∪ (all ＼ ⟪ b ⟫)) ∩ As}
             (inj₂ (∈-∩ .Equivalence.to
               ( ∈-∪⁺ {X = all ＼ ⟪ a ⟫} {Y = all ＼ ⟪ b ⟫}
                      (inj₂ (⟪⟫⊆all＼ a b a≠b a (here refl)))
               , a∈As )))
        where
          a≠b : ¬ (a ≡ b)
          a≠b refl = b∉As a∈As

    -- Test 4: sync discipline: P = a ➔ STOP, Q = b ➔ STOP, a ∈ As, b ∉ As.
    -- P needs sync on a which Q can't provide → a is refused.
    -- Q can fire b async → b is NOT refused.
    ∥-sync-blocks : ∀ {a b : A} {As : ℙ A}
      → a ∈ toList As → ¬ (b ∈ toList As)
      → (a ➔ STOP) ∥⦅ As ⦆ (b ➔ STOP) ⊢ᶠ (⟨⟩ , ⟪ a ⟫)
    ∥-sync-blocks {a} a∈ b∉ = ⊆ᶠ (⟪⟫⊆∥-refuse₄ a∈ b∉) (∥⟨⟩ ➔⟨⟩ ➔⟨⟩)

    -- Negative test: b is NOT refused in the above (Q can fire it async).
    -- Induction on the derivation: every constructor path either forces b
    -- into the refusal (contradicting Q's non-refusal of b) or forces
    -- b ∈ As (contradicting b∉As).
    ∥-async-alive : ∀ {a b : A} {As : ℙ A}
      → a ∈ toList As → ¬ (b ∈ toList As)
      → ¬ ((a ➔ STOP) ∥⦅ As ⦆ (b ➔ STOP) ⊢ᶠ (⟨⟩ , ⟪ b ⟫))
    ∥-async-alive {a} {b} {As} a∈ b∉ = go
      where
        opaque
          unfolding setToList

          -- b cannot sit in any ⟨⟩-refusal of the composite. Either it
          -- came from X ∩ Y (then Q = b ➔ STOP refuses b — impossible by
          -- ¬➔-refuses-head), or from (X ∪ Y) ∩ As (then b ∈ As —
          -- impossible by b∉).
          go-gen : ∀ {Z : ℙ A}
            → (a ➔ STOP) ∥⦅ As ⦆ (b ➔ STOP) ⊢ᶠ (⟨⟩ , Z)
            → ¬ (b ∈ toList Z)
          go-gen (∥⟨⟩ {X = X} {Y = Y} _ q) b∈Z
            with ∈-∪⁻ {X = X ∩ Y} {Y = (X ∪ Y) ∩ As} b∈Z
          ... | inj₁ b∈X∩Y =
                  ¬➔-refuses-head q
                    (proj₂ (∈-∩ {X = X} {Y = Y} .Equivalence.from b∈X∩Y))
          ... | inj₂ b∈∪∩As =
                  b∉ (proj₂ (∈-∩ {X = X ∪ Y} {Y = As}
                               .Equivalence.from b∈∪∩As))
          go-gen (⊆ᶠ sub p) b∈Z = go-gen p (sub b b∈Z)

          go : ¬ ((a ➔ STOP) ∥⦅ As ⦆ (b ➔ STOP) ⊢ᶠ (⟨⟩ , ⟪ b ⟫))
          go p = go-gen p (here refl)
```

