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
open import abstract-set-theory.Prelude using (Type; Maybe; nothing; just; DecEq; _≡_; _≟_; refl; sym)
open import Data.Sum using (inj₁; inj₂)
open import Data.Bool as Bool using (Bool; true; false)
open import Data.List as L using (List; []; _∷_)
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Bool.ListAction using () renaming (all to allᵇ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Relation.Nullary as Null using (yes; no; Dec; contradiction)
open import abstract-set-theory.FiniteSetTheory using (ℙ_; mapˢ; fromList; _≡ᵉ_) renaming (❴_❵ˢ to ⟪_⟫; setToList to toList)

open import Traces.CSP using (Trace; Process; Alphabet; STOP; SKIP; _➔_; _□_; _⊓_; _∥⦅_⦆_)
import Traces.CSP
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
  holds?ᵖᵇ Prop P = allᵇ (holds?ᵇ Prop) (toList (traces P))
```
## Examples
```
  module _ {a b c : Alphabet.A α} where
    open L using (_∷_; [])

    P : Process α
    P = a ➔ (b ➔ (c ➔ SKIP))

    Q : Process α
    Q = a ➔ (c ➔ SKIP)

    R : Process α
    R = P ∥⦅ fromList (a ∷ (c ∷ [])) ⦆ Q

    prop-a-before-c : Prop α
    prop-a-before-c = ((¬ (` c)) U (` a))

    -- Agda tries to unroll the traces...
    -- This is why the structural approach is needed.
    --a-Before-c : Holdsᵖ  R
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
  open Traces.CSP.TraceSemantics {α}
  open Traces.CSP.Reduction α
  open Traces.CSP.FailureSemantics {α}
  open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)

  infix 1 _⊨_
  {-# NO_POSITIVITY_CHECK #-}
  data _⊨_ : Process α → Prop α → Type where
    -- Boolean connectives
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
    ¬₁_ : {P : Process α} {p : Prop α}
      → Null.¬ (P ⊨ p)
      → P ⊨ ¬ p
    imp₁ : {P : Process α} {p q : Prop α}
      → Null.¬ (P ⊨ p)
      → P ⊨ p ⇒ q
    imp₂ : {P : Process α} {p q : Prop α}
      → P ⊨ p
      → P ⊨ q
      → P ⊨ p ⇒ q

    -- Atomic event propositions.  ` a holds for P iff every τ-reachable
    -- offer of P is exactly {a} — Milner's weak-initials reading. This
    -- covers `a ➔ P` directly, Roscoe's identical-initials collapse
    -- `(a ➔ P) □ (a ➔ Q)`, and τ-hidden-prefix forms like
    -- `(b ➔ a ➔ P) ∖ {b}`.
    `_ : {P : Process α} {a : A} → initials* P ≡ᵉ ⟪ a ⟫ → P ⊨ ` a

    -- Next: progress-capable + every next step (obs OR τ) lands in p.
    X-step : {P : Process α} {p : Prop α}
      → Null.¬ (P ⊢ᶠ (⟨⟩ , all))                         -- not deadlocked
      → All (_⊨ p) (L.map proj₂ (followups P))           -- all obs-steps land in p
      → All (_⊨ p) (τ-followups P)                       -- all τ-steps land in p
      → P ⊨ X p

    -- Eventually: two cases.
    -- F-now: p already holds here.
    F-now : {P : Process α} {p : Prop α}
      → P ⊨ p
      → P ⊨ F p
    -- F-step: on the next step (obs or τ), F p still holds. Reuses X
    -- directly — this is the adversarial reading: every possible next
    -- step must still eventually reach p, and the process must not be
    -- deadlocked (so "eventually" actually gets a chance to fire).
    F-step : {P : Process α} {p : Prop α}
      → P ⊨ X (F p)
      → P ⊨ F p

    -- F□: external choice is "pick a side". F p on the composite holds
    -- when each offered side ⊨ F p — evaluated on the side itself, not
    -- its successor after the env picks. This matches Roscoe's reading
    -- that □ offers a menu; picking an initial commits to that branch.
    -- τ-prefixed □ is not special here: `τ ➔ Q` in a □ reduces to ⊓
    -- (internal choice) by Roscoe's step law, which is covered by F⊓.
    F□ : {P Q : Process α} {p : Prop α}
      → P ⊨ F p
      → Q ⊨ F p
      → P □ Q ⊨ F p

    -- Globally: p holds now AND at every obs-successor AND at every τ-successor.
    -- No deadlock premise: when both followup lists are empty (STOP), the
    -- universal clauses are vacuously true and we just need p locally.
    G-step : {P : Process α} {p : Prop α}
      → P ⊨ p
      → All (_⊨ G p) (L.map proj₂ (followups P))
      → All (_⊨ G p) (τ-followups P)
      → P ⊨ G p

    -- Until: base case q holds now.
    U-now : {P : Process α} {p q : Prop α}
      → P ⊨ q
      → P ⊨ p U q
    -- Step case: p holds now, must make progress, every successor (obs and τ)
    -- preserves p U q.
    U-step : {P : Process α} {p q : Prop α}
      → P ⊨ p
      → Null.¬ (P ⊢ᶠ (⟨⟩ , all))
      → All (_⊨ p U q) (L.map proj₂ (followups P))
      → All (_⊨ p U q) (τ-followups P)
      → P ⊨ p U q
```

## Derivable convenience lemmas

Several old primitive rules are now derivable.  Kept here as lemmas for
ergonomics (and so the old usage patterns still work).

```
  open import Data.List.Relation.Unary.Any using (here; there)

  -- ⊓ demonic: both branches must eventually satisfy p
  F⊓ : {P Q : Process α} {p : Prop α}
    → P ⊨ F p
    → Q ⊨ F p
    → P ⊓ Q ⊨ F p
  F⊓ pF qF = F-step (X-step (¬Stable→¬⊢ᶠ (λ ())) [] (pF ∷ qF ∷ []))

  -- Prefix: F p on the body gives F p on the prefixed process. The only
  -- obs-followup of `a ➔ P` is `(a , P)`, and `a ➔ P` cannot stably refuse
  -- its own head event.
  F➔ : {P : Process α} {p : Prop α} {a : A}
    → P ⊨ F p
    → a ➔ P ⊨ F p
  F➔ pF = F-step (X-step ¬➔-deadlocked (pF ∷ []) [])

  -- Helpers for building `_⊨ ` a` witnesses without hand-proving ≡ᵉ.
  -- Each lemma corresponds to a CSP combinator whose weak-initials
  -- reduce to a singleton by definition.
  open import Axiom.Set.Properties (abstract-set-theory.FiniteSetTheory.th) using (≡ᵉ-isEquivalence; ∉-∅)
  open import Relation.Binary.Structures using (IsEquivalence)
  open import Function.Bundles using (Equivalence)
  open import abstract-set-theory.FiniteSetTheory using (∈-singleton; ∈-∪)

  private
    module ≡ᵉ = IsEquivalence (≡ᵉ-isEquivalence {A})

  -- Prefix atom: `a ➔ P` offers exactly {a}.
  `➔ : {P : Process α} {a : A} → a ➔ P ⊨ ` a
  `➔ = `_ ≡ᵉ.refl

  -- SKIP atom
  `SKIP : SKIP ⊨ ` ✓
  `SKIP = `_ ≡ᵉ.refl

  -- SKIP eventually terminates (trivially now)
  FSKIP : SKIP ⊨ F (` ✓)
  FSKIP = F-now `SKIP
```

## Decision procedure

Left as future work once the rule set stabilises.

```
  -- _⊨?_ : (P : Process α) → (p : Prop α) → Dec (P ⊨ p)
  -- _⊨?_ = ?
```

## Soundness sanity checks

```
  module Soundness where
    open import Data.List.Relation.Unary.Any using (here; there)

    -- STOP never witnesses any atom: initials* STOP = ∅, so ⟪a⟫ ⊆ ∅ is absurd.
    STOP-⊭-atom : ∀ {a : A} → Null.¬ (STOP ⊨ ` a)
    STOP-⊭-atom (`_ (_ , ⟪a⟫⊆∅)) = ∉-∅ (⟪a⟫⊆∅ (Equivalence.to ∈-singleton refl))

    -- STOP is not progress-capable: X p always fails on STOP
    STOP-⊭-X : ∀ {p : Prop α} → Null.¬ (STOP ⊨ X p)
    STOP-⊭-X (X-step ¬dead _ _) = ¬dead STOPᶠ

    -- STOP can never eventually satisfy an atom (no successors, no local match,
    -- and F-τ guard fails because τ-followups STOP = []).
    STOP-⊭-F-atom : ∀ {a : A} → Null.¬ (STOP ⊨ F (` a))
    STOP-⊭-F-atom (F-now p) = STOP-⊭-atom p
    STOP-⊭-F-atom (F-step xF) = STOP-⊭-X xF

    -- STOP satisfies any negation of F atom (via ¬₁)
    STOP-⊨-¬F-atom : ∀ {a : A} → STOP ⊨ ¬ F (` a)
    STOP-⊨-¬F-atom = ¬₁ STOP-⊭-F-atom

    -- `b ➔ STOP` can never F-satisfy an atom distinct from b: F-now requires
    -- initials to match, F-step lands at STOP, F□ doesn't apply.
    ➔STOP-⊭-F-atom : ∀ {a b : A}
      → Null.¬ (a ≡ b)
      → Null.¬ (b ➔ STOP ⊨ F (` a))
    ➔STOP-⊭-F-atom a≢b (F-now (`_ (_ , ⟪a⟫⊆⟪b⟫))) =
      a≢b (Equivalence.from ∈-singleton
        (⟪a⟫⊆⟪b⟫ (Equivalence.to ∈-singleton refl)))
    ➔STOP-⊭-F-atom _ (F-step (X-step _ (stopF ∷ []) _)) = STOP-⊭-F-atom stopF

    -- Internal choice with STOP breaks F (` ✓): the STOP branch deadlocks
    -- No matter which F-rule we try, the process can τ-pick STOP and refuse ✓.
    -- The a≢✓ premise rules out the F-now branch: if a ≡ ✓ then
    -- initials* (a ➔ SKIP) ⊓ STOP) = ⟪a⟫ ∪ ∅ ≡ᵉ ⟪✓⟫ and F-now could fire.
    dead-⊓ : ∀ {a : A}
      → Null.¬ (a ≡ ✓)
      → Null.¬ ((a ➔ SKIP) ⊓ STOP ⊨ F (` ✓))
    dead-⊓ a≢✓ (F-now (`_ (⟪a⟫∪∅⊆⟪✓⟫ , _))) =
      a≢✓ (Equivalence.from ∈-singleton
        (⟪a⟫∪∅⊆⟪✓⟫ (Equivalence.to ∈-∪ (inj₁ (Equivalence.to ∈-singleton refl)))))
    dead-⊓ _ (F-step (X-step _ _ (_ ∷ stopF ∷ []))) = STOP-⊭-F-atom stopF

    -- External choice is adversarial for liveness. The environment may
    -- pick the b-branch and deadlock, so the composite CANNOT promise
    -- eventual ✓. Under F-step = X (F p), every obs-successor must
    -- satisfy F (` ✓) — but STOP does not.
    dead-□ : ∀ {a b : A}
      → Null.¬ (a ≡ ✓) → Null.¬ (b ≡ ✓)
      → Null.¬ (((a ➔ SKIP) □ (b ➔ STOP)) ⊨ F (` ✓))
    dead-□ a≢✓ b≢✓ (F-now (`_ (⟪a⟫∪⟪b⟫⊆⟪✓⟫ , _))) =
      a≢✓ (Equivalence.from ∈-singleton
        (⟪a⟫∪⟪b⟫⊆⟪✓⟫ (Equivalence.to ∈-∪ (inj₁ (Equivalence.to ∈-singleton refl)))))
    dead-□ _ _ (F-step (X-step _ (_ ∷ stopF ∷ []) _)) = STOP-⊭-F-atom stopF
    dead-□ _ b≢✓ (F□ _ qF) = ➔STOP-⊭-F-atom (b≢✓ ∘ sym) qF
      where open import Relation.Binary.PropositionalEquality using (sym)
            open import Function using (_∘_)
```

## Examples

### Sequential and choice processes

```
  module _ {a b c : Alphabet.A α} where
    open L using (_∷_; [])

    -- Both branches eventually reach `b`: the left does `a` then `b`,
    -- the right does `b` directly. F□ evaluates F (` b) on each
    -- offered side itself: `a ➔ b ➔ STOP` via F➔ ∘ F-now of `➔;
    -- `b ➔ a ➔ STOP` directly via F-now of `➔.
    sat-ex₁ : (a ➔ b ➔ STOP) □ (b ➔ a ➔ STOP) ⊨ F (` b)
    sat-ex₁ = F□ (F➔ (F-now `➔)) (F-now `➔)

    -- a then a then b satisfies (` a) U (` b): at every step before `b`
    -- the head is `a`, so `a` holds; eventually `b` fires and U terminates.
    sat-ex₂ : a ➔ a ➔ b ➔ STOP ⊨ (` a) U (` b)
    sat-ex₂ = U-step `➔ ¬➔-deadlocked
                    (U-step `➔ ¬➔-deadlocked
                            (U-now `➔ ∷ [])
                            [] ∷ [])
                    []
```

### Vending machine

```
  module _ {coin tea coffee : Alphabet.A α} where
    open L using (_∷_; [])

    VM₁ : Process α
    VM₁ = coin ➔ ((tea ➔ STOP) □ (coffee ➔ STOP))

    VMSpec : Prop α
    VMSpec = (` coin) ⇒ (X ((` tea) ∨ (` coffee)))

    -- Blocked on atom-through-□: the X-step obs-successor is the bare □,
    -- and neither `_∨₁_` nor `_∨₂_` can witness ` tea / ` coffee at the □
    -- level (atom rules only fire on `a ➔ _` and SKIP).  Resolving needs
    -- either a `□-atom` distributing rule (`P ⊨ ` a → P □ Q ⊨ ` a`) or a
    -- reformulation that pushes X down into the □ branches.  See
    -- session-notes.md — "Open design: atoms through □ and ∥".
    -- VM₁-VMSpec : VM₁ ⊨ VMSpec
    -- VM₁-VMSpec = ?
```

### The r-sat parallel example

```
  module _ {a b c : Alphabet.A α} where
    open L using (_∷_; [])

    prop-a-before-c : Prop α
    prop-a-before-c = ((¬ (` c)) U (` a))

    P : Process α
    P = a ➔ (b ➔ (c ➔ SKIP))

    Q : Process α
    Q = a ➔ (c ➔ SKIP)

    R : Process α
    R = P ∥⦅ fromList (a ∷ (c ∷ [])) ⦆ Q

    -- Blocked on atom-through-∥ and U over ∥: R's obs-followups are ∥
    -- composites whose head atoms aren't directly witnessable via `` `_ ``.
    -- Same root cause as VM₁-VMSpec.  Deferred.
    -- r-sat : R ⊨ prop-a-before-c
    -- r-sat = ?
```

### next-⊓ refutation

```
  module _ {a b : Alphabet.A α} where
    -- Internal choice does NOT make the next event certain: the process
    -- could τ-pick (b ➔ STOP), whose head atom is b.  Under the new
    -- X-step, τ-branches must directly witness ` a, but (b ➔ STOP) ⊨ ` a
    -- only if b ≡ a.
    next-⊓ : Null.¬ (a ≡ b) → Null.¬ ((a ➔ STOP) ⊓ (b ➔ STOP) ⊨ (X_ (` a)))
    next-⊓ a≢b (X-step _ _ (_ ∷ `_ (_ , ⟪a⟫⊆⟪b⟫) ∷ [])) =
      a≢b (Equivalence.from ∈-singleton (⟪a⟫⊆⟪b⟫ (Equivalence.to ∈-singleton refl)))
```
