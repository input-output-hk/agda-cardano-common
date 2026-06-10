# Dining philosophers

A worked, fully-proved example modelling the classic **dining philosophers**
problem, parameterised over the number `n = suc (suc m)` of philosophers
seated around a ring. The model is a *relational* transition system
(`Config = Fin n → Local`, transitions `_⟶[_]_`) bridged to the coinductive
interaction-tree / CSP semantics by a vis-guarded generator `proc`.

**The four headline results** (all proved, no postulates):

- `philosophers-deadlock`      — the **symmetric** strategy has a reachable,
                                  stuck configuration (`allOne`): classic deadlock.
- `philosophers-deadlock-free` — the **asymmetric** (resource-ordered) strategy
                                  is deadlock-free: every reachable config is enabled.
- `eat-reachable`              — liveness: a configuration where philosopher `0`
                                  is eating is reachable.
- `proc-allOne-IsStuck`        — the §F interaction-tree bridge lifts the relational
                                  deadlock to a genuine `IsStuck (Sym.proc allOne)`.

This file develops the foundations (Parts A–E: ring, configurations,
`heldBy`/`Free`/`Valid`, transitions, the validity invariant, both deadlock
analyses, and liveness) and then **Part F** — the interaction-tree bridge
(`§F`): the event type `DP`, the decidable enabled-step `stepTo?`, the
coinductive generator `proc` (productive via vis-guarding, **no** termination
pragma), soundness/completeness of the decision, and the lifted deadlock.

```agda
{-# OPTIONS --guardedness #-}

module CSP.Examples.DiningPhilosophers.DiningPhilosophers where
```

## §1. Imports

We work entirely in `Fin`/`ℕ` and propositional equality; no interaction
trees are needed for the foundations. We bring in `Data.Nat` order helpers
(`_<?_`, `s<s`, `1+n≢n`) to define and reason about the cyclic successor.

```agda
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _<?_; _≤?_; z<s; s<s)
open import Data.Nat.Properties using
  (1+n≢n; ≤-refl; n<1+n; <⇒≤; ≤∧≮⇒≡; ≤-pred; ≤-trans; <-trans; ≮⇒≥; <-irrefl
  ; ≤-total; ≤⇒≯; <-≤-trans; m<1+n⇒m<n∨m≡n)
open import Data.Fin using (Fin; toℕ; fromℕ<)
  renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (toℕ<n; toℕ-fromℕ<; toℕ-injective)
import Data.Fin as Fin
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (if_then_else_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)
```

A small numeric helper used when building the saturated configuration: a
`≤` that is also `≢` is a strict `<`.

```agda
≤∧≢⇒< : ∀ {a b} → a ≤ b → a ≢ b → a < b
≤∧≢⇒< {a} {b} le ne with a <? b
... | yes q = q
... | no  q = ⊥-elim (ne (≤∧≮⇒≡ le q))
```

## §2. The ring: cyclic successor on `Fin (suc (suc m))`

Philosophers sit around a circular table; fork `i ⊕1` is the right-hand
neighbour of fork `i`. We require at least two philosophers (`n = suc (suc m)`)
so the ring has no self-loop. The successor sends the last index back to
`fzero` and otherwise increments: we detect "is `i` the last index?" by
asking whether `suc (toℕ i) < suc (suc m)`. When it is, `fromℕ<` rebuilds the
incremented value as an element of `Fin (suc (suc m))`; otherwise we wrap to
`fzero`.

```agda
_⊕1 : ∀ {m} → Fin (suc (suc m)) → Fin (suc (suc m))
_⊕1 {m} i with suc (toℕ i) <? suc (suc m)
... | yes p = fromℕ< p
... | no  _ = fzero
```

## §3. The successor has no fixed point

Because the ring has at least two seats, no fork equals its neighbour:
`i ≢ i ⊕1`. We argue on the numeric image. In the incrementing branch,
`toℕ (i ⊕1) ≡ suc (toℕ i)`, which differs from `toℕ i` (`1+n≢n`). In the
wrapping branch `toℕ (i ⊕1) ≡ 0`, but `i` must be the last index — in
particular `toℕ i ≠ 0`, since otherwise `suc (toℕ i) ≡ 1 < suc (suc m)`
would have selected the incrementing branch.

```agda
⊕1-≢ : ∀ {m} (i : Fin (suc (suc m))) → i ≢ i ⊕1
⊕1-≢ {m} i eq with suc (toℕ i) <? suc (suc m)
... | yes p = 1+n≢n (sym (trans (cong toℕ eq) (toℕ-fromℕ< p)))
... | no ¬p = ¬p (toℕ-not-zero⇒last i≢0)
  where
    -- in the wrapping branch toℕ (i ⊕1) ≡ 0, so toℕ i ≡ 0
    i≢0 : toℕ i ≡ zero
    i≢0 = cong toℕ eq

    -- but if toℕ i ≡ 0 then suc (toℕ i) ≡ 1 is below suc (suc m),
    -- which contradicts the no-branch guard ¬p
    toℕ-not-zero⇒last : toℕ i ≡ zero → suc (toℕ i) < suc (suc m)
    toℕ-not-zero⇒last e rewrite e = s<s z<s
```

## §4. The generic development

The entire model is generic in the **fork-acquisition order**: each
philosopher `i` picks up two forks, `first i` and `second i`, in some
order, but the two forks are always exactly `i` and `i ⊕1` (`forks-ok`).
This lets a later part instantiate the asymmetric "one philosopher grabs
the other fork first" deadlock-free strategy alongside the naive symmetric
one.

```agda
module Generic {m : ℕ}
  (first second : Fin (suc (suc m)) → Fin (suc (suc m)))
  (forks-ok : ∀ i → (first i ≡ i × second i ≡ i ⊕1)
                   ⊎ (first i ≡ i ⊕1 × second i ≡ i))
  where

  n : ℕ
  n = suc (suc m)

  Phil = Fin n
  Fork = Fin n
```

### §4.1. Local state and configurations

Each philosopher is in one of three local states: `think`ing, holding
`one` fork, or `eat`ing (holding both). A global `Config` assigns a local
state to every philosopher; `init` starts everyone thinking. `update c i ℓ`
sets philosopher `i`'s state to `ℓ`, leaving the others unchanged — decided
by `Fin` equality on the philosopher index.

```agda
  data Local : Set where think one eat : Local

  Config : Set
  Config = Phil → Local

  init : Config
  init _ = think

  update : Config → Phil → Local → Config
  update c i ℓ j with i Fin.≟ j
  ... | yes _ = ℓ
  ... | no  _ = c j
```

### §4.2. Fork ownership

`j ∈heldBy (c , i)` says fork `j` is held by philosopher `i` in config `c`.
A thinking philosopher holds nothing; one holding a single fork holds
`first i`; an eating philosopher holds both `first i` and `second i`. A fork
is `Free` when no philosopher holds it.

```agda
  _∈heldBy_ : Fork → (Config × Phil) → Set
  j ∈heldBy (c , i) with c i
  ... | think = ⊥
  ... | one   = j ≡ first i
  ... | eat   = (j ≡ first i) ⊎ (j ≡ second i)

  Free : Config → Fork → Set
  Free c j = ∀ i → ¬ (j ∈heldBy (c , i))
```

### §4.3. Mutual exclusion

A configuration is `Valid` when no fork is held by two distinct
philosophers simultaneously — the mutual-exclusion safety property the
forks are meant to guarantee.

```agda
  Valid : Config → Set
  Valid c = ∀ i i' j → i ≢ i' → j ∈heldBy (c , i) → ¬ (j ∈heldBy (c , i'))
```

## §5. The labelled transition relation

A philosopher acts by one of three `Kind`s: pick up the `first` fork
(`takeFirst`, requires `think` and a free `first` fork), pick up the
`second` fork (`takeSecond`, requires holding `one` and a free `second`
fork), or `finish` eating and release both forks (returning to `think`).
An `Action` records which philosopher took which kind of step.

```agda
  data Kind : Set where takeFirst takeSecond finish : Kind
  Action = Phil × Kind

  data _⟶[_]_ : Config → Action → Config → Set where
    step-first  : ∀ {c i} → c i ≡ think → Free c (first i)
                → c ⟶[ i , takeFirst  ] update c i one
    step-second : ∀ {c i} → c i ≡ one   → Free c (second i)
                → c ⟶[ i , takeSecond ] update c i eat
    step-finish : ∀ {c i} → c i ≡ eat
                → c ⟶[ i , finish     ] update c i think

  Enabled : Config → Set
  Enabled c = Σ[ a ∈ Action ] Σ[ c' ∈ Config ] (c ⟶[ a ] c')

  Stuck : Config → Set
  Stuck c = ¬ Enabled c

  data Reachable : Config → Set where
    rfl  : Reachable init
    step : ∀ {c a c'} → Reachable c → c ⟶[ a ] c' → Reachable c'
```

## §6. The validity invariant

### §6.1. Membership characterisation lemmas

`_∈heldBy_` is defined by pattern-matching on `c i`. The following lemmas
expose its computational behaviour once the local state at `i` is known,
turning the opaque `with`-defined predicate into concrete equalities we
can manipulate (`rewrite`ing by the state equation forces the reduction).

```agda
  held-think : ∀ {c i j} → c i ≡ think → ¬ (j ∈heldBy (c , i))
  held-think {c} {i} eq h rewrite eq = h

  held-one→ : ∀ {c i j} → c i ≡ one → j ∈heldBy (c , i) → j ≡ first i
  held-one→ eq h rewrite eq = h

  held-one← : ∀ {c i j} → c i ≡ one → j ≡ first i → j ∈heldBy (c , i)
  held-one← eq p rewrite eq = p

  held-eat→ : ∀ {c i j} → c i ≡ eat
            → j ∈heldBy (c , i) → (j ≡ first i) ⊎ (j ≡ second i)
  held-eat→ eq h rewrite eq = h

  held-eat← : ∀ {c i j} → c i ≡ eat
            → (j ≡ first i) ⊎ (j ≡ second i) → j ∈heldBy (c , i)
  held-eat← eq p rewrite eq = p
```

### §6.2. Update lemmas

`update c i ℓ` changes only philosopher `i`. At index `i` it returns `ℓ`;
at any other index it is unchanged.

```agda
  update-same : ∀ {c i ℓ} → (update c i ℓ) i ≡ ℓ
  update-same {c} {i} {ℓ} with i Fin.≟ i
  ... | yes _  = refl
  ... | no ¬p  = ⊥-elim (¬p refl)

  update-other : ∀ {c i ℓ i'} → i ≢ i' → (update c i ℓ) i' ≡ c i'
  update-other {c} {i} {ℓ} {i'} ne with i Fin.≟ i'
  ... | yes p = ⊥-elim (ne p)
  ... | no  _ = refl
```

### §6.3. Membership transport across `update`

Membership of fork `j` by philosopher `p` depends only on the value the
config assigns to `p` (and on the fixed forks `first p`/`second p`). Hence
membership in `update c i ℓ` at an index `p ≢ i` agrees with membership in
`c`, since `update` leaves `c p` untouched. We package both directions.

```agda
  held-other→ : ∀ {c i ℓ p j} → i ≢ p
              → j ∈heldBy (update c i ℓ , p) → j ∈heldBy (c , p)
  held-other→ {c} {i} {ℓ} {p} ne h rewrite update-other {c} {i} {ℓ} ne = h

  held-other← : ∀ {c i ℓ p j} → i ≢ p
              → j ∈heldBy (c , p) → j ∈heldBy (update c i ℓ , p)
  held-other← {c} {i} {ℓ} {p} ne h rewrite update-other {c} {i} {ℓ} ne = h
```

### §6.4. The invariant

`init` is vacuously valid: everyone thinks, so no fork is held at all.
Each transition preserves validity. The argument is, in each case, that
the stepping philosopher `i` only ever *gains* a fork that was `Free`
before the step (so it cannot clash with anyone) or *loses* forks (which
can only help), while every other pair of philosophers is governed,
unchanged, by `Valid c`.

```agda
  valid-init : Valid init
  valid-init i i' j _ h = ⊥-elim (held-think {init} {i} {j} refl h)

  valid-step : ∀ {c a c'} → Valid c → c ⟶[ a ] c' → Valid c'
```

#### takeFirst

The stepping philosopher `i` moves `think → one`, newly holding `first i`,
which was `Free c`. A clash in `update c i one` either (a) involves `i` on
one side — then the fork is `first i`, held by the *other* side already in
`c`, contradicting freedom — or (b) avoids `i` entirely and is ruled out by
`Valid c`.

```agda
  valid-step V (step-first {c} {i} eqc fr) p q j ne hp hq
    with p Fin.≟ i | q Fin.≟ i
  ... | yes refl | yes refl = ⊥-elim (ne refl)
  ... | yes refl | no  q≢i  =
        let jf : j ≡ first i
            jf = held-one→ {update c i one} {i} {j} (update-same {c} {i} {one}) hp
            hq-c : j ∈heldBy (c , q)
            hq-c = held-other→ (λ e → q≢i (sym e)) hq
        in fr q (subst (λ x → x ∈heldBy (c , q)) jf hq-c)
  ... | no  p≢i  | yes refl =
        let jf : j ≡ first i
            jf = held-one→ {update c i one} {i} {j} (update-same {c} {i} {one}) hq
            hp-c : j ∈heldBy (c , p)
            hp-c = held-other→ (λ e → p≢i (sym e)) hp
        in fr p (subst (λ x → x ∈heldBy (c , p)) jf hp-c)
  ... | no  p≢i  | no  q≢i  =
        V p q j ne
          (held-other→ (λ e → p≢i (sym e)) hp)
          (held-other→ (λ e → q≢i (sym e)) hq)
```

#### takeSecond

The stepping philosopher `i` moves `one → eat`, gaining `second i` (which
was `Free c`) on top of `first i` (which it already held in `c`, where it
was governed by `Valid c`). For a clash involving `i`: if the shared fork
is `first i`, philosopher `i` already held it in `c`, so `Valid c` applies;
if it is `second i`, freedom is contradicted. Clashes avoiding `i` are
unchanged.

```agda
  valid-step V (step-second {c} {i} eqc fr) p q j ne hp hq
    with p Fin.≟ i | q Fin.≟ i
  ... | yes refl | yes refl = ⊥-elim (ne refl)
  ... | yes refl | no  q≢i  =
        let hq-c : j ∈heldBy (c , q)
            hq-c = held-other→ (λ e → q≢i (sym e)) hq
        in [ (λ j≡f → V i q j ne
                        (held-one← {c} {i} {j} eqc j≡f) hq-c)
           , (λ j≡s → fr q (subst (λ x → x ∈heldBy (c , q)) j≡s hq-c))
           ] (held-eat→ {update c i eat} {i} {j} (update-same {c} {i} {eat}) hp)
  ... | no  p≢i  | yes refl =
        let hp-c : j ∈heldBy (c , p)
            hp-c = held-other→ (λ e → p≢i (sym e)) hp
        in [ (λ j≡f → V i p j (λ e → ne (sym e))
                        (held-one← {c} {i} {j} eqc j≡f) hp-c)
           , (λ j≡s → fr p (subst (λ x → x ∈heldBy (c , p)) j≡s hp-c))
           ] (held-eat→ {update c i eat} {i} {j} (update-same {c} {i} {eat}) hq)
  ... | no  p≢i  | no  q≢i  =
        V p q j ne
          (held-other→ (λ e → p≢i (sym e)) hp)
          (held-other→ (λ e → q≢i (sym e)) hq)
```

#### finish

The stepping philosopher `i` moves `eat → think`, releasing both forks. Any
purported holding by `i` in the resulting config is absurd (it now thinks);
clashes among the others are unchanged and ruled out by `Valid c`.

```agda
  valid-step V (step-finish {c} {i} eqc) p q j ne hp hq
    with p Fin.≟ i | q Fin.≟ i
  ... | yes refl | _        =
        ⊥-elim (held-think {update c i think} {i} {j} (update-same {c} {i} {think}) hp)
  ... | no  p≢i  | yes refl =
        ⊥-elim (held-think {update c i think} {i} {j} (update-same {c} {i} {think}) hq)
  ... | no  p≢i  | no  q≢i  =
        V p q j ne
          (held-other→ (λ e → p≢i (sym e)) hp)
          (held-other→ (λ e → q≢i (sym e)) hq)

  reachable-valid : ∀ {c} → Reachable c → Valid c
  reachable-valid rfl         = valid-init
  reachable-valid (step r tr) = valid-step (reachable-valid r) tr
```

## §7. The symmetric system deadlocks

We now exhibit the classic deadlock of the **symmetric** strategy, in which
every philosopher reaches first for the fork on the same side
(`first i ≡ i`, `second i ≡ i ⊕1`). The deadlocked configuration is the one
where *everyone* holds exactly one fork: no philosopher can pick up a second
fork (its right neighbour already holds it), none is eating (so none can
finish), and none is thinking (so none can take a first fork).

### §7.1. The saturated configuration as a reachable update-spine

Rather than postulate the literal constant `λ _ → one` — which would force
function extensionality to identify it with the configuration actually
produced by the transitions — we *build* the saturated configuration as the
concrete spine of `update`s reached by letting philosophers
`0, 1, …, n-1` pick up their first fork in turn. `build k` is the
configuration after the first `k` philosophers (indices `< k`) have grabbed
a fork; `update-eq` is the `update` lemma keyed to an arbitrary queried
index.

```agda
  update-eq : ∀ {c i ℓ j} → i ≡ j → (update c i ℓ) j ≡ ℓ
  update-eq {c} {i} {ℓ} {j} e with i Fin.≟ j
  ... | yes _  = refl
  ... | no ¬p  = ⊥-elim (¬p e)

  build : ℕ → Config
  build zero    = init
  build (suc k) with suc k ≤? n
  ... | yes p = update (build k) (fromℕ< p) one
  ... | no  _ = build k
```

### §7.2. The two faces of `build`

Below the threshold philosophers hold `one`; at or above it they still
`think`. These are proved by induction on `k`, peeling one `update` per
step and dispatching on whether the queried index is the just-updated one.

```agda
  build-lt : ∀ k (i : Phil) → toℕ i < k → build k i ≡ one
  build-lt zero i ()
  build-lt (suc k) i lt with suc k ≤? n
  ... | no ¬p = build-lt k i (≤-trans (toℕ<n i) (≮⇒≥ ¬p))
  ... | yes p with toℕ i <? k
  ...   | yes ti<k = trans (update-other {build k} {fromℕ< p} {one} ne)
                          (build-lt k i ti<k)
    where
      ne : fromℕ< p ≢ i
      ne e = <-irrefl ti≡k ti<k
        where
          ti≡k : toℕ i ≡ k
          ti≡k = trans (sym (cong toℕ e)) (toℕ-fromℕ< p)
  ...   | no ¬ti<k = update-eq {build k} {fromℕ< p} {one}
                        (toℕ-injective (trans (toℕ-fromℕ< p) (sym ti≡k)))
    where
      ti≡k : toℕ i ≡ k
      ti≡k = ≤∧≮⇒≡ (≤-pred lt) ¬ti<k

  build-ge : ∀ k (i : Phil) → ¬ (toℕ i < k) → build k i ≡ think
  build-ge zero i _ = refl
  build-ge (suc k) i ¬lt with suc k ≤? n
  ... | no _ = build-ge k i (λ z → ¬lt (<-trans z (n<1+n k)))
  ... | yes p = trans (update-other {build k} {fromℕ< p} {one} ne)
                      (build-ge k i (λ z → ¬lt (<-trans z (n<1+n k))))
    where
      ne : fromℕ< p ≢ i
      ne e = ¬lt (subst (λ x → x < suc k) ti≡k (n<1+n k))
        where
          ti≡k : k ≡ toℕ i
          ti≡k = trans (sym (toℕ-fromℕ< p)) (cong toℕ e)
```

### §7.3. No philosopher in `build k` eats, and `build k` is free below the spine

In any `build k` configuration no one is `eat`ing, and a one-holder holds
its own first fork. Hence any fork `j` whose index lies at or above the
threshold is `Free`: the only candidate holder would have to be a
one-holding philosopher `p` with `first p ≡ j`, but under symmetry
(`first p ≡ p`) that forces `j ≡ p`, contradicting `p`'s being below the
threshold while `j` is not. The `go` dispatcher takes the state equation
explicitly so the opaque `_∈heldBy_` reduces in each branch.

```agda
  build-not-eat : ∀ k (q : Phil) → build k q ≢ eat
  build-not-eat k q e with toℕ q <? k
  ... | yes z = bad (trans (sym (build-lt k q z)) e)
    where bad : one ≡ eat → ⊥
          bad ()
  ... | no  z = bad (trans (sym (build-ge k q z)) e)
    where bad : think ≡ eat → ⊥
          bad ()

  build-one⇒lt : ∀ k (q : Phil) → build k q ≡ one → toℕ q < k
  build-one⇒lt k q e with toℕ q <? k
  ... | yes z = z
  ... | no  z = ⊥-elim (bad (trans (sym e) (build-ge k q z)))
    where bad : one ≡ think → ⊥
          bad ()

  build-free : ∀ k (j : Phil)
             → (∀ i → first i ≡ i)
             → ¬ (toℕ j < k)
             → Free (build k) j
  build-free k j symF ¬jlt p hp = go (build k p) refl hp
    where
      go : (ℓ : Local) → build k p ≡ ℓ → j ∈heldBy (build k , p) → ⊥
      go think eqp h = held-think {build k} {p} eqp h
      go eat   eqp h = build-not-eat k p eqp
      go one   eqp h = ¬jlt (subst (λ x → x < k) (sym (cong toℕ j≡p)) (build-one⇒lt k p eqp))
        where
          j≡p : j ≡ p
          j≡p = trans (held-one→ {build k} {p} eqp h) (symF p)
```

### §7.4. `build n` is reachable from `init`

Stepping `build k → build (suc k)` is exactly the `takeFirst` action of
philosopher `k` (index `fromℕ< p`): it still `think`s in `build k`
(`build-ge`), and its first fork — which under symmetry is itself — is
`Free` (`build-free`). No `funext` is needed: `build (suc k)` is *literally*
the `update` appearing in the transition's target.

```agda
  build-reachable : ∀ k → k ≤ n → (∀ i → first i ≡ i) → Reachable (build k)
  build-reachable zero    _  _    = rfl
  build-reachable (suc k) le symF with suc k ≤? n
  ... | no ¬p = ⊥-elim (¬p le)
  ... | yes p = step (build-reachable k (<⇒≤ le) symF) tr
    where
      iₖ : Phil
      iₖ = fromℕ< p
      eqc : build k iₖ ≡ think
      eqc = build-ge k iₖ (λ z → <-irrefl (toℕ-fromℕ< p) z)
      fr : Free (build k) (first iₖ)
      fr = subst (Free (build k)) (sym (symF iₖ))
                 (build-free k iₖ symF (λ z → <-irrefl (toℕ-fromℕ< p) z))
      tr : build k ⟶[ iₖ , takeFirst ] update (build k) iₖ one
      tr = step-first {build k} {iₖ} eqc fr
```

### §7.5. The saturated configuration `allOne`

`allOne` is `build n` — every philosopher holds `one`, but defined as the
reachable update-spine rather than the literal constant. `allOne-all-one`
recovers the pointwise fact `allOne i ≡ one` (every index is `< n`), which
is all we need downstream — no extensional equality with `λ _ → one`.

```agda
  allOne : Config
  allOne = build n

  allOne-reachable : (∀ i → first i ≡ i) → Reachable allOne
  allOne-reachable symF = build-reachable n ≤-refl symF

  allOne-all-one : ∀ i → allOne i ≡ one
  allOne-all-one i = build-lt n i (toℕ<n i)
```

### §7.6. `allOne` is stuck

Every action is refuted via `allOne-all-one`: a `takeFirst` needs a
`think`er, a `finish` needs an `eat`er — both contradict `allOne i ≡ one`.
A `takeSecond` by `i` needs `second i` free, but philosopher `i ⊕1` holds
its first fork, which under symmetry is `first (i ⊕1) ≡ i ⊕1 ≡ second i`.

```agda
  allOne-stuck : (∀ i → first i ≡ i) → (∀ i → second i ≡ i ⊕1) → Stuck allOne
  allOne-stuck symF symS ((i , takeFirst) , c' , step-first {c} {.i} eq _) =
    one≢think (trans (sym (allOne-all-one i)) eq)
    where one≢think : one ≡ think → ⊥
          one≢think ()
  allOne-stuck symF symS ((i , finish) , c' , step-finish {c} {.i} eq) =
    one≢eat (trans (sym (allOne-all-one i)) eq)
    where one≢eat : one ≡ eat → ⊥
          one≢eat ()
  allOne-stuck symF symS ((i , takeSecond) , c' , step-second {c} {.i} eq fr) =
    fr (i ⊕1) held
    where
      held : second i ∈heldBy (allOne , i ⊕1)
      held = held-one← {allOne} {i ⊕1} {second i} (allOne-all-one (i ⊕1)) j≡first
        where
          j≡first : second i ≡ first (i ⊕1)
          j≡first = trans (symS i) (sym (symF (i ⊕1)))
```

### §7.7. Deadlock

Packaging §7.5 and §7.6: under the symmetric strategy there is a reachable
configuration with no enabled action.

```agda
  symmetric-deadlock : (∀ i → first i ≡ i) → (∀ i → second i ≡ i ⊕1)
                     → Reachable allOne × Stuck allOne
  symmetric-deadlock symF symS = allOne-reachable symF , allOne-stuck symF symS
```

## §8. The asymmetric system is deadlock-free

We now show that if the fork-acquisition order is **strictly increasing**
(`asym-order : ∀ i → first i Fin.< second i`, i.e. `toℕ (first i) < toℕ
(second i)`), then *every reachable configuration has an enabled action* —
there is no deadlock. This is the classic resource-ordering argument: with a
strict global order on forks and everyone grabbing their lower-numbered fork
first, no cyclic wait can form, so the **highest-held fork** always belongs
to a philosopher who can make progress.

### §8.1. Per-philosopher "top fork"

For a holder `P` we identify a single witness fork `topFork`, dominating every
fork `P` holds (by `toℕ`). A `one`-holder holds only `first P`; an
`eat`-holder holds `first P` and `second P`, and under `asym-order` the larger
is `second P`. We carry the held proof and the domination proof together.

```agda
  TopOf : Config → Phil → Set
  TopOf c P = Σ[ F ∈ Fork ]
                ( F ∈heldBy (c , P)
                × (∀ j → j ∈heldBy (c , P) → toℕ j ≤ toℕ F) )

  topFork : (asym : ∀ i → first i Fin.< second i)
          → ∀ {c} P (ℓ : Local) → c P ≡ ℓ → ℓ ≢ think → TopOf c P
  topFork asym {c} P think eqP ¬think = ⊥-elim (¬think refl)
  topFork asym {c} P one   eqP ¬think =
    first P , held-one← {c} {P} {first P} eqP refl , dom
    where
      dom : ∀ j → j ∈heldBy (c , P) → toℕ j ≤ toℕ (first P)
      dom j h rewrite held-one→ {c} {P} {j} eqP h = ≤-refl
  topFork asym {c} P eat   eqP ¬think =
    second P , held-eat← {c} {P} {second P} eqP (inj₂ refl) , dom
    where
      open Data.Nat.Properties using (≤-reflexive)
      dom : ∀ j → j ∈heldBy (c , P) → toℕ j ≤ toℕ (second P)
      dom j h = [ (λ j≡f → ≤-trans (≤-reflexive (cong toℕ j≡f)) (<⇒≤ (asym P)))
                , (λ j≡s → ≤-reflexive (cong toℕ j≡s))
                ] (held-eat→ {c} {P} {j} eqP h)
```

### §8.2. Scanning for the globally highest held fork

`scan k` examines philosophers whose index is `< k` and reports either that
all of them are thinking, or returns a held fork `F` (held by some `P` with
`toℕ P < k`) that dominates every fork held by any philosopher of index
`< k`. The recursion peels philosopher `iₖ` (index `k`) and merges its
`TopOf` witness, if any, with the recursive result via numeric totality.

```agda
  ScanResult : Config → ℕ → Set
  ScanResult c k =
      (∀ i → toℕ i < k → c i ≡ think)
    ⊎ Σ[ F ∈ Fork ] Σ[ P ∈ Phil ]
        ( toℕ P < k
        × F ∈heldBy (c , P)
        × (∀ j i → toℕ i < k → j ∈heldBy (c , i) → toℕ j ≤ toℕ F) )

  -- split "toℕ i < suc k" into "below k" or "equal to the k-th philosopher"
  splitPhil : ∀ {k} (p : suc k ≤ n) (i : Phil)
            → toℕ i < suc k → toℕ i < k ⊎ i ≡ fromℕ< p
  splitPhil {k} p i lt with m<1+n⇒m<n∨m≡n lt
  ... | inj₁ below = inj₁ below
  ... | inj₂ eqk   = inj₂ (toℕ-injective (trans eqk (sym (toℕ-fromℕ< p))))

  scan : (asym : ∀ i → first i Fin.< second i) → ∀ {c} k → k ≤ n → ScanResult c k
  scan asym zero _ = inj₁ (λ i ())
```

The `iₖ`-thinking branch leaves the verdict unchanged (extending the
all-think / domination range to include `iₖ` is routine, dispatching the new
index via `splitPhil`). When `iₖ` holds a fork we take its `TopOf` witness and,
if the recursion already found a fork, keep the numerically larger of the two;
either way the merged fork dominates the extended range.

```agda
  scan asym {c} (suc k) p with scan asym {c} k (<⇒≤ p)
  scan asym {c} (suc k) p | inj₁ allThink with c (fromℕ< p) in eqk
  ... | think = inj₁ ext
    where
      ext : ∀ i → toℕ i < suc k → c i ≡ think
      ext i lt with splitPhil p i lt
      ... | inj₁ below = allThink i below
      ... | inj₂ refl  = eqk
  ... | one = inj₂ (proj₁ top , fromℕ< p , iₖ<sk , proj₁ (proj₂ top) , dom)
    where
      iₖ<sk : toℕ (fromℕ< p) < suc k
      iₖ<sk = subst (λ x → x < suc k) (sym (toℕ-fromℕ< p)) (n<1+n k)
      top : TopOf c (fromℕ< p)
      top = topFork asym {c} (fromℕ< p) one eqk (λ ())
      dom : ∀ j i → toℕ i < suc k → j ∈heldBy (c , i) → toℕ j ≤ toℕ (proj₁ top)
      dom j i lt h with splitPhil p i lt
      ... | inj₂ refl  = proj₂ (proj₂ top) j h
      ... | inj₁ below = ⊥-elim (held-think {c} {i} (allThink i below) h)
  ... | eat = inj₂ (proj₁ top , fromℕ< p , iₖ<sk , proj₁ (proj₂ top) , dom)
    where
      iₖ<sk : toℕ (fromℕ< p) < suc k
      iₖ<sk = subst (λ x → x < suc k) (sym (toℕ-fromℕ< p)) (n<1+n k)
      top : TopOf c (fromℕ< p)
      top = topFork asym {c} (fromℕ< p) eat eqk (λ ())
      dom : ∀ j i → toℕ i < suc k → j ∈heldBy (c , i) → toℕ j ≤ toℕ (proj₁ top)
      dom j i lt h with splitPhil p i lt
      ... | inj₂ refl  = proj₂ (proj₂ top) j h
      ... | inj₁ below = ⊥-elim (held-think {c} {i} (allThink i below) h)
  scan asym {c} (suc k) p | inj₂ (F , P , P<k , F∈P , Fdom)
    with c (fromℕ< p) in eqk
  ... | think = inj₂ (F , P , m≤n⇒m≤1+n P<k , F∈P , dom)
    where
      open Data.Nat.Properties using (m≤n⇒m≤1+n)
      dom : ∀ j i → toℕ i < suc k → j ∈heldBy (c , i) → toℕ j ≤ toℕ F
      dom j i lt h with splitPhil p i lt
      ... | inj₁ below = Fdom j i below h
      ... | inj₂ refl  = ⊥-elim (held-think {c} {i} eqk h)
  ... | one = merge
    where
      open Data.Nat.Properties using (m≤n⇒m≤1+n)
      top : TopOf c (fromℕ< p)
      top = topFork asym {c} (fromℕ< p) one eqk (λ ())
      iₖ<sk : toℕ (fromℕ< p) < suc k
      iₖ<sk = subst (λ x → x < suc k) (sym (toℕ-fromℕ< p)) (n<1+n k)
      merge : ScanResult c (suc k)
      merge with ≤-total (toℕ (proj₁ top)) (toℕ F)
      ... | inj₁ top≤F = inj₂ (F , P , m≤n⇒m≤1+n P<k , F∈P , dom)
        where
          dom : ∀ j i → toℕ i < suc k → j ∈heldBy (c , i) → toℕ j ≤ toℕ F
          dom j i lt h with splitPhil p i lt
          ... | inj₁ below = Fdom j i below h
          ... | inj₂ refl  = ≤-trans (proj₂ (proj₂ top) j h) top≤F
      ... | inj₂ F≤top = inj₂ (proj₁ top , fromℕ< p , iₖ<sk , proj₁ (proj₂ top) , dom)
        where
          dom : ∀ j i → toℕ i < suc k → j ∈heldBy (c , i) → toℕ j ≤ toℕ (proj₁ top)
          dom j i lt h with splitPhil p i lt
          ... | inj₁ below = ≤-trans (Fdom j i below h) F≤top
          ... | inj₂ refl  = proj₂ (proj₂ top) j h
  ... | eat = merge
    where
      open Data.Nat.Properties using (m≤n⇒m≤1+n)
      top : TopOf c (fromℕ< p)
      top = topFork asym {c} (fromℕ< p) eat eqk (λ ())
      iₖ<sk : toℕ (fromℕ< p) < suc k
      iₖ<sk = subst (λ x → x < suc k) (sym (toℕ-fromℕ< p)) (n<1+n k)
      merge : ScanResult c (suc k)
      merge with ≤-total (toℕ (proj₁ top)) (toℕ F)
      ... | inj₁ top≤F = inj₂ (F , P , m≤n⇒m≤1+n P<k , F∈P , dom)
        where
          dom : ∀ j i → toℕ i < suc k → j ∈heldBy (c , i) → toℕ j ≤ toℕ F
          dom j i lt h with splitPhil p i lt
          ... | inj₁ below = Fdom j i below h
          ... | inj₂ refl  = ≤-trans (proj₂ (proj₂ top) j h) top≤F
      ... | inj₂ F≤top = inj₂ (proj₁ top , fromℕ< p , iₖ<sk , proj₁ (proj₂ top) , dom)
        where
          dom : ∀ j i → toℕ i < suc k → j ∈heldBy (c , i) → toℕ j ≤ toℕ (proj₁ top)
          dom j i lt h with splitPhil p i lt
          ... | inj₁ below = ≤-trans (Fdom j i below h) F≤top
          ... | inj₂ refl  = proj₂ (proj₂ top) j h
```

### §8.3. The globally highest held fork

Running `scan` at `k = n` covers every philosopher (`toℕ i < n` always),
yielding the global verdict: either all think, or there is a held fork `F`
dominating *every* held fork.

```agda
  maxHeld : (asym : ∀ i → first i Fin.< second i) → ∀ {c}
          → (∀ i → c i ≡ think)
          ⊎ Σ[ F ∈ Fork ] Σ[ P ∈ Phil ]
              ( F ∈heldBy (c , P)
              × (∀ j i → j ∈heldBy (c , i) → toℕ j ≤ toℕ F) )
  maxHeld asym {c} with scan asym {c} n ≤-refl
  ... | inj₁ allThink = inj₁ (λ i → allThink i (toℕ<n i))
  ... | inj₂ (F , P , _ , F∈P , Fdom) =
        inj₂ (F , P , F∈P , λ j i h → Fdom j i (toℕ<n i) h)
```

### §8.4. Deadlock-freedom

If every philosopher thinks, philosopher `fzero` can take its first fork
(every fork is free, since nothing is held). Otherwise take the global
maximum held fork `F`, held by `P`, and case on `P`'s local state:

- `P` eats: `P` can `finish`.
- `P` holds `one`: then `F ≡ first P`, and by `asym-order` `toℕ F < toℕ
  (second P)`. If `second P` were held by anyone, maximality of `F` would
  force `toℕ (second P) ≤ toℕ F`, contradicting `toℕ F < toℕ (second P)`. So
  `second P` is free and `P` can `takeSecond`.
- `P` thinks: impossible, since `P` holds `F`.

No philosopher waits forever: the highest fork-holder always advances.

```agda
  no-deadlock : (asym-order : ∀ i → first i Fin.< second i)
              → ∀ {c} → Reachable c → Enabled c
  no-deadlock asym {c} r with maxHeld asym {c}
  ... | inj₁ allThink =
        (fzero , takeFirst) , update c fzero one ,
        step-first {c} {fzero} (allThink fzero) free
    where
      free : Free c (first fzero)
      free i h = held-think {c} {i} (allThink i) h
  ... | inj₂ (F , P , F∈P , Fdom) = go (c P) refl
    where
      go : (ℓ : Local) → c P ≡ ℓ → Enabled c
      go think eqP = ⊥-elim (held-think {c} {P} eqP F∈P)
      go eat   eqP = (P , finish) , update c P think , step-finish {c} {P} eqP
      go one   eqP =
        (P , takeSecond) , update c P eat , step-second {c} {P} eqP free
        where
          F≡fP : F ≡ first P
          F≡fP = held-one→ {c} {P} {F} eqP F∈P
          F<sP : toℕ F < toℕ (second P)
          F<sP = subst (λ x → toℕ x < toℕ (second P)) (sym F≡fP) (asym P)
          free : Free c (second P)
          free Q hQ = ≤⇒≯ (Fdom (second P) Q hQ) F<sP
```

### §8.5. Remark

`no-deadlock` takes `asym-order` as a *hypothesis*, not a module parameter:
the symmetric instance of §7 does not satisfy it (there `first i ⊕ second i`
need not be ordered), so there is no conflict with the deadlock of §7. A
later part will instantiate `Generic` with a concrete strictly-ordered
acquisition strategy and discharge `asym-order`, obtaining genuine
deadlock-freedom.

## §9. A liveness witness: someone can eat

Safety (mutual exclusion, §6) and the deadlock analysis (§7–§8) describe
what *cannot* go wrong; we close the generic development with a small
*liveness* witness, exhibiting a concrete reachable configuration in which
philosopher `0` is eating. The trace is the obvious one — `0` takes its
first fork, then its second:
`init —(0, takeFirst)→ update init 0 one —(0, takeSecond)→ update _ 0 eat`.

### §9.1. The two forks of a philosopher are distinct

Whichever way `forks-ok` resolves, philosopher `i`'s two forks are `i` and
`i ⊕1` (in some order), and these differ by `⊕1-≢`. Hence `first i ≢ second
i`. This is needed to see that grabbing the *second* fork after the *first*
is a genuine fresh acquisition (the second is not the one already held).

```agda
  forks-distinct : ∀ i → first i ≢ second i
  forks-distinct i eq with forks-ok i
  ... | inj₁ (f≡i  , s≡i⊕1) = ⊕1-≢ i (trans (sym f≡i) (trans eq s≡i⊕1))
  ... | inj₂ (f≡i⊕1 , s≡i ) = ⊕1-≢ i (sym (trans (sym f≡i⊕1) (trans eq s≡i)))
```

### §9.2. The eating configuration is reachable

`c1` is `init` with philosopher `0` holding `one`; `c2` is `c1` with `0`
`eat`ing. The first step is `takeFirst`: at `init` everyone thinks, so every
fork is free (nothing is held). The second step is `takeSecond`: in `c1` the
only non-thinker is `0`, holding `first 0`; it does not hold `second 0`
because the two forks differ (`forks-distinct`), and everyone else holds
nothing. So `second 0` is free and `0` can pick it up to eat.

```agda
  eat-reachable : Σ[ c ∈ Config ] (Reachable c × (c fzero ≡ eat))
  eat-reachable = c2 , step (step rfl step1) step2 , update-same {c1} {fzero} {eat}
    where
      c1 : Config
      c1 = update init fzero one
      c2 : Config
      c2 = update c1 fzero eat

      free-first : Free init (first fzero)
      free-first i h = held-think {init} {i} {first fzero} refl h

      step1 : init ⟶[ fzero , takeFirst ] c1
      step1 = step-first {init} {fzero} refl free-first

      free-second : Free c1 (second fzero)
      free-second i h with fzero Fin.≟ i
      -- at i ≡ 0: c1 0 ≡ one, so h : second 0 ≡ first 0, impossible
      ... | yes refl = forks-distinct fzero (sym h)
      -- at i ≢ 0: c1 i ≡ init i ≡ think, so h : ⊥ directly
      ... | no  z≢i  = h

      step2 : c1 ⟶[ fzero , takeSecond ] c2
      step2 = step-second {c1} {fzero} (update-same {init} {fzero} {one}) free-second
```

## §F. The interaction-tree bridge

So far the model is a *relational* transition system on `Config`. We now
build the bridge to the interaction-tree / CSP semantics: a coinductive
`proc : Config → ITree DP …` whose visible events are exactly the enabled
`Action`s, and we lift the relational deadlock (`Stuck allOne`) to a genuine
`IsStuck` state of the generated tree.

### §F.1. Event type and decidable equality

`DP` is the visible-event type for *this* philosopher count `n`: a single
constructor `act i k` carrying the philosopher `i` and the action `Kind` `k`,
returning the unit response type (mirroring `coin : VM ⊤` in the vending
machine). Decidable equality on `AnyTypes DP` reduces to decidable equality
on the payload `(Phil × Kind)`: `Phil = Fin n` has `Fin._≟_`, and `Kind` has
the obvious three-constructor decision.

```agda
  open import Level using () renaming (zero to lzero)
  open import Function using (case_of_)
  open import Data.Unit.Polymorphic using (⊤; tt)
  open import Data.Maybe using (Maybe; just; nothing)
  open import Relation.Nullary using (Dec; yes; no)

  open import Interaction_Trees
  open import ITree_Relations.LTS

  data DP : Set → Set where act : Phil → Kind → DP (⊤ {lzero})

  Kind-≟ : (k k' : Kind) → Dec (k ≡ k')
  Kind-≟ takeFirst  takeFirst  = yes refl
  Kind-≟ takeSecond takeSecond = yes refl
  Kind-≟ finish     finish     = yes refl
  Kind-≟ takeFirst  takeSecond = no λ ()
  Kind-≟ takeFirst  finish     = no λ ()
  Kind-≟ takeSecond takeFirst  = no λ ()
  Kind-≟ takeSecond finish     = no λ ()
  Kind-≟ finish     takeFirst  = no λ ()
  Kind-≟ finish     takeSecond = no λ ()

  DP-AnyTypes-≟ : (x y : AnyTypes DP) → Dec (x ≡ y)
  DP-AnyTypes-≟ (_ , act i k) (_ , act i' k') with i Fin.≟ i' | Kind-≟ k k'
  ... | yes refl | yes refl = yes refl
  ... | no  i≢i' | _        = no λ { refl → i≢i' refl }
  ... | _        | no  k≢k' = no λ { refl → k≢k' refl }
```

### §F.2. The decidable enabled-step generator `proc`

`Free?` scans the (finite) set of philosophers to decide whether a fork is
free; `stepTo?` decides whether action `(i , k)` is enabled at `c` and, if
so, returns the successor config. `proc c` then offers exactly those enabled
actions as visible events. The continuation `proc c'` sits under the `vis`
constructor, so `proc` is productive *without* any termination pragma — it is
vis-guarded.

```agda
  Local-≟ : (ℓ ℓ' : Local) → Dec (ℓ ≡ ℓ')
  Local-≟ think think = yes refl
  Local-≟ one   one   = yes refl
  Local-≟ eat   eat   = yes refl
  Local-≟ think one   = no λ ()
  Local-≟ think eat   = no λ ()
  Local-≟ one   think = no λ ()
  Local-≟ one   eat   = no λ ()
  Local-≟ eat   think = no λ ()
  Local-≟ eat   one   = no λ ()

  -- Free c j = ∀ i → ¬ (j ∈heldBy (c , i)); decided by scanning the first k
  -- philosophers and combining with Fin's finite quantifier decision.
  HeldByAny? : (c : Config) (j : Fork) → Dec (Σ[ i ∈ Phil ] (j ∈heldBy (c , i)))
  HeldByAny? c j = anyDec
    where
      open import Data.Fin.Properties using (any?)
      member? : (i : Phil) → Dec (j ∈heldBy (c , i))
      member? i = go (c i) refl
        where
          go : (ℓ : Local) → c i ≡ ℓ → Dec (j ∈heldBy (c , i))
          go think eqc = no (held-think {c} {i} eqc)
          go one   eqc with j Fin.≟ first i
          ... | yes p = yes (held-one← {c} {i} eqc p)
          ... | no ¬p = no λ h → ¬p (held-one→ {c} {i} eqc h)
          go eat   eqc with j Fin.≟ first i | j Fin.≟ second i
          ... | yes p | _     = yes (held-eat← {c} {i} eqc (inj₁ p))
          ... | _     | yes q = yes (held-eat← {c} {i} eqc (inj₂ q))
          ... | no ¬p | no ¬q = no λ h → [ ¬p , ¬q ] (held-eat→ {c} {i} eqc h)
      anyDec : Dec (Σ[ i ∈ Phil ] (j ∈heldBy (c , i)))
      anyDec = any? member?

  Free? : (c : Config) (j : Fork) → Dec (Free c j)
  Free? c j with HeldByAny? c j
  ... | yes (i , h) = no λ fr → fr i h
  ... | no  ¬held   = yes λ i h → ¬held (i , h)

  stepTo? : (c : Config) (i : Phil) (k : Kind) → Maybe Config
  stepTo? c i takeFirst  with Local-≟ (c i) think | Free? c (first i)
  ... | yes _ | yes _ = just (update c i one)
  ... | _     | _     = nothing
  stepTo? c i takeSecond with Local-≟ (c i) one | Free? c (second i)
  ... | yes _ | yes _ = just (update c i eat)
  ... | _     | _     = nothing
  stepTo? c i finish     with Local-≟ (c i) eat
  ... | yes _ = just (update c i think)
  ... | no  _ = nothing

  -- procStep wraps the optional successor so the recursive `proc c'` call
  -- sits literally under the `just` of the `vis` continuation — vis-guarded,
  -- hence productive without any termination pragma.
  procStep : Maybe Config → Maybe (ITree DP (ExtI DP) (⊤ {lzero}))
  proc     : Config → ITree DP (ExtI DP) (⊤ {lzero})

  procStep nothing   = nothing
  procStep (just c') = just (proc c')

  ITree.force (proc c) = vis λ where
    (_ , act i k) tt → procStep (stepTo? c i k)
```

### §F.3. Soundness of the decision, and the lifted deadlock

The decision procedure `stepTo?` agrees with the relational transition
`_⟶[_]_`: it returns `just c'` exactly when the action is enabled with
successor `c'`. We prove both directions.

`stepTo?-complete` (relation → decision): every relational step is witnessed
by `stepTo?`. `stepTo?-sound` (decision → relation): every `just` answer is a
genuine relational step. Then `proc-step` lifts a relational step to a visible
LTS transition of `proc`, and `proc-stuck` lifts relational `Stuck` to the
interaction-tree `IsStuck`.

```agda
  stepTo?-complete : ∀ {c i k c'} → c ⟶[ i , k ] c' → stepTo? c i k ≡ just c'
  stepTo?-complete (step-first {c} {i} eqc fr)
    with Local-≟ (c i) think | Free? c (first i)
  ... | yes _   | yes _   = refl
  ... | no ¬eq  | _       = ⊥-elim (¬eq eqc)
  ... | yes _   | no ¬fr  = ⊥-elim (¬fr fr)
  stepTo?-complete (step-second {c} {i} eqc fr)
    with Local-≟ (c i) one | Free? c (second i)
  ... | yes _   | yes _   = refl
  ... | no ¬eq  | _       = ⊥-elim (¬eq eqc)
  ... | yes _   | no ¬fr  = ⊥-elim (¬fr fr)
  stepTo?-complete (step-finish {c} {i} eqc)
    with Local-≟ (c i) eat
  ... | yes _   = refl
  ... | no ¬eq  = ⊥-elim (¬eq eqc)

  stepTo?-sound : ∀ {c i k c'} → stepTo? c i k ≡ just c' → c ⟶[ i , k ] c'
  stepTo?-sound {c} {i} {takeFirst} eq
    with Local-≟ (c i) think | Free? c (first i)
  ... | yes eqc | yes fr  with eq
  ...   | refl = step-first eqc fr
  stepTo?-sound {c} {i} {takeFirst} () | no _   | _
  stepTo?-sound {c} {i} {takeFirst} () | yes _  | no _
  stepTo?-sound {c} {i} {takeSecond} eq
    with Local-≟ (c i) one | Free? c (second i)
  ... | yes eqc | yes fr  with eq
  ...   | refl = step-second eqc fr
  stepTo?-sound {c} {i} {takeSecond} () | no _   | _
  stepTo?-sound {c} {i} {takeSecond} () | yes _  | no _
  stepTo?-sound {c} {i} {finish} eq
    with Local-≟ (c i) eat
  ... | yes eqc with eq
  ...   | refl = step-finish eqc
  stepTo?-sound {c} {i} {finish} () | no _

  -- A relational step lifts to a visible LTS transition of the generated tree.
  proc-step : ∀ {c i k c'} → c ⟶[ i , k ] c'
            → proc c ─[ ev (evl (evLabel (⊤ {lzero}) (act i k) tt)) ]─► proc c'
  proc-step {c} {i} {k} {c'} tr =
    sVis {at = ⊤ , act i k} {a = tt} refl eqj
    where
      eqj : procStep (stepTo? c i k) ≡ just (proc c')
      eqj rewrite stepTo?-complete tr = refl

  -- The relational deadlock lifts to a genuine `IsStuck` of the tree.
  -- force (proc c) = vis, so the only inbound LTS constructors are sVis
  -- (fires a visible `act i k`) and sMixVis (needs force ≡ mix, impossible).
  -- An sVis firing carries eqj : procStep (stepTo? c i k) ≡ just t', forcing
  -- stepTo? c i k ≡ just c''; stepTo?-sound then gives an enabled action,
  -- contradicting Stuck c.
  proc-stuck : ∀ {c} → Stuck c → IsStuck (proc c)
  proc-stuck {c} stk (sVis {at = _ , act i k} {a = tt} refl eqj)
    with stepTo? c i k in eqs
  ... | just c' = stk ((i , k) , c' , stepTo?-sound {c} {i} {k} {c'} eqs)
  ... | nothing = case eqj of λ ()
  proc-stuck {c} stk (sMixVis eq-mix _) = case eq-mix of λ ()
```

The top-level corollary specialises §F to the **symmetric** instance and its
deadlocked configuration `allOne`: the generated tree at `allOne` is a real
interaction-tree deadlock. It appears at the end of §10, after `module Sym`.

## §10. Two concrete instances and the headline corollaries

The generic development of §4–§9 is parametric in the fork-acquisition order
`first`/`second` (subject only to `forks-ok`). We now discharge that
parameter with the two canonical strategies and read off the headline
results: the **symmetric** strategy deadlocks (§7), the **asymmetric**
resource-ordered strategy is deadlock-free (§8). Both definitions live at the
top level, outside `Generic`.

### §10.1. A numeric distinctness lemma

`⊕1-≢` says `i ≢ i ⊕1`; transported through `toℕ` (injective) it gives the
numeric form `toℕ (i ⊕1) ≢ toℕ i`, which both asymmetric proofs need to turn
a non-strict comparison into a strict one.

```agda
⊕1-toℕ-≢ : ∀ {m} (i : Fin (suc (suc m))) → toℕ (i ⊕1) ≢ toℕ i
⊕1-toℕ-≢ i e = ⊕1-≢ i (sym (toℕ-injective e))
```

### §10.2. The symmetric strategy

Every philosopher reaches first for fork `i`, then `i ⊕1` — the naive
"everyone grabs the same-side fork first" policy of §7.

```agda
symFirst symSecond : ∀ {m} → Fin (suc (suc m)) → Fin (suc (suc m))
symFirst  i = i
symSecond i = i ⊕1

symForks : ∀ {m} (i : Fin (suc (suc m)))
         → (symFirst i ≡ i × symSecond i ≡ i ⊕1)
         ⊎ (symFirst i ≡ i ⊕1 × symSecond i ≡ i)
symForks i = inj₁ (refl , refl)

module Sym {m} = Generic {m} symFirst symSecond symForks
```

### §10.3. The asymmetric (resource-ordered) strategy

Each philosopher takes its **lower-numbered** fork first: `asymFirst i` is
whichever of `{i, i ⊕1}` has the smaller `toℕ`, `asymSecond i` the larger,
decided by `toℕ i <? toℕ (i ⊕1)`.

```agda
asymFirst asymSecond : ∀ {m} → Fin (suc (suc m)) → Fin (suc (suc m))
asymFirst  i = if ⌊ toℕ i <? toℕ (i ⊕1) ⌋ then i      else i ⊕1
asymSecond i = if ⌊ toℕ i <? toℕ (i ⊕1) ⌋ then i ⊕1   else i
```

`asymForks`: the two forks are `{i, i ⊕1}` in one order or the other,
decided by the same comparison. When `i < i ⊕1` they are taken in increasing
index order (`inj₁`); otherwise `i ⊕1 ≤ i`, and since they differ this is
strict `i ⊕1 < i`, so the forks are swapped (`inj₂`).

```agda
asymForks : ∀ {m} (i : Fin (suc (suc m)))
          → (asymFirst i ≡ i × asymSecond i ≡ i ⊕1)
          ⊎ (asymFirst i ≡ i ⊕1 × asymSecond i ≡ i)
asymForks i with toℕ i <? toℕ (i ⊕1)
... | yes _ = inj₁ (refl , refl)
... | no  _ = inj₂ (refl , refl)
```

`asymOrder`: `asymFirst i` is strictly below `asymSecond i` by `toℕ`. When
`i < i ⊕1` that is exactly the comparison; otherwise `toℕ (i ⊕1) ≤ toℕ i`
(`≮⇒≥`), strict because `toℕ (i ⊕1) ≢ toℕ i` (`⊕1-toℕ-≢`).

```agda
asymOrder : ∀ {m} (i : Fin (suc (suc m))) → asymFirst i Fin.< asymSecond i
asymOrder i with toℕ i <? toℕ (i ⊕1)
... | yes lt = lt
... | no ¬lt = ≤∧≢⇒< (≮⇒≥ ¬lt) (⊕1-toℕ-≢ i)

module Asym {m} = Generic {m} asymFirst asymSecond asymForks
```

### §10.4. Headline corollaries

```agda
-- The symmetric system can deadlock: a reachable, stuck configuration.
philosophers-deadlock
  : ∀ {m} → Sym.Reachable {m} Sym.allOne × Sym.Stuck {m} Sym.allOne
philosophers-deadlock {m} = Sym.symmetric-deadlock (λ _ → refl) (λ _ → refl)

-- The asymmetric (resource-ordered) system is deadlock-free:
-- every reachable configuration has an enabled action.
philosophers-deadlock-free
  : ∀ {m} {c : Asym.Config {m}} → Asym.Reachable c → Asym.Enabled c
philosophers-deadlock-free {m} = Asym.no-deadlock asymOrder
```

### §10.5. The deadlock as a genuine interaction-tree `IsStuck`

The relational deadlock of the symmetric system (`Sym.Stuck Sym.allOne`)
lifts, through the §F bridge, to a real interaction-tree deadlock: the
generated tree `Sym.proc Sym.allOne` admits no LTS transition whatsoever.

```agda
open import ITree_Relations.LTS using (IsStuck)

-- The generated interaction tree of the symmetric deadlock configuration
-- is genuinely stuck: no LTS label is enabled.
proc-allOne-IsStuck : ∀ {m} → IsStuck (Sym.proc {m} Sym.allOne)
proc-allOne-IsStuck {m} =
  Sym.proc-stuck (Sym.allOne-stuck (λ _ → refl) (λ _ → refl))
```

