# Dining philosophers (CSP model): compositional ∥ₐ⁺ scaffold + deadlock

This is a parameterised CSP dining-philosophers model built **compositionally**
as the non-empty alphabetised-parallel fold (`∥ₐ⁺`) of one component per
philosopher and one per fork.  For `n = suc (suc m)` philosophers and forks
arranged in a ring, we set up the event type `DP`, its decidable equality, the
CSP operator instances, the ring arithmetic `_⊕1` / `_⊖1`, the per-component
processes and (value-level `EventSet`) alphabets, and finally a **deadlock
theorem** for the symmetric system.

This is the *react* port of the legacy `ITree` model: `Interaction_Trees` →
`Process_Trees`, `ITree` → `PTree`, `CSP.Definitions.{Operators,Iterate,
AlphaParallel}` → `CSP.Operators` (the alphabetised-parallel operator `αpar`,
its mixfix `_⟦_∥_⟧_`, the component record `Comp`, the union alphabet `unionα`
and the non-empty fold `∥ₐ⁺` now all live in `CSP.Operators`; the standalone
`CSP.AlphaParallel` module has been removed).

```agda
{-# OPTIONS --guardedness #-}

module CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP where

open import Level using (lift) renaming (zero to lzero)
open import Data.Nat using (ℕ; suc; zero; _<?_)
open import Data.Nat.Properties using (n<1+n)
open import Data.Fin using (Fin; toℕ; fromℕ<; inject₁) renaming (zero to fzero; suc to fsuc)
import Data.Fin as Fin
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; concatMap; drop)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Vec using (Vec; tabulate; toList)
open import Data.Bool using (if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary.Decidable.Core using (_⊎-dec_; _×-dec_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Class.DecEq using (DecEq; Irrelevant⇒DecEq)

open import Process_Trees
open import Semantics.LTS
open import Semantics.Failures using (⟹-refl)
open import Semantics.Deadlock using (IsStuck; HasDeadlock; ∖√-refl; strip∖√)
open PTree

instance
  DecEq-⊤poly : DecEq (⊤ {lzero})
  DecEq-⊤poly = Irrelevant⇒DecEq (λ { (lift _) (lift _) → refl })

module Sys (m : ℕ) where
  n : ℕ
  n = suc (suc m)
  Phil = Fin n
  Fork = Fin n

  data DP : Set → Set where
    picks    : Phil → Fork → DP (⊤ {lzero})
    putsdown : Phil → Fork → DP (⊤ {lzero})

  DP-AnyTypes-≟ : (x y : AnyTypes DP) → Dec (x ≡ y)
  DP-AnyTypes-≟ (_ , picks i f) (_ , picks i′ f′) with i Fin.≟ i′ | f Fin.≟ f′
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ { refl → ¬p refl }
  ... | _        | no ¬q    = no λ { refl → ¬q refl }
  DP-AnyTypes-≟ (_ , putsdown i f) (_ , putsdown i′ f′) with i Fin.≟ i′ | f Fin.≟ f′
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ { refl → ¬p refl }
  ... | _        | no ¬q    = no λ { refl → ¬q refl }
  DP-AnyTypes-≟ (_ , picks _ _)    (_ , putsdown _ _) = no λ ()
  DP-AnyTypes-≟ (_ , putsdown _ _) (_ , picks _ _)    = no λ ()

  import CSP.Operators {E = DP} as CSPOps
  open CSPOps DP-AnyTypes-≟
  open EventSet
  import CSP.Laws.AlphaParallel {E = DP} as CSPAParLaws
  open CSPAParLaws DP-AnyTypes-≟
  import CSP.Laws.AlphaParallelList {E = DP} as CSPAParList
  open CSPAParList DP-AnyTypes-≟

  _⊕1 : Fin n → Fin n
  _⊕1 i with suc (toℕ i) <? n
  ... | yes p = fromℕ< p
  ... | no  _ = fzero

  _⊖1 : Fin n → Fin n
  _⊖1 fzero    = fromℕ< (n<1+n (suc m))
  _⊖1 (fsuc i) = inject₁ i
```

Each philosopher `i` repeatedly picks up two forks (in a configurable order
given by `first`/`second`), then puts them both down again. Each fork `j` is
held by at most one of its two neighbouring philosophers at a time.

```agda
  PHIL : (first second : Phil → Fork) → Phil → PTree DP (ExtI DP) ⊥
  PHIL first second i =
    loop0 ( picks i (first i)     ⟶₀
           (picks i (second i)    ⟶₀
           (putsdown i (second i) ⟶₀
           (putsdown i (first i)  ⟶₀ Skip))) )

  FORK : Fork → PTree DP (ExtI DP) ⊥
  FORK j =
    loop0 ( (picks j j      ⟶₀ (putsdown j j      ⟶₀ Skip))
          □ (picks (j ⊖1) j ⟶₀ (putsdown (j ⊖1) j ⟶₀ Skip)) )
```

```agda
  -- Per-component alphabets are now value-level `EventSet`s.  The DP events carry
  -- `⊤`, so the value argument `a : ⊤` is ignored: the membership predicate and its
  -- decision are exactly the old (channel-level) `Alpha`/`Dec-Alpha`, now folded into
  -- the `mem`/`dec` fields of a single `EventSet`.
  AlphaP : Phil → EventSet
  AlphaP i .mem (_ , picks    i′ f) a = (i′ ≡ i) × ((f ≡ i) ⊎ (f ≡ i ⊕1))
  AlphaP i .mem (_ , putsdown i′ f) a = (i′ ≡ i) × ((f ≡ i) ⊎ (f ≡ i ⊕1))
  AlphaP i .dec (_ , picks    i′ f) a = (i′ Fin.≟ i) ×-dec ((f Fin.≟ i) ⊎-dec (f Fin.≟ (i ⊕1)))
  AlphaP i .dec (_ , putsdown i′ f) a = (i′ Fin.≟ i) ×-dec ((f Fin.≟ i) ⊎-dec (f Fin.≟ (i ⊕1)))

  AlphaF : Fork → EventSet
  AlphaF j .mem (_ , picks    p f) a = (f ≡ j) × ((p ≡ j) ⊎ (p ≡ j ⊖1))
  AlphaF j .mem (_ , putsdown p f) a = (f ≡ j) × ((p ≡ j) ⊎ (p ≡ j ⊖1))
  AlphaF j .dec (_ , picks    p f) a = (f Fin.≟ j) ×-dec ((p Fin.≟ j) ⊎-dec (p Fin.≟ (j ⊖1)))
  AlphaF j .dec (_ , putsdown p f) a = (f Fin.≟ j) ×-dec ((p Fin.≟ j) ⊎-dec (p Fin.≟ (j ⊖1)))
```

The whole system is the flat alphabetised parallel composition of all the
philosopher and fork processes. We build the component list with an explicit
**head** (`comps0`) plus a **tail** (`compsRest`), then take the non-empty fold
`∥ₐ⁺` of them.  The collection is non-empty for any `m` (since `n = suc (suc m)
≥ 2` there is always at least philosopher `0` and its fork), so the head is the
philosopher-`0` component and the tail is fork `0` followed by every remaining
philosopher/fork pair.  The symmetric instance has every philosopher pick up its
left fork first (deadlocks); the asymmetric instance flips philosopher `0`'s
order (deadlock-free).

```agda
  philComp : (first second : Phil → Fork) → Phil → Comp DP ⊥
  philComp first second i = comp (AlphaP i) (PHIL first second i)

  forkComp : Fork → Comp DP ⊥
  forkComp j = comp (AlphaF j) (FORK j)

  allPhils : List Phil
  allPhils = toList (tabulate (λ (i : Fin n) → i))

  -- The non-empty component collection, given as head + tail.  The full component
  -- list is `comps = concatMap (λ i → philComp i ∷ forkComp i ∷ []) allPhils`, i.e.
  -- `[phil0, fork0, phil1, fork1, …, phil(n-1), fork(n-1)]`.  `comps0` is its HEAD
  -- (the philosopher-`0` component) and `compsRest` is its genuine TAIL: fork `0`
  -- followed by the philosopher/fork pair of every *remaining* philosopher
  -- (`drop 1 allPhils = [1,…,n-1]`).  Each philosopher and fork is listed EXACTLY
  -- once — there is no duplication of philosopher/fork `0`.
  comps0 : (first second : Phil → Fork) → Comp DP ⊥
  comps0 first second = philComp first second fzero

  compsRest : (first second : Phil → Fork) → List (Comp DP ⊥)
  compsRest first second =
    forkComp fzero ∷ concatMap (λ i → philComp first second i ∷ forkComp i ∷ []) (drop 1 allPhils)

  SYSTEM : (first second : Phil → Fork)
         → PTree DP (ExtI DP) (RetOf⁺ (comps0 first second) (compsRest first second))
  SYSTEM first second = ∥ₐ⁺ (comps0 first second) (compsRest first second)

  symFirst symSecond : Phil → Fork
  symFirst  i = i
  symSecond i = i ⊕1

  asymFirst asymSecond : Phil → Fork
  asymFirst  i = if ⌊ i Fin.≟ fzero ⌋ then i ⊕1 else i
  asymSecond i = if ⌊ i Fin.≟ fzero ⌋ then i    else i ⊕1

  SYSTEMsym  : PTree DP (ExtI DP) (RetOf⁺ (comps0 symFirst  symSecond)  (compsRest symFirst  symSecond))
  SYSTEMsym  = SYSTEM symFirst  symSecond
  SYSTEMasym : PTree DP (ExtI DP) (RetOf⁺ (comps0 asymFirst asymSecond) (compsRest asymFirst asymSecond))
  SYSTEMasym = SYSTEM asymFirst asymSecond
```

## The symmetric deadlock

We prove that the symmetric two-philosopher system genuinely deadlocks.

**Configuration.**  In the symmetric ring (`first i = i`, `second i = i ⊕1`)
every philosopher first picks up the fork to its left and is then blocked
waiting for the fork to its right, which its neighbour holds.  Concretely, at
the deadlocked state philosopher `i` has performed `picks i i` and now offers
only `picks i (i ⊕1)`; fork `i` has been taken by philosopher `i` (via its
`picks i i` branch) and now offers only `putsdown i i`.  Every visible event is
declined by *some* owning component, so no LTS step is enabled.

**Why this is stated and proved at the concrete two-philosopher instance
(`m = 0`, `n = 2`), with the directly-constructed stuck composite (empty
reaching trace).**  Two infrastructural facts shape the proof.

* The *n-ary* `∥ₐ⁺-IsStuck` discharges a `(yes , yes)` synchronisation event via
  its `NetBlockedAt` sync field, which (in the strengthened, tail-refuser form)
  asks that EITHER the head OR the tail-composite refuse it.  Certifying our
  deadlock this way would still require assembling, for each of the eight
  events, the full per-layer `NetBlocked` routing datum over the head/tail split
  — more bookkeeping than the configuration warrants.  We instead read the
  stuckness straight off the fused offer map, which at `m = 0` reduces to
  `nothing` definitionally.

* `dead-IsStuck` works by **direct reduction** of the composite
  `∥ₐ⁺ deadHead deadTail` offer map.  The four-component alphabetised parallel
  (`[phil0, fork0, phil1, fork1]`) fuses into a single `react` node whose merged
  offer and τ-map are computed symbolically.  Each of the eight concrete events
  (`picks i j` and `putsdown i j` for `i, j ∈ {0, 1}`) is handed to a `sVis`
  case; the merged offer at that event reduces to `nothing` and
  `case br of λ ()` closes the goal.  The τ case uses `dead-headed` (which
  applies `∥ₐ⁺-headed` to derive that the merged τ-map is everywhere `nothing`)
  to refute `sTau`'s `branch-eq` directly.

The result is **non-vacuous**: the philosophers DO still offer their blocked
second picks (each `philD i` and `forkD j` is a single-offer `react` node),
but alphabetised parallel forces synchronisation with a partner that declines,
so the composite's merged offer is `nothing` at every event despite those
individual offers being present.

```agda
module Deadlock where
  open Sys 0
  import CSP.Operators {E = DP} as Ops
  open Ops DP-AnyTypes-≟
  open EventSet
  import CSP.Laws.AlphaParallel {E = DP} as AParLaws
  open AParLaws DP-AnyTypes-≟
  import CSP.Laws.AlphaParallelList {E = DP} as AParList
  open AParList DP-AnyTypes-≟

  -- Deadlocked component processes (each a single-offer prefix process).
  --   philD i : philosopher i has picked its first fork (i), now offers only its
  --             blocked second pick `picks i (i ⊕1)`.
  --   forkD j : fork j has been taken (by philosopher j via `picks j j`), now offers
  --             only `putsdown j j`.
  -- The blocked states are modelled as the (finite) prefix runs that have already
  -- consumed the first pick; they end in `Skip` (return ⊤) rather than re-entering
  -- the `loop0`, since at the deadlock the loop body is never completed.  This is the
  -- directly-constructed stuck composite (a faithful snapshot of the blocked
  -- configuration), not the `loop0` residual of `SYSTEMsym` — see the discussion above.
  philD : Phil → PTree DP (ExtI DP) (⊤ {lzero})
  philD i = picks i (i ⊕1) ⟶₀ (putsdown i (i ⊕1) ⟶₀ (putsdown i i ⟶₀ Skip))

  forkD : Fork → PTree DP (ExtI DP) (⊤ {lzero})
  forkD j = putsdown j j ⟶₀ Skip

  philDC : Phil → Comp DP (⊤ {lzero})
  philDC i = comp (AlphaP i) (philD i)

  forkDC : Fork → Comp DP (⊤ {lzero})
  forkDC j = comp (AlphaF j) (forkD j)

  -- The deadlocked network (two philosophers, two forks), as head + tail for `∥ₐ⁺`.
  deadHead : Comp DP (⊤ {lzero})
  deadHead = philDC fzero

  deadTail : List (Comp DP (⊤ {lzero}))
  deadTail = forkDC fzero ∷ philDC (fsuc fzero) ∷ forkDC (fsuc fzero) ∷ []

  -- A prefix process `e ⟶₀ p` is `react`-headed-and-stable (its τ-map is `∅t`).
  prefix-head : ∀ {A : Set} (e : DP A) (p : PTree DP (ExtI DP) (⊤ {lzero}))
              → VisHead (e ⟶₀ p)
  prefix-head e p = _ , _ , refl , (λ _ _ → refl)

  -- A prefix process refuses every event that does NOT match its head label.
  prefix-refuses : ∀ {A : Set} (e : DP A) (p : PTree DP (ExtI DP) (⊤ {lzero}))
                 → (at : AnyTypes DP) (a : proj₁ at)
                 → ¬ ((A , e) ≡ at)
                 → Refuses (e ⟶₀ p) at a
  prefix-refuses {A} e p at a ¬eq v τc refl with DP-AnyTypes-≟ (A , e) at
  ... | yes eq = ⊥-elim (¬eq eq)
  ... | no  _  = refl
```

**The deadlock theorem.**  The composite `∥ₐ⁺ deadHead deadTail` is
`react`-headed, and its *merged* visible-offer map is `nothing` at **every**
event: each event is owned by some pair (a philosopher and a fork) that must
synchronise, but the fork declines (offers a different label), so the
`(yes , yes)` routing of the two-alphabet operator yields `nothing`.  Note the
philosophers genuinely *do* still offer their blocked second picks — this is the
real, offer-bearing deadlock — yet the composite refuses everything because the
alphabetised parallel forces synchronisation with the (declining) forks.  We
read this off by **direct reduction** of the `∥ₐ⁺` composite's offer map; we do
*not* route through `∥ₐ⁺-IsStuck`, whose per-layer `NetBlocked` routing datum
would have to be assembled by hand for each of the eight events.  See the
discussion above.

```agda
  -- Every component (prefix process) is react-headed-and-stable, so the whole fold is
  -- react-headed-and-stable (`∥ₐ⁺-headed`); this gives the merged τ-map's stability.
  allVisDead : All (λ d → VisHead (Comp.proc d)) (deadHead ∷ deadTail)
  allVisDead = prefix-head _ _ ∷ prefix-head _ _ ∷ prefix-head _ _ ∷ prefix-head _ _ ∷ []

  dead-headed : VisHead (∥ₐ⁺ deadHead deadTail)
  dead-headed = ∥ₐ⁺-headed deadHead deadTail allVisDead

  -- No τ is enabled: the composite's merged τ-map only forwards an operand τ, and every
  -- operand is a stable prefix process (τ-map `∅t`), so the merged τ-map is everywhere
  -- `nothing` (from `∥ₐ⁺-headed`) — refuting `sTau`'s `branch-eq`.
  -- No visible event is enabled: at each concrete event the merged offer reduces to
  -- `nothing`, refuting `sVis`'s `branch-eq`.  `sRet`/`sSil` clash with the `react`
  -- force.  (`feq ≡ refl` because `∥ₐ⁺ deadHead deadTail .force` IS a `react` node.)
  dead-IsStuck : IsStuck (∥ₐ⁺ deadHead deadTail)
  dead-IsStuck (sRet ())
  dead-IsStuck (sSil ())
  dead-IsStuck (sTau {i = i} {a = a} refl br)
    with dead-headed
  ... | (v , τc , refl , st) = case trans (sym (st i a)) br of λ ()
  dead-IsStuck (sVis {at = _ , picks fzero fzero}                refl br) = case br of λ ()
  dead-IsStuck (sVis {at = _ , picks fzero (fsuc fzero)}         refl br) = case br of λ ()
  dead-IsStuck (sVis {at = _ , picks (fsuc fzero) fzero}         refl br) = case br of λ ()
  dead-IsStuck (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
  dead-IsStuck (sVis {at = _ , putsdown fzero fzero}               refl br) = case br of λ ()
  dead-IsStuck (sVis {at = _ , putsdown fzero (fsuc fzero)}        refl br) = case br of λ ()
  dead-IsStuck (sVis {at = _ , putsdown (fsuc fzero) fzero}        refl br) = case br of λ ()
  dead-IsStuck (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)} refl br) = case br of λ ()

  -- The deadlock theorem: the directly-constructed all-first-forks-held configuration
  -- of the symmetric two-philosopher system is stuck, hence has a deadlock (the empty
  -- reaching trace, since we exhibit the stuck composite itself).  Non-vacuous: the
  -- philosophers still offer their (blocked) second picks, but the composite genuinely
  -- declines every event.
  dp-csp-deadlock : HasDeadlock (∥ₐ⁺ deadHead deadTail)
  dp-csp-deadlock = [] , ∥ₐ⁺ deadHead deadTail , ∖√-refl , dead-IsStuck
```

## The reachable symmetric deadlock

The snapshot above exhibits a *directly-constructed* stuck configuration.  Here we
instead prove that the **real `loop0`-based system `SYSTEMsym` REACHES a stuck state
along a genuine (non-empty) trace** — i.e. `HasDeadlock SYSTEMsym` at `m = 0`
(`n = 2`).

**The reaching trace** is `picks 0 0` then `picks 1 1`.  At `m = 0` the corrected
`SYSTEMsym` is the genuine FOUR-fold fold `∥ₐ⁺ cP0 [cF0, cP1, cF1]` — one component
per philosopher and per fork, with no duplication.  `picks 0 0` synchronises `phil0`
with `fork0`; `picks 1 1` synchronises `phil1` with `fork1`.

**How it is assembled.**

1. *Residual `VisHead`/`Refuses`.*  `loop0 (picks i (first i) ⟶₀ rest)` is
   react-headed-and-stable with single offer `picks i (first i)`; firing it (`sVis`)
   lands on the `iter-bind` residual, AGAIN react-headed-and-stable, now offering
   `picks i (second i)`.  All these `VisHead`s hold by `refl` + a structured stability
   proof (the `□`-bodied FORK needs the index-shape case split, mirroring `∥ₐ⁺-headed`);
   each residual's offer at every *other* event reduces to `nothing` by `refl` (so it
   refuses it) — in particular `fork1`-after-`picks 1 1` refuses `picks 0 1`.
   (`first i ⊖1` is only *propositionally* `fsuc fzero`, so a residual's *positive*
   offer keyed on `⊖1` does not reduce — but the *negative* `≡ nothing` refusals all do.)

2. *Per-component first-pick big-steps* `Comp.proc c ⟹⟨ … ⟩ residual` + `VisDriven`,
   each a single `⟹-ev (sVis …) ⟹-refl` / `vd-vis … vd-nil`.

3. *Nested layering.*  The two tail composites (`tail2 = ∥ₐ⁺ cP1 [cF1]` and
   `tail3 = ∥ₐ⁺ cF0 [cP1, cF1]`) are built bottom-up as direct composite `sVis` chains
   (each composite is react-headed, so its merged offer at the fired event reduces to
   `just …` by `refl`), giving `VisDriven` for free via `svvd`; the TOP layer
   `cP0 ∥ tail3` is assembled with **`∥ₐ⁺-trace-intro`** from the head big-step, the tail
   big-step `tail3-bs`, and the merged `AlphaSync` (`picks 0 0` sync-both — phil0 and
   fork0 synchronise; `picks 1 1` sync-r — phil0 is not in its alphabet, the tail
   composite performs it solo).  This yields `SYSTEMsym ⟹⟨ map evl s ⟩ top-end`.

4. *Repackaging.*  `top-end` is *definitionally* the `∥ₐ⁺` fold `tower` of the residual
   components (same alphabets, residual processes): `repack-top` is `refl`.

5. *Stuckness.*  We read `IsStuck tower` straight off the fused offer map (all eight
   `picks`/`putsdown` events reduce to `nothing`; the τ-map is everywhere `nothing` by
   `∥ₐ⁺-headed`) — exactly as the snapshot `dead-IsStuck` does.  We do NOT route through
   the strengthened `∥ₐ⁺-IsStuck` here: its n-ary `NetBlockedAt` carries an
   *unconditional* recursive `tail` field that bottoms out at `Refuses` of the INNERMOST
   residual (`fork1`-after-`picks 1 1`), yet that residual genuinely OFFERS `putsdown 1 1`
   (declined at the composite only because its sibling `phil1`-residual declines).  The
   strengthening relaxed the head/tail-composite *sync* split but not this recursive tail
   field, so `∥ₐ⁺-IsStuck` cannot certify this particular tower; direct reduction is sound
   and is the established pattern (`dead-IsStuck`).

The result is **non-vacuous**: the reaching trace is the two genuine synchronisations
`picks 0 0 ∷ picks 1 1 ∷ []`, and the philosophers still OFFER their blocked second
picks at the stuck state — yet the composite declines every event.

```agda
module DeadlockReachable where
  open Sys 0
  open import Level using () renaming (suc to lsuc)
  open import Data.Product using (proj₂; Σ; Σ-syntax)
  open import Data.List using (map)
  open import Data.List.Relation.Unary.All using (All; []; _∷_)
  open import Function using (case_of_)
  open import Semantics.LTS using (Event; evLabel; evl)
  open import Semantics.Failures using (_⟹⟨_⟩_; ⟹-ev)
  open import Process_Trees using (react-injective)
  import CSP.Operators {E = DP} as Ops
  open Ops DP-AnyTypes-≟
  open EventSet
  import CSP.Laws.AlphaParallel {E = DP} as AParLaws
  open AParLaws DP-AnyTypes-≟ using (AlphaSync; sync-nil; sync-l; sync-r; sync-both; VisDriven; vd-nil; vd-vis)
  import CSP.Laws.AlphaParallelList {E = DP} as AParList
  open AParList DP-AnyTypes-≟

  -- the philosopher 0 process (symmetric)
  phil0 : PTree DP (ExtI DP) ⊥
  phil0 = PHIL symFirst symSecond fzero

  -- Probe A: is phil0 react-headed & stable?  (VisHead via the prefix-head shape)
  probeA : VisHead phil0
  probeA = _ , _ , refl , (λ _ _ → refl)

  -- extract the offer map of phil0
  phil0-v : (at : AnyTypes DP) → ContinueType at (Maybe (PTree DP (ExtI DP) ⊥))
  phil0-v = let (v , _ , _ , _) = probeA in v

  -- Probe B: the residual after firing picks 0 0. We GUESS it equals the offer value.
  -- First, find what phil0-v (picks 0 0) tt is by asserting it's `just <hole>`.
  probeB : Σ[ t ∈ PTree DP (ExtI DP) ⊥ ] (phil0-v (_ , picks fzero fzero) tt ≡ just t)
  probeB = _ , refl

  -- The residual after one pick.
  phil0-res : PTree DP (ExtI DP) ⊥
  phil0-res = proj₁ probeB

  -- Probe C: residual react-headed & stable?
  probeC : VisHead phil0-res
  probeC = _ , _ , refl , (λ _ _ → refl)

  phil0-res-v : (at : AnyTypes DP) → ContinueType at (Maybe (PTree DP (ExtI DP) ⊥))
  phil0-res-v = let (v , _ , _ , _) = probeC in v

  -- Probe D: residual offers picks 0 (0⊕1) = picks 0 1
  probeD : Σ[ t ∈ PTree DP (ExtI DP) ⊥ ] (phil0-res-v (_ , picks fzero (fsuc fzero)) tt ≡ just t)
  probeD = _ , refl

  -- Probe E: residual REFUSES picks 0 0 (already consumed) -- offer nothing
  probeE : phil0-res-v (_ , picks fzero fzero) tt ≡ nothing
  probeE = refl

  ----------------------------------------------------------------------------
  -- FORK side
  fork0 : PTree DP (ExtI DP) ⊥
  fork0 = FORK fzero

  -- split: is fork0 react-headed (force ≡ react _ _)?
  probeF0 : Σ[ v ∈ _ ] Σ[ τc ∈ _ ] fork0 .force ≡ react v τc
  probeF0 = _ , _ , refl

  fork0-τc : (i : AnyTypes (ExtI DP)) → ContinueType i (Maybe (PTree DP (ExtI DP) ⊥))
  fork0-τc = let (_ , τc , _) = probeF0 in τc

  -- structured stability proof (case on index shape, mirroring ∥ₐ⁺-headed's `st`)
  probeFst : ∀ i a → fork0-τc i a ≡ nothing
  probeFst (_ , base _)            _ = refl
  probeFst (_ , fin)               _ = refl
  probeFst (_ , pair (base _) _)   _ = refl
  probeFst (_ , pair (pair _ _) _) _ = refl
  probeFst (_ , pair fin i) (lift fzero , a)            = refl
  probeFst (_ , pair fin i) (lift (fsuc fzero) , a)     = refl
  probeFst (_ , pair fin i) (lift (fsuc (fsuc _)) , a)  = refl

  probeF : VisHead fork0
  probeF = _ , _ , refl , probeFst

  fork0-v : (at : AnyTypes DP) → ContinueType at (Maybe (PTree DP (ExtI DP) ⊥))
  fork0-v = let (v , _ , _ , _) = probeF in v

  -- fork0 offers picks 0 0 (its own branch) ...
  probeG : Σ[ t ∈ PTree DP (ExtI DP) ⊥ ] (fork0-v (_ , picks fzero fzero) tt ≡ just t)
  probeG = _ , refl

  -- ... and picks (0⊖1)=picks 1 0 (neighbour branch)
  probeG2 : Σ[ t ∈ PTree DP (ExtI DP) ⊥ ] (fork0-v (_ , picks (fsuc fzero) fzero) tt ≡ just t)
  probeG2 = _ , refl

  fork0-res : PTree DP (ExtI DP) ⊥
  fork0-res = proj₁ probeG

  probeH0 : Σ[ v ∈ _ ] Σ[ τc ∈ _ ] fork0-res .force ≡ react v τc
  probeH0 = _ , _ , refl
  fork0-res-τc = let (_ , τc , _) = probeH0 in τc
  probeHst : ∀ i a → fork0-res-τc i a ≡ nothing
  probeHst (_ , base _)            _ = refl
  probeHst (_ , fin)               _ = refl
  probeHst (_ , pair (base _) _)   _ = refl
  probeHst (_ , pair (pair _ _) _) _ = refl
  probeHst (_ , pair fin i) (lift fzero , a)            = refl
  probeHst (_ , pair fin i) (lift (fsuc fzero) , a)     = refl
  probeHst (_ , pair fin i) (lift (fsuc (fsuc _)) , a)  = refl
  probeH : VisHead fork0-res
  probeH = _ , _ , refl , probeHst

  fork0-res-v : (at : AnyTypes DP) → ContinueType at (Maybe (PTree DP (ExtI DP) ⊥))
  fork0-res-v = let (v , _ , _ , _) = probeH in v

  -- after fork0 takes picks 0 0, it offers ONLY putsdown 0 0 and REFUSES picks 1 0
  probeI : Σ[ t ∈ PTree DP (ExtI DP) ⊥ ] (fork0-res-v (_ , putsdown fzero fzero) tt ≡ just t)
  probeI = _ , refl

  -- does fzero ⊖1 reduce to fsuc fzero at n=2 ?  PROPOSITIONALLY (deceq) yes, defn no.
  probe-⊖ : (fzero ⊖1) ≡ fsuc fzero
  probe-⊖ = refl

  -- KEY for deadlock: fork1 after taking picks 1 1 REFUSES picks 0 1 (the phil0 blocked pick)
  fork1 : PTree DP (ExtI DP) ⊥
  fork1 = FORK (fsuc fzero)
  probeK0 : Σ[ v ∈ _ ] Σ[ τc ∈ _ ] fork1 .force ≡ react v τc
  probeK0 = _ , _ , refl
  fork1-τc = let (_ , τc , _) = probeK0 in τc
  probeKst : ∀ i a → fork1-τc i a ≡ nothing
  probeKst (_ , base _)            _ = refl
  probeKst (_ , fin)               _ = refl
  probeKst (_ , pair (base _) _)   _ = refl
  probeKst (_ , pair (pair _ _) _) _ = refl
  probeKst (_ , pair fin i) (lift fzero , a)            = refl
  probeKst (_ , pair fin i) (lift (fsuc fzero) , a)     = refl
  probeKst (_ , pair fin i) (lift (fsuc (fsuc _)) , a)  = refl
  probeK : VisHead fork1
  probeK = _ , _ , refl , probeKst
  fork1-v : (at : AnyTypes DP) → ContinueType at (Maybe (PTree DP (ExtI DP) ⊥))
  fork1-v = let (v , _ , _ , _) = probeK in v
  -- fork1 offers picks 1 1
  probeL : Σ[ t ∈ PTree DP (ExtI DP) ⊥ ] (fork1-v (_ , picks (fsuc fzero) (fsuc fzero)) tt ≡ just t)
  probeL = _ , refl
  fork1-res : PTree DP (ExtI DP) ⊥
  fork1-res = proj₁ probeL
  probeM0 : Σ[ v ∈ _ ] Σ[ τc ∈ _ ] fork1-res .force ≡ react v τc
  probeM0 = _ , _ , refl
  fork1-res-τc = let (_ , τc , _) = probeM0 in τc
  probeMst : ∀ i a → fork1-res-τc i a ≡ nothing
  probeMst (_ , base _)            _ = refl
  probeMst (_ , fin)               _ = refl
  probeMst (_ , pair (base _) _)   _ = refl
  probeMst (_ , pair (pair _ _) _) _ = refl
  probeMst (_ , pair fin i) (lift fzero , a)            = refl
  probeMst (_ , pair fin i) (lift (fsuc fzero) , a)     = refl
  probeMst (_ , pair fin i) (lift (fsuc (fsuc _)) , a)  = refl
  probeM : VisHead fork1-res
  probeM = _ , _ , refl , probeMst
  fork1-res-v : (at : AnyTypes DP) → ContinueType at (Maybe (PTree DP (ExtI DP) ⊥))
  fork1-res-v = let (v , _ , _ , _) = probeM in v
  -- fork1-res REFUSES picks 0 1 (= picks (1⊖1) 1, the neighbour pick) -- blocked!
  probeN : fork1-res-v (_ , picks fzero (fsuc fzero)) tt ≡ nothing
  probeN = refl
  -- and offers putsdown 1 1
  probeO : Σ[ t ∈ PTree DP (ExtI DP) ⊥ ] (fork1-res-v (_ , putsdown (fsuc fzero) (fsuc fzero)) tt ≡ just t)
  probeO = _ , refl

  ----------------------------------------------------------------------------
  -- Alphabet membership probes for the trace events.
  open EventSet

  -- picks 0 0 ∈ AlphaP 0 (phil0): (0≡0)×(0≡0 ⊎ ...)
  probeAP00 : AlphaP fzero .mem (_ , picks fzero fzero) tt
  probeAP00 = refl , inj₁ refl

  -- picks 0 0 ∈ AlphaF 0 (fork0): (0≡0)×(0≡0 ⊎ ...)
  probeAF00 : AlphaF fzero .mem (_ , picks fzero fzero) tt
  probeAF00 = refl , inj₁ refl

  -- picks 1 1 ∈ AlphaP 1 (phil1)
  probeAP11 : AlphaP (fsuc fzero) .mem (_ , picks (fsuc fzero) (fsuc fzero)) tt
  probeAP11 = refl , inj₁ refl

  -- picks 1 1 ∈ AlphaF 1 (fork1)
  probeAF11 : AlphaF (fsuc fzero) .mem (_ , picks (fsuc fzero) (fsuc fzero)) tt
  probeAF11 = refl , inj₁ refl

  -- Non-membership facts for sync-l / sync-r routing.
  -- picks 0 0 ∉ AlphaP 1 (phil1):  i′=0 ≠ 1
  probe¬AP1-00 : ¬ AlphaP (fsuc fzero) .mem (_ , picks fzero fzero) tt
  probe¬AP1-00 (() , _)
  -- picks 0 0 ∉ AlphaF 1 (fork1): f=0 ≠ 1
  probe¬AF1-00 : ¬ AlphaF (fsuc fzero) .mem (_ , picks fzero fzero) tt
  probe¬AF1-00 (() , _)
  -- picks 1 1 ∉ AlphaP 0 (phil0): i′=1 ≠ 0
  probe¬AP0-11 : ¬ AlphaP fzero .mem (_ , picks (fsuc fzero) (fsuc fzero)) tt
  probe¬AP0-11 (() , _)
  -- picks 1 1 ∉ AlphaF 0 (fork0): f=1 ≠ 0
  probe¬AF0-11 : ¬ AlphaF fzero .mem (_ , picks (fsuc fzero) (fsuc fzero)) tt
  probe¬AF0-11 (() , _)

  -- union membership: picks 0 0 ∈ unionα [fork0,phil1,fork1] (via fork0 head)
  probeU-00 : unionα (forkComp fzero ∷ philComp symFirst symSecond (fsuc fzero) ∷ forkComp (fsuc fzero) ∷ []) .mem (_ , picks fzero fzero) tt
  probeU-00 = inj₁ (refl , inj₁ refl)
  -- picks 1 1 ∈ unionα [fork0,phil1,fork1] (via phil1, the 2nd)
  probeU-11 : unionα (forkComp fzero ∷ philComp symFirst symSecond (fsuc fzero) ∷ forkComp (fsuc fzero) ∷ []) .mem (_ , picks (fsuc fzero) (fsuc fzero)) tt
  probeU-11 = inj₂ (inj₁ (refl , inj₁ refl))

  ----------------------------------------------------------------------------
  -- Build the reachable deadlock.

  -- phil1 + residual
  phil1 : PTree DP (ExtI DP) ⊥
  phil1 = PHIL symFirst symSecond (fsuc fzero)
  probeP1 : VisHead phil1
  probeP1 = _ , _ , refl , (λ _ _ → refl)
  phil1-v = let (v , _ , _ , _) = probeP1 in v
  probeP1off : Σ[ t ∈ PTree DP (ExtI DP) ⊥ ] (phil1-v (_ , picks (fsuc fzero) (fsuc fzero)) tt ≡ just t)
  probeP1off = _ , refl
  phil1-res : PTree DP (ExtI DP) ⊥
  phil1-res = proj₁ probeP1off
  probeP1res : VisHead phil1-res
  probeP1res = _ , _ , refl , (λ _ _ → refl)

  -- isStable directly (force reduces to react, so isStable = ∀ i a → τc i a ≡ nothing).
  st-phil0 : isStable phil0
  st-phil0 _ _ = refl
  st-phil0-res : isStable phil0-res
  st-phil0-res _ _ = refl
  st-phil1 : isStable phil1
  st-phil1 _ _ = refl
  st-phil1-res : isStable phil1-res
  st-phil1-res _ _ = refl
  st-fork0 : isStable fork0
  st-fork0 (_ , base _)            _ = refl
  st-fork0 (_ , fin)               _ = refl
  st-fork0 (_ , pair (base _) _)   _ = refl
  st-fork0 (_ , pair (pair _ _) _) _ = refl
  st-fork0 (_ , pair fin i) (lift fzero , a)            = refl
  st-fork0 (_ , pair fin i) (lift (fsuc fzero) , a)     = refl
  st-fork0 (_ , pair fin i) (lift (fsuc (fsuc _)) , a)  = refl
  st-fork0-res : isStable fork0-res
  st-fork0-res (_ , base _)            _ = refl
  st-fork0-res (_ , fin)               _ = refl
  st-fork0-res (_ , pair (base _) _)   _ = refl
  st-fork0-res (_ , pair (pair _ _) _) _ = refl
  st-fork0-res (_ , pair fin i) (lift fzero , a)            = refl
  st-fork0-res (_ , pair fin i) (lift (fsuc fzero) , a)     = refl
  st-fork0-res (_ , pair fin i) (lift (fsuc (fsuc _)) , a)  = refl
  st-fork1 : isStable fork1
  st-fork1 (_ , base _)            _ = refl
  st-fork1 (_ , fin)               _ = refl
  st-fork1 (_ , pair (base _) _)   _ = refl
  st-fork1 (_ , pair (pair _ _) _) _ = refl
  st-fork1 (_ , pair fin i) (lift fzero , a)            = refl
  st-fork1 (_ , pair fin i) (lift (fsuc fzero) , a)     = refl
  st-fork1 (_ , pair fin i) (lift (fsuc (fsuc _)) , a)  = refl
  st-fork1-res : isStable fork1-res
  st-fork1-res (_ , base _)            _ = refl
  st-fork1-res (_ , fin)               _ = refl
  st-fork1-res (_ , pair (base _) _)   _ = refl
  st-fork1-res (_ , pair (pair _ _) _) _ = refl
  st-fork1-res (_ , pair fin i) (lift fzero , a)            = refl
  st-fork1-res (_ , pair fin i) (lift (fsuc fzero) , a)     = refl
  st-fork1-res (_ , pair fin i) (lift (fsuc (fsuc _)) , a)  = refl

  ----------------------------------------------------------------------------
  -- Per-component single-event big-steps (each fires its first pick) + VisDriven.

  -- phil0 fires picks 0 0
  bc-phil0 : phil0 ⟹⟨ map evl (evLabel (⊤ {lzero}) (picks fzero fzero) tt ∷ []) ⟩ phil0-res
  bc-phil0 = ⟹-ev (sVis {at = _ , picks fzero fzero} {a = tt} refl refl) ⟹-refl
  vd-phil0 : VisDriven bc-phil0
  vd-phil0 = vd-vis {at = _ , picks fzero fzero} {a = tt} refl refl vd-nil

  -- phil1 fires picks 1 1
  bc-phil1 : phil1 ⟹⟨ map evl (evLabel (⊤ {lzero}) (picks (fsuc fzero) (fsuc fzero)) tt ∷ []) ⟩ phil1-res
  bc-phil1 = ⟹-ev (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)} {a = tt} refl refl) ⟹-refl
  vd-phil1 : VisDriven bc-phil1
  vd-phil1 = vd-vis {at = _ , picks (fsuc fzero) (fsuc fzero)} {a = tt} refl refl vd-nil

  -- fork0 fires picks 0 0
  bc-fork0 : fork0 ⟹⟨ map evl (evLabel (⊤ {lzero}) (picks fzero fzero) tt ∷ []) ⟩ fork0-res
  bc-fork0 = ⟹-ev (sVis {at = _ , picks fzero fzero} {a = tt} refl refl) ⟹-refl
  vd-fork0 : VisDriven bc-fork0
  vd-fork0 = vd-vis {at = _ , picks fzero fzero} {a = tt} refl refl vd-nil

  -- fork1 fires picks 1 1
  bc-fork1 : fork1 ⟹⟨ map evl (evLabel (⊤ {lzero}) (picks (fsuc fzero) (fsuc fzero)) tt ∷ []) ⟩ fork1-res
  bc-fork1 = ⟹-ev (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)} {a = tt} refl refl) ⟹-refl
  vd-fork1 : VisDriven bc-fork1
  vd-fork1 = vd-vis {at = _ , picks (fsuc fzero) (fsuc fzero)} {a = tt} refl refl vd-nil

  ----------------------------------------------------------------------------
  -- SYSTEMsym (m=0) is the FOUR-fold fold: ∥ₐ⁺ cP0 [cF0, cP1, cF1]
  -- (one component per philosopher and per fork; no duplication).
  cP0 cP1 cF0 cF1 : Comp DP ⊥
  cP0 = philComp symFirst symSecond fzero
  cP1 = philComp symFirst symSecond (fsuc fzero)
  cF0 = forkComp fzero
  cF1 = forkComp (fsuc fzero)

  -- residual components (original alphabets)
  rc0 rcF0 rc1 rcF1 : Comp DP ⊥
  rc0  = comp (AlphaP fzero) phil0-res
  rcF0 = comp (AlphaF fzero) fork0-res
  rc1  = comp (AlphaP (fsuc fzero)) phil1-res
  rcF1 = comp (AlphaF (fsuc fzero)) fork1-res

  -- helper: VisDriven single-vis bigstep from a react-headed tree offering at.
  svbs : ∀ {ℓr} {R : Set ℓr} {t t′ : PTree DP (ExtI DP) R} {at a}
         {v : (at′ : AnyTypes DP) → ContinueType at′ (Maybe (PTree DP (ExtI DP) R))}
         {τc}
       → t .force ≡ react v τc → v at a ≡ just t′
       → t ⟹⟨ map evl (evLabel (proj₁ at) (proj₂ at) a ∷ []) ⟩ t′
  svbs {at = at} {a = a} fe je = ⟹-ev (sVis {at = at} {a = a} fe je) ⟹-refl
  svvd : ∀ {ℓr} {R : Set ℓr} {t t′ : PTree DP (ExtI DP) R} {at a}
         {v : (at′ : AnyTypes DP) → ContinueType at′ (Maybe (PTree DP (ExtI DP) R))}
         {τc}
       → (fe : t .force ≡ react v τc) → (je : v at a ≡ just t′)
       → VisDriven (svbs {t = t} {t′ = t′} {at = at} {a = a} fe je)
  svvd {at = at} {a = a} fe je = vd-vis {at = at} {a = a} fe je vd-nil

  ----------------------------------------------------------------------------
  -- Endpoint stability via ∥ₐ⁺-headed on repackaged residual comps.
  allVH-rc1 : All (λ d → VisHead (Comp.proc d)) (rc1 ∷ rcF1 ∷ [])
  allVH-rc1 = probeP1res ∷ probeM ∷ []
  allVH-rcF0-1 : All (λ d → VisHead (Comp.proc d)) (rcF0 ∷ rc1 ∷ rcF1 ∷ [])
  allVH-rcF0-1 = probeH ∷ probeP1res ∷ probeM ∷ []
  allVH-all : All (λ d → VisHead (Comp.proc d)) (rc0 ∷ rcF0 ∷ rc1 ∷ rcF1 ∷ [])
  allVH-all = probeC ∷ allVH-rcF0-1

  react⇒isStable′ : ∀ {ℓr} {R : Set ℓr} {t : PTree DP (ExtI DP) R} {v0 τc0}
                 → t .force ≡ react v0 τc0 → (∀ i a → τc0 i a ≡ nothing) → isStable t
  react⇒isStable′ {t = t} eq tn with PTree.force t
  ... | react v0 τc0 rewrite proj₂ (react-injective eq) = tn

  st-of : ∀ {ℓr} {R : Set ℓr} (c : Comp DP R) (xs : List (Comp DP R))
        → All (λ d → VisHead (Comp.proc d)) (c ∷ xs) → isStable (∥ₐ⁺ c xs)
  st-of c xs vhs with ∥ₐ⁺-headed c xs vhs
  ... | (v , τc , feq , stb) = react⇒isStable′ {t = ∥ₐ⁺ c xs} feq stb

  ----------------------------------------------------------------------------
  -- LAYER 2 (tail2 = ∥ₐ⁺ cP1 [cF1]) : sync-both on e11.
  tail2 : PTree DP (ExtI DP) (RetOf⁺ cP1 (cF1 ∷ []))
  tail2 = ∥ₐ⁺ cP1 (cF1 ∷ [])
  tail2-end : PTree DP (ExtI DP) (RetOf⁺ cP1 (cF1 ∷ []))
  tail2-end = ∥ₐ⁺ rc1 (rcF1 ∷ [])
  -- tail2 fires e11 as a single composite sVis (both operands react-headed-stable).
  tail2-bs : tail2 ⟹⟨ map evl (evLabel (⊤ {lzero}) (picks (fsuc fzero) (fsuc fzero)) tt ∷ []) ⟩ tail2-end
  tail2-bs = svbs {t = tail2} {t′ = tail2-end} {at = _ , picks (fsuc fzero) (fsuc fzero)} {a = tt} refl refl
  tail2-vd : VisDriven tail2-bs
  tail2-vd = svvd {t = tail2} {t′ = tail2-end} {at = _ , picks (fsuc fzero) (fsuc fzero)} {a = tt} refl refl
  st-tail2-end : isStable tail2-end
  st-tail2-end = st-of rc1 (rcF1 ∷ []) allVH-rc1

  ----------------------------------------------------------------------------
  -- LAYER 3 (tail3 = ∥ₐ⁺ cF0 [cP1,cF1]) : cF0 solo e00, then e11.
  tail3 : PTree DP (ExtI DP) (RetOf⁺ cF0 (cP1 ∷ cF1 ∷ []))
  tail3 = ∥ₐ⁺ cF0 (cP1 ∷ cF1 ∷ [])
  tail3-mid : PTree DP (ExtI DP) (RetOf⁺ cF0 (cP1 ∷ cF1 ∷ []))
  tail3-mid = fork0-res ⟦ Comp.alpha cF0 ∥ unionα (cP1 ∷ cF1 ∷ []) ⟧ tail2
  tail3-end : PTree DP (ExtI DP) (RetOf⁺ cF0 (cP1 ∷ cF1 ∷ []))
  tail3-end = ∥ₐ⁺ rcF0 (rc1 ∷ rcF1 ∷ [])
  tail3-bs : tail3 ⟹⟨ map evl ( evLabel (⊤ {lzero}) (picks fzero fzero) tt
                              ∷ evLabel (⊤ {lzero}) (picks (fsuc fzero) (fsuc fzero)) tt ∷ []) ⟩ tail3-end
  tail3-bs = ⟹-ev (sVis {at = _ , picks fzero fzero} {a = tt} refl refl)
                (⟹-ev (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)} {a = tt} refl refl) ⟹-refl)
  tail3-vd : VisDriven tail3-bs
  tail3-vd = vd-vis {at = _ , picks fzero fzero} {a = tt} refl refl
                (vd-vis {at = _ , picks (fsuc fzero) (fsuc fzero)} {a = tt} refl refl vd-nil)
  st-tail3-end : isStable tail3-end
  st-tail3-end = st-of rcF0 (rc1 ∷ rcF1 ∷ []) allVH-rcF0-1

  ----------------------------------------------------------------------------
  -- TOP layer via ∥ₐ⁺-trace-intro: cP0 (head) against tail3 = ∥ₐ⁺ cF0 [cP1,cF1].
  --   picks 0 0 : ∈ AlphaP 0 and ∈ unionα [cF0,cP1,cF1] (via cF0) → sync-both.
  --   picks 1 1 : ∉ AlphaP 0, ∈ unionα [cF0,cP1,cF1] (via cP1)   → sync-r.
  asyTop : AlphaSync {I = DP} (Comp.alpha cP0) (unionα (cF0 ∷ cP1 ∷ cF1 ∷ []))
             (evLabel (⊤ {lzero}) (picks fzero fzero) tt ∷ [])
             (evLabel (⊤ {lzero}) (picks fzero fzero) tt ∷ evLabel (⊤ {lzero}) (picks (fsuc fzero) (fsuc fzero)) tt ∷ [])
             (evLabel (⊤ {lzero}) (picks fzero fzero) tt ∷ evLabel (⊤ {lzero}) (picks (fsuc fzero) (fsuc fzero)) tt ∷ [])
  asyTop = sync-both (refl , inj₁ refl) (inj₁ (refl , inj₁ refl))
              (sync-r (λ { (() , _) }) (inj₂ (inj₁ (refl , inj₁ refl))) sync-nil)

  topSys : PTree DP (ExtI DP) (RetOf⁺ cP0 (cF0 ∷ cP1 ∷ cF1 ∷ []))
  topSys = ∥ₐ⁺ cP0 (cF0 ∷ cP1 ∷ cF1 ∷ [])
  top-end : PTree DP (ExtI DP) (RetOf⁺ cP0 (cF0 ∷ cP1 ∷ cF1 ∷ []))
  top-end = phil0-res ⟦ Comp.alpha cP0 ∥ unionα (cF0 ∷ cP1 ∷ cF1 ∷ []) ⟧ tail3-end

  top-bs : topSys ⟹⟨ map evl ( evLabel (⊤ {lzero}) (picks fzero fzero) tt
                            ∷ evLabel (⊤ {lzero}) (picks (fsuc fzero) (fsuc fzero)) tt ∷ []) ⟩ top-end
  top-bs = ∥ₐ⁺-trace-intro cP0 cF0 (cP1 ∷ cF1 ∷ [])
             {bc = bc-phil0} {bxs = tail3-bs} asyTop vd-phil0 tail3-vd st-phil0-res st-tail3-end

  ----------------------------------------------------------------------------
  -- The whole reaching big-step on SYSTEMsym (topSys ≡ SYSTEMsym definitionally).
  reach-bs : SYSTEMsym ⟹⟨ map evl ( evLabel (⊤ {lzero}) (picks fzero fzero) tt
                                  ∷ evLabel (⊤ {lzero}) (picks (fsuc fzero) (fsuc fzero)) tt ∷ []) ⟩ top-end
  reach-bs = top-bs

  ----------------------------------------------------------------------------
  -- The stuck endpoint as a ∥ₐ⁺ tower of residual components, IsStuck by direct reduction.
  tower : PTree DP (ExtI DP) (RetOf⁺ rc0 (rcF0 ∷ rc1 ∷ rcF1 ∷ []))
  tower = ∥ₐ⁺ rc0 (rcF0 ∷ rc1 ∷ rcF1 ∷ [])
  repack-top : tower ≡ top-end
  repack-top = refl
  tower-headed : VisHead tower
  tower-headed = ∥ₐ⁺-headed rc0 (rcF0 ∷ rc1 ∷ rcF1 ∷ []) allVH-all
  tower-IsStuck : IsStuck tower
  tower-IsStuck (sRet ())
  tower-IsStuck (sSil ())
  tower-IsStuck (sTau {i = i} {a = a} refl br)
    with tower-headed
  ... | (v , τc , refl , st) rewrite st i a = case br of λ ()
  tower-IsStuck (sVis {at = _ , picks fzero fzero}                refl br) = case br of λ ()
  tower-IsStuck (sVis {at = _ , picks fzero (fsuc fzero)}         refl br) = case br of λ ()
  tower-IsStuck (sVis {at = _ , picks (fsuc fzero) fzero}         refl br) = case br of λ ()
  tower-IsStuck (sVis {at = _ , picks (fsuc fzero) (fsuc fzero)}  refl br) = case br of λ ()
  tower-IsStuck (sVis {at = _ , putsdown fzero fzero}               refl br) = case br of λ ()
  tower-IsStuck (sVis {at = _ , putsdown fzero (fsuc fzero)}        refl br) = case br of λ ()
  tower-IsStuck (sVis {at = _ , putsdown (fsuc fzero) fzero}        refl br) = case br of λ ()
  tower-IsStuck (sVis {at = _ , putsdown (fsuc fzero) (fsuc fzero)} refl br) = case br of λ ()

  top-end-IsStuck : IsStuck top-end
  top-end-IsStuck = tower-IsStuck

  dp-csp-deadlock-reachable : HasDeadlock SYSTEMsym
  dp-csp-deadlock-reachable =
    ( evLabel (⊤ {lzero}) (picks fzero fzero) tt
    ∷ evLabel (⊤ {lzero}) (picks (fsuc fzero) (fsuc fzero)) tt ∷ [])
    , top-end , strip∖√ reach-bs , top-end-IsStuck
```

Sanity check: instantiate the module at `m = 0` (so `n = 2`) and force both
systems *and* the deadlock theorem to elaborate end-to-end.

```agda
private
  module Sanity where
    open Sys 0
    open Deadlock
    open DeadlockReachable
    sanity-sym               = SYSTEMsym
    sanity-asym              = SYSTEMasym
    sanity-deadlock          = dp-csp-deadlock
    -- the REACHABLE deadlock of the real loop0-based SYSTEMsym (m = 0, n = 2)
    sanity-deadlock-reachable : HasDeadlock SYSTEMsym
    sanity-deadlock-reachable = dp-csp-deadlock-reachable
```
