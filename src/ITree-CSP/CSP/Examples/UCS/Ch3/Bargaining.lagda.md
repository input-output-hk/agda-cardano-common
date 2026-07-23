# UCS chapter 3: bargaining Customer and Merchant deadlock (no agreement)

A "UCS" example, porting the bargaining Customer/Merchant processes of A.W.
Roscoe's *Understanding Concurrent Systems* (UCS), chapter 3, machine-readable
companion file:

- `fdr-examples/ucs/chapter03/ucs3.csp` (UCS ch. 3, bargaining)

A `Customer` and a `Merchant` haggle over the price of an item on a shared
`buy` channel; the `Merchant` announces `outofstock` for items it does not
stock.  Each side has its own price model:

```csp
pval(x) = (7*x + 1) % 8          -- customer's MAXIMUM acceptable price for item x
mval(x) = (5*x + 3) % 7          -- merchant's MINIMUM acceptable price for item x

Merchant(X) =    buy?x?y : (x ∈ X ∧ mval(x) ≤ y ≤ 10) -> Merchant(diff(X,{x}))
              [] outofstock!x : (x ∉ X)                -> Merchant(X)

Customer(Y) = |~| x : Item @
                 (   buy.x?y : {0 .. min(Y, pval(x))} -> Customer(Y - y)
                  [] outofstock.x                     -> Customer(Y) )

assert Customer(Y0) [| {| buy, outofstock |} |] Merchant(X0) :[deadlock free]   -- FAILS in FDR
```

**Why the full-synchronisation composition deadlocks.**  Under full
synchronisation on `{| buy, outofstock |}`, *every* `buy`/`outofstock` event
must be offered by *both* the customer and the merchant.  The `Customer`
resolves an **internal** choice of which item to bargain for (a τ), and for
**item 1** the two price windows are disjoint:

- `pval 1 = (7·1+1) % 8 = 8 % 8 = 0` — the customer will pay only `y ∈ {0}`;
- `mval 1 = (5·1+3) % 7 = 8 % 7 = 1` — the merchant sells item 1 only at
  `y ∈ {1 .. 10}`.

So there is **no price** on which both agree, and — since item 1 is in stock —
the merchant never offers `outofstock.1` either.  After the customer silently
commits to item 1, the composite offers *nothing*: a genuine **deadlock** at
the empty trace.  (By contrast `pval 2 = 15 % 8 = 7` and `mval 2 = 13 % 7 = 6`
overlap on `{6,7}`, so item 2 *could* agree — it is item 1 that is fatal.)
FDR's `:[deadlock free]` assertion therefore *fails*; we prove the dual,
`HasDeadlock`, and derive `¬ DeadlockFree`.

**Modelling reductions (documented).**  The maths — the price functions `pval`,
`mval` — is kept *exactly* as in the source (`%`, `*`, `+`).  Only the finite
domains are reduced:

- **Items.**  `Customer` bargains over the two-item internal choice
  `Item = {1, 2}` (item 1 is the no-agreement item; item 2 is retained so the
  internal choice is genuine).  Prices/items are carried as plain `ℕ` on the
  value channels.
- **Stock.**  `X0 = {1,2,3,4}` (as a decidable `ℕ → Bool` predicate), in the
  spirit of the source's `Merchant({1,2,3,4})`; item 1 ∈ `X0`, so the merchant
  offers neither a matching `buy.1.y` nor `outofstock.1`.
- **Money.**  `Y0 = 30` (any `Y0 ≥ pval x` behaves identically, as
  `min(Y0, pval x) = pval x`).

The deadlock is reached in a **single** silent step (the customer's item-1
internal choice), so no unfolding of the `Customer`/`Merchant` recursions is
needed for the witness.

## §1. Imports

```agda
{-# OPTIONS --guardedness #-}

module CSP.Examples.UCS.Ch3.Bargaining where

open import Level using (lift) renaming (zero to lzero)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; _+_; _*_; _∸_; _≟_; _≤?_; _≤_; z≤n; s≤s) renaming (_⊓_ to _⊓ℕ_)
open import Data.Nat using (_%_)
open import Data.Bool using (Bool; true; false; _∧_; not)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Process_Trees
open PTree
```

## §2. The event type and its decidable equality

Two value-carrying channels: `buy` carries the *(item, price)* pair the two
parties are negotiating, `outofstock` carries just the *item*.  With two
constructors the hand-rolled decider is two diagonal clauses plus the two
off-diagonal `no`s.

```agda
data BEv : Set → Set where
  buy        : BEv (ℕ × ℕ)      -- buy.item.price
  outofstock : BEv ℕ            -- outofstock.item

BEv-≟ : (x y : AnyTypes BEv) → Dec (x ≡ y)
BEv-≟ (_ , buy)        (_ , buy)        = yes refl
BEv-≟ (_ , outofstock) (_ , outofstock) = yes refl
BEv-≟ (_ , buy)        (_ , outofstock) = no (λ ())
BEv-≟ (_ , outofstock) (_ , buy)        = no (λ ())

open import CSP.Operators BEv-≟
open EventSet
```

## §3. The price functions

Taken verbatim from the source: the customer's maximum `pval` and the
merchant's minimum `mval`.  These are ordinary (non-corecursive) `ℕ → ℕ`
functions, so they reduce by computation (`pval 1 = 0`, `mval 1 = 1`).

```agda
pval mval : ℕ → ℕ
pval x = (7 * x + 1) % 8          -- customer max price
mval x = (5 * x + 3) % 7          -- merchant min price
```

## §4. The processes

`BProc` is the process type; all offers are value-guarded `react` nodes.

```agda
BProc : Set₁
BProc = PTree BEv (ExtI BEv) (⊤poly {lzero})
```

### §4.1 `Customer`, `custBody`, `Merchant`

Following the Collatz (UCS ch. 2) idiom, the corecursive `Customer`/`Merchant`
loops are written as **inlined `react` copatterns** rather than through the
`⟶`/`□`/`⊓` operators: the corecursive calls must sit *directly* under `just`
in an offer map for the guardedness checker to accept them (routing them
through the operators makes them function arguments, which the checker
rejects — exactly as for `Aω`/`Pd` in Collatz).

`Customer Y` is the **internal choice** over the two items: its τ-part is
precisely the binary `⊓`/`br2` shape (`fin` tag `0` = item 1, tag `1` = item
2), and its visible-offer part is empty — so `Customer Y ─[τ]─► custBody 1 Y`
is the item-1 branch of the choice.

`custBody x Y` is the per-item body `buy.x?y:{0..min(Y,pval x)} → Customer(Y−y)
□ outofstock.x → Customer Y`, inlined as one stable (τ-free) offer map: it
offers `buy.(x, y)` for every price `y ≤ min(Y, pval x)`, and `outofstock.x`.

`Merchant X` offers `buy.(x, y)` for `x ∈ X` and `mval x ≤ y ≤ 10`, and
`outofstock.x` for `x ∉ X`.  It is **stock-depleting**, faithful to the source's
`Merchant(diff(X,{x}))`: after selling item `x` it re-enters
`Merchant (remove x X)` — item `x` is *removed* from stock — whereas after an
`outofstock.x` it re-enters with the unchanged `Merchant X`.  `remove x X` is the
pointwise update of the decidable membership predicate `X : ℕ → Bool` that turns
the `x`-slot off.

```agda
remove : ℕ → (ℕ → Bool) → (ℕ → Bool)
remove x X = λ i → X i ∧ not (does (i ≟ x))

Customer : ℕ → BProc
custBody : ℕ → ℕ → BProc
Merchant : (ℕ → Bool) → BProc

force (Customer Y) = react ∅v
  (λ where
     (_ , fin) x → case x of λ where
         (lift fzero)        → just (custBody 1 Y)
         (lift (fsuc fzero)) → just (custBody 2 Y)
         _                   → nothing
     (_ , base _)   _ → nothing
     (_ , pair _ _) _ → nothing)

force (custBody x Y) = react
  (λ where
     (_ , buy) (i , y) → case i ≟ x of λ where
         (yes _) → case y ≤? (Y ⊓ℕ pval x) of λ where
             (yes _) → just (Customer (Y ∸ y))
             (no  _) → nothing
         (no  _) → nothing
     (_ , outofstock) i → case i ≟ x of λ where
         (yes _) → just (Customer Y)
         (no  _) → nothing)
  ∅t

force (Merchant X) = react
  (λ where
     (_ , buy) (i , y) → case X i of λ where
         false → nothing
         true  → case mval i ≤? y of λ where
             (no  _) → nothing
             (yes _) → case y ≤? 10 of λ where
                 (no  _) → nothing
                 (yes _) → just (Merchant (remove i X))
     (_ , outofstock) i → case X i of λ where
         true  → nothing
         false → just (Merchant X))
  ∅t
```

### §4.2 The reduced domain and the full-synchronisation set

`X0 = {1,2,3,4}`, `Y0 = 30`, and `SyncSet` is the total event set `{| buy,
outofstock |}` (every event at every value is a member — `mem` is the
inhabited `⊤poly`, decided by `yes tt`), so `Par⊤ SyncSet` is *full*
synchronisation.

```agda
X0 : ℕ → Bool
X0 i = does (1 ≤? i) ∧ does (i ≤? 4)

Y0 : ℕ
Y0 = 30

SyncSet : EventSet
SyncSet .mem at x = ⊤poly {lzero}
SyncSet .dec at x = yes tt
```

## §5. Verification machinery

```agda
open import Semantics.LTS      {E = BEv} {I = ExtI BEv}
open import Semantics.Deadlock {E = BEv} {I = ExtI BEv}
  using ( IsStuck; HasDeadlock; DeadlockFree
        ; _⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; hasDeadlock⇒¬deadlockFree )
open import CSP.Laws.Traces.TraceLawsParallel BEv-≟
  using (Par-τ-L; Par-sync)
open import CSP.Laws.Traces.TraceLawsParallelElim BEv-≟
  using (Par-ev-elim; evSync; evL; evR; evBoth; ev√; Par-τ-elim; τL; τR)
```

### §5.1 Neither operand has a τ

`custBody x Y` and `Merchant X` are stable `react` nodes (τ-part `∅t`), so
they have no τ-transition.

```agda
custBody-no-τ : ∀ {x Y t′} → custBody x Y ─[ τ ]─► t′ → ⊥
custBody-no-τ (sSil eq)      = case eq of λ ()
custBody-no-τ (sTau refl br) = case br of λ ()

merchant-no-τ : ∀ {X t′} → Merchant X ─[ τ ]─► t′ → ⊥
merchant-no-τ (sSil eq)      = case eq of λ ()
merchant-no-τ (sTau refl br) = case br of λ ()
```

### §5.2 The item-1 internal choice, the deadlocked state, and the reach

`Customer Y0 ─[τ]─► custBody 1 Y0` is the left (`fin` tag `0`) branch of the
internal choice — a single silent step.  The composite `W` after that step is
stuck (§5.3).

```agda
W : BProc
W = Par⊤ SyncSet (custBody 1 Y0) (Merchant X0)

cust-item1-τ : Customer Y0 ─[ τ ]─► custBody 1 Y0
cust-item1-τ = sTau {i = _ , fin {n = 2}} {a = lift fzero} refl refl

reach : Par⊤ SyncSet (Customer Y0) (Merchant X0) ⟹∖√⟨ [] ⟩ W
reach = ∖√-τ (Par-τ-L SyncSet (λ _ _ → tt) (Customer Y0) (Merchant X0) cust-item1-τ)
             ∖√-refl
```

### §5.3 `W` is stuck (item 1 has no agreement)

Every visible step of `W`, inverted by `Par-ev-elim`, is a solo/both move
outside `SyncSet` (impossible — `SyncSet` is total, `¬m tt` is absurd), a joint
`√` (impossible — `custBody 1 Y0` is not at `ret`), or a synchronisation
(`evSync`) which would require the customer and merchant to offer the *same*
`buy`/`outofstock` event — refuted by `noAgree`.  A τ-step, inverted by
`Par-τ-elim`, would be an operand τ — refuted by §5.1.

`noAgree` is the heart: a shared step of `custBody 1 Y0` and `Merchant X0` on
one event is impossible.

- `buy.(i, y)`: the customer offers it only for `i = 1` and `y ≤ min(Y0, pval
  1) = 0`, i.e. `y = 0`; but the merchant offers `buy.(1, 0)` only if `mval 1 =
  1 ≤ 0` — false, so its offer map is `nothing`.
- `outofstock.i`: the customer offers it only for `i = 1`; but item 1 ∈ `X0`,
  so the merchant's `outofstock.1` offer (guarded by `1 ∉ X0`) is `nothing`.

```agda
noAgree : ∀ {X} {e : BEv X} {a : X} {P′ Q′}
        → custBody 1 Y0 ─[ ev (evl (evLabel X e a)) ]─► P′
        → Merchant X0   ─[ ev (evl (evLabel X e a)) ]─► Q′
        → ⊥
noAgree (sVis {at = _ , buy} {a = i , y} refl br) (sVis {at = _ , buy} refl brM)
  with i ≟ 1
... | no  _ = case br of λ ()
... | yes refl with y ≤? (Y0 ⊓ℕ pval 1)
...   | no  _   = case br of λ ()
...   | yes z≤n = case brM of λ ()
noAgree (sVis {at = _ , outofstock} {a = i} refl br) (sVis {at = _ , outofstock} refl brM)
  with i ≟ 1
... | no  _    = case br of λ ()
... | yes refl = case brM of λ ()

stuck : IsStuck W
stuck {l = ev _} step with Par-ev-elim SyncSet (λ _ _ → tt) (custBody 1 Y0) (Merchant X0) step
... | evL ¬m _              = ¬m tt
... | evR ¬m _              = ¬m tt
... | evBoth ¬m _ _         = ¬m tt
... | ev√ fp _              = case fp of λ ()
... | evSync _ cbStep mStep = noAgree cbStep mStep
stuck {l = τ} step with Par-τ-elim SyncSet (λ _ _ → tt) (custBody 1 Y0) (Merchant X0) step
... | τL _ pτ _ = custBody-no-τ pτ
... | τR _ qτ _ = merchant-no-τ qτ
```

### §5.4 The deadlock theorem

```agda
bargaining-deadlocks : HasDeadlock (Par⊤ SyncSet (Customer Y0) (Merchant X0))
bargaining-deadlocks = [] , W , reach , stuck

¬barg-deadlockFree : ¬ DeadlockFree (Par⊤ SyncSet (Customer Y0) (Merchant X0))
¬barg-deadlockFree = hasDeadlock⇒¬deadlockFree bargaining-deadlocks
```

The full-synchronisation `Customer(Y0) [| {| buy, outofstock |} |] Merchant(X0)
:[deadlock free]` assertion therefore fails, exactly as FDR reports: item 1's
buyer/seller price windows are disjoint, so after the customer commits to it
the two parties can neither agree a price nor fall back on `outofstock`.

## §6. Trace refinement: at most one `buy` (`Buy(2) [T= sys`)

`sys = Customer(Y0) [| {| buy, outofstock |} |] Merchant(X0)`.  Beyond the
deadlock witness we record a *trace-refinement* (safety) property of `sys` that
is characteristic of the **stock-depleting** merchant.

**What the depleting merchant does.**  Every visible event of `sys` must
synchronise (the set is total), so both operands must offer it.  On the reduced
domain:

- **Item 1** never agrees on `buy` (`pval 1 = 0 < 1 = mval 1`, independent of
  stock) and its `outofstock.1` is always refused (`1 ∈ X0`, and `1` is never
  depleted because no `buy.1` ever fires) — so item 1 contributes *no* visible
  event ever (this is the deadlock of §5).
- **Item 2** agrees on `buy.(2, y)` for `y ∈ {6, 7}` *while `2 ∈ stock`*.  But a
  successful `buy.2` re-enters `Merchant (remove 2 X0)`, so `2 ∉ stock`
  thereafter: `buy.2` is then refused, and `outofstock.2` *becomes enabled* and
  synchronises (the customer always offers `outofstock` for its chosen item).
  So item 2 is bought **at most once**, after which only `outofstock.2` events
  remain — *unboundedly many* of them, since
  `custBody 2 Y ─outofstock.2─► Customer Y` and `outofstock` leaves the stock
  unchanged.

Hence every trace of `sys` contains **at most one `buy`**, followed by any
number of `outofstock`s.  This is exactly refined by `Buy 2` — the process
allowing up to two `buy`s and, at every level, arbitrarily many `outofstock`s:

```text
Buy(0)   =                            outofstock -> Buy(0)
Buy(k+1) = (buy -> Buy(k))         [] outofstock -> Buy(k+1)
assert Buy(2) [T= sys              -- traces sys ⊆ traces (Buy 2)
```

We prove `Buy(2) [T= sys` by a **weak simulation** of `sys` by `Buy 2`
(`WSimFromRel` / `wsim→⊑T`), tracking the *remaining allowed buys* and whether
item 2 is still in stock.  (Stock depletion, not money, is what bounds the buys,
so no budget invariant is needed here.)

**The source's `NEvs(10) [T= sys` (bounded *total* events) is FALSE — and we
prove it so (`nevs-fails`, §6.6).**  In a hypothetical *non-depleting* merchant
the stock never changes, `outofstock.2` never synchronises, and `sys` could only
perform `buy.2` events — at most `⌊30 / 6⌋ = 5`, hence `≤ 10` total events.  With
the **faithful** depleting merchant, `outofstock.2` synchronises *after*
depletion and loops forever, so `sys` has traces such as
`⟨buy.(2,6), outofstock.2, outofstock.2, …⟩` of *unbounded* length.  Therefore
`NEvs(10) [T= sys` — indeed `NEvs(n) [T= sys` for **any** finite `n` — is
*false*: depletion **enables** `outofstock`, it does not merely remove events.
Rather than drop this failing assertion, we record it as a machine-checked
**negation** `nevs-fails : ¬ (NEvs 10 ⊑T sys)` (§6.6) — matching how the module
already proves its other failing FDR asserts (`¬barg-deadlockFree`) as
negations.  The positive spec the depleting merchant *does* satisfy is
`buy-spec : Buy(2) [T= sys` (bounded *buys*, unbounded *outofstock*).

```agda
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (zero; suc)
open import Data.Nat.Properties using (≤-trans; m⊓n≤n; n≤0⇒n≡0; 1+n≰n)

open import Semantics.WeakBisim {E = BEv} {I = ExtI BEv}
  using (_═[_]═►_; wev; wτ; _─[τ*]─►_; τ*-refl)
open import Semantics.Failures  {E = BEv} {I = ExtI BEv}
  using (_⊑T_; traces; _⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import Semantics.WeakSim   {E = BEv} {I = ExtI BEv}
  using (WSim; wsim→⊑T)
open import Semantics.BisimFromRel {E = BEv} {I = ExtI BEv}
```

### §6.1 The specification process `Buy` and `sys`

`Buy k` allows up to `k` visible `buy` events; at every level it also offers
`outofstock` and stays at the *same* level (so `outofstock` is unbounded), while
each `buy` decrements the level.  `Buy 0` refuses `buy` and only loops on
`outofstock`.  We write it as an inlined `react` copattern (guardedness: the
corecursive `Buy` sits directly under `just`), matching the `Customer`/`Merchant`
idiom.

```agda
Buy : ℕ → BProc
force (Buy zero) = react
  (λ where
     (_ , buy)        _ → nothing
     (_ , outofstock) _ → just (Buy zero))
  ∅t
force (Buy (suc k)) = react
  (λ where
     (_ , buy)        _ → just (Buy k)
     (_ , outofstock) _ → just (Buy (suc k)))
  ∅t

sys : BProc
sys = Par⊤ SyncSet (Customer Y0) (Merchant X0)
```

`Buy (suc k)` fires any `buy.(i, y)` to `Buy k`, and any `outofstock.i` back to
`Buy (suc k)`:

```agda
Buy-buy : ∀ {k} {i y : ℕ}
        → Buy (suc k) ─[ ev (evl (evLabel (ℕ × ℕ) buy (i , y))) ]─► Buy k
Buy-buy = sVis refl refl

Buy-oos : ∀ {k} {i : ℕ}
        → Buy (suc k) ─[ ev (evl (evLabel ℕ outofstock i)) ]─► Buy (suc k)
Buy-oos = sVis refl refl
```

### §6.2 Operand step facts

`Customer Y` has no *visible* step (its offer map is empty — `∅v`); its only
transitions are the internal-choice τ's to `custBody 1 Y` / `custBody 2 Y`.

```agda
customer-no-ev : ∀ {Y} {l : Event√ (⊤poly {lzero})} {t′}
               → Customer Y ─[ ev l ]─► t′ → ⊥
customer-no-ev (sRet eq)      = case eq of λ ()
customer-no-ev (sVis refl br) = case br of λ ()

customer-τ-inv : ∀ {Y t′} → Customer Y ─[ τ ]─► t′
               → (t′ ≡ custBody 1 Y) ⊎ (t′ ≡ custBody 2 Y)
customer-τ-inv (sSil eq) = case eq of λ ()
customer-τ-inv (sTau {i = _ , fin} {a = lift fzero}               refl br) = inj₁ (sym (just-injective br))
customer-τ-inv (sTau {i = _ , fin} {a = lift (fsuc fzero)}        refl br) = inj₂ (sym (just-injective br))
customer-τ-inv (sTau {i = _ , fin} {a = lift (fsuc (fsuc _))}     refl br) = case br of λ ()
customer-τ-inv (sTau {i = _ , base _}   refl br) = case br of λ ()
customer-τ-inv (sTau {i = _ , pair _ _} refl br) = case br of λ ()
```

Item 1 admits no synchronisation with *any* stock `X` in which item 1 is
present (`X 1 ≡ true`): `buy.(1, y)` needs the customer's `y ≤ Y ⊓ pval 1 = 0`
yet the merchant's `mval 1 = 1 ≤ y` (impossible, *independent of stock*);
`outofstock.1` is blocked by `1 ∈ X`.  Both reachable stocks — `X0` and the
depleted `remove 2 X0` — keep item 1 (`X0 1 = (remove 2 X0) 1 = true`), so this
covers every reachable item-1 state.

```agda
noAgree1 : ∀ {Y X} → X 1 ≡ true
         → ∀ {Z} {e : BEv Z} {a : Z} {P′ Q′}
         → custBody 1 Y ─[ ev (evl (evLabel Z e a)) ]─► P′
         → Merchant X   ─[ ev (evl (evLabel Z e a)) ]─► Q′
         → ⊥
noAgree1 {Y} x1 (sVis {at = _ , buy} {a = i , y} refl br) (sVis {at = _ , buy} refl brM)
  with i ≟ 1
... | no  _ = case br of λ ()
... | yes refl with y ≤? (Y ⊓ℕ pval 1)
...   | no  _   = case br of λ ()
...   | yes yle rewrite n≤0⇒n≡0 (≤-trans yle (m⊓n≤n Y (pval 1))) | x1 = case brM of λ ()
noAgree1 x1 (sVis {at = _ , outofstock} {a = i} refl br) (sVis {at = _ , outofstock} refl brM)
  with i ≟ 1
... | no  _    = case br of λ ()
... | yes refl rewrite x1 = case brM of λ ()
```

### §6.3 The simulation relation

Six reachable `sys` shapes, split by whether item 2 is still in stock.  While
`2 ∈ stock` (`Merchant X0`) a `buy.2` is still possible, so these relate to
`Buy 2`; once item 2 is sold out (`Merchant (remove 2 X0)`) only `outofstock`
remains, so those relate to `Buy 1` (which still allows the unbounded
`outofstock` self-loop).  No money/budget invariant is needed — depletion, not
money, bounds the buys.

```agda
data Rel : BProc → BProc → Set₁ where
  rS₂  : ∀ {Y} → Rel (Par⊤ SyncSet (Customer Y)   (Merchant X0))            (Buy 2)
  rC1₂ : ∀ {Y} → Rel (Par⊤ SyncSet (custBody 1 Y) (Merchant X0))            (Buy 2)
  rC2₂ : ∀ {Y} → Rel (Par⊤ SyncSet (custBody 2 Y) (Merchant X0))            (Buy 2)
  rS₁  : ∀ {Y} → Rel (Par⊤ SyncSet (Customer Y)   (Merchant (remove 2 X0))) (Buy 1)
  rC1₁ : ∀ {Y} → Rel (Par⊤ SyncSet (custBody 1 Y) (Merchant (remove 2 X0))) (Buy 1)
  rC2₁ : ∀ {Y} → Rel (Par⊤ SyncSet (custBody 2 Y) (Merchant (remove 2 X0))) (Buy 1)
```

### §6.4 The weak simulation `sys ↝ Buy 2`

Two item-2 synchronisation lemmas, one per stock:

- **`cb2X0`** (item 2 still stocked): the joint step is `buy.(2, y)` with
  `6 ≤ y ≤ 10`, landing in `Customer (Y ∸ y) ‖ Merchant (remove 2 X0)` — the
  *depleted* state — matched by `Buy 2 ─buy─► Buy 1`.  The `outofstock.2` offer
  is refused (`2 ∈ X0`).
- **`cb2rm`** (item 2 sold out): `buy.2` is refused (`2 ∉ remove 2 X0`); the
  joint step is `outofstock.2`, back to `Customer Y ‖ Merchant (remove 2 X0)`,
  matched by `Buy 1 ─outofstock─► Buy 1` (the self-loop).

```agda
cb2X0 : ∀ {Y} {X} {e : BEv X} {a : X} {P′ Q′}
      → custBody 2 Y ─[ ev (evl (evLabel X e a)) ]─► P′
      → Merchant X0  ─[ ev (evl (evLabel X e a)) ]─► Q′
      → Σ[ q′ ∈ BProc ] ((Buy 2 ═[ ev (evl (evLabel X e a)) ]═► q′)
                         × Rel (Par⊤ SyncSet P′ Q′) q′)
cb2X0 {Y} (sVis {at = _ , buy} {a = i , y} refl br) (sVis {at = _ , buy} refl brM)
  with i ≟ 2
... | no  _ = case br of λ ()
... | yes refl with y ≤? (Y ⊓ℕ pval 2)
...   | no  _ = case br of λ ()
...   | yes _ with mval 2 ≤? y
...     | no  _ = case brM of λ ()
...     | yes _ with y ≤? 10
...       | no  _ = case brM of λ ()
...       | yes _ with just-injective br | just-injective brM
...         | refl | refl = Buy 1 , wev τ*-refl Buy-buy τ*-refl , rS₁
cb2X0 (sVis {at = _ , outofstock} {a = i} refl br) (sVis {at = _ , outofstock} refl brM)
  with i ≟ 2
... | no  _    = case br of λ ()
... | yes refl = case brM of λ ()

cb2rm : ∀ {Y} {X} {e : BEv X} {a : X} {P′ Q′}
      → custBody 2 Y           ─[ ev (evl (evLabel X e a)) ]─► P′
      → Merchant (remove 2 X0) ─[ ev (evl (evLabel X e a)) ]─► Q′
      → Σ[ q′ ∈ BProc ] ((Buy 1 ═[ ev (evl (evLabel X e a)) ]═► q′)
                         × Rel (Par⊤ SyncSet P′ Q′) q′)
cb2rm (sVis {at = _ , buy} {a = i , y} refl br) (sVis {at = _ , buy} refl brM)
  with i ≟ 2
... | no  _    = case br of λ ()
... | yes refl = case brM of λ ()
cb2rm (sVis {at = _ , outofstock} {a = i} refl br) (sVis {at = _ , outofstock} refl brM)
  with i ≟ 2
... | no  _    = case br of λ ()
... | yes refl with just-injective br | just-injective brM
...   | refl | refl = Buy 1 , wev τ*-refl Buy-oos τ*-refl , rS₁

Rel-fwd-ev : ∀ {p q} {l : Event√ (⊤poly {lzero})} {p′}
           → Rel p q → p ─[ ev l ]─► p′
           → Σ[ q′ ∈ BProc ] ((q ═[ ev l ]═► q′) × Rel p′ q′)
Rel-fwd-ev (rS₂ {Y}) step with Par-ev-elim SyncSet (λ _ _ → tt) (Customer Y) (Merchant X0) step
... | evL ¬m _         = ⊥-elim (¬m tt)
... | evR ¬m _         = ⊥-elim (¬m tt)
... | evBoth ¬m _ _    = ⊥-elim (¬m tt)
... | ev√ fp _         = case fp of λ ()
... | evSync _ cStep _ = ⊥-elim (customer-no-ev cStep)
Rel-fwd-ev (rC1₂ {Y}) step with Par-ev-elim SyncSet (λ _ _ → tt) (custBody 1 Y) (Merchant X0) step
... | evL ¬m _              = ⊥-elim (¬m tt)
... | evR ¬m _              = ⊥-elim (¬m tt)
... | evBoth ¬m _ _         = ⊥-elim (¬m tt)
... | ev√ fp _              = case fp of λ ()
... | evSync _ cbStep mStep = ⊥-elim (noAgree1 refl cbStep mStep)
Rel-fwd-ev (rC2₂ {Y}) step with Par-ev-elim SyncSet (λ _ _ → tt) (custBody 2 Y) (Merchant X0) step
... | evL ¬m _              = ⊥-elim (¬m tt)
... | evR ¬m _              = ⊥-elim (¬m tt)
... | evBoth ¬m _ _         = ⊥-elim (¬m tt)
... | ev√ fp _              = case fp of λ ()
... | evSync _ cbStep mStep = cb2X0 cbStep mStep
Rel-fwd-ev (rS₁ {Y}) step with Par-ev-elim SyncSet (λ _ _ → tt) (Customer Y) (Merchant (remove 2 X0)) step
... | evL ¬m _         = ⊥-elim (¬m tt)
... | evR ¬m _         = ⊥-elim (¬m tt)
... | evBoth ¬m _ _    = ⊥-elim (¬m tt)
... | ev√ fp _         = case fp of λ ()
... | evSync _ cStep _ = ⊥-elim (customer-no-ev cStep)
Rel-fwd-ev (rC1₁ {Y}) step with Par-ev-elim SyncSet (λ _ _ → tt) (custBody 1 Y) (Merchant (remove 2 X0)) step
... | evL ¬m _              = ⊥-elim (¬m tt)
... | evR ¬m _              = ⊥-elim (¬m tt)
... | evBoth ¬m _ _         = ⊥-elim (¬m tt)
... | ev√ fp _              = case fp of λ ()
... | evSync _ cbStep mStep = ⊥-elim (noAgree1 refl cbStep mStep)
Rel-fwd-ev (rC2₁ {Y}) step with Par-ev-elim SyncSet (λ _ _ → tt) (custBody 2 Y) (Merchant (remove 2 X0)) step
... | evL ¬m _              = ⊥-elim (¬m tt)
... | evR ¬m _              = ⊥-elim (¬m tt)
... | evBoth ¬m _ _         = ⊥-elim (¬m tt)
... | ev√ fp _              = case fp of λ ()
... | evSync _ cbStep mStep = cb2rm cbStep mStep

Rel-fwd-τ : ∀ {p q} {p′}
          → Rel p q → p ─[ τ ]─► p′
          → Σ[ q′ ∈ BProc ] ((q ═[ τ ]═► q′) × Rel p′ q′)
Rel-fwd-τ (rS₂ {Y}) step with Par-τ-elim SyncSet (λ _ _ → tt) (Customer Y) (Merchant X0) step
... | τL _ cτ refl with customer-τ-inv cτ
...   | inj₁ refl = Buy 2 , wτ τ*-refl , rC1₂
...   | inj₂ refl = Buy 2 , wτ τ*-refl , rC2₂
Rel-fwd-τ rS₂ step | τR _ mτ _ = ⊥-elim (merchant-no-τ mτ)
Rel-fwd-τ (rC1₂ {Y}) step with Par-τ-elim SyncSet (λ _ _ → tt) (custBody 1 Y) (Merchant X0) step
... | τL _ cbτ _ = ⊥-elim (custBody-no-τ cbτ)
... | τR _ mτ  _ = ⊥-elim (merchant-no-τ mτ)
Rel-fwd-τ (rC2₂ {Y}) step with Par-τ-elim SyncSet (λ _ _ → tt) (custBody 2 Y) (Merchant X0) step
... | τL _ cbτ _ = ⊥-elim (custBody-no-τ cbτ)
... | τR _ mτ  _ = ⊥-elim (merchant-no-τ mτ)
Rel-fwd-τ (rS₁ {Y}) step with Par-τ-elim SyncSet (λ _ _ → tt) (Customer Y) (Merchant (remove 2 X0)) step
... | τL _ cτ refl with customer-τ-inv cτ
...   | inj₁ refl = Buy 1 , wτ τ*-refl , rC1₁
...   | inj₂ refl = Buy 1 , wτ τ*-refl , rC2₁
Rel-fwd-τ rS₁ step | τR _ mτ _ = ⊥-elim (merchant-no-τ mτ)
Rel-fwd-τ (rC1₁ {Y}) step with Par-τ-elim SyncSet (λ _ _ → tt) (custBody 1 Y) (Merchant (remove 2 X0)) step
... | τL _ cbτ _ = ⊥-elim (custBody-no-τ cbτ)
... | τR _ mτ  _ = ⊥-elim (merchant-no-τ mτ)
Rel-fwd-τ (rC2₁ {Y}) step with Par-τ-elim SyncSet (λ _ _ → tt) (custBody 2 Y) (Merchant (remove 2 X0)) step
... | τL _ cbτ _ = ⊥-elim (custBody-no-τ cbτ)
... | τR _ mτ  _ = ⊥-elim (merchant-no-τ mτ)

module BR = WSimFromRel Rel Rel-fwd-ev Rel-fwd-τ
```

### §6.5 The refinement theorem

The start state `Customer Y0 ‖ Merchant X0` relates to `Buy 2` (`rS₂`), giving
the refinement directly.

```agda
buy-spec : Buy 2 ⊑T sys
buy-spec = wsim→⊑T (BR.rel→wsim (rS₂ {Y0}))
```

`buy-spec` unfolds to `∀ s → traces sys s → traces (Buy 2) s`, i.e. the FDR
assertion `Buy(2) [T= sys`: every observable behaviour of the depleting
bargaining composite has **at most two `buy` events** (in fact at most one) —
after which item 2 is out of stock and only `outofstock`s remain.  Note `sys`
here is the **two-item** (`Item = {1,2}`) *reduced* model of §4.2, so this is the
reduced-domain `Buy(2)`; it is not claimed equivalent to the source's five-item
`Buy(2)` assertion.

## §6.6 The failing `NEvs(10) [T= sys` assertion, proved false

The source also asserts `NEvs(10) [T= sys` (at most ten *total* events), which
**fails** in FDR.  Faithful to the source, we prove that failure directly as a
machine-checked negation `nevs-fails : ¬ (NEvs 10 ⊑T sys)`, rather than dropping
it.

`NEvs n` offers *every* event and, after any of them, continues as `NEvs (n−1)`;
`NEvs 0 = Stop` (offer map `∅v`), so its traces are exactly the sequences of *at
most `n`* events.  We write it as an inlined `react` copattern (guardedness:
`NEvs n` sits directly under `just`), matching the `Customer`/`Merchant` idiom.

```agda
NEvs : ℕ → BProc
force (NEvs zero)    = react ∅v ∅t
force (NEvs (suc n)) = react (λ _ _ → just (NEvs n)) ∅t
```

**The `NEvs` length bound.**  `NEvs n` has no τ (its τ-part is `∅t`), and each
visible event decrements the index (`NEvs (suc m) ─e─► NEvs m`); `NEvs 0` offers
nothing.  So any trace `s` of `NEvs n` has `length s ≤ n`.

```agda
nevs-no-τ : ∀ {n t′} → NEvs n ─[ τ ]─► t′ → ⊥
nevs-no-τ {zero}  (sSil eq)      = case eq of λ ()
nevs-no-τ {zero}  (sTau refl br) = case br of λ ()
nevs-no-τ {suc n} (sSil eq)      = case eq of λ ()
nevs-no-τ {suc n} (sTau refl br) = case br of λ ()

nevs-ev-inv : ∀ {n} {e : Event√ (⊤poly {lzero})} {t′}
            → NEvs n ─[ ev e ]─► t′
            → Σ[ m ∈ ℕ ] (n ≡ suc m × t′ ≡ NEvs m)
nevs-ev-inv {zero}  (sRet eq)      = case eq of λ ()
nevs-ev-inv {zero}  (sVis refl br) = case br of λ ()
nevs-ev-inv {suc m} (sRet eq)      = case eq of λ ()
nevs-ev-inv {suc m} (sVis refl br) = m , refl , sym (just-injective br)

nevs-bounded : ∀ {n s P′} → NEvs n ⟹⟨ s ⟩ P′ → length s ≤ n
nevs-bounded ⟹-refl        = z≤n
nevs-bounded (⟹-τ  pτ  _)  = ⊥-elim (nevs-no-τ pτ)
nevs-bounded (⟹-ev pev rest) with nevs-ev-inv pev
... | m , refl , refl = s≤s (nevs-bounded rest)
```

**An 11-event `sys` trace.**  After the customer picks item 2 (a τ) the joint
`buy.(2,6)` fires (`6 ∈ {6,7}` and `6 ≤ 10`, so both parties agree) and depletes
item 2; thereafter the customer re-picks item 2 (τ) and the *now-enabled*
`outofstock.2` synchronises, looping forever.  Ten such loops after the single
`buy` give a trace of length **11**.

```agda
evBuy evOOS : Event√ (⊤poly {lzero})
evBuy = evl (evLabel (ℕ × ℕ) buy (2 , 6))
evOOS = evl (evLabel ℕ outofstock 2)

oosTrace : ℕ → List (Event√ (⊤poly {lzero}))
oosTrace zero    = []
oosTrace (suc n) = evOOS ∷ oosTrace n

w : List (Event√ (⊤poly {lzero}))
w = evBuy ∷ oosTrace 10                              -- length w = 11

cust-item2-τ : ∀ {Y} → Customer Y ─[ τ ]─► custBody 2 Y
cust-item2-τ = sTau {i = _ , fin {n = 2}} {a = lift (fsuc fzero)} refl refl

custBody-buy26 : custBody 2 Y0 ─[ ev evBuy ]─► Customer (Y0 ∸ 6)
custBody-buy26 = sVis {at = (ℕ × ℕ) , buy} {a = 2 , 6} refl refl

merch-buy26 : Merchant X0 ─[ ev evBuy ]─► Merchant (remove 2 X0)
merch-buy26 = sVis {at = (ℕ × ℕ) , buy} {a = 2 , 6} refl refl

cb2-oos : ∀ {Y} → custBody 2 Y ─[ ev evOOS ]─► Customer Y
cb2-oos = sVis {at = ℕ , outofstock} {a = 2} refl refl

merch-oos : Merchant (remove 2 X0) ─[ ev evOOS ]─► Merchant (remove 2 X0)
merch-oos = sVis {at = ℕ , outofstock} {a = 2} refl refl

sys-buy : Par⊤ SyncSet (custBody 2 Y0) (Merchant X0)
          ─[ ev evBuy ]─► Par⊤ SyncSet (Customer (Y0 ∸ 6)) (Merchant (remove 2 X0))
sys-buy = Par-sync SyncSet (λ _ _ → tt) (custBody 2 Y0) (Merchant X0) tt custBody-buy26 merch-buy26

sys-oos : ∀ {Y} → Par⊤ SyncSet (custBody 2 Y) (Merchant (remove 2 X0))
                  ─[ ev evOOS ]─► Par⊤ SyncSet (Customer Y) (Merchant (remove 2 X0))
sys-oos {Y} = Par-sync SyncSet (λ _ _ → tt) (custBody 2 Y) (Merchant (remove 2 X0)) tt cb2-oos merch-oos

oos-loop : ∀ {Y} (n : ℕ)
         → Par⊤ SyncSet (Customer Y) (Merchant (remove 2 X0))
           ⟹⟨ oosTrace n ⟩ Par⊤ SyncSet (Customer Y) (Merchant (remove 2 X0))
oos-loop zero        = ⟹-refl
oos-loop {Y} (suc n) =
  ⟹-τ (Par-τ-L SyncSet (λ _ _ → tt) (Customer Y) (Merchant (remove 2 X0)) cust-item2-τ)
       (⟹-ev sys-oos (oos-loop n))

witness-sys : traces sys w
witness-sys = _ ,
  ⟹-τ (Par-τ-L SyncSet (λ _ _ → tt) (Customer Y0) (Merchant X0) cust-item2-τ)
       (⟹-ev sys-buy (oos-loop 10))
```

**The negation.**  If `NEvs 10 ⊑T sys` held, applying it to the 11-event trace
`w` (which `witness-sys` shows is a trace of `sys`) would make `w` a trace of
`NEvs 10`, forcing `length w = 11 ≤ 10` — absurd.

```agda
nevs-fails : ¬ (NEvs 10 ⊑T sys)
nevs-fails nevs with nevs w witness-sys
... | _ , der = 1+n≰n (nevs-bounded der)
```

So `NEvs(10) [T= sys` is machine-checked FALSE, exactly as FDR reports: the
depleting merchant's `outofstock.2` self-loop gives `sys` traces of unbounded
length.
