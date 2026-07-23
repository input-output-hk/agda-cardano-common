# TPC/UCS chapter 1: the up/down family

The first of five example modules porting chapter-1 processes from A.W.
Roscoe's two CSP books — *The Theory and Practice of Concurrency* (TPC) and
*Understanding Concurrent Systems* (UCS) — to this process-tree
formalisation. Both books' machine-readable companion files open with the
same tiny two-event alphabet `{up, down}` and the same handful of processes
built from it:

- `fdr-examples/tpc/chapter01/chapter1.csp` (TPC §1.1)
- `fdr-examples/ucs/chapter01/ucs1.csp` (UCS ch. 1)

```csp
channel up, down

P0 = up -> down -> up -> down -> STOP
P1 = up -> down -> P1
P2 = up -> down -> up -> down -> P2

Pu = up -> Pd
Pd = down -> Pu

COUNT(n) = if n==0 then (up -> COUNT(1))
                   else (up -> COUNT(n+1) [] down -> COUNT(n-1))

LCOUNT(L,n) =  (n<L & up -> LCOUNT(L,n+1))
              [](n>0 & down -> LCOUNT(L,n-1))

AROUND = up -> AROUND [] down -> AROUND
```

This module is **definitions only**: it ports the shapes above onto
`PTree` using the `CSP.Operators` combinators, with no proofs. Later
modules in the `TPC` family will state and prove the refinements the
`.csp` files leave as FDR `assert`s (e.g. `P1 [T= P2`, `P2 [T= Pu`,
`Pu [T= P1`, `P0 [T= P1`, and the `P0`-vs-`P1` non-reverse).

## §1. Imports

The event alphabet needs no return-value payloads beyond `⊤` for `up`/`down`
themselves, but the counter-shaped processes (`COUNT`, `LCOUNT`) carry a
`ℕ`-valued state through `loop`, and the `Pu`/`Pd` pair carries a `Bool`
state recording which of the two mutually-recursive processes we are at.

Note the `_<ᵇ_` clash: both `Data.Bool` and `Data.Nat` export a function
named `_<ᵇ_` (booleans' own less-than, and `ℕ`'s boolean-valued
less-than). We need the `ℕ` one for `LCOUNT`'s guards, so it is dropped
from the `Data.Bool` import and kept only in the `Data.Nat` import.

```agda
{-# OPTIONS --guardedness #-}

module CSP.Examples.TPC.Ch1.UpDown where

open import Level using (lift) renaming (zero to lzero)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as Poly
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; pred; _<ᵇ_)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_; Irrelevant⇒DecEq)
open import Class.DecEq.Instances using (DecEq-ℕ)

open import Process_Trees
```

## §2. The event type

`up` and `down` — two nullary visible events, mirroring the `.csp` files'
`channel up, down`.

```agda
data UD : Set → Set where
  up down : UD ⊤
```

## §3. Decidable equality

```agda
UD-≟ : (x y : AnyTypes UD) → Dec (x ≡ y)
UD-≟ (_ , up)   (_ , up)   = yes refl
UD-≟ (_ , down) (_ , down) = yes refl
UD-≟ (_ , up)   (_ , down) = no λ ()
UD-≟ (_ , down) (_ , up)   = no λ ()

open import CSP.Operators UD-≟
```

`_□_` (needed by `COUNT`/`LCOUNT` below, whose branches return `ℕ`) is
parametrised by a `DecEq` instance on the return type. `DecEq ℕ` is
already available as `DecEq-ℕ` from `Class.DecEq.Instances` (imported
above), so no hand-written instance is required there. The only instance
we must supply ourselves is `DecEq` for the polymorphic unit type
`Poly.⊤ {lzero}`, the return type shared by `P0`, `P1`, `P2`, and `AROUND`
— following the same `Irrelevant⇒DecEq` idiom as
`CSP.Examples.VendingMachine.VendingMachine`.

```agda
instance
  DecEq-⊤poly : DecEq (Poly.⊤ {lzero})
  DecEq-⊤poly = Irrelevant⇒DecEq (λ { (lift _) (lift _) → refl })
```

## §4. Process definitions

```agda
Proc : Set₁
Proc = PTree UD (ExtI UD) (Poly.⊤ {lzero})
```

### §4.1 `P0` — a finite trace then `STOP`

`P0 = up -> down -> up -> down -> STOP` (TPC §1.1 / UCS ch. 1): fires
`up`, `down`, `up`, `down` and then deadlocks.

```agda
P0 : Proc
P0 = up ⟶₀ (down ⟶₀ (up ⟶₀ (down ⟶₀ Stop)))
```

### §4.2 `P1`, `P2` — periodic loops

`P1 = up -> down -> P1` and `P2 = up -> down -> up -> down -> P2` are the
period-2 and period-4 variants of the same idea, each looping forever via
`loop0` (the non-stateful forever-loop combinator).

```agda
P1 : Proc
P1 = loop0 (up ⟶₀ (down ⟶₀ Skip))

P2 : Proc
P2 = loop0 (up ⟶₀ (down ⟶₀ (up ⟶₀ (down ⟶₀ Skip))))
```

### §4.3 `Pu`/`Pd` — the mutually recursive pair

`Pu = up -> Pd` and `Pd = down -> Pu` are mutually recursive in the `.csp`
source. We encode the two-state cycle as a single `Bool`-indexed `loop`
body (`true` = "at `Pu`", `false` = "at `Pd`"), which sidesteps the
project's no-`mutual`-blocks convention while preserving the same
transition structure: `up` from the `true` state leads to the `false`
state, `down` from the `false` state leads back to the `true` state.

```agda
pu-step : Bool → PTree UD (ExtI UD) Bool
pu-step true  = up   ⟶₀ Ret false
pu-step false = down ⟶₀ Ret true

Pu : Proc
Pu = loop pu-step true
```

### §4.4 `COUNT` — the infinite-state counter

`COUNT(n) = if n==0 then (up -> COUNT(1)) else (up -> COUNT(n+1) [] down -> COUNT(n-1))`.
At `0` only `up` is offered (there is nothing to count down from); at any
`suc n` both `up` (increment) and `down` (decrement) are offered via `□`.
As the `.csp` comment notes, this process is genuinely infinite-state.

```agda
count-step : ℕ → PTree UD (ExtI UD) ℕ
count-step zero    = up ⟶₀ Ret 1
count-step (suc n) = (up ⟶₀ Ret (suc (suc n))) □ (down ⟶₀ Ret n)

COUNT : ℕ → Proc
COUNT = loop count-step
```

### §4.5 `LCOUNT` — the counter bounded above by `L`

`LCOUNT(L,n) = (n<L & up -> LCOUNT(L,n+1)) [] (n>0 & down -> LCOUNT(L,n-1))`.
The `.csp` guarded-alternative form `b & a -> P` (available only when `b`
holds, `STOP` otherwise) is realised here with `_◁_▷_` (`P ◁ b ▷ Q = if b
then P else Q`), guarding each side of the `□` by its corresponding
boolean condition against `Stop`.

```agda
lcount-step : ℕ → ℕ → PTree UD (ExtI UD) ℕ
lcount-step L n = ((up   ⟶₀ Ret (suc n))  ◁ n <ᵇ L ▷ Stop)
                □ ((down ⟶₀ Ret (pred n)) ◁ 0 <ᵇ n ▷ Stop)

LCOUNT : ℕ → ℕ → Proc
LCOUNT L = loop (lcount-step L)
```

### §4.6 `AROUND` — `RUN({up,down})`

`AROUND = up -> AROUND [] down -> AROUND`, which the `.csp` file notes is
equivalent to `RUN({up,down})`: forever offering both `up` and `down`.

```agda
AROUND : Proc
AROUND = loop0 ((up ⟶₀ Skip) □ (down ⟶₀ Skip))
```

## §5. Verification

The `.csp` companion files pose the `P0`-vs-`P1` pair as two FDR asserts:

```csp
assert P1 [T= P0
assert P0 [T= P1   -- intended to FAIL
```

The first holds: every trace of the finite `P0` is a prefix of the
alternating `up·down` stream, which `P1` also produces. The second fails:
after `up,down,up,down` the process `P0` is `STOP`, so it cannot extend the
trace with a fifth event, while `P1` loops on forever. We prove the first
via a weak simulation (`Semantics.WeakSim`) and the second as a negation
with the five-event witness trace `⟨up,down,up,down,up⟩`.

```agda
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (case_of_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (sym)

open import Semantics.LTS       {E = UD} {I = ExtI UD} hiding (Diverges)
open import Semantics.WeakBisim {E = UD} {I = ExtI UD}
  using (WSimF; _═[_]═►_; wev; wτ; _─[τ*]─►_; τ*-refl; τ*-step)
open import Semantics.Failures  {E = UD} {I = ExtI UD}
  using (_⊑T_; traces; _⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import Semantics.WeakSim   {E = UD} {I = ExtI UD}
open import CSP.Laws.Traces.TraceLaws UD-≟
  using (⟶-trace-elim; Stop-no-τ; Stop-no-ev; Stop-traces-empty)
open import CSP.Laws.Traces.PrefixInversion UD-≟
  using (Prefix-cont-fires; ⟶₀-no-τ; ⟶₀-ev-inv; sil-inj; sil-no-ev; sil-τ-uniq; divergesSil)
open WSimF
```

### §5.1 The FDR asserts

```agda
-- assert P1 [T= P0   (holds)
P1⊑TP0 : P1 ⊑T P0

-- assert P0 [T= P1   (FAILS, as the books intend)
¬P0⊑TP1 : ¬ (P0 ⊑T P1)
```

### §5.2 Node-level scaffolding

Every state of `P0` is a pure prefix node (or `Stop`), so it is stable (no
τ-steps) and fires exactly one event. The imported `Prefix-cont-fires` /
`⟶₀-ev-inv` (from `CSP.Laws.Traces.PrefixInversion`, the same idiom as
`CSP.Examples.VendingMachine.VendingMachine_LTL_Sat`) pin both the
event and the successor of a prefix step; `⟶₀-no-τ` refutes silent steps.

### §5.3 The reachable states of `P0` and `P1`

`P0` passes through five sequential states; we name the three inner ones
(the first is `P0` itself, the last is `Stop`).

```agda
P0₁ P0₂ P0₃ : Proc
P0₁ = down ⟶₀ (up ⟶₀ (down ⟶₀ Stop))
P0₂ = up ⟶₀ (down ⟶₀ Stop)
P0₃ = down ⟶₀ Stop
```

`P1 = loop0 body` unfolds to `iter-bind (body >>= loop-back) step`, where
`loop-back` re-enters the loop by returning `inj₁`. Stepping through one
iteration visits two proper states — after `up` and after `up·down` — and
the second has a single `sil` re-entry step back to `P1` itself. We spell
the states out as `iter-bind` terms (definitional unfoldings of `P1`'s
successors, checked by the `refl`s in §5.4 below).

```agda
loopK : Poly.⊤ {lzero} → PTree UD (ExtI UD) (Poly.⊤ {lzero} ⊎ Poly.⊤ {lzero})
loopK _ = (up ⟶₀ (down ⟶₀ Skip)) >>= (λ a′ → Ret (inj₁ a′))

P1↑ P1↑↓ : Proc
P1↑  = iter-bind ((down ⟶₀ Skip) >>= (λ a′ → Ret (inj₁ a′))) loopK
P1↑↓ = iter-bind (Skip            >>= (λ a′ → Ret (inj₁ a′))) loopK
```

### §5.4 `P1`'s strong steps

All three steps hold by `refl`: the offer maps of the `iter-bind`/`>>=`
nodes compute, and `P1↑↓`'s `sil` re-entry lands (definitionally) back on
`P1`.

```agda
P1-up : P1 ─[ ev (evl (evLabel ⊤ up tt)) ]─► P1↑
P1-up = sVis {at = ⊤ , up} {a = tt} refl refl

P1↑-down : P1↑ ─[ ev (evl (evLabel ⊤ down tt)) ]─► P1↑↓
P1↑-down = sVis {at = ⊤ , down} {a = tt} refl refl

P1↑↓-τ : P1↑↓ ─[ τ ]─► P1
P1↑↓-τ = sSil refl
```

### §5.5 `assert P1 [T= P0`: a weak simulation of `P0` by `P1`

Each of `P0`'s five states is matched inside `P1`'s loop: start ↦ `P1`;
after `up` ↦ `P1↑`; after `up·down` ↦ `P1` again (the weak answer's
trailing `τ*` absorbs `P1`'s `sil` loop re-entry); after `up·down·up` ↦
`P1↑`; and the final `Stop` ↦ `P1↑↓`, vacuously (a `Stop` state has no
steps to match). The chain is not recursive — `sim₄` down to `sim₀` are
plain definitions, no corecursion needed.

```agda
sim₄ : WSim (Poly.⊤ {lzero}) Stop P1↑↓
sim₄ .fwd .on-ev  stp = ⊥-elim (Stop-no-ev stp)
sim₄ .fwd .on-tau stp = ⊥-elim (Stop-no-τ  stp)

sim₃ : WSim (Poly.⊤ {lzero}) P0₃ P1↑
sim₃ .fwd .on-ev stp with ⟶₀-ev-inv stp
... | _ , refl , refl = P1↑↓ , wev τ*-refl P1↑-down τ*-refl , sim₄
sim₃ .fwd .on-tau stp = ⊥-elim (⟶₀-no-τ stp)

sim₂ : WSim (Poly.⊤ {lzero}) P0₂ P1
sim₂ .fwd .on-ev stp with ⟶₀-ev-inv stp
... | _ , refl , refl = P1↑ , wev τ*-refl P1-up τ*-refl , sim₃
sim₂ .fwd .on-tau stp = ⊥-elim (⟶₀-no-τ stp)

sim₁ : WSim (Poly.⊤ {lzero}) P0₁ P1↑
sim₁ .fwd .on-ev stp with ⟶₀-ev-inv stp
... | _ , refl , refl = P1 , wev τ*-refl P1↑-down (τ*-step P1↑↓-τ τ*-refl) , sim₂
sim₁ .fwd .on-tau stp = ⊥-elim (⟶₀-no-τ stp)

sim₀ : WSim (Poly.⊤ {lzero}) P0 P1
sim₀ .fwd .on-ev stp with ⟶₀-ev-inv stp
... | _ , refl , refl = P1↑ , wev τ*-refl P1-up τ*-refl , sim₁
sim₀ .fwd .on-tau stp = ⊥-elim (⟶₀-no-τ stp)

P1⊑TP0 = wsim→⊑T sim₀
```

### §5.6 `assert P0 [T= P1` fails: the witness trace

`s* = ⟨up,down,up,down,up⟩` is a trace of `P1` (two full loop iterations,
each followed by the silent re-entry, then one more `up`) but not of `P0`
(after four events `P0` is `Stop`, which refuses everything).

```agda
s* : List (Event√ (Poly.⊤ {lzero}))
s* = evl (evLabel ⊤ up tt) ∷ evl (evLabel ⊤ down tt) ∷ evl (evLabel ⊤ up tt)
   ∷ evl (evLabel ⊤ down tt) ∷ evl (evLabel ⊤ up tt) ∷ []

P1-does-s* : traces P1 s*
P1-does-s* = P1↑ ,
  ⟹-ev P1-up (⟹-ev P1↑-down (⟹-τ P1↑↓-τ
  (⟹-ev P1-up (⟹-ev P1↑-down (⟹-τ P1↑↓-τ
  (⟹-ev P1-up ⟹-refl))))))

P0-refuses-s* : ¬ traces P0 s*
P0-refuses-s* tr₀ with ⟶-trace-elim up (λ _ → P0₁) tr₀
... | inj₁ ()
... | inj₂ (_ , _ , refl , tr₁) with ⟶-trace-elim down (λ _ → P0₂) tr₁
...   | inj₁ ()
...   | inj₂ (_ , _ , refl , tr₂) with ⟶-trace-elim up (λ _ → P0₃) tr₂
...     | inj₁ ()
...     | inj₂ (_ , _ , refl , tr₃) with ⟶-trace-elim down (λ _ → Stop) tr₃
...       | inj₁ ()
...       | inj₂ (_ , _ , refl , tr₄) = case Stop-traces-empty tr₄ of λ ()

¬P0⊑TP1 p0⊑p1 = P0-refuses-s* (p0⊑p1 s* P1-does-s*)
```

## §6. Loop equivalences: `P1 ≈DR P2` and `P1 ≈DR Pu`

The remaining chapter-1 asserts about the three loops say they are all
trace-equivalent presentations of the same alternating `up·down` stream:

```csp
assert P1 [T= P2
assert P2 [T= Pu
assert Pu [T= P1
```

We prove something stronger: `P1`, `P2` and `Pu` are pairwise
**divergence-respecting weakly bisimilar** (`≈DR`), which yields the full
failures-divergences equivalence via `drbisim→≈FD` — so all three FDR trace
asserts (and their `[F=`/`[FD=` strengthenings) follow as corollaries.

```agda
open import Data.Product using (proj₁; proj₂)

open import Semantics.DRBisim             {E = UD} {I = ExtI UD}
open import Semantics.DRImpliesFD         {E = UD} {I = ExtI UD} using (drbisim→≈FD)
open import Semantics.FailuresDivergences {E = UD} {I = ExtI UD} using (_≈FD_)
open import Semantics.Failures            {E = UD} {I = ExtI UD} using (traces-respects-≈)
open import Semantics.BisimFromRel        {E = UD} {I = ExtI UD}
```

### §6.1 The statements

```agda
P1≈DRP2 : P1 ≈DR P2
P1≈DRPu : P1 ≈DR Pu

-- discharges FDR asserts: P1 [T= P2, P1 [F= P2, P1 [FD= P2 (and conversely)
P1≈FDP2 : P1 ≈FD P2

-- discharges FDR asserts: P2 [T= Pu, Pu [T= P1
P2⊑TPu : P2 ⊑T Pu
Pu⊑TP1 : Pu ⊑T P1
```

### §6.2 The reachable states of `P2` and `Pu`

Exactly as in §5.3 for `P1`: each loop state is an `iter-bind` term, the
definitional unfolding of the loop's successors (checked by the `refl`s in
§6.3 below). `P2`'s body passes through four proper states before the
silent re-entry; `Pu`'s `Bool`-indexed body re-enters silently after
*every* event (the `Ret false`/`Ret true` state changes), so it has a τ
after `up` (into the `Pd` state) and another after `down` (back to `Pu`).

```agda
loopK₂ : Poly.⊤ {lzero} → PTree UD (ExtI UD) (Poly.⊤ {lzero} ⊎ Poly.⊤ {lzero})
loopK₂ _ = (up ⟶₀ (down ⟶₀ (up ⟶₀ (down ⟶₀ Skip)))) >>= (λ a′ → Ret (inj₁ a′))

P2₁ P2₂ P2₃ P2₄ : Proc
P2₁ = iter-bind ((down ⟶₀ (up ⟶₀ (down ⟶₀ Skip))) >>= (λ a′ → Ret (inj₁ a′))) loopK₂
P2₂ = iter-bind ((up ⟶₀ (down ⟶₀ Skip))            >>= (λ a′ → Ret (inj₁ a′))) loopK₂
P2₃ = iter-bind ((down ⟶₀ Skip)                     >>= (λ a′ → Ret (inj₁ a′))) loopK₂
P2₄ = iter-bind (Skip                                >>= (λ a′ → Ret (inj₁ a′))) loopK₂

puK : Bool → PTree UD (ExtI UD) (Bool ⊎ Poly.⊤ {lzero})
puK b = pu-step b >>= (λ a′ → Ret (inj₁ a′))

Pu↑ Pd Pd↓ : Proc
Pu↑ = iter-bind (Ret false >>= (λ a′ → Ret (inj₁ a′))) puK
Pd  = iter puK false
Pd↓ = iter-bind (Ret true  >>= (λ a′ → Ret (inj₁ a′))) puK
```

### §6.3 Strong steps of `P2` and `Pu`

All hold by `refl`, exactly as in §5.4.

```agda
P2-up : P2 ─[ ev (evl (evLabel ⊤ up tt)) ]─► P2₁
P2-up = sVis {at = ⊤ , up} {a = tt} refl refl

P2₁-down : P2₁ ─[ ev (evl (evLabel ⊤ down tt)) ]─► P2₂
P2₁-down = sVis {at = ⊤ , down} {a = tt} refl refl

P2₂-up : P2₂ ─[ ev (evl (evLabel ⊤ up tt)) ]─► P2₃
P2₂-up = sVis {at = ⊤ , up} {a = tt} refl refl

P2₃-down : P2₃ ─[ ev (evl (evLabel ⊤ down tt)) ]─► P2₄
P2₃-down = sVis {at = ⊤ , down} {a = tt} refl refl

P2₄-τ : P2₄ ─[ τ ]─► P2
P2₄-τ = sSil refl

Pu-up : Pu ─[ ev (evl (evLabel ⊤ up tt)) ]─► Pu↑
Pu-up = sVis {at = ⊤ , up} {a = tt} refl refl

Pu↑-τ : Pu↑ ─[ τ ]─► Pd
Pu↑-τ = sSil refl

Pd-down : Pd ─[ ev (evl (evLabel ⊤ down tt)) ]─► Pd↓
Pd-down = sVis {at = ⊤ , down} {a = tt} refl refl

Pd↓-τ : Pd↓ ─[ τ ]─► Pu
Pd↓-τ = sSil refl
```

### §6.4 Loop-node inversions

Every *stable* state of the three loops has the shape
`iter-bind ((ce ⟶₀ X) >>= inj₁-Ret) K`: a prefix node wrapped by the bind
and iteration continuations. Its offer map fires exactly the prefixed
event (with successor `iter-bind (X >>= inj₁-Ret) K`) and its τ-map is
everywhere `nothing` (the prefix's `∅t`, mapped through `bindT`/`iterT`).
The two lemmas below capture this once, generically in the loop-state type
`A` (`Poly.⊤` for `P1`/`P2`, `Bool` for `Pu`), following the
`Prefix-cont-fires` idiom of §5.2: a `with` on the `UD-≟` decision that the
offer map is stuck on.

```agda
loop-ev-inv : ∀ {A : Set} (ce : UD ⊤) (X : PTree UD (ExtI UD) A)
                (K : A → PTree UD (ExtI UD) (A ⊎ Poly.⊤ {lzero}))
                {l : Event√ (Poly.⊤ {lzero})} {t′ : Proc}
            → iter-bind ((ce ⟶₀ X) >>= (λ a′ → Ret (inj₁ a′))) K ─[ ev l ]─► t′
            → (l ≡ evl (evLabel ⊤ ce tt))
              × (t′ ≡ iter-bind (X >>= (λ a′ → Ret (inj₁ a′))) K)
loop-ev-inv ce X K (sRet eq) = case eq of λ ()
loop-ev-inv ce X K (sVis {at = at} {a = a} refl br) with UD-≟ (⊤ , ce) at
... | yes refl = refl , sym (just-injective br)
... | no ¬eq   = ⊥-elim (case br of λ ())

loop-no-τ : ∀ {A : Set} (ce : UD ⊤) (X : PTree UD (ExtI UD) A)
              (K : A → PTree UD (ExtI UD) (A ⊎ Poly.⊤ {lzero})) {t′ : Proc}
          → iter-bind ((ce ⟶₀ X) >>= (λ a′ → Ret (inj₁ a′))) K ─[ τ ]─► t′ → ⊥
loop-no-τ ce X K (sSil eq)      = case eq of λ ()
loop-no-τ ce X K (sTau refl br) = case br of λ ()
```

The *silent* states (`P1↑↓`, `P2₄`, `Pu↑`, `Pd↓`) force to a `sil` node:
they offer no visible event and take exactly one τ, to the node named by
the `sil` — captured by the imported `sil-inj`/`sil-no-ev`/`sil-τ-uniq`
(and, in §6.5, `divergesSil`) from `CSP.Laws.Traces.PrefixInversion`.

### §6.5 None of the loop states diverges

`Diverges` demands an infinite τ-chain. Each of the eleven loop states is
either stable (its first `Diverges.step` is already refuted by
`loop-no-τ`) or a `sil` state whose single τ lands on a stable state
(chase one step with `divergesSil`, then refute).

```agda
¬div-P1 : Diverges P1 → ⊥
¬div-P1 d = loop-no-τ up (down ⟶₀ Skip) loopK (Diverges.step d)

¬div-P1↑ : Diverges P1↑ → ⊥
¬div-P1↑ d = loop-no-τ down Skip loopK (Diverges.step d)

¬div-P1↑↓ : Diverges P1↑↓ → ⊥
¬div-P1↑↓ d = ¬div-P1 (divergesSil refl d)

¬div-P2 : Diverges P2 → ⊥
¬div-P2 d = loop-no-τ up (down ⟶₀ (up ⟶₀ (down ⟶₀ Skip))) loopK₂ (Diverges.step d)

¬div-P2₁ : Diverges P2₁ → ⊥
¬div-P2₁ d = loop-no-τ down (up ⟶₀ (down ⟶₀ Skip)) loopK₂ (Diverges.step d)

¬div-P2₂ : Diverges P2₂ → ⊥
¬div-P2₂ d = loop-no-τ up (down ⟶₀ Skip) loopK₂ (Diverges.step d)

¬div-P2₃ : Diverges P2₃ → ⊥
¬div-P2₃ d = loop-no-τ down Skip loopK₂ (Diverges.step d)

¬div-P2₄ : Diverges P2₄ → ⊥
¬div-P2₄ d = ¬div-P2 (divergesSil refl d)

¬div-Pu : Diverges Pu → ⊥
¬div-Pu d = loop-no-τ up (Ret false) puK (Diverges.step d)

¬div-Pd : Diverges Pd → ⊥
¬div-Pd d = loop-no-τ down (Ret true) puK (Diverges.step d)

¬div-Pu↑ : Diverges Pu↑ → ⊥
¬div-Pu↑ d = ¬div-Pd (divergesSil refl d)

¬div-Pd↓ : Diverges Pd↓ → ⊥
¬div-Pd↓ d = ¬div-Pu (divergesSil refl d)
```

### §6.6 From a step-matching relation to `≈DR`

The two bisimulations are cyclic, so their `DRbisim` proofs must be
corecursive. Rather than defining a dozen mutually corecursive record
values (one per state pair *and orientation* — `bwd` residuals are
`DRbisim` values with the sides swapped, and wrapping a sibling in
`drbisim-sym` would break guardedness), we factor the corecursion out
*once*: any binary relation on processes whose pairs (i) match each
other's strong steps by weak steps, staying in the relation, and (ii)
contain no divergent process, is contained in `≈DR`. All the real work
then happens in plain, non-corecursive case analyses on the relation; the
coinductive machinery is the shared `DRFromRel` principle imported from
`Semantics.BisimFromRel` in the §6 block above.

### §6.7 `P1 ≈DR P2`

The relation: `P1`'s three states paired with `P2`'s five, following the
two loops around one period of `P2` (= two periods of `P1`). The pair
`r₂′` is the τ-shifted intermediate — after `up·down`, `P1` has silently
re-entered its loop while `P2` is still mid-body — and `r₄` closes the
cycle: from `(P1↑↓ , P2₄)` both re-entry `sil`s fire and we are back at
`(P1 , P2)`.

```agda
data R12 : Proc → Proc → Set₁ where
  r₀  : R12 P1   P2
  r₁  : R12 P1↑  P2₁
  r₂  : R12 P1↑↓ P2₂
  r₂′ : R12 P1   P2₂
  r₃  : R12 P1↑  P2₃
  r₄  : R12 P1↑↓ P2₄

R12-fwd-ev : ∀ {p q} {l : Event√ (Poly.⊤ {lzero})} {p′} → R12 p q → p ─[ ev l ]─► p′
           → Σ[ q′ ∈ Proc ] ((q ═[ ev l ]═► q′) × R12 p′ q′)
R12-fwd-ev r₀  stp with loop-ev-inv up (down ⟶₀ Skip) loopK stp
... | refl , refl = P2₁ , wev τ*-refl P2-up τ*-refl , r₁
R12-fwd-ev r₁  stp with loop-ev-inv down Skip loopK stp
... | refl , refl = P2₂ , wev τ*-refl P2₁-down τ*-refl , r₂
R12-fwd-ev r₂  stp = ⊥-elim (sil-no-ev refl stp)
R12-fwd-ev r₂′ stp with loop-ev-inv up (down ⟶₀ Skip) loopK stp
... | refl , refl = P2₃ , wev τ*-refl P2₂-up τ*-refl , r₃
R12-fwd-ev r₃  stp with loop-ev-inv down Skip loopK stp
... | refl , refl = P2₄ , wev τ*-refl P2₃-down τ*-refl , r₄
R12-fwd-ev r₄  stp = ⊥-elim (sil-no-ev refl stp)

R12-fwd-τ : ∀ {p q p′} → R12 p q → p ─[ τ ]─► p′
          → Σ[ q′ ∈ Proc ] ((q ═[ τ ]═► q′) × R12 p′ q′)
R12-fwd-τ r₀  stp = ⊥-elim (loop-no-τ up (down ⟶₀ Skip) loopK stp)
R12-fwd-τ r₁  stp = ⊥-elim (loop-no-τ down Skip loopK stp)
R12-fwd-τ r₂  stp with sil-τ-uniq refl stp
... | refl = P2₂ , wτ τ*-refl , r₂′
R12-fwd-τ r₂′ stp = ⊥-elim (loop-no-τ up (down ⟶₀ Skip) loopK stp)
R12-fwd-τ r₃  stp = ⊥-elim (loop-no-τ down Skip loopK stp)
R12-fwd-τ r₄  stp with sil-τ-uniq refl stp
... | refl = P2 , wτ (τ*-step P2₄-τ τ*-refl) , r₀

R12-bwd-ev : ∀ {p q} {l : Event√ (Poly.⊤ {lzero})} {q′} → R12 p q → q ─[ ev l ]─► q′
           → Σ[ p′ ∈ Proc ] ((p ═[ ev l ]═► p′) × R12 p′ q′)
R12-bwd-ev r₀  stp with loop-ev-inv up (down ⟶₀ (up ⟶₀ (down ⟶₀ Skip))) loopK₂ stp
... | refl , refl = P1↑ , wev τ*-refl P1-up τ*-refl , r₁
R12-bwd-ev r₁  stp with loop-ev-inv down (up ⟶₀ (down ⟶₀ Skip)) loopK₂ stp
... | refl , refl = P1↑↓ , wev τ*-refl P1↑-down τ*-refl , r₂
R12-bwd-ev r₂  stp with loop-ev-inv up (down ⟶₀ Skip) loopK₂ stp
... | refl , refl = P1↑ , wev (τ*-step P1↑↓-τ τ*-refl) P1-up τ*-refl , r₃
R12-bwd-ev r₂′ stp with loop-ev-inv up (down ⟶₀ Skip) loopK₂ stp
... | refl , refl = P1↑ , wev τ*-refl P1-up τ*-refl , r₃
R12-bwd-ev r₃  stp with loop-ev-inv down Skip loopK₂ stp
... | refl , refl = P1↑↓ , wev τ*-refl P1↑-down τ*-refl , r₄
R12-bwd-ev r₄  stp = ⊥-elim (sil-no-ev refl stp)

R12-bwd-τ : ∀ {p q q′} → R12 p q → q ─[ τ ]─► q′
          → Σ[ p′ ∈ Proc ] ((p ═[ τ ]═► p′) × R12 p′ q′)
R12-bwd-τ r₀  stp = ⊥-elim (loop-no-τ up (down ⟶₀ (up ⟶₀ (down ⟶₀ Skip))) loopK₂ stp)
R12-bwd-τ r₁  stp = ⊥-elim (loop-no-τ down (up ⟶₀ (down ⟶₀ Skip)) loopK₂ stp)
R12-bwd-τ r₂  stp = ⊥-elim (loop-no-τ up (down ⟶₀ Skip) loopK₂ stp)
R12-bwd-τ r₂′ stp = ⊥-elim (loop-no-τ up (down ⟶₀ Skip) loopK₂ stp)
R12-bwd-τ r₃  stp = ⊥-elim (loop-no-τ down Skip loopK₂ stp)
R12-bwd-τ r₄  stp with sil-τ-uniq refl stp
... | refl = P1 , wτ (τ*-step P1↑↓-τ τ*-refl) , r₀

R12-¬divL : ∀ {p q} → R12 p q → Diverges p → ⊥
R12-¬divL r₀  = ¬div-P1
R12-¬divL r₁  = ¬div-P1↑
R12-¬divL r₂  = ¬div-P1↑↓
R12-¬divL r₂′ = ¬div-P1
R12-¬divL r₃  = ¬div-P1↑
R12-¬divL r₄  = ¬div-P1↑↓

R12-¬divR : ∀ {p q} → R12 p q → Diverges q → ⊥
R12-¬divR r₀  = ¬div-P2
R12-¬divR r₁  = ¬div-P2₁
R12-¬divR r₂  = ¬div-P2₂
R12-¬divR r₂′ = ¬div-P2₂
R12-¬divR r₃  = ¬div-P2₃
R12-¬divR r₄  = ¬div-P2₄

module M12 = DRFromRel R12 R12-fwd-ev R12-fwd-τ R12-bwd-ev R12-bwd-τ R12-¬divL R12-¬divR

P1≈DRP2 = M12.rel→dr r₀
```

### §6.8 `P1 ≈DR Pu`

The relation: `(P1 , Pu)`, after `up` `(P1↑ , Pu↑)`, the τ-shift
`(P1↑ , Pd)` once `Pu` has silently moved to its `Pd` state, and after
`down` `(P1↑↓ , Pd↓)` — from which both re-entry τs return to `(P1 , Pu)`.

```agda
data R1u : Proc → Proc → Set₁ where
  c₀  : R1u P1   Pu
  c₁  : R1u P1↑  Pu↑
  c₁′ : R1u P1↑  Pd
  c₂  : R1u P1↑↓ Pd↓

R1u-fwd-ev : ∀ {p q} {l : Event√ (Poly.⊤ {lzero})} {p′} → R1u p q → p ─[ ev l ]─► p′
           → Σ[ q′ ∈ Proc ] ((q ═[ ev l ]═► q′) × R1u p′ q′)
R1u-fwd-ev c₀  stp with loop-ev-inv up (down ⟶₀ Skip) loopK stp
... | refl , refl = Pu↑ , wev τ*-refl Pu-up τ*-refl , c₁
R1u-fwd-ev c₁  stp with loop-ev-inv down Skip loopK stp
... | refl , refl = Pd↓ , wev (τ*-step Pu↑-τ τ*-refl) Pd-down τ*-refl , c₂
R1u-fwd-ev c₁′ stp with loop-ev-inv down Skip loopK stp
... | refl , refl = Pd↓ , wev τ*-refl Pd-down τ*-refl , c₂
R1u-fwd-ev c₂  stp = ⊥-elim (sil-no-ev refl stp)

R1u-fwd-τ : ∀ {p q p′} → R1u p q → p ─[ τ ]─► p′
          → Σ[ q′ ∈ Proc ] ((q ═[ τ ]═► q′) × R1u p′ q′)
R1u-fwd-τ c₀  stp = ⊥-elim (loop-no-τ up (down ⟶₀ Skip) loopK stp)
R1u-fwd-τ c₁  stp = ⊥-elim (loop-no-τ down Skip loopK stp)
R1u-fwd-τ c₁′ stp = ⊥-elim (loop-no-τ down Skip loopK stp)
R1u-fwd-τ c₂  stp with sil-τ-uniq refl stp
... | refl = Pu , wτ (τ*-step Pd↓-τ τ*-refl) , c₀

R1u-bwd-ev : ∀ {p q} {l : Event√ (Poly.⊤ {lzero})} {q′} → R1u p q → q ─[ ev l ]─► q′
           → Σ[ p′ ∈ Proc ] ((p ═[ ev l ]═► p′) × R1u p′ q′)
R1u-bwd-ev c₀  stp with loop-ev-inv up (Ret false) puK stp
... | refl , refl = P1↑ , wev τ*-refl P1-up τ*-refl , c₁
R1u-bwd-ev c₁  stp = ⊥-elim (sil-no-ev refl stp)
R1u-bwd-ev c₁′ stp with loop-ev-inv down (Ret true) puK stp
... | refl , refl = P1↑↓ , wev τ*-refl P1↑-down τ*-refl , c₂
R1u-bwd-ev c₂  stp = ⊥-elim (sil-no-ev refl stp)

R1u-bwd-τ : ∀ {p q q′} → R1u p q → q ─[ τ ]─► q′
          → Σ[ p′ ∈ Proc ] ((p ═[ τ ]═► p′) × R1u p′ q′)
R1u-bwd-τ c₀  stp = ⊥-elim (loop-no-τ up (Ret false) puK stp)
R1u-bwd-τ c₁  stp with sil-τ-uniq refl stp
... | refl = P1↑ , wτ τ*-refl , c₁′
R1u-bwd-τ c₁′ stp = ⊥-elim (loop-no-τ down (Ret true) puK stp)
R1u-bwd-τ c₂  stp with sil-τ-uniq refl stp
... | refl = P1 , wτ (τ*-step P1↑↓-τ τ*-refl) , c₀

R1u-¬divL : ∀ {p q} → R1u p q → Diverges p → ⊥
R1u-¬divL c₀  = ¬div-P1
R1u-¬divL c₁  = ¬div-P1↑
R1u-¬divL c₁′ = ¬div-P1↑
R1u-¬divL c₂  = ¬div-P1↑↓

R1u-¬divR : ∀ {p q} → R1u p q → Diverges q → ⊥
R1u-¬divR c₀  = ¬div-Pu
R1u-¬divR c₁  = ¬div-Pu↑
R1u-¬divR c₁′ = ¬div-Pd
R1u-¬divR c₂  = ¬div-Pd↓

module M1u = DRFromRel R1u R1u-fwd-ev R1u-fwd-τ R1u-bwd-ev R1u-bwd-τ R1u-¬divL R1u-¬divR

P1≈DRPu = M1u.rel→dr c₀
```

### §6.9 The FDR corollaries

`≈DR` is an equivalence (`drbisim-sym`/`drbisim-trans`), so `P2 ≈DR Pu`
comes for free by composing through `P1`; the failures-divergences
equivalence is the `drbisim→≈FD` bridge, and the trace refinements are
extracted with `traces-respects-≈` after weakening `≈DR` to plain weak
bisimilarity.

```agda
P2≈DRPu : P2 ≈DR Pu
P2≈DRPu = drbisim-trans (drbisim-sym P1≈DRP2) P1≈DRPu

P1≈FDP2 = drbisim→≈FD P1≈DRP2

P2⊑TPu s = proj₂ (traces-respects-≈ (drbisim→wbisim P2≈DRPu))

Pu⊑TP1 s = proj₁ (traces-respects-≈ (drbisim→wbisim P1≈DRPu))
```
