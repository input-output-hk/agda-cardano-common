# UCS chapter 3: a full-synchronisation identity

A "UCS" example, porting the little full-synchronisation identity from A.W.
Roscoe's *Understanding Concurrent Systems* (UCS), chapter 3, machine-readable
companion file:

- `fdr-examples/ucs/chapter03/ucs3.csp` (UCS ch. 3)

The `.csp` file builds, over the three-event alphabet `{a,b,c}`, a process
`REPEAT` that repeats *any* single event twice before looping, and asserts that
running one copy of `REPEAT` that is *forced to start with `a`* in lockstep with
a free copy of `REPEAT` (synchronising on the whole alphabet) is nothing more
than the process `AS` that does `a` forever:

```csp
channel a, b, c

AS = a -> AS
REPEAT = [] x : {a,b,c} @ x -> x -> REPEAT
Events = {a,b,c}
aRR = (a -> REPEAT) [| Events |] REPEAT

assert AS   [T= aRR
assert aRR  [T= AS
```

**Why it holds.** Under full synchronisation on `Events = {a,b,c}` every event
must be offered by *both* operands. At the start `a -> REPEAT` offers only `a`,
while `REPEAT` offers `a`, `b`, `c`; the only common event is `a`, so `a` fires
and the two sides swap roles (one becomes free `REPEAT`, the other becomes the
`a -> REPEAT` residue of its first step). From then on exactly one side is a
"committed to `a`" state and the other is free `REPEAT`, so again only `a` is
jointly offered. Hence `aRR` does `a` forever — exactly `AS`. We prove both
trace-refinement directions (`AS [T= aRR` and `aRR [T= AS`), which together give
`AS =T aRR`.

## §1. Imports

```agda
{-# OPTIONS --guardedness #-}

module CSP.Examples.UCS.Ch3.SyncIdentity where

open import Level using (lift) renaming (zero to lzero)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Class.DecEq using (DecEq; Irrelevant⇒DecEq)

open import Process_Trees
open PTree
```

## §2. The event type

`a`, `b`, `c` — three nullary visible events, mirroring the `.csp`
`channel a, b, c`.

```agda
data SEv : Set → Set where
  a b c : SEv (⊤poly {lzero})
```

## §3. Decidable equality

```agda
SEv-≟ : (x y : AnyTypes SEv) → Dec (x ≡ y)
SEv-≟ (_ , a) (_ , a) = yes refl
SEv-≟ (_ , b) (_ , b) = yes refl
SEv-≟ (_ , c) (_ , c) = yes refl
SEv-≟ (_ , a) (_ , b) = no λ ()
SEv-≟ (_ , a) (_ , c) = no λ ()
SEv-≟ (_ , b) (_ , a) = no λ ()
SEv-≟ (_ , b) (_ , c) = no λ ()
SEv-≟ (_ , c) (_ , a) = no λ ()
SEv-≟ (_ , c) (_ , b) = no λ ()

open import CSP.Operators SEv-≟
open EventSet
```

`⊤poly {lzero}` is `Lift ⊤`, propositionally irrelevant, so its `DecEq` is
trivial (the same `Irrelevant⇒DecEq` idiom as the other examples).

```agda
instance
  DecEq-⊤poly : DecEq (⊤poly {lzero})
  DecEq-⊤poly = Irrelevant⇒DecEq (λ { (lift _) (lift _) → refl })
```

## §4. The processes

```agda
DProc : Set₁
DProc = PTree SEv (ExtI SEv) (⊤poly {lzero})
```

### §4.1 The full-synchronisation alphabet `Events = {a,b,c}`

Every `SEv` event lives at the payload type `⊤poly {lzero}`, so *all* events are
members: `Events` is the total event set (its `mem` predicate is always the
inhabited `⊤poly`, decided by `yes tt`).

```agda
Events : EventSet
Events .mem at x = ⊤poly {lzero}
Events .dec at x = yes tt
```

### §4.2 `REPEAT = [] x : {a,b,c} @ x -> x -> REPEAT`

`REPEAT` offers all three events; firing `x` leaves the residue `x -> REPEAT`
(the state that must repeat `x` once more before looping). We write `REPEAT`
and its three residues `REPa`/`REPb`/`REPc` as inlined `react` copatterns —
exactly the technique used for `Aω`/`Pd` in `CSP.Examples.UCS.Ch2.Collatz`:
the corecursive occurrences sit *directly* under `just`/`react`, so the
guardedness checker sees them as productive, and the offer maps compute
definitionally (which makes the step/inversion lemmas below hold by `refl`).
This is the trace-identical presentation of `loop0 (□ x @ x -> x -> REPEAT)`;
the `loop0`-over-`□` form has the same behaviour but its `τ`-stability
inversion would require peeling a stack of `iter`/`bind`/`□` `τ`-elim lemmas.

```agda
REPEAT REPa REPb REPc : DProc
force REPa   = react (λ { (_ , a) _ → just REPEAT ; (_ , b) _ → nothing   ; (_ , c) _ → nothing   }) ∅t
force REPb   = react (λ { (_ , a) _ → nothing     ; (_ , b) _ → just REPEAT ; (_ , c) _ → nothing   }) ∅t
force REPc   = react (λ { (_ , a) _ → nothing     ; (_ , b) _ → nothing    ; (_ , c) _ → just REPEAT }) ∅t
force REPEAT = react (λ { (_ , a) _ → just REPa   ; (_ , b) _ → just REPb  ; (_ , c) _ → just REPc  }) ∅t
```

### §4.3 `aRR = (a -> REPEAT) [| Events |] REPEAT`

```agda
aRR : DProc
aRR = Par⊤ Events (a ⟶₀ REPEAT) REPEAT
```

### §4.4 `AS = a -> AS`

`AS` is the non-terminating single-event loop, built with `loop0` (its silent
loop re-entry `τ` is handled explicitly below).

```agda
AS : DProc
AS = loop0 (a ⟶₀ Skip)

asK : ⊤poly {lzero} → PTree SEv (ExtI SEv) (⊤poly {lzero} ⊎ ⊤poly {lzero})
asK _ = (a ⟶₀ Skip) >>= (λ a′ → Ret (inj₁ a′))

-- the state after `AS` fires `a`: a `sil` node one `τ` away from `AS`
AS↑ : DProc
AS↑ = iter-bind (Skip >>= (λ a′ → Ret (inj₁ a′))) asK
```

## §5. Verification machinery

```agda
open import Semantics.LTS            {E = SEv} {I = ExtI SEv}
open import Semantics.WeakBisim      {E = SEv} {I = ExtI SEv}
  using (_═[_]═►_; wev; wτ; _─[τ*]─►_; τ*-refl; τ*-step)
open import Semantics.Failures       {E = SEv} {I = ExtI SEv}
  using (_⊑T_; traces)
open import Semantics.WeakSim        {E = SEv} {I = ExtI SEv}
  using (WSim; wsim→⊑T)
open import Semantics.BisimFromRel   {E = SEv} {I = ExtI SEv}
open import CSP.Laws.Traces.PrefixInversion SEv-≟
  using (⟶₀-no-τ; ⟶₀-ev-inv; loop-pfx-ev-inv; loop-pfx-no-τ; sil-no-ev; sil-τ-uniq)
open import CSP.Laws.Traces.TraceLawsParallel SEv-≟
  using (Par-sync)
open import CSP.Laws.Traces.TraceLawsParallelElim SEv-≟
  using ( Par-ev-elim; ParevR; evSync; evL; evR; evBoth; ev√
        ; Par-τ-elim; ParτR; τL; τR)
```

The single visible event we ever fire, `a` at the (irrelevant) payload `tt`:

```agda
evA : Event√ (⊤poly {lzero})
evA = evl (evLabel (⊤poly {lzero}) a tt)
```

### §5.1 Operand strong steps

Every reachable operand is a stable `react` node: the prefix `a -> REPEAT`,
`REPEAT`, and the residue `REPa` each fire `a` (nothing else is jointly enabled
in the reachable states), while `AS`/`AS↑` are the loop's two states. All hold
by `refl` (the inlined offer maps and the `loop0` unfolding compute).

```agda
pfx-a : (a ⟶₀ REPEAT) ─[ ev evA ]─► REPEAT
pfx-a = sVis {at = ⊤poly {lzero} , a} {a = tt} refl refl

REPEAT-a : REPEAT ─[ ev evA ]─► REPa
REPEAT-a = sVis {at = ⊤poly {lzero} , a} {a = tt} refl refl

REPa-a : REPa ─[ ev evA ]─► REPEAT
REPa-a = sVis {at = ⊤poly {lzero} , a} {a = tt} refl refl

AS-a : AS ─[ ev evA ]─► AS↑
AS-a = sVis {at = ⊤poly {lzero} , a} {a = tt} refl refl

AS↑-τ : AS↑ ─[ τ ]─► AS
AS↑-τ = sSil refl
```

### §5.2 Operand inversions

`REPa` fires only `a` (its other channels offer `nothing`), and once the event
is pinned to `a`, `REPEAT` can only step to `REPa`. Both `REPEAT` and `REPa`
are stable (their `τ`-part is `∅t`), so neither takes a `τ`.

```agda
repa-ev-inv : ∀ {l t′} → REPa ─[ ev l ]─► t′ → (l ≡ evA) × (t′ ≡ REPEAT)
repa-ev-inv (sRet eq) = case eq of λ ()
repa-ev-inv (sVis {at = _ , a} {a = x} refl br) = refl , sym (just-injective br)
repa-ev-inv (sVis {at = _ , b} {a = x} refl br) = case br of λ ()
repa-ev-inv (sVis {at = _ , c} {a = x} refl br) = case br of λ ()

repeat-a-inv : ∀ {t′} → REPEAT ─[ ev evA ]─► t′ → t′ ≡ REPa
repeat-a-inv (sVis {at = ⊤poly , a} {a = x} refl br) = sym (just-injective br)

repeat-no-τ : ∀ {t′} → REPEAT ─[ τ ]─► t′ → ⊥
repeat-no-τ (sSil eq)      = case eq of λ ()
repeat-no-τ (sTau refl br) = case br of λ ()

repa-no-τ : ∀ {t′} → REPa ─[ τ ]─► t′ → ⊥
repa-no-τ (sSil eq)      = case eq of λ ()
repa-no-τ (sTau refl br) = case br of λ ()
```

### §5.3 The three reachable `aRR` states and their `a`-steps

`aRR` cycles through three states, all firing `a` (via `Par-sync`, since `a`
is in `Events` and both operands offer it):

```text
aRR = (a->REPEAT) ‖ REPEAT   --a-->   REPEAT ‖ REPa   --a-->   REPa ‖ REPEAT   --a-->  REPEAT ‖ REPa ...
```

```agda
T1 T2 : DProc
T1 = Par⊤ Events REPEAT REPa
T2 = Par⊤ Events REPa   REPEAT

S0-a : aRR ─[ ev evA ]─► T1
S0-a = Par-sync Events _ (a ⟶₀ REPEAT) REPEAT tt pfx-a REPEAT-a

T1-a : T1 ─[ ev evA ]─► T2
T1-a = Par-sync Events _ REPEAT REPa tt REPEAT-a REPa-a

T2-a : T2 ─[ ev evA ]─► T1
T2-a = Par-sync Events _ REPa REPEAT tt REPa-a REPEAT-a
```

### §5.4 `AS [T= aRR`: a weak simulation of `aRR` by `AS`

`AS [T= aRR` unfolds to `∀ s → traces aRR s → traces AS s`, so `aRR` is the
*simulated* side. Every reachable `aRR` state is matched by `AS` (which answers
each `a` with its own `a`, absorbing its loop re-entry `τ` in the trailing
`τ*`); none of the `aRR` states takes a `τ`.

```agda
data R1 : DProc → DProc → Set₁ where
  q0 : R1 aRR AS
  q1 : R1 T1  AS
  q2 : R1 T2  AS

R1-fwd-ev : ∀ {p q} {l : Event√ (⊤poly {lzero})} {p′}
          → R1 p q → p ─[ ev l ]─► p′
          → Σ[ q′ ∈ DProc ] ((q ═[ ev l ]═► q′) × R1 p′ q′)
R1-fwd-ev q0 stp with Par-ev-elim Events _ (a ⟶₀ REPEAT) REPEAT stp
... | evL ¬m _      = ⊥-elim (¬m tt)
... | evR ¬m _      = ⊥-elim (¬m tt)
... | evBoth ¬m _ _ = ⊥-elim (¬m tt)
... | ev√ fp _      = case fp of λ ()
... | evSync _ pStep qStep with ⟶₀-ev-inv pStep
...   | x , refl , refl with repeat-a-inv qStep
...     | refl = AS , wev τ*-refl AS-a (τ*-step AS↑-τ τ*-refl) , q1
R1-fwd-ev q1 stp with Par-ev-elim Events _ REPEAT REPa stp
... | evL ¬m _      = ⊥-elim (¬m tt)
... | evR ¬m _      = ⊥-elim (¬m tt)
... | evBoth ¬m _ _ = ⊥-elim (¬m tt)
... | ev√ fp _      = case fp of λ ()
... | evSync _ pStep qStep with repa-ev-inv qStep
...   | refl , refl with repeat-a-inv pStep
...     | refl = AS , wev τ*-refl AS-a (τ*-step AS↑-τ τ*-refl) , q2
R1-fwd-ev q2 stp with Par-ev-elim Events _ REPa REPEAT stp
... | evL ¬m _      = ⊥-elim (¬m tt)
... | evR ¬m _      = ⊥-elim (¬m tt)
... | evBoth ¬m _ _ = ⊥-elim (¬m tt)
... | ev√ fp _      = case fp of λ ()
... | evSync _ pStep qStep with repa-ev-inv pStep
...   | refl , refl with repeat-a-inv qStep
...     | refl = AS , wev τ*-refl AS-a (τ*-step AS↑-τ τ*-refl) , q1

R1-fwd-τ : ∀ {p q p′}
         → R1 p q → p ─[ τ ]─► p′
         → Σ[ q′ ∈ DProc ] ((q ═[ τ ]═► q′) × R1 p′ q′)
R1-fwd-τ q0 stp with Par-τ-elim Events _ (a ⟶₀ REPEAT) REPEAT stp
... | τL _ pτ _ = ⊥-elim (⟶₀-no-τ pτ)
... | τR _ qτ _ = ⊥-elim (repeat-no-τ qτ)
R1-fwd-τ q1 stp with Par-τ-elim Events _ REPEAT REPa stp
... | τL _ pτ _ = ⊥-elim (repeat-no-τ pτ)
... | τR _ qτ _ = ⊥-elim (repa-no-τ qτ)
R1-fwd-τ q2 stp with Par-τ-elim Events _ REPa REPEAT stp
... | τL _ pτ _ = ⊥-elim (repa-no-τ pτ)
... | τR _ qτ _ = ⊥-elim (repeat-no-τ qτ)

module M1 = WSimFromRel R1 R1-fwd-ev R1-fwd-τ

-- assert AS [T= aRR   (traces aRR ⊆ traces AS)
as⊑aRR : AS ⊑T aRR
as⊑aRR = wsim→⊑T (M1.rel→wsim q0)
```

### §5.5 `aRR [T= AS`: a weak simulation of `AS` by `aRR`

`aRR [T= AS` unfolds to `∀ s → traces AS s → traces aRR s`, so now `AS` is the
*simulated* side. `AS` fires `a` into `AS↑`, then re-enters via a `τ`; `aRR`
answers each `a` with the corresponding `Par-sync` `a`-step and absorbs `AS`'s
`τ` by staying put.

```agda
data R2 : DProc → DProc → Set₁ where
  e0 : R2 AS  aRR
  e1 : R2 AS↑ T1
  e2 : R2 AS  T1
  e3 : R2 AS↑ T2
  e4 : R2 AS  T2

R2-fwd-ev : ∀ {p q} {l : Event√ (⊤poly {lzero})} {p′}
          → R2 p q → p ─[ ev l ]─► p′
          → Σ[ q′ ∈ DProc ] ((q ═[ ev l ]═► q′) × R2 p′ q′)
R2-fwd-ev e0 stp with loop-pfx-ev-inv a (λ _ → Skip) asK stp
... | x , refl , refl = T1 , wev τ*-refl S0-a τ*-refl , e1
R2-fwd-ev e2 stp with loop-pfx-ev-inv a (λ _ → Skip) asK stp
... | x , refl , refl = T2 , wev τ*-refl T1-a τ*-refl , e3
R2-fwd-ev e4 stp with loop-pfx-ev-inv a (λ _ → Skip) asK stp
... | x , refl , refl = T1 , wev τ*-refl T2-a τ*-refl , e1
R2-fwd-ev e1 stp = ⊥-elim (sil-no-ev refl stp)
R2-fwd-ev e3 stp = ⊥-elim (sil-no-ev refl stp)

R2-fwd-τ : ∀ {p q p′}
         → R2 p q → p ─[ τ ]─► p′
         → Σ[ q′ ∈ DProc ] ((q ═[ τ ]═► q′) × R2 p′ q′)
R2-fwd-τ e0 stp = ⊥-elim (loop-pfx-no-τ a (λ _ → Skip) asK stp)
R2-fwd-τ e2 stp = ⊥-elim (loop-pfx-no-τ a (λ _ → Skip) asK stp)
R2-fwd-τ e4 stp = ⊥-elim (loop-pfx-no-τ a (λ _ → Skip) asK stp)
R2-fwd-τ e1 stp with sil-τ-uniq refl stp
... | refl = T1 , wτ τ*-refl , e2
R2-fwd-τ e3 stp with sil-τ-uniq refl stp
... | refl = T2 , wτ τ*-refl , e4

module M2 = WSimFromRel R2 R2-fwd-ev R2-fwd-τ

-- assert aRR [T= AS   (traces AS ⊆ traces aRR)
aRR⊑as : aRR ⊑T AS
aRR⊑as = wsim→⊑T (M2.rel→wsim e0)
```

Together `as⊑aRR` and `aRR⊑as` give `AS =T aRR`, discharging both `.csp`
asserts.
