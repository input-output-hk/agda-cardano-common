# UCS chapter 2: the Collatz recursion

A book-pure "UCS" example, porting the Collatz process of A.W. Roscoe's
*Understanding Concurrent Systems* (UCS), chapter 2, machine-readable
companion file:

- `fdr-examples/ucs/chapter02/ucs2.csp` (UCS ch. 2)

The `.csp` file encodes the Collatz `(3n+1)/2` recursion as a family of
single-event processes and asserts that, started at `45`, it eventually
reaches `1` — where it settles into offering the event `a` forever:

```csp
channel a, b, c

P(n) = if n == 1 then a -> P(1)
       else if n % 2 == 0 then P(n / 2)
       else P((3 * n + 1) / 2)

assert P(45) [T= a -> STOP
```

Every step to a value other than `1` is *silent* (there is no visible
event on the `else` branches), so `P(n)` is a productive silent recursion:
we model each non-`1` step as a `τ`-transition (`Tau`) to `P(next n)`, and
the terminal `n = 1` state as the process `Aω = a → Aω` offering `a`. The
Collatz conjecture — that this recursion terminates for every `n` — is
*not* what the assert asks: `P(45) [T= a -> STOP` is the finite claim that
`a -> STOP` (do at most one `a`, then deadlock) trace-refines `P(45)`,
i.e. every trace of `a -> STOP` is a trace of `P(45)`. That reduces to a
single *halting witness*: the concrete 12-step `τ`-chain
`45 → 68 → 34 → 17 → 26 → 13 → 20 → 10 → 5 → 8 → 4 → 2 → 1` down to the
`a`-offering state. No appeal to the (open) Collatz conjecture is needed.

## §1. Imports

```agda
{-# OPTIONS --guardedness #-}

module CSP.Examples.UCS.Ch2.Collatz where

open import Level using (lift) renaming (zero to lzero)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; suc; _+_; _*_; _/_; _%_; _≟_; _<?_)
open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Class.DecEq using (DecEq; Irrelevant⇒DecEq) renaming (_≟_ to _≟c_)
open import Class.DecEq.Instances using (DecEq-ℕ)

open import Process_Trees
open PTree

-- `⊤poly {lzero}` is `Lift ⊤`, propositionally irrelevant, so its DecEq is trivial.
-- Needed for the external choice `□` in `Bd` (whose return type is `⊤poly`).
instance
  DecEq-⊤poly : DecEq (⊤poly {lzero})
  DecEq-⊤poly = Irrelevant⇒DecEq (λ { (lift _) (lift _) → refl })
```

## §2. The event type

`a` — one nullary visible event (the `.csp` `channel a`). The scalar
recursion `P` (§4) uses only `a`; the value-carrying processes of §6 add
two more channels: `b` — the nullary *bound-exceeded* event, and `d` — a
value-carrying channel (`d.n` announces the current Collatz value `n`).

```agda
data Coll : Set → Set where
  a : Coll ⊤poly
  b : Coll ⊤poly
  d : Coll ℕ
```

## §3. Decidable equality

```agda
Coll-≟ : (x y : AnyTypes Coll) → Dec (x ≡ y)
Coll-≟ (_ , a) (_ , a) = yes refl
Coll-≟ (_ , b) (_ , b) = yes refl
Coll-≟ (_ , d) (_ , d) = yes refl
Coll-≟ (_ , a) (_ , b) = no (λ ())
Coll-≟ (_ , a) (_ , d) = no (λ ())
Coll-≟ (_ , b) (_ , a) = no (λ ())
Coll-≟ (_ , b) (_ , d) = no (λ ())
Coll-≟ (_ , d) (_ , a) = no (λ ())
Coll-≟ (_ , d) (_ , b) = no (λ ())

open import CSP.Operators Coll-≟
```

## §4. The Collatz model

```agda
DProc : Set₁
DProc = PTree Coll (ExtI Coll) (⊤poly {lzero})
```

One Collatz step of the `(3n+1)/2` variant: halve if even, else fold
`3n+1` and halve.

```agda
next : ℕ → ℕ
next n = if does (n % 2 ≟ 0) then n / 2 else (3 * n + 1) / 2
```

`Aω = a → Aω`: the `n = 1` fixed point, offering `a` forever. Written as
a copattern that unfolds the prefix `react` node by hand (rather than
`Aω = a ⟶₀ Aω`, which the guardedness checker rejects because the
corecursive `Aω` ends up as an *argument* to the offer-map builder
`Prefix-cont` and so is not seen under a constructor): the offer map is
inlined as a lambda offering `a`, with the recursive `Aω` directly under
`just`/`react` — exactly the shape of `Operators`' own `Run`.

```agda
Aω : DProc
force Aω = react (λ { (_ , a) _ → just Aω ; (_ , b) _ → nothing ; (_ , d) _ → nothing }) ∅t
```

`P n`: a silent recursion. At `n = 1` it copies `Aω`'s stable
`a`-offering node; at any other `n` it takes one `τ`-step to `P (next n)`
(the corecursive call is guarded under `sil`).

```agda
P : ℕ → DProc
force (P n) with n ≟ 1
... | yes _ = force Aω
... | no  _ = sil (P (next n))
```

## §5. Verification

The remaining machinery: the labelled-transition steps, the weak-trace
relation `_⟹⟨_⟩_`, and the prefix/`Stop` trace inversions used to turn a
trace of `a -> STOP` into one of the two shapes `⟨⟩` / `⟨ev a⟩`.

```agda
open import Semantics.LTS       {E = Coll} {I = ExtI Coll}
open import Semantics.Failures  {E = Coll} {I = ExtI Coll}
  using (_⊑T_; traces; _⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import CSP.Laws.Traces.TraceLaws Coll-≟
  using (Stop-traces-empty)
open import CSP.Laws.Traces.PrefixInversion Coll-≟
  using (⟶₀-no-τ; ⟶₀-ev-inv)
```

### §5.1 The assert

```agda
-- assert P(45) [T= a -> STOP   (holds)
p45-refines-aStop : P 45 ⊑T (a ⟶₀ Stop)
```

### §5.2 The halting witness

The concrete 12-step `τ`-chain from `P 45` down to the `a`-offering fixed
point `Aω`, followed by the visible `a`. Each `P n ─[τ]─► P (next n)`
holds by `sSil refl`: `force (P n)` reduces (via `n ≟ 1 = no`) to
`sil (P (next n))`, and `next n` reduces by computation to the next
Collatz value — so the successor is definitional
(`next 45 = 68`, …, `next 2 = 1`). The final `P 1 ─[ev a]─► Aω` holds by
`sVis`: `force (P 1)` reduces (via `1 ≟ 1 = yes`) to `force Aω`, whose
visible offer of `a` fires.

```agda
p45⟹a : P 45 ⟹⟨ evl (evLabel ⊤poly a tt) ∷ [] ⟩ Aω
p45⟹a =
  ⟹-τ (sSil refl)   -- 45 → 68
  (⟹-τ (sSil refl)   -- 68 → 34
  (⟹-τ (sSil refl)   -- 34 → 17
  (⟹-τ (sSil refl)   -- 17 → 26
  (⟹-τ (sSil refl)   -- 26 → 13
  (⟹-τ (sSil refl)   -- 13 → 20
  (⟹-τ (sSil refl)   -- 20 → 10
  (⟹-τ (sSil refl)   -- 10 → 5
  (⟹-τ (sSil refl)   -- 5 → 8
  (⟹-τ (sSil refl)   -- 8 → 4
  (⟹-τ (sSil refl)   -- 4 → 2
  (⟹-τ (sSil refl)   -- 2 → 1
  (⟹-ev (sVis {at = ⊤poly , a} {a = tt} refl refl) ⟹-refl))))))))))))
```

### §5.3 The proof

`traces (a -> STOP)` contains exactly `⟨⟩` and `⟨ev a⟩`: the source trace
derivation either stops immediately (`⟹-refl`), cannot take a `τ`
(`⟶₀-no-τ`), or fires `a` into `Stop` (`⟶₀-ev-inv`) after which `Stop`
admits only the empty continuation (`Stop-traces-empty`). The empty trace
maps to `⟹-refl`; the single-`a` trace maps to the halting witness.

```agda
p45-refines-aStop s (_ , ⟹-refl)      = P 45 , ⟹-refl
p45-refines-aStop s (_ , ⟹-τ st _)    = ⊥-elim (⟶₀-no-τ st)
p45-refines-aStop s (P′ , ⟹-ev st rest) with ⟶₀-ev-inv st
... | _ , refl , refl with Stop-traces-empty (P′ , rest)
...   | refl = Aω , p45⟹a
```

## §6. Value-carrying processes `Pd`, `Bd`, and the reduced feeder `Rest`

The `.csp` companion also carries a value-announcing variant of the
Collatz process and asserts it is trace-contained in a `RUN`-like buffer:

```csp
NN = 4000
Pd(n) = if n > NN then b -> STOP
        else if n == 1 then a -> Pd(1)
             else d!n -> Pd(next(n))

Bd = a -> Bd [] d?_ -> Bd            -- RUN over {a} ∪ {d.*}, never offers b
assert Bd [T= d?n:{2..100} -> Pd(n)
```

`Pd(n)` announces each Collatz value on the `d` channel (`d!n`), settling
into `a -> Pd(1)` at the fixed point, and *guards* against runaway growth
with the bound `NN`: if a value ever exceeds `NN` it emits the
bound-exceeded event `b` and stops. `Bd` is `RUN` over `{a} ∪ {d.*}`: it
offers `a` and every `d.v` forever and *never* offers `b`.

**Reduced domain.** We prove the second assert over the reduced start
domain `{2,3,4,5}` rather than the book's `{2..100}`. This is a deliberate,
documented reduction: the full `{2..100}` does **not** port. The
`(3n+1)/2` trajectory from `n = 27` climbs past `NN = 4000` (it peaks at
`4616`), so `Pd(27)` eventually emits `b` — an event `Bd` never offers —
and the refinement `Bd [T= d?n:{2..100} -> Pd(n)` is simply **false** in
this model. For the retained starts `{2,3,4,5}` every trajectory stays
tiny (the reachable set is `{1,2,3,4,5,8}`, peaking at `8 ≪ 4000`), so
`Pd` emits only `d.*` and then `a`, never `b`; each such behaviour is a
behaviour of `Bd`. The primary deliverable of this module is the scalar
`P(45) [T= a -> STOP` assert (§5); this second, value-carrying assert is
reduced-domain by design.

Like `Aω`, `Pd`'s visible-event nodes are written as inlined `react`
copatterns rather than via the `⟶`/`!` operators: the corecursive `Pd`
call must sit *directly* under `just` in the offer map for the
guardedness checker to see it as productive (routing it through
`Prefix`/`Output` makes it a function argument, which the checker
rejects — the same reason `Aω` is hand-unfolded). The three inlined
offer maps reproduce exactly `b ⟶₀ Stop` (overflow), `a ⟶₀ Pd 1` (at the
fixed point), and `d ! n ⟶ Pd (next n)` (the value-output step: offer
`d` only for the carried value `n`, via `x ≟c n`).

```agda
NN : ℕ
NN = 4000

Pd : ℕ → DProc
force (Pd n) with NN <? n
... | yes _ = react (λ { (_ , b) _ → just Stop  ; (_ , a) _ → nothing ; (_ , d) _ → nothing }) ∅t
... | no  _ with n ≟ 1
...   | yes _ = react (λ { (_ , a) _ → just (Pd 1) ; (_ , b) _ → nothing ; (_ , d) _ → nothing }) ∅t
...   | no  _ = react (λ { (_ , d) x → case (x ≟c n) of λ where (yes _) → just (Pd (next n)) ; (no _) → nothing
                        ; (_ , a) _ → nothing
                        ; (_ , b) _ → nothing }) ∅t
```

`Bd = a → Bd □ d?_ → Bd`, a non-terminating `RUN` over `{a} ∪ {d.*}`
built with `loop0`; both summands re-enter the loop through `Skip`.

```agda
bd-body : PTree Coll (ExtI Coll) (⊤poly {lzero})
bd-body = (a ⟶₀ Skip) □ (d ⟶ λ _ → Skip)

Bd : DProc
Bd = loop0 bd-body
```

`Rest = d?n:{2,3,4,5} → Pd(n)`: read a value on `d`, and for a value in
the reduced domain continue as `Pd n`; any other value leads to `Stop`
(exactly `d?n → (Pd n ◁ n∈{2..5} ▷ Stop)`, written here as a total
dispatch `pick` so that inversion exposes concrete start values).

```agda
pick : ℕ → DProc
pick 2 = Pd 2
pick 3 = Pd 3
pick 4 = Pd 4
pick 5 = Pd 5
pick _ = Stop

Rest : DProc
Rest = d ⟶ pick
```

## §7. `Bd [T= Rest` over the reduced domain

`Bd ⊑T Rest` unfolds to `∀ s → traces Rest s → traces Bd s`, so `Rest`
is the *simulated* side: we exhibit a weak simulation of `Rest` inside
`Bd` (every move `Rest` makes, `Bd` matches) and conclude with `wsim→⊑T`.
The simulation is corecursive over the (finite) reachable state space;
the corecursion is the shared `WSimFromRel` principle.

```agda
open import Semantics.WeakBisim {E = Coll} {I = ExtI Coll}
  using (_═[_]═►_; wev; _─[τ*]─►_; τ*-refl; τ*-step)
open import Semantics.WeakSim   {E = Coll} {I = ExtI Coll} using (WSim; wsim→⊑T)
open import Semantics.BisimFromRel {E = Coll} {I = ExtI Coll}
```

### §7.1 `Bd`'s transitions

`Bd` is a stable `react` node offering `a` and every `d.v`; firing either
summand lands in the shared re-entry state `BdRe` (a `sil` state one `τ`
away from `Bd`). `bdK`/`BdRe` are the definitional unfoldings of `loop0`'s
successors; the `refl`s below discharge the offer-map computation (the
channel decider `Coll-≟` fires on the concrete `a`/`d` indices).

```agda
bdK : ⊤poly {lzero} → PTree Coll (ExtI Coll) (⊤poly {lzero} ⊎ ⊤poly {lzero})
bdK _ = bd-body >>= (λ a′ → Ret (inj₁ a′))

BdRe : DProc
BdRe = iter-bind (Skip >>= (λ a′ → Ret (inj₁ a′))) bdK

Bd-a : ∀ (x : ⊤poly {lzero}) → Bd ─[ ev (evl (evLabel (⊤poly {lzero}) a x)) ]─► BdRe
Bd-a x = sVis {at = ⊤poly {lzero} , a} {a = x} refl refl

Bd-d : ∀ (n : ℕ) → Bd ─[ ev (evl (evLabel ℕ d n)) ]─► BdRe
Bd-d n = sVis {at = ℕ , d} {a = n} refl refl

BdRe-τ : BdRe ─[ τ ]─► Bd
BdRe-τ = sSil refl
```

### §7.2 Firing inversion for `Rest`

`Rest = d ⟶ pick` fires `d.n` for every `n`, landing in `pick n`. The
`Pd`-node inversions are done inline in `RR-fwd-ev` by matching the
`react` offer map on the channel (`(_ , d)` / `(_ , a)` / `(_ , b)`) —
the offer maps are inlined pattern lambdas, so the wrong-channel arms are
`nothing` (absurd against `just`) and the right arm computes directly.

```agda
rest-ev-inv : ∀ {l : Event√ (⊤poly {lzero})} {p′ : DProc}
            → Rest ─[ ev l ]─► p′
            → Σ[ n ∈ ℕ ] ((l ≡ evl (evLabel ℕ d n)) × (p′ ≡ pick n))
rest-ev-inv (sRet eq) = ⊥-elim (case eq of λ ())
rest-ev-inv (sVis {at = at} {a = x} refl br) with Coll-≟ (ℕ , d) at
... | no  _    = ⊥-elim (case br of λ ())
... | yes refl = x , refl , sym (just-injective br)
```

### §7.3 The simulation relation

The reachable states of `Rest`: `Rest` itself, `Stop` (out-of-domain
reads), and `Pd k` for `k` in the reachable set `{1,2,3,4,5,8}` — closed
under `next` (`next 2=1`, `next 3=5`, `next 4=2`, `next 5=8`, `next 8=4`)
with `1` the `a`-looping fixed point. Every state is matched by `Bd`, and
none of them can ever offer `b`.

```agda
data RR : DProc → DProc → Set₁ where
  rRest : RR Rest Bd
  rP1   : RR (Pd 1) Bd
  rP2   : RR (Pd 2) Bd
  rP3   : RR (Pd 3) Bd
  rP4   : RR (Pd 4) Bd
  rP5   : RR (Pd 5) Bd
  rP8   : RR (Pd 8) Bd
  rStop : RR Stop Bd

rest-cont : ∀ n → RR (pick n) Bd
rest-cont 0 = rStop
rest-cont 1 = rStop
rest-cont 2 = rP2
rest-cont 3 = rP3
rest-cont 4 = rP4
rest-cont 5 = rP5
rest-cont (suc (suc (suc (suc (suc (suc n)))))) = rStop
```

`Bd` matches every visible move: a `d.n` from `Rest`/`Pd`, or an `a` from
`Pd 1`, each via `Bd ═[ev …]═► Bd` (fire, then the loop re-entry `τ`).

```agda
RR-fwd-ev : ∀ {p q} {l : Event√ (⊤poly {lzero})} {p′}
          → RR p q → p ─[ ev l ]─► p′
          → Σ[ q′ ∈ DProc ] ((q ═[ ev l ]═► q′) × RR p′ q′)
RR-fwd-ev rRest stp with rest-ev-inv stp
... | n , refl , refl = Bd , wev τ*-refl (Bd-d n) (τ*-step BdRe-τ τ*-refl) , rest-cont n
RR-fwd-ev rP1 (sRet eq) = ⊥-elim (case eq of λ ())
RR-fwd-ev rP1 (sVis {at = _ , b} refl br) = ⊥-elim (case br of λ ())
RR-fwd-ev rP1 (sVis {at = _ , d} refl br) = ⊥-elim (case br of λ ())
RR-fwd-ev rP1 (sVis {at = _ , a} {a = x} refl br) with just-injective br
... | refl = Bd , wev τ*-refl (Bd-a x) (τ*-step BdRe-τ τ*-refl) , rP1
RR-fwd-ev rP2 (sRet eq) = ⊥-elim (case eq of λ ())
RR-fwd-ev rP2 (sVis {at = _ , a} refl br) = ⊥-elim (case br of λ ())
RR-fwd-ev rP2 (sVis {at = _ , b} refl br) = ⊥-elim (case br of λ ())
RR-fwd-ev rP2 (sVis {at = _ , d} {a = x} refl br) with x ≟c 2
... | no  _    = ⊥-elim (case br of λ ())
... | yes refl with just-injective br
...   | refl = Bd , wev τ*-refl (Bd-d 2) (τ*-step BdRe-τ τ*-refl) , rP1
RR-fwd-ev rP3 (sRet eq) = ⊥-elim (case eq of λ ())
RR-fwd-ev rP3 (sVis {at = _ , a} refl br) = ⊥-elim (case br of λ ())
RR-fwd-ev rP3 (sVis {at = _ , b} refl br) = ⊥-elim (case br of λ ())
RR-fwd-ev rP3 (sVis {at = _ , d} {a = x} refl br) with x ≟c 3
... | no  _    = ⊥-elim (case br of λ ())
... | yes refl with just-injective br
...   | refl = Bd , wev τ*-refl (Bd-d 3) (τ*-step BdRe-τ τ*-refl) , rP5
RR-fwd-ev rP4 (sRet eq) = ⊥-elim (case eq of λ ())
RR-fwd-ev rP4 (sVis {at = _ , a} refl br) = ⊥-elim (case br of λ ())
RR-fwd-ev rP4 (sVis {at = _ , b} refl br) = ⊥-elim (case br of λ ())
RR-fwd-ev rP4 (sVis {at = _ , d} {a = x} refl br) with x ≟c 4
... | no  _    = ⊥-elim (case br of λ ())
... | yes refl with just-injective br
...   | refl = Bd , wev τ*-refl (Bd-d 4) (τ*-step BdRe-τ τ*-refl) , rP2
RR-fwd-ev rP5 (sRet eq) = ⊥-elim (case eq of λ ())
RR-fwd-ev rP5 (sVis {at = _ , a} refl br) = ⊥-elim (case br of λ ())
RR-fwd-ev rP5 (sVis {at = _ , b} refl br) = ⊥-elim (case br of λ ())
RR-fwd-ev rP5 (sVis {at = _ , d} {a = x} refl br) with x ≟c 5
... | no  _    = ⊥-elim (case br of λ ())
... | yes refl with just-injective br
...   | refl = Bd , wev τ*-refl (Bd-d 5) (τ*-step BdRe-τ τ*-refl) , rP8
RR-fwd-ev rP8 (sRet eq) = ⊥-elim (case eq of λ ())
RR-fwd-ev rP8 (sVis {at = _ , a} refl br) = ⊥-elim (case br of λ ())
RR-fwd-ev rP8 (sVis {at = _ , b} refl br) = ⊥-elim (case br of λ ())
RR-fwd-ev rP8 (sVis {at = _ , d} {a = x} refl br) with x ≟c 8
... | no  _    = ⊥-elim (case br of λ ())
... | yes refl with just-injective br
...   | refl = Bd , wev τ*-refl (Bd-d 8) (τ*-step BdRe-τ τ*-refl) , rP4
RR-fwd-ev rStop (sRet eq) = ⊥-elim (case eq of λ ())
RR-fwd-ev rStop (sVis refl br) = ⊥-elim (case br of λ ())
```

No simulated state has a `τ` (each is a stable `react`, its `τ`-part
`∅t`): all `τ`-cases are absurd.

```agda
RR-fwd-τ : ∀ {p q p′} → RR p q → p ─[ τ ]─► p′
         → Σ[ q′ ∈ DProc ] ((q ═[ τ ]═► q′) × RR p′ q′)
RR-fwd-τ rRest (sSil eq)      = ⊥-elim (case eq of λ ())
RR-fwd-τ rRest (sTau refl br) = ⊥-elim (case br of λ ())
RR-fwd-τ rP1 (sSil eq)      = ⊥-elim (case eq of λ ())
RR-fwd-τ rP1 (sTau refl br) = ⊥-elim (case br of λ ())
RR-fwd-τ rP2 (sSil eq)      = ⊥-elim (case eq of λ ())
RR-fwd-τ rP2 (sTau refl br) = ⊥-elim (case br of λ ())
RR-fwd-τ rP3 (sSil eq)      = ⊥-elim (case eq of λ ())
RR-fwd-τ rP3 (sTau refl br) = ⊥-elim (case br of λ ())
RR-fwd-τ rP4 (sSil eq)      = ⊥-elim (case eq of λ ())
RR-fwd-τ rP4 (sTau refl br) = ⊥-elim (case br of λ ())
RR-fwd-τ rP5 (sSil eq)      = ⊥-elim (case eq of λ ())
RR-fwd-τ rP5 (sTau refl br) = ⊥-elim (case br of λ ())
RR-fwd-τ rP8 (sSil eq)      = ⊥-elim (case eq of λ ())
RR-fwd-τ rP8 (sTau refl br) = ⊥-elim (case br of λ ())
RR-fwd-τ rStop (sSil eq)      = ⊥-elim (case eq of λ ())
RR-fwd-τ rStop (sTau refl br) = ⊥-elim (case br of λ ())
```

### §7.4 The assert

```agda
module MRR = WSimFromRel RR RR-fwd-ev RR-fwd-τ

-- assert Bd [T= d?n:{2,3,4,5} -> Pd(n)   (reduced from the book's {2..100})
bd-refines-rest : Bd ⊑T Rest
bd-refines-rest = wsim→⊑T (MRR.rel→wsim rRest)
```
