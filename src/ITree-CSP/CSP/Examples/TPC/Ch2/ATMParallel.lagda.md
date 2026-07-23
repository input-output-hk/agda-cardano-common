# TPC chapter 2: the ATM and its customer under total synchronisation

Second chapter-2 example (parallel operators), porting the interface-parallel
ATM/customer combination of A.W. Roscoe's *The Theory and Practice of
Concurrency* (TPC §2.1) to this process-tree formalisation. Source:

- `fdr-examples/tpc/chapter02/section2-1.csp`

```csp
ATM1 = incard?c -> pin.fpin(c) -> req?n ->
         dispense!n -> outcard.c -> ATM1

CUST1(card) = incard.card -> pin?p:S(card) -> req.50 ->
              dispense?x:{y | y <- WA, y >=50} -> outcard.card -> CUST1(card)

S(1) = {PIN.1,PIN.4,PIN.7}          -- card 1's remembered PINs (fpin(1) among them)

ATM1andCUST1(card) = ATM1 [|Events|] CUST1(card)

SeqATMC(card) = incard.card -> pin.fpin(card) -> req.50 -> dispense.50 ->
                outcard.card -> SeqATMC(card)

assert SeqATMC(1) [T= ATM1andCUST1(1)
assert ATM1andCUST1(1) [T= SeqATMC(1)
```

`ATM1` is the deterministic cash machine of chapter 1
(`CSP.Examples.TPC.Ch1.ATM`); `CUST1(card)` is the customer who inserts a
fixed card, accepts any PIN echo in the remembered set `S(card)`, requests
`50`, accepts any dispensed amount `≥ 50`, and takes the card back.
`ATM1andCUST1(card)` synchronises the two over **all** events (interface
parallel `[|Events|]`, i.e. TPC's synchronous parallel `‖`), so every event
needs the joint agreement of both sides — on the channel *and* on the payload.
For card 1 the customer's PIN menu `{PIN.1, PIN.4, PIN.7}` contains the
machine's echo `fpin(1) = PIN.1`, so the combination runs forever through the
one common cycle and is trace-equivalent to the sequential contraction
`SeqATMC(1)`. This module proves both TPC asserts about card 1:

```text
seq⊑par1 : SeqATMC c1 ⊑T ATM1andCUST1 c1     -- every product trace is sequential (§5.5)
par⊑seq1 : ATM1andCUST1 c1 ⊑T SeqATMC c1     -- every sequential trace is realised (§5.6)
```

**Modelling reductions** (only card 1 is proved, so the payload alphabets are
pruned to the values reachable in `ATM1andCUST1(1)`):

- `Card` has the single value `c1` (the book's `CARD = {1..10}`: the customer
  only ever inserts card 1, and under total synchronisation the machine's
  `incard?c` can then only read card 1);
- `PIN` has the three values `p1 p4 p7` — exactly `S(1)`, with
  `fpin c1 = p1 ∈ S(1)`;
- `Amt` has the single value `a50` (the book's `WA = {10,…,100}`: the customer
  only ever requests `50`, so `req`/`dispense` only ever carry `50`).

With the types pruned this way, `CUST1`'s *constrained* inputs become plain
input prefixes: the PIN menu `pin?p:S(1)` is an input over the whole of `PIN`
(since `S(1) = PIN`), and `dispense?x:{y≥50}` an input over the whole of `Amt`
(since `{y ∈ WA | y ≥ 50} ∩ Amt = {a50} = Amt`). This is the encoding that
keeps the synchronisation proofs tractable: the interesting content — the
machine offers only `pin.p1` while the customer would accept `p1/p4/p7`, and
total sync selects `p1` — is untouched, because the *machine* side still
outputs the single value `fpin c1`.

## §1. Imports

```agda
{-# OPTIONS --guardedness #-}

module CSP.Examples.TPC.Ch2.ATMParallel where

open import Level using () renaming (zero to lzero)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as Poly
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Sum using (_⊎_; inj₁)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Class.DecEq using (DecEq)

open import Process_Trees
```

## §2. The payload types

Three tiny closed enums (see the modelling reductions above), each with a
hand-written decidable equality packaged as a `DecEq` instance for the output
prefixes `e ! v ⟶ …` and the loop-inversion lemmas.

```agda
data Card : Set where
  c1 : Card

data PIN : Set where
  p1 p4 p7 : PIN

data Amt : Set where
  a50 : Amt

Card-≟ : (x y : Card) → Dec (x ≡ y)
Card-≟ c1 c1 = yes refl

PIN-≟ : (x y : PIN) → Dec (x ≡ y)
PIN-≟ p1 p1 = yes refl
PIN-≟ p4 p4 = yes refl
PIN-≟ p7 p7 = yes refl
PIN-≟ p1 p4 = no λ ()
PIN-≟ p1 p7 = no λ ()
PIN-≟ p4 p1 = no λ ()
PIN-≟ p4 p7 = no λ ()
PIN-≟ p7 p1 = no λ ()
PIN-≟ p7 p4 = no λ ()

Amt-≟ : (x y : Amt) → Dec (x ≡ y)
Amt-≟ a50 a50 = yes refl

instance
  DecEq-Card : DecEq Card
  DecEq-Card = record { _≟_ = Card-≟ }

  DecEq-PIN : DecEq PIN
  DecEq-PIN = record { _≟_ = PIN-≟ }

  DecEq-Amt : DecEq Amt
  DecEq-Amt = record { _≟_ = Amt-≟ }
```

The PIN-lookup function: `fpin(c) = PIN.c`, so `fpin c1 = p1` — which is why
card 1's combination runs (`p1 ∈ S(1)`), unlike card 2's.

```agda
fpin : Card → PIN
fpin c1 = p1
```

## §3. The event type and its decidable equality

Five channels, mirroring `channel incard, outcard : CARD`,
`channel pin : PINs`, `channel req, dispense : WA` (the chapter-1 `refuse`
channel belongs to `ATM2` only and is dropped). Five constructors give
`5 × 5 = 25` clauses on `AnyTypes ATMCh`: five diagonal `yes refl` and twenty
off-diagonal `no λ ()`, the plain hand-rolled idiom of the chapter-1
`ATM.ATMCh-≟`.

```agda
data ATMCh : Set → Set where
  incard outcard : ATMCh Card
  pin            : ATMCh PIN
  req dispense   : ATMCh Amt

ATMCh-≟ : (x y : AnyTypes ATMCh) → Dec (x ≡ y)
ATMCh-≟ (_ , incard)   (_ , incard)   = yes refl
ATMCh-≟ (_ , outcard)  (_ , outcard)  = yes refl
ATMCh-≟ (_ , pin)      (_ , pin)      = yes refl
ATMCh-≟ (_ , req)      (_ , req)      = yes refl
ATMCh-≟ (_ , dispense) (_ , dispense) = yes refl

ATMCh-≟ (_ , incard)   (_ , outcard)  = no λ ()
ATMCh-≟ (_ , incard)   (_ , pin)      = no λ ()
ATMCh-≟ (_ , incard)   (_ , req)      = no λ ()
ATMCh-≟ (_ , incard)   (_ , dispense) = no λ ()

ATMCh-≟ (_ , outcard)  (_ , incard)   = no λ ()
ATMCh-≟ (_ , outcard)  (_ , pin)      = no λ ()
ATMCh-≟ (_ , outcard)  (_ , req)      = no λ ()
ATMCh-≟ (_ , outcard)  (_ , dispense) = no λ ()

ATMCh-≟ (_ , pin)      (_ , incard)   = no λ ()
ATMCh-≟ (_ , pin)      (_ , outcard)  = no λ ()
ATMCh-≟ (_ , pin)      (_ , req)      = no λ ()
ATMCh-≟ (_ , pin)      (_ , dispense) = no λ ()

ATMCh-≟ (_ , req)      (_ , incard)   = no λ ()
ATMCh-≟ (_ , req)      (_ , outcard)  = no λ ()
ATMCh-≟ (_ , req)      (_ , pin)      = no λ ()
ATMCh-≟ (_ , req)      (_ , dispense) = no λ ()

ATMCh-≟ (_ , dispense) (_ , incard)   = no λ ()
ATMCh-≟ (_ , dispense) (_ , outcard)  = no λ ()
ATMCh-≟ (_ , dispense) (_ , pin)      = no λ ()
ATMCh-≟ (_ , dispense) (_ , req)      = no λ ()

open import CSP.Operators ATMCh-≟
```

## §4. Process definitions

Each loop body is written as a ladder of named continuations (rather than
inline lambdas) so the verification below can name every reachable state; the
ladders are definitionally the nested prefixes of the `.csp` bodies.

```agda
AtmProc : Set₁
AtmProc = PTree ATMCh (ExtI ATMCh) (Poly.⊤ {lzero})
```

### §4.1 `ATM1` — the machine

`ATM1 = incard?c → pin!(fpin c) → req?n → dispense!n → outcard!c → ATM1`
(exactly chapter 1's `ATM1`, over the pruned alphabet).

```agda
a1c₄ : Card → AtmProc                 -- outcard!c → (loop)
a1c₄ c = outcard ! c ⟶ Skip

a1c₃ : Card → Amt → AtmProc           -- dispense!n → …
a1c₃ c n = dispense ! n ⟶ a1c₄ c

a1c₂ : Card → AtmProc                 -- req?n → …
a1c₂ c = req ⟶ a1c₃ c

a1c₁ : Card → AtmProc                 -- pin!(fpin c) → …
a1c₁ c = pin ! fpin c ⟶ a1c₂ c

atm1-body : AtmProc
atm1-body = incard ⟶ a1c₁

ATM1 : AtmProc
ATM1 = loop0 atm1-body
```

### §4.2 `CUST1` — the customer

`CUST1(card) = incard!card → pin?p:S(card) → req!50 → dispense?x:{y≥50} →
outcard!card → CUST1(card)`. Both constrained inputs are plain input
prefixes over the pruned types (`S(1) = PIN`, `{y ≥ 50} = Amt`; see the
header); their continuations ignore the read value, exactly as in the book.

```agda
cuc₄ : Card → AtmProc                 -- outcard!card → (loop)
cuc₄ c = outcard ! c ⟶ Skip

cuc₃ : Card → Amt → AtmProc           -- dispense?x:{y≥50} → …  (x unused)
cuc₃ c x = cuc₄ c

cuc₂ : Card → AtmProc                 -- req!50 → …
cuc₂ c = req ! a50 ⟶ (dispense ⟶ cuc₃ c)

cuc₁ : Card → PIN → AtmProc           -- pin?p:S(card) → …  (p unused)
cuc₁ c p = cuc₂ c

cust1-body : Card → AtmProc
cust1-body c = incard ! c ⟶ (pin ⟶ cuc₁ c)

CUST1 : Card → AtmProc
CUST1 c = loop0 (cust1-body c)
```

### §4.3 `SeqATMC` — the sequential contraction

`SeqATMC(card) = incard!card → pin!(fpin card) → req!50 → dispense!50 →
outcard!card → SeqATMC(card)`: the single common cycle, all outputs.

```agda
sqc₄ : Card → AtmProc                 -- outcard!card → (loop)
sqc₄ c = outcard ! c ⟶ Skip

sqc₃ : Card → AtmProc                 -- dispense!50 → …
sqc₃ c = dispense ! a50 ⟶ sqc₄ c

sqc₂ : Card → AtmProc                 -- req!50 → …
sqc₂ c = req ! a50 ⟶ sqc₃ c

sqc₁ : Card → AtmProc                 -- pin!(fpin card) → …
sqc₁ c = pin ! fpin c ⟶ sqc₂ c

seq-body : Card → AtmProc
seq-body c = incard ! c ⟶ sqc₁ c

SeqATMC : Card → AtmProc
SeqATMC c = loop0 (seq-body c)
```

### §4.4 The interface parallel over all events

`[|Events|]` is `_∥⇘_⇙_` at the *total* event set: every event (any channel,
any payload) is in the synchronisation set, so nothing interleaves — each
step is a joint step of both operands.

```agda
EventsAll : EventSet
EventsAll = chanSet (λ _ → ⊤) (λ _ → yes tt)

ATM1andCUST1 : Card → AtmProc
ATM1andCUST1 c = ATM1 ∥⇘ EventsAll ⇙ CUST1 c
```

## §5. Verification

The two TPC asserts about card 1, as trace refinements. The proof pivots on
one observation: *at the pruned alphabet, `ATM1`'s trace language is already
`SeqATMC c1`'s* — the machine reads the only card `c1`, echoes
`fpin c1 = p1`, reads the only amount `a50`, dispenses it and returns the
card — while `CUST1 c1`'s language is the same cycle except that its `pin`
step also admits `p4`/`p7`. Under total synchronisation a `ParInter EventsAll`
interleaving witness degenerates to the *diagonal* (`psoloL`/`psoloR` need an
unsynchronised event, and `EventsAll` refuses none), so the product's traces
are exactly the common language — `SeqATMC c1`'s.

Concretely: `seq⊑par1` de-interleaves a product trace with `Par-trace-elim
EventsAll`, characterises the ATM-side share by the cyclic grammar `STr`
(§5.2), collapses the witness to the diagonal (`STr-forceL`, §5.4), and
replays the grammar on `SeqATMC c1` (§5.5). `par⊑seq1` characterises a
`SeqATMC c1` trace by the same grammar, realises it on *both* operands
(`ATM1-intro` / `CUST1-intro` — the customer resolves its PIN menu at `p1`
and its dispense menu at `a50`), and re-interleaves with `Par-trace-intro
EventsAll` along the all-`psync` diagonal witness (§5.6).

```agda
open import Semantics.LTS       {E = ATMCh} {I = ExtI ATMCh}
open import Semantics.Failures  {E = ATMCh} {I = ExtI ATMCh}
  using (_⊑T_; traces; _⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)

open import CSP.Laws.Traces.PrefixInversion ATMCh-≟
  using (loop-pfx-ev-inv; loop-pfx-no-τ; loop-out-ev-inv; loop-out-no-τ;
         out-fire; sil-no-ev; sil-τ-uniq)
open import CSP.Laws.Traces.TraceLawsParallel ATMCh-≟ using (Mg)
open import CSP.Laws.Traces.TraceLawsParallelTrace ATMCh-≟
  using (ParInter; pnil; psync; psoloL; psoloR; p√; Par-trace-elim)
open import CSP.Laws.Traces.TraceLawsParallelMono ATMCh-≟
  using (Par-trace-intro)
```

### §5.1 The FDR asserts

```agda
-- assert SeqATMC(1) [T= ATM1andCUST1(1)   (holds)
seq⊑par1 : SeqATMC c1 ⊑T ATM1andCUST1 c1

-- assert ATM1andCUST1(1) [T= SeqATMC(1)   (holds — the PIN is remembered)
par⊑seq1 : ATM1andCUST1 c1 ⊑T SeqATMC c1
```

### §5.2 The cyclic trace grammar

The five event labels of the cycle, and the merge function of the CSP
parallel (η-equal to the one baked into `_∥⇘_⇙_`).

```agda
Ev : Set₁
Ev = Event√ (Poly.⊤ {lzero})

lblIn lblOut : Card → Ev
lblIn  c = evl (evLabel Card incard  c)
lblOut c = evl (evLabel Card outcard c)

lblPin : PIN → Ev
lblPin p = evl (evLabel PIN pin p)

lblReq lblDis : Amt → Ev
lblReq n = evl (evLabel Amt req      n)
lblDis n = evl (evLabel Amt dispense n)

mg⊤ : Mg (Poly.⊤ {lzero}) (Poly.⊤ {lzero}) (Poly.⊤ {lzero})
mg⊤ _ _ = Poly.tt
```

`STr ph s`: `s` is a (finite) trace of the five-phase cycle
`incard.c1 · pin.p1 · req.a50 · dispense.a50 · outcard.c1 · (repeat)` read
from phase `ph` — the trace language of `SeqATMC c1`, and (at the pruned
alphabet) of `ATM1`, and of the synchronised product.

```agda
data Phase : Set where
  ph0 ph1 ph2 ph3 ph4 : Phase

data STr : Phase → List Ev → Set₁ where
  snil : ∀ {ph} → STr ph []
  sIn  : ∀ {s} → STr ph1 s → STr ph0 (lblIn  c1  ∷ s)
  sPin : ∀ {s} → STr ph2 s → STr ph1 (lblPin p1  ∷ s)
  sReq : ∀ {s} → STr ph3 s → STr ph2 (lblReq a50 ∷ s)
  sDis : ∀ {s} → STr ph4 s → STr ph3 (lblDis a50 ∷ s)
  sOut : ∀ {s} → STr ph0 s → STr ph4 (lblOut c1  ∷ s)
```

### §5.3 The reachable states and their strong steps

All three processes are `loop0`s, so their states are `iter-bind` terms over
their bodies' continuation ladders — definitional unfoldings checked by the
`refl`s and `out-fire`s in the step proofs. Since `Card` and `Amt` are
singletons, the ATM's reader states only ever hold `c1`/`a50`, so all states
are closed terms. Machine `M`, customer `C`, sequential `S`; index 5 is the
silent loop re-entry state in each case.

```agda
atmK custK seqK : Poly.⊤ {lzero}
                → PTree ATMCh (ExtI ATMCh) (Poly.⊤ {lzero} ⊎ Poly.⊤ {lzero})
atmK  _ = atm1-body      >>= (λ a′ → Ret (inj₁ a′))
custK _ = cust1-body c1  >>= (λ a′ → Ret (inj₁ a′))
seqK  _ = seq-body c1    >>= (λ a′ → Ret (inj₁ a′))

M₁ M₂ M₃ M₄ M₅ : AtmProc
M₁ = iter-bind (a1c₁ c1     >>= (λ a′ → Ret (inj₁ a′))) atmK
M₂ = iter-bind (a1c₂ c1     >>= (λ a′ → Ret (inj₁ a′))) atmK
M₃ = iter-bind (a1c₃ c1 a50 >>= (λ a′ → Ret (inj₁ a′))) atmK
M₄ = iter-bind (a1c₄ c1     >>= (λ a′ → Ret (inj₁ a′))) atmK
M₅ = iter-bind (Skip        >>= (λ a′ → Ret (inj₁ a′))) atmK

C₁ C₂ C₃ C₄ C₅ : AtmProc
C₁ = iter-bind ((pin ⟶ cuc₁ c1)      >>= (λ a′ → Ret (inj₁ a′))) custK
C₂ = iter-bind (cuc₂ c1              >>= (λ a′ → Ret (inj₁ a′))) custK
C₃ = iter-bind ((dispense ⟶ cuc₃ c1) >>= (λ a′ → Ret (inj₁ a′))) custK
C₄ = iter-bind (cuc₄ c1              >>= (λ a′ → Ret (inj₁ a′))) custK
C₅ = iter-bind (Skip                 >>= (λ a′ → Ret (inj₁ a′))) custK

S₁ S₂ S₃ S₄ S₅ : AtmProc
S₁ = iter-bind (sqc₁ c1 >>= (λ a′ → Ret (inj₁ a′))) seqK
S₂ = iter-bind (sqc₂ c1 >>= (λ a′ → Ret (inj₁ a′))) seqK
S₃ = iter-bind (sqc₃ c1 >>= (λ a′ → Ret (inj₁ a′))) seqK
S₄ = iter-bind (sqc₄ c1 >>= (λ a′ → Ret (inj₁ a′))) seqK
S₅ = iter-bind (Skip    >>= (λ a′ → Ret (inj₁ a′))) seqK
```

The strong steps. Reader prefixes fire definitionally (`refl refl`: the
`Prefix-cont` guard is a channel decision on closed constructors); payload
outputs go through the channel-generic `out-fire` (chapter 1's propositional
output-firing idiom); the loop re-entries are `sSil refl`.

```agda
-- ATM1's cycle
ATM1-in : ATM1 ─[ ev (lblIn c1) ]─► M₁
ATM1-in = sVis {at = Card , incard} {a = c1} refl refl

M₁-pin : M₁ ─[ ev (lblPin p1) ]─► M₂
M₁-pin = sVis {at = PIN , pin} {a = p1} refl (out-fire pin p1 (a1c₂ c1) atmK)

M₂-req : M₂ ─[ ev (lblReq a50) ]─► M₃
M₂-req = sVis {at = Amt , req} {a = a50} refl refl

M₃-dis : M₃ ─[ ev (lblDis a50) ]─► M₄
M₃-dis = sVis {at = Amt , dispense} {a = a50} refl (out-fire dispense a50 (a1c₄ c1) atmK)

M₄-out : M₄ ─[ ev (lblOut c1) ]─► M₅
M₄-out = sVis {at = Card , outcard} {a = c1} refl (out-fire outcard c1 Skip atmK)

M₅-τ : M₅ ─[ τ ]─► ATM1
M₅-τ = sSil refl

-- CUST1 c1's cycle (its pin/dispense menus resolved at p1/a50)
CUST1-in : CUST1 c1 ─[ ev (lblIn c1) ]─► C₁
CUST1-in = sVis {at = Card , incard} {a = c1} refl (out-fire incard c1 (pin ⟶ cuc₁ c1) custK)

C₁-pin : C₁ ─[ ev (lblPin p1) ]─► C₂
C₁-pin = sVis {at = PIN , pin} {a = p1} refl refl

C₂-req : C₂ ─[ ev (lblReq a50) ]─► C₃
C₂-req = sVis {at = Amt , req} {a = a50} refl (out-fire req a50 (dispense ⟶ cuc₃ c1) custK)

C₃-dis : C₃ ─[ ev (lblDis a50) ]─► C₄
C₃-dis = sVis {at = Amt , dispense} {a = a50} refl refl

C₄-out : C₄ ─[ ev (lblOut c1) ]─► C₅
C₄-out = sVis {at = Card , outcard} {a = c1} refl (out-fire outcard c1 Skip custK)

C₅-τ : C₅ ─[ τ ]─► CUST1 c1
C₅-τ = sSil refl

-- SeqATMC c1's cycle (all outputs)
Seq-in : SeqATMC c1 ─[ ev (lblIn c1) ]─► S₁
Seq-in = sVis {at = Card , incard} {a = c1} refl (out-fire incard c1 (sqc₁ c1) seqK)

S₁-pin : S₁ ─[ ev (lblPin p1) ]─► S₂
S₁-pin = sVis {at = PIN , pin} {a = p1} refl (out-fire pin p1 (sqc₂ c1) seqK)

S₂-req : S₂ ─[ ev (lblReq a50) ]─► S₃
S₂-req = sVis {at = Amt , req} {a = a50} refl (out-fire req a50 (sqc₃ c1) seqK)

S₃-dis : S₃ ─[ ev (lblDis a50) ]─► S₄
S₃-dis = sVis {at = Amt , dispense} {a = a50} refl (out-fire dispense a50 (sqc₄ c1) seqK)

S₄-out : S₄ ─[ ev (lblOut c1) ]─► S₅
S₄-out = sVis {at = Card , outcard} {a = c1} refl (out-fire outcard c1 Skip seqK)

S₅-τ : S₅ ─[ τ ]─► SeqATMC c1
S₅-τ = sSil refl
```

### §5.4 Big-step characterisations (the elim halves)

`ASt`/`SSt` index the reachable states of `ATM1`/`SeqATMC c1` by their phase;
reading a big-step off as an `STr` derivation is structural induction with
the chapter-1 loop step-inversions (`loop-pfx-ev-inv`/`loop-out-ev-inv` for
the events, `loop-pfx-no-τ`/`loop-out-no-τ` for stability, `sil-τ-uniq` for
the re-entry). In `ATM1-char` the reader inversions produce an *arbitrary*
payload witness, which the singleton types `Card`/`Amt` immediately pin to
`c1`/`a50` — this is where the pruned alphabet collapses `ATM1`'s language
onto the sequential cycle.

```agda
data ASt : Phase → AtmProc → Set₁ where
  A0 : ASt ph0 ATM1
  A1 : ASt ph1 M₁
  A2 : ASt ph2 M₂
  A3 : ASt ph3 M₃
  A4 : ASt ph4 M₄
  A5 : ASt ph0 M₅

ATM1-char : ∀ {ph p s} {p′ : AtmProc} → ASt ph p → p ⟹⟨ s ⟩ p′ → STr ph s
ATM1-char _  ⟹-refl        = snil
ATM1-char A0 (⟹-τ st _)    = ⊥-elim (loop-pfx-no-τ incard a1c₁ atmK st)
ATM1-char A0 (⟹-ev st rest) with loop-pfx-ev-inv incard a1c₁ atmK st
... | c1 , refl , refl = sIn (ATM1-char A1 rest)
ATM1-char A1 (⟹-τ st _)    = ⊥-elim (loop-out-no-τ pin p1 (a1c₂ c1) atmK st)
ATM1-char A1 (⟹-ev st rest) with loop-out-ev-inv pin p1 (a1c₂ c1) atmK st
... | refl , refl = sPin (ATM1-char A2 rest)
ATM1-char A2 (⟹-τ st _)    = ⊥-elim (loop-pfx-no-τ req (a1c₃ c1) atmK st)
ATM1-char A2 (⟹-ev st rest) with loop-pfx-ev-inv req (a1c₃ c1) atmK st
... | a50 , refl , refl = sReq (ATM1-char A3 rest)
ATM1-char A3 (⟹-τ st _)    = ⊥-elim (loop-out-no-τ dispense a50 (a1c₄ c1) atmK st)
ATM1-char A3 (⟹-ev st rest) with loop-out-ev-inv dispense a50 (a1c₄ c1) atmK st
... | refl , refl = sDis (ATM1-char A4 rest)
ATM1-char A4 (⟹-τ st _)    = ⊥-elim (loop-out-no-τ outcard c1 Skip atmK st)
ATM1-char A4 (⟹-ev st rest) with loop-out-ev-inv outcard c1 Skip atmK st
... | refl , refl = sOut (ATM1-char A5 rest)
ATM1-char A5 (⟹-τ st rest) with sil-τ-uniq refl st
... | refl = ATM1-char A0 rest
ATM1-char A5 (⟹-ev st _)   = ⊥-elim (sil-no-ev refl st)

data SSt : Phase → AtmProc → Set₁ where
  B0 : SSt ph0 (SeqATMC c1)
  B1 : SSt ph1 S₁
  B2 : SSt ph2 S₂
  B3 : SSt ph3 S₃
  B4 : SSt ph4 S₄
  B5 : SSt ph0 S₅

SeqATMC-char : ∀ {ph p s} {p′ : AtmProc} → SSt ph p → p ⟹⟨ s ⟩ p′ → STr ph s
SeqATMC-char _  ⟹-refl        = snil
SeqATMC-char B0 (⟹-τ st _)    = ⊥-elim (loop-out-no-τ incard c1 (sqc₁ c1) seqK st)
SeqATMC-char B0 (⟹-ev st rest) with loop-out-ev-inv incard c1 (sqc₁ c1) seqK st
... | refl , refl = sIn (SeqATMC-char B1 rest)
SeqATMC-char B1 (⟹-τ st _)    = ⊥-elim (loop-out-no-τ pin p1 (sqc₂ c1) seqK st)
SeqATMC-char B1 (⟹-ev st rest) with loop-out-ev-inv pin p1 (sqc₂ c1) seqK st
... | refl , refl = sPin (SeqATMC-char B2 rest)
SeqATMC-char B2 (⟹-τ st _)    = ⊥-elim (loop-out-no-τ req a50 (sqc₃ c1) seqK st)
SeqATMC-char B2 (⟹-ev st rest) with loop-out-ev-inv req a50 (sqc₃ c1) seqK st
... | refl , refl = sReq (SeqATMC-char B3 rest)
SeqATMC-char B3 (⟹-τ st _)    = ⊥-elim (loop-out-no-τ dispense a50 (sqc₄ c1) seqK st)
SeqATMC-char B3 (⟹-ev st rest) with loop-out-ev-inv dispense a50 (sqc₄ c1) seqK st
... | refl , refl = sDis (SeqATMC-char B4 rest)
SeqATMC-char B4 (⟹-τ st _)    = ⊥-elim (loop-out-no-τ outcard c1 Skip seqK st)
SeqATMC-char B4 (⟹-ev st rest) with loop-out-ev-inv outcard c1 Skip seqK st
... | refl , refl = sOut (SeqATMC-char B5 rest)
SeqATMC-char B5 (⟹-τ st rest) with sil-τ-uniq refl st
... | refl = SeqATMC-char B0 rest
SeqATMC-char B5 (⟹-ev st _)   = ⊥-elim (sil-no-ev refl st)
```

The total-synchronisation collapse: a `ParInter EventsAll` witness whose
left share is an `STr` trace is the *diagonal* — `psoloL`/`psoloR` would need
an event outside `EventsAll` (there are none: `mem` is constantly `⊤`), and
the joint-√ `p√` would need `√` at the head of the left share, which no `STr`
trace contains. So the composite trace *is* the left share.

```agda
STr-forceL : ∀ {ph sP sQ s}
           → ParInter EventsAll mg⊤ sP sQ s → STr ph sP → sP ≡ s
STr-forceL pnil          _         = refl
STr-forceL (psync _ PI)  (sIn  tl) = cong (lblIn  c1  ∷_) (STr-forceL PI tl)
STr-forceL (psync _ PI)  (sPin tl) = cong (lblPin p1  ∷_) (STr-forceL PI tl)
STr-forceL (psync _ PI)  (sReq tl) = cong (lblReq a50 ∷_) (STr-forceL PI tl)
STr-forceL (psync _ PI)  (sDis tl) = cong (lblDis a50 ∷_) (STr-forceL PI tl)
STr-forceL (psync _ PI)  (sOut tl) = cong (lblOut c1  ∷_) (STr-forceL PI tl)
STr-forceL (psoloL ¬m _) _         = ⊥-elim (¬m tt)
STr-forceL (psoloR ¬m _) _         = ⊥-elim (¬m tt)
STr-forceL p√ ()
```

### §5.5 `assert SeqATMC(1) [T= ATM1andCUST1(1)`

The intro half for the sequential machine (each `STr` production is the
matching §5.3 step; `sOut` also crosses the silent re-entry), then the
assembly: de-interleave the product trace, characterise the ATM share,
collapse to the diagonal, replay on `SeqATMC c1`.

```agda
seqSt : Phase → AtmProc
seqSt ph0 = SeqATMC c1
seqSt ph1 = S₁
seqSt ph2 = S₂
seqSt ph3 = S₃
seqSt ph4 = S₄

SeqATMC-intro : ∀ {ph s} → STr ph s → traces (seqSt ph) s
SeqATMC-intro {ph} snil = seqSt ph , ⟹-refl
SeqATMC-intro (sIn tl) with SeqATMC-intro tl
... | p′ , bs = p′ , ⟹-ev Seq-in bs
SeqATMC-intro (sPin tl) with SeqATMC-intro tl
... | p′ , bs = p′ , ⟹-ev S₁-pin bs
SeqATMC-intro (sReq tl) with SeqATMC-intro tl
... | p′ , bs = p′ , ⟹-ev S₂-req bs
SeqATMC-intro (sDis tl) with SeqATMC-intro tl
... | p′ , bs = p′ , ⟹-ev S₃-dis bs
SeqATMC-intro (sOut tl) with SeqATMC-intro tl
... | p′ , bs = p′ , ⟹-ev S₄-out (⟹-τ S₅-τ bs)

seq⊑par1 s (Rt , bs) with Par-trace-elim EventsAll mg⊤ ATM1 (CUST1 c1) bs
... | sP , sQ , P′ , Q′ , rP , rQ , inter with ATM1-char A0 rP
...   | str with STr-forceL inter str
...     | refl = SeqATMC-intro str
```

### §5.6 `assert ATM1andCUST1(1) [T= SeqATMC(1)`

The intro halves for the two operands (the customer answers the machine's
`pin.p1` from its three-value menu and the machine's `dispense.a50` from its
amount menu — both are the plain prefix steps of §5.3), the all-`psync`
diagonal witness, and the assembly through `Par-trace-intro`.

```agda
atmSt cusSt : Phase → AtmProc
atmSt ph0 = ATM1
atmSt ph1 = M₁
atmSt ph2 = M₂
atmSt ph3 = M₃
atmSt ph4 = M₄

cusSt ph0 = CUST1 c1
cusSt ph1 = C₁
cusSt ph2 = C₂
cusSt ph3 = C₃
cusSt ph4 = C₄

ATM1-intro : ∀ {ph s} → STr ph s → traces (atmSt ph) s
ATM1-intro {ph} snil = atmSt ph , ⟹-refl
ATM1-intro (sIn tl) with ATM1-intro tl
... | p′ , bs = p′ , ⟹-ev ATM1-in bs
ATM1-intro (sPin tl) with ATM1-intro tl
... | p′ , bs = p′ , ⟹-ev M₁-pin bs
ATM1-intro (sReq tl) with ATM1-intro tl
... | p′ , bs = p′ , ⟹-ev M₂-req bs
ATM1-intro (sDis tl) with ATM1-intro tl
... | p′ , bs = p′ , ⟹-ev M₃-dis bs
ATM1-intro (sOut tl) with ATM1-intro tl
... | p′ , bs = p′ , ⟹-ev M₄-out (⟹-τ M₅-τ bs)

CUST1-intro : ∀ {ph s} → STr ph s → traces (cusSt ph) s
CUST1-intro {ph} snil = cusSt ph , ⟹-refl
CUST1-intro (sIn tl) with CUST1-intro tl
... | p′ , bs = p′ , ⟹-ev CUST1-in bs
CUST1-intro (sPin tl) with CUST1-intro tl
... | p′ , bs = p′ , ⟹-ev C₁-pin bs
CUST1-intro (sReq tl) with CUST1-intro tl
... | p′ , bs = p′ , ⟹-ev C₂-req bs
CUST1-intro (sDis tl) with CUST1-intro tl
... | p′ , bs = p′ , ⟹-ev C₃-dis bs
CUST1-intro (sOut tl) with CUST1-intro tl
... | p′ , bs = p′ , ⟹-ev C₄-out (⟹-τ C₅-τ bs)

STr-diag : ∀ {ph s} → STr ph s → ParInter EventsAll mg⊤ s s s
STr-diag snil      = pnil
STr-diag (sIn  tl) = psync tt (STr-diag tl)
STr-diag (sPin tl) = psync tt (STr-diag tl)
STr-diag (sReq tl) = psync tt (STr-diag tl)
STr-diag (sDis tl) = psync tt (STr-diag tl)
STr-diag (sOut tl) = psync tt (STr-diag tl)

par⊑seq1 s (Rt , bs) with SeqATMC-char B0 bs
... | str with ATM1-intro str | CUST1-intro str
...   | P′ , rP | Q′ , rQ =
        Par-trace-intro EventsAll mg⊤ ATM1 (CUST1 c1) rP rQ (STr-diag str)
```

## §6. Status

Both card-1 asserts of TPC §2.1's ATM/customer combination are discharged:
`seq⊑par1` (§5.5) and `par⊑seq1` (§5.6) together give the trace equivalence
`traces (ATM1andCUST1 c1) = traces (SeqATMC c1)`. The card-2 asserts (the
customer who *mis*remembers the PIN: refinement holds one way only, and the
combination deadlocks) need a second card value and a failures-level
deadlock argument, and are out of scope here. No postulates, no
`NON_TERMINATING`, no `mutual` blocks.
