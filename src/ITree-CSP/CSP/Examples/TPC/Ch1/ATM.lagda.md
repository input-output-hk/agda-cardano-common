# TPC/UCS chapter 1: the ATM (`ATM1`, `ATM2`)

The fifth of five example modules porting chapter-1 processes from A.W.
Roscoe's two CSP books — *The Theory and Practice of Concurrency* (TPC) and
*Understanding Concurrent Systems* (UCS) — to this process-tree
formalisation. Sources:

- `fdr-examples/tpc/chapter01/chapter1.csp` (TPC §1.1, lines ~189–208)
- `fdr-examples/ucs/chapter01/ucs1.csp` (UCS ch. 1, same processes)

```csp
ATM1 = incard?c -> pin.fpin(c) -> req?n -> dispense!n -> outcard.c -> ATM1

ATM2 = incard?c -> pin.fpin(c) -> req?n ->
         ((dispense!n -> outcard.c -> ATM2)
          |~| (refuse -> (ATM2 |~| outcard.c -> ATM2)))
```

`ATM1` is the deterministic cash machine: read the card, check the PIN,
read the requested amount, dispense it, and return the card. `ATM2` adds
the possibility of refusing the transaction: after `req`, it
*internally* chooses (`|~|`, CSP internal choice) between dispensing as
before, or refusing — and after a refusal it internally chooses again
between silently restarting (keeping the card, `ATM2`) or returning the
card first (`outcard.c -> ATM2`). `fpin(c)`, the PIN-lookup function
applied to the card, is kept abstract per the brief: we model `pin` as
carrying the card's own digit `c` (`pin!c`), the only information about
`fpin` that matters at this level of abstraction — the machine echoes
some deterministic function of the inserted card on the `pin` channel.

This module carries both the definitions (§§1–4) and their verification
(§5). The definitions port the two processes onto `PTree` using the
`CSP.Operators` combinators (in particular the payload prefixes
`e ⟶ λ x → …` for reads and `e ! v ⟶ …` for writes, and `_⊓_` for
`|~|`); §5 discharges the two FDR asserts about the pair — the
deterministic machine trace-refines the nondeterministic one
(`ATM2 [T= ATM1` holds) but not conversely (`ATM1 [T= ATM2` fails,
witnessed by a trace ending in `refuse`).

## §1. Imports

`Card` needs `Data.Fin`; the amount alphabet `W5` is a small closed enum
kept symbolic (`w10 … w50`) rather than the literal values `{10,20,30,40,50}`,
exactly as `UpDown`'s `UD` keeps `up`/`down` symbolic. `DecEq-Fin`
(`Class.DecEq.Instances`) supplies `DecEq (Fin 10)` for the `pin`/`outcard`
output prefixes; `DecEq W5` is hand-written below for the `dispense` output
prefix. Neither channel returns to a `Poly.⊤`-typed `_□_`/`⨅⁺` here (`ATM1`
and `ATM2` use only prefixes and `⊓`, which needs no `DecEq` on the process
return type), so — unlike `UpDown.lagda.md` and `DayRoutine.lagda.md` — a
`DecEq-⊤poly` instance is *not* required.

```agda
{-# OPTIONS --guardedness #-}

module CSP.Examples.TPC.Ch1.ATM where

open import Level using () renaming (zero to lzero)
open import Data.Unit using (⊤)
import Data.Unit.Polymorphic as Poly
open import Data.Fin using (Fin)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq)
open import Class.DecEq.Instances using (DecEq-Fin)

open import Process_Trees
```

## §2. The payload types

`Card = Fin 10` mirrors `CARD = {0..9}`; `W5` mirrors the amount alphabet
`WA = {10,20,30,40,50}`, kept as five symbolic constructors.

```agda
Card : Set
Card = Fin 10

data W5 : Set where
  w10 w20 w30 w40 w50 : W5
```

`DecEq W5` is needed for the `dispense ! n ⟶ …` output prefix; `DecEq
Card` (needed for `pin ! c ⟶ …` and `outcard ! c ⟶ …`) comes from
`DecEq-Fin` opened above, which resolves `DecEq (Fin 10)` by instance
search.

```agda
W5-≟ : (x y : W5) → Dec (x ≡ y)
W5-≟ w10 w10 = yes refl
W5-≟ w20 w20 = yes refl
W5-≟ w30 w30 = yes refl
W5-≟ w40 w40 = yes refl
W5-≟ w50 w50 = yes refl
W5-≟ w10 w20 = no λ ()
W5-≟ w10 w30 = no λ ()
W5-≟ w10 w40 = no λ ()
W5-≟ w10 w50 = no λ ()
W5-≟ w20 w10 = no λ ()
W5-≟ w20 w30 = no λ ()
W5-≟ w20 w40 = no λ ()
W5-≟ w20 w50 = no λ ()
W5-≟ w30 w10 = no λ ()
W5-≟ w30 w20 = no λ ()
W5-≟ w30 w40 = no λ ()
W5-≟ w30 w50 = no λ ()
W5-≟ w40 w10 = no λ ()
W5-≟ w40 w20 = no λ ()
W5-≟ w40 w30 = no λ ()
W5-≟ w40 w50 = no λ ()
W5-≟ w50 w10 = no λ ()
W5-≟ w50 w20 = no λ ()
W5-≟ w50 w30 = no λ ()
W5-≟ w50 w40 = no λ ()

instance
  DecEq-W5 : DecEq W5
  DecEq-W5 = record { _≟_ = W5-≟ }
```

## §3. The event type and its decidable equality

Six channels: `incard`/`outcard`/`pin` carry a `Card`, `req`/`dispense`
carry a `W5`, and `refuse` is nullary (`⊤`), mirroring the `.csp`
declarations `channel incard, outcard, pin : CARD`, `channel req,
dispense : WA`, `channel refuse`.

```agda
data ATMCh : Set → Set where
  incard outcard pin : ATMCh Card
  req dispense       : ATMCh W5
  refuse              : ATMCh ⊤
```

Six constructors give `6 × 6 = 36` clauses on `AnyTypes ATMCh`: six
diagonal `yes refl` and thirty off-diagonal `no λ ()`, following the
plain hand-rolled idiom of `UpDown.UD-≟`/`Copy.Ch-≟` (small enough not to
need the `Fin`-retract trick of `DayRoutine.Ev-≟`).

```agda
ATMCh-≟ : (x y : AnyTypes ATMCh) → Dec (x ≡ y)
ATMCh-≟ (_ , incard)  (_ , incard)  = yes refl
ATMCh-≟ (_ , outcard) (_ , outcard) = yes refl
ATMCh-≟ (_ , pin)     (_ , pin)     = yes refl
ATMCh-≟ (_ , req)     (_ , req)     = yes refl
ATMCh-≟ (_ , dispense) (_ , dispense) = yes refl
ATMCh-≟ (_ , refuse)  (_ , refuse)  = yes refl

ATMCh-≟ (_ , incard)  (_ , outcard) = no λ ()
ATMCh-≟ (_ , incard)  (_ , pin)     = no λ ()
ATMCh-≟ (_ , incard)  (_ , req)     = no λ ()
ATMCh-≟ (_ , incard)  (_ , dispense)= no λ ()
ATMCh-≟ (_ , incard)  (_ , refuse)  = no λ ()

ATMCh-≟ (_ , outcard) (_ , incard)  = no λ ()
ATMCh-≟ (_ , outcard) (_ , pin)     = no λ ()
ATMCh-≟ (_ , outcard) (_ , req)     = no λ ()
ATMCh-≟ (_ , outcard) (_ , dispense)= no λ ()
ATMCh-≟ (_ , outcard) (_ , refuse)  = no λ ()

ATMCh-≟ (_ , pin)     (_ , incard)  = no λ ()
ATMCh-≟ (_ , pin)     (_ , outcard) = no λ ()
ATMCh-≟ (_ , pin)     (_ , req)     = no λ ()
ATMCh-≟ (_ , pin)     (_ , dispense)= no λ ()
ATMCh-≟ (_ , pin)     (_ , refuse)  = no λ ()

ATMCh-≟ (_ , req)     (_ , incard)  = no λ ()
ATMCh-≟ (_ , req)     (_ , outcard) = no λ ()
ATMCh-≟ (_ , req)     (_ , pin)     = no λ ()
ATMCh-≟ (_ , req)     (_ , dispense)= no λ ()
ATMCh-≟ (_ , req)     (_ , refuse)  = no λ ()

ATMCh-≟ (_ , dispense)(_ , incard)  = no λ ()
ATMCh-≟ (_ , dispense)(_ , outcard) = no λ ()
ATMCh-≟ (_ , dispense)(_ , pin)     = no λ ()
ATMCh-≟ (_ , dispense)(_ , req)     = no λ ()
ATMCh-≟ (_ , dispense)(_ , refuse)  = no λ ()

ATMCh-≟ (_ , refuse)  (_ , incard)  = no λ ()
ATMCh-≟ (_ , refuse)  (_ , outcard) = no λ ()
ATMCh-≟ (_ , refuse)  (_ , pin)     = no λ ()
ATMCh-≟ (_ , refuse)  (_ , req)     = no λ ()
ATMCh-≟ (_ , refuse)  (_ , dispense)= no λ ()

open import CSP.Operators ATMCh-≟
```

## §4. Process definitions

```agda
AtmProc : Set₁
AtmProc = PTree ATMCh (ExtI ATMCh) (Poly.⊤ {lzero})
```

### §4.1 `ATM1` — the deterministic machine

`ATM1 = incard?c -> pin.fpin(c) -> req?n -> dispense!n -> outcard.c ->
ATM1`: read the card, echo (a function of) it on `pin`, read the
requested amount, dispense it, return the card, loop.

```agda
atm1-body : AtmProc
atm1-body = incard ⟶ λ c → (pin ! c ⟶ (req ⟶ λ n →
              (dispense ! n ⟶ (outcard ! c ⟶ Skip))))

ATM1 : AtmProc
ATM1 = loop0 atm1-body
```

### §4.2 `ATM2` — the machine that may refuse

`ATM2` follows `ATM1` up to `req`, then internally chooses (`_⊓_`)
between dispensing (exactly `ATM1`'s tail) or refusing; after a refusal
it internally chooses again between silently looping back (still holding
the card) or returning the card first. The nesting mirrors the `.csp`
source exactly: `(dispense!n -> outcard.c -> ATM2) |~| (refuse -> (ATM2
|~| outcard.c -> ATM2))`.

```agda
atm2-body : AtmProc
atm2-body = incard ⟶ λ c → (pin ! c ⟶ (req ⟶ λ n →
              ((dispense ! n ⟶ (outcard ! c ⟶ Skip))
               ⊓ (refuse ⟶₀ (Skip ⊓ (outcard ! c ⟶ Skip))))))

ATM2 : AtmProc
ATM2 = loop0 atm2-body
```

## §5. Verification

The `.csp` companion files pose the pair as two FDR asserts:

```csp
assert ATM2 [T= ATM1
assert ATM1 [T= ATM2   -- intended to FAIL
```

The first holds: `ATM1` is exactly the resolution of `ATM2`'s internal
choice that always dispenses, so every trace of `ATM1` is a trace of
`ATM2`. We prove it via a weak simulation of `ATM1` inside `ATM2`
(`Semantics.WeakSim`), resolving `ATM2`'s `⊓` by the internal τ into its
*left* (dispense) arm whenever `ATM1` dispenses. The second fails:
`ATM2` can perform `refuse` after `incard·pin·req`, while `ATM1` at that
point offers only `dispense` — refuted with the four-event witness trace
`⟨incard.0, pin.0, req.10, refuse⟩`.

The machinery (loop-node step inversions generalised over the channel,
the propositional `out-fire` idiom for payload outputs whose offer map
is stuck on the decision `u ≟ u`, the factored-out `WSimFromRel`
corecursion) is imported from the shared
`CSP.Laws.Traces.PrefixInversion` and `Semantics.BisimFromRel` modules;
the witness-trace negation follows `UpDown.lagda.md` §5. What is new here is
driving a `⊓` *inside* a loop state: the post-`req` state of `ATM2`
forces to a `react` whose τ-part is `br2` threaded through
`bindT`/`iterT`, so a single `sTau` at the `fin` index with payload
`lift fzero` / `lift (fsuc fzero)` selects the dispense / refuse arm
definitionally (cf. `⊓-stepL`/`⊓-stepR` in `CSP.Laws.Bisim.Laws` for the
bare `⊓` node).

```agda
open import Level using (Lift; lift)
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (case_of_)
open import Relation.Nullary using (¬_)
open import Class.DecEq using (_≟_)

open import Semantics.LTS       {E = ATMCh} {I = ExtI ATMCh}
open import Semantics.WeakBisim {E = ATMCh} {I = ExtI ATMCh}
  using (WSimF; _═[_]═►_; wev; wτ; _─[τ*]─►_; τ*-refl; τ*-step)
open import Semantics.Failures  {E = ATMCh} {I = ExtI ATMCh}
  using (_⊑T_; traces; _⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import Semantics.WeakSim   {E = ATMCh} {I = ExtI ATMCh}
open WSimF

open import CSP.Laws.Traces.PrefixInversion ATMCh-≟
  using (loop-pfx-ev-inv; loop-pfx-no-τ; loop-out-ev-inv; loop-out-no-τ;
         loop-pfx-trace-elim; loop-out-trace-elim; out-fire;
         sil-no-ev; sil-τ-uniq)
open import Semantics.BisimFromRel {E = ATMCh} {I = ExtI ATMCh}
```

The six event labels, one per channel, carrying their payloads.

```agda
lblIn lblPin lblOut : Card → Event√ (Poly.⊤ {lzero})
lblIn  c = evl (evLabel Card incard  c)
lblPin c = evl (evLabel Card pin     c)
lblOut c = evl (evLabel Card outcard c)

lblReq lblDis : W5 → Event√ (Poly.⊤ {lzero})
lblReq n = evl (evLabel W5 req      n)
lblDis n = evl (evLabel W5 dispense n)

lblRef : Event√ (Poly.⊤ {lzero})
lblRef = evl (evLabel ⊤ refuse tt)
```

### §5.1 The FDR asserts

```agda
-- assert ATM2 [T= ATM1   (holds)
ATM2⊑TATM1 : ATM2 ⊑T ATM1

-- assert ATM1 [T= ATM2   (FAILS, as FDR intends)
¬ATM1⊑TATM2 : ¬ (ATM1 ⊑T ATM2)
```

### §5.2 Node-level scaffolding

Step inversions for the two stable loop-node shapes that occur along
`ATM1` (reader prefix and payload output), imported channel-generic from
`CSP.Laws.Traces.PrefixInversion` in the §5 block above; the `⊓` states
of `ATM2` are never *inverted* below — only driven — so no `⊓` inversion
is needed. A prefix state fires its event at every payload `x` (hence
the `Σ` in the conclusion); an output state fires only its carried value
`u`; both shapes are τ-free.

The `sil` helpers (loop re-entry states) are imported from
`CSP.Laws.Traces.PrefixInversion` in the §5 block above.

The propositional output-firing lemma (the channel-generic `out-fire`,
imported from `CSP.Laws.Traces.PrefixInversion` in the §5 block above,
covering all three output channels `pin`/`dispense`/`outcard`): the
offer map of a loop state sitting on `ce ! u ⟶ P` is the `Output-cont`
guard threaded through `bindV` and `iterV`, all stuck on the one
decision `u ≟ u` (the payload is an *open* `Card`/`W5` variable); a
`with` — matched as `yes _`, not `yes refl` — discharges it and the
whole pipeline computes.

### §5.3 The reachable states

Naming the nested continuations of the two bodies (definitionally the
bodies' lambdas, via η) lets the inversion lemmas and states below be
stated compactly. `ATM2`'s dispense arm is *literally* `ATM1`'s tail
`a1c₃`, which is the whole point of the refinement.

```agda
a1c₄ : Card → AtmProc                 -- outcard!c → (loop)
a1c₄ c = outcard ! c ⟶ Skip

a1c₃ : Card → W5 → AtmProc            -- dispense!n → …
a1c₃ c n = dispense ! n ⟶ a1c₄ c

a1c₂ : Card → AtmProc                 -- req?n → …
a1c₂ c = req ⟶ a1c₃ c

a1c₁ : Card → AtmProc                 -- pin!c → …
a1c₁ c = pin ! c ⟶ a1c₂ c

a2ref : Card → AtmProc                -- refuse → (ATM2 ⊓ outcard!c → ATM2)
a2ref c = refuse ⟶₀ (Skip ⊓ (outcard ! c ⟶ Skip))

a2c₃ : Card → W5 → AtmProc            -- the post-req internal choice
a2c₃ c n = a1c₃ c n ⊓ a2ref c

a2c₂ : Card → AtmProc
a2c₂ c = req ⟶ a2c₃ c

a2c₁ : Card → AtmProc
a2c₁ c = pin ! c ⟶ a2c₂ c
```

Both processes are `loop0`s, so their states are `iter-bind` terms —
definitional unfoldings of the loops' successors, checked by the `refl`s
(and firing lemmas) in the step proofs of §5.4.

```agda
atm1K atm2K : Poly.⊤ {lzero} → PTree ATMCh (ExtI ATMCh) (Poly.⊤ {lzero} ⊎ Poly.⊤ {lzero})
atm1K _ = atm1-body >>= (λ a′ → Ret (inj₁ a′))
atm2K _ = atm2-body >>= (λ a′ → Ret (inj₁ a′))

M₁ : Card → AtmProc
M₁ c = iter-bind (a1c₁ c >>= (λ a′ → Ret (inj₁ a′))) atm1K

M₂ : Card → AtmProc
M₂ c = iter-bind (a1c₂ c >>= (λ a′ → Ret (inj₁ a′))) atm1K

M₃ : Card → W5 → AtmProc
M₃ c n = iter-bind (a1c₃ c n >>= (λ a′ → Ret (inj₁ a′))) atm1K

M₄ : Card → AtmProc
M₄ c = iter-bind (a1c₄ c >>= (λ a′ → Ret (inj₁ a′))) atm1K

M₅ : AtmProc
M₅ = iter-bind (Skip >>= (λ a′ → Ret (inj₁ a′))) atm1K

N₁ : Card → AtmProc
N₁ c = iter-bind (a2c₁ c >>= (λ a′ → Ret (inj₁ a′))) atm2K

N₂ : Card → AtmProc
N₂ c = iter-bind (a2c₂ c >>= (λ a′ → Ret (inj₁ a′))) atm2K

N₃ : Card → W5 → AtmProc                 -- ON the ⊓ (unstable: two τs enabled)
N₃ c n = iter-bind (a2c₃ c n >>= (λ a′ → Ret (inj₁ a′))) atm2K

N₃L : Card → W5 → AtmProc                -- after τ into the dispense arm
N₃L c n = iter-bind (a1c₃ c n >>= (λ a′ → Ret (inj₁ a′))) atm2K

N₃R : Card → AtmProc                     -- after τ into the refuse arm
N₃R c = iter-bind (a2ref c >>= (λ a′ → Ret (inj₁ a′))) atm2K

N₄ : Card → AtmProc
N₄ c = iter-bind (a1c₄ c >>= (λ a′ → Ret (inj₁ a′))) atm2K

N₅ : AtmProc
N₅ = iter-bind (Skip >>= (λ a′ → Ret (inj₁ a′))) atm2K

N₆ : Card → AtmProc                      -- after refuse: the inner ⊓
N₆ c = iter-bind ((Skip ⊓ (outcard ! c ⟶ Skip)) >>= (λ a′ → Ret (inj₁ a′))) atm2K
```

### §5.4 `ATM2`'s strong steps

The reads and the nullary `refuse` fire definitionally (`refl refl`, the
`Prefix-cont` guard is a channel decision on closed constructors); the
payload outputs need their `*-fire` lemma; the two `⊓`-resolving τs pick
a `br2` branch at the closed `fin` index (payload `lift fzero` = left
arm, `lift (fsuc fzero)` = right arm), where the whole
`br2`/`bindT`/`iterT` pipeline computes; the loop re-entry is `sSil refl`.

```agda
ATM2-incard : ∀ c → ATM2 ─[ ev (lblIn c) ]─► N₁ c
ATM2-incard c = sVis {at = Card , incard} {a = c} refl refl

N₁-pin : ∀ c → N₁ c ─[ ev (lblPin c) ]─► N₂ c
N₁-pin c = sVis {at = Card , pin} {a = c} refl (out-fire pin c (a2c₂ c) atm2K)

N₂-req : ∀ c n → N₂ c ─[ ev (lblReq n) ]─► N₃ c n
N₂-req c n = sVis {at = W5 , req} {a = n} refl refl

N₃-τL : ∀ c n → N₃ c n ─[ τ ]─► N₃L c n
N₃-τL c n = sTau {i = Lift lzero (Fin 2) , fin} {a = lift fzero} refl refl

N₃-τR : ∀ c n → N₃ c n ─[ τ ]─► N₃R c
N₃-τR c n = sTau {i = Lift lzero (Fin 2) , fin} {a = lift (fsuc fzero)} refl refl

N₃L-dispense : ∀ c n → N₃L c n ─[ ev (lblDis n) ]─► N₄ c
N₃L-dispense c n = sVis {at = W5 , dispense} {a = n} refl (out-fire dispense n (a1c₄ c) atm2K)

N₄-outcard : ∀ c → N₄ c ─[ ev (lblOut c) ]─► N₅
N₄-outcard c = sVis {at = Card , outcard} {a = c} refl (out-fire outcard c Skip atm2K)

N₅-τ : N₅ ─[ τ ]─► ATM2
N₅-τ = sSil refl

N₃R-refuse : ∀ c → N₃R c ─[ ev lblRef ]─► N₆ c
N₃R-refuse c = sVis {at = ⊤ , refuse} {a = tt} refl refl
```

### §5.5 `assert ATM2 [T= ATM1`: a weak simulation of `ATM1` inside `ATM2`

The factored-out one-directional corecursion `WSimFromRel` is imported
from `Semantics.BisimFromRel` in the §5 block above.

The relation pairs `ATM1`'s six states with the matching `ATM2` states,
indexed by the bound card `c` and amount `n`. The one interesting pair
is `w₃`: when `ATM1` fires `req n` from `M₂ c`, `ATM2` answers with the
same `req n` *followed by the internal τ into the dispense arm*
(`N₃-τL`, absorbed in the weak answer's trailing `τ*`) — so the residual
pair is `(M₃ c n , N₃L c n)`, from which both sides dispense in
lockstep. The refuse arm of `ATM2`'s `⊓` is simply never entered.

```agda
data RAtm : AtmProc → AtmProc → Set₁ where
  w₀ : RAtm ATM1 ATM2
  w₁ : ∀ c → RAtm (M₁ c) (N₁ c)
  w₂ : ∀ c → RAtm (M₂ c) (N₂ c)
  w₃ : ∀ c n → RAtm (M₃ c n) (N₃L c n)
  w₄ : ∀ c → RAtm (M₄ c) (N₄ c)
  w₅ : RAtm M₅ N₅

RAtm-fwd-ev : ∀ {p q} {l : Event√ (Poly.⊤ {lzero})} {p′} → RAtm p q → p ─[ ev l ]─► p′
            → Σ[ q′ ∈ AtmProc ] ((q ═[ ev l ]═► q′) × RAtm p′ q′)
RAtm-fwd-ev w₀ stp with loop-pfx-ev-inv incard a1c₁ atm1K stp
... | c , refl , refl = N₁ c , wev τ*-refl (ATM2-incard c) τ*-refl , w₁ c
RAtm-fwd-ev (w₁ c) stp with loop-out-ev-inv pin c (a1c₂ c) atm1K stp
... | refl , refl = N₂ c , wev τ*-refl (N₁-pin c) τ*-refl , w₂ c
RAtm-fwd-ev (w₂ c) stp with loop-pfx-ev-inv req (a1c₃ c) atm1K stp
... | n , refl , refl =
      N₃L c n , wev τ*-refl (N₂-req c n) (τ*-step (N₃-τL c n) τ*-refl) , w₃ c n
RAtm-fwd-ev (w₃ c n) stp with loop-out-ev-inv dispense n (a1c₄ c) atm1K stp
... | refl , refl = N₄ c , wev τ*-refl (N₃L-dispense c n) τ*-refl , w₄ c
RAtm-fwd-ev (w₄ c) stp with loop-out-ev-inv outcard c Skip atm1K stp
... | refl , refl = N₅ , wev τ*-refl (N₄-outcard c) τ*-refl , w₅
RAtm-fwd-ev w₅ stp = ⊥-elim (sil-no-ev refl stp)

RAtm-fwd-τ : ∀ {p q p′} → RAtm p q → p ─[ τ ]─► p′
           → Σ[ q′ ∈ AtmProc ] ((q ═[ τ ]═► q′) × RAtm p′ q′)
RAtm-fwd-τ w₀ stp = ⊥-elim (loop-pfx-no-τ incard a1c₁ atm1K stp)
RAtm-fwd-τ (w₁ c) stp = ⊥-elim (loop-out-no-τ pin c (a1c₂ c) atm1K stp)
RAtm-fwd-τ (w₂ c) stp = ⊥-elim (loop-pfx-no-τ req (a1c₃ c) atm1K stp)
RAtm-fwd-τ (w₃ c n) stp = ⊥-elim (loop-out-no-τ dispense n (a1c₄ c) atm1K stp)
RAtm-fwd-τ (w₄ c) stp = ⊥-elim (loop-out-no-τ outcard c Skip atm1K stp)
RAtm-fwd-τ w₅ stp with sil-τ-uniq refl stp
... | refl = ATM2 , wτ (τ*-step N₅-τ τ*-refl) , w₀

module MAtm = WSimFromRel RAtm RAtm-fwd-ev RAtm-fwd-τ

ATM2⊑TATM1 = wsim→⊑T (MAtm.rel→wsim w₀)
```

### §5.6 `assert ATM1 [T= ATM2` fails: the witness trace

Trace-level eliminations for the two stable loop-node shapes
(`loop-pfx-trace-elim`/`loop-out-trace-elim`, imported from
`CSP.Laws.Traces.PrefixInversion` in the §5 block above): a trace of a
prefix/output loop state is empty or starts with the offered event.

The witness: `s* = ⟨incard.0, pin.0, req.10, refuse⟩`. `ATM2` performs
it by reading card `0`, echoing the pin, reading the request, then
resolving its `⊓` into the *refuse* arm (`N₃-τR`) and firing `refuse`.

```agda
c₀ : Card
c₀ = fzero

s* : List (Event√ (Poly.⊤ {lzero}))
s* = lblIn c₀ ∷ lblPin c₀ ∷ lblReq w10 ∷ lblRef ∷ []

ATM2-does-s* : traces ATM2 s*
ATM2-does-s* = N₆ c₀ ,
  ⟹-ev (ATM2-incard c₀) (⟹-ev (N₁-pin c₀) (⟹-ev (N₂-req c₀ w10)
    (⟹-τ (N₃-τR c₀ w10) (⟹-ev (N₃R-refuse c₀) ⟹-refl))))
```

`ATM1` cannot: after `incard.0, pin.0, req.10` it sits at `M₃ c₀ w10`,
the `dispense!10` output state, whose offer map at the `refuse` index is
`nothing` *definitionally* (the channel decision
`ATMCh-≟ (W5 , dispense) (⊤ , refuse)` computes to `no` on closed
constructors) — so the `refuse` step is refuted by node inversion, with
no label-discrimination needed.

```agda
M₃-no-refuse : ∀ {t′ : AtmProc} → M₃ c₀ w10 ─[ ev lblRef ]─► t′ → ⊥
M₃-no-refuse (sVis refl br) = case br of λ ()

M₃-refuses : ¬ traces (M₃ c₀ w10) (lblRef ∷ [])
M₃-refuses (_ , ⟹-τ st _)  = loop-out-no-τ dispense w10 (a1c₄ c₀) atm1K st
M₃-refuses (_ , ⟹-ev st _) = M₃-no-refuse st

ATM1-refuses-s* : ¬ traces ATM1 s*
ATM1-refuses-s* tr₀ with loop-pfx-trace-elim incard a1c₁ atm1K tr₀
... | inj₁ ()
... | inj₂ (_ , _ , refl , tr₁) with loop-out-trace-elim pin c₀ (a1c₂ c₀) atm1K tr₁
...   | inj₁ ()
...   | inj₂ (_ , refl , tr₂) with loop-pfx-trace-elim req (a1c₃ c₀) atm1K tr₂
...     | inj₁ ()
...     | inj₂ (_ , _ , refl , tr₃) = M₃-refuses tr₃

¬ATM1⊑TATM2 a1⊑a2 = ATM1-refuses-s* (a1⊑a2 s* ATM2-does-s*)
```
