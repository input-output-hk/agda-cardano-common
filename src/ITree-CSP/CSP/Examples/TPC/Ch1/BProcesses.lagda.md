# TPC/UCS chapter 1: `B0`/`B1`, and `BX`

The third of five example modules porting chapter-1 processes from A.W.
Roscoe's two CSP books — *The Theory and Practice of Concurrency* (TPC) and
*Understanding Concurrent Systems* (UCS) — to this process-tree
formalisation. Both books' machine-readable companion files pose the same
tiny two-event `{a, b}` example and the same (intentionally failing) `assert`:

- `fdr-examples/tpc/chapter01/chapter1.csp` (TPC §1.1)
- `fdr-examples/ucs/chapter01/ucs1.csp` (UCS ch. 1)

```csp
channel a,b

B0 = a -> B0 [] b -> B1
B1 = a -> B0 [] b -> STOP

-- Above, B0 is the process (labelled P in the notes) which STOPs when
-- supplied with two consecutive b's

BX = a -> B0 [] b -> a -> b -> a -> b -> a -> a -> b -> b -> b -> STOP

assert B0 [T= BX
```

`B0` is the two-state machine that deadlocks the instant it is offered two
consecutive `b`s; `BX` is a fixed implementation whose `b`-branch runs
through a nine-event chain — `a,b,a,b,a,a,b,b,b` — before stopping, a chain
that itself contains **three** consecutive `b`s (`…,b,b,b,STOP`). The
`assert` is the book's own worked *counter-example* to the naive guess that
`B0` (the *specification* "no two consecutive `b`s") refines to `BX`: FDR
reports it false, and this module proves the refutation with an explicit
witness trace.

## §1. Imports

```agda
{-# OPTIONS --guardedness #-}

module CSP.Examples.TPC.Ch1.BProcesses where

open import Level using (lift) renaming (zero to lzero)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as Poly
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_; Irrelevant⇒DecEq)

open import Process_Trees
```

## §2. The event type

Two nullary visible events, mirroring the `.csp` files' `channel a,b`.

```agda
data AB : Set → Set where
  a b : AB ⊤
```

## §3. Decidable equality

```agda
AB-≟ : (x y : AnyTypes AB) → Dec (x ≡ y)
AB-≟ (_ , a) (_ , a) = yes refl
AB-≟ (_ , b) (_ , b) = yes refl
AB-≟ (_ , a) (_ , b) = no λ ()
AB-≟ (_ , b) (_ , a) = no λ ()

open import CSP.Operators AB-≟
```

The only instance required is `DecEq` for the polymorphic unit type
`Poly.⊤ {lzero}`, the return type of `BProc` (`B0`/`BX`), following the same
`Irrelevant⇒DecEq` idiom as `CSP.Examples.TPC.Ch1.UpDown`/`DayRoutine`.
`_□_` also needs a `DecEq` instance for `b-step`'s own return type `BSt`,
supplied below as `DecEq-BSt`.

```agda
instance
  DecEq-⊤poly : DecEq (Poly.⊤ {lzero})
  DecEq-⊤poly = Irrelevant⇒DecEq (λ { (lift _) (lift _) → refl })
```

## §4. Process definitions

```agda
BProc : Set₁
BProc = PTree AB (ExtI AB) (Poly.⊤ {lzero})

data BSt : Set where
  st0 st1 : BSt

instance
  DecEq-BSt : DecEq BSt
  DecEq-BSt = record { _≟_ = dec } where
    dec : (x y : BSt) → Dec (x ≡ y)
    dec st0 st0 = yes refl ; dec st1 st1 = yes refl
    dec st0 st1 = no λ () ; dec st1 st0 = no λ ()

-- B0 = a -> B0 [] b -> B1 ; B1 = a -> B0 [] b -> STOP
b-step : BSt → PTree AB (ExtI AB) BSt
b-step st0 = (a ⟶₀ Ret st0) □ (b ⟶₀ Ret st1)
b-step st1 = (a ⟶₀ Ret st0) □ (b ⟶₀ Stop)   -- Stop never returns: loop stuck = deadlock

B0 : BProc
B0 = loop b-step st0

-- BX = a -> B0 [] b -> a->b->a->b->a->a->b->b->b->STOP
BX : BProc
BX = (a ⟶₀ B0)
   □ (b ⟶₀ (a ⟶₀ (b ⟶₀ (a ⟶₀ (b ⟶₀ (a ⟶₀ (a ⟶₀
       (b ⟶₀ (b ⟶₀ (b ⟶₀ Stop))))))))))
```

## §5. Verification

The `.csp` files pose one FDR assert about this pair — intended, by the
books' own account, to **fail**:

```csp
assert B0 [T= BX
```

`B0` is the specification "never two consecutive `b`s in a row"; `BX` is an
implementation whose `b`-branch happens to contain the chain
`a,b,a,b,a,a,b,b,b` — three consecutive `b`s at the end. So `BX` can perform
the ten-event trace `⟨b,a,b,a,b,a,a,b,b,b⟩` (its whole `b`-branch), but `B0`
cannot: after the eighth event (`…,a,b`) `B0` is at state `st1` having just
seen one `b`; the ninth event (`b`) drives it to the `Stop`-in-body dead end
(two consecutive `b`s), and the tenth event (`b` again) is then impossible.
We prove the refutation with exactly this ten-event witness.

```agda
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ-syntax; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (case_of_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import Semantics.LTS      {E = AB} {I = ExtI AB}
open import Semantics.Failures {E = AB} {I = ExtI AB}
  using (_⊑T_; traces; _⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)

open import CSP.Laws.Traces.PrefixInversion AB-≟
  using (sil-inj; sil-no-ev; sil-τ-uniq; TEmpty; ∅t-empty; □-mt-empty)
```

### §5.1 The FDR assert

```agda
-- assert B0 [T= BX   (FAILS, as the books' own worked example intends)
¬B0⊑TBX : ¬ (B0 ⊑T BX)
```

All events of this alphabet are nullary, so their visible labels share one
shape, abbreviated `lbl`:

```agda
lbl : AB ⊤ → Event√ (Poly.⊤ {lzero})
lbl e = evl (evLabel ⊤ e tt)
```

### §5.2 Node-level scaffolding

A `sil`-headed state offers no visible event and takes exactly one τ, to
the named successor — `sil-inj`/`sil-no-ev`/`sil-τ-uniq` are imported from
`CSP.Laws.Traces.PrefixInversion` above.

```agda
-- Combine a `sil`-witness with a multi-step trace, peeling the forced τ.
-- The continuation is required to be *nonempty* (`e ∷ s`, not `[]`): a
-- `sil`-headed state need not answer an *empty* remaining trace via its own
-- τ (`⟹-refl` on the source node is also a valid — different — witness of
-- that), but every use below applies this only mid-descent, where at least
-- one more event of `s*` is still pending, so the nonempty shape always
-- holds at the call sites.
sil-cont : ∀ {u v : BProc} → PTree.force u ≡ sil v
         → ∀ {e s t} → u ⟹⟨ e ∷ s ⟩ t → v ⟹⟨ e ∷ s ⟩ t
sil-cont eq (⟹-ev stp _)   = ⊥-elim (sil-no-ev eq stp)
sil-cont eq (⟹-τ stp rest) with sil-τ-uniq eq stp
... | refl = rest
```

`b-step`'s stable τ-refusal needs the `TEmpty`/`□-mt-empty` machinery
(imported from `CSP.Laws.Traces.PrefixInversion` above; `DayRoutine` §5.7
needs it for `day-step upSt`'s eight nested `□`s, here `b-step`'s single
level of `□` needs it once).

### §5.3 The reachable states of `B0` and `BX`

`BX`'s `b`-branch is a straight-line prefix chain; we name its nine inner
tail states (the first is `BX` itself, the tenth event lands on `Stop`).
`B0`'s loop, by contrast, is stateful (`BSt`-indexed): `bK` mirrors
`loop`'s hidden internal `step` (`loop body a = iter step a` where
`step s = body s >>= inj₁-Ret`, `CSP.Operators` around l.1042), so
`B0 ≡ iter-bind (bK st0) bK` and `B1 ≡ iter-bind (bK st1) bK` hold
definitionally. `toSt0`/`toSt1` are the silent re-entry way-stations reached
right after firing an event (before the loop returns to `B0`/`B1`); `S2` is
the *stuck* state reached once a second consecutive `b` has driven the body
to `Stop` — it is itself a stable `react` node (no `sil` wrapper), since
`Stop >>= k` and its `iter-bind` wrapping never reduce through a `ret`.

```agda
bK : BSt → PTree AB (ExtI AB) (BSt ⊎ Poly.⊤ {lzero})
bK s = b-step s >>= (λ a′ → Ret (inj₁ a′))

toSt0 toSt1 : BProc
toSt0 = iter-bind (Ret st0 >>= (λ a′ → Ret (inj₁ a′))) bK
toSt1 = iter-bind (Ret st1 >>= (λ a′ → Ret (inj₁ a′))) bK

B1 : BProc
B1 = loop b-step st1

S2 : BProc
S2 = iter-bind (Stop >>= (λ a′ → Ret (inj₁ a′))) bK

X1 X2 X3 X4 X5 X6 X7 X8 X9 : BProc
X9 = b ⟶₀ Stop
X8 = b ⟶₀ X9
X7 = b ⟶₀ X8
X6 = a ⟶₀ X7
X5 = a ⟶₀ X6
X4 = b ⟶₀ X5
X3 = a ⟶₀ X4
X2 = b ⟶₀ X3
X1 = a ⟶₀ X2
```

### §5.4 The witness trace and `BX`'s positive side

`s* = ⟨b,a,b,a,b,a,a,b,b,b⟩` is `BX`'s whole `b`-branch: fired straight down
the chain `X1 … X9` (all hold by `refl`, the same idiom as `UpDown`/
`DayRoutine`'s straight-line prefix steps).

```agda
s* : List (Event√ (Poly.⊤ {lzero}))
s* = lbl b ∷ lbl a ∷ lbl b ∷ lbl a ∷ lbl b ∷ lbl a ∷ lbl a ∷ lbl b ∷ lbl b ∷ lbl b ∷ []

BX-b : BX ─[ ev (lbl b) ]─► X1
BX-b = sVis {at = ⊤ , b} {a = tt} refl refl

X1-a : X1 ─[ ev (lbl a) ]─► X2
X1-a = sVis {at = ⊤ , a} {a = tt} refl refl

X2-b : X2 ─[ ev (lbl b) ]─► X3
X2-b = sVis {at = ⊤ , b} {a = tt} refl refl

X3-a : X3 ─[ ev (lbl a) ]─► X4
X3-a = sVis {at = ⊤ , a} {a = tt} refl refl

X4-b : X4 ─[ ev (lbl b) ]─► X5
X4-b = sVis {at = ⊤ , b} {a = tt} refl refl

X5-a : X5 ─[ ev (lbl a) ]─► X6
X5-a = sVis {at = ⊤ , a} {a = tt} refl refl

X6-a : X6 ─[ ev (lbl a) ]─► X7
X6-a = sVis {at = ⊤ , a} {a = tt} refl refl

X7-b : X7 ─[ ev (lbl b) ]─► X8
X7-b = sVis {at = ⊤ , b} {a = tt} refl refl

X8-b : X8 ─[ ev (lbl b) ]─► X9
X8-b = sVis {at = ⊤ , b} {a = tt} refl refl

X9-b : X9 ─[ ev (lbl b) ]─► Stop
X9-b = sVis {at = ⊤ , b} {a = tt} refl refl

BX-does-s* : traces BX s*
BX-does-s* = Stop ,
  ⟹-ev BX-b (⟹-ev X1-a (⟹-ev X2-b (⟹-ev X3-a (⟹-ev X4-b
  (⟹-ev X5-a (⟹-ev X6-a (⟹-ev X7-b (⟹-ev X8-b (⟹-ev X9-b ⟹-refl)))))))))
```

### §5.5 `B0`'s loop inversion and stability

`bloop-ev-inv` inverts a strong event-step out of any `((a ⟶₀ X) □ (b ⟶₀
Y))`-bodied loop state (both of `B0`/`B1`'s shapes, with `X`/`Y`
instantiated differently), mirroring `loop-ev-inv`'s `with`-on-`AB-≟`
idiom but combining both sides of the `□`'s merged offer map.

```agda
bloop-ev-inv : (X Y : PTree AB (ExtI AB) BSt) → ∀ {l t′}
             → iter-bind (((a ⟶₀ X) □ (b ⟶₀ Y)) >>= (λ a′ → Ret (inj₁ a′))) bK
                 ─[ ev l ]─► t′
             → ((l ≡ lbl a) × (t′ ≡ iter-bind (X >>= (λ a′ → Ret (inj₁ a′))) bK))
               ⊎ ((l ≡ lbl b) × (t′ ≡ iter-bind (Y >>= (λ a′ → Ret (inj₁ a′))) bK))
bloop-ev-inv X Y (sRet eq) = case eq of λ ()
bloop-ev-inv X Y (sVis {at = at} {a = aa} refl br) with AB-≟ (⊤ , a) at
... | yes refl = inj₁ (refl , sym (just-injective br))
... | no ¬eq with AB-≟ (⊤ , b) at
...   | yes refl = inj₂ (refl , sym (just-injective br))
...   | no ¬eq2 = ⊥-elim (case br of λ ())
```

`B0`/`B1` never take a silent step on their own (their `□`'s two prefixes
are both stable): the τ-emptiness of `b-step st0`/`b-step st1`'s single `□`
level, then the `Up-no-τ` idiom of `DayRoutine` §5.7 (re-doing the stuck
`with`-match on the concrete body to force it in step with the abstract
index carried by `sTau`).

```agda
bStep0-τ-empty : TEmpty (viewT (PTree.force (b-step st0)))
bStep0-τ-empty = □-mt-empty ∅t-empty ∅t-empty

bStep1-τ-empty : TEmpty (viewT (PTree.force (b-step st1)))
bStep1-τ-empty = □-mt-empty ∅t-empty ∅t-empty

B0-no-τ : ∀ {t′} → B0 ─[ τ ]─► t′ → ⊥
B0-no-τ (sSil eq) = case eq of λ ()
B0-no-τ (sTau {i = i} {a = x} refl br)
  with viewT (PTree.force (b-step st0)) i x | bStep0-τ-empty i x
... | just _  | ()
... | nothing | refl = case br of λ ()

B1-no-τ : ∀ {t′} → B1 ─[ τ ]─► t′ → ⊥
B1-no-τ (sSil eq) = case eq of λ ()
B1-no-τ (sTau {i = i} {a = x} refl br)
  with viewT (PTree.force (b-step st1)) i x | bStep1-τ-empty i x
... | just _  | ()
... | nothing | refl = case br of λ ()
```

`S2` (`b-step`'s `Stop` branch, wrapped by the loop) is stuck outright:
`Stop`'s own offer/τ maps are the unconditional constants `∅v`/`∅t`, so
every wrapping layer (`>>=`, `iter-bind`) collapses to `nothing` without
needing any index case analysis.

```agda
loop-stop-no-ev : ∀ {l t′} → S2 ─[ ev l ]─► t′ → ⊥
loop-stop-no-ev (sRet eq)     = case eq of λ ()
loop-stop-no-ev (sVis refl ())

loop-stop-no-τ : ∀ {t′} → S2 ─[ τ ]─► t′ → ⊥
loop-stop-no-τ (sSil eq)      = case eq of λ ()
loop-stop-no-τ (sTau refl ())
```

### §5.6 `assert B0 [T= BX` fails: refuting `traces B0 s*`

Each `peelB□?` lemma consumes exactly one event of `s*` from a fixed
source state, using `bloop-ev-inv` to pin the fired event and successor
(discharging the other event of the `□` as impossible) and `τ-peel` to
absorb the loop's silent re-entry.

```agda
peelB0a : ∀ {e s t} → B0 ⟹⟨ lbl a ∷ e ∷ s ⟩ t → B0 ⟹⟨ e ∷ s ⟩ t
peelB0a (⟹-τ stp _) = ⊥-elim (B0-no-τ stp)
peelB0a (⟹-ev stp rest) with bloop-ev-inv (Ret st0) (Ret st1) stp
... | inj₁ (refl , refl) = sil-cont refl rest
... | inj₂ (eq   , _)    = case eq of λ ()

peelB0b : ∀ {e s t} → B0 ⟹⟨ lbl b ∷ e ∷ s ⟩ t → B1 ⟹⟨ e ∷ s ⟩ t
peelB0b (⟹-τ stp _) = ⊥-elim (B0-no-τ stp)
peelB0b (⟹-ev stp rest) with bloop-ev-inv (Ret st0) (Ret st1) stp
... | inj₁ (eq   , _)    = case eq of λ ()
... | inj₂ (refl , refl) = sil-cont refl rest

peelB1a : ∀ {e s t} → B1 ⟹⟨ lbl a ∷ e ∷ s ⟩ t → B0 ⟹⟨ e ∷ s ⟩ t
peelB1a (⟹-τ stp _) = ⊥-elim (B1-no-τ stp)
peelB1a (⟹-ev stp rest) with bloop-ev-inv (Ret st0) Stop stp
... | inj₁ (refl , refl) = sil-cont refl rest
... | inj₂ (eq   , _)    = case eq of λ ()

peelB1b : ∀ {s t} → B1 ⟹⟨ lbl b ∷ s ⟩ t → S2 ⟹⟨ s ⟩ t
peelB1b (⟹-τ stp _) = ⊥-elim (B1-no-τ stp)
peelB1b (⟹-ev stp rest) with bloop-ev-inv (Ret st0) Stop stp
... | inj₁ (eq   , _)    = case eq of λ ()
... | inj₂ (refl , refl) = rest
```

Nine peels walk `B0` through the trace `⟨b,a,b,a,b,a,a,b,b,b⟩`'s first nine
events — `st0 →b→ st1 →a→ st0 →b→ st1 →a→ st0 →b→ st1 →a→ st0 →a→ st0 →b→
st1` — landing on `S2` (two consecutive `b`s consumed) with exactly one
event of `s*` left over; `S2` cannot fire it.

```agda
S2-refuses-last : ∀ {t} → S2 ⟹⟨ lbl b ∷ [] ⟩ t → ⊥
S2-refuses-last (⟹-τ stp _) = loop-stop-no-τ stp
S2-refuses-last (⟹-ev stp _) = loop-stop-no-ev stp

B0-refuses-s* : ¬ traces B0 s*
B0-refuses-s* (_ , tr) = S2-refuses-last tr9
  where
  tr1 = peelB0b tr
  tr2 = peelB1a tr1
  tr3 = peelB0b tr2
  tr4 = peelB1a tr3
  tr5 = peelB0b tr4
  tr6 = peelB1a tr5
  tr7 = peelB0a tr6
  tr8 = peelB0b tr7
  tr9 = peelB1b tr8

¬B0⊑TBX b0⊑bx = B0-refuses-s* (b0⊑bx s* BX-does-s*)
```
