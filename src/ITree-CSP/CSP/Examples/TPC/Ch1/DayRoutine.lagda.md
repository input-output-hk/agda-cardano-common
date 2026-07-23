# TPC/UCS chapter 1: the daily routine (`Day`, `Groundhog_Day`, `Asleep`/`InBed`/`Up`)

The second of five example modules porting chapter-1 processes from A.W.
Roscoe's *Understanding Concurrent Systems* (UCS) to this process-tree
formalisation. Source:

- `fdr-examples/ucs/chapter01/ucs1.csp` (UCS ch. 1, the `Day`/`Groundhog_Day`
  and `Asleep`/`InBed`/`Up` fragments)

This module is **UCS-only** (TPC chapter 1 has no equivalent example).

```csp
channel getup,eat,breakfast,work,lunch,play,dinner,tv,gotobed,sleep,wake,swim,jog,read

Day = getup -> breakfast -> work -> lunch -> play -> dinner ->
      tv -> gotobed -> STOP

Groundhog_Day = getup -> breakfast -> work -> lunch -> play -> dinner ->
                tv -> gotobed -> Groundhog_Day

assert Groundhog_Day [T= Day
assert Day [T= Groundhog_Day

Asleep = sleep -> Asleep
         [] wake -> InBed

InBed = sleep -> Asleep
        [] read -> InBed
        [] tv -> InBed
        [] getup -> Up

Up = gotobed -> InBed
     [] read -> Up
     [] eat -> Up
     [] lunch -> Up
     [] breakfast -> Up
     [] dinner -> Up
     [] tv -> Up
     [] work -> Up
     [] play -> Up

assert InBed [T= Groundhog_Day
assert Up [T= Groundhog_Day
```

§§1–4 port the shapes above onto `PTree` using the `CSP.Operators`
combinators; §5 then states and proves the four FDR asserts (the two
failing ones as negations with explicit witness traces).

## §1. Imports

The fourteen-event alphabet `swim`/`jog` are declared in the `.csp` channel
list but unused by the two process families quoted above (they appear
elsewhere in the source file); we still include them in `Ev` so `Ev-≟`
matches the `.csp` channel declaration exactly. With fourteen constructors, a
hand-written `Ev-≟` would need `14 × 14 = 196` clauses; instead we retract
`AnyTypes Ev` into `Fin 14` and reuse `Data.Fin.Properties._≟_`, which needs
only `14 + 14 + 14 = 42` short clauses (`toFin`, `fromFin`, `retract`).

```agda
{-# OPTIONS --guardedness #-}

module CSP.Examples.TPC.Ch1.DayRoutine where

open import Level using (lift) renaming (zero to lzero)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as Poly
open import Data.Product using (_,_)
open import Data.Fin using (Fin; zero; suc; #_)
import Data.Fin.Properties as FinP
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
open import Class.DecEq using (DecEq; _≟_; Irrelevant⇒DecEq)

open import Process_Trees
```

## §2. The event type

Fourteen nullary visible events, mirroring the `.csp` file's `channel
getup,eat,breakfast,work,lunch,play,dinner,tv,gotobed,sleep,wake,swim,jog,read`.

```agda
data Ev : Set → Set where
  getup eat breakfast work lunch play dinner tv gotobed
    sleep wake swim jog read : Ev ⊤
```

## §3. Decidable equality via a `Fin 14` retract

`toFin` sends each of the fourteen constructors to its index; `fromFin` is
the inverse mapping; `retract` witnesses `fromFin (toFin x) ≡ x` for every
`x` (all fourteen cases hold by `refl`, since `toFin`/`fromFin` compute on
each constructor). `Ev-≟` then transports a `Fin 14` equality decision back
along the retraction. Per the repo's `with`-on-`Fin`-equality technique, we
bind the `yes` case as `| yes p` (not `| yes refl`) and rebuild the equality
with `cong`/`trans`/`sym`, since matching `refl` here would desynchronise
the decision procedure from the indices.

```agda
toFin : AnyTypes Ev → Fin 14
toFin (_ , getup)     = # 0
toFin (_ , eat)       = # 1
toFin (_ , breakfast) = # 2
toFin (_ , work)      = # 3
toFin (_ , lunch)     = # 4
toFin (_ , play)      = # 5
toFin (_ , dinner)    = # 6
toFin (_ , tv)        = # 7
toFin (_ , gotobed)   = # 8
toFin (_ , sleep)     = # 9
toFin (_ , wake)      = # 10
toFin (_ , swim)      = # 11
toFin (_ , jog)       = # 12
toFin (_ , read)      = # 13

fromFin : Fin 14 → AnyTypes Ev
fromFin zero                                   = ⊤ , getup
fromFin (suc zero)                             = ⊤ , eat
fromFin (suc (suc zero))                       = ⊤ , breakfast
fromFin (suc (suc (suc zero)))                 = ⊤ , work
fromFin (suc (suc (suc (suc zero))))           = ⊤ , lunch
fromFin (suc (suc (suc (suc (suc zero)))))     = ⊤ , play
fromFin (suc (suc (suc (suc (suc (suc zero)))))) = ⊤ , dinner
fromFin (suc (suc (suc (suc (suc (suc (suc zero))))))) = ⊤ , tv
fromFin (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = ⊤ , gotobed
fromFin (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = ⊤ , sleep
fromFin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) = ⊤ , wake
fromFin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) = ⊤ , swim
fromFin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) = ⊤ , jog
fromFin (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))) = ⊤ , read

retract : ∀ x → fromFin (toFin x) ≡ x
retract (_ , getup)     = refl
retract (_ , eat)       = refl
retract (_ , breakfast) = refl
retract (_ , work)      = refl
retract (_ , lunch)     = refl
retract (_ , play)      = refl
retract (_ , dinner)    = refl
retract (_ , tv)        = refl
retract (_ , gotobed)   = refl
retract (_ , sleep)     = refl
retract (_ , wake)      = refl
retract (_ , swim)      = refl
retract (_ , jog)       = refl
retract (_ , read)      = refl

Ev-≟ : (x y : AnyTypes Ev) → Dec (x ≡ y)
Ev-≟ x y with toFin x FinP.≟ toFin y
... | yes p = yes (trans (sym (retract x)) (trans (cong fromFin p) (retract y)))
... | no ¬p = no λ { refl → ¬p refl }

open import CSP.Operators Ev-≟
```

`_□_` (needed by `day-step` below, whose branches return `DayState`) is
parametrised by a `DecEq` instance on the return type; `DecEq-DayState` is
supplied in §4. The only other instance required is `DecEq` for the
polymorphic unit type `Poly.⊤ {lzero}`, the return type shared by `Day` and
`GroundhogDay`, following the same `Irrelevant⇒DecEq` idiom as
`CSP.Examples.TPC.Ch1.UpDown`.

```agda
instance
  DecEq-⊤poly : DecEq (Poly.⊤ {lzero})
  DecEq-⊤poly = Irrelevant⇒DecEq (λ { (lift _) (lift _) → refl })
```

## §4. Process definitions

### §4.1 `Day` and `Groundhog_Day`

`dayBody` is the common eight-event chain shared by `Day` (which then
deadlocks, `STOP`) and `Groundhog_Day` (which loops forever, `loop0`).

```agda
DProc : Set₁
DProc = PTree Ev (ExtI Ev) (Poly.⊤ {lzero})

dayBody : PTree Ev (ExtI Ev) (Poly.⊤ {lzero})
dayBody = getup ⟶₀ (breakfast ⟶₀ (work ⟶₀ (lunch ⟶₀ (play ⟶₀
          (dinner ⟶₀ (tv ⟶₀ (gotobed ⟶₀ Skip)))))))

Day : DProc
Day = getup ⟶₀ (breakfast ⟶₀ (work ⟶₀ (lunch ⟶₀ (play ⟶₀
      (dinner ⟶₀ (tv ⟶₀ (gotobed ⟶₀ Stop)))))))

GroundhogDay : DProc
GroundhogDay = loop0 dayBody
```

### §4.2 `Asleep`/`InBed`/`Up`

The three mutually-recursive states of the `.csp` source are encoded as a
single `DayState`-indexed `loop` body (`day-step`), sidestepping the
project's no-`mutual`-blocks convention while preserving the same
transition structure. `Asleep` itself is inlined below as `loop day-step
asleepSt`; the module exports the `InBed` and `Up` instances by name (as
required by later modules), leaving `Asleep` unnamed since nothing in this
chapter references it directly.

```agda
data DayState : Set where
  asleepSt inBedSt upSt : DayState

instance
  DecEq-DayState : DecEq DayState
  DecEq-DayState = record { _≟_ = dec } where
    dec : (x y : DayState) → Dec (x ≡ y)
    dec asleepSt asleepSt = yes refl
    dec inBedSt  inBedSt  = yes refl
    dec upSt     upSt     = yes refl
    dec asleepSt inBedSt  = no λ () ; dec asleepSt upSt    = no λ ()
    dec inBedSt  asleepSt = no λ () ; dec inBedSt  upSt    = no λ ()
    dec upSt     asleepSt = no λ () ; dec upSt     inBedSt = no λ ()
```

`day-step` mirrors the three `.csp` equations directly: `Asleep` offers
`sleep`/`wake`, `InBed` offers `sleep`/`read`/`tv`/`getup`, and `Up` offers
`gotobed` plus the eight while-awake events (`read`, `eat`, `lunch`,
`breakfast`, `dinner`, `tv`, `work`, `play`), each looping back to `upSt`.

```agda
day-step : DayState → PTree Ev (ExtI Ev) DayState
day-step asleepSt = (sleep ⟶₀ Ret asleepSt) □ (wake ⟶₀ Ret inBedSt)
day-step inBedSt  = (sleep ⟶₀ Ret asleepSt) □ ((read ⟶₀ Ret inBedSt)
                  □ ((tv ⟶₀ Ret inBedSt) □ (getup ⟶₀ Ret upSt)))
day-step upSt     = (gotobed ⟶₀ Ret inBedSt) □ ((read ⟶₀ Ret upSt)
                  □ ((eat ⟶₀ Ret upSt) □ ((lunch ⟶₀ Ret upSt)
                  □ ((breakfast ⟶₀ Ret upSt) □ ((dinner ⟶₀ Ret upSt)
                  □ ((tv ⟶₀ Ret upSt) □ ((work ⟶₀ Ret upSt)
                  □ (play ⟶₀ Ret upSt))))))))

InBed : DProc
InBed = loop day-step inBedSt

Up : DProc
Up = loop day-step upSt
```

## §5. Verification

The `.csp` fragment quoted at the top poses four FDR asserts:

```csp
assert Groundhog_Day [T= Day
assert Day [T= Groundhog_Day      -- intended to FAIL
assert InBed [T= Groundhog_Day
assert Up [T= Groundhog_Day       -- FAILS: a discover-it-yourself assert
```

The first holds: `Day` performs one pass of the eight-event chain and then
deadlocks, and `Groundhog_Day` produces every prefix of that pass on its
first loop iteration. The second fails: after `gotobed` the process `Day`
is `STOP`, while `Groundhog_Day` silently re-enters its loop and offers
`getup` again — the nine-event witness trace
`⟨getup,…,gotobed,getup⟩` separates them. The third holds: every position
of `Groundhog_Day` is matched by a state of the `day-step` machine started
at `inBedSt` (`getup` moves it to `upSt`, where the six while-awake events
of the daily round self-loop, and `gotobed` returns it to `inBedSt`). The
fourth is one of the book's **discover-it-yourself** asserts (UCS poses it
expecting the reader to find out that it fails): `Groundhog_Day`'s very
first event is `getup`, and `day-step upSt` — nine branches — never offers
`getup`, so the one-event witness `⟨getup⟩` already refutes it.

The proof machinery is ported from `CSP.Examples.TPC.Ch1.UpDown` §§5–6
(prefix/loop node inversions, weak-simulation refinement, witness-trace
negation, and the factored-out corecursion of `DRFromRel` — here in its
one-directional `WSim` form), re-instantiated at the `Ev` alphabet.

```agda
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (case_of_)
open import Relation.Nullary using (¬_)

open import Semantics.LTS       {E = Ev} {I = ExtI Ev}
open import Semantics.WeakBisim {E = Ev} {I = ExtI Ev}
  using (WSimF; _═[_]═►_; wev; wτ; _─[τ*]─►_; τ*-refl; τ*-step)
open import Semantics.Failures  {E = Ev} {I = ExtI Ev}
  using (_⊑T_; traces; _⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import Semantics.WeakSim   {E = Ev} {I = ExtI Ev}
open import CSP.Laws.Traces.TraceLaws Ev-≟
  using (⟶-trace-elim; Stop-no-τ; Stop-no-ev; Stop-traces-empty)
open import CSP.Laws.Traces.PrefixInversion Ev-≟
  using (⟶₀-no-τ; ⟶₀-ev-inv; sil-no-ev; sil-τ-uniq;
         TEmpty; ∅t-empty; □-mt-empty)
open import Semantics.BisimFromRel {E = Ev} {I = ExtI Ev}
open WSimF
```

All events of the daily round are nullary, so their visible labels share
one shape, abbreviated `lbl`:

```agda
lbl : Ev ⊤ → Event√ (Poly.⊤ {lzero})
lbl e = evl (evLabel ⊤ e tt)
```

### §5.1 The FDR asserts

```agda
-- assert Groundhog_Day [T= Day   (holds)
GD⊑TDay : GroundhogDay ⊑T Day

-- assert Day [T= Groundhog_Day   (FAILS, as UCS intends)
¬Day⊑TGD : ¬ (Day ⊑T GroundhogDay)

-- assert InBed [T= Groundhog_Day   (holds)
InBed⊑TGD : InBed ⊑T GroundhogDay

-- assert Up [T= Groundhog_Day   (FAILS: UCS's discover-it-yourself assert)
¬Up⊑TGD : ¬ (Up ⊑T GroundhogDay)
```

### §5.2 Node-level scaffolding

A pure prefix node is stable and fires exactly its own event
(`Prefix-cont-fires`, `⟶₀-no-τ`, `⟶₀-ev-inv`); and a `sil`-headed state
offers no visible event and takes exactly one τ, to the named successor
(`sil-no-ev`, `sil-τ-uniq`). These are imported from
`CSP.Laws.Traces.PrefixInversion` in the §5 block above. A *stable* loop
state of the shape `iter-bind ((ce ⟶₀ X) >>= inj₁-Ret) K` likewise fires
exactly `ce`, with successor `iter-bind (X >>= inj₁-Ret) K` (`loop-ev-inv`,
`loop-no-τ`, stated below on the nullary `_⟶₀_` sugar; the shared module's
`loop-pfx-*` versions invert the payload-carrying `_⟶_` shape instead).

```agda
loop-ev-inv : ∀ {A : Set} (ce : Ev ⊤) (X : PTree Ev (ExtI Ev) A)
                (K : A → PTree Ev (ExtI Ev) (A ⊎ Poly.⊤ {lzero}))
                {l : Event√ (Poly.⊤ {lzero})} {t′ : DProc}
            → iter-bind ((ce ⟶₀ X) >>= (λ a′ → Ret (inj₁ a′))) K ─[ ev l ]─► t′
            → (l ≡ lbl ce)
              × (t′ ≡ iter-bind (X >>= (λ a′ → Ret (inj₁ a′))) K)
loop-ev-inv ce X K (sRet eq) = case eq of λ ()
loop-ev-inv ce X K (sVis {at = at} {a = a} refl br) with Ev-≟ (⊤ , ce) at
... | yes refl = refl , sym (just-injective br)
... | no ¬eq   = ⊥-elim (case br of λ ())

loop-no-τ : ∀ {A : Set} (ce : Ev ⊤) (X : PTree Ev (ExtI Ev) A)
              (K : A → PTree Ev (ExtI Ev) (A ⊎ Poly.⊤ {lzero})) {t′ : DProc}
          → iter-bind ((ce ⟶₀ X) >>= (λ a′ → Ret (inj₁ a′))) K ─[ τ ]─► t′ → ⊥
loop-no-τ ce X K (sSil eq)      = case eq of λ ()
loop-no-τ ce X K (sTau refl br) = case br of λ ()
```

### §5.3 The reachable states of `Day` and `GroundhogDay`

`Day` passes through nine sequential states; we name the seven inner ones
(the first is `Day` itself, the last is `Stop`). `Day ≡ getup ⟶₀ D₁`
holds definitionally.

```agda
D₁ D₂ D₃ D₄ D₅ D₆ D₇ : DProc
D₇ = gotobed ⟶₀ Stop
D₆ = tv ⟶₀ D₇
D₅ = dinner ⟶₀ D₆
D₄ = play ⟶₀ D₅
D₃ = lunch ⟶₀ D₄
D₂ = work ⟶₀ D₃
D₁ = breakfast ⟶₀ D₂
```

`GroundhogDay = loop0 dayBody` unfolds to `iter-bind (dayBody >>= inj₁-Ret)
gdK`, where `gdK` re-enters the loop. Its states are the `iter-bind` terms
over the successive tails `B₁ … B₈` of `dayBody` (so `dayBody ≡ getup ⟶₀
B₁` definitionally); `GD₈` is the silent re-entry state, whose `sil` lands
back on `GroundhogDay` itself.

```agda
B₁ B₂ B₃ B₄ B₅ B₆ B₇ B₈ : PTree Ev (ExtI Ev) (Poly.⊤ {lzero})
B₈ = Skip
B₇ = gotobed ⟶₀ B₈
B₆ = tv ⟶₀ B₇
B₅ = dinner ⟶₀ B₆
B₄ = play ⟶₀ B₅
B₃ = lunch ⟶₀ B₄
B₂ = work ⟶₀ B₃
B₁ = breakfast ⟶₀ B₂

gdK : Poly.⊤ {lzero} → PTree Ev (ExtI Ev) (Poly.⊤ {lzero} ⊎ Poly.⊤ {lzero})
gdK _ = dayBody >>= (λ a′ → Ret (inj₁ a′))

GD₁ GD₂ GD₃ GD₄ GD₅ GD₆ GD₇ GD₈ : DProc
GD₁ = iter-bind (B₁ >>= (λ a′ → Ret (inj₁ a′))) gdK
GD₂ = iter-bind (B₂ >>= (λ a′ → Ret (inj₁ a′))) gdK
GD₃ = iter-bind (B₃ >>= (λ a′ → Ret (inj₁ a′))) gdK
GD₄ = iter-bind (B₄ >>= (λ a′ → Ret (inj₁ a′))) gdK
GD₅ = iter-bind (B₅ >>= (λ a′ → Ret (inj₁ a′))) gdK
GD₆ = iter-bind (B₆ >>= (λ a′ → Ret (inj₁ a′))) gdK
GD₇ = iter-bind (B₇ >>= (λ a′ → Ret (inj₁ a′))) gdK
GD₈ = iter-bind (B₈ >>= (λ a′ → Ret (inj₁ a′))) gdK
```

All of `GroundhogDay`'s strong steps hold by `refl` (as in `UpDown` §5.4):
the offer maps of the `iter-bind`/`>>=` nodes compute, and `GD₈`'s `sil`
re-entry lands (definitionally) back on `GroundhogDay`.

```agda
GD-getup      : GroundhogDay ─[ ev (lbl getup) ]─► GD₁
GD-getup      = sVis {at = ⊤ , getup} {a = tt} refl refl

GD₁-breakfast : GD₁ ─[ ev (lbl breakfast) ]─► GD₂
GD₁-breakfast = sVis {at = ⊤ , breakfast} {a = tt} refl refl

GD₂-work      : GD₂ ─[ ev (lbl work) ]─► GD₃
GD₂-work      = sVis {at = ⊤ , work} {a = tt} refl refl

GD₃-lunch     : GD₃ ─[ ev (lbl lunch) ]─► GD₄
GD₃-lunch     = sVis {at = ⊤ , lunch} {a = tt} refl refl

GD₄-play      : GD₄ ─[ ev (lbl play) ]─► GD₅
GD₄-play      = sVis {at = ⊤ , play} {a = tt} refl refl

GD₅-dinner    : GD₅ ─[ ev (lbl dinner) ]─► GD₆
GD₅-dinner    = sVis {at = ⊤ , dinner} {a = tt} refl refl

GD₆-tv        : GD₆ ─[ ev (lbl tv) ]─► GD₇
GD₆-tv        = sVis {at = ⊤ , tv} {a = tt} refl refl

GD₇-gotobed   : GD₇ ─[ ev (lbl gotobed) ]─► GD₈
GD₇-gotobed   = sVis {at = ⊤ , gotobed} {a = tt} refl refl

GD₈-τ         : GD₈ ─[ τ ]─► GroundhogDay
GD₈-τ         = sSil refl
```

### §5.4 `assert Groundhog_Day [T= Day`: a weak simulation of `Day` by `GroundhogDay`

Each of `Day`'s nine states is matched inside `GroundhogDay`'s single loop
pass: state `Dᵢ` ↦ `GDᵢ`, and the final `Stop` ↦ `GD₈`, vacuously (a
`Stop` state has no steps to match; `GD₈`'s pending loop re-entry is never
needed). The chain is acyclic — `sim₈` down to `sim₀` are plain
definitions, no corecursion needed (exactly `UpDown` §5.5, with nine
states instead of five).

```agda
sim₈ : WSim (Poly.⊤ {lzero}) Stop GD₈
sim₈ .fwd .on-ev  stp = ⊥-elim (Stop-no-ev stp)
sim₈ .fwd .on-tau stp = ⊥-elim (Stop-no-τ  stp)

sim₇ : WSim (Poly.⊤ {lzero}) D₇ GD₇
sim₇ .fwd .on-ev stp with ⟶₀-ev-inv stp
... | _ , refl , refl = GD₈ , wev τ*-refl GD₇-gotobed τ*-refl , sim₈
sim₇ .fwd .on-tau stp = ⊥-elim (⟶₀-no-τ stp)

sim₆ : WSim (Poly.⊤ {lzero}) D₆ GD₆
sim₆ .fwd .on-ev stp with ⟶₀-ev-inv stp
... | _ , refl , refl = GD₇ , wev τ*-refl GD₆-tv τ*-refl , sim₇
sim₆ .fwd .on-tau stp = ⊥-elim (⟶₀-no-τ stp)

sim₅ : WSim (Poly.⊤ {lzero}) D₅ GD₅
sim₅ .fwd .on-ev stp with ⟶₀-ev-inv stp
... | _ , refl , refl = GD₆ , wev τ*-refl GD₅-dinner τ*-refl , sim₆
sim₅ .fwd .on-tau stp = ⊥-elim (⟶₀-no-τ stp)

sim₄ : WSim (Poly.⊤ {lzero}) D₄ GD₄
sim₄ .fwd .on-ev stp with ⟶₀-ev-inv stp
... | _ , refl , refl = GD₅ , wev τ*-refl GD₄-play τ*-refl , sim₅
sim₄ .fwd .on-tau stp = ⊥-elim (⟶₀-no-τ stp)

sim₃ : WSim (Poly.⊤ {lzero}) D₃ GD₃
sim₃ .fwd .on-ev stp with ⟶₀-ev-inv stp
... | _ , refl , refl = GD₄ , wev τ*-refl GD₃-lunch τ*-refl , sim₄
sim₃ .fwd .on-tau stp = ⊥-elim (⟶₀-no-τ stp)

sim₂ : WSim (Poly.⊤ {lzero}) D₂ GD₂
sim₂ .fwd .on-ev stp with ⟶₀-ev-inv stp
... | _ , refl , refl = GD₃ , wev τ*-refl GD₂-work τ*-refl , sim₃
sim₂ .fwd .on-tau stp = ⊥-elim (⟶₀-no-τ stp)

sim₁ : WSim (Poly.⊤ {lzero}) D₁ GD₁
sim₁ .fwd .on-ev stp with ⟶₀-ev-inv stp
... | _ , refl , refl = GD₂ , wev τ*-refl GD₁-breakfast τ*-refl , sim₂
sim₁ .fwd .on-tau stp = ⊥-elim (⟶₀-no-τ stp)

sim₀ : WSim (Poly.⊤ {lzero}) Day GroundhogDay
sim₀ .fwd .on-ev stp with ⟶₀-ev-inv stp
... | _ , refl , refl = GD₁ , wev τ*-refl GD-getup τ*-refl , sim₁
sim₀ .fwd .on-tau stp = ⊥-elim (⟶₀-no-τ stp)

GD⊑TDay = wsim→⊑T sim₀
```

### §5.5 `assert Day [T= Groundhog_Day` fails: the witness trace

`s* = ⟨getup,breakfast,work,lunch,play,dinner,tv,gotobed,getup⟩` is a trace
of `GroundhogDay` (one full pass, the silent loop re-entry, then the first
event of the second pass) but not of `Day` (after eight events `Day` is
`Stop`, which refuses everything). The refutation peels the eight prefixes
off `Day` with `⟶-trace-elim` and then refutes the ninth event on `Stop`.

```agda
s* : List (Event√ (Poly.⊤ {lzero}))
s* = lbl getup ∷ lbl breakfast ∷ lbl work ∷ lbl lunch ∷ lbl play
   ∷ lbl dinner ∷ lbl tv ∷ lbl gotobed ∷ lbl getup ∷ []

GD-does-s* : traces GroundhogDay s*
GD-does-s* = GD₁ ,
  ⟹-ev GD-getup (⟹-ev GD₁-breakfast (⟹-ev GD₂-work (⟹-ev GD₃-lunch
  (⟹-ev GD₄-play (⟹-ev GD₅-dinner (⟹-ev GD₆-tv (⟹-ev GD₇-gotobed
  (⟹-τ GD₈-τ (⟹-ev GD-getup ⟹-refl)))))))))

Day-refuses-s* : ¬ traces Day s*
Day-refuses-s* tr₀ with ⟶-trace-elim getup (λ _ → D₁) tr₀
... | inj₁ ()
... | inj₂ (_ , _ , refl , tr₁) with ⟶-trace-elim breakfast (λ _ → D₂) tr₁
...   | inj₁ ()
...   | inj₂ (_ , _ , refl , tr₂) with ⟶-trace-elim work (λ _ → D₃) tr₂
...     | inj₁ ()
...     | inj₂ (_ , _ , refl , tr₃) with ⟶-trace-elim lunch (λ _ → D₄) tr₃
...       | inj₁ ()
...       | inj₂ (_ , _ , refl , tr₄) with ⟶-trace-elim play (λ _ → D₅) tr₄
...         | inj₁ ()
...         | inj₂ (_ , _ , refl , tr₅) with ⟶-trace-elim dinner (λ _ → D₆) tr₅
...           | inj₁ ()
...           | inj₂ (_ , _ , refl , tr₆) with ⟶-trace-elim tv (λ _ → D₇) tr₆
...             | inj₁ ()
...             | inj₂ (_ , _ , refl , tr₇) with ⟶-trace-elim gotobed (λ _ → Stop) tr₇
...               | inj₁ ()
...               | inj₂ (_ , _ , refl , tr₈) = case Stop-traces-empty tr₈ of λ ()

¬Day⊑TGD d⊑gd = Day-refuses-s* (d⊑gd s* GD-does-s*)
```

### §5.6 `assert InBed [T= Groundhog_Day`: simulating the loop in the state machine

Here the *simulated* process (`GroundhogDay`) is the infinite loop, so the
weak simulation is cyclic and its `WSim` proof must be corecursive. The
corecursion is factored out once, in the shared `WSimFromRel` principle
imported from `Semantics.BisimFromRel`: any binary relation whose pairs
match the left component's strong steps by weak steps of the right,
staying in the relation, is contained in a weak simulation. All the real
work then happens in plain, non-corecursive case analyses on the relation;
every corecursive call sits directly under the record copatterns, so
guardedness is immediate.

The `day-step` machine's relevant states: `InBed` and `Up` themselves,
plus the two silent way-stations reached after firing an event — the loop
body has returned the next `DayState` and is about to re-enter (`toUp`
after any event leading to `upSt`, `toInBed` after `gotobed`).

```agda
dsK : DayState → PTree Ev (ExtI Ev) (DayState ⊎ Poly.⊤ {lzero})
dsK s = day-step s >>= (λ s′ → Ret (inj₁ s′))

toUp toInBed : DProc
toUp    = iter-bind (Ret upSt    >>= (λ s′ → Ret (inj₁ s′))) dsK
toInBed = iter-bind (Ret inBedSt >>= (λ s′ → Ret (inj₁ s′))) dsK
```

The machine's strong steps all hold by `refl`: the nested `□`s of
`day-step` force to a single `react` node whose merged offer map
(`mergeVis`/`mergeMaybe`) *computes* on each closed event, selecting the
correct branch of the choice — so no dedicated `□`-introduction lemma is
needed, exactly as for the plain prefix loops of §5.3.

```agda
IB-getup     : InBed ─[ ev (lbl getup) ]─► toUp
IB-getup     = sVis {at = ⊤ , getup} {a = tt} refl refl

Up-breakfast : Up ─[ ev (lbl breakfast) ]─► toUp
Up-breakfast = sVis {at = ⊤ , breakfast} {a = tt} refl refl

Up-work      : Up ─[ ev (lbl work) ]─► toUp
Up-work      = sVis {at = ⊤ , work} {a = tt} refl refl

Up-lunch     : Up ─[ ev (lbl lunch) ]─► toUp
Up-lunch     = sVis {at = ⊤ , lunch} {a = tt} refl refl

Up-play      : Up ─[ ev (lbl play) ]─► toUp
Up-play      = sVis {at = ⊤ , play} {a = tt} refl refl

Up-dinner    : Up ─[ ev (lbl dinner) ]─► toUp
Up-dinner    = sVis {at = ⊤ , dinner} {a = tt} refl refl

Up-tv        : Up ─[ ev (lbl tv) ]─► toUp
Up-tv        = sVis {at = ⊤ , tv} {a = tt} refl refl

Up-gotobed   : Up ─[ ev (lbl gotobed) ]─► toInBed
Up-gotobed   = sVis {at = ⊤ , gotobed} {a = tt} refl refl

toUp-τ       : toUp ─[ τ ]─► Up
toUp-τ       = sSil refl

toInBed-τ    : toInBed ─[ τ ]─► InBed
toInBed-τ    = sSil refl
```

The relation: `GroundhogDay`'s start and its silent re-entry state `GD₈`
↦ `InBed` (which offers `getup`); the positions after `getup` … after `tv`
↦ `Up`. Each visible answer fires the corresponding `day-step` offer and
absorbs the machine's own loop re-entry `sil` in the trailing `τ*`; `GD₈`'s
τ is answered by `InBed` standing still.

```agda
data RGD : DProc → DProc → Set₁ where
  g₀ : RGD GroundhogDay InBed
  g₁ : RGD GD₁ Up
  g₂ : RGD GD₂ Up
  g₃ : RGD GD₃ Up
  g₄ : RGD GD₄ Up
  g₅ : RGD GD₅ Up
  g₆ : RGD GD₆ Up
  g₇ : RGD GD₇ Up
  g₈ : RGD GD₈ InBed

RGD-fwd-ev : ∀ {p q} {l : Event√ (Poly.⊤ {lzero})} {p′} → RGD p q → p ─[ ev l ]─► p′
           → Σ[ q′ ∈ DProc ] ((q ═[ ev l ]═► q′) × RGD p′ q′)
RGD-fwd-ev g₀ stp with loop-ev-inv getup B₁ gdK stp
... | refl , refl = Up , wev τ*-refl IB-getup (τ*-step toUp-τ τ*-refl) , g₁
RGD-fwd-ev g₁ stp with loop-ev-inv breakfast B₂ gdK stp
... | refl , refl = Up , wev τ*-refl Up-breakfast (τ*-step toUp-τ τ*-refl) , g₂
RGD-fwd-ev g₂ stp with loop-ev-inv work B₃ gdK stp
... | refl , refl = Up , wev τ*-refl Up-work (τ*-step toUp-τ τ*-refl) , g₃
RGD-fwd-ev g₃ stp with loop-ev-inv lunch B₄ gdK stp
... | refl , refl = Up , wev τ*-refl Up-lunch (τ*-step toUp-τ τ*-refl) , g₄
RGD-fwd-ev g₄ stp with loop-ev-inv play B₅ gdK stp
... | refl , refl = Up , wev τ*-refl Up-play (τ*-step toUp-τ τ*-refl) , g₅
RGD-fwd-ev g₅ stp with loop-ev-inv dinner B₆ gdK stp
... | refl , refl = Up , wev τ*-refl Up-dinner (τ*-step toUp-τ τ*-refl) , g₆
RGD-fwd-ev g₆ stp with loop-ev-inv tv B₇ gdK stp
... | refl , refl = Up , wev τ*-refl Up-tv (τ*-step toUp-τ τ*-refl) , g₇
RGD-fwd-ev g₇ stp with loop-ev-inv gotobed B₈ gdK stp
... | refl , refl = InBed , wev τ*-refl Up-gotobed (τ*-step toInBed-τ τ*-refl) , g₈
RGD-fwd-ev g₈ stp = ⊥-elim (sil-no-ev refl stp)

RGD-fwd-τ : ∀ {p q p′} → RGD p q → p ─[ τ ]─► p′
          → Σ[ q′ ∈ DProc ] ((q ═[ τ ]═► q′) × RGD p′ q′)
RGD-fwd-τ g₀ stp = ⊥-elim (loop-no-τ getup B₁ gdK stp)
RGD-fwd-τ g₁ stp = ⊥-elim (loop-no-τ breakfast B₂ gdK stp)
RGD-fwd-τ g₂ stp = ⊥-elim (loop-no-τ work B₃ gdK stp)
RGD-fwd-τ g₃ stp = ⊥-elim (loop-no-τ lunch B₄ gdK stp)
RGD-fwd-τ g₄ stp = ⊥-elim (loop-no-τ play B₅ gdK stp)
RGD-fwd-τ g₅ stp = ⊥-elim (loop-no-τ dinner B₆ gdK stp)
RGD-fwd-τ g₆ stp = ⊥-elim (loop-no-τ tv B₇ gdK stp)
RGD-fwd-τ g₇ stp = ⊥-elim (loop-no-τ gotobed B₈ gdK stp)
RGD-fwd-τ g₈ stp with sil-τ-uniq refl stp
... | refl = InBed , wτ τ*-refl , g₀

module MGD = WSimFromRel RGD RGD-fwd-ev RGD-fwd-τ

InBed⊑TGD = wsim→⊑T (MGD.rel→wsim g₀)
```

### §5.7 `assert Up [T= Groundhog_Day` fails: `upSt` never offers `getup`

The one-event witness `⟨getup⟩` is a trace of `GroundhogDay` (its very
first offer) but not of `Up`. Refuting it needs two facts about the state
`Up`: it takes no τ-step, and it does not offer `getup`.

The second is pure computation: on the *closed* event `getup` the merged
offer map of `day-step upSt`'s nine branches reduces to `nothing`, so the
branch equation of a purported `sVis` step is absurd. The first needs a
little more care than `loop-no-τ`: a plain prefix loop state's τ-part is
literally `∅t`, which reduces to `nothing` even on an *open* τ-index,
whereas the `□` composite's τ-part is `□-mt`, which pattern-matches on the
index — so its emptiness is proved by index case analysis (`□-mt-empty`),
propagated through the eight nested `□`s of `day-step upSt`, and finally
transported under the `>>=`/`iter-bind` wrappers by re-doing the stuck
`with`-match (the `▷-slide-τ-eq` idiom).

```agda
-- the τ-part of day-step upSt is empty: chain □-mt-empty through the 8 nested □s
upStep-τ-empty : TEmpty (viewT (PTree.force (day-step upSt)))
upStep-τ-empty =
  □-mt-empty ∅t-empty (□-mt-empty ∅t-empty (□-mt-empty ∅t-empty
  (□-mt-empty ∅t-empty (□-mt-empty ∅t-empty (□-mt-empty ∅t-empty
  (□-mt-empty ∅t-empty (□-mt-empty ∅t-empty ∅t-empty)))))))

Up-no-τ : ∀ {t′ : DProc} → Up ─[ τ ]─► t′ → ⊥
Up-no-τ (sSil eq) = case eq of λ ()
Up-no-τ (sTau {i = i} {a = a} refl br)
  with viewT (PTree.force (day-step upSt)) i a | upStep-τ-empty i a
... | just _  | ()
... | nothing | refl = case br of λ ()

Up-no-getup : ∀ {q : DProc} → Up ─[ ev (lbl getup) ]─► q → ⊥
Up-no-getup (sVis refl ())

GD-does-getup : traces GroundhogDay (lbl getup ∷ [])
GD-does-getup = GD₁ , ⟹-ev GD-getup ⟹-refl

Up-refuses-getup : ¬ traces Up (lbl getup ∷ [])
Up-refuses-getup (_ , ⟹-τ  stp _) = Up-no-τ stp
Up-refuses-getup (_ , ⟹-ev stp _) = Up-no-getup stp

¬Up⊑TGD up⊑gd = Up-refuses-getup (up⊑gd (lbl getup ∷ []) GD-does-getup)
```
