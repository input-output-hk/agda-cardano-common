# UCS chapter 3: Peter and Maggie deadlock under full synchronisation

A "UCS" example, porting the Peter/Maggie morning-routine processes from A.W.
Roscoe's *Understanding Concurrent Systems* (UCS), chapter 3, machine-readable
companion file:

- `fdr-examples/ucs/chapter03/ucs3.csp` (UCS ch. 3)

Peter and Maggie each get up, then — in some order — do their exercise (Peter
jogs, Maggie swims) and eat breakfast, before proceeding with the rest of the
day (`Up`):

```csp
Peter  = getup -> ((jog  -> breakfast -> Up) [] (breakfast -> jog  -> Up))
Maggie = getup -> ((swim -> breakfast -> Up) [] (breakfast -> swim -> Up))
Events = {getup, breakfast, jog, swim, ...}

assert Peter [| Events |] Maggie :[deadlock free]   -- FAILS in FDR
```

**Why the full-synchronisation composition deadlocks.** Under full
synchronisation on the whole alphabet `Events`, *every* event must be offered by
*both* operands. Both offer `getup`, so it fires. Both are now at their `[]`
choice; the only event jointly enabled there is `breakfast` (Peter also offers
`jog`, Maggie also offers `swim`, but those are not shared), so `breakfast`
fires. Now Peter is committed to `jog` and Maggie is committed to `swim` —
neither event is offered by both, so the composite refuses everything: a
genuine **deadlock**. FDR's `:[deadlock free]` assertion on the full-sync
composition therefore *fails*; we prove the dual, `HasDeadlock`, exhibiting the
√-free trace `⟨getup, breakfast⟩` to a stuck state (and derive
`¬ DeadlockFree`).

A later companion result shows that the *alphabetised* parallel (Peter owning
`jog`, Maggie owning `swim`, only `getup`/`breakfast` shared) is instead
deadlock-free; the definitions here are shared with that development.

## §1. Imports

```agda
{-# OPTIONS --guardedness #-}

module CSP.Examples.UCS.Ch3.PeterMaggie where

open import Level renaming (zero to lzero)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; Irrelevant⇒DecEq)

open import Process_Trees
open PTree
```

## §2. The event type

`getup`, `breakfast`, `jog`, `swim` are the events Peter and Maggie use; `read`
is a single stand-in event for the "rest of the day" loop `Up`. All are nullary
visible events at the (propositionally irrelevant) payload `⊤poly {lzero}`.

```agda
data DEv : Set → Set where
  getup breakfast jog swim read : DEv (⊤poly {lzero})
```

## §3. Decidable equality

```agda
DEv-≟ : (x y : AnyTypes DEv) → Dec (x ≡ y)
DEv-≟ (_ , getup)     (_ , getup)     = yes refl
DEv-≟ (_ , breakfast) (_ , breakfast) = yes refl
DEv-≟ (_ , jog)       (_ , jog)       = yes refl
DEv-≟ (_ , swim)      (_ , swim)      = yes refl
DEv-≟ (_ , read)      (_ , read)      = yes refl
DEv-≟ (_ , getup)     (_ , breakfast) = no λ ()
DEv-≟ (_ , getup)     (_ , jog)       = no λ ()
DEv-≟ (_ , getup)     (_ , swim)      = no λ ()
DEv-≟ (_ , getup)     (_ , read)      = no λ ()
DEv-≟ (_ , breakfast) (_ , getup)     = no λ ()
DEv-≟ (_ , breakfast) (_ , jog)       = no λ ()
DEv-≟ (_ , breakfast) (_ , swim)      = no λ ()
DEv-≟ (_ , breakfast) (_ , read)      = no λ ()
DEv-≟ (_ , jog)       (_ , getup)     = no λ ()
DEv-≟ (_ , jog)       (_ , breakfast) = no λ ()
DEv-≟ (_ , jog)       (_ , swim)      = no λ ()
DEv-≟ (_ , jog)       (_ , read)      = no λ ()
DEv-≟ (_ , swim)      (_ , getup)     = no λ ()
DEv-≟ (_ , swim)      (_ , breakfast) = no λ ()
DEv-≟ (_ , swim)      (_ , jog)       = no λ ()
DEv-≟ (_ , swim)      (_ , read)      = no λ ()
DEv-≟ (_ , read)      (_ , getup)     = no λ ()
DEv-≟ (_ , read)      (_ , breakfast) = no λ ()
DEv-≟ (_ , read)      (_ , jog)       = no λ ()
DEv-≟ (_ , read)      (_ , swim)      = no λ ()

open import CSP.Operators DEv-≟
open EventSet
```

`⊤poly {lzero}` is `Lift ⊤`, propositionally irrelevant, so its `DecEq` is
trivial (the same `Irrelevant⇒DecEq` idiom as the other examples). External
choice `_□_` needs it for the return type.

```agda
instance
  DecEq-⊤poly : DecEq (⊤poly {lzero})
  DecEq-⊤poly = Irrelevant⇒DecEq (λ { (lift _) (lift _) → refl })
```

## §4. The processes

```agda
DProc : Set₁
DProc = PTree DEv (ExtI DEv) (⊤poly {lzero})
```

### §4.1 The full-synchronisation alphabet `Events`

Every `DEv` event lives at the payload type `⊤poly {lzero}`, so *all* events are
members: `Events` is the total event set (its `mem` predicate is always the
inhabited `⊤poly`, decided by `yes tt`).

```agda
Events : EventSet
Events .mem at x = ⊤poly {lzero}
Events .dec at x = yes tt
```

### §4.2 `Up`, `Peter`, `Maggie`

`Up` is a minimal always-progressing stand-in for the rest of the day; it is
never reached here (the deadlock precedes it). The residual states after the
first two events are named for reuse in the step lemmas below: `Wj = jog -> Up`
(Peter's forced next move) and `Ws = swim -> Up` (Maggie's).

```agda
Up : DProc
Up = loop0 (read ⟶₀ Skip)

Wj Ws : DProc
Wj = jog  ⟶₀ Up
Ws = swim ⟶₀ Up

Pbody Mbody : DProc
Pbody = (jog  ⟶₀ (breakfast ⟶₀ Up)) □ (breakfast ⟶₀ Wj)
Mbody = (swim ⟶₀ (breakfast ⟶₀ Up)) □ (breakfast ⟶₀ Ws)

Peter Maggie : DProc
Peter  = getup ⟶₀ Pbody
Maggie = getup ⟶₀ Mbody
```

## §5. Verification machinery

```agda
open import Semantics.LTS      {E = DEv} {I = ExtI DEv}
open import Semantics.Deadlock {E = DEv} {I = ExtI DEv}
  using ( IsStuck; HasDeadlock; DeadlockFree
        ; _⟹∖√⟨_⟩_; ∖√-refl; ∖√-ev; hasDeadlock⇒¬deadlockFree )
open import CSP.Laws.Traces.PrefixInversion DEv-≟
  using (⟶₀-ev-inv; ⟶₀-no-τ)
open import CSP.Laws.Traces.TraceLawsParallel DEv-≟
  using (Par-sync)
open import CSP.Laws.Traces.TraceLawsParallelElim DEv-≟
  using (Par-ev-elim; evSync; evL; evR; evBoth; ev√; Par-τ-elim; τL; τR)
```

The two events on the deadlocking trace, at the (irrelevant) payload `tt`:

```agda
evGetup evBreakfast : Event
evGetup     = evLabel (⊤poly {lzero}) getup     tt
evBreakfast = evLabel (⊤poly {lzero}) breakfast tt
```

### §5.1 Operand steps

`Peter`/`Maggie` fire `getup` into their `□` bodies; each body then fires
`breakfast` (its only enabled event that the other operand can also match) into
Peter's `jog`-commitment `Wj` / Maggie's `swim`-commitment `Ws`. All hold by
`refl` (the prefix offer maps and the `□` merge compute definitionally).

```agda
peter-getup : Peter ─[ ev (evl evGetup) ]─► Pbody
peter-getup = sVis {at = ⊤poly {lzero} , getup} {a = tt} refl refl

maggie-getup : Maggie ─[ ev (evl evGetup) ]─► Mbody
maggie-getup = sVis {at = ⊤poly {lzero} , getup} {a = tt} refl refl

pbody-breakfast : Pbody ─[ ev (evl evBreakfast) ]─► Wj
pbody-breakfast = sVis {at = ⊤poly {lzero} , breakfast} {a = tt} refl refl

mbody-breakfast : Mbody ─[ ev (evl evBreakfast) ]─► Ws
mbody-breakfast = sVis {at = ⊤poly {lzero} , breakfast} {a = tt} refl refl
```

### §5.2 The deadlocked state and the reaching trace

`W` is the state after `⟨getup, breakfast⟩`: Peter must `jog`, Maggie must
`swim`, and under full synchronisation neither is jointly offered. The reach
uses `Par-sync` twice (both operands offer `getup`, then both offer
`breakfast`), since both events are in the total `Events`.

```agda
W : DProc
W = Par⊤ Events Wj Ws

reach-getup : Par⊤ Events Peter Maggie ─[ ev (evl evGetup) ]─► Par⊤ Events Pbody Mbody
reach-getup = Par-sync Events _ Peter Maggie tt peter-getup maggie-getup

reach-breakfast : Par⊤ Events Pbody Mbody ─[ ev (evl evBreakfast) ]─► W
reach-breakfast = Par-sync Events _ Pbody Mbody tt pbody-breakfast mbody-breakfast

reach : Par⊤ Events Peter Maggie ⟹∖√⟨ evGetup ∷ evBreakfast ∷ [] ⟩ W
reach = ∖√-ev reach-getup (∖√-ev reach-breakfast ∖√-refl)
```

### §5.3 `W` is stuck

No transition of `W` is possible. A visible step, inverted by `Par-ev-elim`, is
either a solo/both move outside `Events` (impossible — `Events` is total, so its
non-membership witness `¬m tt` is absurd), a joint `√` (impossible — neither
operand is at `ret`), or a synchronisation (impossible — it would require Peter
and Maggie to fire the *same* event, but Peter offers only `jog` and Maggie only
`swim`). A `τ`-step, inverted by `Par-τ-elim`, would be an operand `τ`, but each
operand is a stable prefix (`⟶₀-no-τ`).

```agda
stuck : IsStuck W
stuck {l = ev _} step with Par-ev-elim Events _ Wj Ws step
... | evL ¬m _      = ¬m tt
... | evR ¬m _      = ¬m tt
... | evBoth ¬m _ _ = ¬m tt
... | ev√ fp _      = case fp of λ ()
... | evSync _ pStep qStep with ⟶₀-ev-inv pStep
...   | _ , refl , _ with ⟶₀-ev-inv qStep
...     | _ , eqbad , _ = case eqbad of λ ()
stuck {l = τ} step with Par-τ-elim Events _ Wj Ws step
... | τL _ pτ _ = ⟶₀-no-τ pτ
... | τR _ qτ _ = ⟶₀-no-τ qτ
```

### §5.4 The deadlock theorem

```agda
peterMaggie-deadlocks : HasDeadlock (Par⊤ Events Peter Maggie)
peterMaggie-deadlocks = evGetup ∷ evBreakfast ∷ [] , W , reach , stuck

¬pm-deadlockFree : ¬ DeadlockFree (Par⊤ Events Peter Maggie)
¬pm-deadlockFree = hasDeadlock⇒¬deadlockFree peterMaggie-deadlocks
```

The full-synchronisation `Peter [| Events |] Maggie :[deadlock free]` assertion
therefore fails, exactly as FDR reports.

## §6. The alphabetised parallel is deadlock-free

We now prove the *complement* result on a **finite family that preserves the
`□` choice**: under **alphabetised** parallel, where `jog` belongs to Peter's
alphabet only and `swim` to Maggie's only (so each may perform its exercise
*solo*, without the other's participation), the composition is
**deadlock-free**.  Only the truly shared events `getup`/`breakfast`
synchronise.

```csp
AP = Events ∖ {swim}   -- = {getup, breakfast, jog, read}
AM = Events ∖ {jog}    -- = {getup, breakfast, swim, read}

assert PeterDF [ AP || AM ] MaggieDF :[deadlock free]   -- HOLDS in FDR
```

Under `_⟦ AP ∥ AM ⟧_` the routing is: `getup`/`breakfast`/`read` in both
alphabets (synchronise), `jog ∈ AP ∖ AM` (Peter-solo), `swim ∈ AM ∖ AP`
(Maggie-solo).  This is precisely why the alphabetised composition escapes the
full-sync deadlock: after `getup`, Peter can `jog` on its own and Maggie can
`swim` on its own — no state ever refuses *every* event.

### §6.0 The finite family (retains `□`; only `Up ↦ Skip`)

To keep the reachable-state set **finite** (the `read`-loop `Up = loop0 …` of
§4.2 unfolds via τ forever, forcing a genuinely coinductive reachability
argument), we prove both results on a **loop-free** variant that **retains every
essential feature** of §4.2 — in particular the external-choice ordering `□`
between exercise-first and breakfast-first — replacing *only* the `read`-loop
tail `Up` by `Skip` (finite termination):

```text
PeterDF  = getup ⟶ ((jog  ⟶ breakfast ⟶ Skip) □ (breakfast ⟶ jog  ⟶ Skip))
MaggieDF = getup ⟶ ((swim ⟶ breakfast ⟶ Skip) □ (breakfast ⟶ swim ⟶ Skip))
```

This mirrors the original `Peter`/`Maggie` of §4.2 exactly, with `Up` replaced
by `Skip`.  The reduction keeps the phenomenon intact and lets us prove **both**
sides of the contrast on this **one** family:

* full-sync `PeterDF [| Events |] MaggieDF` still **deadlocks** after
  `⟨getup, breakfast⟩` (Peter is then committed to `jog`, Maggie to `swim`,
  neither shared) — `peterMaggieDF-deadlocks` (§6.6); whereas
* the alphabetised `PeterDF ⟦ AP ∥ AM ⟧ MaggieDF` is **deadlock-free**
  (`pm-deadlockFree`, §6.5): each does its solo action, both reconverge on the
  shared `breakfast`, and terminate.

So this is a genuine *same processes, different parallel operator ⇒ deadlock vs
deadlock-free* contrast, proved (not merely asserted).  Task-2's
`peterMaggie-deadlocks` / `¬pm-deadlockFree` for the *original*, loop-carrying
`Peter`/`Maggie` of §4.2 are untouched and remain the source-faithful versions.

Because `IsStuck` counts successful termination (`√`) as an enabled move, the
terminal `Skip ⟦∥⟧ Skip` state is **not** a deadlock (it offers `√`), and
`⟹∖√`-reachability never steps past it.  Retaining `□` makes the alphabetised
reachable set the finite DAG of **nine** composite states (`C00 → C11 →
{CjB, CsB, Cbb} → {Cjs, Csk, Cks} → C33`); we discharge deadlock-freedom by
exhibiting a `Live` witness (an enabled move at every reachable state) for each,
bottom-up.

### §6.1 The alphabets `AP`, `AM`

`AP = Events ∖ {swim}` and `AM = Events ∖ {jog}`: `getup`, `breakfast`, `read`
are shared; `jog` is Peter-solo (`∈ AP`, `∉ AM`); `swim` is Maggie-solo (`∈ AM`,
`∉ AP`).  Every event the finite family fires (`getup`/`jog`/`swim`/`breakfast`)
is therefore routed cleanly; `read` is never fired here but sits in both
alphabets so the set-difference reading is honest.

```agda
AP : EventSet
AP .mem (_ , getup)     _ = ⊤poly {lzero}
AP .mem (_ , breakfast) _ = ⊤poly {lzero}
AP .mem (_ , jog)       _ = ⊤poly {lzero}
AP .mem (_ , read)      _ = ⊤poly {lzero}
AP .mem (_ , swim)      _ = ⊥
AP .dec (_ , getup)     _ = yes tt
AP .dec (_ , breakfast) _ = yes tt
AP .dec (_ , jog)       _ = yes tt
AP .dec (_ , read)      _ = yes tt
AP .dec (_ , swim)      _ = no (λ z → z)

AM : EventSet
AM .mem (_ , getup)     _ = ⊤poly {lzero}
AM .mem (_ , breakfast) _ = ⊤poly {lzero}
AM .mem (_ , swim)      _ = ⊤poly {lzero}
AM .mem (_ , read)      _ = ⊤poly {lzero}
AM .mem (_ , jog)       _ = ⊥
AM .dec (_ , getup)     _ = yes tt
AM .dec (_ , breakfast) _ = yes tt
AM .dec (_ , swim)      _ = yes tt
AM .dec (_ , read)      _ = yes tt
AM .dec (_ , jog)       _ = no (λ z → z)
```

### §6.2 The `□`-preserving processes and their residues

```agda
PjB PbJ PL PR PBodyDF PeterDF : DProc
PjB     = breakfast ⟶₀ Skip        -- Peter after jog:       offers breakfast
PbJ     = jog       ⟶₀ Skip        -- Peter after breakfast: offers jog
PL      = jog       ⟶₀ PjB         -- Peter's exercise-first □-branch
PR      = breakfast ⟶₀ PbJ         -- Peter's breakfast-first □-branch
PBodyDF = PL □ PR
PeterDF = getup ⟶₀ PBodyDF

MsB MbS ML MR MBodyDF MaggieDF : DProc
MsB      = breakfast ⟶₀ Skip       -- Maggie after swim:      offers breakfast
MbS      = swim      ⟶₀ Skip       -- Maggie after breakfast: offers swim
ML       = swim      ⟶₀ MsB        -- Maggie's exercise-first □-branch
MR       = breakfast ⟶₀ MbS        -- Maggie's breakfast-first □-branch
MBodyDF  = ML □ MR
MaggieDF = getup ⟶₀ MBodyDF
```

The composite of two `DProc`s returns a *pair* (`⊤poly × ⊤poly`).  The nine
reachable composite states:

```agda
DProc² : Set₁
DProc² = PTree DEv (ExtI DEv) (⊤poly {lzero} × ⊤poly {lzero})

C00 C11 CjB CsB Cbb Cjs Csk Cks C33 : DProc²
C00 = PeterDF ⟦ AP ∥ AM ⟧ MaggieDF   -- start
C11 = PBodyDF ⟦ AP ∥ AM ⟧ MBodyDF    -- after getup (sync)
CjB = PjB     ⟦ AP ∥ AM ⟧ MBodyDF    -- after getup, jog  (Peter solo)
CsB = PBodyDF ⟦ AP ∥ AM ⟧ MsB        -- after getup, swim (Maggie solo)
Cbb = PbJ     ⟦ AP ∥ AM ⟧ MbS        -- after getup, breakfast (sync)
Cjs = PjB     ⟦ AP ∥ AM ⟧ MsB        -- both did solo exercise; breakfast pending
Csk = Skip    ⟦ AP ∥ AM ⟧ MbS        -- Peter terminated; Maggie still to swim
Cks = PbJ     ⟦ AP ∥ AM ⟧ Skip       -- Maggie terminated; Peter still to jog
C33 = Skip    ⟦ AP ∥ AM ⟧ Skip       -- both terminated (offers √, not stuck)
```

### §6.3 Machinery: single-step inversion (parallel *and* external choice)

```agda
open import Data.Sum using (inj₁; inj₂)
open import CSP.Laws.AlphaParallel DEv-≟
  using ( αVisR; vSync; vSoloL; vSoloR; v√
        ; αpar-vis-step-inv; αpar-τ-step-inv )
open import CSP.Laws.Traces.TraceLawsExtChoiceMono DEv-≟
  using (□-ev-elim; evP; evQ; evPQ)
open import Semantics.DeadlockDR {E = DEv} {I = ExtI DEv}
  using (Progress; progress⇒deadlockFree; Live; Live⇒Progress)
open Live
```

The `□`-headed bodies `PBodyDF`/`MBodyDF` have **no τ-transition**: each
`□`-branch is a stable prefix (τ-map `∅t`), so the fused choice τ-map `□-mt`
offers `nothing` everywhere.  We record this directly (via `□-mt-elim`), since a
generic `□-τ-elim` would also expose the never-taken commit/slide branches.

```agda
PBody-no-τ : ∀ {t′} → PBodyDF ─[ τ ]─► t′ → ⊥
PBody-no-τ (sSil feq) = case feq of λ ()
PBody-no-τ (sTau {i = _ , base _}            refl br) = case br of λ ()
PBody-no-τ (sTau {i = _ , fin}               refl br) = case br of λ ()
PBody-no-τ (sTau {i = _ , pair (base _) _}   refl br) = case br of λ ()
PBody-no-τ (sTau {i = _ , pair (pair _ _) _} refl br) = case br of λ ()
PBody-no-τ (sTau {i = _ , pair fin _} {a = lift fzero          , _} refl br) = case br of λ ()
PBody-no-τ (sTau {i = _ , pair fin _} {a = lift (fsuc fzero)    , _} refl br) = case br of λ ()
PBody-no-τ (sTau {i = _ , pair fin _} {a = lift (fsuc (fsuc _)) , _} refl br) = case br of λ ()

MBody-no-τ : ∀ {t′} → MBodyDF ─[ τ ]─► t′ → ⊥
MBody-no-τ (sSil feq) = case feq of λ ()
MBody-no-τ (sTau {i = _ , base _}            refl br) = case br of λ ()
MBody-no-τ (sTau {i = _ , fin}               refl br) = case br of λ ()
MBody-no-τ (sTau {i = _ , pair (base _) _}   refl br) = case br of λ ()
MBody-no-τ (sTau {i = _ , pair (pair _ _) _} refl br) = case br of λ ()
MBody-no-τ (sTau {i = _ , pair fin _} {a = lift fzero          , _} refl br) = case br of λ ()
MBody-no-τ (sTau {i = _ , pair fin _} {a = lift (fsuc fzero)    , _} refl br) = case br of λ ()
MBody-no-τ (sTau {i = _ , pair fin _} {a = lift (fsuc (fsuc _)) , _} refl br) = case br of λ ()
```

`Skip` (`ret`) likewise has no τ and no visible event (its only move is `√`):

```agda
Skip-no-τ : ∀ {t′} → Skip {lzero} ─[ τ ]─► t′ → ⊥
Skip-no-τ (sSil feq)   = case feq of λ ()
Skip-no-τ (sTau feq _) = case feq of λ ()

Skip-no-ev : ∀ {e : Event} {t′} → Skip {lzero} ─[ ev (evl e) ]─► t′ → ⊥
Skip-no-ev (sVis feq _) = case feq of λ ()
```

### §6.4 A `Live` witness at each reachable state (bottom-up)

For `stepev` we invert the composite's visible step (`αpar-vis-step-inv` into
`αVisR`); in a `□`-headed operand we then invert the choice step
(`□-ev-elim` into `evP`/`evQ`/`evPQ`) and finally the underlying prefix
(`⟶₀-ev-inv`).  Wrong-alphabet routings are absurd (the membership witness is
inhabited/empty as required), a `vSync` on distinct offered events
(`jog`≠`swim`, etc.) is refuted by constructor disjointness, and `evPQ` (both
`□`-branches firing one event) is refuted because the two branches offer
different events.  `v√` cannot arise (operands are `react`-headed, not `ret`).

```agda
-- C33: both terminated.  Only move is √ (sRet); no τ, no evl-event.
liveC33 : Live C33
liveC33 .move                = _ , _ , sRet refl
liveC33 .stepτ  (sSil feq)   = case feq of λ ()
liveC33 .stepτ  (sTau feq _) = case feq of λ ()
liveC33 .stepev (sVis feq _) = case feq of λ ()

-- Csk: Peter done, Maggie offers swim (solo) → C33.
liveCsk : Live Csk
liveCsk .move = _ , _ , sVis {at = ⊤poly {lzero} , swim} {a = tt} refl refl
liveCsk .stepτ st with αpar-τ-step-inv st
... | inj₁ (_ , Pτ , _) = ⊥-elim (Skip-no-τ Pτ)
... | inj₂ (_ , Qτ , _) = ⊥-elim (⟶₀-no-τ Qτ)
liveCsk .stepev (sVis feq br) = go (αpar-vis-step-inv feq br)
  where
    go : ∀ {t″ l} → αVisR AP AM Skip MbS t″ l → Live t″
    go (vSync _ _ Pev _) = ⊥-elim (Skip-no-ev Pev)
    go (vSoloL _ _ Pev)  = ⊥-elim (Skip-no-ev Pev)
    go (vSoloR _ _ Qev) with ⟶₀-ev-inv Qev
    ... | _ , refl , refl = liveC33
    go (v√ _ eqQ) = case eqQ of λ ()

-- Cks: Maggie done, Peter offers jog (solo) → C33.
liveCks : Live Cks
liveCks .move = _ , _ , sVis {at = ⊤poly {lzero} , jog} {a = tt} refl refl
liveCks .stepτ st with αpar-τ-step-inv st
... | inj₁ (_ , Pτ , _) = ⊥-elim (⟶₀-no-τ Pτ)
... | inj₂ (_ , Qτ , _) = ⊥-elim (Skip-no-τ Qτ)
liveCks .stepev (sVis feq br) = go (αpar-vis-step-inv feq br)
  where
    go : ∀ {t″ l} → αVisR AP AM PbJ Skip t″ l → Live t″
    go (vSync _ _ _ Qev) = ⊥-elim (Skip-no-ev Qev)
    go (vSoloL _ _ Pev) with ⟶₀-ev-inv Pev
    ... | _ , refl , refl = liveC33
    go (vSoloR _ _ Qev) = ⊥-elim (Skip-no-ev Qev)
    go (v√ eqP _) = case eqP of λ ()

-- Cjs: both offer breakfast (shared) → sync to C33.
liveCjs : Live Cjs
liveCjs .move = _ , _ , αpar-sync-step {at = ⊤poly {lzero} , breakfast} {a = tt}
                          tt tt refl refl refl refl
liveCjs .stepτ st with αpar-τ-step-inv st
... | inj₁ (_ , Pτ , _) = ⊥-elim (⟶₀-no-τ Pτ)
... | inj₂ (_ , Qτ , _) = ⊥-elim (⟶₀-no-τ Qτ)
liveCjs .stepev (sVis feq br) = go (αpar-vis-step-inv feq br)
  where
    go : ∀ {t″ l} → αVisR AP AM PjB MsB t″ l → Live t″
    go (vSync _ _ Pev Qev) with ⟶₀-ev-inv Pev
    ... | _ , refl , refl with ⟶₀-ev-inv Qev
    ...   | _ , refl , refl = liveC33
    go (vSoloL _ ¬pB Pev) with ⟶₀-ev-inv Pev
    ... | _ , refl , _ = ⊥-elim (¬pB tt)
    go (vSoloR ¬pA _ Qev) with ⟶₀-ev-inv Qev
    ... | _ , refl , _ = ⊥-elim (¬pA tt)
    go (v√ eqP _) = case eqP of λ ()

-- Cbb: Peter offers jog (solo→Csk); Maggie offers swim (solo→Cks).
liveCbb : Live Cbb
liveCbb .move = _ , _ , αpar-soloL-step {at = ⊤poly {lzero} , jog} {a = tt}
                          tt (λ ()) refl refl refl
liveCbb .stepτ st with αpar-τ-step-inv st
... | inj₁ (_ , Pτ , _) = ⊥-elim (⟶₀-no-τ Pτ)
... | inj₂ (_ , Qτ , _) = ⊥-elim (⟶₀-no-τ Qτ)
liveCbb .stepev (sVis feq br) = go (αpar-vis-step-inv feq br)
  where
    go : ∀ {t″ l} → αVisR AP AM PbJ MbS t″ l → Live t″
    go (vSync _ _ Pev Qev) with ⟶₀-ev-inv Pev
    ... | _ , refl , _ with ⟶₀-ev-inv Qev
    ...   | _ , eqbad , _ = case eqbad of λ ()
    go (vSoloL _ _ Pev) with ⟶₀-ev-inv Pev
    ... | _ , refl , refl = liveCsk
    go (vSoloR _ _ Qev) with ⟶₀-ev-inv Qev
    ... | _ , refl , refl = liveCks
    go (v√ eqP _) = case eqP of λ ()

-- CjB: Peter past jog (offers breakfast), Maggie at □.
--   swim (Maggie solo) → Cjs;  breakfast (sync) → Csk.
liveCjB : Live CjB
liveCjB .move = _ , _ , αpar-soloR-step {at = ⊤poly {lzero} , swim} {a = tt}
                          (λ ()) tt refl refl refl
liveCjB .stepτ st with αpar-τ-step-inv st
... | inj₁ (_ , Pτ , _) = ⊥-elim (⟶₀-no-τ Pτ)
... | inj₂ (_ , Qτ , _) = ⊥-elim (MBody-no-τ Qτ)
liveCjB .stepev (sVis feq br) = go (αpar-vis-step-inv feq br)
  where
    go : ∀ {t″ l} → αVisR AP AM PjB MBodyDF t″ l → Live t″
    go (vSync _ _ Pev Qev) with ⟶₀-ev-inv Pev
    ... | _ , refl , refl with □-ev-elim ML MR Qev
    ...   | evP Qs with ⟶₀-ev-inv Qs
    ...     | _ , eqbad , _ = case eqbad of λ ()
    go (vSync _ _ Pev Qev) | _ , refl , refl | evQ Qs with ⟶₀-ev-inv Qs
    ...     | _ , refl , refl = liveCsk
    go (vSync _ _ Pev Qev) | _ , refl , refl | evPQ Qs1 _ with ⟶₀-ev-inv Qs1
    ...     | _ , eqbad , _ = case eqbad of λ ()
    go (vSoloL _ ¬pB Pev) with ⟶₀-ev-inv Pev
    ... | _ , refl , _ = ⊥-elim (¬pB tt)
    go (vSoloR ¬pA _ Qev) with □-ev-elim ML MR Qev
    ... | evP Qs with ⟶₀-ev-inv Qs
    ...   | _ , refl , refl = liveCjs
    go (vSoloR ¬pA _ Qev) | evQ Qs with ⟶₀-ev-inv Qs
    ...   | _ , refl , _ = ⊥-elim (¬pA tt)
    go (vSoloR ¬pA _ Qev) | evPQ Qs1 Qs2 with ⟶₀-ev-inv Qs1
    ...   | _ , refl , _ with ⟶₀-ev-inv Qs2
    ...     | _ , eqbad , _ = case eqbad of λ ()
    go (v√ eqP _) = case eqP of λ ()

-- CsB: Maggie past swim (offers breakfast), Peter at □.
--   jog (Peter solo) → Cjs;  breakfast (sync) → Cks.
liveCsB : Live CsB
liveCsB .move = _ , _ , αpar-soloL-step {at = ⊤poly {lzero} , jog} {a = tt}
                          tt (λ ()) refl refl refl
liveCsB .stepτ st with αpar-τ-step-inv st
... | inj₁ (_ , Pτ , _) = ⊥-elim (PBody-no-τ Pτ)
... | inj₂ (_ , Qτ , _) = ⊥-elim (⟶₀-no-τ Qτ)
liveCsB .stepev (sVis feq br) = go (αpar-vis-step-inv feq br)
  where
    go : ∀ {t″ l} → αVisR AP AM PBodyDF MsB t″ l → Live t″
    go (vSync _ _ Pev Qev) with ⟶₀-ev-inv Qev
    ... | _ , refl , refl with □-ev-elim PL PR Pev
    ...   | evP Ps with ⟶₀-ev-inv Ps
    ...     | _ , eqbad , _ = case eqbad of λ ()
    go (vSync _ _ Pev Qev) | _ , refl , refl | evQ Ps with ⟶₀-ev-inv Ps
    ...     | _ , refl , refl = liveCks
    go (vSync _ _ Pev Qev) | _ , refl , refl | evPQ Ps1 _ with ⟶₀-ev-inv Ps1
    ...     | _ , eqbad , _ = case eqbad of λ ()
    go (vSoloL _ _ Pev) with □-ev-elim PL PR Pev
    ... | evP Ps with ⟶₀-ev-inv Ps
    ...   | _ , refl , refl = liveCjs
    go (vSoloL _ ¬pB Pev) | evQ Ps with ⟶₀-ev-inv Ps
    ...   | _ , refl , _ = ⊥-elim (¬pB tt)
    go (vSoloL _ ¬pB Pev) | evPQ Ps1 Ps2 with ⟶₀-ev-inv Ps1
    ...   | _ , refl , _ with ⟶₀-ev-inv Ps2
    ...     | _ , eqbad , _ = case eqbad of λ ()
    go (vSoloR ¬pA _ Qev) with ⟶₀-ev-inv Qev
    ... | _ , refl , _ = ⊥-elim (¬pA tt)
    go (v√ eqP _) = case eqP of λ ()

-- C11: after getup.  Peter offers jog (solo→CjB); Maggie offers swim
--   (solo→CsB); both offer breakfast (sync→Cbb).
liveC11 : Live C11
liveC11 .move = _ , _ , αpar-soloL-step {at = ⊤poly {lzero} , jog} {a = tt}
                          tt (λ ()) refl refl refl
liveC11 .stepτ st with αpar-τ-step-inv st
... | inj₁ (_ , Pτ , _) = ⊥-elim (PBody-no-τ Pτ)
... | inj₂ (_ , Qτ , _) = ⊥-elim (MBody-no-τ Qτ)
liveC11 .stepev (sVis feq br) = go (αpar-vis-step-inv feq br)
  where
    go : ∀ {t″ l} → αVisR AP AM PBodyDF MBodyDF t″ l → Live t″
    go (vSync _ pB Pev Qev) with □-ev-elim PL PR Pev
    ... | evP Ps with ⟶₀-ev-inv Ps
    ...   | _ , refl , _ = ⊥-elim pB
    go (vSync _ pB Pev Qev) | evQ Ps with ⟶₀-ev-inv Ps
    ...   | _ , refl , refl with □-ev-elim ML MR Qev
    ...     | evP Qs with ⟶₀-ev-inv Qs
    ...       | _ , eqbad , _ = case eqbad of λ ()
    go (vSync _ pB Pev Qev) | evQ Ps | _ , refl , refl | evQ Qs with ⟶₀-ev-inv Qs
    ...       | _ , refl , refl = liveCbb
    go (vSync _ pB Pev Qev) | evQ Ps | _ , refl , refl | evPQ Qs1 _ with ⟶₀-ev-inv Qs1
    ...       | _ , eqbad , _ = case eqbad of λ ()
    go (vSync _ pB Pev Qev) | evPQ Ps1 Ps2 with ⟶₀-ev-inv Ps1
    ...   | _ , refl , _ with ⟶₀-ev-inv Ps2
    ...     | _ , eqbad , _ = case eqbad of λ ()
    go (vSoloL _ ¬pB Pev) with □-ev-elim PL PR Pev
    ... | evP Ps with ⟶₀-ev-inv Ps
    ...   | _ , refl , refl = liveCjB
    go (vSoloL _ ¬pB Pev) | evQ Ps with ⟶₀-ev-inv Ps
    ...   | _ , refl , _ = ⊥-elim (¬pB tt)
    go (vSoloL _ ¬pB Pev) | evPQ Ps1 Ps2 with ⟶₀-ev-inv Ps1
    ...   | _ , refl , _ with ⟶₀-ev-inv Ps2
    ...     | _ , eqbad , _ = case eqbad of λ ()
    go (vSoloR ¬pA _ Qev) with □-ev-elim ML MR Qev
    ... | evP Qs with ⟶₀-ev-inv Qs
    ...   | _ , refl , refl = liveCsB
    go (vSoloR ¬pA _ Qev) | evQ Qs with ⟶₀-ev-inv Qs
    ...   | _ , refl , _ = ⊥-elim (¬pA tt)
    go (vSoloR ¬pA _ Qev) | evPQ Qs1 Qs2 with ⟶₀-ev-inv Qs1
    ...   | _ , refl , _ with ⟶₀-ev-inv Qs2
    ...     | _ , eqbad , _ = case eqbad of λ ()
    go (v√ eqP _) = case eqP of λ ()

-- C00: start.  Only getup is jointly offered → sync to C11.
liveC00 : Live C00
liveC00 .move = _ , _ , αpar-sync-step {at = ⊤poly {lzero} , getup} {a = tt}
                          tt tt refl refl refl refl
liveC00 .stepτ st with αpar-τ-step-inv st
... | inj₁ (_ , Pτ , _) = ⊥-elim (⟶₀-no-τ Pτ)
... | inj₂ (_ , Qτ , _) = ⊥-elim (⟶₀-no-τ Qτ)
liveC00 .stepev (sVis feq br) = go (αpar-vis-step-inv feq br)
  where
    go : ∀ {t″ l} → αVisR AP AM PeterDF MaggieDF t″ l → Live t″
    go (vSync _ _ Pev Qev) with ⟶₀-ev-inv Pev
    ... | _ , refl , refl with ⟶₀-ev-inv Qev
    ...   | _ , refl , refl = liveC11
    go (vSoloL _ ¬pB Pev) with ⟶₀-ev-inv Pev
    ... | _ , refl , _ = ⊥-elim (¬pB tt)
    go (vSoloR ¬pA _ Qev) with ⟶₀-ev-inv Qev
    ... | _ , refl , _ = ⊥-elim (¬pA tt)
    go (v√ eqP _) = case eqP of λ ()
```

### §6.5 Deadlock-freedom

`Live⇒Progress` turns the coinductive liveness at the start state into
`Progress` (every `⟹∖√`-reachable state has an enabled label);
`progress⇒deadlockFree` concludes deadlock-freedom.

```agda
pm-progress : Progress (PeterDF ⟦ AP ∥ AM ⟧ MaggieDF)
pm-progress = Live⇒Progress liveC00

pm-deadlockFree : DeadlockFree (PeterDF ⟦ AP ∥ AM ⟧ MaggieDF)
pm-deadlockFree = progress⇒deadlockFree pm-progress
```

The alphabetised `PeterDF [ AP || AM ] MaggieDF :[deadlock free]` assertion thus
**holds**, the complement of §5's full-synchronisation deadlock.

### §6.6 The same finite family deadlocks under full synchronisation

The `□` choice does **not** rescue the *full-synchronisation* composition: with
every event shared, after `getup` the only jointly-offered event is `breakfast`
(Peter also offers `jog`, Maggie also `swim`, but neither is shared), so
`breakfast` fires — committing Peter to `jog` and Maggie to `swim`, neither
shared.  The composite then refuses everything: a deadlock after
`⟨getup, breakfast⟩`, exactly mirroring §5's `peterMaggie-deadlocks` (the
`□`-body still fires `breakfast` into the commitment `PbJ`/`MbS`, because the
merged offer at `breakfast` is `just`).

```agda
peterDF-getup : PeterDF ─[ ev (evl evGetup) ]─► PBodyDF
peterDF-getup = sVis {at = ⊤poly {lzero} , getup} {a = tt} refl refl

maggieDF-getup : MaggieDF ─[ ev (evl evGetup) ]─► MBodyDF
maggieDF-getup = sVis {at = ⊤poly {lzero} , getup} {a = tt} refl refl

pbodyDF-breakfast : PBodyDF ─[ ev (evl evBreakfast) ]─► PbJ
pbodyDF-breakfast = sVis {at = ⊤poly {lzero} , breakfast} {a = tt} refl refl

mbodyDF-breakfast : MBodyDF ─[ ev (evl evBreakfast) ]─► MbS
mbodyDF-breakfast = sVis {at = ⊤poly {lzero} , breakfast} {a = tt} refl refl

WDF : DProc
WDF = Par⊤ Events PbJ MbS

reachDF-getup : Par⊤ Events PeterDF MaggieDF
                  ─[ ev (evl evGetup) ]─► Par⊤ Events PBodyDF MBodyDF
reachDF-getup = Par-sync Events _ PeterDF MaggieDF tt peterDF-getup maggieDF-getup

reachDF-breakfast : Par⊤ Events PBodyDF MBodyDF ─[ ev (evl evBreakfast) ]─► WDF
reachDF-breakfast = Par-sync Events _ PBodyDF MBodyDF tt pbodyDF-breakfast mbodyDF-breakfast

reachDF : Par⊤ Events PeterDF MaggieDF ⟹∖√⟨ evGetup ∷ evBreakfast ∷ [] ⟩ WDF
reachDF = ∖√-ev reachDF-getup (∖√-ev reachDF-breakfast ∖√-refl)

stuckDF : IsStuck WDF
stuckDF {l = ev _} step with Par-ev-elim Events _ PbJ MbS step
... | evL ¬m _      = ¬m tt
... | evR ¬m _      = ¬m tt
... | evBoth ¬m _ _ = ¬m tt
... | ev√ fp _      = case fp of λ ()
... | evSync _ pStep qStep with ⟶₀-ev-inv pStep
...   | _ , refl , _ with ⟶₀-ev-inv qStep
...     | _ , eqbad , _ = case eqbad of λ ()
stuckDF {l = τ} step with Par-τ-elim Events _ PbJ MbS step
... | τL _ pτ _ = ⟶₀-no-τ pτ
... | τR _ qτ _ = ⟶₀-no-τ qτ

peterMaggieDF-deadlocks : HasDeadlock (Par⊤ Events PeterDF MaggieDF)
peterMaggieDF-deadlocks = evGetup ∷ evBreakfast ∷ [] , WDF , reachDF , stuckDF
```

Thus the **one** finite family `PeterDF`/`MaggieDF` witnesses both sides of the
contrast: it deadlocks under full synchronisation (`peterMaggieDF-deadlocks`)
yet is deadlock-free under the alphabetised parallel (`pm-deadlockFree`) — the
genuine *same processes, different parallel operator* phenomenon.
