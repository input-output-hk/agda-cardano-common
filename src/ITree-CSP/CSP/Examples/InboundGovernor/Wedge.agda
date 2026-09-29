{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- The ouroboros-network inbound-governor wedge, as observed on musashi
-- (relay leios1-rel-a-1, 2026-09-27 14:48:18Z) and as pinned in source
-- (`ouroboros-network` 4b3ab7664f609a1aee0f0c24dcfcfd0ab899fc42).
--
-- ONE ConnectionId, TWO mux identities.  A duplex peer dialling from its
-- listening port reproduces the same 4-tuple on every redial; after an
-- abortive close the kernel accepts the redial while our node still holds
-- the old mux.  At the pin the connection manager ADMITS the second
-- connection over the first (`ConnectionManager/Core.hs`,
-- `includeInboundConnectionImpl`: every live-state case is
-- `writeTVar (connVar v) connState' $> assert False v`, asserts compiled
-- out), and the governor, told of an id it already tracks, KEEPS THE OLD
-- ENTRY and drops the new handle (`InboundGovernor.hs:378`).  The dropped
-- mux is an ORPHAN: running, untracked.  When ANY mux under the id dies,
-- the tracer hook (on the dying mux's thread) resolves the mux to await BY
-- KEY from the governor's map (`InboundGovernor.hs:692-697`) and enqueues
-- it; the sequential handler then blocks on it (`:397`, `atomically
-- result`).  If the map holds a LIVE mux, the governor blocks until THAT
-- mux dies.
--
-- Two facts from source shape the model:
--   F1  every `TraceState Dead` site writes terminal `muxStatus` FIRST
--       (`Mux.hs` 275/459/474/482); `Mux.stopped` retries only on
--       Ready/Stopping.  So `stopOK i` is offered exactly when mux i is
--       dead: a dead mux always completes the await; a live one never does.
--   F2  the lookup is by ConnectionId, so with one id the awaited mux is
--       always the TRACKED one, whichever mux died.
--
-- Events (unit payload):
--   admit i    the CM admits connection i (handshake done, mux i created)
--   new i      the CM announces NewConnection i to the governor
--   die i      mux i dies; its tracer hook fires (mux ↔ hook)
--   notify i   the hook's message reaches the governor loop (hook ↔ IG);
--              the hook is a one-place buffer, so a mux can die while the
--              governor is blocked — as in the code, where the hook only
--              writes to the info channel
--   stopOK i   `Mux.stopped i` returns — offered only by a DEAD mux (F1)
--   promote    the governor is making progress (S7)
--
-- Results (machine-checked; nothing postulated):
--   W1  SysPin reaches W, where the IG awaits `stopOK 0` while mux 0 is
--       live (`wedge-reach`).  The trace is the logged one relabelled:
--       admit m1, new m1, admit m2 (orphan), new m2 (dropped), die m2,
--       notify → lookup finds m1 → await m1.
--   W2  In W the only visible step is `die 0` and there is no τ
--       (`wedge-only-die0`, `wedge-no-τ`); hence `promote` is refused
--       (`wedge-refuses-promote`) and the await cannot complete
--       (`wedge-refuses-stopOK0`).  The wedge lasts exactly as long as the
--       tracked live mux lives — on the 27th, longer than the 3-hour log.
--   W3  It is escapable ONLY by that mux dying: after `die 0`, `stopOK 0`
--       is enabled and the governor moves on (`wedge-escape`).
--   F   With commit 1ccd17298 (Marcin Wójtowicz — refuse a duplicate id in
--       any live state), the second admission is refused while the first
--       connection is live (`fix-refuses-admit1`): no orphan can exist, so
--       the by-key lookup can only ever find the mux that died.
------------------------------------------------------------------------

module CSP.Examples.InboundGovernor.Wedge where

open import Level using (0ℓ) renaming (zero to lzero)
open import Data.Unit using () renaming (⊤ to Unit; tt to unit)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
import Data.Fin.Properties as FinP
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Properties as MaybeP
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq)

open import Process_Trees using (PTree; AnyTypes; ExtI)

------------------------------------------------------------------------
-- §1  Alphabet
------------------------------------------------------------------------

Id : Set
Id = Fin 2

f0 f1 : Id
f0 = zero
f1 = suc zero

data Gov : Set → Set where
  admit   : Id → Gov Unit
  new     : Id → Gov Unit
  die     : Id → Gov Unit
  notify  : Id → Gov Unit
  stopOK  : Id → Gov Unit
  promote : Gov Unit

Gov-≟ : (x y : AnyTypes Gov) → Dec (x ≡ y)
Gov-≟ (_ , admit i)  (_ , admit j)  with i FinP.≟ j
... | yes refl = yes refl
... | no ¬p    = no λ { refl → ¬p refl }
Gov-≟ (_ , new i)    (_ , new j)    with i FinP.≟ j
... | yes refl = yes refl
... | no ¬p    = no λ { refl → ¬p refl }
Gov-≟ (_ , die i)    (_ , die j)    with i FinP.≟ j
... | yes refl = yes refl
... | no ¬p    = no λ { refl → ¬p refl }
Gov-≟ (_ , notify i) (_ , notify j) with i FinP.≟ j
... | yes refl = yes refl
... | no ¬p    = no λ { refl → ¬p refl }
Gov-≟ (_ , stopOK i) (_ , stopOK j) with i FinP.≟ j
... | yes refl = yes refl
... | no ¬p    = no λ { refl → ¬p refl }
Gov-≟ (_ , promote)  (_ , promote)  = yes refl
Gov-≟ (_ , admit _)  (_ , new _)    = no λ ()
Gov-≟ (_ , admit _)  (_ , die _)    = no λ ()
Gov-≟ (_ , admit _)  (_ , notify _) = no λ ()
Gov-≟ (_ , admit _)  (_ , stopOK _) = no λ ()
Gov-≟ (_ , admit _)  (_ , promote)  = no λ ()
Gov-≟ (_ , new _)    (_ , admit _)  = no λ ()
Gov-≟ (_ , new _)    (_ , die _)    = no λ ()
Gov-≟ (_ , new _)    (_ , notify _) = no λ ()
Gov-≟ (_ , new _)    (_ , stopOK _) = no λ ()
Gov-≟ (_ , new _)    (_ , promote)  = no λ ()
Gov-≟ (_ , die _)    (_ , admit _)  = no λ ()
Gov-≟ (_ , die _)    (_ , new _)    = no λ ()
Gov-≟ (_ , die _)    (_ , notify _) = no λ ()
Gov-≟ (_ , die _)    (_ , stopOK _) = no λ ()
Gov-≟ (_ , die _)    (_ , promote)  = no λ ()
Gov-≟ (_ , notify _) (_ , admit _)  = no λ ()
Gov-≟ (_ , notify _) (_ , new _)    = no λ ()
Gov-≟ (_ , notify _) (_ , die _)    = no λ ()
Gov-≟ (_ , notify _) (_ , stopOK _) = no λ ()
Gov-≟ (_ , notify _) (_ , promote)  = no λ ()
Gov-≟ (_ , stopOK _) (_ , admit _)  = no λ ()
Gov-≟ (_ , stopOK _) (_ , new _)    = no λ ()
Gov-≟ (_ , stopOK _) (_ , die _)    = no λ ()
Gov-≟ (_ , stopOK _) (_ , notify _) = no λ ()
Gov-≟ (_ , stopOK _) (_ , promote)  = no λ ()
Gov-≟ (_ , promote)  (_ , admit _)  = no λ ()
Gov-≟ (_ , promote)  (_ , new _)    = no λ ()
Gov-≟ (_ , promote)  (_ , die _)    = no λ ()
Gov-≟ (_ , promote)  (_ , notify _) = no λ ()
Gov-≟ (_ , promote)  (_ , stopOK _) = no λ ()

import CSP.Operators {E = Gov} (Gov-≟) as Op
open Op using (Stop; Ret; Prefix₀; _□_; _⦀_; _∥⇘_⇙_; iter; iter-bind; _>>=_; EventSet; chanSet; ∅ES)

open import Semantics.LTS {E = Gov} {I = ExtI Gov}
  using (_─[_]─►_; Label; Event√; ev; τ; evl; evLabel; sVis; sSil; sTau; sRet)
open import CSP.Laws.Traces.TraceLawsParallel Gov-≟
  using (Par-sync; Par-soloL; Par-soloR; Par-τ-L; Par-τ-R)
open import CSP.Laws.Traces.TraceLawsParallelElim Gov-≟
  using (Par-ev-elim; Par-τ-elim; evSync; evL; evR; evBoth; ev√; τL; τR)
open import CSP.Laws.Traces.PrefixInversion Gov-≟
  using (⟶₀-ev-inv; ⟶₀-no-τ; loop-pfx-ev-inv; loop-pfx-no-τ)

Proc : Set₁
Proc = PTree Gov (ExtI Gov) (⊤ {lzero})

-- the governor's map for the single ConnectionId: nothing, or the tracked mux
St : Set
St = Maybe Id

-- decidable equality on the state, passed to `□` explicitly (the library's
-- generic `DecEq-Maybe` instance would otherwise compete with it)
DecEq-St : DecEq St
DecEq-St = record { _≟_ = MaybeP.≡-dec FinP._≟_ }

infixr 2 _⊞_
_⊞_ : PTree Gov (ExtI Gov) St → PTree Gov (ExtI Gov) St → PTree Gov (ExtI Gov) St
_⊞_ = _□_ ⦃ DecEq-St ⦄

ADMIT NEW DIE NOTIFY STOPOK : Id → Event√ (⊤ {lzero})
ADMIT  i = evl (evLabel Unit (admit i)  unit)
NEW    i = evl (evLabel Unit (new i)    unit)
DIE    i = evl (evLabel Unit (die i)    unit)
NOTIFY i = evl (evLabel Unit (notify i) unit)
STOPOK i = evl (evLabel Unit (stopOK i) unit)

PROMOTE : Event√ (⊤ {lzero})
PROMOTE = evl (evLabel Unit promote unit)

------------------------------------------------------------------------
-- §2  Processes
------------------------------------------------------------------------

-- A mux: admitted, live until it dies, then offers `stopOK` (F1).  One
-- await per death suffices: the IG enqueues one MuxFinished per death.
dead live Mux : Id → Proc
dead i = Prefix₀ (stopOK i) Stop
live i = Prefix₀ (die i) (dead i)
Mux  i = Prefix₀ (admit i) (live i)

-- The tracer hook of mux i: fires at death, delivers one message to the
-- governor's channel whenever the loop next gathers (`InfoChannel`).
Hook : Id → Proc
Hook i = Prefix₀ (die i) (Prefix₀ (notify i) Stop)

dieCs : AnyTypes Gov → Set
dieCs (_ , die _)    = Unit
dieCs (_ , admit _)  = ⊥
dieCs (_ , new _)    = ⊥
dieCs (_ , notify _) = ⊥
dieCs (_ , stopOK _) = ⊥
dieCs (_ , promote)  = ⊥

dieDec : (at : AnyTypes Gov) → Dec (dieCs at)
dieDec (_ , die _)    = yes unit
dieDec (_ , admit _)  = no (λ z → z)
dieDec (_ , new _)    = no (λ z → z)
dieDec (_ , notify _) = no (λ z → z)
dieDec (_ , stopOK _) = no (λ z → z)
dieDec (_ , promote)  = no (λ z → z)

dieES : EventSet
dieES = chanSet dieCs dieDec

-- a connection = its mux with its hook
Conn : Id → Proc
Conn i = Mux i ∥⇘ dieES ⇙ Hook i

Conns : Proc
Conns = Conn f0 ⦀ Conn f1

-- The connection manager AT THE PIN: admits the second connection under the
-- same id while the first is live (the overwrite branch), announces each.
CMpin : Proc
CMpin = Prefix₀ (admit f0) (Prefix₀ (new f0) (Prefix₀ (admit f1) (Prefix₀ (new f1) Stop)))

-- The connection manager WITH 1ccd17298: a duplicate id in a live state is
-- refused (`throwSTM ForbiddenOperation`); a second admission is possible
-- only after the first connection has died (TerminatingState).  It then
-- also lets the second one die.
CMfix : Proc
CMfix = Prefix₀ (admit f0) (Prefix₀ (new f0) (Prefix₀ (die f0)
          (Prefix₀ (admit f1) (Prefix₀ (new f1) (Prefix₀ (die f1) Stop)))))

-- The inbound governor loop, one event per iteration (S3); its state is the
-- map entry for the single id.
--   new i    tracking nothing : track i                    (`Nothing` branch)
--   new i    tracking t       : KEEP t, drop i             (`:378`, the orphan)
--   notify i tracking t       : lookup BY KEY gives t; await `stopOK t`
--                               (`:692-697`, then `:397`) — whichever i died
--   notify i tracking nothing : nothing to do              (`_otherwise -> pure ()`)
--   promote  tracking t       : progress marker            (S7)
igStep : St → PTree Gov (ExtI Gov) St
igStep nothing =
      Prefix₀ (new f0) (Ret (just f0))
  ⊞   Prefix₀ (new f1) (Ret (just f1))
  ⊞   Prefix₀ (notify f0) (Ret nothing)
  ⊞   Prefix₀ (notify f1) (Ret nothing)
igStep (just t) =
      Prefix₀ (new f0) (Ret (just t))
  ⊞   Prefix₀ (new f1) (Ret (just t))
  ⊞   Prefix₀ (notify f0) (Prefix₀ (stopOK t) (Ret nothing))
  ⊞   Prefix₀ (notify f1) (Prefix₀ (stopOK t) (Ret nothing))
  ⊞   Prefix₀ promote     (Ret (just t))

-- the loop, written through `iter` with a TOP-LEVEL step so that every
-- intermediate governor state can be named (`loop`'s step is where-bound)
igK : St → PTree Gov (ExtI Gov) (St ⊎ ⊤ {lzero})
igK a = igStep a >>= λ a′ → Ret (inj₁ a′)

IG : St → Proc
IG st = iter igK st

-- the governor BLOCKED inside its loop, awaiting `stopOK t`
IGaw : Id → Proc
IGaw t = iter-bind (Prefix₀ (stopOK t) (Ret nothing) >>= (λ a′ → Ret (inj₁ a′))) igK

------------------------------------------------------------------------
-- §3  Synchronisation sets and the two systems
------------------------------------------------------------------------

-- connections ↔ (CM, IG): admit (CM), notify and stopOK (IG)
connCs : AnyTypes Gov → Set
connCs (_ , admit _)  = Unit
connCs (_ , notify _) = Unit
connCs (_ , stopOK _) = Unit
connCs (_ , die _)    = ⊥
connCs (_ , new _)    = ⊥
connCs (_ , promote)  = ⊥

connDec : (at : AnyTypes Gov) → Dec (connCs at)
connDec (_ , admit _)  = yes unit
connDec (_ , notify _) = yes unit
connDec (_ , stopOK _) = yes unit
connDec (_ , die _)    = no (λ z → z)
connDec (_ , new _)    = no (λ z → z)
connDec (_ , promote)  = no (λ z → z)

connES : EventSet
connES = chanSet connCs connDec

-- with the fix the CM additionally observes deaths (its state var leaves
-- the live states when the handler exits)
connDieCs : AnyTypes Gov → Set
connDieCs (_ , admit _)  = Unit
connDieCs (_ , notify _) = Unit
connDieCs (_ , stopOK _) = Unit
connDieCs (_ , die _)    = Unit
connDieCs (_ , new _)    = ⊥
connDieCs (_ , promote)  = ⊥

connDieDec : (at : AnyTypes Gov) → Dec (connDieCs at)
connDieDec (_ , admit _)  = yes unit
connDieDec (_ , notify _) = yes unit
connDieDec (_ , stopOK _) = yes unit
connDieDec (_ , die _)    = yes unit
connDieDec (_ , new _)    = no (λ z → z)
connDieDec (_ , promote)  = no (λ z → z)

connDieES : EventSet
connDieES = chanSet connDieCs connDieDec

-- CM ↔ IG: only the NewConnection announcement
newCs : AnyTypes Gov → Set
newCs (_ , new _)    = Unit
newCs (_ , admit _)  = ⊥
newCs (_ , die _)    = ⊥
newCs (_ , notify _) = ⊥
newCs (_ , stopOK _) = ⊥
newCs (_ , promote)  = ⊥

newDec : (at : AnyTypes Gov) → Dec (newCs at)
newDec (_ , new _)    = yes unit
newDec (_ , admit _)  = no (λ z → z)
newDec (_ , die _)    = no (λ z → z)
newDec (_ , notify _) = no (λ z → z)
newDec (_ , stopOK _) = no (λ z → z)
newDec (_ , promote)  = no (λ z → z)

newES : EventSet
newES = chanSet newCs newDec

SysPin : Proc
SysPin = Conns ∥⇘ connES ⇙ (CMpin ∥⇘ newES ⇙ IG nothing)

SysFix : Proc
SysFix = Conns ∥⇘ connDieES ⇙ (CMfix ∥⇘ newES ⇙ IG nothing)

------------------------------------------------------------------------
-- §4  W1 — the wedge is reached (the logged trace, ids relabelled)
--
-- Each step is "there is a state such that …" (as in `RelayLive`): the
-- target of one step is `proj₁` of it and the source of the next.
------------------------------------------------------------------------

-- admit 0: mux 0 and the CM synchronise; hook and IG are not involved
pin₁ : Σ[ P ∈ Proc ] (SysPin ─[ ev (ADMIT f0) ]─► P)
pin₁ = _ ,
  Par-sync _ _ _ _ unit
    (Par-soloL _ _ _ _ (λ ()) (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl) refl)
    (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl)

-- new 0: the CM announces, the IG (tracking nothing) records mux 0
pin₂ : Σ[ P ∈ Proc ] (proj₁ pin₁ ─[ ev (NEW f0) ]─► P)
pin₂ = _ ,
  Par-soloR _ _ _ _ (λ ())
    (Par-sync _ _ _ _ unit (sVis refl refl) (sVis refl refl))
    refl

-- the IG loop-back (`iter`'s sil guard): one τ
pin₃ : Σ[ P ∈ Proc ] (proj₁ pin₂ ─[ τ ]─► P)
pin₃ = _ , Par-τ-R _ _ _ _ (Par-τ-R _ _ _ _ (sSil refl))

-- admit 1 WHILE MUX 0 IS LIVE: the pinned CM admits it (the overwrite branch)
pin₄ : Σ[ P ∈ Proc ] (proj₁ pin₃ ─[ ev (ADMIT f1) ]─► P)
pin₄ = _ ,
  Par-sync _ _ _ _ unit
    (Par-soloR _ _ _ _ (λ ()) (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl) refl)
    (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl)

-- new 1: the IG, already tracking 0, KEEPS 0 and drops 1 — mux 1 is an orphan
pin₅ : Σ[ P ∈ Proc ] (proj₁ pin₄ ─[ ev (NEW f1) ]─► P)
pin₅ = _ ,
  Par-soloR _ _ _ _ (λ ())
    (Par-sync _ _ _ _ unit (sVis refl refl) (sVis refl refl))
    refl

pin₆ : Σ[ P ∈ Proc ] (proj₁ pin₅ ─[ τ ]─► P)
pin₆ = _ , Par-τ-R _ _ _ _ (Par-τ-R _ _ _ _ (sSil refl))

-- die 1: the orphan dies; its hook fires (mux 1 ↔ hook 1 only)
pin₇ : Σ[ P ∈ Proc ] (proj₁ pin₆ ─[ ev (DIE f1) ]─► P)
pin₇ = _ ,
  Par-soloL _ _ _ _ (λ ())
    (Par-soloR _ _ _ _ (λ ()) (Par-sync _ _ _ _ unit (sVis refl refl) (sVis refl refl)) refl)
    refl

-- notify 1: the hook's message reaches the loop; the lookup BY KEY finds
-- mux 0; the IG now awaits `stopOK 0` — of a mux that is alive.
pin₈ : Σ[ P ∈ Proc ] (proj₁ pin₇ ─[ ev (NOTIFY f1) ]─► P)
pin₈ = _ ,
  Par-sync _ _ _ _ unit
    (Par-soloR _ _ _ _ (λ ()) (Par-soloR _ _ _ _ (λ ()) (sVis refl refl) refl) refl)
    (Par-soloR _ _ _ _ (λ ()) (sVis refl refl) refl)

-- THE WEDGED SYSTEM, written out: mux 0 live with its hook unfired, mux 1
-- dead with its hook spent, the pinned CM finished, the governor blocked on
-- `stopOK 0`.  `wedge-reach` checks that this IS the state the trace reaches.
W : Proc
W = ((live f0 ∥⇘ dieES ⇙ Hook f0) ⦀ (dead f1 ∥⇘ dieES ⇙ Stop))
      ∥⇘ connES ⇙ (Stop ∥⇘ newES ⇙ IGaw f0)

wedge-reach : proj₁ pin₇ ─[ ev (NOTIFY f1) ]─► W
wedge-reach = proj₂ pin₈

------------------------------------------------------------------------
-- §5  W3 — escapable only by the tracked live mux dying
------------------------------------------------------------------------

-- mux 0 may still die (its hook is free; the governor's blocked handler does
-- not stop the mux thread) …
esc₁ : Σ[ P ∈ Proc ] (W ─[ ev (DIE f0) ]─► P)
esc₁ = _ ,
  Par-soloL _ _ _ _ (λ ())
    (Par-soloL _ _ _ _ (λ ()) (Par-sync _ _ _ _ unit (sVis refl refl) (sVis refl refl)) refl)
    refl

-- … and only then does `stopOK 0` become enabled: the await completes, the
-- governor unregisters and is back in its loop.
esc₂ : Σ[ P ∈ Proc ] (proj₁ esc₁ ─[ ev (STOPOK f0) ]─► P)
esc₂ = _ ,
  Par-sync _ _ _ _ unit
    (Par-soloL _ _ _ _ (λ ()) (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl) refl)
    (Par-soloR _ _ _ _ (λ ()) (sVis refl refl) refl)

wedge-escape : Σ[ P ∈ Proc ] Σ[ Q ∈ Proc ]
               ((W ─[ ev (DIE f0) ]─► P) × (P ─[ ev (STOPOK f0) ]─► Q))
wedge-escape = _ , _ , proj₂ esc₁ , proj₂ esc₂

------------------------------------------------------------------------
-- §6  F — the fix refuses the second admission while the first is live
------------------------------------------------------------------------

fix₁ : Σ[ P ∈ Proc ] (SysFix ─[ ev (ADMIT f0) ]─► P)
fix₁ = _ ,
  Par-sync _ _ _ _ unit
    (Par-soloL _ _ _ _ (λ ()) (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl) refl)
    (Par-soloL _ _ _ _ (λ ()) (sVis refl refl) refl)

fix₂ : Σ[ P ∈ Proc ] (proj₁ fix₁ ─[ ev (NEW f0) ]─► P)
fix₂ = _ ,
  Par-soloR _ _ _ _ (λ ())
    (Par-sync _ _ _ _ unit (sVis refl refl) (sVis refl refl))
    refl

fix₃ : Σ[ P ∈ Proc ] (proj₁ fix₂ ─[ τ ]─► P)
fix₃ = _ , Par-τ-R _ _ _ _ (Par-τ-R _ _ _ _ (sSil refl))

-- the state with mux 0 admitted, announced and live, under the fixed CM
CMfix₂ : Proc
CMfix₂ = Prefix₀ (die f0) (Prefix₀ (admit f1) (Prefix₀ (new f1) (Prefix₀ (die f1) Stop)))

F : Proc
F = ((live f0 ∥⇘ dieES ⇙ Hook f0) ⦀ Conn f1) ∥⇘ connDieES ⇙ (CMfix₂ ∥⇘ newES ⇙ IG (just f0))

fix-reach : proj₁ fix₂ ─[ τ ]─► F
fix-reach = proj₂ fix₃

------------------------------------------------------------------------
-- §7  Leaf facts: what each component state offers
------------------------------------------------------------------------

-- a live mux offers only its own death
live-ev : ∀ {i} {l : Event√ (⊤ {lzero})} {M} → live i ─[ ev l ]─► M → l ≡ DIE i
live-ev st with ⟶₀-ev-inv st
... | _ , refl , _ = refl

-- a dead mux offers only its own stopOK
dead-ev : ∀ {i} {l : Event√ (⊤ {lzero})} {M} → dead i ─[ ev l ]─► M → l ≡ STOPOK i
dead-ev st with ⟶₀-ev-inv st
... | _ , refl , _ = refl

-- an unfired hook offers only its mux's death
hook-ev : ∀ {i} {l : Event√ (⊤ {lzero})} {M} → Hook i ─[ ev l ]─► M → l ≡ DIE i
hook-ev st with ⟶₀-ev-inv st
... | _ , refl , _ = refl

-- the fixed CM, after `new 0`, offers only `die 0`
cmfix₂-ev : ∀ {l : Event√ (⊤ {lzero})} {M} → CMfix₂ ─[ ev l ]─► M → l ≡ DIE f0
cmfix₂-ev st with ⟶₀-ev-inv st
... | _ , refl , _ = refl

-- Stop offers nothing and has no τ
Stop-no-ev : ∀ {l : Event√ (⊤ {lzero})} {M} → Stop {R = ⊤ {lzero}} ─[ ev l ]─► M → ⊥
Stop-no-ev (sRet ())
Stop-no-ev (sVis refl ())

Stop-no-τ : ∀ {M} → Stop {R = ⊤ {lzero}} ─[ τ ]─► M → ⊥
Stop-no-τ (sSil ())
Stop-no-τ (sTau refl ())

-- the governor tracking `t` offers no `admit` (its menu is new/notify/promote)
IGjust-no-admit : ∀ {t i} {M} → IG (just t) ─[ ev (ADMIT i) ]─► M → ⊥
IGjust-no-admit (sVis refl ())

-- the blocked governor offers only the awaited `stopOK t`, and has no τ
IGaw-ev : ∀ {t} {l : Event√ (⊤ {lzero})} {M} → IGaw t ─[ ev l ]─► M → l ≡ STOPOK t
IGaw-ev st with loop-pfx-ev-inv _ _ _ st
... | _ , refl , _ = refl

IGaw-no-τ : ∀ {t} {M} → IGaw t ─[ τ ]─► M → ⊥
IGaw-no-τ st = loop-pfx-no-τ _ _ _ st

------------------------------------------------------------------------
-- §8  W2 — in W the only visible step is `die 0`, and there is no τ
------------------------------------------------------------------------

connsW : Proc
connsW = (live f0 ∥⇘ dieES ⇙ Hook f0) ⦀ (dead f1 ∥⇘ dieES ⇙ Stop)

cmigW : Proc
cmigW = Stop ∥⇘ newES ⇙ IGaw f0

-- the connections in W offer `die 0` (mux 0 with its hook) or `stopOK 1`
connsW-ev : ∀ {l : Event√ (⊤ {lzero})} {M} → connsW ─[ ev l ]─► M → (l ≡ DIE f0) ⊎ (l ≡ STOPOK f1)
connsW-ev st with Par-ev-elim ∅ES _ (live f0 ∥⇘ dieES ⇙ Hook f0) (dead f1 ∥⇘ dieES ⇙ Stop) st
... | evSync m _ _ = ⊥-elim m
... | ev√ e _ = case e of λ ()
... | evL _ s0 with Par-ev-elim dieES _ (live f0) (Hook f0) s0
...   | evSync _ sL _ = inj₁ (live-ev sL)
...   | evL _ sL      = inj₁ (live-ev sL)
...   | evR _ sH      = inj₁ (hook-ev sH)
...   | evBoth _ sL _ = inj₁ (live-ev sL)
connsW-ev st | evR _ s1 with Par-ev-elim dieES _ (dead f1) Stop s1
...   | evSync _ sD _ = inj₂ (dead-ev sD)
...   | evL _ sD      = inj₂ (dead-ev sD)
...   | evR _ sS      = ⊥-elim (Stop-no-ev sS)
...   | evBoth _ _ sS = ⊥-elim (Stop-no-ev sS)
connsW-ev st | evBoth _ _ s1 with Par-ev-elim dieES _ (dead f1) Stop s1
...   | evSync _ sD _ = inj₂ (dead-ev sD)
...   | evL _ sD      = inj₂ (dead-ev sD)
...   | evR _ sS      = ⊥-elim (Stop-no-ev sS)
...   | evBoth _ _ sS = ⊥-elim (Stop-no-ev sS)

-- the CM/IG pair in W offers only `stopOK 0`
cmigW-ev : ∀ {l : Event√ (⊤ {lzero})} {M} → cmigW ─[ ev l ]─► M → l ≡ STOPOK f0
cmigW-ev st with Par-ev-elim newES _ Stop (IGaw f0) st
... | evSync _ sS _  = ⊥-elim (Stop-no-ev sS)
... | evL _ sS       = ⊥-elim (Stop-no-ev sS)
... | evR _ sG       = IGaw-ev sG
... | evBoth _ sS _  = ⊥-elim (Stop-no-ev sS)
... | ev√ e _        = case e of λ ()

wedge-only-die0 : ∀ {l : Event√ (⊤ {lzero})} {M} → W ─[ ev l ]─► M → l ≡ DIE f0
wedge-only-die0 st with Par-ev-elim connES _ connsW cmigW st
-- a synchronised step must be one the blocked governor offers, `stopOK 0`,
-- but neither connection offers it: mux 0 is live, mux 1 is the wrong mux
... | evSync _ sC sR with cmigW-ev sR
...   | refl with connsW-ev sC
...     | inj₁ ()
...     | inj₂ ()
-- the connections alone: `die 0` (allowed), or `stopOK 1`, which is in the
-- synchronisation set and so cannot be taken alone
wedge-only-die0 st | evL ¬m sC with connsW-ev sC
...   | inj₁ refl = refl
...   | inj₂ refl = ⊥-elim (¬m unit)
-- the CM/IG pair alone can only do `stopOK 0`, which is synchronised
wedge-only-die0 st | evR ¬m sR with cmigW-ev sR
...   | refl = ⊥-elim (¬m unit)
wedge-only-die0 st | evBoth ¬m _ sR with cmigW-ev sR
...   | refl = ⊥-elim (¬m unit)
wedge-only-die0 st | ev√ e _ = case e of λ ()

wedge-no-τ : ∀ {M} → W ─[ τ ]─► M → ⊥
wedge-no-τ st with Par-τ-elim connES _ connsW cmigW st
... | τL _ sC _ with Par-τ-elim ∅ES _ (live f0 ∥⇘ dieES ⇙ Hook f0) (dead f1 ∥⇘ dieES ⇙ Stop) sC
...   | τL _ s0 _ with Par-τ-elim dieES _ (live f0) (Hook f0) s0
...     | τL _ s _ = ⟶₀-no-τ s
...     | τR _ s _ = ⟶₀-no-τ s
wedge-no-τ st | τL _ sC _ | τR _ s1 _ with Par-τ-elim dieES _ (dead f1) Stop s1
...     | τL _ s _ = ⟶₀-no-τ s
...     | τR _ s _ = Stop-no-τ s
wedge-no-τ st | τR _ sR _ with Par-τ-elim newES _ Stop (IGaw f0) sR
...   | τL _ s _ = Stop-no-τ s
...   | τR _ s _ = IGaw-no-τ s

-- corollaries: no progress, and the await cannot complete
wedge-refuses-promote : ∀ {M} → W ─[ ev PROMOTE ]─► M → ⊥
wedge-refuses-promote st = case wedge-only-die0 st of λ ()

wedge-refuses-stopOK0 : ∀ {M} → W ─[ ev (STOPOK f0) ]─► M → ⊥
wedge-refuses-stopOK0 st = case wedge-only-die0 st of λ ()

------------------------------------------------------------------------
-- §9  F — the fix refuses the second admission while the first is live
------------------------------------------------------------------------

fix-refuses-admit1 : ∀ {M} → F ─[ ev (ADMIT f1) ]─► M → ⊥
fix-refuses-admit1 st
  with Par-ev-elim connDieES _ ((live f0 ∥⇘ dieES ⇙ Hook f0) ⦀ Conn f1) (CMfix₂ ∥⇘ newES ⇙ IG (just f0)) st
-- `admit` is synchronised, so the CM/IG pair must take it: the fixed CM
-- offers only `die 0`, and the governor offers no `admit` at all
... | evSync _ _ sR with Par-ev-elim newES _ CMfix₂ (IG (just f0)) sR
...   | evSync m _ _   = ⊥-elim m
...   | evL _ sCM      = case cmfix₂-ev sCM of λ ()
...   | evR _ sG       = IGjust-no-admit sG
...   | evBoth _ sCM _ = case cmfix₂-ev sCM of λ ()
fix-refuses-admit1 st | evL ¬m _      = ¬m unit
fix-refuses-admit1 st | evR ¬m _      = ¬m unit
fix-refuses-admit1 st | evBoth ¬m _ _ = ¬m unit
