{-# OPTIONS --guardedness #-}

-- Inbound-governor wedge model (ouroboros-network pin 4b3ab766, InboundGovernor.hs).
-- One ConnectionId; its connection incarnations are numbered by ℕ and may overlap:
-- a peer reset frees an incarnation's four-tuple while its mux is still alive, and
-- `hs` of the next one is enabled only when `admitOK` of the CM policy holds on the
-- live list: under cmPin every live incarnation is freed (the refined four-tuple rule,
-- v2 spec §4.2), under cmFix also every one is closing (v3 spec §4), released (v4 spec §4) or failedT
-- (v4.1a spec §3: the general release acts on the newest incarnation, with outcome CommitTr/UnsupportedState). `Conn` models the
-- connection threads and mux statuses, `Gov mode` the IG's map, queue and loop; a
-- `Mode` is six switches (enqP, newP, unregP, timer, cmP, relP; v2 spec §4.3, v3 spec §4.1,
-- v4 spec §4: relP = whether the IG release `rel` is modelled).
-- Every offer map is generated from a pure step function, so all reasoning is about
-- `cstep`/`gstep`.
-- Design: docs/superpowers/specs/2026-09-29-governor-wedge-release-general-design.md (v4.1a), on
-- docs/superpowers/specs/2026-09-29-governor-wedge-release-design.md (v4), on
-- docs/superpowers/specs/2026-09-29-governor-wedge-cmfix-design.md (v3), on
-- docs/superpowers/specs/2026-09-28-governor-wedge-overlap-design.md (v2; v1
-- docs/superpowers/specs/2026-09-28-governor-wedge-design.md holds the citation key)
-- Citation key (ouroboros-network paths at the pin): IG:n = line n of
-- ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor.hs ("IG" alone =
-- the inbound governor); CM = .../Ouroboros/Network/ConnectionManager/Core.hs;
-- CH = .../Ouroboros/Network/ConnectionHandler.hs (both under the same framework/lib).
module CSP.Examples.GovernorWedge.Model where

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as M
open import Data.Maybe.Properties using (≡-dec)
open import Data.List using (List; []; _∷_; _∷ʳ_)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum using (_⊎_)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees
open PTree

-- actions only the connection thread of incarnation r performs; reset = the peer resets r's TCP connection
data ConnAct : Set where
  run abort reset fail close : ℕ → ConnAct

-- actions only the inbound governor performs
data GovAct : Set where
  promote take tmo : GovAct

-- the six channels; hs / trace / stopped / rel are shared by Conn and Gov (rel (x , b) = the IG releases its entry x,
-- IG:514-521, and the CM answers CommitTr (b = true) or UnsupportedState (b = false); v4.1a spec §3)
data Ev : Set → Set where
  hs      : Ev ℕ
  trace   : Ev (ℕ × Maybe ℕ)
  stopped : Ev ℕ
  conn    : Ev ConnAct
  gov     : Ev GovAct
  rel     : Ev (ℕ × Bool)

-- decidable equality on the existential event index (what `CSP.Operators` needs)
Ev-≟ : (x y : AnyTypes Ev) → Dec (x ≡ y)
Ev-≟ (_ , hs)      (_ , hs)      = yes refl
Ev-≟ (_ , trace)   (_ , trace)   = yes refl
Ev-≟ (_ , stopped) (_ , stopped) = yes refl
Ev-≟ (_ , conn)    (_ , conn)    = yes refl
Ev-≟ (_ , gov)     (_ , gov)     = yes refl
Ev-≟ (_ , hs)      (_ , trace)   = no λ ()
Ev-≟ (_ , hs)      (_ , stopped) = no λ ()
Ev-≟ (_ , hs)      (_ , conn)    = no λ ()
Ev-≟ (_ , hs)      (_ , gov)     = no λ ()
Ev-≟ (_ , trace)   (_ , hs)      = no λ ()
Ev-≟ (_ , trace)   (_ , stopped) = no λ ()
Ev-≟ (_ , trace)   (_ , conn)    = no λ ()
Ev-≟ (_ , trace)   (_ , gov)     = no λ ()
Ev-≟ (_ , stopped) (_ , hs)      = no λ ()
Ev-≟ (_ , stopped) (_ , trace)   = no λ ()
Ev-≟ (_ , stopped) (_ , conn)    = no λ ()
Ev-≟ (_ , stopped) (_ , gov)     = no λ ()
Ev-≟ (_ , conn)    (_ , hs)      = no λ ()
Ev-≟ (_ , conn)    (_ , trace)   = no λ ()
Ev-≟ (_ , conn)    (_ , stopped) = no λ ()
Ev-≟ (_ , conn)    (_ , gov)     = no λ ()
Ev-≟ (_ , gov)     (_ , hs)      = no λ ()
Ev-≟ (_ , gov)     (_ , trace)   = no λ ()
Ev-≟ (_ , gov)     (_ , stopped) = no λ ()
Ev-≟ (_ , gov)     (_ , conn)    = no λ ()
Ev-≟ (_ , rel)     (_ , rel)     = yes refl
Ev-≟ (_ , rel)     (_ , hs)      = no λ ()
Ev-≟ (_ , rel)     (_ , trace)   = no λ ()
Ev-≟ (_ , rel)     (_ , stopped) = no λ ()
Ev-≟ (_ , rel)     (_ , conn)    = no λ ()
Ev-≟ (_ , rel)     (_ , gov)     = no λ ()
Ev-≟ (_ , hs)      (_ , rel)     = no λ ()
Ev-≟ (_ , trace)   (_ , rel)     = no λ ()
Ev-≟ (_ , stopped) (_ , rel)     = no λ ()
Ev-≟ (_ , conn)    (_ , rel)     = no λ ()
Ev-≟ (_ , gov)     (_ , rel)     = no λ ()

open import Semantics.LTS {E = Ev} {I = ExtI Ev}
open import CSP.Operators Ev-≟
open EventSet

-- return type of every process
U : Set
U = ⊤ {0ℓ}

-- the process type
Proc : Set₁
Proc = PTree Ev (ExtI Ev) U

-- phase of one live incarnation's connection thread; released = the IG released it (CM sees Terminating, mux alive);
-- failedT = its mux failed (terminal), not yet traced, and the CM sees it Terminating: released then failed (the cancel
-- landing, CM:636-637) or failed then released (v4.1a spec §3)
data IPhase : Set where
  hsd running failed closing released failedT : IPhase

-- decidable equality on phases
_≟ᴾ_ : (p q : IPhase) → Dec (p ≡ q)
hsd     ≟ᴾ hsd     = yes refl
hsd     ≟ᴾ running = no λ ()
hsd     ≟ᴾ failed  = no λ ()
hsd     ≟ᴾ closing = no λ ()
running ≟ᴾ hsd     = no λ ()
running ≟ᴾ running = yes refl
running ≟ᴾ failed  = no λ ()
running ≟ᴾ closing = no λ ()
failed  ≟ᴾ hsd     = no λ ()
failed  ≟ᴾ running = no λ ()
failed  ≟ᴾ failed  = yes refl
failed  ≟ᴾ closing = no λ ()
closing ≟ᴾ hsd     = no λ ()
closing ≟ᴾ running = no λ ()
closing ≟ᴾ failed  = no λ ()
closing ≟ᴾ closing = yes refl
hsd      ≟ᴾ released = no λ ()
running  ≟ᴾ released = no λ ()
failed   ≟ᴾ released = no λ ()
closing  ≟ᴾ released = no λ ()
released ≟ᴾ hsd      = no λ ()
released ≟ᴾ running  = no λ ()
released ≟ᴾ failed   = no λ ()
released ≟ᴾ closing  = no λ ()
released ≟ᴾ released = yes refl
hsd      ≟ᴾ failedT  = no λ ()
running  ≟ᴾ failedT  = no λ ()
failed   ≟ᴾ failedT  = no λ ()
closing  ≟ᴾ failedT  = no λ ()
released ≟ᴾ failedT  = no λ ()
failedT  ≟ᴾ hsd      = no λ ()
failedT  ≟ᴾ running  = no λ ()
failedT  ≟ᴾ failed   = no λ ()
failedT  ≟ᴾ closing  = no λ ()
failedT  ≟ᴾ released = no λ ()
failedT  ≟ᴾ failedT  = yes refl

-- one live incarnation: id, phase, and whether a peer reset has freed its four-tuple
record Inc : Set where
  constructor mkInc
  field
    iid   : ℕ
    iph   : IPhase
    freed : Bool
open Inc public

-- connection state: next incarnation id, live incarnations (oldest first), terminal muxes
record CState : Set where
  constructor cst
  field
    next : ℕ
    live : List Inc
    ran  : List ℕ
open CState public

-- every live incarnation has been reset (the four-tuple is free)
allFreed : List Inc → Bool
allFreed []                 = true
allFreed (mkInc _ _ f ∷ is) = f ∧ allFreed is

-- the connection manager's policy for a duplicate ConnectionId: the pin's overwrite, or 1ccd17298's refusal
data CMPolicy : Set where
  cmPin cmFix : CMPolicy

-- every live incarnation is closing (traced or aborted), released, or failedT (released and failed, either order), so the CM sees it Terminating
allClosing : List Inc → Bool
allClosing []                        = true
allClosing (mkInc _ closing _ ∷ is)  = allClosing is
allClosing (mkInc _ released _ ∷ is) = allClosing is
allClosing (mkInc _ failedT _ ∷ is)  = allClosing is
allClosing (mkInc _ _       _ ∷ is) = false

-- may a new handshake be admitted: kernel rule (pin), plus the CM's refusal of live duplicates (fix)
admitOK : CMPolicy → List Inc → Bool
admitOK cmPin is = allFreed is
admitOK cmFix is = allFreed is ∧ allClosing is

-- admitOK entails the kernel rule: cmFix's extra allClosing conjunct drops out by cases on allFreed
admitOK-freed : ∀ pol is → admitOK pol is ≡ true → allFreed is ≡ true
admitOK-freed cmPin is eq = eq
admitOK-freed cmFix is eq with allFreed is | eq
... | true  | _  = refl
... | false | ()

-- move incarnation r from phase p to p′, or nothing if r is not live in p
movePh : ℕ → IPhase → IPhase → List Inc → Maybe (List Inc)
movePh r p p′ [] = nothing
movePh r p p′ (mkInc x ph f ∷ is) with r ≟ x | ph ≟ᴾ p
... | yes _ | yes _ = just (mkInc x p′ f ∷ is)
... | _     | _     = M.map (mkInc x ph f ∷_) (movePh r p p′ is)

-- a peer reset of r, allowed while r is live in hsd, running or released and not yet freed
freeIt : ℕ → List Inc → Maybe (List Inc)
freeIt r [] = nothing
freeIt r (mkInc x ph f ∷ is) with r ≟ x
... | no  _ = M.map (mkInc x ph f ∷_) (freeIt r is)
... | yes _ = resetOK ph f
  where
    -- the reset is enabled only in hsd/running/released and only once
    resetOK : IPhase → Bool → Maybe (List Inc)
    resetOK hsd      false = just (mkInc x hsd true ∷ is)
    resetOK running  false = just (mkInc x running true ∷ is)
    resetOK released false = just (mkInc x released true ∷ is)
    resetOK _        _     = nothing

-- remove r once it is live in closing (socket closed)
closeIt : ℕ → List Inc → Maybe (List Inc)
closeIt r [] = nothing
closeIt r (mkInc x ph f ∷ is) with r ≟ x | ph ≟ᴾ closing
... | yes _ | yes _ = just is
... | _     | _     = M.map (mkInc x ph f ∷_) (closeIt r is)

-- the newest live incarnation (the last one): the one the CM's map entry for the ConnectionId points to (CM:1145)
newest : List Inc → Maybe Inc
newest []           = nothing
newest (i ∷ [])     = just i
newest (_ ∷ j ∷ is) = newest (j ∷ is)

-- the CM half of a release with outcome b, acting on the newest incarnation y (by its id; ids are unique, Invariant.uniq):
-- hsd/running → released and failed → failedT for both outcomes; otherwise CommitTr changes nothing, UnsupportedState is refused
relLive : Bool → Maybe Inc → List Inc → Maybe (List Inc)
relLive _     (just (mkInc y hsd _))     is = movePh y hsd released is
relLive _     (just (mkInc y running _)) is = movePh y running released is
relLive _     (just (mkInc y failed _))  is = movePh y failed failedT is
relLive true  _                          is = just is
relLive false _                          _  = nothing

-- apply a live-list update, keeping next and ran
onLive : (List Inc → Maybe (List Inc)) → CState → Maybe CState
onLive f (cst n is ts) = M.map (λ is′ → cst n is′ ts) (f is)

-- what the mux callback enqueues: the looked-up mux (pin), a payload-free item (main), its own mux (fix #2)
data EnqPolicy : Set where
  atTrace atHandle own : EnqPolicy

-- NewConnection for a key already present: keep the old entry (IG:378) or replace it
data NewPolicy : Set where
  keep replace : NewPolicy

-- after the await ends: delete by key (IG:406) or only if the entry is the awaited mux
data UnregPolicy : Set where
  byKey idChecked : UnregPolicy

-- an IG variant as six switches (the fifth is the CM's duplicate-admission policy, the sixth whether the IG release is modelled)
record Mode : Set where
  constructor mode
  field
    enqP   : EnqPolicy
    newP   : NewPolicy
    unregP : UnregPolicy
    timer  : Bool
    cmP    : CMPolicy
    relP   : Bool
open Mode public

-- the pinned IG (4b3ab766)
AsBuilt : Mode
AsBuilt = mode atTrace keep byKey false cmPin false

-- origin/main 2e83f1a3: lookup at handle time instead of at trace time
Main : Mode
Main = mode atHandle keep byKey false cmPin false

-- fix #2: the callback carries its own mux id instead of a looked-up value
CarryMux : Mode
CarryMux = mode own keep byKey false cmPin false

-- fix #1: the await has a timeout that falls through to the unregister
Timeout : Mode
Timeout = mode atTrace keep byKey true cmPin false

-- NewConnection for a key already present replaces the entry instead of keeping it
ReplaceEntry : Mode
ReplaceEntry = mode atTrace replace byKey false cmPin false

-- fix #2 plus an identity check before unregistering
CarryMuxId : Mode
CarryMuxId = mode own keep idChecked false cmPin false

-- every fix combined
FullFix : Mode
FullFix = mode own replace idChecked false cmPin false

-- the leios branch with the CM fix (1ccd17298) cherry-picked onto the as-built lookup policy
AsBuiltCM : Mode
AsBuiltCM = mode atTrace keep byKey false cmFix false

-- real origin/main: 2e83f1a3 (lookup at handle time) plus the CM fix 1ccd17298
MainReal : Mode
MainReal = mode atHandle keep byKey false cmFix false

-- the CM fix plus fix #2 (own mux id)
CarryMuxCM : Mode
CarryMuxCM = mode own keep byKey false cmFix false

-- AsBuiltCM with the IG release modelled
AsBuiltCMR : Mode
AsBuiltCMR = mode atTrace keep byKey false cmFix true

-- MainReal with the IG release modelled
MainRealR : Mode
MainRealR = mode atHandle keep byKey false cmFix true

-- CarryMuxCM with the IG release modelled
CarryMuxCMR : Mode
CarryMuxCMR = mode own keep byKey false cmFix true

-- CarryMuxCM plus the identity check, with the IG release modelled
CarryMuxIdCMR : Mode
CarryMuxIdCMR = mode own keep idChecked false cmFix true

-- IG queue item: NewConnection r / MuxFinished awaiting r / MuxFinished without payload (main)
data Item : Set where
  nc mf : ℕ → Item
  mfK   : Item

-- IG loop phase: ready to gather, or blocked in `atomically (Mux.stopped r)` (IG:397)
data GPhase : Set where
  idle  : GPhase
  await : ℕ → GPhase

-- IG state: the one map entry, the information-channel queue, the loop phase
record GState : Set where
  constructor gst
  field
    entry  : Maybe ℕ
    queue  : List Item
    gphase : GPhase
open GState public

-- what the callback of r enqueues after its atomic lookup (value v), per policy (IG:692-699)
enq : EnqPolicy → ℕ → Maybe ℕ → List Item → List Item
enq atTrace  _ (just v) q = q ∷ʳ mf v
enq atTrace  _ nothing  q = q
enq atHandle _ _        q = q ∷ʳ mfK
enq own      r _        q = q ∷ʳ mf r

-- IG state after taking queue head i (remaining queue q)
takeG : NewPolicy → Maybe ℕ → Item → List Item → GState
takeG _       nothing  (nc r) q = gst (just r) q idle
takeG keep    (just x) (nc _) q = gst (just x) q idle   -- IG:378
takeG replace (just _) (nc r) q = gst (just r) q idle
takeG _       e        (mf r) q = gst e q (await r)
takeG _       (just x) mfK    q = gst (just x) q (await x)
takeG _       nothing  mfK    q = gst nothing q idle

-- the entry after the await on r ends
unreg : UnregPolicy → ℕ → Maybe ℕ → Maybe ℕ
unreg byKey     _ _        = nothing                  -- IG:406
unreg idChecked r (just x) with x ≟ r
... | yes _ = nothing
... | no  _ = just x
unreg idChecked _ nothing  = nothing

-- one Conn move on (channel, value, CM policy), or nothing if refused; channel-first clauses keep disjointness by refl;
-- fail also from released (to failedT: the CM stays Terminating, CM:636-637), trace also from failedT, rel acts on the
-- newest incarnation (relLive; policy-independent)
cstep : (at : AnyTypes Ev) → proj₁ at → CMPolicy → CState → Maybe CState
cstep (_ , gov) _ _ _ = nothing
cstep (_ , stopped) t _ (cst n is ts) with t ∈? ts
... | yes _ = just (cst n is ts)
... | no  _ = nothing
-- ponytail: hs makes the promise write and CM's NewConnection enqueue one atomic step (CH:377 outbound / CH:449 inbound, CM:1016); in the code the enqueue can lag or be skipped (CM:991-995, when the handler's cleanup wins). Upgrade: a separate CM process per incarnation.
cstep (_ , hs) r pol (cst n is ts) with r ≟ n | admitOK pol is
... | yes _ | true = just (cst (suc n) (is ∷ʳ mkInc n hsd false) ts)
... | _     | _    = nothing
cstep (_ , conn) (run r)   _ c = onLive (movePh r hsd running) c
cstep (_ , conn) (abort r) _ c = onLive (movePh r hsd closing) c
cstep (_ , conn) (reset r) _ c = onLive (freeIt r) c
cstep (_ , conn) (fail r) _ (cst n is ts) =
  M.map (λ is′ → cst n is′ (r ∷ ts)) (movePh r running failed is M.<∣> movePh r released failedT is)
cstep (_ , conn) (close r) _ c = onLive (closeIt r) c
cstep (_ , trace) (r , _) _ c = onLive (λ is → movePh r failed closing is M.<∣> movePh r failedT closing is) c
cstep (_ , rel) (_ , b) _ c = onLive (λ is → relLive b (newest is) is) c

-- the IG's entry after a release answered b: CommitTr unregisters (IG:514-521), UnsupportedState keeps it (IG:544)
relEntry : Bool → Maybe ℕ → Maybe ℕ
relEntry true  _ = nothing
relEntry false e = e

-- one Gov move; hs/trace enqueue in every phase, trace only for v = the current entry (atomic lookup);
-- rel (x , b) only when idle, relP holds and the entry is x; the entry becomes relEntry b e
gstep : (at : AnyTypes Ev) → proj₁ at → Mode → GState → Maybe GState
gstep (_ , conn) _ _ _ = nothing
gstep (_ , rel) (x , b) m (gst e q idle) with relP m | ≡-dec _≟_ e (just x)
... | true | yes _ = just (gst (relEntry b e) q idle)
... | _    | _     = nothing
gstep (_ , rel) _ _ _ = nothing
gstep (_ , hs) r _ (gst e q ph) = just (gst e (q ∷ʳ nc r) ph)
gstep (_ , trace) (r , v) m (gst e q ph) with ≡-dec _≟_ v e
... | yes _ = just (gst e (enq (enqP m) r v q) ph)
... | no  _ = nothing
gstep (_ , gov) promote _ (gst e q idle) = just (gst e q idle)
gstep (_ , gov) take m (gst e (i ∷ q) idle) = just (takeG (newP m) e i q)
gstep (_ , gov) tmo m (gst e q (await r)) with timer m
... | true  = just (gst (unreg (unregP m) r e) q idle)  -- fix #1 falls through to the unregister
... | false = nothing
gstep (_ , gov) _ _ _ = nothing
gstep (_ , stopped) t m (gst e q (await r)) with t ≟ r
... | yes _ = just (gst (unreg (unregP m) r e) q idle)
... | no  _ = nothing
gstep (_ , stopped) _ _ _ = nothing

-- the connection threads under CM policy pol, generated from cstep
Conn : CMPolicy → CState → Proc
force (Conn pol c) = react
  (λ where (X , ch) a → case cstep (X , ch) a pol c of λ where
                          (just c′) → just (Conn pol c′)
                          nothing   → nothing)
  ∅t

-- the inbound governor, generated from gstep
Gov : Mode → GState → Proc
force (Gov m g) = react
  (λ where (X , ch) a → case gstep (X , ch) a m g of λ where
                          (just g′) → just (Gov m g′)
                          nothing   → nothing)
  ∅t

-- shared channels: handshake enqueue, callback lookup+enqueue, Mux.stopped, the IG release
csS : AnyTypes Ev → Set
csS (_ , hs)      = ⊤ {0ℓ}
csS (_ , trace)   = ⊤ {0ℓ}
csS (_ , stopped) = ⊤ {0ℓ}
csS (_ , conn)    = ⊥
csS (_ , gov)     = ⊥
csS (_ , rel)     = ⊤ {0ℓ}

-- … decided
decS : (at : AnyTypes Ev) → Dec (csS at)
decS (_ , hs)      = yes tt
decS (_ , trace)   = yes tt
decS (_ , stopped) = yes tt
decS (_ , conn)    = no (λ z → z)
decS (_ , gov)     = no (λ z → z)
decS (_ , rel)     = yes tt

-- the synchronisation set
syncES : EventSet
syncES = chanSet csS decS

-- the composite at model state (c , g)
SysAt : Mode → CState → GState → Proc
SysAt m c g = Conn (cmP m) c ∥⇘ syncES ⇙ Gov m g

-- initial states: no incarnation created yet; IG empty and idle
c₀ : CState
c₀ = cst 0 [] []

-- the IG's initial state: empty map, empty queue, idle loop
g₀ : GState
g₀ = gst nothing [] idle

-- the system under each IG variant
Sys : Mode → Proc
Sys m = SysAt m c₀ g₀

-- r is live and its mux can still run (hsd or running), freed or not
LiveRun : CState → ℕ → Set
LiveRun c r = Any (λ i → iid i ≡ r × (iph i ≡ hsd ⊎ iph i ≡ running)) (live c)

-- r's mux is alive: live in hsd, running or released (a released mux is still Ready; a failedT one is dead)
LiveMux : CState → ℕ → Set
LiveMux c r = Any (λ i → iid i ≡ r × (iph i ≡ hsd ⊎ iph i ≡ running ⊎ iph i ≡ released)) (live c)

-- r is active: live, in hsd or running, and not freed by a peer reset
Active : CState → ℕ → Set
Active c r = Any (λ i → iid i ≡ r × (iph i ≡ hsd ⊎ iph i ≡ running) × freed i ≡ false) (live c)

-- the IG is idle with an empty queue and tracks the active incarnation, if any
Tracked : CState → GState → Set
Tracked c g = gphase g ≡ idle × queue g ≡ [] × (∀ r → Active c r → entry g ≡ just r)

-- trace letters
lbl : (at : AnyTypes Ev) → proj₁ at → Event√ U
lbl (X , ch) a = evl (evLabel X ch a)

-- trace letters: incarnation r's handshake, and Mux.stopped of mux r
HS ST : ℕ → Event√ U
HS r = lbl (ℕ , hs) r
ST r = lbl (ℕ , stopped) r

-- trace letter: mux r's callback, having looked the key up to v
TR : ℕ → Maybe ℕ → Event√ U
TR r v = lbl ((ℕ × Maybe ℕ) , trace) (r , v)

-- trace letter: the IG releases its entry x, the CM answering CommitTr (b = true) or UnsupportedState (b = false)
REL : ℕ → Bool → Event√ U
REL x b = lbl ((ℕ × Bool) , rel) (x , b)

-- trace letter: a connection-thread action
CN : ConnAct → Event√ U
CN a = lbl (ConnAct , conn) a

-- trace letter: an IG action
GV : GovAct → Event√ U
GV a = lbl (GovAct , gov) a

-- channel disjointness holds by computation on OPEN states, for any CM policy
conn-no-gov : ∀ (a : GovAct) (pol : CMPolicy) (c : CState) → cstep (GovAct , gov) a pol c ≡ nothing
conn-no-gov _ _ _ = refl

-- the IG offers no connection-thread action, by computation on open states
gov-no-conn : ∀ (a : ConnAct) (m : Mode) (g : GState) → gstep (ConnAct , conn) a m g ≡ nothing
gov-no-conn _ _ _ = refl

-- IG:378 — keep policy leaves the existing entry
keep-entry : ∀ x r q → takeG keep (just x) (nc r) q ≡ gst (just x) q idle
keep-entry _ _ _ = refl

-- replace policy installs the new incarnation
replace-entry : ∀ x r q → takeG replace (just x) (nc r) q ≡ gst (just r) q idle
replace-entry _ _ _ = refl

-- the identity check keeps an entry that is not the awaited mux
idcheck-keeps : unreg idChecked 1 (just 2) ≡ just 2
idcheck-keeps = refl

-- the handshake of incarnation 0 is offered initially
hs₀ : cstep (ℕ , hs) 0 cmPin c₀ ≡ just (cst 1 (mkInc 0 hsd false ∷ []) [])
hs₀ = refl

-- the four-tuple rule: no new handshake while an un-freed incarnation is live
hs-blocked : cstep (ℕ , hs) 1 cmPin (cst 1 (mkInc 0 running false ∷ []) []) ≡ nothing
hs-blocked = refl

-- after a peer reset the next handshake is allowed
hs-after-reset : cstep (ℕ , hs) 1 cmPin (cst 1 (mkInc 0 running true ∷ []) [])
               ≡ just (cst 2 (mkInc 0 running true ∷ mkInc 1 hsd false ∷ []) [])
hs-after-reset = refl

-- the pin's CM admits a reset duplicate while the old incarnation still runs
admit-pin : admitOK cmPin (mkInc 0 running true ∷ []) ≡ true
admit-pin = refl

-- the fixed CM refuses it (the old connection is still live in the CM)
admit-fix-refuses : admitOK cmFix (mkInc 0 running true ∷ []) ≡ false
admit-fix-refuses = refl

-- the fixed CM admits once the old incarnation is closing and freed
admit-fix-closing : admitOK cmFix (mkInc 0 closing true ∷ []) ≡ true
admit-fix-closing = refl

-- the kernel rule still applies under the fix: an un-reset closing incarnation holds the tuple
admit-fix-unfreed : admitOK cmFix (mkInc 0 closing false ∷ []) ≡ false
admit-fix-unfreed = refl

-- every v2 named mode uses the pin's CM
v2-modes-pin : cmP AsBuilt ≡ cmPin × cmP Main ≡ cmPin × cmP CarryMux ≡ cmPin × cmP Timeout ≡ cmPin
             × cmP ReplaceEntry ≡ cmPin × cmP CarryMuxId ≡ cmPin × cmP FullFix ≡ cmPin
v2-modes-pin = refl , refl , refl , refl , refl , refl , refl

-- every existing named mode leaves the release out
old-modes-norel : relP AsBuilt ≡ false × relP Main ≡ false × relP CarryMux ≡ false × relP Timeout ≡ false
                × relP ReplaceEntry ≡ false × relP CarryMuxId ≡ false × relP FullFix ≡ false
                × relP AsBuiltCM ≡ false × relP MainReal ≡ false × relP CarryMuxCM ≡ false
old-modes-norel = refl , refl , refl , refl , refl , refl , refl , refl , refl , refl

-- CommitTr on a running newest incarnation releases it; the IG clears its entry
rel-commit-conn : cstep ((ℕ × Bool) , rel) (0 , true) cmFix (cst 1 (mkInc 0 running false ∷ []) [])
                ≡ just (cst 1 (mkInc 0 released false ∷ []) [])
rel-commit-conn = refl
-- (IG side of CommitTr) the IG clears its entry
rel-commit-gov : gstep ((ℕ × Bool) , rel) (0 , true) AsBuiltCMR (gst (just 0) [] idle) ≡ just (gst nothing [] idle)
rel-commit-gov = refl

-- UnsupportedState: the IG keeps its entry
rel-unsup-gov : gstep ((ℕ × Bool) , rel) (0 , false) AsBuiltCMR (gst (just 0) [] idle) ≡ just (gst (just 0) [] idle)
rel-unsup-gov = refl

-- the CM acts on the newest incarnation, not on the IG's x
rel-newest : cstep ((ℕ × Bool) , rel) (0 , true) cmFix (cst 2 (mkInc 0 failedT true ∷ mkInc 1 running false ∷ []) (0 ∷ []))
           ≡ just (cst 2 (mkInc 0 failedT true ∷ mkInc 1 released false ∷ []) (0 ∷ []))
rel-newest = refl

-- entry-only clear: nothing live, CommitTr changes no CM state
rel-entry-only : cstep ((ℕ × Bool) , rel) (0 , true) cmFix (cst 1 [] []) ≡ just (cst 1 [] [])
rel-entry-only = refl

-- UnsupportedState needs an established newest incarnation
rel-unsup-refused : cstep ((ℕ × Bool) , rel) (0 , false) cmFix (cst 1 [] []) ≡ nothing
rel-unsup-refused = refl

-- a failed newest incarnation becomes failedT, and the fixed CM admits over it once freed
rel-failed : cstep ((ℕ × Bool) , rel) (0 , false) cmFix (cst 1 (mkInc 0 failed true ∷ []) (0 ∷ []))
           ≡ just (cst 1 (mkInc 0 failedT true ∷ []) (0 ∷ []))
rel-failed = refl
-- (admission over failedT) the fixed CM counts a freed failedT incarnation as Terminating
admit-fix-failedT : admitOK cmFix (mkInc 0 failedT true ∷ []) ≡ true
admit-fix-failedT = refl

-- without the release switch the IG refuses it (unchanged)
rel-gov-off : gstep ((ℕ × Bool) , rel) (0 , true) AsBuiltCM (gst (just 0) [] idle) ≡ nothing
rel-gov-off = refl

-- the fixed CM admits a duplicate over a released (Terminating) incarnation once freed
admit-fix-released : admitOK cmFix (mkInc 0 released true ∷ []) ≡ true
admit-fix-released = refl

-- a released mux can still fail (the cancel landing); the CM keeps it Terminating, so it becomes failedT
fail-released : cstep (ConnAct , conn) (fail 0) cmFix (cst 1 (mkInc 0 released true ∷ []) [])
              ≡ just (cst 1 (mkInc 0 failedT true ∷ []) (0 ∷ []))
fail-released = refl

-- older running, newest closing: CommitTr changes no CM state (state unreachable under cmFix; a unit test of relLive)
rel-newest-closing-commit : cstep ((ℕ × Bool) , rel) (0 , true) cmFix (cst 2 (mkInc 0 running true ∷ mkInc 1 closing false ∷ []) []) ≡ just (cst 2 (mkInc 0 running true ∷ mkInc 1 closing false ∷ []) [])
rel-newest-closing-commit = refl

-- older running, newest closing: UnsupportedState is refused (state unreachable under cmFix; a unit test of relLive)
rel-newest-closing-unsup : cstep ((ℕ × Bool) , rel) (0 , false) cmFix (cst 2 (mkInc 0 running true ∷ mkInc 1 closing false ∷ []) []) ≡ nothing
rel-newest-closing-unsup = refl
