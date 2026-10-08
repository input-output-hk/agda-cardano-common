{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- LeiosNotify (cardano-blueprint table, no pipelining): RECEPTIVENESS of the real peers,
-- and FAILURES-DIVERGENCES conformance of the real pair to the table.
--
-- Everything is reused from `LeiosNotifyQuit.agda`: the real client at `(l , lo)`, the
-- renamed real server `srv`, the pair `sys`, the abstraction framework (`Abs` / `AbsI` /
-- `Gen` / `GenI` / `Prod`) and the component abstractions `CA` / `SA`.  New here:
--
--   * `row` — the blueprint table AS DATA (state × message ↦ next state or End);
--   * `Tbl` — the table as a process, generic in WHO resolves each state: an agency state
--     whose choice is INTERNAL is a τ-menu (an `ExtI`-indexed internal choice over every
--     payload `x` of the state's channel whose message is a row: `react ∅v τB`, one τ-branch
--     per value), a state whose choice is EXTERNAL is a `pchoice` accepting every such `x`;
--   * its abstraction `TA` (elim + intro), a generic hiding abstraction `HideA`, a generic
--     invariant ⇒ deadlock-freedom lemma `InvDL`, and abstract weak steps `Wk` / `WkI`.
--
-- (R) RECEPTIVENESS.  `ServerEnv` (server states internal, client states external) and
--     `ClientEnv` (the converse) are the MOST GENERAL table-conforming partners: every
--     message the table lets that side send, with ANY payload (any header, point, size,
--     vote list, ⊤ for MsgCanceled; any time / mode / length envelope), and they accept
--     every message the table lets the other side send.  Synchronised on the wire, api /
--     done left OPEN (the application is maximally cooperative, so the only way to get
--     stuck is a wire refusal):
--       `client-receptive : DeadlockFree (client ∥ ServerEnv)`,
--       `server-receptive : DeadlockFree (srv ∥ ClientEnv)`, plus divergence freedom.
--     Why this is "never refuses a table-permitted message": whenever the partner holds
--     agency it resolves its choice by a τ and then offers ONE message only; the real peer
--     at that point (StBusy / StQuit for the client, StIdle for the server) has no agency
--     and no api move, so the pair is stuck unless the peer accepts that very message.
--     As every message / payload is chosen on some run, deadlock freedom = acceptance of
--     all of them, in every reachable state.
--     NEGATIVE CONTROL: `badClient` is the most general client with the row
--     StBusy --MsgCanceled--> StIdle deleted (the upstream "throw on MsgCanceled");
--     `bad-deadlock : HasDeadlock (badClient ∥ ServerEnv)` (after one RequestNext).
--
-- (FD) `LNPSpec⊓` is the table with EVERY agency choice internal (StIdle: the client ⊓
--     RequestNext / Quit; StBusy: the server ⊓ the four replies and MsgCanceled with any
--     payload; StQuit: MsgDone), over the wire only.  `sysH = sys ∖ apiDoneES` hides every
--     api and done event of the pair, so the payloads the pair can produce range over all
--     values supplied through the hidden api.  We prove
--       `sysH≈DR : sysH ≈DR LNPSpec⊓`   (divergence-respecting weak bisimulation), hence
--       `LNPSpec⊓-⊑FD : LNPSpec⊓ ⊑FD sysH`  and  `LNPSpec⊓-≈FD : LNPSpec⊓ ≈FD sysH`,
--     and `sysH-divergenceFree` (hiding introduces no divergence: every api / done event is
--     followed by a wire event or √).  RESTRICTION: the model's peers build every wire
--     payload with the fixed envelope `time₀ / length₀` and the mode of the sender
--     (`LeiosNotifyQuit.pay`), so `LNPSpec⊓` emits the message content chosen freely but
--     with that envelope (`nzS`); with an arbitrary envelope the spec would be strictly
--     more nondeterministic than the pair and only the refinement, not ≈DR, could hold.
--     `⊑FD` goes through `Semantics.DRImpliesFD`, i.e. relies on csp-ptree's classical
--     axiom `¬-divergent→normal` (as every ≈DR ⇒ ⊑FD result in the estate does).
------------------------------------------------------------------------

open import Cardano_network.Params using (Params)

module Cardano_network.Parametric.Leios.LeiosNotifyQuitFD (p : Params) where

open import Data.Bool using (Bool; true; false; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapM)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; suc; _+_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (+-monoˡ-<; +-monoʳ-<)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Unit as U
open import Data.Unit.Polymorphic using (tt)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Decidable.Core using (T?)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Process_Trees
open import Cardano_network.Base
open import Cardano_network.Net p
open import Cardano_network.Data p
open import Cardano_network.LeiosNotifyP p
open import Cardano_network.Parametric.Leios.LeiosNotifyQuit p
open Params p using (Time; Length; time₀; length₀)

open import CSP.Operators LNPEv-≟
  using (Ret; Output; pchoice; iter; iter-bind; iterV; iterT; Par⊤; EventSet; ∅v; _∖_)
open EventSet
open import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv}
open import Semantics.WeakBisim {E = LNPEv} {I = ExtI LNPEv}
  using (_─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wτ; wev)
open import Semantics.DRBisim {E = LNPEv} {I = ExtI LNPEv} using (_≈DR_)
open import Semantics.BisimFromRel {E = LNPEv} {I = ExtI LNPEv} using (module DRFromRel)
open import Semantics.FailuresDivergences {E = LNPEv} {I = ExtI LNPEv} using (_⊑FD_; _≈FD_)
open import Semantics.DRImpliesFD {E = LNPEv} {I = ExtI LNPEv} using (drbisim→⊑FD; drbisim→≈FD)
open import Semantics.Deadlock {E = LNPEv} {I = ExtI LNPEv}
  using (IsStuck; DeadlockFree; HasDeadlock; _⟹∖√⟨_⟩_)
open import Semantics.DivergenceFree {E = LNPEv} {I = ExtI LNPEv} using (DivergenceFree)
open import CSP.Laws.Traces.TraceLawsHide LNPEv-≟
  using (fHide-ret; fHide-ret-inv; Hide-τ; Hide-keep; Hide-hidden; Hide-τ-elim; hτP; hτH; Hide-ev-elim; heV)
open import CSP.Laws.DivFree.Loop LNPEv-≟ using (itτ; itBack; iter-τ-elim; iter-ev-elim)

------------------------------------------------------------------------
-- §0  Generic step lemmas (no Leios content)
------------------------------------------------------------------------

-- a τ of the body lifts through `iter-bind`
iterτ : ∀ {A : Set} {k : A → PTree LNPEv (ExtI LNPEv) (A ⊎ Rr)} {T₀ T₁ : PTree LNPEv (ExtI LNPEv) (A ⊎ Rr)}
      → T₀ ─[ τ ]─► T₁ → iter-bind T₀ k ─[ τ ]─► iter-bind T₁ k
iterτ {k = k} {T₀} {T₁} (sTau {v = v} {τc = τc} {i = i} {a = a} eqT br) = sTau eqF eqB
  where
  -- the bound node is the body's react node, re-wrapped
  eqF : PTree.force (iter-bind T₀ k) ≡ react (iterV k (react v τc)) (iterT k (react v τc))
  eqF rewrite eqT = refl
  -- … whose τ-branch is the body's, re-wrapped
  eqB : iterT k (react v τc) i a ≡ just (iter-bind T₁ k)
  eqB rewrite br = refl
iterτ {k = k} {T₀} {T₁} (sSil eqT) = sSil eqF
  where
  -- a silent body stays silent under the bind
  eqF : PTree.force (iter-bind T₀ k) ≡ sil (iter-bind T₁ k)
  eqF rewrite eqT = refl

-- an `iter-bind` over a body that never returns does not return
iterNoRet : ∀ {A : Set} {k : A → PTree LNPEv (ExtI LNPEv) (A ⊎ Rr)} {T₀ : PTree LNPEv (ExtI LNPEv) (A ⊎ Rr)}
          → (∀ {r} → PTree.force T₀ ≡ ret r → ⊥) → ∀ {r} → PTree.force (iter-bind T₀ k) ≡ ret r → ⊥
iterNoRet {T₀ = T₀} noRet eq with PTree.force T₀
... | ret (inj₁ _) = case eq of λ ()
... | ret (inj₂ _) = noRet refl
... | sil _        = case eq of λ ()
... | react _ _    = case eq of λ ()

-- `deadlock` makes no τ
dlNoτ : ∀ {t : Tree} → deadlock ─[ τ ]─► t → ⊥
dlNoτ (sSil ())
dlNoτ (sTau refl ())

------------------------------------------------------------------------
-- everything below is for one link `l`
------------------------------------------------------------------------

module _ (l : Link) where

  -- this link's abstract labels, read as events
  ⌞_⌟ : Lab l → Event
  ⌞_⌟ = ⌜_⌝ l

  -- an abstract step label, read as a concrete one
  cl : ALbl l → Label Rr
  cl τ′      = τ
  cl (ev′ ω) = ev (evl ⌞ ω ⌟)

  ------------------------------------------------------------------------
  -- §1  The table as data
  ------------------------------------------------------------------------

  -- THE BLUEPRINT TABLE: the successor of a state on a message (`nothing`: no such row)
  row : TSt l → MessageLeiosNotifyP → Maybe (TSt l ⊎ Rr)
  row tIdle MsgLNPRequestNext           = just (inj₁ tBusy)
  row tIdle MsgLNPQuit                  = just (inj₁ tQuit)
  row tBusy (MsgLNPBlockAnnouncement _) = just (inj₁ tIdle)
  row tBusy (MsgLNPBlockOffer _ _)      = just (inj₁ tIdle)
  row tBusy (MsgLNPBlockTxsOffer _)     = just (inj₁ tIdle)
  row tBusy (MsgLNPVotes _)             = just (inj₁ tIdle)
  row tBusy MsgLNPCanceled              = just (inj₁ tIdle)
  row tQuit MsgLNPDone                  = just (inj₂ tt)
  row _     _                           = nothing

  -- the table with the row StBusy --MsgCanceled--> StIdle deleted (the bad client's)
  rowNoCan : TSt l → MessageLeiosNotifyP → Maybe (TSt l ⊎ Rr)
  rowNoCan tBusy MsgLNPCanceled = nothing
  rowNoCan s     m              = row s m

  -- the StIdle rows
  data IdleM : MessageLeiosNotifyP → TSt l ⊎ Rr → Set where
    imN : IdleM MsgLNPRequestNext (inj₁ tBusy)
    imQ : IdleM MsgLNPQuit (inj₁ tQuit)

  -- reading a StIdle row
  idleM : ∀ {m r} → row tIdle m ≡ just r → IdleM m r
  idleM {MsgLNPRequestNext} refl = imN
  idleM {MsgLNPQuit} refl = imQ
  idleM {MsgLNPBlockAnnouncement _} ()
  idleM {MsgLNPBlockOffer _ _} ()
  idleM {MsgLNPBlockTxsOffer _} ()
  idleM {MsgLNPVotes _} ()
  idleM {MsgLNPDone} ()
  idleM {MsgLNPCanceled} ()

  -- the StBusy rows' messages (all lead to StIdle)
  data BusyM : MessageLeiosNotifyP → Set where
    bmA : ∀ h    → BusyM (MsgLNPBlockAnnouncement h)
    bmO : ∀ q sz → BusyM (MsgLNPBlockOffer q sz)
    bmT : ∀ q    → BusyM (MsgLNPBlockTxsOffer q)
    bmV : ∀ vs   → BusyM (MsgLNPVotes vs)
    bmC :          BusyM MsgLNPCanceled

  -- reading a StBusy row
  busyM : ∀ {m r} → row tBusy m ≡ just r → BusyM m × r ≡ inj₁ tIdle
  busyM {MsgLNPBlockAnnouncement h} refl = bmA h , refl
  busyM {MsgLNPBlockOffer q sz} refl = bmO q sz , refl
  busyM {MsgLNPBlockTxsOffer q} refl = bmT q , refl
  busyM {MsgLNPVotes vs} refl = bmV vs , refl
  busyM {MsgLNPCanceled} refl = bmC , refl
  busyM {MsgLNPRequestNext} ()
  busyM {MsgLNPDone} ()
  busyM {MsgLNPQuit} ()

  -- reading the StQuit row
  quitM : ∀ {m r} → row tQuit m ≡ just r → m ≡ MsgLNPDone × r ≡ inj₂ tt
  quitM {MsgLNPDone} refl = refl , refl
  quitM {MsgLNPRequestNext} ()
  quitM {MsgLNPQuit} ()
  quitM {MsgLNPBlockAnnouncement _} ()
  quitM {MsgLNPBlockOffer _ _} ()
  quitM {MsgLNPBlockTxsOffer _} ()
  quitM {MsgLNPVotes _} ()
  quitM {MsgLNPCanceled} ()

  -- the wire channel a state's messages travel on, named at the client end `(l , lo)`
  chan : TSt l → LNPEv Payload
  chan tIdle = sendLNP l lo
  chan tBusy = receiveLNP l lo
  chan tQuit = receiveLNP l lo

  -- the abstract label of a message in a state
  lab : TSt l → Payload → Lab l
  lab tIdle x = wS lo x
  lab tBusy x = wR lo x
  lab tQuit x = wR lo x

  -- … its event is the message on the state's channel
  labOK : ∀ st x → ⌞ lab st x ⌟ ≡ evLabel Payload (chan st) x
  labOK tIdle _ = refl
  labOK tBusy _ = refl
  labOK tQuit _ = refl

  -- … and it is a wire label
  labW : ∀ st x → InE l (wireES l) (lab st x)
  labW tIdle _ = U.tt
  labW tBusy _ = U.tt
  labW tQuit _ = U.tt

  -- the alphabet of a table process: the wire cell at the client end
  data TAl : Lab l → Set where
    taS : ∀ x → TAl (wS lo x)
    taR : ∀ x → TAl (wR lo x)

  -- a message label is in it
  labAl : ∀ st x → TAl (lab st x)
  labAl tIdle _ = taS _
  labAl tBusy _ = taR _
  labAl tQuit _ = taR _

  -- a table process's abstract states: at a state's menu (flag: a pending loop-back τ),
  -- committed to a message after an internal choice, ended
  data TS : Set where
    tM : TSt l → Bool → TS
    tC : TSt l → Payload → TSt l ⊎ Rr → TS
    tE : TS

  -- the abstract state after a row's message
  nxt : TSt l ⊎ Rr → TS
  nxt (inj₁ s) = tM s true
  nxt (inj₂ _) = tE

  -- a table process has ended
  TFin : TS → Set
  TFin tE = U.⊤
  TFin _  = ⊥

  -- the τ-measure of a table process
  tμ : TS → ℕ
  tμ (tM _ false) = 1
  tμ (tM _ true)  = 2
  tμ _            = 0

  ------------------------------------------------------------------------
  -- §2  The table as a process, generic in who holds agency, and its abstraction
  ------------------------------------------------------------------------

  -- `rw`: the rows; `int st`: whether state `st`'s choice is INTERNAL (the process holds
  -- agency there and sends) or EXTERNAL (it accepts); `nz`: the envelope of a sent message
  module Tbl (rw : TSt l → MessageLeiosNotifyP → Maybe (TSt l ⊎ Rr))
             (int : TSt l → Bool) (nz : TSt l → Payload → Payload) where

    -- the successor of a state on a payload (only LeiosNotify messages are rows)
    rowP : TSt l → Payload → Maybe (TSt l ⊎ Rr)
    rowP st (_ , _ , _ , leiosNotifyP m) = rw st m
    rowP _  _                            = nothing

    -- a row payload is a LeiosNotify message
    rowP-inv : ∀ {st x r} → rowP st x ≡ just r
             → Σ[ tm ∈ Time ] Σ[ md ∈ Mode ] Σ[ ln ∈ Length ] Σ[ m ∈ MessageLeiosNotifyP ]
                 (x ≡ (tm , md , ln , leiosNotifyP m) × rw st m ≡ just r)
    rowP-inv {x = tm , md , ln , leiosNotifyP m} eq = tm , md , ln , m , refl , eq
    rowP-inv {x = _ , _ , _ , keepAlive _} ()
    rowP-inv {x = _ , _ , _ , blockFetch _} ()
    rowP-inv {x = _ , _ , _ , chainSync _} ()
    rowP-inv {x = _ , _ , _ , txSubmission _} ()
    rowP-inv {x = _ , _ , _ , leiosNotify _} ()
    rowP-inv {x = _ , _ , _ , leiosFetch _} ()
    rowP-inv {x = _ , _ , _ , leiosFetchP _} ()

    -- EXTERNAL state: accept every payload of a row on the state's channel
    accV : TSt l → (at : AnyTypes LNPEv) → ContinueType at (Maybe (PTree LNPEv (ExtI LNPEv) (TSt l ⊎ Rr)))
    accV st (A , e) a with LNPEv-≟ (A , e) (Payload , chan st)
    ... | yes refl = mapM Ret (rowP st a)
    ... | no _     = nothing

    -- INTERNAL state: one τ-branch per payload of a row (indexed by the channel's `base`
    -- index and the payload), committing to send it
    τB : TSt l → (i : AnyTypes (ExtI LNPEv)) → ContinueType i (Maybe (PTree LNPEv (ExtI LNPEv) (TSt l ⊎ Rr)))
    τB st (B , base e) a with LNPEv-≟ (B , e) (Payload , chan st)
    ... | yes refl = mapM (λ r → Output (chan st) (nz st a) (Ret r)) (rowP st a)
    ... | no _     = nothing
    τB st (_ , pair _ _) _ = nothing
    τB st (_ , fin)      _ = nothing

    -- a state's node: internal choice (pure τ-menu) or external choice (pure menu)
    node : Bool → TSt l → PTree LNPEv (ExtI LNPEv) (TSt l ⊎ Rr)
    node true  st = ptree (react ∅v (τB st))
    node false st = pchoice (accV st)

    -- one table step
    tstep : TSt l → PTree LNPEv (ExtI LNPEv) (TSt l ⊎ Rr)
    tstep st = node (int st) st

    -- THE TABLE PROCESS: loop the step from StIdle
    proc : Tree
    proc = iter tstep tIdle

    -- an accepted offer is a row's payload on the state's channel
    accInv : ∀ st {at a t} → accV st at a ≡ just t
           → Σ[ x ∈ Payload ] Σ[ r ∈ TSt l ⊎ Rr ]
               (evLabel (proj₁ at) (proj₂ at) a ≡ evLabel Payload (chan st) x × rowP st x ≡ just r × t ≡ Ret r)
    accInv st {A , e} {a} eq with LNPEv-≟ (A , e) (Payload , chan st)
    ... | no _ = case eq of λ ()
    ... | yes refl with rowP st a in rq
    ...   | just r  = a , r , refl , rq , sym (just-injective eq)
    ...   | nothing = case eq of λ ()

    -- a τ-branch is a row's payload, committed to
    τBInv : ∀ st {i a t} → τB st i a ≡ just t
          → Σ[ x ∈ Payload ] Σ[ r ∈ TSt l ⊎ Rr ] (rowP st x ≡ just r × t ≡ Output (chan st) (nz st x) (Ret r))
    τBInv st {B , base e} {a} eq with LNPEv-≟ (B , e) (Payload , chan st)
    ... | no _ = case eq of λ ()
    ... | yes refl with rowP st a in rq
    ...   | just r  = a , r , rq , sym (just-injective eq)
    ...   | nothing = case eq of λ ()
    τBInv st {_ , pair _ _} ()
    τBInv st {_ , fin}      ()

    -- the menu accepts every row payload
    accEq : ∀ st x r → rowP st x ≡ just r → accV st (Payload , chan st) x ≡ just (Ret r)
    accEq st x r rx with LNPEv-≟ (Payload , chan st) (Payload , chan st)
    ... | no ¬p    = ⊥-elim (¬p refl)
    ... | yes refl rewrite rx = refl

    -- the τ-menu has a branch for every row payload
    τBEq : ∀ st x r → rowP st x ≡ just r
         → τB st (Payload , base (chan st)) x ≡ just (Output (chan st) (nz st x) (Ret r))
    τBEq st x r rx with LNPEv-≟ (Payload , chan st) (Payload , chan st)
    ... | no ¬p    = ⊥-elim (¬p refl)
    ... | yes refl rewrite rx = refl

    -- a node's τ is an internal choice of a row payload
    nodeτ : ∀ b st {t′} → node b st ─[ τ ]─► t′
          → T b × Σ[ x ∈ Payload ] Σ[ r ∈ TSt l ⊎ Rr ] (rowP st x ≡ just r × t′ ≡ Output (chan st) (nz st x) (Ret r))
    nodeτ true  st (sSil ())
    nodeτ true  st (sTau {i = i} {a = a} refl br) = U.tt , τBInv st {i} {a} br
    nodeτ false st s = ⊥-elim (pchNoτ s)


    -- a node's visible step is an accepted row payload
    nodeE : ∀ b st {e t′} → node b st ─[ ev (evl e) ]─► t′
          → T (not b) × Σ[ x ∈ Payload ] Σ[ r ∈ TSt l ⊎ Rr ]
              (e ≡ evLabel Payload (chan st) x × rowP st x ≡ just r × t′ ≡ Ret r)
    nodeE true  st (sVis refl ())
    nodeE false st (sVis refl br) = U.tt , accInv st br

    -- a node never returns
    nodeNoRet : ∀ b st {r} → PTree.force (node b st) ≡ ret r → ⊥
    nodeNoRet true  _ ()
    nodeNoRet false _ ()

    -- an internal node chooses every row payload
    nodeτI : ∀ b st → T b → ∀ x r → rowP st x ≡ just r → node b st ─[ τ ]─► Output (chan st) (nz st x) (Ret r)
    nodeτI true  st _ x r rx = sTau {i = Payload , base (chan st)} {a = x} refl (τBEq st x r rx)
    nodeτI false _  ()

    -- an external node accepts every row payload
    nodeEI : ∀ b st → T (not b) → ∀ x r → rowP st x ≡ just r
           → node b st ─[ ev (evl (evLabel Payload (chan st) x)) ]─► Ret r
    nodeEI false st _ x r rx = sVis {at = Payload , chan st} {a = x} refl (accEq st x r rx)
    nodeEI true  _  ()

    -- where a table-process tree is
    data TPos : TS → Tree → Set₁ where
      tpM  : ∀ st → TPos (tM st false) (iter tstep st)
      tpM′ : ∀ st → TPos (tM st true) (iter-bind (Ret (inj₁ st)) tstep)
      tpC  : ∀ st x r → TPos (tC st x r) (iter-bind (Output (chan st) (nz st x) (Ret r)) tstep)
      tpE  : TPos tE (iter-bind (Ret (inj₂ tt)) tstep)

    -- the table process's abstract steps: the loop-back, an internal choice, an accepted
    -- message, the committed message sent
    data TStp : TS → ALbl l → TS → Set where
      tτ   : ∀ st → TStp (tM st true) τ′ (tM st false)
      tCh  : ∀ st tm md ln m r → T (int st) → rw st m ≡ just r
           → TStp (tM st false) τ′ (tC st (tm , md , ln , leiosNotifyP m) r)
      tAcc : ∀ st tm md ln m r → T (not (int st)) → rw st m ≡ just r
           → TStp (tM st false) (ev′ (lab st (tm , md , ln , leiosNotifyP m))) (nxt r)
      tEm  : ∀ st x r → TStp (tC st x r) (ev′ (lab st (nz st x))) (nxt r)

    -- the position after a row's message
    tpN : ∀ r → TPos (nxt r) (iter-bind (Ret r) tstep)
    tpN (inj₁ s) = tpM′ s
    tpN (inj₂ _) = tpE

    -- every τ of a positioned tree is an abstract one
    tElimτ : ∀ {σ t t′} → TPos σ t → t ─[ τ ]─► t′ → Σ[ σ′ ∈ TS ] (TStp σ τ′ σ′ × TPos σ′ t′)
    tElimτ (tpM st) s with iter-τ-elim (tstep st) tstep s
    ... | itτ _ s′ refl with nodeτ (int st) st s′
    ...   | it , x , r , rx , refl with rowP-inv {st} {x} rx
    ...     | tm , md , ln , m , refl , rm = _ , tCh st tm md ln m r it rm , tpC st _ r
    tElimτ (tpM st) s | itBack _ eq _ = ⊥-elim (nodeNoRet (int st) st eq)
    tElimτ (tpM′ st) (sSil refl) = _ , tτ st , tpM st
    tElimτ (tpM′ st) (sTau () _)
    tElimτ (tpC st x r) s = ⊥-elim (IterNoτ.τ✗ outNoτ (λ ()) s)
    tElimτ tpE (sSil ())
    tElimτ tpE (sTau () _)

    -- every visible step of a positioned tree is an abstract one
    tElimE : ∀ {σ t t′ e} → TPos σ t → t ─[ ev (evl e) ]─► t′
           → Σ[ ω ∈ Lab l ] Σ[ σ′ ∈ TS ] (e ≡ ⌞ ω ⌟ × TStp σ (ev′ ω) σ′ × TPos σ′ t′)
    tElimE (tpM st) s with iter-ev-elim (tstep st) tstep s
    ... | _ , s′ , refl with nodeE (int st) st s′
    ...   | nit , x , r , refl , rx , refl with rowP-inv {st} {x} rx
    ...     | tm , md , ln , m , refl , rm = _ , _ , sym (labOK st _) , tAcc st tm md ln m r nit rm , tpN r
    tElimE (tpM′ _) (sVis () _)
    tElimE (tpC st x r) s with iter-ev-elim (Output (chan st) (nz st x) (Ret r)) tstep s
    ... | _ , s′ , refl with outI s′
    ...   | refl , refl = _ , _ , sym (labOK st (nz st x)) , tEm st x r , tpN r
    tElimE tpE (sVis () _)

    -- a positioned tree returns only at the end
    tElimR : ∀ {σ t r} → TPos σ t → PTree.force t ≡ ret r → TFin σ
    tElimR (tpM st) eq = ⊥-elim (iterNoRet {k = tstep} {T₀ = tstep st} (nodeNoRet (int st) st) eq)
    tElimR (tpM′ _) ()
    tElimR (tpC _ _ _) ()
    tElimR tpE _ = U.tt

    -- the steps stay on the wire cell
    tAlpha : ∀ {σ ω σ′} → TStp σ (ev′ ω) σ′ → TAl ω
    tAlpha (tAcc st _ _ _ _ _ _ _) = labAl st _
    tAlpha (tEm st _ _)            = labAl st _

    -- … so every visible step is a wire step
    tWire : ∀ {σ ω σ′} → TStp σ (ev′ ω) σ′ → InE l (wireES l) ω
    tWire (tAcc st _ _ _ _ _ _ _) = labW st _
    tWire (tEm st _ _)            = labW st _

    -- the τ-measure decreases
    tμτ : ∀ {σ σ′} → TStp σ τ′ σ′ → tμ σ′ < tμ σ
    tμτ (tτ _)                  = s≤s (s≤s z≤n)
    tμτ (tCh _ _ _ _ _ _ _ _)   = s≤s z≤n

    -- THE ABSTRACTION of the table process
    TA : Abs l TS
    TA = record { Pos = TPos ; Stp = TStp ; Fin = TFin ; Alpha = TAl ; alpha = tAlpha
                ; μ = tμ ; μτ = tμτ ; elimτ = tElimτ ; elimE = tElimE ; elimR = tElimR }

    -- every abstract τ is a concrete one
    tIntroτ : ∀ {σ σ′ t} → TPos σ t → TStp σ τ′ σ′ → Σ[ t′ ∈ Tree ] (t ─[ τ ]─► t′ × TPos σ′ t′)
    tIntroτ (tpM′ st) (tτ _) = _ , sSil refl , tpM st
    tIntroτ (tpM st) (tCh _ tm md ln m r it rm) =
      _ , iterτ (nodeτI (int st) st it (tm , md , ln , leiosNotifyP m) r rm) , tpC st _ r

    -- every abstract visible step is a concrete one
    tIntroE : ∀ {σ σ′ t ω} → TPos σ t → TStp σ (ev′ ω) σ′ → Σ[ t′ ∈ Tree ] (t ─[ ev (evl ⌞ ω ⌟) ]─► t′ × TPos σ′ t′)
    tIntroE (tpM st) (tAcc _ tm md ln m r nit rm) =
      _ , subst (λ e → iter tstep st ─[ ev (evl e) ]─► iter-bind (Ret r) tstep)
                (sym (labOK st (tm , md , ln , leiosNotifyP m)))
                (iterE (nodeEI (int st) st nit (tm , md , ln , leiosNotifyP m) r rm))
        , tpN r
    tIntroE (tpC st x r) (tEm _ _ _) =
      _ , subst (λ e → iter-bind (Output (chan st) (nz st x) (Ret r)) tstep ─[ ev (evl e) ]─► iter-bind (Ret r) tstep)
                (sym (labOK st (nz st x)))
                (iterE (outS (chan st) (nz st x) (Ret r)))
        , tpN r

    -- the ended table process has returned
    tIntroR : ∀ {σ t} → TPos σ t → TFin σ → PTree.force t ≡ ret tt
    tIntroR tpE _ = refl
    tIntroR (tpM _) ()
    tIntroR (tpM′ _) ()
    tIntroR (tpC _ _ _) ()

    -- the intro facts
    TI : AbsI l TA
    TI = record { introτ = tIntroτ ; introE = tIntroE ; introR = tIntroR }

  ------------------------------------------------------------------------
  -- §3  Generic tools: weak steps, hiding, invariants
  ------------------------------------------------------------------------

  -- abstract weak steps of an abstraction
  module Wk {S : Set} (A : Abs l S) where
    open Abs A using (Stp)

    -- a run of abstract τ's
    data τ* : S → S → Set where
      ε   : ∀ {σ} → τ* σ σ
      _◅_ : ∀ {σ σ₁ σ₂} → Stp σ τ′ σ₁ → τ* σ₁ σ₂ → τ* σ σ₂

    -- concatenation
    _◅◅_ : ∀ {σ σ₁ σ₂} → τ* σ σ₁ → τ* σ₁ σ₂ → τ* σ σ₂
    ε        ◅◅ bs = bs
    (a ◅ as) ◅◅ bs = a ◅ (as ◅◅ bs)

    -- a weak step: τ*, or τ* · visible · τ*
    W : S → ALbl l → S → Set
    W σ τ′      σ′ = τ* σ σ′
    W σ (ev′ ω) σ′ = Σ[ σ₁ ∈ S ] Σ[ σ₂ ∈ S ] (τ* σ σ₁ × Stp σ₁ (ev′ ω) σ₂ × τ* σ₂ σ′)

  -- abstract weak steps are concrete weak steps
  module WkI {S : Set} {A : Abs l S} (I : AbsI l A) where
    open Abs A using (Pos)
    open AbsI I
    open Wk A

    -- a τ-run
    τ*I : ∀ {σ σ′ t} → τ* σ σ′ → Pos σ t → Σ[ t′ ∈ Tree ] (t ─[τ*]─► t′ × Pos σ′ t′)
    τ*I ε p = _ , τ*-refl , p
    τ*I (a ◅ as) p with introτ p a
    ... | _ , s , p₁ with τ*I as p₁
    ...   | t′ , r , p′ = t′ , τ*-step s r , p′

    -- a weak step
    WI : ∀ ℓ {σ σ′ t} → W σ ℓ σ′ → Pos σ t → Σ[ t′ ∈ Tree ] (t ═[ cl ℓ ]═► t′ × Pos σ′ t′)
    WI τ′ w p with τ*I w p
    ... | t′ , r , p′ = t′ , wτ r , p′
    WI (ev′ ω) (_ , _ , w₁ , a , w₂) p with τ*I w₁ p
    ... | _ , r₁ , p₁ with introE p₁ a
    ...   | _ , s , p₂ with τ*I w₂ p₂
    ...     | t′ , r₂ , p′ = t′ , wev r₁ s r₂ , p′

  -- HIDING an abstraction: hidden labels become τ's; `ν` must decrease on τ's and on hidden
  -- steps (so the hidden process does not diverge)
  module HideA {S : Set} (A : Abs l S) (H : EventSet) (ν : S → ℕ)
               (ντ : ∀ {σ σ′} → Abs.Stp A σ τ′ σ′ → ν σ′ < ν σ)
               (νh : ∀ {σ ω σ′} → InE l H ω → Abs.Stp A σ (ev′ ω) σ′ → ν σ′ < ν σ) where
    open Abs A

    -- the hidden steps: an own τ, a hidden visible step, a kept visible step
    data HStp : S → ALbl l → S → Set where
      hτ : ∀ {σ σ′}   → Stp σ τ′ σ′ → HStp σ τ′ σ′
      hh : ∀ {σ σ′} ω → InE l H ω → Stp σ (ev′ ω) σ′ → HStp σ τ′ σ′
      hk : ∀ {σ σ′} ω → ¬ InE l H ω → Stp σ (ev′ ω) σ′ → HStp σ (ev′ ω) σ′

    -- a hidden position: the hiding of a positioned tree
    HPos : S → Tree → Set₁
    HPos σ t = Σ[ t₀ ∈ Tree ] (t ≡ t₀ ∖ H × Pos σ t₀)

    -- the measure decreases on every hidden τ
    hμτ : ∀ {σ σ′} → HStp σ τ′ σ′ → ν σ′ < ν σ
    hμτ (hτ a)     = ντ a
    hμτ (hh _ m a) = νh m a

    -- kept steps stay in the alphabet
    hAlpha : ∀ {σ ω σ′} → HStp σ (ev′ ω) σ′ → Alpha ω
    hAlpha (hk _ _ a) = alpha a

    -- every τ of a hidden tree is an own τ or a hidden event
    hElimτ : ∀ {σ t t′} → HPos σ t → t ─[ τ ]─► t′ → Σ[ σ′ ∈ S ] (HStp σ τ′ σ′ × HPos σ′ t′)
    hElimτ (t₀ , refl , p) s with Hide-τ-elim H t₀ s
    ... | hτP P′ s′ refl with elimτ p s′
    ...   | σ′ , a , p′ = σ′ , hτ a , (P′ , refl , p′)
    hElimτ (t₀ , refl , p) s | hτH P′ m s′ refl with elimE p s′
    ...   | ω , σ′ , eq , a , p′ = σ′ , hh ω (subst (InEv l H) eq m) a , (P′ , refl , p′)

    -- every visible step of a hidden tree is a kept one
    hElimE : ∀ {σ t t′ e} → HPos σ t → t ─[ ev (evl e) ]─► t′
           → Σ[ ω ∈ Lab l ] Σ[ σ′ ∈ S ] (e ≡ ⌞ ω ⌟ × HStp σ (ev′ ω) σ′ × HPos σ′ t′)
    hElimE (t₀ , refl , p) s with Hide-ev-elim H t₀ s
    ... | heV P′ ¬m s′ with elimE p s′
    ...   | ω , σ′ , eq , a , p′ = ω , σ′ , eq , hk ω (λ m → ¬m (subst (InEv l H) (sym eq) m)) a , (P′ , refl , p′)

    -- a hidden tree returns only where its source does
    hElimR : ∀ {σ t r} → HPos σ t → PTree.force t ≡ ret r → Fin σ
    hElimR (t₀ , refl , p) eq = elimR p (fHide-ret-inv H t₀ eq)

    -- THE HIDDEN ABSTRACTION
    HAbs : Abs l S
    HAbs = record { Pos = HPos ; Stp = HStp ; Fin = Fin ; Alpha = Alpha ; alpha = hAlpha
                  ; μ = ν ; μτ = hμτ ; elimτ = hElimτ ; elimE = hElimE ; elimR = hElimR }

    -- every hidden abstract τ is a concrete one
    hIntroτ : AbsI l A → ∀ {σ σ′ t} → HPos σ t → HStp σ τ′ σ′ → Σ[ t′ ∈ Tree ] (t ─[ τ ]─► t′ × HPos σ′ t′)
    hIntroτ I (t₀ , refl , p) (hτ a) with AbsI.introτ I p a
    ... | t₁ , s , p′ = _ , Hide-τ H t₀ s , (t₁ , refl , p′)
    hIntroτ I (t₀ , refl , p) (hh ω m a) with AbsI.introE I p a
    ... | t₁ , s , p′ = _ , Hide-hidden H t₀ m s , (t₁ , refl , p′)

    -- every kept abstract step is a concrete one
    hIntroE : AbsI l A → ∀ {σ σ′ t ω} → HPos σ t → HStp σ (ev′ ω) σ′
            → Σ[ t′ ∈ Tree ] (t ─[ ev (evl ⌞ ω ⌟) ]─► t′ × HPos σ′ t′)
    hIntroE I (t₀ , refl , p) (hk ω ¬m a) with AbsI.introE I p a
    ... | t₁ , s , p′ = _ , Hide-keep H t₀ ¬m s , (t₁ , refl , p′)

    -- the hidden tree returns where its source does
    hIntroR : AbsI l A → ∀ {σ t} → HPos σ t → Fin σ → PTree.force t ≡ ret tt
    hIntroR I (t₀ , refl , p) f = fHide-ret H t₀ (AbsI.introR I p f)

    -- the hidden intro facts
    HI : AbsI l A → AbsI l HAbs
    HI I = record { introτ = hIntroτ I ; introE = hIntroE I ; introR = hIntroR I }

  -- an inductive invariant with progress gives deadlock freedom
  module InvDL {S : Set} (A : Abs l S) (I : AbsI l A) (Inv : S → Set)
               (pres : ∀ {σ ℓ σ′} → Inv σ → Abs.Stp A σ ℓ σ′ → Inv σ′)
               (prog : ∀ {σ} → Inv σ → Abs.Fin A σ ⊎ Σ[ ℓ ∈ ALbl l ] Σ[ σ′ ∈ S ] Abs.Stp A σ ℓ σ′) where
    open Abs A using (Pos)
    open Gen l A using (ARun; r0; rτ; rE; runE)

    -- the invariant holds along every abstract run
    invRun : ∀ {σ s σ′} → ARun σ s σ′ → Inv σ → Inv σ′
    invRun r0        i = i
    invRun (rτ a ar) i = invRun ar (pres i a)
    invRun (rE a ar) i = invRun ar (pres i a)

    -- a positioned start satisfying the invariant is deadlock-free
    dlFree : ∀ {σ t} → Pos σ t → Inv σ → DeadlockFree t
    dlFree p i r stk with runE p r
    ... | _ , ar , p′ = GenI.notStuck l I p′ (prog (invRun ar i)) stk

  ------------------------------------------------------------------------
  -- §4  (R) Receptiveness
  ------------------------------------------------------------------------

  -- the server holds agency in StBusy and StQuit
  srvAg : TSt l → Bool
  srvAg tIdle = false
  srvAg _     = true

  -- the client holds agency in StIdle
  cliAg : TSt l → Bool
  cliAg tIdle = true
  cliAg _     = false

  -- an envelope kept as chosen
  nzI : TSt l → Payload → Payload
  nzI _ x = x

  -- the most general server, the most general client, and the bad client
  module SE = Tbl row      srvAg nzI
  -- (the most general client)
  module CE = Tbl row      cliAg nzI
  -- (the most general client WITHOUT the MsgCanceled row)
  module BD = Tbl rowNoCan cliAg nzI

  -- THE MOST GENERAL SERVER: accepts RequestNext / Quit (any payload) in StIdle; in StBusy
  -- internally chooses any of the four replies or MsgCanceled with any payload; in StQuit
  -- internally chooses a MsgDone payload, then √
  ServerEnv : Tree
  ServerEnv = SE.proc

  -- THE MOST GENERAL CLIENT: in StIdle internally chooses RequestNext or Quit (any payload);
  -- in StBusy accepts the four replies and MsgCanceled (any payload); in StQuit accepts
  -- MsgDone, then √
  ClientEnv : Tree
  ClientEnv = CE.proc

  -- THE BAD CLIENT: `ClientEnv` except that in StBusy it does not accept MsgCanceled
  badClient : Tree
  badClient = BD.proc

  -- a table process shares nothing off the wire
  disjT : ∀ {X : Lab l → Set} {ω} → X ω → TAl ω → ¬ InE l (wireES l) ω → ⊥
  disjT _ (taS _) ¬w = ¬w U.tt
  disjT _ (taR _) ¬w = ¬w U.tt

  -- the real client against the most general server, on the wire
  module RCm = Prod l (CA l) SE.TA (wireES l) (λ {ω} → disjT {CAl l} {ω})
  -- the renamed real server against the most general client, on the wire
  module RSm = Prod l (SA l) CE.TA (wireES l) (λ {ω} → disjT {SAl l} {ω})
  -- the bad client against the most general server, on the wire
  module RBm = Prod l BD.TA SE.TA (wireES l) (λ {ω} → disjT {TAl} {ω})

  -- the real client composed with the most general server
  clientEnvSys : Tree
  clientEnvSys = Par⊤ (wireES l) (LNPclientStClient l lo) ServerEnv

  -- the renamed real server composed with the most general client
  serverEnvSys : Tree
  serverEnvSys = Par⊤ (wireES l) (srv l) ClientEnv

  -- the bad client composed with the most general server
  badEnvSys : Tree
  badEnvSys = Par⊤ (wireES l) badClient ServerEnv

  ---------------------------------------------------------------- client side

  -- the reachable joint phases of the real client and `ServerEnv`
  data JC : (CS l × Bool) × TS → Set where
    rc1 : ∀ {fc ft} → JC ((cI , fc) , tM tIdle ft)
    rc2 : ∀ {ft}    → JC ((cR , false) , tM tIdle ft)
    rc3 : ∀ {ft}    → JC ((cS , false) , tM tIdle ft)
    rc4 : ∀ {fc ft} → JC ((cB , fc) , tM tBusy ft)
    rc5 : ∀ {fc tm md ln m r} → row tBusy m ≡ just r
        → JC ((cB , fc) , tC tBusy (tm , md , ln , leiosNotifyP m) r)
    rc6 : ∀ {dv ft} → JC ((cD dv , false) , tM tIdle ft)
    rc7 : ∀ {fc ft} → JC ((cQ , fc) , tM tQuit ft)
    rc8 : ∀ {fc tm md ln m r} → row tQuit m ≡ just r
        → JC ((cQ , fc) , tC tQuit (tm , md , ln , leiosNotifyP m) r)
    rc9 : JC ((cE , false) , tE)

  -- the phases are closed under every joint step
  presC : ∀ {σ ℓ σ′} → JC σ → RCm.PStp σ ℓ σ′ → JC σ′
  presC rc1      (RCm.pτL cτI) = rc1
  presC rc4      (RCm.pτL cτB) = rc4
  presC (rc5 rm) (RCm.pτL cτB) = rc5 rm
  presC rc7      (RCm.pτL cτQ) = rc7
  presC (rc8 rm) (RCm.pτL cτQ) = rc8 rm
  presC rc1 (RCm.pτR (SE.tτ _)) = rc1
  presC rc2 (RCm.pτR (SE.tτ _)) = rc2
  presC rc3 (RCm.pτR (SE.tτ _)) = rc3
  presC rc4 (RCm.pτR (SE.tτ _)) = rc4
  presC rc6 (RCm.pτR (SE.tτ _)) = rc6
  presC rc7 (RCm.pτR (SE.tτ _)) = rc7
  presC rc1 (RCm.pτR (SE.tCh _ _ _ _ _ _ () _))
  presC rc2 (RCm.pτR (SE.tCh _ _ _ _ _ _ () _))
  presC rc3 (RCm.pτR (SE.tCh _ _ _ _ _ _ () _))
  presC rc6 (RCm.pτR (SE.tCh _ _ _ _ _ _ () _))
  presC rc4 (RCm.pτR (SE.tCh _ _ _ _ _ _ _ rm)) = rc5 rm
  presC rc7 (RCm.pτR (SE.tCh _ _ _ _ _ _ _ rm)) = rc8 rm
  presC rc1 (RCm.psL _ (cRN _))   = rc2
  presC rc1 (RCm.psL _ (cQi _))   = rc3
  presC rc6 (RCm.psL _ (cDA _))   = rc1
  presC rc6 (RCm.psL _ (cDO _ _)) = rc1
  presC rc6 (RCm.psL _ (cDT _))   = rc1
  presC rc6 (RCm.psL _ (cDV _))   = rc1
  presC _ (RCm.psL ¬w cSR)       = ⊥-elim (¬w U.tt)
  presC _ (RCm.psL ¬w cSQ)       = ⊥-elim (¬w U.tt)
  presC _ (RCm.psL ¬w (cRA _))   = ⊥-elim (¬w U.tt)
  presC _ (RCm.psL ¬w (cRO _ _)) = ⊥-elim (¬w U.tt)
  presC _ (RCm.psL ¬w (cRT _))   = ⊥-elim (¬w U.tt)
  presC _ (RCm.psL ¬w (cRV _))   = ⊥-elim (¬w U.tt)
  presC _ (RCm.psL ¬w cRC)       = ⊥-elim (¬w U.tt)
  presC _ (RCm.psL ¬w cDn)       = ⊥-elim (¬w U.tt)
  presC _ (RCm.psR ¬w b) = ⊥-elim (¬w (SE.tWire b))
  presC _ (RCm.psy w (cRN _) _)   = ⊥-elim w
  presC _ (RCm.psy w (cQi _) _)   = ⊥-elim w
  presC _ (RCm.psy w (cDA _) _)   = ⊥-elim w
  presC _ (RCm.psy w (cDO _ _) _) = ⊥-elim w
  presC _ (RCm.psy w (cDT _) _)   = ⊥-elim w
  presC _ (RCm.psy w (cDV _) _)   = ⊥-elim w
  presC rc4 (RCm.psy _ (cRA _)   (SE.tAcc _ _ _ _ _ _ () _))
  presC rc4 (RCm.psy _ (cRO _ _) (SE.tAcc _ _ _ _ _ _ () _))
  presC rc4 (RCm.psy _ (cRT _)   (SE.tAcc _ _ _ _ _ _ () _))
  presC rc4 (RCm.psy _ (cRV _)   (SE.tAcc _ _ _ _ _ _ () _))
  presC rc4 (RCm.psy _ cRC       (SE.tAcc _ _ _ _ _ _ () _))
  presC rc7 (RCm.psy _ cDn       (SE.tAcc _ _ _ _ _ _ () _))
  presC rc2 (RCm.psy _ cSR (SE.tAcc _ _ _ _ _ _ _ rm)) with rm
  ... | refl = rc4
  presC rc3 (RCm.psy _ cSQ (SE.tAcc _ _ _ _ _ _ _ rm)) with rm
  ... | refl = rc7
  presC (rc5 rm) (RCm.psy _ (cRA _) (SE.tEm _ _ _)) with rm
  ... | refl = rc6
  presC (rc5 rm) (RCm.psy _ (cRO _ _) (SE.tEm _ _ _)) with rm
  ... | refl = rc6
  presC (rc5 rm) (RCm.psy _ (cRT _) (SE.tEm _ _ _)) with rm
  ... | refl = rc6
  presC (rc5 rm) (RCm.psy _ (cRV _) (SE.tEm _ _ _)) with rm
  ... | refl = rc6
  presC (rc5 rm) (RCm.psy _ cRC (SE.tEm _ _ _)) with rm
  ... | refl = rc1
  presC (rc8 rm) (RCm.psy _ cDn (SE.tEm _ _ _)) with rm
  ... | refl = rc9

  -- PROGRESS: every phase has a joint step, or both have ended.  At `rc5` / `rc8` this is
  -- RECEPTIVENESS itself: whatever row payload `ServerEnv` committed to, the client takes it
  progCE : ∀ {σ} → JC σ → Abs.Fin RCm.ParA σ ⊎ Σ[ ℓ ∈ ALbl l ] Σ[ σ′ ∈ _ ] RCm.PStp σ ℓ σ′
  progCE (rc1 {true})  = inj₂ (_ , _ , RCm.pτL cτI)
  progCE (rc1 {false}) = inj₂ (_ , _ , RCm.psL (λ ()) (cRN U.tt))
  progCE (rc2 {true})  = inj₂ (_ , _ , RCm.pτR (SE.tτ tIdle))
  progCE (rc2 {false}) =
    inj₂ (_ , _ , RCm.psy U.tt cSR (SE.tAcc tIdle time₀ FromInitiator length₀ MsgLNPRequestNext (inj₁ tBusy) U.tt refl))
  progCE (rc3 {true})  = inj₂ (_ , _ , RCm.pτR (SE.tτ tIdle))
  progCE (rc3 {false}) =
    inj₂ (_ , _ , RCm.psy U.tt cSQ (SE.tAcc tIdle time₀ FromInitiator length₀ MsgLNPQuit (inj₁ tQuit) U.tt refl))
  progCE (rc4 {true})          = inj₂ (_ , _ , RCm.pτL cτB)
  progCE (rc4 {false} {true})  = inj₂ (_ , _ , RCm.pτR (SE.tτ tBusy))
  progCE (rc4 {false} {false}) =
    inj₂ (_ , _ , RCm.pτR (SE.tCh tBusy time₀ FromResponder length₀ MsgLNPCanceled (inj₁ tIdle) U.tt refl))
  progCE (rc5 {true} _)    = inj₂ (_ , _ , RCm.pτL cτB)
  progCE (rc5 {false} rm) with busyM rm
  ... | bmA h , _    = inj₂ (_ , _ , RCm.psy U.tt (cRA h) (SE.tEm tBusy _ _))
  ... | bmO q sz , _ = inj₂ (_ , _ , RCm.psy U.tt (cRO q sz) (SE.tEm tBusy _ _))
  ... | bmT q , _    = inj₂ (_ , _ , RCm.psy U.tt (cRT q) (SE.tEm tBusy _ _))
  ... | bmV vs , _   = inj₂ (_ , _ , RCm.psy U.tt (cRV vs) (SE.tEm tBusy _ _))
  ... | bmC , _      = inj₂ (_ , _ , RCm.psy U.tt cRC (SE.tEm tBusy _ _))
  progCE (rc6 {dAnn h})    = inj₂ (_ , _ , RCm.psL (λ ()) (cDA h))
  progCE (rc6 {dOff q sz}) = inj₂ (_ , _ , RCm.psL (λ ()) (cDO q sz))
  progCE (rc6 {dTxs q})    = inj₂ (_ , _ , RCm.psL (λ ()) (cDT q))
  progCE (rc6 {dVot vs})   = inj₂ (_ , _ , RCm.psL (λ ()) (cDV vs))
  progCE (rc7 {true})          = inj₂ (_ , _ , RCm.pτL cτQ)
  progCE (rc7 {false} {true})  = inj₂ (_ , _ , RCm.pτR (SE.tτ tQuit))
  progCE (rc7 {false} {false}) =
    inj₂ (_ , _ , RCm.pτR (SE.tCh tQuit time₀ FromResponder length₀ MsgLNPDone (inj₂ tt) U.tt refl))
  progCE (rc8 {true} _)    = inj₂ (_ , _ , RCm.pτL cτQ)
  progCE (rc8 {false} rm) with quitM rm
  ... | refl , _ = inj₂ (_ , _ , RCm.psy U.tt cDn (SE.tEm tQuit _ _))
  progCE rc9 = inj₁ (U.tt , U.tt)

  -- the invariant argument for the client side
  module DLC = InvDL RCm.ParA (RCm.ParI (CI l) SE.TI) JC presC progCE

  -- the client side starts in phase `rc1`
  cEnv₀ : Abs.Pos RCm.ParA ((cI , false) , tM tIdle false) clientEnvSys
  cEnv₀ = _ , _ , refl , cpI , SE.tpM tIdle

  -- (R) THE CLIENT IS RECEPTIVE: against the most general table-conforming server it never
  -- gets stuck before √ — in StBusy it accepts each of the four replies AND MsgCanceled,
  -- in StQuit MsgDone, with any payload
  client-receptive : DeadlockFree clientEnvSys
  client-receptive = DLC.dlFree cEnv₀ rc1

  -- (R) … and the composition never diverges
  client-receptive-divFree : DivergenceFree clientEnvSys
  client-receptive-divFree = Gen.divFree l RCm.ParA cEnv₀

  ---------------------------------------------------------------- server side

  -- the reachable joint phases of the renamed real server and `ClientEnv`
  data JS : (SS l × Bool) × TS → Set where
    rs1 : ∀ {fs ft} → JS ((sI , fs) , tM tIdle ft)
    rs2 : ∀ {fs tm md ln m r} → row tIdle m ≡ just r
        → JS ((sI , fs) , tC tIdle (tm , md , ln , leiosNotifyP m) r)
    rs3 : ∀ {fs ft} → JS ((sB , fs) , tM tBusy ft)
    rs4 : ∀ {r ft}  → JS ((sN r , false) , tM tBusy ft)
    rs5 : ∀ {fs ft} → JS ((sQ , fs) , tM tQuit ft)
    rs6 : ∀ {ft}    → JS ((sD , false) , tM tQuit ft)
    rs7 : JS ((sE , false) , tE)

  -- the phases are closed under every joint step
  presS : ∀ {σ ℓ σ′} → JS σ → RSm.PStp σ ℓ σ′ → JS σ′
  presS rs1      (RSm.pτL sτI) = rs1
  presS (rs2 rm) (RSm.pτL sτI) = rs2 rm
  presS rs3      (RSm.pτL sτB) = rs3
  presS rs5      (RSm.pτL sτQ) = rs5
  presS rs1 (RSm.pτR (CE.tτ _)) = rs1
  presS rs3 (RSm.pτR (CE.tτ _)) = rs3
  presS rs4 (RSm.pτR (CE.tτ _)) = rs4
  presS rs5 (RSm.pτR (CE.tτ _)) = rs5
  presS rs6 (RSm.pτR (CE.tτ _)) = rs6
  presS rs1 (RSm.pτR (CE.tCh _ _ _ _ _ _ _ rm)) = rs2 rm
  presS rs3 (RSm.pτR (CE.tCh _ _ _ _ _ _ () _))
  presS rs4 (RSm.pτR (CE.tCh _ _ _ _ _ _ () _))
  presS rs5 (RSm.pτR (CE.tCh _ _ _ _ _ _ () _))
  presS rs6 (RSm.pτR (CE.tCh _ _ _ _ _ _ () _))
  presS rs3 (RSm.psL _ (sAA _))   = rs4
  presS rs3 (RSm.psL _ (sAO _ _)) = rs4
  presS rs3 (RSm.psL _ (sAT _))   = rs4
  presS rs3 (RSm.psL _ (sAV _))   = rs4
  presS rs3 (RSm.psL _ (sAC _))   = rs4
  presS rs5 (RSm.psL _ sDn)       = rs6
  presS _ (RSm.psL ¬w sRN)       = ⊥-elim (¬w U.tt)
  presS _ (RSm.psL ¬w sQi)       = ⊥-elim (¬w U.tt)
  presS _ (RSm.psL ¬w (sNA _))   = ⊥-elim (¬w U.tt)
  presS _ (RSm.psL ¬w (sNO _ _)) = ⊥-elim (¬w U.tt)
  presS _ (RSm.psL ¬w (sNT _))   = ⊥-elim (¬w U.tt)
  presS _ (RSm.psL ¬w (sNV _))   = ⊥-elim (¬w U.tt)
  presS _ (RSm.psL ¬w sNC)       = ⊥-elim (¬w U.tt)
  presS _ (RSm.psL ¬w sDS)       = ⊥-elim (¬w U.tt)
  presS _ (RSm.psR ¬w b) = ⊥-elim (¬w (CE.tWire b))
  presS _ (RSm.psy w (sAA _) _)   = ⊥-elim w
  presS _ (RSm.psy w (sAO _ _) _) = ⊥-elim w
  presS _ (RSm.psy w (sAT _) _)   = ⊥-elim w
  presS _ (RSm.psy w (sAV _) _)   = ⊥-elim w
  presS _ (RSm.psy w (sAC _) _)   = ⊥-elim w
  presS _ (RSm.psy w sDn _)       = ⊥-elim w
  presS rs1 (RSm.psy _ sRN (CE.tAcc _ _ _ _ _ _ () _))
  presS rs1 (RSm.psy _ sQi (CE.tAcc _ _ _ _ _ _ () _))
  presS (rs2 rm) (RSm.psy _ sRN (CE.tEm _ _ _)) with rm
  ... | refl = rs3
  presS (rs2 rm) (RSm.psy _ sQi (CE.tEm _ _ _)) with rm
  ... | refl = rs5
  presS rs4 (RSm.psy _ (sNA _) (CE.tAcc _ _ _ _ _ _ _ rm)) with rm
  ... | refl = rs1
  presS rs4 (RSm.psy _ (sNO _ _) (CE.tAcc _ _ _ _ _ _ _ rm)) with rm
  ... | refl = rs1
  presS rs4 (RSm.psy _ (sNT _) (CE.tAcc _ _ _ _ _ _ _ rm)) with rm
  ... | refl = rs1
  presS rs4 (RSm.psy _ (sNV _) (CE.tAcc _ _ _ _ _ _ _ rm)) with rm
  ... | refl = rs1
  presS rs4 (RSm.psy _ sNC (CE.tAcc _ _ _ _ _ _ _ rm)) with rm
  ... | refl = rs1
  presS rs6 (RSm.psy _ sDS (CE.tAcc _ _ _ _ _ _ _ rm)) with rm
  ... | refl = rs7

  -- PROGRESS: every phase has a joint step, or both have ended.  At `rs2` this is
  -- RECEPTIVENESS itself: whichever of RequestNext / Quit `ClientEnv` committed to (any
  -- payload), the server takes it
  progSE : ∀ {σ} → JS σ → Abs.Fin RSm.ParA σ ⊎ Σ[ ℓ ∈ ALbl l ] Σ[ σ′ ∈ _ ] RSm.PStp σ ℓ σ′
  progSE (rs1 {true})          = inj₂ (_ , _ , RSm.pτL sτI)
  progSE (rs1 {false} {true})  = inj₂ (_ , _ , RSm.pτR (CE.tτ tIdle))
  progSE (rs1 {false} {false}) =
    inj₂ (_ , _ , RSm.pτR (CE.tCh tIdle time₀ FromInitiator length₀ MsgLNPRequestNext (inj₁ tBusy) U.tt refl))
  progSE (rs2 {true} _)   = inj₂ (_ , _ , RSm.pτL sτI)
  progSE (rs2 {false} rm) with idleM rm
  ... | imN = inj₂ (_ , _ , RSm.psy U.tt sRN (CE.tEm tIdle _ _))
  ... | imQ = inj₂ (_ , _ , RSm.psy U.tt sQi (CE.tEm tIdle _ _))
  progSE (rs3 {true})  = inj₂ (_ , _ , RSm.pτL sτB)
  progSE (rs3 {false}) = inj₂ (_ , _ , RSm.psL (λ ()) (sAC U.tt))
  progSE (rs4 {_} {true}) = inj₂ (_ , _ , RSm.pτR (CE.tτ tBusy))
  progSE (rs4 {rA h} {false}) =
    inj₂ (_ , _ , RSm.psy U.tt (sNA h) (CE.tAcc tBusy time₀ FromResponder length₀ (MsgLNPBlockAnnouncement h) (inj₁ tIdle) U.tt refl))
  progSE (rs4 {rO q sz} {false}) =
    inj₂ (_ , _ , RSm.psy U.tt (sNO q sz) (CE.tAcc tBusy time₀ FromResponder length₀ (MsgLNPBlockOffer q sz) (inj₁ tIdle) U.tt refl))
  progSE (rs4 {rT q} {false}) =
    inj₂ (_ , _ , RSm.psy U.tt (sNT q) (CE.tAcc tBusy time₀ FromResponder length₀ (MsgLNPBlockTxsOffer q) (inj₁ tIdle) U.tt refl))
  progSE (rs4 {rV vs} {false}) =
    inj₂ (_ , _ , RSm.psy U.tt (sNV vs) (CE.tAcc tBusy time₀ FromResponder length₀ (MsgLNPVotes vs) (inj₁ tIdle) U.tt refl))
  progSE (rs4 {rC} {false}) =
    inj₂ (_ , _ , RSm.psy U.tt sNC (CE.tAcc tBusy time₀ FromResponder length₀ MsgLNPCanceled (inj₁ tIdle) U.tt refl))
  progSE (rs5 {true})  = inj₂ (_ , _ , RSm.pτL sτQ)
  progSE (rs5 {false}) = inj₂ (_ , _ , RSm.psL (λ ()) sDn)
  progSE (rs6 {true})  = inj₂ (_ , _ , RSm.pτR (CE.tτ tQuit))
  progSE (rs6 {false}) =
    inj₂ (_ , _ , RSm.psy U.tt sDS (CE.tAcc tQuit time₀ FromResponder length₀ MsgLNPDone (inj₂ tt) U.tt refl))
  progSE rs7 = inj₁ (U.tt , U.tt)

  -- the invariant argument for the server side
  module DLS = InvDL RSm.ParA (RSm.ParI (SI l) CE.TI) JS presS progSE

  -- the server side starts in phase `rs1`
  sEnv₀ : Abs.Pos RSm.ParA ((sI , false) , tM tIdle false) serverEnvSys
  sEnv₀ = _ , _ , refl , srv₀ l , CE.tpM tIdle

  -- (R) THE SERVER IS RECEPTIVE: against the most general table-conforming client it never
  -- gets stuck before √ — in StIdle it accepts both RequestNext and Quit, in StBusy /
  -- StQuit it accepts nothing (it holds agency), with any payload
  server-receptive : DeadlockFree serverEnvSys
  server-receptive = DLS.dlFree sEnv₀ rs1

  -- (R) … and the composition never diverges
  server-receptive-divFree : DivergenceFree serverEnvSys
  server-receptive-divFree = Gen.divFree l RSm.ParA sEnv₀

  ---------------------------------------------------------------- the negative control

  -- the bad pair's start
  σB₀ : TS × TS
  σB₀ = tM tIdle false , tM tIdle false

  -- the stuck state: the bad client in StBusy, `ServerEnv` committed to MsgCanceled
  σBX : TS × TS
  σBX = tM tBusy false , tC tBusy (pay l FromResponder MsgLNPCanceled) (inj₁ tIdle)

  -- the trace into it: one RequestNext
  badTr : List Event
  badTr = ⌞ wS lo (pay l FromInitiator MsgLNPRequestNext) ⌟ ∷ []

  -- the abstract run into it
  badRun : Gen.ARun l RBm.ParA σB₀ badTr σBX
  badRun =
    rτ (RBm.pτL (BD.tCh tIdle time₀ FromInitiator length₀ MsgLNPRequestNext (inj₁ tBusy) U.tt refl))
    (rE (RBm.psy U.tt (BD.tEm tIdle _ _)
                      (SE.tAcc tIdle time₀ FromInitiator length₀ MsgLNPRequestNext (inj₁ tBusy) U.tt refl))
    (rτ (RBm.pτL (BD.tτ tBusy))
    (rτ (RBm.pτR (SE.tτ tBusy))
    (rτ (RBm.pτR (SE.tCh tBusy time₀ FromResponder length₀ MsgLNPCanceled (inj₁ tIdle) U.tt refl))
     r0))))
    where open Gen l RBm.ParA using (rE; rτ; r0)

  -- in the stuck state nothing moves: the bad client offers only the four replies, the
  -- server only MsgCanceled
  noStepB : ∀ {ℓ σ′} → RBm.PStp σBX ℓ σ′ → ⊥
  noStepB (RBm.pτL (BD.tCh _ _ _ _ _ _ () _))
  noStepB (RBm.psL ¬w b) = ¬w (BD.tWire b)
  noStepB (RBm.psR ¬w b) = ¬w (SE.tWire b)
  noStepB (RBm.psy _ (BD.tAcc _ _ _ _ _ _ _ rm) (SE.tEm _ _ _)) = case rm of λ ()

  -- (R−) NEGATIVE CONTROL: the check has teeth — a client that does not accept MsgCanceled
  -- in StBusy deadlocks against the most general server, right after one RequestNext
  bad-deadlock : HasDeadlock badEnvSys
  bad-deadlock with GenI.runI l (RBm.ParI BD.TI SE.TI) badRun (_ , _ , refl , BD.tpM tIdle , SE.tpM tIdle)
  ... | W , r , p = badTr , W , r , Gen.stuckE l RBm.ParA p noStepB (λ { (() , _) })

  ------------------------------------------------------------------------
  -- §5  (FD) The hidden pair against the table with internal agency choices
  ------------------------------------------------------------------------

  -- whether an event is peer-local (api or done)
  locEv : ∀ {A} → LNPEv A → Bool
  locEv (apiLPev _ _ _) = true
  locEv (doneLNP _ _)   = true
  locEv _               = false

  -- every api and done event of the pair (both directions)
  apiDoneES : EventSet
  apiDoneES = record { mem = λ at _ → T (locEv (proj₂ at)) ; dec = λ at _ → T? (locEv (proj₂ at)) }

  -- THE HIDDEN PAIR: the real pair with all api / done events hidden (only the wire remains)
  sysH : Tree
  sysH = sys l ∖ apiDoneES

  -- every agency choice is internal
  allAg : TSt l → Bool
  allAg _ = true

  -- the mode of a state's sender
  modeOf : TSt l → Mode
  modeOf tIdle = FromInitiator
  modeOf _     = FromResponder

  -- the peers' envelope (`time₀` / sender mode / `length₀`) around the chosen message
  nzS : TSt l → Payload → Payload
  nzS st (_ , _ , _ , msg) = time₀ , modeOf st , length₀ , msg

  -- the table with every agency choice internal
  module SPc = Tbl row allAg nzS

  -- THE TABLE WITH INTERNAL AGENCY CHOICES: StIdle ⊓ {RequestNext, Quit}; StBusy ⊓ over the
  -- four replies and MsgCanceled with any content; StQuit MsgDone then √; wire only
  LNPSpec⊓ : Tree
  LNPSpec⊓ = SPc.proc

  -- the wire and the peer-local events are disjoint
  disjWH : ∀ {ω} → InE l (wireES l) ω → InE l apiDoneES ω → ⊥
  disjWH {wS _ _}   _ ()
  disjWH {wR _ _}   _ ()
  disjWH {ap _ _ _} ()
  disjWH {dn _}     ()

  -- every label is on the wire or peer-local
  offWH : ∀ {ω} → ¬ InE l (wireES l) ω → ¬ InE l apiDoneES ω → ⊥
  offWH {wS _ _}   ¬w _  = ¬w U.tt
  offWH {wR _ _}   ¬w _  = ¬w U.tt
  offWH {ap _ _ _} _  ¬h = ¬h U.tt
  offWH {dn _}     _  ¬h = ¬h U.tt

  -- the client's distance to its next wire event (api steps and loop-backs count)
  νc : CS l → Bool → ℕ
  νc cI     f = suc (fl l f)
  νc (cD _) _ = 3
  νc _      f = fl l f

  -- the server's distance to its next wire event
  νs : SS l → Bool → ℕ
  νs sB f = suc (fl l f)
  νs sQ f = suc (fl l f)
  νs _  f = fl l f

  -- the pair's measure
  νS : SysS l → ℕ
  νS ((c , fc) , (s , fs)) = νc c fc + νs s fs

  -- every τ of the pair decreases the measure
  ντS : ∀ {σ σ′} → Abs.Stp (SysA l) σ τ′ σ′ → νS σ′ < νS σ
  ντS {_ , (s , fs)} (P1.pτL cτI) = +-monoˡ-< (νs s fs) (s≤s (s≤s z≤n))
  ντS {_ , (s , fs)} (P1.pτL cτB) = +-monoˡ-< (νs s fs) (s≤s z≤n)
  ντS {_ , (s , fs)} (P1.pτL cτQ) = +-monoˡ-< (νs s fs) (s≤s z≤n)
  ντS {(c , fc) , _} (P1.pτR sτI) = +-monoʳ-< (νc c fc) (s≤s z≤n)
  ντS {(c , fc) , _} (P1.pτR sτB) = +-monoʳ-< (νc c fc) (s≤s (s≤s z≤n))
  ντS {(c , fc) , _} (P1.pτR sτQ) = +-monoʳ-< (νc c fc) (s≤s (s≤s z≤n))

  -- every api / done step of the pair decreases the measure
  νhS : ∀ {σ ω σ′} → InE l apiDoneES ω → Abs.Stp (SysA l) σ (ev′ ω) σ′ → νS σ′ < νS σ
  νhS {_ , (s , fs)} _ (P1.psL _ (cRN _))   = +-monoˡ-< (νs s fs) (s≤s z≤n)
  νhS {_ , (s , fs)} _ (P1.psL _ (cQi _))   = +-monoˡ-< (νs s fs) (s≤s z≤n)
  νhS {_ , (s , fs)} _ (P1.psL _ (cDA _))   = +-monoˡ-< (νs s fs) (s≤s (s≤s (s≤s z≤n)))
  νhS {_ , (s , fs)} _ (P1.psL _ (cDO _ _)) = +-monoˡ-< (νs s fs) (s≤s (s≤s (s≤s z≤n)))
  νhS {_ , (s , fs)} _ (P1.psL _ (cDT _))   = +-monoˡ-< (νs s fs) (s≤s (s≤s (s≤s z≤n)))
  νhS {_ , (s , fs)} _ (P1.psL _ (cDV _))   = +-monoˡ-< (νs s fs) (s≤s (s≤s (s≤s z≤n)))
  νhS m (P1.psL _ cSR)       = ⊥-elim m
  νhS m (P1.psL _ cSQ)       = ⊥-elim m
  νhS m (P1.psL _ (cRA _))   = ⊥-elim m
  νhS m (P1.psL _ (cRO _ _)) = ⊥-elim m
  νhS m (P1.psL _ (cRT _))   = ⊥-elim m
  νhS m (P1.psL _ (cRV _))   = ⊥-elim m
  νhS m (P1.psL _ cRC)       = ⊥-elim m
  νhS m (P1.psL _ cDn)       = ⊥-elim m
  νhS {(c , fc) , _} _ (P1.psR _ (sAA _))   = +-monoʳ-< (νc c fc) (s≤s z≤n)
  νhS {(c , fc) , _} _ (P1.psR _ (sAO _ _)) = +-monoʳ-< (νc c fc) (s≤s z≤n)
  νhS {(c , fc) , _} _ (P1.psR _ (sAT _))   = +-monoʳ-< (νc c fc) (s≤s z≤n)
  νhS {(c , fc) , _} _ (P1.psR _ (sAV _))   = +-monoʳ-< (νc c fc) (s≤s z≤n)
  νhS {(c , fc) , _} _ (P1.psR _ (sAC _))   = +-monoʳ-< (νc c fc) (s≤s z≤n)
  νhS {(c , fc) , _} _ (P1.psR _ sDn)       = +-monoʳ-< (νc c fc) (s≤s z≤n)
  νhS m (P1.psR _ sRN)       = ⊥-elim m
  νhS m (P1.psR _ sQi)       = ⊥-elim m
  νhS m (P1.psR _ (sNA _))   = ⊥-elim m
  νhS m (P1.psR _ (sNO _ _)) = ⊥-elim m
  νhS m (P1.psR _ (sNT _))   = ⊥-elim m
  νhS m (P1.psR _ (sNV _))   = ⊥-elim m
  νhS m (P1.psR _ sNC)       = ⊥-elim m
  νhS m (P1.psR _ sDS)       = ⊥-elim m
  νhS m (P1.psy {ω = ω} w _ _) = ⊥-elim (disjWH {ω} w m)

  -- the hidden pair's abstraction
  module HS = HideA (SysA l) apiDoneES νS ντS νhS

  -- … and its intro facts
  HSI : AbsI l HS.HAbs
  HSI = HS.HI (SysI l)

  -- the hidden pair starts at the pair's start
  sysH₀ : HS.HPos (σ₀ l) sysH
  sysH₀ = sys l , refl , sys₀ l

  -- (FD) HIDING INTRODUCES NO DIVERGENCE: every api / done event is followed by a wire
  -- event or √ (the measure `νS`)
  sysH-divergenceFree : DivergenceFree sysH
  sysH-divergenceFree = Gen.divFree l HS.HAbs sysH₀

  -- weak steps of the hidden pair
  module WH = Wk HS.HAbs
  -- weak steps of the table
  module WT = Wk SPc.TA
  -- (concrete)
  module WIH = WkI HSI
  -- (concrete)
  module WIT = WkI SPc.TI

  -- THE BISIMULATION on abstract states: the hidden pair's phase against the table's state
  data DR : SysS l → TS → Set where
    dI  : ∀ {fc fs ft}      → DR ((cI , fc) , (sI , fs)) (tM tIdle ft)
    dD  : ∀ {dv fs ft}      → DR ((cD dv , false) , (sI , fs)) (tM tIdle ft)
    dR  : ∀ {fs tm md ln}   → DR ((cR , false) , (sI , fs))
                                 (tC tIdle (tm , md , ln , leiosNotifyP MsgLNPRequestNext) (inj₁ tBusy))
    dS  : ∀ {fs tm md ln}   → DR ((cS , false) , (sI , fs))
                                 (tC tIdle (tm , md , ln , leiosNotifyP MsgLNPQuit) (inj₁ tQuit))
    dB  : ∀ {fc fs ft}      → DR ((cB , fc) , (sB , fs)) (tM tBusy ft)
    dN  : ∀ {fc r tm md ln} → DR ((cB , fc) , (sN r , false))
                                 (tC tBusy (tm , md , ln , leiosNotifyP (repM l r)) (inj₁ tIdle))
    dQ  : ∀ {fc fs ft}      → DR ((cQ , fc) , (sQ , fs)) (tM tQuit ft)
    dDn : ∀ {fc tm md ln}   → DR ((cQ , fc) , (sD , false))
                                 (tC tQuit (tm , md , ln , leiosNotifyP MsgLNPDone) (inj₂ tt))
    dE  : DR ((cE , false) , (sE , false)) tE

  -- the table settles a pending loop-back, then takes an internal choice
  spT : ∀ {st ft ρ′} → SPc.TStp (tM st false) τ′ ρ′ → WT.τ* (tM st ft) ρ′
  spT {st} {true}  a = SPc.tτ st WT.◅ (a WT.◅ WT.ε)
  spT {st} {false} a = a WT.◅ WT.ε

  -- the hidden pair settles a pending client loop-back
  fC : ∀ {c s fc} → CStp l (c , true) τ′ (c , false) → WH.τ* ((c , fc) , s) ((c , false) , s)
  fC {fc = true}  a = HS.hτ (P1.pτL a) WH.◅ WH.ε
  fC {fc = false} _ = WH.ε

  -- the hidden pair settles a pending server loop-back
  fS : ∀ {c s fs} → SStp l (s , true) τ′ (s , false) → WH.τ* (c , (s , fs)) (c , (s , false))
  fS {fs = true}  a = HS.hτ (P1.pτR a) WH.◅ WH.ε
  fS {fs = false} _ = WH.ε

  -- the hidden pair delivers a reply (hidden) and settles the loop-back
  dlvH : ∀ {fs} dv → WH.τ* ((cD dv , false) , (sI , fs)) ((cI , false) , (sI , fs))
  dlvH (dAnn h)    = HS.hh _ U.tt (P1.psL (λ ()) (cDA h))    WH.◅ (HS.hτ (P1.pτL cτI) WH.◅ WH.ε)
  dlvH (dOff q sz) = HS.hh _ U.tt (P1.psL (λ ()) (cDO q sz)) WH.◅ (HS.hτ (P1.pτL cτI) WH.◅ WH.ε)
  dlvH (dTxs q)    = HS.hh _ U.tt (P1.psL (λ ()) (cDT q))    WH.◅ (HS.hτ (P1.pτL cτI) WH.◅ WH.ε)
  dlvH (dVot vs)   = HS.hh _ U.tt (P1.psL (λ ()) (cDV vs))   WH.◅ (HS.hτ (P1.pτL cτI) WH.◅ WH.ε)

  -- the hidden pair matches the table's StIdle choice (the client's hidden api command)
  idleGo : ∀ {fs tm md ln m r} → row tIdle m ≡ just r
         → Σ[ σ′ ∈ SysS l ] (WH.τ* ((cI , false) , (sI , fs)) σ′ × DR σ′ (tC tIdle (tm , md , ln , leiosNotifyP m) r))
  idleGo rm with idleM rm
  ... | imN = _ , HS.hh _ U.tt (P1.psL (λ ()) (cRN U.tt)) WH.◅ WH.ε , dR
  ... | imQ = _ , HS.hh _ U.tt (P1.psL (λ ()) (cQi U.tt)) WH.◅ WH.ε , dS

  -- the hidden pair matches the table's StBusy choice (the server's hidden api command)
  busyGo : ∀ {fc tm md ln m r} → row tBusy m ≡ just r
         → Σ[ σ′ ∈ SysS l ] (WH.τ* ((cB , fc) , (sB , false)) σ′ × DR σ′ (tC tBusy (tm , md , ln , leiosNotifyP m) r))
  busyGo rm with busyM rm
  ... | bmA h , refl    = _ , HS.hh _ U.tt (P1.psR (λ ()) (sAA h)) WH.◅ WH.ε , dN
  ... | bmO q sz , refl = _ , HS.hh _ U.tt (P1.psR (λ ()) (sAO q sz)) WH.◅ WH.ε , dN
  ... | bmT q , refl    = _ , HS.hh _ U.tt (P1.psR (λ ()) (sAT q)) WH.◅ WH.ε , dN
  ... | bmV vs , refl   = _ , HS.hh _ U.tt (P1.psR (λ ()) (sAV vs)) WH.◅ WH.ε , dN
  ... | bmC , refl      = _ , HS.hh _ U.tt (P1.psR (λ ()) (sAC U.tt)) WH.◅ WH.ε , dN

  -- the hidden pair matches the table's StQuit choice (the server's hidden done)
  quitGo : ∀ {fc tm md ln m r} → row tQuit m ≡ just r
         → Σ[ σ′ ∈ SysS l ] (WH.τ* ((cQ , fc) , (sQ , false)) σ′ × DR σ′ (tC tQuit (tm , md , ln , leiosNotifyP m) r))
  quitGo rm with quitM rm
  ... | refl , refl = _ , HS.hh _ U.tt (P1.psR (λ ()) sDn) WH.◅ WH.ε , dDn

  -- the ended pair makes no τ
  endNoτ : ∀ {σ′} → Abs.Stp (SysA l) ((cE , false) , (sE , false)) τ′ σ′ → ⊥
  endNoτ (P1.pτL ())
  endNoτ (P1.pτR ())

  -- FORWARD: every hidden-pair step is matched by a weak table step
  fwdA : ∀ {σ ρ ℓ σ′} → DR σ ρ → HS.HStp σ ℓ σ′ → Σ[ ρ′ ∈ TS ] (WT.W ρ ℓ ρ′ × DR σ′ ρ′)
  fwdA dI  (HS.hτ (P1.pτL cτI)) = _ , WT.ε , dI
  fwdA dB  (HS.hτ (P1.pτL cτB)) = _ , WT.ε , dB
  fwdA dN  (HS.hτ (P1.pτL cτB)) = _ , WT.ε , dN
  fwdA dQ  (HS.hτ (P1.pτL cτQ)) = _ , WT.ε , dQ
  fwdA dDn (HS.hτ (P1.pτL cτQ)) = _ , WT.ε , dDn
  fwdA dI  (HS.hτ (P1.pτR sτI)) = _ , WT.ε , dI
  fwdA dD  (HS.hτ (P1.pτR sτI)) = _ , WT.ε , dD
  fwdA dR  (HS.hτ (P1.pτR sτI)) = _ , WT.ε , dR
  fwdA dS  (HS.hτ (P1.pτR sτI)) = _ , WT.ε , dS
  fwdA dB  (HS.hτ (P1.pτR sτB)) = _ , WT.ε , dB
  fwdA dQ  (HS.hτ (P1.pτR sτQ)) = _ , WT.ε , dQ
  fwdA dE  (HS.hτ a) = ⊥-elim (endNoτ a)
  fwdA dI (HS.hh _ _ (P1.psL _ (cRN _))) =
    _ , spT (SPc.tCh tIdle time₀ FromInitiator length₀ MsgLNPRequestNext (inj₁ tBusy) U.tt refl) , dR
  fwdA dI (HS.hh _ _ (P1.psL _ (cQi _))) =
    _ , spT (SPc.tCh tIdle time₀ FromInitiator length₀ MsgLNPQuit (inj₁ tQuit) U.tt refl) , dS
  fwdA dD (HS.hh _ _ (P1.psL _ (cDA _)))   = _ , WT.ε , dI
  fwdA dD (HS.hh _ _ (P1.psL _ (cDO _ _))) = _ , WT.ε , dI
  fwdA dD (HS.hh _ _ (P1.psL _ (cDT _)))   = _ , WT.ε , dI
  fwdA dD (HS.hh _ _ (P1.psL _ (cDV _)))   = _ , WT.ε , dI
  fwdA _ (HS.hh _ m (P1.psL _ cSR))       = ⊥-elim m
  fwdA _ (HS.hh _ m (P1.psL _ cSQ))       = ⊥-elim m
  fwdA _ (HS.hh _ m (P1.psL _ (cRA _)))   = ⊥-elim m
  fwdA _ (HS.hh _ m (P1.psL _ (cRO _ _))) = ⊥-elim m
  fwdA _ (HS.hh _ m (P1.psL _ (cRT _)))   = ⊥-elim m
  fwdA _ (HS.hh _ m (P1.psL _ (cRV _)))   = ⊥-elim m
  fwdA _ (HS.hh _ m (P1.psL _ cRC))       = ⊥-elim m
  fwdA _ (HS.hh _ m (P1.psL _ cDn))       = ⊥-elim m
  fwdA dB (HS.hh _ _ (P1.psR _ (sAA h))) =
    _ , spT (SPc.tCh tBusy time₀ FromResponder length₀ (MsgLNPBlockAnnouncement h) (inj₁ tIdle) U.tt refl) , dN
  fwdA dB (HS.hh _ _ (P1.psR _ (sAO q sz))) =
    _ , spT (SPc.tCh tBusy time₀ FromResponder length₀ (MsgLNPBlockOffer q sz) (inj₁ tIdle) U.tt refl) , dN
  fwdA dB (HS.hh _ _ (P1.psR _ (sAT q))) =
    _ , spT (SPc.tCh tBusy time₀ FromResponder length₀ (MsgLNPBlockTxsOffer q) (inj₁ tIdle) U.tt refl) , dN
  fwdA dB (HS.hh _ _ (P1.psR _ (sAV vs))) =
    _ , spT (SPc.tCh tBusy time₀ FromResponder length₀ (MsgLNPVotes vs) (inj₁ tIdle) U.tt refl) , dN
  fwdA dB (HS.hh _ _ (P1.psR _ (sAC _))) =
    _ , spT (SPc.tCh tBusy time₀ FromResponder length₀ MsgLNPCanceled (inj₁ tIdle) U.tt refl) , dN
  fwdA dQ (HS.hh _ _ (P1.psR _ sDn)) =
    _ , spT (SPc.tCh tQuit time₀ FromResponder length₀ MsgLNPDone (inj₂ tt) U.tt refl) , dDn
  fwdA _ (HS.hh _ m (P1.psR _ sRN))       = ⊥-elim m
  fwdA _ (HS.hh _ m (P1.psR _ sQi))       = ⊥-elim m
  fwdA _ (HS.hh _ m (P1.psR _ (sNA _)))   = ⊥-elim m
  fwdA _ (HS.hh _ m (P1.psR _ (sNO _ _))) = ⊥-elim m
  fwdA _ (HS.hh _ m (P1.psR _ (sNT _)))   = ⊥-elim m
  fwdA _ (HS.hh _ m (P1.psR _ (sNV _)))   = ⊥-elim m
  fwdA _ (HS.hh _ m (P1.psR _ sNC))       = ⊥-elim m
  fwdA _ (HS.hh _ m (P1.psR _ sDS))       = ⊥-elim m
  fwdA _ (HS.hh ω m (P1.psy w _ _))       = ⊥-elim (disjWH {ω} w m)
  fwdA _ (HS.hk ω ¬m (P1.psL ¬w _)) = ⊥-elim (offWH {ω} ¬w ¬m)
  fwdA _ (HS.hk ω ¬m (P1.psR ¬w _)) = ⊥-elim (offWH {ω} ¬w ¬m)
  fwdA _ (HS.hk _ _ (P1.psy w (cRN _) _))   = ⊥-elim w
  fwdA _ (HS.hk _ _ (P1.psy w (cQi _) _))   = ⊥-elim w
  fwdA _ (HS.hk _ _ (P1.psy w (cDA _) _))   = ⊥-elim w
  fwdA _ (HS.hk _ _ (P1.psy w (cDO _ _) _)) = ⊥-elim w
  fwdA _ (HS.hk _ _ (P1.psy w (cDT _) _))   = ⊥-elim w
  fwdA _ (HS.hk _ _ (P1.psy w (cDV _) _))   = ⊥-elim w
  fwdA dR (HS.hk _ _ (P1.psy _ cSR sRN)) = _ , (_ , _ , WT.ε , SPc.tEm tIdle _ _ , WT.ε) , dB
  fwdA dS (HS.hk _ _ (P1.psy _ cSQ sQi)) = _ , (_ , _ , WT.ε , SPc.tEm tIdle _ _ , WT.ε) , dQ
  fwdA dN (HS.hk _ _ (P1.psy _ (cRA _) (sNA _)))   = _ , (_ , _ , WT.ε , SPc.tEm tBusy _ _ , WT.ε) , dD
  fwdA dN (HS.hk _ _ (P1.psy _ (cRO _ _) (sNO _ _))) = _ , (_ , _ , WT.ε , SPc.tEm tBusy _ _ , WT.ε) , dD
  fwdA dN (HS.hk _ _ (P1.psy _ (cRT _) (sNT _)))   = _ , (_ , _ , WT.ε , SPc.tEm tBusy _ _ , WT.ε) , dD
  fwdA dN (HS.hk _ _ (P1.psy _ (cRV _) (sNV _)))   = _ , (_ , _ , WT.ε , SPc.tEm tBusy _ _ , WT.ε) , dD
  fwdA dN (HS.hk _ _ (P1.psy _ cRC sNC))           = _ , (_ , _ , WT.ε , SPc.tEm tBusy _ _ , WT.ε) , dI
  fwdA dDn (HS.hk _ _ (P1.psy _ cDn sDS))          = _ , (_ , _ , WT.ε , SPc.tEm tQuit _ _ , WT.ε) , dE

  -- BACKWARD: every table step is matched by a weak hidden-pair step
  bwdA : ∀ {σ ρ ℓ ρ′} → DR σ ρ → SPc.TStp ρ ℓ ρ′ → Σ[ σ′ ∈ SysS l ] (WH.W σ ℓ σ′ × DR σ′ ρ′)
  bwdA _ (SPc.tAcc _ _ _ _ _ _ () _)
  bwdA dI (SPc.tτ _) = _ , WH.ε , dI
  bwdA dD (SPc.tτ _) = _ , WH.ε , dD
  bwdA dB (SPc.tτ _) = _ , WH.ε , dB
  bwdA dQ (SPc.tτ _) = _ , WH.ε , dQ
  bwdA dI (SPc.tCh _ _ _ _ _ _ _ rm) with idleGo rm
  ... | σ′ , w , d = σ′ , fC cτI WH.◅◅ w , d
  bwdA (dD {dv}) (SPc.tCh _ _ _ _ _ _ _ rm) with idleGo rm
  ... | σ′ , w , d = σ′ , dlvH dv WH.◅◅ w , d
  bwdA dB (SPc.tCh _ _ _ _ _ _ _ rm) with busyGo rm
  ... | σ′ , w , d = σ′ , fS sτB WH.◅◅ w , d
  bwdA dQ (SPc.tCh _ _ _ _ _ _ _ rm) with quitGo rm
  ... | σ′ , w , d = σ′ , fS sτQ WH.◅◅ w , d
  bwdA dR (SPc.tEm _ _ _) = _ , (_ , _ , fS sτI , HS.hk _ (λ ()) (P1.psy U.tt cSR sRN) , WH.ε) , dB
  bwdA dS (SPc.tEm _ _ _) = _ , (_ , _ , fS sτI , HS.hk _ (λ ()) (P1.psy U.tt cSQ sQi) , WH.ε) , dQ
  bwdA (dN {r = rA h}) (SPc.tEm _ _ _) =
    _ , (_ , _ , fC cτB , HS.hk _ (λ ()) (P1.psy U.tt (cRA h) (sNA h)) , WH.ε) , dD
  bwdA (dN {r = rO q sz}) (SPc.tEm _ _ _) =
    _ , (_ , _ , fC cτB , HS.hk _ (λ ()) (P1.psy U.tt (cRO q sz) (sNO q sz)) , WH.ε) , dD
  bwdA (dN {r = rT q}) (SPc.tEm _ _ _) =
    _ , (_ , _ , fC cτB , HS.hk _ (λ ()) (P1.psy U.tt (cRT q) (sNT q)) , WH.ε) , dD
  bwdA (dN {r = rV vs}) (SPc.tEm _ _ _) =
    _ , (_ , _ , fC cτB , HS.hk _ (λ ()) (P1.psy U.tt (cRV vs) (sNV vs)) , WH.ε) , dD
  bwdA (dN {r = rC}) (SPc.tEm _ _ _) =
    _ , (_ , _ , fC cτB , HS.hk _ (λ ()) (P1.psy U.tt cRC sNC) , WH.ε) , dI
  bwdA dDn (SPc.tEm _ _ _) =
    _ , (_ , _ , fC cτQ , HS.hk _ (λ ()) (P1.psy U.tt cDn sDS) , WH.ε) , dE

  -- the pair has ended exactly when the table has (one direction)
  finL : ∀ {σ ρ} → DR σ ρ → Abs.Fin (SysA l) σ → TFin ρ
  finL dE  _ = U.tt
  finL dI  (() , _)
  finL dD  (() , _)
  finL dR  (() , _)
  finL dS  (() , _)
  finL dB  (() , _)
  finL dN  (() , _)
  finL dQ  (() , _)
  finL dDn (() , _)

  -- (the other)
  finR : ∀ {σ ρ} → DR σ ρ → TFin ρ → Abs.Fin (SysA l) σ
  finR dE _ = U.tt , U.tt
  finR dI  ()
  finR dD  ()
  finR dR  ()
  finR dS  ()
  finR dB  ()
  finR dN  ()
  finR dQ  ()
  finR dDn ()

  -- the concrete relation: positioned, abstractly related trees, or both past √
  Rel : Tree → Tree → Set₁
  Rel p q = (Σ[ σ ∈ SysS l ] Σ[ ρ ∈ TS ] (DR σ ρ × HS.HPos σ p × SPc.TPos ρ q)) ⊎ (p ≡ deadlock × q ≡ deadlock)

  -- a visible (or √) step of the hidden pair is matched by the table
  rFwdE : ∀ {p q} {lb : Event√ Rr} {p′} → Rel p q → p ─[ ev lb ]─► p′ → Σ[ q′ ∈ Tree ] (q ═[ ev lb ]═► q′ × Rel p′ q′)
  rFwdE (inj₁ (_ , _ , d , hp , tp)) (sRet eq) =
    deadlock , wev τ*-refl (sRet (SPc.tIntroR tp (finL d (HS.hElimR hp eq)))) τ*-refl , inj₂ (refl , refl)
  rFwdE {q = q} (inj₁ (_ , _ , d , hp , tp)) s@(sVis _ _) with HS.hElimE hp s
  ... | ω , σ′ , eq , a , hp′ with fwdA d a
  ...   | ρ′ , w , d′ with WIT.WI (ev′ ω) w tp
  ...     | q′ , wk , tp′ = q′ , subst (λ e → q ═[ ev (evl e) ]═► q′) (sym eq) wk , inj₁ (σ′ , ρ′ , d′ , hp′ , tp′)
  rFwdE (inj₂ (refl , refl)) (sRet ())
  rFwdE (inj₂ (refl , refl)) (sVis refl ())

  -- a τ of the hidden pair is matched by the table
  rFwdT : ∀ {p q p′} → Rel p q → p ─[ τ ]─► p′ → Σ[ q′ ∈ Tree ] (q ═[ τ ]═► q′ × Rel p′ q′)
  rFwdT (inj₁ (_ , _ , d , hp , tp)) s with HS.hElimτ hp s
  ... | σ′ , a , hp′ with fwdA d a
  ...   | ρ′ , w , d′ with WIT.WI τ′ w tp
  ...     | q′ , wk , tp′ = q′ , wk , inj₁ (σ′ , ρ′ , d′ , hp′ , tp′)
  rFwdT (inj₂ (refl , refl)) s = ⊥-elim (dlNoτ s)

  -- a visible (or √) step of the table is matched by the hidden pair
  rBwdE : ∀ {p q} {lb : Event√ Rr} {q′} → Rel p q → q ─[ ev lb ]─► q′ → Σ[ p′ ∈ Tree ] (p ═[ ev lb ]═► p′ × Rel p′ q′)
  rBwdE (inj₁ (_ , _ , d , hp , tp)) (sRet eq) =
    deadlock , wev τ*-refl (sRet (AbsI.introR HSI hp (finR d (SPc.tElimR tp eq)))) τ*-refl , inj₂ (refl , refl)
  rBwdE {p = p} (inj₁ (_ , _ , d , hp , tp)) s@(sVis _ _) with SPc.tElimE tp s
  ... | ω , ρ′ , eq , a , tp′ with bwdA d a
  ...   | σ′ , w , d′ with WIH.WI (ev′ ω) w hp
  ...     | p′ , wk , hp′ = p′ , subst (λ e → p ═[ ev (evl e) ]═► p′) (sym eq) wk , inj₁ (σ′ , ρ′ , d′ , hp′ , tp′)
  rBwdE (inj₂ (refl , refl)) (sRet ())
  rBwdE (inj₂ (refl , refl)) (sVis refl ())

  -- a τ of the table is matched by the hidden pair
  rBwdT : ∀ {p q q′} → Rel p q → q ─[ τ ]─► q′ → Σ[ p′ ∈ Tree ] (p ═[ τ ]═► p′ × Rel p′ q′)
  rBwdT (inj₁ (_ , _ , d , hp , tp)) s with SPc.tElimτ tp s
  ... | ρ′ , a , tp′ with bwdA d a
  ...   | σ′ , w , d′ with WIH.WI τ′ w hp
  ...     | p′ , wk , hp′ = p′ , wk , inj₁ (σ′ , ρ′ , d′ , hp′ , tp′)
  rBwdT (inj₂ (refl , refl)) s = ⊥-elim (dlNoτ s)

  -- the hidden pair never diverges
  ndivL : ∀ {p q} → Rel p q → Diverges p → ⊥
  ndivL (inj₁ (_ , _ , _ , hp , _)) dv = Gen.noDiv l HS.HAbs hp dv
  ndivL (inj₂ (refl , _)) dv = dlNoτ (Diverges.step dv)

  -- the table never diverges
  ndivR : ∀ {p q} → Rel p q → Diverges q → ⊥
  ndivR (inj₁ (_ , _ , _ , _ , tp)) dv = Gen.noDiv l SPc.TA tp dv
  ndivR (inj₂ (_ , refl)) dv = dlNoτ (Diverges.step dv)

  -- the two start related
  rel₀ : Rel sysH LNPSpec⊓
  rel₀ = inj₁ (σ₀ l , tM tIdle false , dI , sysH₀ , SPc.tpM tIdle)

  -- (FD) THE HIDDEN PAIR IS THE TABLE: divergence-respecting weak bisimilarity of the real
  -- pair (api / done hidden) and the table with internal agency choices
  sysH≈DR : sysH ≈DR LNPSpec⊓
  sysH≈DR = DRFromRel.rel→dr Rel rFwdE rFwdT rBwdE rBwdT ndivL ndivR rel₀

  -- (FD) (the other orientation)
  LNPSpec⊓≈DR : LNPSpec⊓ ≈DR sysH
  LNPSpec⊓≈DR = DRFromRel.rel→rd Rel rFwdE rFwdT rBwdE rBwdT ndivL ndivR rel₀

  -- (FD) FAILURES-DIVERGENCES CONFORMANCE: the hidden pair refines the table in the
  -- failures-divergences model (no trace, refusal or divergence outside the table)
  LNPSpec⊓-⊑FD : LNPSpec⊓ ⊑FD sysH
  LNPSpec⊓-⊑FD = drbisim→⊑FD LNPSpec⊓≈DR

  -- (FD) … and in fact the two are failures-divergences EQUIVALENT
  LNPSpec⊓-≈FD : LNPSpec⊓ ≈FD sysH
  LNPSpec⊓-≈FD = drbisim→≈FD LNPSpec⊓≈DR
