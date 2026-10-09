{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- LeiosNotify with PIPELINING (ouroboros-consensus PR 2344): properties of the depth-1
-- pipelined client and read-ahead server of `LeiosNotifyPipelined.agda`, composed over two
-- one-way FIFOs.  All results ∀ `Params`, ∀ link `l`.
--
-- THE SYSTEMS.  `psys l = (client(l , lo) ⦀ server(l , hi)) [| wire |] (fifo l lo hi ⦀ fifo l hi lo)`,
-- api / done open to the environment; `pblk = psys l [| srvApi |] Skip` refuses ALL FIVE
-- server api sends (the four notifications and `lnpSendCanceled`), exactly as
-- `LeiosNotifyQuit.blk` does for the non-pipelined pair: the server APPLICATION is silent.
--
-- THE METHOD (reused from `LeiosNotifyQuit`: `Abs`/`AbsI`, `Gen`/`GenI`, `Prod`, `SkA`, the
-- table `LNPSpec` and its row lemmas).  The four components are abstracted by small LTSs —
-- the peers through `PeerLNP`'s views of the reused `LeiosNotifyP` rounds plus one view of
-- each peer's single extra transition (`CBusyP`, `SBusyP`, `drainV`); one FIFO abstraction,
-- generic in its two directions — and composed with `Prod` (peers interleaved, FIFOs
-- interleaved, the two synchronised on the wire).  An inductive invariant `J` (25 joint
-- phases) carries side facts on every visible step (`Side`): the quit command enters the
-- post-quit region and it is never left; there the rank strictly drops (server api sends
-- exempt); and how the step changes the protocol-order bookkeeping — `PK`, the client
-- messages sent but not yet answered, and `Ans`, the answered ones paired with the server's.
--
-- MESSAGES.  `cm s` / `sm s`: the payloads the client (`sendLNP l lo`) / the server
-- (`sendLNP l hi`) SENDS in trace `s`, in send order.  `alt cs ss` is the protocol order as
-- the client end names it: c₁ s₁ c₂ s₂ …, then only the FIRST unanswered client message.
--
-- THE RESULTS:
--  (P1) `psys-protocolOrder`: for every √-free trace `s` of `psys l`, `alt (cm s) (sm s)` is a
--       trace of the blueprint table `LNPSpec l` (termination included), and
--       `length (sm s) ≤ length (cm s)` (CAUSALITY: traces are prefix closed, so the i-th
--       server message is sent after the i-th client message).  The structure behind it,
--       `psys-pairing` (`Pair s`): `cm s ≡ cs₀ ++ pend`, pend ∈ {[], [RN], [Quit], [RN , Quit]},
--       with `cs₀` paired one-to-one, in order, with `sm s` (`Ans`: RN ↦ a reply or
--       MsgCanceled, Quit ↦ MsgDone).  Consequently every MsgCanceled (0 or more) precedes
--       MsgQuit in protocol order.  DEVIATION from "alt cm sm is a table trace" read with
--       the whole tail: after a pipelined RN·Quit with RN still unanswered, "… RN Quit" is
--       NOT a table trace (StBusy has no Quit row) — the Quit's protocol-order place is
--       after RN's answer, which does not exist yet.  `alt` therefore stops after the first
--       unanswered client message; `Pair` records the pipelined one.
--  (P2) `pblk-afterQuit`: with the server application silent, once the client's quit command
--       `lnpSendDone` has occurred (from StIdle or PIPELINED with a request outstanding),
--       the rest is deadlock-free, divergence-free and has at most 8 visible events, so every
--       run from there is finite and ends in √.  `pblk-tight`: 8 is attained (RequestNext
--       still in the FIFO when the quit is commanded).
--  (P3) `psys-quitShape`: if MsgQuit is sent after `s₁` with k = |cm s₁| ∸ |sm s₁| requests
--       outstanding, then k ≤ 1, the client sends nothing more, and the server's messages
--       after it are a prefix of (k replies, then MsgDone) (`QuitTail`).  ATTRIBUTION,
--       `psys-attribution`: every notification the server sends was commanded by its
--       application, so a reply it did not command is MsgCanceled; `pblk-noNotification`
--       and `pblk-quitShape` (`QuitTailC`): with the application silent, the outstanding
--       request is answered by MsgCanceled (the read-ahead).
--  (P4) `psys-deadlockFree`, `psys-divergenceFree` (api / done open).
--  (P5) `stall-vs-pipelined`: the non-pipelined pair with the application silent has a
--       deadlock (`LeiosNotifyQuit.blk-deadlock`, the stall `blk-stall` after RequestNext),
--       the pipelined system has none (`pblk-deadlockFree`); `pblk-quitAfterRN`: the stall's
--       situation (RequestNext received by the server) continues through the pipelined quit,
--       the read-ahead MsgCanceled and MsgDone to √.
--  Also `psys-noBlock`: capacity 2 suffices — a peer about to send always finds room.
--
-- Pair level over idealised channels (see `LeiosNotifyPipelined.agda`'s header for the gap to
-- the real shared medium).  Constructive: no postulate, no `Classical`.
------------------------------------------------------------------------

open import Cardano_network.Params using (Params)

module Cardano_network.Parametric.Leios.LeiosNotifyPipelinedProps (p : Params) where

open import Data.Bool using (Bool; true; false; T; not; _∧_; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ; length-++; ∷-injective)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁻ˡ; ++⁻ʳ)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; _≤ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤ᵇ⇒≤; m≤m+n; m+n∸m≡n; +-assoc; +-identityʳ; m+n≡0⇒m≡0; m+n≡0⇒n≡0)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Unit as U
open import Data.Unit.Polymorphic using (tt)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees
open import Cardano_network.Base
open import Cardano_network.Net p
open import Cardano_network.Data p
open import Cardano_network.LeiosNotifyP p
open import Cardano_network.Parametric.Leios.NoLivelock.PeerLNP p
  using ( snd; iV
        ; CIdleV; ciNext; ciQuit; cIdleV; CBusyV; cbCan; cbAnn; cbOff; cbTxs; cbVote; cBusyV
        ; CQuitV; cqDone; cQuitV
        ; SIdleV; siNext; siQuit; sIdleV; SBusyV; sbCan; sbAnn; sbOff; sbTxs; sbVote; sBusyV
        ; SQuitV; sqDone; sQuitV )
open import Cardano_network.Parametric.Leios.LeiosNotifyQuit p
  using ( Tree; ≟-refl; vOf; pchS; outS; outI; pchNoτ; outNoτ; iterE; module IterNoτ
        ; Lab; wS; wR; ap; dn; ⌜_⌝; ALbl; τ′; ev′; InE; Abs; module Abs; AbsI; module AbsI
        ; module Gen; module GenI; module Prod
        ; pay; fl; fl<; Dlv; dAnn; dOff; dTxs; dVot; dlvT; Rep; rA; rO; rT; rV; rC; repM
        ; CAl; caS; caR; caA; SkA; SkI; wireES; srvCmd; srvEv; srvApi; disjSk
        ; specStep; LNPSpec; specEnd; spGo; spEnd; tReq; tQt; tAnn; tOff; tTxs; tVot; tCan; tDone
        ; tIdle; tBusy; tQuit; isQuitApi; QuitApi; quitApi-T; ∧-l; ∧-r; ⇒
        ; blk; blk-deadlock )
open import Cardano_network.Parametric.Leios.LeiosNotifyPipelined p
open Params p using (time₀; length₀)

open import CSP.Operators LNPEv-≟
  using (Ret; Output; pchoice; iter; iter-bind; viewV; Par⊤; Skip; EventSet; ∅ES)
open EventSet
open import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv}
open import Semantics.Deadlock {E = LNPEv} {I = ExtI LNPEv}
  using (IsStuck; DeadlockFree; HasDeadlock; _⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
open import Semantics.DivergenceFree {E = LNPEv} {I = ExtI LNPEv} using (DivergenceFree)
open import CSP.Laws.DivFree.Loop LNPEv-≟ using (iter-ev-elim)

------------------------------------------------------------------------
-- §0  Payloads, replies and the protocol-order pairing (link-free)
------------------------------------------------------------------------

-- the payloads the peers send, on their fixed envelope (`time₀` / sender mode / `length₀`)
pRN pQ pC pD : Payload
pRN = time₀ , FromInitiator , length₀ , leiosNotifyP MsgLNPRequestNext
pQ  = time₀ , FromInitiator , length₀ , leiosNotifyP MsgLNPQuit
pC  = time₀ , FromResponder , length₀ , leiosNotifyP MsgLNPCanceled
pD  = time₀ , FromResponder , length₀ , leiosNotifyP MsgLNPDone

-- a REPLY payload (any envelope): one of the four notifications, or MsgCanceled
data RepP : Payload → Set where
  rpA : ∀ {tm md ln} h    → RepP (tm , md , ln , leiosNotifyP (MsgLNPBlockAnnouncement h))
  rpO : ∀ {tm md ln} q sz → RepP (tm , md , ln , leiosNotifyP (MsgLNPBlockOffer q sz))
  rpT : ∀ {tm md ln} q    → RepP (tm , md , ln , leiosNotifyP (MsgLNPBlockTxsOffer q))
  rpV : ∀ {tm md ln} vs   → RepP (tm , md , ln , leiosNotifyP (MsgLNPVotes vs))
  rpC : ∀ {tm md ln}      → RepP (tm , md , ln , leiosNotifyP MsgLNPCanceled)

-- a reply is not a direction's last message
notLast : ∀ {x} → RepP x → isLast x ≡ false
notLast (rpA _)   = refl
notLast (rpO _ _) = refl
notLast (rpT _)   = refl
notLast (rpV _)   = refl
notLast rpC       = refl

-- ONE protocol-order answer (flags: has MsgDone been sent, before / after): RequestNext is
-- answered by a reply, MsgQuit by MsgDone
data Ans1 : Bool → Payload → Payload → Bool → Set where
  a1R : ∀ {x} → RepP x → Ans1 false pRN x false
  a1Q : Ans1 false pQ pD true

-- THE PROTOCOL-ORDER PAIRING of the client's messages `cs` with the server's messages `ss`
-- (both in send order): the i-th server message answers the i-th client message; every
-- client message but the last is RequestNext; MsgQuit, if answered, is answered by MsgDone
-- and is the last (flag `true`)
data Ans : Bool → List Payload → List Payload → Set where
  aε : Ans false [] []
  aR : ∀ {b x cs ss} → RepP x → Ans b cs ss → Ans b (pRN ∷ cs) (x ∷ ss)
  aQ : Ans true (pQ ∷ []) (pD ∷ [])

-- the pairing grows by one answer at the end
ans-snoc : ∀ {b cs ss q x b′} → Ans b cs ss → Ans1 b q x b′ → Ans b′ (cs ++ q ∷ []) (ss ++ x ∷ [])
ans-snoc aε       (a1R k) = aR k aε
ans-snoc aε       a1Q     = aQ
ans-snoc (aR k a) n       = aR k (ans-snoc a n)
ans-snoc aQ       ()

-- the client messages sent but NOT YET ANSWERED (in send order): nothing, RequestNext,
-- MsgQuit, or the pipelined RequestNext·MsgQuit
data PK : Set where
  k0 kR kQ kRQ : PK

-- (as a list)
pl : PK → List Payload
pl k0  = []
pl kR  = pRN ∷ []
pl kQ  = pQ ∷ []
pl kRQ = pRN ∷ pQ ∷ []

------------------------------------------------------------------------
-- everything below is for one link `l`
------------------------------------------------------------------------

module _ (l : Link) where

  -- this link's labels, read as events
  ⌞_⌟ : Lab l → Event
  ⌞_⌟ = ⌜_⌝ l

  ------------------------------------------------------------------------
  -- §1  The pipelined client's abstraction
  ------------------------------------------------------------------------

  -- the client's loop body, at `(l , lo)`
  kc : LNPState → Rd
  kc = pcStep l lo

  -- the client's phases: its three loop menus, the committed RequestNext / MsgQuit sends,
  -- the committed PIPELINED MsgQuit send, the drain menu, a delivery, the end
  data CPh : Set where
    cIdle cBusy cQuit cSndRN cSndQ cSndPQ cDrain cEnd : CPh
    cDlv : Dlv l → CPh

  -- the phase of a loop state
  cPh : LNPState → CPh
  cPh stIdle = cIdle
  cPh stBusy = cBusy
  cPh stQuit = cQuit

  -- where the client goes on a received reply: a delivery, or (MsgCanceled) straight back
  rcvTo : ∀ {x} → RepP x → CPh × Bool
  rcvTo (rpA h)    = cDlv (dAnn h) , false
  rcvTo (rpO q sz) = cDlv (dOff q sz) , false
  rcvTo (rpT q)    = cDlv (dTxs q) , false
  rcvTo (rpV vs)   = cDlv (dVot vs) , false
  rcvTo rpC        = cIdle , true

  -- the client's continuation on a received reply (exactly `clientStepP`'s)
  rcvT : ∀ {x} → RepP x → Rd
  rcvT (rpA h)    = dlvT l (dAnn h)
  rcvT (rpO q sz) = dlvT l (dOff q sz)
  rcvT (rpT q)    = dlvT l (dTxs q)
  rcvT (rpV vs)   = dlvT l (dVot vs)
  rcvT rpC        = Ret (inj₁ stIdle)

  -- the api delivery label of a delivery phase
  dlL : Dlv l → Lab l
  dlL (dAnn h)    = ap lo lnpRecvBlockAnnouncement h
  dlL (dOff q sz) = ap lo lnpRecvBlockOffer (q , sz)
  dlL (dTxs q)    = ap lo lnpRecvBlockTxsOffer q
  dlL (dVot vs)   = ap lo lnpRecvVotes vs

  -- where a client tree is (the flag marks a pending loop-back τ)
  data CPos : CPh × Bool → Tree → Set₁ where
    cpM : ∀ st → CPos (cPh st , false) (iter kc st)
    cp′ : ∀ st → CPos (cPh st , true) (iter-bind (Ret (inj₁ st)) kc)
    cpR : CPos (cSndRN , false) (iter-bind (snd l lo FromInitiator MsgLNPRequestNext stBusy) kc)
    cpS : CPos (cSndQ , false) (iter-bind (snd l lo FromInitiator MsgLNPQuit stQuit) kc)
    cpP : CPos (cSndPQ , false) (iter-bind (sendLNP l lo ! pQ ⟶ drainP l lo) kc)
    cpX : CPos (cDrain , false) (iter-bind (drainP l lo) kc)
    cpD : ∀ dv → CPos (cDlv dv , false) (iter-bind (dlvT l dv) kc)
    cpE : CPos (cEnd , false) (iter-bind (Ret (inj₂ tt)) kc)

  -- the client's abstract steps: one per table transition / api event, plus the pipelined
  -- quit (`cQp`, `cSP`) and the drain (`cDr`)
  data CSt : CPh × Bool → ALbl l → CPh × Bool → Set where
    cτ  : ∀ {c} → CSt (c , true) τ′ (c , false)
    cRN : ∀ u → CSt (cIdle , false) (ev′ (ap lo lnpSendRequestNext u)) (cSndRN , false)
    cQi : ∀ u → CSt (cIdle , false) (ev′ (ap lo lnpSendDone u)) (cSndQ , false)
    cSR : CSt (cSndRN , false) (ev′ (wS lo pRN)) (cBusy , true)
    cSQ : CSt (cSndQ , false) (ev′ (wS lo pQ)) (cQuit , true)
    cRc : ∀ {x} (k : RepP x) → CSt (cBusy , false) (ev′ (wR lo x)) (rcvTo k)
    cQp : ∀ u → CSt (cBusy , false) (ev′ (ap lo lnpSendDone u)) (cSndPQ , false)
    cSP : CSt (cSndPQ , false) (ev′ (wS lo pQ)) (cDrain , false)
    cDr : ∀ {x} → RepP x → CSt (cDrain , false) (ev′ (wR lo x)) (cQuit , true)
    cDl : ∀ dv → CSt (cDlv dv , false) (ev′ (dlL dv)) (cIdle , true)
    cDn : ∀ {tm md ln} → CSt (cQuit , false) (ev′ (wR lo (tm , md , ln , leiosNotifyP MsgLNPDone))) (cEnd , false)

  -- the client has terminated
  CFin : CPh × Bool → Set
  CFin (cEnd , _) = U.⊤
  CFin _          = ⊥

  -- the client's steps stay in its alphabet (wire cell and api at direction `lo`)
  cAlpha : ∀ {σ ω σ′} → CSt σ (ev′ ω) σ′ → CAl l ω
  cAlpha (cRN _)        = caA _ _
  cAlpha (cQi _)        = caA _ _
  cAlpha cSR            = caS _
  cAlpha cSQ            = caS _
  cAlpha (cRc _)        = caR _
  cAlpha (cQp _)        = caA _ _
  cAlpha cSP            = caS _
  cAlpha (cDr _)        = caR _
  cAlpha (cDl (dAnn _))   = caA _ _
  cAlpha (cDl (dOff _ _)) = caA _ _
  cAlpha (cDl (dTxs _))   = caA _ _
  cAlpha (cDl (dVot _))   = caA _ _
  cAlpha cDn            = caR _

  -- the client's τ-measure decreases
  cμτ : ∀ {σ σ′} → CSt σ τ′ σ′ → fl l (proj₂ σ′) < fl l (proj₂ σ)
  cμτ cτ = fl< l

  -- the pipelined StBusy round offers the reused StBusy menu or the pipelined quit
  data CBusyP : Event → Rd → Set₁ where
    cbOld  : ∀ {x t} → CBusyV l lo x t → CBusyP x t
    cbPipe : ∀ u → CBusyP ⌞ ap lo lnpSendDone u ⌟ (sendLNP l lo ! pQ ⟶ drainP l lo)

  -- the pipelined quit's inversion
  pqV : ∀ {at a t} → pipeQuit l lo at a ≡ just t → CBusyP (evLabel (proj₁ at) (proj₂ at) a) t
  pqV {at = _ , apiLPev l′ d′ m} eq with l′ ≟ l | d′ ≟ lo | m ≟ lnpSendDone
  ... | yes refl | yes refl | yes refl = subst (CBusyP _) (just-injective eq) (cbPipe _)
  ... | no _     | _        | _        with () ← eq
  ... | yes refl | no _     | _        with () ← eq
  ... | yes refl | yes refl | no _     with () ← eq
  pqV {at = _ , sendLNP _ _}    ()
  pqV {at = _ , receiveLNP _ _} ()
  pqV {at = _ , doneLNP _ _}    ()

  -- the pipelined StBusy round's offer, inverted
  cBusyP′ : ∀ {at a t} → orM (viewV (PTree.force (clientStepP l lo stBusy)) at a) (pipeQuit l lo at a) ≡ just t
          → CBusyP (evLabel (proj₁ at) (proj₂ at) a) t
  cBusyP′ {at} {a} br with viewV (PTree.force (clientStepP l lo stBusy)) at a in eq
  ... | just t₀ = subst (CBusyP _) (just-injective br) (cbOld (cBusyV (sVis refl eq)))
  ... | nothing = pqV br

  -- the pipelined StBusy round's inversion
  cBusyP : ∀ {x t} → kc stBusy ─[ ev (evl x) ]─► t → CBusyP x t
  cBusyP (sVis refl br) = cBusyP′ br

  -- a received reply, read off the reused StBusy view
  busyRep : ∀ {x t} → CBusyV l lo x t → Σ[ y ∈ Payload ] (RepP y × x ≡ ⌞ wR lo y ⌟)
  busyRep cbCan        = _ , rpC , refl
  busyRep (cbAnn h)    = _ , rpA h , refl
  busyRep (cbOff q sz) = _ , rpO q sz , refl
  busyRep (cbTxs q)    = _ , rpT q , refl
  busyRep (cbVote vs)  = _ , rpV vs , refl

  -- the drain menu's offer, inverted: a reply, discarded
  drainV′ : ∀ {at a} {t : Rd} → Maybe.map {B = Rd} (λ _ → Ret (inj₁ stQuit)) (viewV (PTree.force (clientStepP l lo stBusy)) at a) ≡ just t
          → Σ[ y ∈ Payload ] (RepP y × evLabel (proj₁ at) (proj₂ at) a ≡ ⌞ wR lo y ⌟ × t ≡ Ret (inj₁ stQuit))
  drainV′ {at} {a} br with viewV (PTree.force (clientStepP l lo stBusy)) at a in eq
  ... | just t₀ with busyRep (cBusyV (sVis refl eq))
  ...   | y , k , e = y , k , e , sym (just-injective br)
  drainV′ br | nothing with () ← br

  -- the drain menu's inversion
  drainV : ∀ {x t} → drainP l lo ─[ ev (evl x) ]─► t
         → Σ[ y ∈ Payload ] (RepP y × x ≡ ⌞ wR lo y ⌟ × t ≡ Ret (inj₁ stQuit))
  drainV (sVis refl br) = drainV′ br

  -- the client makes a τ only at a loop-back
  cElimτ : ∀ {σ t t′} → CPos σ t → t ─[ τ ]─► t′ → Σ[ σ′ ∈ _ ] (CSt σ τ′ σ′ × CPos σ′ t′)
  cElimτ (cpM stIdle) st = ⊥-elim (IterNoτ.τ✗ pchNoτ (λ ()) st)
  cElimτ (cpM stBusy) st = ⊥-elim (IterNoτ.τ✗ pchNoτ (λ ()) st)
  cElimτ (cpM stQuit) st = ⊥-elim (IterNoτ.τ✗ pchNoτ (λ ()) st)
  cElimτ (cp′ st) (sSil refl) = _ , cτ , cpM st
  cElimτ (cp′ _)  (sTau () _)
  cElimτ cpR st = ⊥-elim (IterNoτ.τ✗ outNoτ (λ ()) st)
  cElimτ cpS st = ⊥-elim (IterNoτ.τ✗ outNoτ (λ ()) st)
  cElimτ cpP st = ⊥-elim (IterNoτ.τ✗ outNoτ (λ ()) st)
  cElimτ cpX st = ⊥-elim (IterNoτ.τ✗ pchNoτ (λ ()) st)
  cElimτ (cpD (dAnn _))   st = ⊥-elim (IterNoτ.τ✗ outNoτ (λ ()) st)
  cElimτ (cpD (dOff _ _)) st = ⊥-elim (IterNoτ.τ✗ (outNoτ ⦃ DecEq-Offer ⦄) (λ ()) st)
  cElimτ (cpD (dTxs _))   st = ⊥-elim (IterNoτ.τ✗ (outNoτ ⦃ DecEq-EBPoint ⦄) (λ ()) st)
  cElimτ (cpD (dVot _))   st = ⊥-elim (IterNoτ.τ✗ (outNoτ ⦃ iV ⦄) (λ ()) st)
  cElimτ cpE (sSil ())
  cElimτ cpE (sTau () _)

  -- every visible client step is an abstract one
  cElimE : ∀ {σ t t′ e} → CPos σ t → t ─[ ev (evl e) ]─► t′
         → Σ[ ω ∈ Lab l ] Σ[ σ′ ∈ _ ] (e ≡ ⌞ ω ⌟ × CSt σ (ev′ ω) σ′ × CPos σ′ t′)
  cElimE (cpM stIdle) st with iter-ev-elim (kc stIdle) kc st
  ... | _ , st′ , refl with cIdleV st′
  ...   | ciNext u = _ , _ , refl , cRN u , cpR
  ...   | ciQuit u = _ , _ , refl , cQi u , cpS
  cElimE (cpM stBusy) st with iter-ev-elim (kc stBusy) kc st
  ... | _ , st′ , refl with cBusyP st′
  ...   | cbOld cbCan        = _ , _ , refl , cRc rpC , cp′ stIdle
  ...   | cbOld (cbAnn h)    = _ , _ , refl , cRc (rpA h) , cpD (dAnn h)
  ...   | cbOld (cbOff q sz) = _ , _ , refl , cRc (rpO q sz) , cpD (dOff q sz)
  ...   | cbOld (cbTxs q)    = _ , _ , refl , cRc (rpT q) , cpD (dTxs q)
  ...   | cbOld (cbVote vs)  = _ , _ , refl , cRc (rpV vs) , cpD (dVot vs)
  ...   | cbPipe u           = _ , _ , refl , cQp u , cpP
  cElimE (cpM stQuit) st with iter-ev-elim (kc stQuit) kc st
  ... | _ , st′ , refl with cQuitV st′
  ...   | cqDone = _ , _ , refl , cDn , cpE
  cElimE (cp′ _) (sVis () _)
  cElimE cpR st with iter-ev-elim (snd l lo FromInitiator MsgLNPRequestNext stBusy) kc st
  ... | _ , st′ , refl with outI st′
  ...   | refl , refl = _ , _ , refl , cSR , cp′ stBusy
  cElimE cpS st with iter-ev-elim (snd l lo FromInitiator MsgLNPQuit stQuit) kc st
  ... | _ , st′ , refl with outI st′
  ...   | refl , refl = _ , _ , refl , cSQ , cp′ stQuit
  cElimE cpP st with iter-ev-elim (sendLNP l lo ! pQ ⟶ drainP l lo) kc st
  ... | _ , st′ , refl with outI st′
  ...   | refl , refl = _ , _ , refl , cSP , cpX
  cElimE cpX st with iter-ev-elim (drainP l lo) kc st
  ... | _ , st′ , refl with drainV st′
  ...   | _ , k , refl , refl = _ , _ , refl , cDr k , cp′ stQuit
  cElimE (cpD (dAnn h)) st with iter-ev-elim (dlvT l (dAnn h)) kc st
  ... | _ , st′ , refl with outI st′
  ...   | refl , refl = _ , _ , refl , cDl (dAnn h) , cp′ stIdle
  cElimE (cpD (dOff q sz)) st with iter-ev-elim (dlvT l (dOff q sz)) kc st
  ... | _ , st′ , refl with outI ⦃ DecEq-Offer ⦄ st′
  ...   | refl , refl = _ , _ , refl , cDl (dOff q sz) , cp′ stIdle
  cElimE (cpD (dTxs q)) st with iter-ev-elim (dlvT l (dTxs q)) kc st
  ... | _ , st′ , refl with outI ⦃ DecEq-EBPoint ⦄ st′
  ...   | refl , refl = _ , _ , refl , cDl (dTxs q) , cp′ stIdle
  cElimE (cpD (dVot vs)) st with iter-ev-elim (dlvT l (dVot vs)) kc st
  ... | _ , st′ , refl with outI ⦃ iV ⦄ st′
  ...   | refl , refl = _ , _ , refl , cDl (dVot vs) , cp′ stIdle
  cElimE cpE (sVis () _)

  -- a client tree returns only at the end
  cElimR : ∀ {σ t r} → CPos σ t → PTree.force t ≡ ret r → CFin σ
  cElimR cpE _ = U.tt
  cElimR (cpM stIdle) ()
  cElimR (cpM stBusy) ()
  cElimR (cpM stQuit) ()
  cElimR (cp′ _) ()
  cElimR cpR ()
  cElimR cpS ()
  cElimR cpP ()
  cElimR cpX ()
  cElimR (cpD (dAnn _))   ()
  cElimR (cpD (dOff _ _)) ()
  cElimR (cpD (dTxs _))   ()
  cElimR (cpD (dVot _))   ()

  -- the client abstraction
  CA : Abs l (CPh × Bool)
  CA = record { Pos = CPos ; Stp = CSt ; Fin = CFin ; Alpha = CAl l ; alpha = cAlpha
              ; μ = λ σ → fl l (proj₂ σ) ; μτ = cμτ
              ; elimτ = cElimτ ; elimE = cElimE ; elimR = cElimR }

  -- the reused StBusy menu offers every reply, with `clientStepP`'s continuation
  repOff : ∀ {x} (k : RepP x) → vOf (clientStepP l lo stBusy) (_ , receiveLNP l lo) x ≡ just (rcvT k)
  repOff (rpA _)   rewrite ≟-refl l = refl
  repOff (rpO _ _) rewrite ≟-refl l = refl
  repOff (rpT _)   rewrite ≟-refl l = refl
  repOff (rpV _)   rewrite ≟-refl l = refl
  repOff rpC       rewrite ≟-refl l = refl

  -- an offer of the reused StBusy menu is an offer of the pipelined StBusy round
  busyOff : ∀ {at a t} → viewV (PTree.force (clientStepP l lo stBusy)) at a ≡ just t
          → orM (viewV (PTree.force (clientStepP l lo stBusy)) at a) (pipeQuit l lo at a) ≡ just t
  busyOff eq rewrite eq = refl

  -- the position after a received reply
  rcvPos : ∀ {x} (k : RepP x) → CPos (rcvTo k) (iter-bind (rcvT k) kc)
  rcvPos (rpA h)    = cpD (dAnn h)
  rcvPos (rpO q sz) = cpD (dOff q sz)
  rcvPos (rpT q)    = cpD (dTxs q)
  rcvPos (rpV vs)   = cpD (dVot vs)
  rcvPos rpC        = cp′ stIdle

  -- every abstract client τ is a concrete one
  cIntroτ : ∀ {σ σ′ t} → CPos σ t → CSt σ τ′ σ′ → Σ[ t′ ∈ Tree ] (t ─[ τ ]─► t′ × CPos σ′ t′)
  cIntroτ (cp′ st) cτ = _ , sSil refl , cpM st

  -- every abstract visible client step is a concrete one
  cIntroE : ∀ {σ σ′ t ω} → CPos σ t → CSt σ (ev′ ω) σ′
          → Σ[ t′ ∈ Tree ] (t ─[ ev (evl ⌞ ω ⌟) ]─► t′ × CPos σ′ t′)
  cIntroE (cpM stIdle) (cRN u) = _ , iterE (pchS e) , cpR
    where
    -- the idle menu offers RequestNext
    e : vOf (kc stIdle) (_ , apiLPev l lo lnpSendRequestNext) u ≡ just (snd l lo FromInitiator MsgLNPRequestNext stBusy)
    e rewrite ≟-refl l = refl
  cIntroE (cpM stIdle) (cQi u) = _ , iterE (pchS e) , cpS
    where
    -- the idle menu offers the quit
    e : vOf (kc stIdle) (_ , apiLPev l lo lnpSendDone) u ≡ just (snd l lo FromInitiator MsgLNPQuit stQuit)
    e rewrite ≟-refl l = refl
  cIntroE (cpM stBusy) (cRc {x} k) = _ , iterE (pchS (busyOff {at = _ , receiveLNP l lo} {a = x} (repOff k))) , rcvPos k
  cIntroE (cpM stBusy) (cQp u) = _ , iterE (pchS e) , cpP
    where
    -- the busy round offers the pipelined quit
    e : orM (viewV (PTree.force (clientStepP l lo stBusy)) (_ , apiLPev l lo lnpSendDone) u)
            (pipeQuit l lo (_ , apiLPev l lo lnpSendDone) u)
        ≡ just (sendLNP l lo ! pQ ⟶ drainP l lo)
    e rewrite ≟-refl l = refl
  cIntroE (cpM stQuit) (cDn {tm} {md} {ln}) = _ , iterE (pchS e) , cpE
    where
    -- the quit menu accepts MsgDone
    e : vOf (kc stQuit) (_ , receiveLNP l lo) (tm , md , ln , leiosNotifyP MsgLNPDone) ≡ just (Ret (inj₂ tt))
    e rewrite ≟-refl l = refl
  cIntroE cpR cSR = _ , iterE (outS (sendLNP l lo) _ _) , cp′ stBusy
  cIntroE cpS cSQ = _ , iterE (outS (sendLNP l lo) _ _) , cp′ stQuit
  cIntroE cpP cSP = _ , iterE (outS (sendLNP l lo) _ _) , cpX
  cIntroE cpX (cDr k) = _ , iterE (pchS (cong (Maybe.map (λ _ → Ret (inj₁ stQuit))) (repOff k))) , cp′ stQuit
  cIntroE (cpD (dAnn h))    (cDl _) = _ , iterE (outS (apiLPev l lo lnpRecvBlockAnnouncement) _ _) , cp′ stIdle
  cIntroE (cpD (dOff q sz)) (cDl _) = _ , iterE (outS ⦃ DecEq-Offer ⦄ (apiLPev l lo lnpRecvBlockOffer) _ _) , cp′ stIdle
  cIntroE (cpD (dTxs q))    (cDl _) = _ , iterE (outS ⦃ DecEq-EBPoint ⦄ (apiLPev l lo lnpRecvBlockTxsOffer) _ _) , cp′ stIdle
  cIntroE (cpD (dVot vs))   (cDl _) = _ , iterE (outS ⦃ iV ⦄ (apiLPev l lo lnpRecvVotes) _ _) , cp′ stIdle

  -- the terminated client has returned
  cIntroR : ∀ {σ t} → CPos σ t → CFin σ → PTree.force t ≡ ret tt
  cIntroR cpE _ = refl
  cIntroR (cpM stIdle) ()
  cIntroR (cpM stBusy) ()
  cIntroR (cpM stQuit) ()
  cIntroR (cp′ stIdle) ()
  cIntroR (cp′ stBusy) ()
  cIntroR (cp′ stQuit) ()

  -- the client's intro facts
  CI : AbsI l CA
  CI = record { introτ = cIntroτ ; introE = cIntroE ; introR = cIntroR }

  ------------------------------------------------------------------------
  -- §2  The read-ahead server's abstraction
  ------------------------------------------------------------------------

  -- the server's loop body, at `(l , hi)` (NOT renamed: the FIFOs translate the channels)
  ks : LNPState → Rd
  ks = psStep l hi

  -- the server's phases: its three loop menus, a committed api reply, the committed
  -- read-ahead MsgCanceled, the committed MsgDone, the end
  data SPh : Set where
    sIdle sBusy sQuit sCanc sDone sEnd : SPh
    sRep : Rep l → SPh

  -- the phase of a loop state
  sPh : LNPState → SPh
  sPh stIdle = sIdle
  sPh stBusy = sBusy
  sPh stQuit = sQuit

  -- the api tag of a reply command
  rTag : Rep l → ApiLPTag
  rTag (rA _)   = lnpSendBlockAnnouncement
  rTag (rO _ _) = lnpSendBlockOffer
  rTag (rT _)   = lnpSendBlockTxsOffer
  rTag (rV _)   = lnpSendVotes
  rTag rC       = lnpSendCanceled

  -- … its carrier
  rCar : (r : Rep l) → ApiLPCar (rTag r)
  rCar (rA h)    = h
  rCar (rO q sz) = q , sz
  rCar (rT q)    = q
  rCar (rV vs)   = vs
  rCar rC        = U.tt

  -- the server application's reply command, as a label
  apL : Rep l → Lab l
  apL r = ap hi (rTag r) (rCar r)

  -- every reply command is a server api send
  srvTag : ∀ r → T (srvCmd l (rTag r))
  srvTag (rA _)   = U.tt
  srvTag (rO _ _) = U.tt
  srvTag (rT _)   = U.tt
  srvTag (rV _)   = U.tt
  srvTag rC       = U.tt

  -- the reply the server sends for a command is a reply payload
  repP : ∀ r → RepP (pay l FromResponder (repM l r))
  repP (rA h)    = rpA h
  repP (rO q sz) = rpO q sz
  repP (rT q)    = rpT q
  repP (rV vs)   = rpV vs
  repP rC        = rpC

  -- where a server tree is
  data SPos : SPh × Bool → Tree → Set₁ where
    spM : ∀ st → SPos (sPh st , false) (iter ks st)
    sp′ : ∀ st → SPos (sPh st , true) (iter-bind (Ret (inj₁ st)) ks)
    spN : ∀ r → SPos (sRep r , false) (iter-bind (snd l hi FromResponder (repM l r) stIdle) ks)
    spC : SPos (sCanc , false) (iter-bind (snd l hi FromResponder MsgLNPCanceled stQuit) ks)
    spD : SPos (sDone , false) (iter-bind (sendLNP l hi ! pD ⟶ Ret (inj₂ tt)) ks)
    spE : SPos (sEnd , false) (iter-bind (Ret (inj₂ tt)) ks)

  -- the server's abstract steps (its own cell `(l , hi)`: receives `wR hi`, sends `wS hi`)
  data SSt : SPh × Bool → ALbl l → SPh × Bool → Set where
    sτ  : ∀ {s} → SSt (s , true) τ′ (s , false)
    sRN : ∀ {tm md ln} → SSt (sIdle , false) (ev′ (wR hi (tm , md , ln , leiosNotifyP MsgLNPRequestNext))) (sBusy , true)
    sQi : ∀ {tm md ln} → SSt (sIdle , false) (ev′ (wR hi (tm , md , ln , leiosNotifyP MsgLNPQuit))) (sQuit , true)
    sAp : ∀ r → SSt (sBusy , false) (ev′ (apL r)) (sRep r , false)
    sRA : ∀ {tm md ln} → SSt (sBusy , false) (ev′ (wR hi (tm , md , ln , leiosNotifyP MsgLNPQuit))) (sCanc , false)
    sNx : ∀ r → SSt (sRep r , false) (ev′ (wS hi (pay l FromResponder (repM l r)))) (sIdle , true)
    sCx : SSt (sCanc , false) (ev′ (wS hi pC)) (sQuit , true)
    sDn : SSt (sQuit , false) (ev′ (dn hi)) (sDone , false)
    sDS : SSt (sDone , false) (ev′ (wS hi pD)) (sEnd , false)

  -- the server has terminated
  SFin : SPh × Bool → Set
  SFin (sEnd , _) = U.⊤
  SFin _          = ⊥

  -- the server's alphabet: its own wire cell, api and done, at direction `hi`
  data SAl : Lab l → Set where
    saS : ∀ x   → SAl (wS hi x)
    saR : ∀ x   → SAl (wR hi x)
    saA : ∀ m v → SAl (ap hi m v)
    saD :         SAl (dn hi)

  -- the server's steps stay in its alphabet
  sAlpha : ∀ {σ ω σ′} → SSt σ (ev′ ω) σ′ → SAl ω
  sAlpha sRN     = saR _
  sAlpha sQi     = saR _
  sAlpha (sAp _) = saA _ _
  sAlpha sRA     = saR _
  sAlpha (sNx _) = saS _
  sAlpha sCx     = saS _
  sAlpha sDn     = saD
  sAlpha sDS     = saS _

  -- the server's τ-measure decreases
  sμτ : ∀ {σ σ′} → SSt σ τ′ σ′ → fl l (proj₂ σ′) < fl l (proj₂ σ)
  sμτ sτ = fl< l

  -- the read-ahead server's StBusy round offers the reused StBusy menu or the read-ahead
  data SBusyP : Event → Rd → Set₁ where
    sbOld : ∀ {x t} → SBusyV l hi x t → SBusyP x t
    sbRA  : ∀ {tm md ln} → SBusyP ⌞ wR hi (tm , md , ln , leiosNotifyP MsgLNPQuit) ⌟
                                  (snd l hi FromResponder MsgLNPCanceled stQuit)

  -- the read-ahead's inversion
  raV : ∀ {at a t} → readAhead l hi at a ≡ just t → SBusyP (evLabel (proj₁ at) (proj₂ at) a) t
  raV {at = _ , receiveLNP l′ d′} {a = _ , _ , _ , msg} eq with l′ ≟ l | d′ ≟ hi | msg ≟ leiosNotifyP MsgLNPQuit
  ... | yes refl | yes refl | yes refl = subst (SBusyP _) (just-injective eq) sbRA
  ... | no _     | _        | _        with () ← eq
  ... | yes refl | no _     | _        with () ← eq
  ... | yes refl | yes refl | no _     with () ← eq
  raV {at = _ , sendLNP _ _}   ()
  raV {at = _ , apiLPev _ _ _} ()
  raV {at = _ , doneLNP _ _}   ()

  -- the read-ahead server's StBusy round's offer, inverted
  sBusyP′ : ∀ {at a t} → orM (viewV (PTree.force (serverStepP l hi stBusy)) at a) (readAhead l hi at a) ≡ just t
          → SBusyP (evLabel (proj₁ at) (proj₂ at) a) t
  sBusyP′ {at} {a} br with viewV (PTree.force (serverStepP l hi stBusy)) at a in eq
  ... | just t₀ = subst (SBusyP _) (just-injective br) (sbOld (sBusyV (sVis refl eq)))
  ... | nothing = raV br

  -- the read-ahead server's StBusy round's inversion
  sBusyP : ∀ {x t} → ks stBusy ─[ ev (evl x) ]─► t → SBusyP x t
  sBusyP (sVis refl br) = sBusyP′ br

  -- the server makes a τ only at a loop-back
  sElimτ : ∀ {σ t t′} → SPos σ t → t ─[ τ ]─► t′ → Σ[ σ′ ∈ _ ] (SSt σ τ′ σ′ × SPos σ′ t′)
  sElimτ (spM stIdle) st = ⊥-elim (IterNoτ.τ✗ pchNoτ (λ ()) st)
  sElimτ (spM stBusy) st = ⊥-elim (IterNoτ.τ✗ pchNoτ (λ ()) st)
  sElimτ (spM stQuit) st = ⊥-elim (IterNoτ.τ✗ pchNoτ (λ ()) st)
  sElimτ (sp′ st) (sSil refl) = _ , sτ , spM st
  sElimτ (sp′ _)  (sTau () _)
  sElimτ (spN _) st = ⊥-elim (IterNoτ.τ✗ outNoτ (λ ()) st)
  sElimτ spC st = ⊥-elim (IterNoτ.τ✗ outNoτ (λ ()) st)
  sElimτ spD st = ⊥-elim (IterNoτ.τ✗ outNoτ (λ ()) st)
  sElimτ spE (sSil ())
  sElimτ spE (sTau () _)

  -- every visible server step is an abstract one
  sElimE : ∀ {σ t t′ e} → SPos σ t → t ─[ ev (evl e) ]─► t′
         → Σ[ ω ∈ Lab l ] Σ[ σ′ ∈ _ ] (e ≡ ⌞ ω ⌟ × SSt σ (ev′ ω) σ′ × SPos σ′ t′)
  sElimE (spM stIdle) st with iter-ev-elim (ks stIdle) ks st
  ... | _ , st′ , refl with sIdleV st′
  ...   | siNext = _ , _ , refl , sRN , sp′ stBusy
  ...   | siQuit = _ , _ , refl , sQi , sp′ stQuit
  sElimE (spM stBusy) st with iter-ev-elim (ks stBusy) ks st
  ... | _ , st′ , refl with sBusyP st′
  ...   | sbOld (sbCan u)    = _ , _ , refl , sAp rC , spN rC
  ...   | sbOld (sbAnn h)    = _ , _ , refl , sAp (rA h) , spN (rA h)
  ...   | sbOld (sbOff q sz) = _ , _ , refl , sAp (rO q sz) , spN (rO q sz)
  ...   | sbOld (sbTxs q)    = _ , _ , refl , sAp (rT q) , spN (rT q)
  ...   | sbOld (sbVote vs)  = _ , _ , refl , sAp (rV vs) , spN (rV vs)
  ...   | sbRA               = _ , _ , refl , sRA , spC
  sElimE (spM stQuit) st with iter-ev-elim (ks stQuit) ks st
  ... | _ , st′ , refl with sQuitV st′
  ...   | sqDone _ = _ , _ , refl , sDn , spD
  sElimE (sp′ _) (sVis () _)
  sElimE (spN r) st with iter-ev-elim (snd l hi FromResponder (repM l r) stIdle) ks st
  ... | _ , st′ , refl with outI st′
  ...   | refl , refl = _ , _ , refl , sNx r , sp′ stIdle
  sElimE spC st with iter-ev-elim (snd l hi FromResponder MsgLNPCanceled stQuit) ks st
  ... | _ , st′ , refl with outI st′
  ...   | refl , refl = _ , _ , refl , sCx , sp′ stQuit
  sElimE spD st with iter-ev-elim (sendLNP l hi ! pD ⟶ Ret (inj₂ tt)) ks st
  ... | _ , st′ , refl with outI st′
  ...   | refl , refl = _ , _ , refl , sDS , spE
  sElimE spE (sVis () _)

  -- a server tree returns only at the end
  sElimR : ∀ {σ t r} → SPos σ t → PTree.force t ≡ ret r → SFin σ
  sElimR spE _ = U.tt
  sElimR (spM stIdle) ()
  sElimR (spM stBusy) ()
  sElimR (spM stQuit) ()
  sElimR (sp′ _) ()
  sElimR (spN _) ()
  sElimR spC ()
  sElimR spD ()

  -- the server abstraction
  SA : Abs l (SPh × Bool)
  SA = record { Pos = SPos ; Stp = SSt ; Fin = SFin ; Alpha = SAl ; alpha = sAlpha
              ; μ = λ σ → fl l (proj₂ σ) ; μτ = sμτ
              ; elimτ = sElimτ ; elimE = sElimE ; elimR = sElimR }

  -- an offer of the reused server StBusy menu is an offer of the read-ahead StBusy round
  sbusyOff : ∀ {at a t} → viewV (PTree.force (serverStepP l hi stBusy)) at a ≡ just t
           → orM (viewV (PTree.force (serverStepP l hi stBusy)) at a) (readAhead l hi at a) ≡ just t
  sbusyOff eq rewrite eq = refl

  -- the reused server StBusy menu takes every reply command
  cmdOff : ∀ r → vOf (serverStepP l hi stBusy) (_ , apiLPev l hi (rTag r)) (rCar r)
               ≡ just (snd l hi FromResponder (repM l r) stIdle)
  cmdOff (rA _)   rewrite ≟-refl l = refl
  cmdOff (rO _ _) rewrite ≟-refl l = refl
  cmdOff (rT _)   rewrite ≟-refl l = refl
  cmdOff (rV _)   rewrite ≟-refl l = refl
  cmdOff rC       rewrite ≟-refl l = refl

  -- every abstract server τ is a concrete one
  sIntroτ : ∀ {σ σ′ t} → SPos σ t → SSt σ τ′ σ′ → Σ[ t′ ∈ Tree ] (t ─[ τ ]─► t′ × SPos σ′ t′)
  sIntroτ (sp′ st) sτ = _ , sSil refl , spM st

  -- every abstract visible server step is a concrete one
  sIntroE : ∀ {σ σ′ t ω} → SPos σ t → SSt σ (ev′ ω) σ′
          → Σ[ t′ ∈ Tree ] (t ─[ ev (evl ⌞ ω ⌟) ]─► t′ × SPos σ′ t′)
  sIntroE (spM stIdle) (sRN {tm} {md} {ln}) = _ , iterE (pchS e) , sp′ stBusy
    where
    -- the idle menu accepts RequestNext
    e : vOf (ks stIdle) (_ , receiveLNP l hi) (tm , md , ln , leiosNotifyP MsgLNPRequestNext) ≡ just (Ret (inj₁ stBusy))
    e rewrite ≟-refl l = refl
  sIntroE (spM stIdle) (sQi {tm} {md} {ln}) = _ , iterE (pchS e) , sp′ stQuit
    where
    -- the idle menu accepts MsgQuit
    e : vOf (ks stIdle) (_ , receiveLNP l hi) (tm , md , ln , leiosNotifyP MsgLNPQuit) ≡ just (Ret (inj₁ stQuit))
    e rewrite ≟-refl l = refl
  sIntroE (spM stBusy) (sAp r) = _ , iterE (pchS (sbusyOff {at = _ , apiLPev l hi (rTag r)} {a = rCar r} (cmdOff r))) , spN r
  sIntroE (spM stBusy) (sRA {tm} {md} {ln}) = _ , iterE (pchS e) , spC
    where
    -- the busy round reads MsgQuit ahead
    e : orM (viewV (PTree.force (serverStepP l hi stBusy)) (_ , receiveLNP l hi) (tm , md , ln , leiosNotifyP MsgLNPQuit))
            (readAhead l hi (_ , receiveLNP l hi) (tm , md , ln , leiosNotifyP MsgLNPQuit))
        ≡ just (snd l hi FromResponder MsgLNPCanceled stQuit)
    e rewrite ≟-refl l = refl
  sIntroE (spM stQuit) sDn = _ , iterE (pchS e) , spD
    where
    -- the quit menu offers the peer-local done
    e : vOf (ks stQuit) (_ , doneLNP l hi) U.tt ≡ just (sendLNP l hi ! pD ⟶ Ret (inj₂ tt))
    e rewrite ≟-refl l = refl
  sIntroE (spN r) (sNx _) = _ , iterE (outS (sendLNP l hi) _ _) , sp′ stIdle
  sIntroE spC sCx = _ , iterE (outS (sendLNP l hi) _ _) , sp′ stQuit
  sIntroE spD sDS = _ , iterE (outS (sendLNP l hi) _ _) , spE

  -- the terminated server has returned
  sIntroR : ∀ {σ t} → SPos σ t → SFin σ → PTree.force t ≡ ret tt
  sIntroR spE _ = refl
  sIntroR (spM stIdle) ()
  sIntroR (spM stBusy) ()
  sIntroR (spM stQuit) ()
  sIntroR (sp′ stIdle) ()
  sIntroR (sp′ stBusy) ()
  sIntroR (sp′ stQuit) ()

  -- the server's intro facts
  SI : AbsI l SA
  SI = record { introτ = sIntroτ ; introE = sIntroE ; introR = sIntroR }

  ------------------------------------------------------------------------
  -- §3  The FIFOs' abstraction
  ------------------------------------------------------------------------

  -- a FIFO's phase: its contents, or closed
  data BPh : Set where
    bq   : BSt → BPh
    bEnd : BPh

  -- the phase after a delivery: closed if it was the last message, else empty (loop-back)
  aOut : Bool → BPh × Bool
  aOut true  = bEnd , false
  aOut false = bq β0 , true

  -- one FIFO, from `(l , i)`'s sends to `(l , o)`'s receives
  module Fifo (i o : Dir) where

    -- its loop body
    kf : BSt → Bd
    kf = fifoStep l i o

    -- where a FIFO tree is
    data FPos : BPh × Bool → Tree → Set₁ where
      fpM : ∀ b → FPos (bq b , false) (iter kf b)
      fp′ : ∀ b → FPos (bq b , true) (iter-bind (Ret (inj₁ b)) kf)
      fpE : FPos (bEnd , false) (iter-bind (Ret (inj₂ tt)) kf)

    -- the position after a delivery
    posAfter : ∀ c → FPos (aOut c) (iter-bind (Ret (afterB c)) kf)
    posAfter true  = fpE
    posAfter false = fp′ β0

    -- its abstract steps: inputs while there is room, outputs of the head
    data FSt : BPh × Bool → ALbl l → BPh × Bool → Set where
      fτ  : ∀ {b} → FSt (b , true) τ′ (b , false)
      fI0 : ∀ x   → FSt (bq β0 , false) (ev′ (wS i x)) (bq (β1 x) , true)
      fI1 : ∀ x y → FSt (bq (β1 x) , false) (ev′ (wS i y)) (bq (β2 x y) , true)
      fO1 : ∀ x   → FSt (bq (β1 x) , false) (ev′ (wR o x)) (aOut (isLast x))
      fO2 : ∀ x y → FSt (bq (β2 x y) , false) (ev′ (wR o x)) (bq (β1 y) , true)

    -- the FIFO has closed
    FFin : BPh × Bool → Set
    FFin (bEnd , _) = U.⊤
    FFin _          = ⊥

    -- its alphabet: the sender's sends and the receiver's receives
    data FAl : Lab l → Set where
      faI : ∀ x → FAl (wS i x)
      faO : ∀ x → FAl (wR o x)

    -- its steps stay in its alphabet
    fAlpha : ∀ {σ ω σ′} → FSt σ (ev′ ω) σ′ → FAl ω
    fAlpha (fI0 _)   = faI _
    fAlpha (fI1 _ _) = faI _
    fAlpha (fO1 _)   = faO _
    fAlpha (fO2 _ _) = faO _

    -- its τ-measure decreases
    fμτ : ∀ {σ σ′} → FSt σ τ′ σ′ → fl l (proj₂ σ′) < fl l (proj₂ σ)
    fμτ fτ = fl< l

    -- what a FIFO round offers: an input or an output
    data FV (b : BSt) : Event → Bd → Set₁ where
      fvI : ∀ {x t} → inB b x ≡ just t → FV b (evLabel _ (sendLNP l i) x) t
      fvO : ∀ {y t} → outB b y ≡ just t → FV b (evLabel _ (receiveLNP l o) y) t

    -- a FIFO round's offer, inverted
    fifoV′ : ∀ {b at a t} → fifoV l i o b at a ≡ just t → FV b (evLabel (proj₁ at) (proj₂ at) a) t
    fifoV′ {at = _ , sendLNP l′ d′} eq with l′ ≟ l | d′ ≟ i
    ... | yes refl | yes refl = fvI eq
    ... | no _     | _        with () ← eq
    ... | yes refl | no _     with () ← eq
    fifoV′ {at = _ , receiveLNP l′ d′} eq with l′ ≟ l | d′ ≟ o
    ... | yes refl | yes refl = fvO eq
    ... | no _     | _        with () ← eq
    ... | yes refl | no _     with () ← eq
    fifoV′ {at = _ , apiLPev _ _ _} ()
    fifoV′ {at = _ , doneLNP _ _}   ()

    -- a FIFO round's inversion
    fifoVw : ∀ {b x t} → kf b ─[ ev (evl x) ]─► t → FV b x t
    fifoVw (sVis refl br) = fifoV′ br

    -- an output from one message is that message
    out1 : ∀ {x y t} → outB (β1 x) y ≡ just t → y ≡ x × t ≡ Ret (afterB (isLast x))
    out1 {x} {y} eq with y ≟ x
    ... | yes e = e , sym (just-injective eq)
    ... | no _  with () ← eq

    -- (two messages)
    out2 : ∀ {x z y t} → outB (β2 x z) y ≡ just t → y ≡ x × t ≡ Ret (inj₁ (β1 z))
    out2 {x} {z} {y} eq with y ≟ x
    ... | yes e = e , sym (just-injective eq)
    ... | no _  with () ← eq

    -- a FIFO makes a τ only at a loop-back
    fElimτ : ∀ {σ t t′} → FPos σ t → t ─[ τ ]─► t′ → Σ[ σ′ ∈ _ ] (FSt σ τ′ σ′ × FPos σ′ t′)
    fElimτ (fpM b) st = ⊥-elim (IterNoτ.τ✗ pchNoτ (λ ()) st)
    fElimτ (fp′ b) (sSil refl) = _ , fτ , fpM b
    fElimτ (fp′ _) (sTau () _)
    fElimτ fpE (sSil ())
    fElimτ fpE (sTau () _)

    -- every visible FIFO step is an abstract one
    fElimE : ∀ {σ t t′ e} → FPos σ t → t ─[ ev (evl e) ]─► t′
           → Σ[ ω ∈ Lab l ] Σ[ σ′ ∈ _ ] (e ≡ ⌞ ω ⌟ × FSt σ (ev′ ω) σ′ × FPos σ′ t′)
    fElimE (fpM b) st with iter-ev-elim (kf b) kf st
    ... | _ , st′ , refl with b | fifoVw st′
    ...   | β0       | fvI refl = _ , _ , refl , fI0 _ , fp′ _
    ...   | β0       | fvO ()
    ...   | β1 x     | fvI refl = _ , _ , refl , fI1 x _ , fp′ _
    ...   | β1 x     | fvO eq with out1 eq
    ...     | refl , refl = _ , _ , refl , fO1 x , posAfter (isLast x)
    fElimE (fpM b) st | _ , st′ , refl | β2 _ _   | fvI ()
    fElimE (fpM b) st | _ , st′ , refl | β2 x z   | fvO eq with out2 eq
    ...     | refl , refl = _ , _ , refl , fO2 x z , fp′ _
    fElimE (fp′ _) (sVis () _)
    fElimE fpE (sVis () _)

    -- a FIFO returns only when closed
    fElimR : ∀ {σ t r} → FPos σ t → PTree.force t ≡ ret r → FFin σ
    fElimR fpE _ = U.tt
    fElimR (fpM β0) ()
    fElimR (fpM (β1 _)) ()
    fElimR (fpM (β2 _ _)) ()
    fElimR (fp′ _) ()

    -- the FIFO abstraction
    FA : Abs l (BPh × Bool)
    FA = record { Pos = FPos ; Stp = FSt ; Fin = FFin ; Alpha = FAl ; alpha = fAlpha
                ; μ = λ σ → fl l (proj₂ σ) ; μτ = fμτ
                ; elimτ = fElimτ ; elimE = fElimE ; elimR = fElimR }

    -- every abstract FIFO τ is a concrete one
    fIntroτ : ∀ {σ σ′ t} → FPos σ t → FSt σ τ′ σ′ → Σ[ t′ ∈ Tree ] (t ─[ τ ]─► t′ × FPos σ′ t′)
    fIntroτ (fp′ b) fτ = _ , sSil refl , fpM b

    -- every abstract visible FIFO step is a concrete one
    fIntroE : ∀ {σ σ′ t ω} → FPos σ t → FSt σ (ev′ ω) σ′
            → Σ[ t′ ∈ Tree ] (t ─[ ev (evl ⌞ ω ⌟) ]─► t′ × FPos σ′ t′)
    fIntroE (fpM β0) (fI0 x) = _ , iterE (pchS e) , fp′ (β1 x)
      where
      -- the empty FIFO takes an input
      e : vOf (kf β0) (_ , sendLNP l i) x ≡ just (Ret (inj₁ (β1 x)))
      e rewrite ≟-refl l | ≟-refl i = refl
    fIntroE (fpM (β1 x)) (fI1 _ y) = _ , iterE (pchS e) , fp′ (β2 x y)
      where
      -- a one-message FIFO takes an input
      e : vOf (kf (β1 x)) (_ , sendLNP l i) y ≡ just (Ret (inj₁ (β2 x y)))
      e rewrite ≟-refl l | ≟-refl i = refl
    fIntroE (fpM (β1 x)) (fO1 _) = _ , iterE (pchS e) , posAfter (isLast x)
      where
      -- a one-message FIFO delivers it
      e : vOf (kf (β1 x)) (_ , receiveLNP l o) x ≡ just (Ret (afterB (isLast x)))
      e rewrite ≟-refl l | ≟-refl o | ≟-refl x = refl
    fIntroE (fpM (β2 x y)) (fO2 _ _) = _ , iterE (pchS e) , fp′ (β1 y)
      where
      -- a two-message FIFO delivers its head
      e : vOf (kf (β2 x y)) (_ , receiveLNP l o) x ≡ just (Ret (inj₁ (β1 y)))
      e rewrite ≟-refl l | ≟-refl o | ≟-refl x = refl

    -- the closed FIFO has returned
    fIntroR : ∀ {σ t} → FPos σ t → FFin σ → PTree.force t ≡ ret tt
    fIntroR fpE _ = refl

    -- the FIFO's intro facts
    FI : AbsI l FA
    FI = record { introτ = fIntroτ ; introE = fIntroE ; introR = fIntroR }

  -- the client→server FIFO and the server→client FIFO
  module F₁ = Fifo lo hi
  -- (server→client)
  module F₂ = Fifo hi lo

  ------------------------------------------------------------------------
  -- §4  The system's abstraction
  ------------------------------------------------------------------------

  -- the peers' alphabets are disjoint
  disjP : ∀ {ω} → CAl l ω → SAl ω → ¬ InE l ∅ES ω → ⊥
  disjP (caS _)   ()
  disjP (caR _)   ()
  disjP (caA _ _) ()

  -- the FIFOs' alphabets are disjoint
  disjF : ∀ {ω} → F₁.FAl ω → F₂.FAl ω → ¬ InE l ∅ES ω → ⊥
  disjF (F₁.faI _) ()
  disjF (F₁.faO _) ()

  -- the FIFOs' events are all wire events
  chW : ∀ {ω} → F₁.FAl ω ⊎ F₂.FAl ω → InE l (wireES l) ω
  chW (inj₁ (F₁.faI _)) = U.tt
  chW (inj₁ (F₁.faO _)) = U.tt
  chW (inj₂ (F₂.faI _)) = U.tt
  chW (inj₂ (F₂.faO _)) = U.tt

  -- the peers and the FIFOs share only wire events
  disjT : ∀ {ω} → CAl l ω ⊎ SAl ω → F₁.FAl ω ⊎ F₂.FAl ω → ¬ InE l (wireES l) ω → ⊥
  disjT _ b ¬w = ¬w (chW b)

  -- the peers (interleaved)
  module PP = Prod l CA SA ∅ES disjP
  -- the FIFOs (interleaved)
  module PB = Prod l F₁.FA F₂.FA ∅ES disjF
  -- the system: peers and FIFOs synchronised on the wire
  module PT = Prod l PP.ParA PB.ParA (wireES l) disjT
  -- the system with every server api send blocked
  module PX = Prod l PT.ParA (SkA l) (srvApi l) (λ {ω} → disjSk l {srvApi l} {ω})

  -- the system's abstract states
  SysS : Set
  SysS = ((CPh × Bool) × (SPh × Bool)) × ((BPh × Bool) × (BPh × Bool))

  -- the system's abstraction and intro facts
  SysA : Abs l SysS
  SysA = PT.ParA

  -- (intro)
  SysI : AbsI l SysA
  SysI = PT.ParI (PP.ParI CI SI) (PB.ParI F₁.FI F₂.FI)

  -- THE BLOCKED SYSTEM: every server api send (the four notifications and the cancel) refused
  pblk : Tree
  pblk = Par⊤ (srvApi l) (psys l) Skip

  -- the blocked system's abstraction and intro facts
  BlkA : Abs l (SysS × U.⊤)
  BlkA = PX.ParA

  -- (intro)
  BlkI : AbsI l BlkA
  BlkI = PX.ParI SysI (SkI l)

  -- the initial abstract state
  σ₀ : SysS
  σ₀ = ((cIdle , false) , (sIdle , false)) , ((bq β0 , false) , (bq β0 , false))

  -- the system starts there
  psys₀ : Abs.Pos SysA σ₀ (psys l)
  psys₀ = _ , _ , refl , (_ , _ , refl , cpM stIdle , spM stIdle) , (_ , _ , refl , F₁.fpM β0 , F₂.fpM β0)

  -- … and so does the blocked system
  pblk₀ : Abs.Pos BlkA (σ₀ , U.tt) pblk
  pblk₀ = _ , _ , refl , psys₀ , refl

  ------------------------------------------------------------------------
  -- §5  The joint invariant
  ------------------------------------------------------------------------

  -- the empty FIFO
  e0 : BPh
  e0 = bq β0

  -- THE JOINT INVARIANT: the 25 reachable joint phases (client, server, client→server
  -- FIFO, server→client FIFO), loop-back flags aside.  `a…`: nothing outstanding, before
  -- the quit command; `b…`: one RequestNext outstanding (in the FIFO, held by the server,
  -- its reply commanded, its reply in the FIFO); `q…`: after a quit from StIdle; `p…`: the
  -- pipelined quit commanded with one RequestNext outstanding; `x…`: the pipelined MsgQuit
  -- sent, the client draining the owed reply
  data J : CPh → SPh → BPh → BPh → Set where
    a1 : J cIdle sIdle e0 e0
    a2 : J cSndRN sIdle e0 e0
    a3 : ∀ dv → J (cDlv dv) sIdle e0 e0
    b1 : J cBusy sIdle (bq (β1 pRN)) e0
    b2 : J cBusy sBusy e0 e0
    b3 : ∀ r → J cBusy (sRep r) e0 e0
    b4 : ∀ {x} → RepP x → J cBusy sIdle e0 (bq (β1 x))
    q1 : J cSndQ sIdle e0 e0
    q2 : J cQuit sIdle (bq (β1 pQ)) e0
    q3 : J cQuit sQuit bEnd e0
    q4 : J cQuit sDone bEnd e0
    q5 : J cQuit sEnd bEnd (bq (β1 pD))
    q6 : J cEnd sEnd bEnd bEnd
    p1 : J cSndPQ sIdle (bq (β1 pRN)) e0
    p2 : J cSndPQ sBusy e0 e0
    p3 : ∀ r → J cSndPQ (sRep r) e0 e0
    p4 : ∀ {x} → RepP x → J cSndPQ sIdle e0 (bq (β1 x))
    x1 : J cDrain sIdle (bq (β2 pRN pQ)) e0
    x2 : J cDrain sBusy (bq (β1 pQ)) e0
    x3 : ∀ r → J cDrain (sRep r) (bq (β1 pQ)) e0
    x4 : ∀ {x} → RepP x → J cDrain sIdle (bq (β1 pQ)) (bq (β1 x))
    x5 : J cDrain sCanc bEnd e0
    x6 : ∀ {x} → RepP x → J cDrain sQuit bEnd (bq (β1 x))
    x7 : ∀ {x} → RepP x → J cDrain sDone bEnd (bq (β1 x))
    x8 : ∀ {x} → RepP x → J cDrain sEnd bEnd (bq (β2 x pD))

  -- the invariant on a system state
  JJ : SysS → Set
  JJ (((c , _) , (s , _)) , ((b₁ , _) , (b₂ , _))) = J c s b₁ b₂

  -- after the client's quit command
  postJ : ∀ {c s b₁ b₂} → J c s b₁ b₂ → Bool
  postJ a1     = false
  postJ a2     = false
  postJ (a3 _) = false
  postJ b1     = false
  postJ b2     = false
  postJ (b3 _) = false
  postJ (b4 _) = false
  postJ _      = true

  -- after the quit command, with the server application silent: the most visible events
  -- still possible (e.g. p1: MsgQuit sent, RequestNext received, MsgQuit read ahead,
  -- MsgCanceled sent, MsgCanceled drained, done, MsgDone sent, MsgDone received = 8)
  rankJ : ∀ {c s b₁ b₂} → J c s b₁ b₂ → ℕ
  rankJ q1     = 5
  rankJ q2     = 4
  rankJ q3     = 3
  rankJ q4     = 2
  rankJ q5     = 1
  rankJ p1     = 8
  rankJ p2     = 7
  rankJ (p3 _) = 7
  rankJ (p4 _) = 6
  rankJ x1     = 7
  rankJ x2     = 6
  rankJ (x3 _) = 6
  rankJ (x4 _) = 5
  rankJ x5     = 5
  rankJ (x6 _) = 4
  rankJ (x7 _) = 3
  rankJ (x8 _) = 2
  rankJ _      = 0

  -- the client messages sent but not yet answered by a server message
  pkJ : ∀ {c s b₁ b₂} → J c s b₁ b₂ → PK
  pkJ b1     = kR
  pkJ b2     = kR
  pkJ (b3 _) = kR
  pkJ q2     = kQ
  pkJ q3     = kQ
  pkJ q4     = kQ
  pkJ p1     = kR
  pkJ p2     = kR
  pkJ (p3 _) = kR
  pkJ x1     = kRQ
  pkJ x2     = kRQ
  pkJ (x3 _) = kRQ
  pkJ (x4 _) = kQ
  pkJ x5     = kRQ
  pkJ (x6 _) = kQ
  pkJ (x7 _) = kQ
  pkJ _      = k0

  -- whether MsgDone has been sent
  clJ : ∀ {c s b₁ b₂} → J c s b₁ b₂ → Bool
  clJ q5     = true
  clJ q6     = true
  clJ (x8 _) = true
  clJ _      = false

  -- side fact: the quit command leads after it
  qOK : ∀ {c s b₁ b₂} → Lab l → J c s b₁ b₂ → Bool
  qOK ω j′ = not (isQuitApi l ω) ∨ postJ j′

  -- side fact: once after the quit command, always after it
  postOK : ∀ {c s b₁ b₂ c′ s′ b₁′ b₂′} → J c s b₁ b₂ → J c′ s′ b₁′ b₂′ → Bool
  postOK j j′ = not (postJ j) ∨ postJ j′

  -- side fact: after the quit command, the rank strictly drops
  rkDrop : ∀ {c s b₁ b₂ c′ s′ b₁′ b₂′} → J c s b₁ b₂ → J c′ s′ b₁′ b₂′ → Bool
  rkDrop j j′ = not (postJ j) ∨ (suc (rankJ j′) ≤ᵇ rankJ j)

  -- the protocol side facts of a step: a client send appends to the unanswered client
  -- messages; a server send answers the first of them; any other step changes neither
  PSide : ∀ {c s b₁ b₂ c′ s′ b₁′ b₂′} → Lab l → J c s b₁ b₂ → J c′ s′ b₁′ b₂′ → Set
  PSide (wS lo x)  j j′ = pl (pkJ j′) ≡ pl (pkJ j) ++ x ∷ [] × clJ j′ ≡ clJ j
  PSide (wS hi x)  j j′ = Σ[ q ∈ Payload ] (pl (pkJ j) ≡ q ∷ pl (pkJ j′) × Ans1 (clJ j) q x (clJ j′))
  PSide (wR _ _)   j j′ = pkJ j′ ≡ pkJ j × clJ j′ ≡ clJ j
  PSide (ap _ _ _) j j′ = pkJ j′ ≡ pkJ j × clJ j′ ≡ clJ j
  PSide (dn _)     j j′ = pkJ j′ ≡ pkJ j × clJ j′ ≡ clJ j

  -- all side facts of a visible step (the rank need not drop on a server api send: the
  -- bound is only claimed with those sends blocked)
  Side : ∀ {c s b₁ b₂ c′ s′ b₁′ b₂′} → Lab l → J c s b₁ b₂ → J c′ s′ b₁′ b₂′ → Set
  Side ω j j′ = T (qOK ω j′) × T (postOK j j′) × (¬ InE l (srvApi l) ω → T (rkDrop j j′)) × PSide ω j j′

  -- a client api step (RequestNext, the quit command, a delivery)
  capi : ∀ {c f σc′ s b₁ b₂ ω} → ¬ InE l (wireES l) ω → CSt (c , f) (ev′ ω) σc′
       → (j : J c s b₁ b₂) → Σ[ j′ ∈ J (proj₁ σc′) s b₁ b₂ ] Side ω j j′
  capi _ (cRN _) a1     = a2 , _ , _ , (λ _ → _) , refl , refl
  capi _ (cQi _) a1     = q1 , _ , _ , (λ _ → _) , refl , refl
  capi _ (cQp _) b1     = p1 , _ , _ , (λ _ → _) , refl , refl
  capi _ (cQp _) b2     = p2 , _ , _ , (λ _ → _) , refl , refl
  capi _ (cQp _) (b3 r) = p3 r , _ , _ , (λ _ → _) , refl , refl
  capi _ (cQp _) (b4 k) = p4 k , _ , _ , (λ _ → _) , refl , refl
  capi _ (cDl (dAnn _))   (a3 _) = a1 , _ , _ , (λ _ → _) , refl , refl
  capi _ (cDl (dOff _ _)) (a3 _) = a1 , _ , _ , (λ _ → _) , refl , refl
  capi _ (cDl (dTxs _))   (a3 _) = a1 , _ , _ , (λ _ → _) , refl , refl
  capi _ (cDl (dVot _))   (a3 _) = a1 , _ , _ , (λ _ → _) , refl , refl
  capi ¬w cSR     _ = ⊥-elim (¬w U.tt)
  capi ¬w cSQ     _ = ⊥-elim (¬w U.tt)
  capi ¬w cSP     _ = ⊥-elim (¬w U.tt)
  capi ¬w (cRc _) _ = ⊥-elim (¬w U.tt)
  capi ¬w (cDr _) _ = ⊥-elim (¬w U.tt)
  capi ¬w cDn     _ = ⊥-elim (¬w U.tt)

  -- a server api / done step (a reply command, the peer-local done)
  sapi : ∀ {c s f σs′ b₁ b₂ ω} → ¬ InE l (wireES l) ω → SSt (s , f) (ev′ ω) σs′
       → (j : J c s b₁ b₂) → Σ[ j′ ∈ J c (proj₁ σs′) b₁ b₂ ] Side ω j j′
  sapi _ (sAp r) b2     = b3 r , _ , _ , (λ _ → _) , refl , refl
  sapi _ (sAp r) p2     = p3 r , _ , _ , (λ ¬s → ⊥-elim (¬s (srvTag r))) , refl , refl
  sapi _ (sAp r) x2     = x3 r , _ , _ , (λ ¬s → ⊥-elim (¬s (srvTag r))) , refl , refl
  sapi _ sDn     q3     = q4 , _ , _ , (λ _ → _) , refl , refl
  sapi _ sDn     (x6 k) = x7 k , _ , _ , (λ _ → _) , refl , refl
  sapi ¬w sRN     _ = ⊥-elim (¬w U.tt)
  sapi ¬w sQi     _ = ⊥-elim (¬w U.tt)
  sapi ¬w sRA     _ = ⊥-elim (¬w U.tt)
  sapi ¬w (sNx _) _ = ⊥-elim (¬w U.tt)
  sapi ¬w sCx     _ = ⊥-elim (¬w U.tt)
  sapi ¬w sDS     _ = ⊥-elim (¬w U.tt)

  -- the client sends into the client→server FIFO
  syncC1 : ∀ {c f σc′ s b₁ h σ₁′ b₂ ω} → CSt (c , f) (ev′ ω) σc′ → F₁.FSt (b₁ , h) (ev′ ω) σ₁′
         → (j : J c s b₁ b₂) → Σ[ j′ ∈ J (proj₁ σc′) s (proj₁ σ₁′) b₂ ] Side ω j j′
  syncC1 cSR (F₁.fI0 _)   a2     = b1 , _ , _ , (λ _ → _) , refl , refl
  syncC1 cSQ (F₁.fI0 _)   q1     = q2 , _ , _ , (λ _ → _) , refl , refl
  syncC1 cSP (F₁.fI1 _ _) p1     = x1 , _ , _ , (λ _ → _) , refl , refl
  syncC1 cSP (F₁.fI0 _)   p2     = x2 , _ , _ , (λ _ → _) , refl , refl
  syncC1 cSP (F₁.fI0 _)   (p3 r) = x3 r , _ , _ , (λ _ → _) , refl , refl
  syncC1 cSP (F₁.fI0 _)   (p4 k) = x4 k , _ , _ , (λ _ → _) , refl , refl
  syncC1 (cRN _) ()
  syncC1 (cQi _) ()
  syncC1 (cRc _) ()
  syncC1 (cQp _) ()
  syncC1 (cDr _) ()
  syncC1 (cDl (dAnn _))   ()
  syncC1 (cDl (dOff _ _)) ()
  syncC1 (cDl (dTxs _))   ()
  syncC1 (cDl (dVot _))   ()
  syncC1 cDn ()

  -- the client receives a reply in StBusy (delivered, or MsgCanceled: straight back)
  rcv4 : ∀ {x} (k : RepP x)
       → Σ[ j′ ∈ J (proj₁ (rcvTo k)) sIdle e0 (proj₁ (aOut (isLast x))) ] Side (wR lo x) (b4 k) j′
  rcv4 (rpA h)    = a3 (dAnn h) , _ , _ , (λ _ → _) , refl , refl
  rcv4 (rpO q sz) = a3 (dOff q sz) , _ , _ , (λ _ → _) , refl , refl
  rcv4 (rpT q)    = a3 (dTxs q) , _ , _ , (λ _ → _) , refl , refl
  rcv4 (rpV vs)   = a3 (dVot vs) , _ , _ , (λ _ → _) , refl , refl
  rcv4 rpC        = a1 , _ , _ , (λ _ → _) , refl , refl

  -- the client receives from the server→client FIFO
  syncC2 : ∀ {c f σc′ s b₁ b₂ h σ₂′ ω} → CSt (c , f) (ev′ ω) σc′ → F₂.FSt (b₂ , h) (ev′ ω) σ₂′
         → (j : J c s b₁ b₂) → Σ[ j′ ∈ J (proj₁ σc′) s b₁ (proj₁ σ₂′) ] Side ω j j′
  syncC2 (cRc k) (F₂.fO1 _) (b4 _) = rcv4 k
  syncC2 (cDr k) (F₂.fO1 _) (x4 _) rewrite notLast k = q2 , _ , _ , (λ _ → _) , refl , refl
  syncC2 (cDr k) (F₂.fO1 _) (x6 _) rewrite notLast k = q3 , _ , _ , (λ _ → _) , refl , refl
  syncC2 (cDr k) (F₂.fO1 _) (x7 _) rewrite notLast k = q4 , _ , _ , (λ _ → _) , refl , refl
  syncC2 (cDr _) (F₂.fO2 _ _) (x8 _) = q5 , _ , _ , (λ _ → _) , refl , refl
  syncC2 cDn (F₂.fO1 _) q5 = q6 , _ , _ , (λ _ → _) , refl , refl
  syncC2 (cRN _) ()
  syncC2 (cQi _) ()
  syncC2 cSR ()
  syncC2 cSQ ()
  syncC2 (cQp _) ()
  syncC2 cSP ()
  syncC2 (cDl (dAnn _))   ()
  syncC2 (cDl (dOff _ _)) ()
  syncC2 (cDl (dTxs _))   ()
  syncC2 (cDl (dVot _))   ()

  -- the server receives from the client→server FIFO
  syncS1 : ∀ {c s f σs′ b₁ h σ₁′ b₂ ω} → SSt (s , f) (ev′ ω) σs′ → F₁.FSt (b₁ , h) (ev′ ω) σ₁′
         → (j : J c s b₁ b₂) → Σ[ j′ ∈ J c (proj₁ σs′) (proj₁ σ₁′) b₂ ] Side ω j j′
  syncS1 sRN (F₁.fO1 _)   b1     = b2 , _ , _ , (λ _ → _) , refl , refl
  syncS1 sRN (F₁.fO1 _)   p1     = p2 , _ , _ , (λ _ → _) , refl , refl
  syncS1 sRN (F₁.fO2 _ _) x1     = x2 , _ , _ , (λ _ → _) , refl , refl
  syncS1 sQi (F₁.fO1 _)   q2     = q3 , _ , _ , (λ _ → _) , refl , refl
  syncS1 sQi (F₁.fO1 _)   (x4 k) = x6 k , _ , _ , (λ _ → _) , refl , refl
  syncS1 sRA (F₁.fO1 _)   x2     = x5 , _ , _ , (λ _ → _) , refl , refl
  syncS1 (sAp _) ()
  syncS1 (sNx _) ()
  syncS1 sCx ()
  syncS1 sDn ()
  syncS1 sDS ()

  -- the server sends into the server→client FIFO
  syncS2 : ∀ {c s f σs′ b₁ b₂ h σ₂′ ω} → SSt (s , f) (ev′ ω) σs′ → F₂.FSt (b₂ , h) (ev′ ω) σ₂′
         → (j : J c s b₁ b₂) → Σ[ j′ ∈ J c (proj₁ σs′) b₁ (proj₁ σ₂′) ] Side ω j j′
  syncS2 (sNx r) (F₂.fI0 _)   (b3 _) = b4 (repP r) , _ , _ , (λ _ → _) , pRN , refl , a1R (repP r)
  syncS2 (sNx r) (F₂.fI0 _)   (p3 _) = p4 (repP r) , _ , _ , (λ _ → _) , pRN , refl , a1R (repP r)
  syncS2 (sNx r) (F₂.fI0 _)   (x3 _) = x4 (repP r) , _ , _ , (λ _ → _) , pRN , refl , a1R (repP r)
  syncS2 sCx     (F₂.fI0 _)   x5     = x6 rpC , _ , _ , (λ _ → _) , pRN , refl , a1R rpC
  syncS2 sDS     (F₂.fI0 _)   q4     = q5 , _ , _ , (λ _ → _) , pQ , refl , a1Q
  syncS2 sDS     (F₂.fI1 _ _) (x7 k) = x8 k , _ , _ , (λ _ → _) , pQ , refl , a1Q
  syncS2 sRN ()
  syncS2 sQi ()
  syncS2 (sAp _) ()
  syncS2 sRA ()
  syncS2 sDn ()

  -- THE INVARIANT IS INDUCTIVE (visible steps): every visible system step keeps it, with
  -- the side facts
  J-ev : ∀ {σ ω σ′} (j : JJ σ) → Abs.Stp SysA σ (ev′ ω) σ′ → Σ[ j′ ∈ JJ σ′ ] Side ω j j′
  J-ev j (PT.psy _ (PP.psL _ c) (PB.psL _ b)) = syncC1 c b j
  J-ev j (PT.psy _ (PP.psL _ c) (PB.psR _ b)) = syncC2 c b j
  J-ev j (PT.psy _ (PP.psR _ s) (PB.psL _ b)) = syncS1 s b j
  J-ev j (PT.psy _ (PP.psR _ s) (PB.psR _ b)) = syncS2 s b j
  J-ev j (PT.psy _ (PP.psy () _ _) _)
  J-ev j (PT.psy _ (PP.psL _ _) (PB.psy () _ _))
  J-ev j (PT.psy _ (PP.psR _ _) (PB.psy () _ _))
  J-ev j (PT.psL ¬w (PP.psL _ c)) = capi ¬w c j
  J-ev j (PT.psL ¬w (PP.psR _ s)) = sapi ¬w s j
  J-ev j (PT.psL _ (PP.psy () _ _))
  J-ev j (PT.psR ¬w (PB.psL _ b)) = ⊥-elim (¬w (chW (inj₁ (F₁.fAlpha b))))
  J-ev j (PT.psR ¬w (PB.psR _ b)) = ⊥-elim (¬w (chW (inj₂ (F₂.fAlpha b))))
  J-ev j (PT.psR _ (PB.psy () _ _))

  -- … and every τ keeps the phase (only a loop-back flag changes)
  J-τ : ∀ {σ σ′} (j : JJ σ) → Abs.Stp SysA σ τ′ σ′
      → Σ[ j′ ∈ JJ σ′ ] (postJ j′ ≡ postJ j × rankJ j′ ≡ rankJ j × pkJ j′ ≡ pkJ j × clJ j′ ≡ clJ j)
  J-τ j (PT.pτL (PP.pτL cτ))    = j , refl , refl , refl , refl
  J-τ j (PT.pτL (PP.pτR sτ))    = j , refl , refl , refl , refl
  J-τ j (PT.pτR (PB.pτL F₁.fτ)) = j , refl , refl , refl , refl
  J-τ j (PT.pτR (PB.pτR F₂.fτ)) = j , refl , refl , refl , refl

  ------------------------------------------------------------------------
  -- §6  Progress
  ------------------------------------------------------------------------

  -- a step label the blocking set does not touch (a τ, or a label off the server api sends)
  OffSrv : ALbl l → Set
  OffSrv τ′      = U.⊤
  OffSrv (ev′ ω) = ¬ InE l (srvApi l) ω

  -- what progress gives at a state: the end, or a step that is not a server api send
  Prog : SysS → Set
  Prog σ = Abs.Fin SysA σ ⊎ Σ[ ℓ ∈ ALbl l ] Σ[ σ′ ∈ SysS ] (Abs.Stp SysA σ ℓ σ′ × OffSrv ℓ)

  -- PROGRESS with no loop-back pending: every joint phase has a step that is NOT a server
  -- api send (a held request is escaped by the client's pipelined quit, `b2`, or by the
  -- server's read-ahead, `x2`), or has terminated (`q6`)
  progJ : ∀ {c s b₁ b₂} (j : J c s b₁ b₂) → Prog (((c , false) , (s , false)) , ((b₁ , false) , (b₂ , false)))
  progJ a1               = inj₂ (_ , _ , PT.psL (λ ()) (PP.psL (λ ()) (cRN U.tt)) , λ ())
  progJ a2               = inj₂ (_ , _ , PT.psy U.tt (PP.psL (λ ()) cSR) (PB.psL (λ ()) (F₁.fI0 _)) , λ ())
  progJ (a3 (dAnn h))    = inj₂ (_ , _ , PT.psL (λ ()) (PP.psL (λ ()) (cDl (dAnn h))) , λ ())
  progJ (a3 (dOff q sz)) = inj₂ (_ , _ , PT.psL (λ ()) (PP.psL (λ ()) (cDl (dOff q sz))) , λ ())
  progJ (a3 (dTxs q))    = inj₂ (_ , _ , PT.psL (λ ()) (PP.psL (λ ()) (cDl (dTxs q))) , λ ())
  progJ (a3 (dVot vs))   = inj₂ (_ , _ , PT.psL (λ ()) (PP.psL (λ ()) (cDl (dVot vs))) , λ ())
  progJ b1               = inj₂ (_ , _ , PT.psy U.tt (PP.psR (λ ()) sRN) (PB.psL (λ ()) (F₁.fO1 _)) , λ ())
  progJ b2               = inj₂ (_ , _ , PT.psL (λ ()) (PP.psL (λ ()) (cQp U.tt)) , λ ())
  progJ (b3 r)           = inj₂ (_ , _ , PT.psy U.tt (PP.psR (λ ()) (sNx r)) (PB.psR (λ ()) (F₂.fI0 _)) , λ ())
  progJ (b4 k)           = inj₂ (_ , _ , PT.psy U.tt (PP.psL (λ ()) (cRc k)) (PB.psR (λ ()) (F₂.fO1 _)) , λ ())
  progJ q1               = inj₂ (_ , _ , PT.psy U.tt (PP.psL (λ ()) cSQ) (PB.psL (λ ()) (F₁.fI0 _)) , λ ())
  progJ q2               = inj₂ (_ , _ , PT.psy U.tt (PP.psR (λ ()) sQi) (PB.psL (λ ()) (F₁.fO1 _)) , λ ())
  progJ q3               = inj₂ (_ , _ , PT.psL (λ ()) (PP.psR (λ ()) sDn) , λ ())
  progJ q4               = inj₂ (_ , _ , PT.psy U.tt (PP.psR (λ ()) sDS) (PB.psR (λ ()) (F₂.fI0 _)) , λ ())
  progJ q5               = inj₂ (_ , _ , PT.psy U.tt (PP.psL (λ ()) cDn) (PB.psR (λ ()) (F₂.fO1 _)) , λ ())
  progJ q6               = inj₁ ((U.tt , U.tt) , (U.tt , U.tt))
  progJ p1               = inj₂ (_ , _ , PT.psy U.tt (PP.psL (λ ()) cSP) (PB.psL (λ ()) (F₁.fI1 _ _)) , λ ())
  progJ p2               = inj₂ (_ , _ , PT.psy U.tt (PP.psL (λ ()) cSP) (PB.psL (λ ()) (F₁.fI0 _)) , λ ())
  progJ (p3 _)           = inj₂ (_ , _ , PT.psy U.tt (PP.psL (λ ()) cSP) (PB.psL (λ ()) (F₁.fI0 _)) , λ ())
  progJ (p4 _)           = inj₂ (_ , _ , PT.psy U.tt (PP.psL (λ ()) cSP) (PB.psL (λ ()) (F₁.fI0 _)) , λ ())
  progJ x1               = inj₂ (_ , _ , PT.psy U.tt (PP.psR (λ ()) sRN) (PB.psL (λ ()) (F₁.fO2 _ _)) , λ ())
  progJ x2               = inj₂ (_ , _ , PT.psy U.tt (PP.psR (λ ()) sRA) (PB.psL (λ ()) (F₁.fO1 _)) , λ ())
  progJ (x3 r)           = inj₂ (_ , _ , PT.psy U.tt (PP.psR (λ ()) (sNx r)) (PB.psR (λ ()) (F₂.fI0 _)) , λ ())
  progJ (x4 k)           = inj₂ (_ , _ , PT.psy U.tt (PP.psL (λ ()) (cDr k)) (PB.psR (λ ()) (F₂.fO1 _)) , λ ())
  progJ x5               = inj₂ (_ , _ , PT.psy U.tt (PP.psR (λ ()) sCx) (PB.psR (λ ()) (F₂.fI0 _)) , λ ())
  progJ (x6 _)           = inj₂ (_ , _ , PT.psL (λ ()) (PP.psR (λ ()) sDn) , λ ())
  progJ (x7 _)           = inj₂ (_ , _ , PT.psy U.tt (PP.psR (λ ()) sDS) (PB.psR (λ ()) (F₂.fI1 _ _)) , λ ())
  progJ (x8 k)           = inj₂ (_ , _ , PT.psy U.tt (PP.psL (λ ()) (cDr k)) (PB.psR (λ ()) (F₂.fO2 _ _)) , λ ())

  -- a client loop-back is pending, or none is
  cτ? : ∀ {c f t} → CPos (c , f) t → f ≡ false ⊎ Σ[ σ′ ∈ CPh × Bool ] CSt (c , f) τ′ σ′
  cτ? (cpM _) = inj₁ refl
  cτ? (cp′ _) = inj₂ (_ , cτ)
  cτ? cpR     = inj₁ refl
  cτ? cpS     = inj₁ refl
  cτ? cpP     = inj₁ refl
  cτ? cpX     = inj₁ refl
  cτ? (cpD _) = inj₁ refl
  cτ? cpE     = inj₁ refl

  -- (the server)
  sτ? : ∀ {s f t} → SPos (s , f) t → f ≡ false ⊎ Σ[ σ′ ∈ SPh × Bool ] SSt (s , f) τ′ σ′
  sτ? (spM _) = inj₁ refl
  sτ? (sp′ _) = inj₂ (_ , sτ)
  sτ? (spN _) = inj₁ refl
  sτ? spC     = inj₁ refl
  sτ? spD     = inj₁ refl
  sτ? spE     = inj₁ refl

  -- (a FIFO)
  fτ? : ∀ {i o b f t} → Fifo.FPos i o (b , f) t → f ≡ false ⊎ Σ[ σ′ ∈ BPh × Bool ] Fifo.FSt i o (b , f) τ′ σ′
  fτ? (Fifo.fpM _) = inj₁ refl
  fτ? (Fifo.fp′ _) = inj₂ (_ , Fifo.fτ)
  fτ? Fifo.fpE     = inj₁ refl

  -- PROGRESS at every positioned state: a pending loop-back τ, or the phase's witness
  prog : ∀ {σ t} → JJ σ → Abs.Pos SysA σ t → Prog σ
  prog j (_ , _ , _ , (_ , _ , _ , pc , ps) , (_ , _ , _ , p₁ , p₂)) with cτ? pc | sτ? ps | fτ? p₁ | fτ? p₂
  ... | inj₂ (_ , a) | _            | _            | _            = inj₂ (τ′ , _ , PT.pτL (PP.pτL a) , U.tt)
  ... | inj₁ refl    | inj₂ (_ , a) | _            | _            = inj₂ (τ′ , _ , PT.pτL (PP.pτR a) , U.tt)
  ... | inj₁ refl    | inj₁ refl    | inj₂ (_ , a) | _            = inj₂ (τ′ , _ , PT.pτR (PB.pτL a) , U.tt)
  ... | inj₁ refl    | inj₁ refl    | inj₁ refl    | inj₂ (_ , a) = inj₂ (τ′ , _ , PT.pτR (PB.pτR a) , U.tt)
  ... | inj₁ refl    | inj₁ refl    | inj₁ refl    | inj₁ refl    = progJ j

  -- forgetting the blocking side condition
  progS : ∀ {σ t} → JJ σ → Abs.Pos SysA σ t
        → Abs.Fin SysA σ ⊎ Σ[ ℓ ∈ ALbl l ] Σ[ σ′ ∈ SysS ] Abs.Stp SysA σ ℓ σ′
  progS j p with prog j p
  ... | inj₁ f                = inj₁ f
  ... | inj₂ (ℓ , σ′ , a , _) = inj₂ (ℓ , σ′ , a)

  -- a step of the blocked system is a system step
  unblk : ∀ {σ ℓ σ′} → Abs.Stp BlkA σ ℓ σ′ → Abs.Stp SysA (proj₁ σ) ℓ (proj₁ σ′)
  unblk (PX.pτL a)   = a
  unblk (PX.psL _ a) = a
  unblk (PX.pτR ())
  unblk (PX.psy _ _ ())
  unblk (PX.psR _ ())

  -- a visible step of the blocked system is never a server api send
  offB : ∀ {σ ω σ′} → Abs.Stp BlkA σ (ev′ ω) σ′ → ¬ InE l (srvApi l) ω
  offB (PX.psL ¬s _) = ¬s
  offB (PX.psy _ _ ())
  offB (PX.psR _ ())

  -- progress of the blocked system: the witness never needs a blocked server send
  progB : ∀ {σ t} → JJ (proj₁ σ) → Abs.Pos BlkA σ t
        → Abs.Fin BlkA σ ⊎ Σ[ ℓ ∈ ALbl l ] Σ[ σ′ ∈ SysS × U.⊤ ] Abs.Stp BlkA σ ℓ σ′
  progB j (_ , _ , refl , p , refl) with prog j p
  ... | inj₁ f                     = inj₁ (f , U.tt)
  ... | inj₂ (τ′ , _ , a , _)      = inj₂ (τ′ , _ , PX.pτL a)
  ... | inj₂ (ev′ _ , _ , a , off) = inj₂ (ev′ _ , _ , PX.psL off a)

  ------------------------------------------------------------------------
  -- §7  Walking a run
  ------------------------------------------------------------------------

  -- the client messages an event sends (the client's own sends, at `(l , lo)`)
  cmE : Event → List Payload
  cmE (evLabel _ (sendLNP _ lo) x) = x ∷ []
  cmE _                            = []

  -- the server messages an event sends (the server's own sends, at `(l , hi)`)
  smE : Event → List Payload
  smE (evLabel _ (sendLNP _ hi) x) = x ∷ []
  smE _                            = []

  -- THE CLIENT'S MESSAGES of a trace, in send order
  cm : List Event → List Payload
  cm []      = []
  cm (e ∷ s) = cmE e ++ cm s

  -- THE SERVER'S MESSAGES of a trace, in send order
  sm : List Event → List Payload
  sm []      = []
  sm (e ∷ s) = smE e ++ sm s

  -- the protocol-order invariant at phase `j`: the client's messages so far are the answered
  -- ones `cs₀` followed by the unanswered ones of `j`, and `cs₀` is paired with the server's
  K : ∀ {c s b₁ b₂} → J c s b₁ b₂ → List Payload → List Payload → Set
  K j cs ss = Σ[ cs₀ ∈ List Payload ] (cs ≡ cs₀ ++ pl (pkJ j) × Ans (clJ j) cs₀ ss)

  -- the invariant before anything happened
  K₀ : K a1 [] []
  K₀ = [] , refl , aε

  -- a step that changes neither the unanswered messages nor the flag keeps it
  kSame : ∀ {c s b₁ b₂ c′ s′ b₁′ b₂′} {j : J c s b₁ b₂} {j′ : J c′ s′ b₁′ b₂′} {cs ss}
        → pkJ j′ ≡ pkJ j → clJ j′ ≡ clJ j → K j cs ss → K j′ cs ss
  kSame {j′ = j′} {ss = ss} e c (cs₀ , eq , a) =
    cs₀ , trans eq (cong (λ k → cs₀ ++ pl k) (sym e)) , subst (λ b → Ans b cs₀ ss) (sym c) a

  -- one visible step keeps it, extended by the step's messages
  kstep : ∀ ω {c s b₁ b₂ c′ s′ b₁′ b₂′} {j : J c s b₁ b₂} {j′ : J c′ s′ b₁′ b₂′} {cs ss}
        → PSide ω j j′ → K j cs ss → K j′ (cs ++ cmE ⌞ ω ⌟) (ss ++ smE ⌞ ω ⌟)
  kstep (wS lo x) {j = j} {j′} {ss = ss} (e , c) (cs₀ , refl , a) =
    cs₀ , trans (++-assoc cs₀ (pl (pkJ j)) (x ∷ [])) (cong (cs₀ ++_) (sym e))
        , subst₂ (λ b ys → Ans b cs₀ ys) (sym c) (sym (++-identityʳ ss)) a
  kstep (wS hi x) {j = j} {j′} (q , e , n) (cs₀ , refl , a) =
    cs₀ ++ q ∷ []
        , trans (++-identityʳ (cs₀ ++ pl (pkJ j)))
                (trans (cong (cs₀ ++_) e) (sym (++-assoc cs₀ (q ∷ []) (pl (pkJ j′)))))
        , ans-snoc a n
  kstep (wR _ _)   {cs = cs} {ss} (e , c) k =
    subst₂ (K _) (sym (++-identityʳ cs)) (sym (++-identityʳ ss)) (kSame e c k)
  kstep (ap _ _ _) {cs = cs} {ss} (e , c) k =
    subst₂ (K _) (sym (++-identityʳ cs)) (sym (++-identityʳ ss)) (kSame e c k)
  kstep (dn _)     {cs = cs} {ss} (e , c) k =
    subst₂ (K _) (sym (++-identityʳ cs)) (sym (++-identityʳ ss)) (kSame e c k)

  -- every rank is at most 8
  rank≤8 : ∀ {c s b₁ b₂} (j : J c s b₁ b₂) → rankJ j ≤ 8
  rank≤8 j = ≤ᵇ⇒≤ (rankJ j) 8 (r8 j)
    where
    -- by computation
    r8 : ∀ {c s b₁ b₂} (j : J c s b₁ b₂) → T (rankJ j ≤ᵇ 8)
    r8 a1     = U.tt
    r8 a2     = U.tt
    r8 (a3 _) = U.tt
    r8 b1     = U.tt
    r8 b2     = U.tt
    r8 (b3 _) = U.tt
    r8 (b4 _) = U.tt
    r8 q1     = U.tt
    r8 q2     = U.tt
    r8 q3     = U.tt
    r8 q4     = U.tt
    r8 q5     = U.tt
    r8 q6     = U.tt
    r8 p1     = U.tt
    r8 p2     = U.tt
    r8 (p3 _) = U.tt
    r8 (p4 _) = U.tt
    r8 x1     = U.tt
    r8 x2     = U.tt
    r8 (x3 _) = U.tt
    r8 (x4 _) = U.tt
    r8 x5     = U.tt
    r8 (x6 _) = U.tt
    r8 (x7 _) = U.tt
    r8 (x8 _) = U.tt

  -- the invariants along any run of a system (`π` reads the pipelined system's state off it)
  module Walk {S : Set} (A : Abs l S) (π : S → SysS)
              (un : ∀ {σ ℓ σ′} → Abs.Stp A σ ℓ σ′ → Abs.Stp SysA (π σ) ℓ (π σ′)) where
    open Abs A using (Pos; Fin; Stp)
    open Gen l A using (ARun; r0; rτ; rE; runE)

    -- along a run: `J` holds, the protocol-order invariant grows by the run's messages, and
    -- the post-quit phase is entered by the quit command and never left
    walk : ∀ {σ s σ′} → ARun σ s σ′ → (j : JJ (π σ)) → ∀ {cs ss} → K j cs ss
         → Σ[ j′ ∈ JJ (π σ′) ] (K j′ (cs ++ cm s) (ss ++ sm s) × ((Any (QuitApi l) s ⊎ T (postJ j)) → T (postJ j′)))
    walk r0 j {cs} {ss} k =
      j , subst₂ (K j) (sym (++-identityʳ cs)) (sym (++-identityʳ ss)) k , λ { (inj₁ ()) ; (inj₂ p) → p }
    walk (rτ a ar) j k with J-τ j (un a)
    ... | j₁ , p≡ , _ , k≡ , c≡ with walk ar j₁ (kSame k≡ c≡ k)
    ...   | j′ , k′ , f = j′ , k′ , λ { (inj₁ q) → f (inj₁ q) ; (inj₂ p) → f (inj₂ (subst T (sym p≡) p)) }
    walk (rE {s = s} {ω = ω} a ar) j {cs} {ss} k with J-ev j (un a)
    ... | j₁ , qo , po , _ , ps with walk ar j₁ (kstep ω ps k)
    ...   | j′ , k′ , f =
            j′ , subst₂ (K j′) (++-assoc cs (cmE ⌞ ω ⌟) (cm s)) (++-assoc ss (smE ⌞ ω ⌟) (sm s)) k′ , g
      where
      -- the quit command here, later, or already behind
      g : (Any (QuitApi l) (⌞ ω ⌟ ∷ s) ⊎ T (postJ j)) → T (postJ j′)
      g (inj₁ (here q))  = f (inj₂ (⇒ l {isQuitApi l ω} qo (quitApi-T l ω q)))
      g (inj₁ (there q)) = f (inj₁ q)
      g (inj₂ p)         = f (inj₂ (⇒ l {postJ j} po p))

    -- (generic) a positioned start satisfying the invariants, with progress, is deadlock-free
    dlFree : (I : AbsI l A)
           → (∀ {σ t} → JJ (π σ) → Pos σ t → Fin σ ⊎ Σ[ ℓ ∈ ALbl l ] Σ[ σ′ ∈ S ] Stp σ ℓ σ′)
           → ∀ {σ t} → Pos σ t → (j : JJ (π σ)) → K j [] [] → DeadlockFree t
    dlFree I pr p j k r stk with runE p r
    ... | _ , ar , p′ = GenI.notStuck l I p′ (pr (proj₁ (walk ar j k)) p′) stk

  -- the rank bound, for a system whose visible steps are never server api sends
  module WalkB {S : Set} (A : Abs l S) (π : S → SysS)
               (un : ∀ {σ ℓ σ′} → Abs.Stp A σ ℓ σ′ → Abs.Stp SysA (π σ) ℓ (π σ′))
               (off : ∀ {σ ω σ′} → Abs.Stp A σ (ev′ ω) σ′ → ¬ InE l (srvApi l) ω) where
    open Abs A using (Pos; Fin; Stp)
    open Gen l A using (ARun; r0; rτ; rE; runE)
    open Walk A π un using (walk)

    -- after the quit command, a run has at most `rankJ` visible events
    bound : ∀ {σ s σ′} → ARun σ s σ′ → (j : JJ (π σ)) → T (postJ j) → length s ≤ rankJ j
    bound r0 _ _ = z≤n
    bound (rτ a ar) j p with J-τ j (un a)
    ... | j₁ , p≡ , r≡ , _ = subst (_ ≤_) r≡ (bound ar j₁ (subst T (sym p≡) p))
    bound (rE a ar) j p with J-ev j (un a)
    ... | j₁ , _ , po , rk , _ =
          ≤-trans (s≤s (bound ar j₁ (⇒ l {postJ j} po p)))
                  (≤ᵇ⇒≤ (suc (rankJ j₁)) (rankJ j) (⇒ l {postJ j} (rk (off a)) p))

    -- once the quit is commanded: what remains is deadlock-free, divergence-free, and has
    -- at most 8 visible events
    afterQuit : (I : AbsI l A)
              → (∀ {σ t} → JJ (π σ) → Pos σ t → Fin σ ⊎ Σ[ ℓ ∈ ALbl l ] Σ[ σ′ ∈ S ] Stp σ ℓ σ′)
              → ∀ {σ t} → Pos σ t → (j : JJ (π σ)) → K j [] [] → ∀ {s W} → t ⟹∖√⟨ s ⟩ W → Any (QuitApi l) s
              → DeadlockFree W × DivergenceFree W × (∀ {s′ W′} → W ⟹∖√⟨ s′ ⟩ W′ → length s′ ≤ 8)
    afterQuit I pr p j k {W = W} r q with runE p r
    ... | _ , ar , p₁ with walk ar j k
    ...   | j₁ , k₁ , post = dl , Gen.divFree l A p₁ , bd
      where
      -- the quit command is behind
      post₁ : T (postJ j₁)
      post₁ = post (inj₁ q)
      -- no deadlock from here
      dl : DeadlockFree W
      dl r′ stk with runE p₁ r′
      ... | _ , ar′ , p₂ = GenI.notStuck l I p₂ (pr (proj₁ (walk ar′ j₁ k₁)) p₂) stk
      -- at most 8 more visible events
      bd : ∀ {s′ W′} → W ⟹∖√⟨ s′ ⟩ W′ → length s′ ≤ 8
      bd r′ with runE p₁ r′
      ... | _ , ar′ , _ = ≤-trans (bound ar′ j₁ post₁) (rank≤8 j₁)

  -- the walk of the pipelined system
  module WS = Walk SysA (λ σ → σ) (λ a → a)
  -- the walk of the blocked system
  module WB = Walk BlkA proj₁ unblk
  -- the rank bound of the blocked system
  module WBB = WalkB BlkA proj₁ unblk offB

  ------------------------------------------------------------------------
  -- §8  (P4) deadlock and divergence freedom; (P5, P2) the blocked system
  ------------------------------------------------------------------------

  -- (P4) THE PIPELINED SYSTEM NEVER GETS STUCK BEFORE √ (api / done open to the environment)
  psys-deadlockFree : DeadlockFree (psys l)
  psys-deadlockFree = WS.dlFree SysI progS psys₀ a1 K₀

  -- (P4) … and never diverges
  psys-divergenceFree : DivergenceFree (psys l)
  psys-divergenceFree = Gen.divFree l SysA psys₀

  -- (P5) WITH THE SERVER APPLICATION SILENT (all five server api sends refused, incl.
  -- `lnpSendCanceled`) THE PIPELINED SYSTEM NEVER GETS STUCK.  Contrast `blk-deadlock l :
  -- HasDeadlock (blk l)` for the non-pipelined pair: there "RequestNext sent" is a stall;
  -- here the busy client can still quit (`progJ b2`) and the read-ahead server answers the
  -- held request with MsgCanceled (`progJ x2`)
  pblk-deadlockFree : DeadlockFree pblk
  pblk-deadlockFree = WB.dlFree BlkI progB pblk₀ a1 K₀

  -- (P2) QUIT COMPLETES WITHOUT THE SERVER APPLICATION.  With every server api send refused,
  -- once the client's quit command `lnpSendDone` has occurred in a trace — from StIdle or
  -- PIPELINED with a request outstanding — the rest is deadlock-free, divergence-free and has
  -- at most 8 visible events; so every run from there is finite and ends in √ (an infinite
  -- run would diverge, a maximal finite run that is not stuck has √ available).  8 is tight
  -- (`pblk-tight`): RequestNext still in the client→server FIFO when the quit is commanded,
  -- then MsgQuit sent, RequestNext received, MsgQuit read ahead, MsgCanceled sent, drained,
  -- done, MsgDone sent, received
  pblk-afterQuit : ∀ {s W} → pblk ⟹∖√⟨ s ⟩ W → Any (QuitApi l) s
                 → DeadlockFree W × DivergenceFree W × (∀ {s′ W′} → W ⟹∖√⟨ s′ ⟩ W′ → length s′ ≤ 8)
  pblk-afterQuit = WBB.afterQuit BlkI progB pblk₀ a1 K₀

  ------------------------------------------------------------------------
  -- §9  (P1) Protocol-order table conformance
  ------------------------------------------------------------------------

  -- once MsgDone has been sent nothing is left unanswered
  shut : ∀ {c s b₁ b₂} (j : J c s b₁ b₂) → T (clJ j) → pkJ j ≡ k0
  shut q5     _ = refl
  shut q6     _ = refl
  shut (x8 _) _ = refl
  shut a1     ()
  shut a2     ()
  shut (a3 _) ()
  shut b1     ()
  shut b2     ()
  shut (b3 _) ()
  shut (b4 _) ()
  shut q1     ()
  shut q2     ()
  shut q3     ()
  shut q4     ()
  shut p1     ()
  shut p2     ()
  shut (p3 _) ()
  shut (p4 _) ()
  shut x1     ()
  shut x2     ()
  shut (x3 _) ()
  shut (x4 _) ()
  shut x5     ()
  shut (x6 _) ()
  shut (x7 _) ()

  -- THE PAIRING FACTS of a trace `s`: the client's messages `cm s` are the answered ones
  -- `cs₀` followed by the unanswered ones `pl k` (nothing, RequestNext, MsgQuit, or the
  -- pipelined RequestNext·MsgQuit); `cs₀` is paired one-to-one, in order, with the server's
  -- messages `sm s` (`Ans`); and once MsgDone is sent nothing is unanswered
  Pair : List Event → Set
  Pair s = Σ[ cs₀ ∈ List Payload ] Σ[ k ∈ PK ] Σ[ b ∈ Bool ]
             (cm s ≡ cs₀ ++ pl k × Ans b cs₀ (sm s) × (T b → k ≡ k0))

  -- the pairing facts, read off the protocol-order invariant at the end of a run
  toPair : ∀ {σ s} {P : JJ σ → Set₁} → Σ[ j′ ∈ JJ σ ] (K j′ (cm s) (sm s) × P j′) → Pair s
  toPair (j′ , (cs₀ , eq , a) , _) = cs₀ , pkJ j′ , clJ j′ , eq , a , shut j′

  -- (P1) THE PROTOCOL-ORDER PAIRING holds of every √-free trace of the pipelined system
  psys-pairing : ∀ {s W} → psys l ⟹∖√⟨ s ⟩ W → Pair s
  psys-pairing {s} r = toPair {σ = proj₁ ru} {s = s} (WS.walk (proj₁ (proj₂ ru)) a1 K₀)
    where
    -- the abstract run
    ru = Gen.runE l SysA psys₀ r

  -- (… and of the blocked system)
  pblk-pairing : ∀ {s W} → pblk ⟹∖√⟨ s ⟩ W → Pair s
  pblk-pairing {s} r = toPair {σ = proj₁ (proj₁ ru)} {s = s} (WB.walk (proj₁ (proj₂ ru)) a1 K₀)
    where
    -- the abstract run
    ru = Gen.runE l BlkA pblk₀ r

  -- THE PROTOCOL-ORDER SEQUENCE of client messages `cs` and server messages `ss`, as the
  -- client end `(l , lo)` names them (sent / received): c₁ s₁ c₂ s₂ … — and, once the
  -- server's messages run out, only the FIRST unanswered client message (a pipelined
  -- MsgQuit behind an unanswered RequestNext has no place in the table order yet: its
  -- predecessor's answer must come first)
  alt : List Payload → List Payload → List Event
  alt []       _        = []
  alt (c ∷ _)  []       = ⌞ wS lo c ⌟ ∷ []
  alt (c ∷ cs) (x ∷ xs) = ⌞ wS lo c ⌟ ∷ ⌞ wR lo x ⌟ ∷ alt cs xs

  -- the sequence of a paired prefix followed by unanswered messages
  alt-pend : ∀ {b cs₀ ss} → Ans b cs₀ ss → ∀ ys → alt (cs₀ ++ ys) ss ≡ alt cs₀ ss ++ alt ys []
  alt-pend aε       _  = refl
  alt-pend (aR _ a) ys = cong (λ z → _ ∷ _ ∷ z) (alt-pend a ys)
  alt-pend aQ       _  = refl

  -- the table after a paired prefix: StIdle, or End once MsgDone was sent
  specAt : Bool → Tree
  specAt false = LNPSpec l
  specAt true  = specEnd l

  -- table row StBusy --reply--> StIdle, for every reply
  rowRep : ∀ {x} → RepP x → vOf (specStep l tBusy) (_ , receiveLNP l lo) x ≡ just (Ret (inj₁ tIdle))
  rowRep (rpA {tm} {md} {ln} h)    = tAnn l {tm} {md} {ln} h
  rowRep (rpO {tm} {md} {ln} q sz) = tOff l {tm} {md} {ln} q sz
  rowRep (rpT {tm} {md} {ln} q)    = tTxs l {tm} {md} {ln} q
  rowRep (rpV {tm} {md} {ln} vs)   = tVot l {tm} {md} {ln} vs
  rowRep (rpC {tm} {md} {ln})      = tCan l {tm} {md} {ln}

  -- a paired prefix is a table run
  ans-run : ∀ {b cs ss} → Ans b cs ss → ∀ {s r} → specAt b ⟹∖√⟨ s ⟩ r → LNPSpec l ⟹∖√⟨ alt cs ss ++ s ⟩ r
  ans-run aε       rest = rest
  ans-run (aR k a) rest = spGo l tIdle (tReq l {time₀} {FromInitiator} {length₀}) (spGo l tBusy (rowRep k) (ans-run a rest))
  ans-run aQ       rest = spGo l tIdle (tQt l {time₀} {FromInitiator} {length₀})
                            (spEnd l (tDone l {time₀} {FromResponder} {length₀}) rest)

  -- the table state after the first unanswered client message
  tgt : Bool → PK → Tree
  tgt b k0  = specAt b
  tgt _ kR  = iter (specStep l) tBusy
  tgt _ kQ  = iter (specStep l) tQuit
  tgt _ kRQ = iter (specStep l) tBusy

  -- the first unanswered client message is a table row from StIdle
  pend-run : ∀ b k → (T b → k ≡ k0) → specAt b ⟹∖√⟨ alt (pl k) [] ⟩ tgt b k
  pend-run b     k0  _  = ∖√-refl
  pend-run false kR  _  = spGo l tIdle (tReq l {time₀} {FromInitiator} {length₀}) ∖√-refl
  pend-run false kQ  _  = spGo l tIdle (tQt l {time₀} {FromInitiator} {length₀}) ∖√-refl
  pend-run false kRQ _  = spGo l tIdle (tReq l {time₀} {FromInitiator} {length₀}) ∖√-refl
  pend-run true  kR  sh with () ← sh U.tt
  pend-run true  kQ  sh with () ← sh U.tt
  pend-run true  kRQ sh with () ← sh U.tt

  -- a pairing has equal lengths
  ans-len : ∀ {b cs ss} → Ans b cs ss → length cs ≡ length ss
  ans-len aε       = refl
  ans-len (aR _ a) = cong suc (ans-len a)
  ans-len aQ       = refl

  -- the client has terminated only at its End phase
  cEnd? : ∀ {c f} → CFin (c , f) → c ≡ cEnd
  cEnd? {cEnd} _ = refl
  cEnd? {cIdle}   ()
  cEnd? {cBusy}   ()
  cEnd? {cQuit}   ()
  cEnd? {cSndRN}  ()
  cEnd? {cSndQ}   ()
  cEnd? {cSndPQ}  ()
  cEnd? {cDrain}  ()
  cEnd? {cDlv _}  ()

  -- … where the table has terminated too
  endTgt : ∀ {s b₁ b₂} (j : J cEnd s b₁ b₂) → PTree.force (tgt (clJ j) (pkJ j)) ≡ ret tt
  endTgt q6 = refl

  -- (P1) PROTOCOL-ORDER TABLE CONFORMANCE: for every √-free trace `s` of the pipelined
  -- system, the protocol-order sequence of its client messages `cm s` and server messages
  -- `sm s` is a trace of the blueprint table `LNPSpec` (reused from `LeiosNotifyQuit`), and
  -- if the system has terminated so has the table there.  CAUSALITY: the server never sends
  -- more messages than the client (`length (sm s) ≤ length (cm s)`; as traces are prefix
  -- closed, the i-th server message is sent after the i-th client message).  Hence any
  -- MsgCanceled (0 or more, api-commanded or read-ahead) precede MsgQuit in protocol order,
  -- and MsgQuit is answered by MsgDone only
  psys-protocolOrder : ∀ {s W} → psys l ⟹∖√⟨ s ⟩ W
    → (Σ[ W′ ∈ Tree ] (LNPSpec l ⟹∖√⟨ alt (cm s) (sm s) ⟩ W′ × (PTree.force W ≡ ret tt → PTree.force W′ ≡ ret tt)))
      × length (sm s) ≤ length (cm s)
  psys-protocolOrder {s} {W} r with Gen.runE l SysA psys₀ r
  ... | _ , ar , p′ with WS.walk ar a1 K₀
  ...   | j′ , (cs₀ , eq , a) , _ = (tgt (clJ j′) (pkJ j′) , run , finT) , causal
    where
    -- the table run, via the pairing
    run : LNPSpec l ⟹∖√⟨ alt (cm s) (sm s) ⟩ tgt (clJ j′) (pkJ j′)
    run = subst (λ z → LNPSpec l ⟹∖√⟨ z ⟩ tgt (clJ j′) (pkJ j′))
                (sym (trans (cong (λ z → alt z (sm s)) eq) (alt-pend a (pl (pkJ j′)))))
                (ans-run a (pend-run (clJ j′) (pkJ j′) (shut j′)))
    -- termination of the system is termination of the client, at `q6`
    finT : PTree.force W ≡ ret tt → PTree.force (tgt (clJ j′) (pkJ j′)) ≡ ret tt
    finT e with Abs.elimR SysA p′ e
    ... | (cf , _) , _ with cEnd? cf
    ...   | refl = endTgt j′
    -- the server's messages are as many as the answered client messages
    causal : length (sm s) ≤ length (cm s)
    causal = subst₂ _≤_ (ans-len a) (sym (trans (cong length eq) (length-++ cs₀)))
                    (m≤m+n (length cs₀) (length (pl (pkJ j′))))

  ------------------------------------------------------------------------
  -- §10  (P3) The shutdown shape
  ------------------------------------------------------------------------

  -- what the server sends after MsgQuit, when MsgQuit was sent with k requests
  -- outstanding: (a prefix of) k replies, then MsgDone
  data QuitTail : ℕ → List Payload → Set where
    qt0   : QuitTail 0 []
    qt0D  : QuitTail 0 (pD ∷ [])
    qt1   : QuitTail 1 []
    qt1R  : ∀ {x} → RepP x → QuitTail 1 (x ∷ [])
    qt1RD : ∀ {x} → RepP x → QuitTail 1 (x ∷ pD ∷ [])

  -- the client's message sequences: RequestNexts, possibly closed by one MsgQuit
  data RQ : List Payload → Set where
    rqε : RQ []
    rqR : ∀ {cs} → RQ cs → RQ (pRN ∷ cs)
    rqQ : RQ (pQ ∷ [])

  -- a pairing and its unanswered messages have that shape
  shape : ∀ {b cs₀ ss} → Ans b cs₀ ss → ∀ k → (T b → k ≡ k0) → RQ (cs₀ ++ pl k)
  shape aε       k0  _  = rqε
  shape aε       kR  _  = rqR rqε
  shape aε       kQ  _  = rqQ
  shape aε       kRQ _  = rqR rqQ
  shape (aR _ a) k   sh = rqR (shape a k sh)
  shape aQ       k   sh with sh U.tt
  ... | refl = rqQ

  -- in that shape MsgQuit is last, and everything before it is RequestNext
  rq-split : ∀ as {bs} → RQ (as ++ pQ ∷ bs) → bs ≡ [] × All (_≡ pRN) as
  rq-split []           rqQ     = refl , []
  rq-split (_ ∷ [])     (rqR q) = proj₁ (rq-split [] q) , refl ∷ []
  rq-split (_ ∷ a ∷ as) (rqR q) = proj₁ (rq-split (a ∷ as) q) , refl ∷ proj₂ (rq-split (a ∷ as) q)

  -- unanswered messages that are all RequestNext: none, or one
  kOK : ∀ k → All (_≡ pRN) (pl k) → k ≡ k0 ⊎ k ≡ kR
  kOK k0  _            = inj₁ refl
  kOK kR  _            = inj₂ refl
  kOK kQ  (() ∷ _)
  kOK kRQ (_ ∷ () ∷ _)

  -- a pairing of RequestNexts only has not been closed by MsgDone
  ans-noQ : ∀ {b cs ss} → Ans b cs ss → All (_≡ pRN) cs → b ≡ false
  ans-noQ aε       _        = refl
  ans-noQ (aR _ a) (_ ∷ al) = ans-noQ a al
  ans-noQ aQ       (() ∷ _)

  -- a list equation with a shorter left prefix splits
  pfx : ∀ (as : List Payload) {bs cs ds} → length as ≤ length cs → as ++ bs ≡ cs ++ ds
      → Σ[ ys ∈ List Payload ] (cs ≡ as ++ ys × bs ≡ ys ++ ds)
  pfx []       {cs = cs}     _       e = cs , refl , e
  pfx (_ ∷ _)  {cs = []}     ()      _
  pfx (_ ∷ as) {cs = _ ∷ cs} (s≤s le) e with ∷-injective e
  ... | refl , e′ with pfx as {cs = cs} le e′
  ...   | ys , refl , e″ = ys , refl , e″

  -- an open pairing is a prefix of any extension of it
  ans-split : ∀ {b cs₁ ys ss₁ ss₂} → Ans false cs₁ ss₁ → Ans b (cs₁ ++ ys) (ss₁ ++ ss₂) → Ans b ys ss₂
  ans-split aε        a         = a
  ans-split (aR _ a₁) (aR _ a₂) = ans-split a₁ a₂

  -- the answers to the messages from MsgQuit's predecessor on
  tailQ : ∀ {k₁ ys k b ss} → k₁ ≡ k0 ⊎ k₁ ≡ kR → pl k₁ ++ pQ ∷ [] ≡ ys ++ pl k → Ans b ys ss
        → QuitTail (length (pl k₁)) ss
  tailQ (inj₁ refl) _  aε               = qt0
  tailQ (inj₁ refl) _  aQ               = qt0D
  tailQ (inj₁ refl) () (aR _ _)
  tailQ (inj₂ refl) _  aε               = qt1
  tailQ (inj₂ refl) _  (aR k aε)        = qt1R k
  tailQ (inj₂ refl) _  (aR k aQ)        = qt1RD k
  tailQ (inj₂ refl) () (aR _ (aR _ _))
  tailQ (inj₂ refl) () aQ

  -- the client's messages of a concatenated trace
  cm-++ : ∀ s₁ s₂ → cm (s₁ ++ s₂) ≡ cm s₁ ++ cm s₂
  cm-++ []       _  = refl
  cm-++ (e ∷ s₁) s₂ = trans (cong (cmE e ++_) (cm-++ s₁ s₂)) (sym (++-assoc (cmE e) (cm s₁) (cm s₂)))

  -- the server's messages of a concatenated trace
  sm-++ : ∀ s₁ s₂ → sm (s₁ ++ s₂) ≡ sm s₁ ++ sm s₂
  sm-++ []       _  = refl
  sm-++ (e ∷ s₁) s₂ = trans (cong (smE e ++_) (sm-++ s₁ s₂)) (sym (++-assoc (smE e) (sm s₁) (sm s₂)))

  -- a run of a concatenated trace passes through a state after the first part
  pre : ∀ {t W : Tree} s₁ {s₂} → t ⟹∖√⟨ s₁ ++ s₂ ⟩ W → Σ[ W₁ ∈ Tree ] (t ⟹∖√⟨ s₁ ⟩ W₁ × W₁ ⟹∖√⟨ s₂ ⟩ W)
  pre []       r            = _ , ∖√-refl , r
  pre (e ∷ s₁) (∖√-τ st r)  with pre (e ∷ s₁) r
  ... | _ , r₁ , r₂ = _ , ∖√-τ st r₁ , r₂
  pre (e ∷ s₁) (∖√-ev st r) with pre s₁ r
  ... | _ , r₁ , r₂ = _ , ∖√-ev st r₁ , r₂

  -- THE SHAPE, from the pairing facts before MsgQuit is sent and at any later point
  quitCore : ∀ s₁ s₂ → Pair s₁ → Pair (s₁ ++ ⌞ wS lo pQ ⌟ ∷ s₂)
           → cm s₂ ≡ [] × QuitTail (length (cm s₁) ∸ length (sm s₁)) (sm s₂)
  quitCore s₁ s₂ (cs₁ , k₁ , b₁ , e₁ , a₁ , _) (cs₀ , k , b , e , a , h) = cm₂ , subst (λ n → QuitTail n (sm s₂)) (sym kIs) qt
    where
    -- the client's messages: those before, MsgQuit, those after
    cmS : cs₀ ++ pl k ≡ cm s₁ ++ pQ ∷ cm s₂
    cmS = trans (sym e) (cm-++ s₁ (⌞ wS lo pQ ⌟ ∷ s₂))
    -- MsgQuit is the client's last message, and everything before it is RequestNext
    split : cm s₂ ≡ [] × All (_≡ pRN) (cm s₁)
    split = rq-split (cm s₁) (subst RQ cmS (shape a k h))
    -- nothing after MsgQuit
    cm₂ : cm s₂ ≡ []
    cm₂ = proj₁ split
    -- before MsgQuit: RequestNexts only
    allRN : All (_≡ pRN) (cs₁ ++ pl k₁)
    allRN = subst (All (_≡ pRN)) e₁ (proj₂ split)
    -- so at most one was unanswered, and MsgDone was not yet sent
    kk : k₁ ≡ k0 ⊎ k₁ ≡ kR
    kk = kOK k₁ (++⁻ʳ cs₁ allRN)
    -- (the pairing before MsgQuit is open)
    a₁′ : Ans false cs₁ (sm s₁)
    a₁′ = subst (λ z → Ans z cs₁ (sm s₁)) (ans-noQ a₁ (++⁻ˡ cs₁ allRN)) a₁
    -- the answered prefix grew from `cs₁` to `cs₀`
    le : length cs₁ ≤ length cs₀
    le = subst₂ _≤_ (sym (ans-len a₁)) (sym (trans (ans-len a) (cong length (sm-++ s₁ (⌞ wS lo pQ ⌟ ∷ s₂)))))
                (subst (length (sm s₁) ≤_) (sym (length-++ (sm s₁))) (m≤m+n (length (sm s₁)) (length (sm s₂))))
    -- the whole client sequence, both ways
    whole : cs₁ ++ (pl k₁ ++ pQ ∷ []) ≡ cs₀ ++ pl k
    whole = trans (sym (++-assoc cs₁ (pl k₁) (pQ ∷ [])))
                  (trans (cong (λ z → z ++ pQ ∷ []) (sym e₁))
                         (trans (cong (λ z → cm s₁ ++ pQ ∷ z) (sym cm₂)) (sym cmS)))
    -- the newly answered messages
    sp : Σ[ ys ∈ List Payload ] (cs₀ ≡ cs₁ ++ ys × pl k₁ ++ pQ ∷ [] ≡ ys ++ pl k)
    sp = pfx cs₁ le whole
    -- … are answered by the server's messages after MsgQuit
    aT : Ans b (proj₁ sp) (sm s₂)
    aT = ans-split a₁′ (subst₂ (Ans b) (proj₁ (proj₂ sp)) (sm-++ s₁ (⌞ wS lo pQ ⌟ ∷ s₂)) a)
    -- the shape
    qt : QuitTail (length (pl k₁)) (sm s₂)
    qt = tailQ kk (proj₂ (proj₂ sp)) aT
    -- the number outstanding when MsgQuit was sent
    kIs : length (cm s₁) ∸ length (sm s₁) ≡ length (pl k₁)
    kIs = trans (cong₂ _∸_ (trans (cong length e₁) (length-++ cs₁)) (sym (ans-len a₁)))
                (m+n∸m≡n (length cs₁) (length (pl k₁)))

  -- (P3) THE SHUTDOWN SHAPE.  If MsgQuit is sent (the client's `sendLNP l lo` of MsgQuit) after
  -- a trace `s₁` with k = |client messages| ∸ |server messages| requests outstanding, then
  -- k ≤ 1 (`QuitTail` has only the indices 0 and 1), the client sends nothing more
  -- (`cm s₂ ≡ []`), and the server's messages after it are (a prefix of) k replies — each
  -- answering an outstanding RequestNext — followed by MsgDone.  With P1 this is: in
  -- protocol order the k outstanding requests are answered before MsgQuit, and MsgDone
  -- follows MsgQuit.  Which of those replies are MsgCanceled is `psys-attribution` /
  -- `pblk-quitShape`
  psys-quitShape : ∀ {s₁ s₂ W} → psys l ⟹∖√⟨ s₁ ++ ⌞ wS lo pQ ⌟ ∷ s₂ ⟩ W
                 → cm s₂ ≡ [] × QuitTail (length (cm s₁) ∸ length (sm s₁)) (sm s₂)
  psys-quitShape {s₁} {s₂} r = quitCore s₁ s₂ (psys-pairing (proj₁ (proj₂ (pre s₁ r)))) (psys-pairing r)

  ------------------------------------------------------------------------
  -- §11  (P3) Who answers: the server application, or MsgCanceled
  ------------------------------------------------------------------------

  -- a notification message counts 1
  isN : Payload → ℕ
  isN (_ , _ , _ , leiosNotifyP (MsgLNPBlockAnnouncement _)) = 1
  isN (_ , _ , _ , leiosNotifyP (MsgLNPBlockOffer _ _))      = 1
  isN (_ , _ , _ , leiosNotifyP (MsgLNPBlockTxsOffer _))     = 1
  isN (_ , _ , _ , leiosNotifyP (MsgLNPVotes _))             = 1
  isN _                                                      = 0

  -- the notifications among messages
  nN : List Payload → ℕ
  nN []       = 0
  nN (x ∷ xs) = isN x + nN xs

  -- (over a concatenation)
  nN-++ : ∀ xs ys → nN (xs ++ ys) ≡ nN xs + nN ys
  nN-++ []       _  = refl
  nN-++ (x ∷ xs) ys = trans (cong (isN x +_) (nN-++ xs ys)) (sym (+-assoc (isN x) (nN xs) (nN ys)))

  -- a server notification command counts 1
  cntTag : ApiLPTag → ℕ
  cntTag lnpSendBlockAnnouncement = 1
  cntTag lnpSendBlockOffer        = 1
  cntTag lnpSendBlockTxsOffer     = 1
  cntTag lnpSendVotes             = 1
  cntTag _                        = 0

  -- the server application's notification commands in an event
  cmdE : Event → ℕ
  cmdE (evLabel _ (apiLPev _ hi m) _) = cntTag m
  cmdE _                              = 0

  -- … in a trace
  nCmd : List Event → ℕ
  nCmd []      = 0
  nCmd (e ∷ s) = cmdE e + nCmd s

  -- a commanded notification not yet sent
  spc : SPh → ℕ
  spc (sRep (rA _))   = 1
  spc (sRep (rO _ _)) = 1
  spc (sRep (rT _))   = 1
  spc (sRep (rV _))   = 1
  spc _               = 0

  -- (of a system state)
  pcS : SysS → ℕ
  pcS σ = spc (proj₁ (proj₂ (proj₁ σ)))

  -- a client step neither commands nor sends a notification of the server
  cz : ∀ {ω} n → CAl l ω → nN (smE ⌞ ω ⌟) + n ≡ n + cmdE ⌞ ω ⌟
  cz n (caS _)   = sym (+-identityʳ n)
  cz n (caR _)   = sym (+-identityʳ n)
  cz n (caA _ _) = sym (+-identityʳ n)

  -- a server step: a command is counted until its notification is sent
  sz : ∀ {σs ω σs′} → SSt σs (ev′ ω) σs′ → nN (smE ⌞ ω ⌟) + spc (proj₁ σs′) ≡ spc (proj₁ σs) + cmdE ⌞ ω ⌟
  sz sRN            = refl
  sz sQi            = refl
  sz (sAp (rA _))   = refl
  sz (sAp (rO _ _)) = refl
  sz (sAp (rT _))   = refl
  sz (sAp (rV _))   = refl
  sz (sAp rC)       = refl
  sz sRA            = refl
  sz (sNx (rA _))   = refl
  sz (sNx (rO _ _)) = refl
  sz (sNx (rT _))   = refl
  sz (sNx (rV _))   = refl
  sz (sNx rC)       = refl
  sz sCx            = refl
  sz sDn            = refl
  sz sDS            = refl

  -- every visible system step keeps the count
  cntV : ∀ {σ ω σ′} → Abs.Stp SysA σ (ev′ ω) σ′ → nN (smE ⌞ ω ⌟) + pcS σ′ ≡ pcS σ + cmdE ⌞ ω ⌟
  cntV (PT.psy _ (PP.psL _ c) _)     = cz _ (cAlpha c)
  cntV (PT.psy _ (PP.psR _ s) _)     = sz s
  cntV (PT.psy _ (PP.psy () _ _) _)
  cntV (PT.psL _ (PP.psL _ c))       = cz _ (cAlpha c)
  cntV (PT.psL _ (PP.psR _ s))       = sz s
  cntV (PT.psL _ (PP.psy () _ _))
  cntV (PT.psR ¬w (PB.psL _ b))      = ⊥-elim (¬w (chW (inj₁ (F₁.fAlpha b))))
  cntV (PT.psR ¬w (PB.psR _ b))      = ⊥-elim (¬w (chW (inj₂ (F₂.fAlpha b))))
  cntV (PT.psR _ (PB.psy () _ _))

  -- … and every τ
  cntτ : ∀ {σ σ′} → Abs.Stp SysA σ τ′ σ′ → pcS σ′ ≡ pcS σ
  cntτ (PT.pτL (PP.pτL cτ))    = refl
  cntτ (PT.pτL (PP.pτR sτ))    = refl
  cntτ (PT.pτR (PB.pτL F₁.fτ)) = refl
  cntτ (PT.pτR (PB.pτR F₂.fτ)) = refl

  -- a server api send of a notification is in the blocked set
  cnt0 : ∀ m → ¬ T (srvCmd l m) → cntTag m ≡ 0
  cnt0 lnpSendRequestNext       _  = refl
  cnt0 lnpSendDone              _  = refl
  cnt0 lnpSendBlockAnnouncement ¬s = ⊥-elim (¬s U.tt)
  cnt0 lnpSendBlockOffer        ¬s = ⊥-elim (¬s U.tt)
  cnt0 lnpSendBlockTxsOffer     ¬s = ⊥-elim (¬s U.tt)
  cnt0 lnpSendVotes             ¬s = ⊥-elim (¬s U.tt)
  cnt0 lnpSendCanceled          _  = refl
  cnt0 lnpRecvBlockAnnouncement _  = refl
  cnt0 lnpRecvBlockOffer        _  = refl
  cnt0 lnpRecvBlockTxsOffer     _  = refl
  cnt0 lnpRecvVotes             _  = refl
  cnt0 lfpSendBlockRequest      _  = refl
  cnt0 lfpSendBlockTxsRequest   _  = refl
  cnt0 lfpSendDone              _  = refl
  cnt0 lfpSendBlock             _  = refl
  cnt0 lfpSendBlockTxs          _  = refl
  cnt0 lfpRecvBlock             _  = refl
  cnt0 lfpRecvBlockTxs          _  = refl
  cnt0 lfpReqBlockRequest       _  = refl
  cnt0 lfpReqBlockTxsRequest    _  = refl

  -- a label off the blocked set commands no notification
  cmd0 : ∀ ω → ¬ InE l (srvApi l) ω → cmdE ⌞ ω ⌟ ≡ 0
  cmd0 (wS _ _)    _  = refl
  cmd0 (wR _ _)    _  = refl
  cmd0 (ap lo _ _) _  = refl
  cmd0 (ap hi m _) ¬s = cnt0 m ¬s
  cmd0 (dn _)      _  = refl

  -- the count along any run of a system
  module Count {S : Set} (A : Abs l S) (π : S → SysS)
               (un : ∀ {σ ℓ σ′} → Abs.Stp A σ ℓ σ′ → Abs.Stp SysA (π σ) ℓ (π σ′)) where
    open Gen l A using (ARun; r0; rτ; rE)

    -- notifications sent + the one commanded and pending = notification commands
    cnt : ∀ {σ s σ′} → ARun σ s σ′ → nN (sm s) + pcS (π σ′) ≡ pcS (π σ) + nCmd s
    cnt r0 = sym (+-identityʳ _)
    cnt (rτ a ar) = trans (cnt ar) (cong (_+ _) (cntτ (un a)))
    cnt (rE {s = s} {ω = ω} a ar) =
      trans (cong (_+ _) (nN-++ (smE ⌞ ω ⌟) (sm s)))
      (trans (+-assoc (nN (smE ⌞ ω ⌟)) (nN (sm s)) _)
      (trans (cong (nN (smE ⌞ ω ⌟) +_) (cnt ar))
      (trans (sym (+-assoc (nN (smE ⌞ ω ⌟)) _ (nCmd s)))
      (trans (cong (_+ nCmd s) (cntV (un a)))
             (+-assoc _ (cmdE ⌞ ω ⌟) (nCmd s))))))

  -- the count of the pipelined system
  module CS = Count SysA (λ σ → σ) (λ a → a)
  -- the count of the blocked system
  module CB = Count BlkA proj₁ unblk

  -- the blocked system's runs command nothing
  noCmd : ∀ {σ s σ′} → Gen.ARun l BlkA σ s σ′ → nCmd s ≡ 0
  noCmd (Gen.r0)       = refl
  noCmd (Gen.rτ _ ar)  = noCmd ar
  noCmd (Gen.rE {ω = ω} a ar) = trans (cong (_+ _) (cmd0 ω (offB a))) (noCmd ar)

  -- (P3) ATTRIBUTION: every notification the server sends was commanded by its application
  -- (`lnpSend{BlockAnnouncement,BlockOffer,BlockTxsOffer,Votes}`); so a reply that the
  -- application did not command is MsgCanceled
  psys-attribution : ∀ {s W} → psys l ⟹∖√⟨ s ⟩ W → nN (sm s) ≤ nCmd s
  psys-attribution {s} r with Gen.runE l SysA psys₀ r
  ... | σ′ , ar , _ = subst (nN (sm s) ≤_) (CS.cnt ar) (m≤m+n (nN (sm s)) (pcS σ′))

  -- (P3) … in particular, with the server application silent, the server sends no
  -- notification at all: every reply is MsgCanceled
  pblk-noNotification : ∀ {s W} → pblk ⟹∖√⟨ s ⟩ W → nN (sm s) ≡ 0
  pblk-noNotification {s} r = m+n≡0⇒m≡0 (nN (sm s)) (trans (CB.cnt ar) (noCmd ar))
    where
    -- the abstract run
    ar = proj₁ (proj₂ (Gen.runE l BlkA pblk₀ r))

  -- the shutdown tail with every reply MsgCanceled
  data QuitTailC : ℕ → List Payload → Set where
    qc0   : QuitTailC 0 []
    qc0D  : QuitTailC 0 (pD ∷ [])
    qc1   : QuitTailC 1 []
    qc1C  : ∀ {tm md ln} → QuitTailC 1 ((tm , md , ln , leiosNotifyP MsgLNPCanceled) ∷ [])
    qc1CD : ∀ {tm md ln} → QuitTailC 1 ((tm , md , ln , leiosNotifyP MsgLNPCanceled) ∷ pD ∷ [])

  -- a shutdown tail without notifications has only MsgCanceled replies
  toC : ∀ {k ss} → QuitTail k ss → nN ss ≡ 0 → QuitTailC k ss
  toC qt0             _ = qc0
  toC qt0D            _ = qc0D
  toC qt1             _ = qc1
  toC (qt1R rpC)      _ = qc1C
  toC (qt1RD rpC)     _ = qc1CD
  toC (qt1R (rpA _))  ()
  toC (qt1R (rpO _ _)) ()
  toC (qt1R (rpT _))  ()
  toC (qt1R (rpV _))  ()
  toC (qt1RD (rpA _))  ()
  toC (qt1RD (rpO _ _)) ()
  toC (qt1RD (rpT _))  ()
  toC (qt1RD (rpV _))  ()

  -- (P3) THE SHUTDOWN SHAPE WITH THE SERVER APPLICATION SILENT: as `psys-quitShape`, and the
  -- outstanding request (k = 1) is answered by MsgCanceled — the read-ahead
  pblk-quitShape : ∀ {s₁ s₂ W} → pblk ⟹∖√⟨ s₁ ++ ⌞ wS lo pQ ⌟ ∷ s₂ ⟩ W
                 → cm s₂ ≡ [] × QuitTailC (length (cm s₁) ∸ length (sm s₁)) (sm s₂)
  pblk-quitShape {s₁} {s₂} r with quitCore s₁ s₂ (pblk-pairing (proj₁ (proj₂ (pre s₁ r)))) (pblk-pairing r)
  ... | cm₂ , qt = cm₂ , toC qt n₂
    where
    -- no notification after MsgQuit either
    n₂ : nN (sm s₂) ≡ 0
    n₂ = m+n≡0⇒n≡0 (nN (sm s₁))
           (trans (sym (nN-++ (sm s₁) (sm s₂)))
                  (trans (cong nN (sym (sm-++ s₁ (⌞ wS lo pQ ⌟ ∷ s₂)))) (pblk-noNotification r)))

  ------------------------------------------------------------------------
  -- §12  (P5, P2) Concrete runs of the blocked system
  ------------------------------------------------------------------------

  -- the terminated state of the blocked system
  σE : SysS × U.⊤
  σE = (((cEnd , false) , (sEnd , false)) , ((bEnd , false) , (bEnd , false))) , U.tt

  -- every component has terminated there
  finE : Abs.Fin BlkA σE
  finE = ((U.tt , U.tt) , (U.tt , U.tt)) , U.tt

  -- a run of the blocked system to its terminated state is a concrete run to √
  runTo√ : ∀ {σ s} → Gen.ARun l BlkA σ s σE → ∀ {t} → Abs.Pos BlkA σ t
         → Σ[ W ∈ Tree ] (t ⟹∖√⟨ s ⟩ W × PTree.force W ≡ ret tt)
  runTo√ ar p = proj₁ ri , proj₁ (proj₂ ri) , AbsI.introR BlkI (proj₂ (proj₂ ri)) finE
    where
    -- the concrete run
    ri = GenI.runI l BlkI ar p

  -- the trace of (P5): RequestNext commanded, sent, RECEIVED by the server (it now holds the
  -- request — exactly `LeiosNotifyQuit.trRN`'s situation, there a stall); then the client's
  -- quit command, MsgQuit, read ahead by the server, MsgCanceled sent and drained, the
  -- server's done, MsgDone sent and received
  trP : List Event
  trP = ⌞ ap lo lnpSendRequestNext U.tt ⌟ ∷ ⌞ wS lo pRN ⌟ ∷ ⌞ wR hi pRN ⌟
      ∷ ⌞ ap lo lnpSendDone U.tt ⌟ ∷ ⌞ wS lo pQ ⌟ ∷ ⌞ wR hi pQ ⌟ ∷ ⌞ wS hi pC ⌟ ∷ ⌞ wR lo pC ⌟
      ∷ ⌞ dn hi ⌟ ∷ ⌞ wS hi pD ⌟ ∷ ⌞ wR lo pD ⌟ ∷ []

  -- its abstract run, to the terminated state
  runP : Gen.ARun l BlkA (σ₀ , U.tt) trP σE
  runP =
    rE (PX.psL (λ ()) (PT.psL (λ ()) (PP.psL (λ ()) (cRN U.tt))))
    (rE (PX.psL (λ ()) (PT.psy U.tt (PP.psL (λ ()) cSR) (PB.psL (λ ()) (F₁.fI0 _))))
    (rτ (PX.pτL (PT.pτL (PP.pτL cτ)))
    (rτ (PX.pτL (PT.pτR (PB.pτL F₁.fτ)))
    (rE (PX.psL (λ ()) (PT.psy U.tt (PP.psR (λ ()) sRN) (PB.psL (λ ()) (F₁.fO1 _))))
    (rτ (PX.pτL (PT.pτL (PP.pτR sτ)))
    (rτ (PX.pτL (PT.pτR (PB.pτL F₁.fτ)))
    (rE (PX.psL (λ ()) (PT.psL (λ ()) (PP.psL (λ ()) (cQp U.tt))))
    (rE (PX.psL (λ ()) (PT.psy U.tt (PP.psL (λ ()) cSP) (PB.psL (λ ()) (F₁.fI0 _))))
    (rτ (PX.pτL (PT.pτR (PB.pτL F₁.fτ)))
    (rE (PX.psL (λ ()) (PT.psy U.tt (PP.psR (λ ()) sRA) (PB.psL (λ ()) (F₁.fO1 _))))
    (rE (PX.psL (λ ()) (PT.psy U.tt (PP.psR (λ ()) sCx) (PB.psR (λ ()) (F₂.fI0 _))))
    (rτ (PX.pτL (PT.pτL (PP.pτR sτ)))
    (rτ (PX.pτL (PT.pτR (PB.pτR F₂.fτ)))
    (rE (PX.psL (λ ()) (PT.psy U.tt (PP.psL (λ ()) (cDr rpC)) (PB.psR (λ ()) (F₂.fO1 _))))
    (rτ (PX.pτL (PT.pτL (PP.pτL cτ)))
    (rτ (PX.pτL (PT.pτR (PB.pτR F₂.fτ)))
    (rE (PX.psL (λ ()) (PT.psL (λ ()) (PP.psR (λ ()) sDn)))
    (rE (PX.psL (λ ()) (PT.psy U.tt (PP.psR (λ ()) sDS) (PB.psR (λ ()) (F₂.fI0 _))))
    (rτ (PX.pτL (PT.pτR (PB.pτR F₂.fτ)))
    (rE (PX.psL (λ ()) (PT.psy U.tt (PP.psL (λ ()) cDn) (PB.psR (λ ()) (F₂.fO1 _))))
     r0))))))))))))))))))))
    where open Gen l BlkA using (rE; rτ; r0)

  -- (P5) THE PIPELINED COUNTERPART OF THE STALL.  `blk-stall l` (LeiosNotifyQuit): with the
  -- server application silent, "RequestNext commanded, sent and received" leaves the
  -- non-pipelined pair STUCK (the client in StBusy cannot quit).  Here, with the server
  -- application equally silent, the same situation continues: the client quits
  -- (pipelined), the server reads MsgQuit ahead and cancels, and the run reaches √
  pblk-quitAfterRN : Σ[ W ∈ Tree ] (pblk ⟹∖√⟨ trP ⟩ W × PTree.force W ≡ ret tt)
  pblk-quitAfterRN = runTo√ runP pblk₀

  -- the tight run of (P2): RequestNext commanded and sent (still in the FIFO), quit commanded
  trT₁ : List Event
  trT₁ = ⌞ ap lo lnpSendRequestNext U.tt ⌟ ∷ ⌞ wS lo pRN ⌟ ∷ ⌞ ap lo lnpSendDone U.tt ⌟ ∷ []

  -- … then 8 events: MsgQuit sent, RequestNext received, MsgQuit read ahead, MsgCanceled sent
  -- and drained, done, MsgDone sent and received
  trT₂ : List Event
  trT₂ = ⌞ wS lo pQ ⌟ ∷ ⌞ wR hi pRN ⌟ ∷ ⌞ wR hi pQ ⌟ ∷ ⌞ wS hi pC ⌟ ∷ ⌞ wR lo pC ⌟
       ∷ ⌞ dn hi ⌟ ∷ ⌞ wS hi pD ⌟ ∷ ⌞ wR lo pD ⌟ ∷ []

  -- the state between them
  σM : SysS × U.⊤
  σM = (((cSndPQ , false) , (sIdle , false)) , ((bq (β1 pRN) , false) , (bq β0 , false))) , U.tt

  -- the abstract run of the first part
  runT₁ : Gen.ARun l BlkA (σ₀ , U.tt) trT₁ σM
  runT₁ =
    rE (PX.psL (λ ()) (PT.psL (λ ()) (PP.psL (λ ()) (cRN U.tt))))
    (rE (PX.psL (λ ()) (PT.psy U.tt (PP.psL (λ ()) cSR) (PB.psL (λ ()) (F₁.fI0 _))))
    (rτ (PX.pτL (PT.pτL (PP.pτL cτ)))
    (rτ (PX.pτL (PT.pτR (PB.pτL F₁.fτ)))
    (rE (PX.psL (λ ()) (PT.psL (λ ()) (PP.psL (λ ()) (cQp U.tt))))
     r0))))
    where open Gen l BlkA using (rE; rτ; r0)

  -- the abstract run of the second part, to the terminated state
  runT₂ : Gen.ARun l BlkA σM trT₂ σE
  runT₂ =
    rE (PX.psL (λ ()) (PT.psy U.tt (PP.psL (λ ()) cSP) (PB.psL (λ ()) (F₁.fI1 _ _))))
    (rτ (PX.pτL (PT.pτR (PB.pτL F₁.fτ)))
    (rE (PX.psL (λ ()) (PT.psy U.tt (PP.psR (λ ()) sRN) (PB.psL (λ ()) (F₁.fO2 _ _))))
    (rτ (PX.pτL (PT.pτL (PP.pτR sτ)))
    (rτ (PX.pτL (PT.pτR (PB.pτL F₁.fτ)))
    (rE (PX.psL (λ ()) (PT.psy U.tt (PP.psR (λ ()) sRA) (PB.psL (λ ()) (F₁.fO1 _))))
    (rE (PX.psL (λ ()) (PT.psy U.tt (PP.psR (λ ()) sCx) (PB.psR (λ ()) (F₂.fI0 _))))
    (rτ (PX.pτL (PT.pτL (PP.pτR sτ)))
    (rτ (PX.pτL (PT.pτR (PB.pτR F₂.fτ)))
    (rE (PX.psL (λ ()) (PT.psy U.tt (PP.psL (λ ()) (cDr rpC)) (PB.psR (λ ()) (F₂.fO1 _))))
    (rτ (PX.pτL (PT.pτL (PP.pτL cτ)))
    (rτ (PX.pτL (PT.pτR (PB.pτR F₂.fτ)))
    (rE (PX.psL (λ ()) (PT.psL (λ ()) (PP.psR (λ ()) sDn)))
    (rE (PX.psL (λ ()) (PT.psy U.tt (PP.psR (λ ()) sDS) (PB.psR (λ ()) (F₂.fI0 _))))
    (rτ (PX.pτL (PT.pτR (PB.pτR F₂.fτ)))
    (rE (PX.psL (λ ()) (PT.psy U.tt (PP.psL (λ ()) cDn) (PB.psR (λ ()) (F₂.fO1 _))))
     r0)))))))))))))))
    where open Gen l BlkA using (rE; rτ; r0)

  -- (P2) THE BOUND 8 IS TIGHT: a trace of the blocked system containing the quit command,
  -- after which exactly 8 visible events lead to √
  pblk-tight : Σ[ W ∈ Tree ] Σ[ W′ ∈ Tree ]
                 (pblk ⟹∖√⟨ trT₁ ⟩ W × Any (QuitApi l) trT₁ × W ⟹∖√⟨ trT₂ ⟩ W′
                  × length trT₂ ≡ 8 × PTree.force W′ ≡ ret tt)
  pblk-tight = proj₁ ri₁ , proj₁ ri₂ , proj₁ (proj₂ ri₁) , there (there (here refl))
             , proj₁ (proj₂ ri₂) , refl , proj₂ (proj₂ ri₂)
    where
    -- the first part, concretely
    ri₁ = GenI.runI l BlkI runT₁ pblk₀
    -- the second part, concretely, to √
    ri₂ = runTo√ runT₂ (proj₂ (proj₂ ri₁))

  ------------------------------------------------------------------------
  -- §13  Capacity 2 suffices: a FIFO never refuses a sender
  ------------------------------------------------------------------------

  -- a FIFO with room for one more message (it offers an input: `fI0` / `fI1`)
  data Room : BPh → Set where
    room0 : Room (bq β0)
    room1 : ∀ {x} → Room (bq (β1 x))

  -- the client phases whose only move is a send (`cSR`, `cSQ`, `cSP`)
  data CSnd : CPh → Set where
    csR : CSnd cSndRN
    csQ : CSnd cSndQ
    csP : CSnd cSndPQ

  -- the server phases whose only move is a send (`sNx`, `sCx`, `sDS`)
  data SSnd : SPh → Set where
    ssR : ∀ {r} → SSnd (sRep r)
    ssC : SSnd sCanc
    ssD : SSnd sDone

  -- a sending client finds room in the client→server FIFO
  roomC : ∀ {c s b₁ b₂} → CSnd c → J c s b₁ b₂ → Room b₁
  roomC csR a2     = room0
  roomC csQ q1     = room0
  roomC csP p1     = room1
  roomC csP p2     = room0
  roomC csP (p3 _) = room0
  roomC csP (p4 _) = room0

  -- a sending server finds room in the server→client FIFO
  roomS : ∀ {c s b₁ b₂} → SSnd s → J c s b₁ b₂ → Room b₂
  roomS ssR (b3 _) = room0
  roomS ssR (p3 _) = room0
  roomS ssR (x3 _) = room0
  roomS ssC x5     = room0
  roomS ssD q4     = room0
  roomS ssD (x7 _) = room1

  -- CAPACITY 2 SUFFICES: in every state reachable in the pipelined system, a peer about to
  -- send finds room in its FIFO — the FIFOs never block a sender, so they behave as
  -- unbounded ones (capacity 1 would block the pipelined MsgQuit behind RequestNext, `p1`)
  psys-noBlock : ∀ {s W} → psys l ⟹∖√⟨ s ⟩ W
               → Σ[ σ ∈ SysS ] (Abs.Pos SysA σ W
                   × (CSnd (proj₁ (proj₁ (proj₁ σ))) → Room (proj₁ (proj₁ (proj₂ σ))))
                   × (SSnd (proj₁ (proj₂ (proj₁ σ))) → Room (proj₁ (proj₂ (proj₂ σ)))))
  psys-noBlock r = proj₁ ru , proj₂ (proj₂ ru) , (λ c → roomC c j) , (λ s → roomS s j)
    where
    -- the abstract run
    ru = Gen.runE l SysA psys₀ r
    -- the invariant at its end
    j = proj₁ (WS.walk (proj₁ (proj₂ ru)) a1 K₀)

  -- (P5) THE CONTRAST, side by side: with the server application silent the non-pipelined
  -- pair deadlocks (`LeiosNotifyQuit.blk-deadlock`: the stall `blk-stall` after RequestNext),
  -- the pipelined system never does
  stall-vs-pipelined : HasDeadlock (blk l) × DeadlockFree pblk
  stall-vs-pipelined = blk-deadlock l , pblk-deadlockFree
