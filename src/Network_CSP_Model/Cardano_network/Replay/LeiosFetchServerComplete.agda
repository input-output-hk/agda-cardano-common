{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)

-- SERVER COMPLETENESS and the SERVER BRIDGE (trace-replay Phase 5,
-- Increment 2; amendment B1).
--   * `server-complete`: every server-spec trace whose received requests ask
--     for held EBs (`All (ReqHeld bs) es`) is observed (under `clsS`/`forget`)
--     on some √-free run of `serverModel bs`.
--   * `server-bridge`: a log trace is a server-spec trace iff it is observed
--     on a run of `serverModel bs` for SOME body store `bs` (⇐ is
--     `server-sound`; ⇒ takes `bs` = the hashes the trace requests).
-- Obtained from the generic `Bridge.complete` (unchanged) with the
-- co-simulation `RelC bs`.  The model run is ours to choose, so `RelC` keeps
-- the composite in ONE canonical state per spec state (every pending
-- loop-back drained, the store at its loop head): six shapes, no τ
-- interleavings.  The held fact `h ∈ bs` enters at the request event (the
-- `co-ev` premise), is recorded in `cBusyB`/`cBusyT`, and is spent at the
-- spec's `sServe`, where the waiting thread reads the body off the store
-- (`LeiosFetchServerForward.store-read`).
-- Invariant 1 (B7a): checked with `agda --safe` on the command line.
module Cardano_network.Replay.LeiosFetchServerComplete (k : ℕ) where

open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using (refl)

open import Process_Trees using (ExtI)
open import Cardano_network.Base using (N2N_LeiosFetch; FromInitiator; FromResponder)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Net replayParams
  using (Net_Api; output; input; lfpReqBlockRequest; lfpReqBlockTxsRequest; lfpSendBlock; lfpSendBlockTxs)
open import Cardano_network.Data replayParams
  using ( Payload; MessageLeiosFetchP; leiosFetchP; MsgLFPBlockRequest; MsgLFPBlock
        ; MsgLFPBlockTxsRequest; MsgLFPBlockTxs; MsgLFPDone; DecEq-EBPoint; DecEq-TxsRequest )
open import Cardano_network.LeiosFetchP replayParams using (serverStepP; stBlock; stBlockTxs)
open import Cardano_network.Replay.LeiosFetchServerModel using (Proc; Bodies; lS; dS; nS; serverModel; bodyStore)
open import Cardano_network.Replay.LeiosFetchServerParts using (C; peerAfter; lat; bodyA; bodyB; a2; b2)
open import Cardano_network.Replay.LeiosFetchServerRel k using (repB; repT; doneR)
open import Cardano_network.Replay.LeiosFetchServerForward
open import Cardano_network.Replay.LeiosFetchServerSound k using (server-sound)
open import Cardano_network.Replay.LeiosFetchObs using (ObsS; clsS; forget)
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (Event; evLabel; sVis; sSil)
open import Semantics.Deadlock {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
import Semantics.Replay.Bridge {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as BrS

open import Cardano_network.Replay.LeiosFetchSession
  using ( St; E; Send; Recv; sIdle; sBusy; sReady; sClosed; blockReq; blockTxsReq; server₀
        ; MsgLeiosBlockRequest; MsgLeiosBlockTxsRequest; module Spec )
open Spec k
  using (leiosFetch; _-[_]→_; _-τ→_; sRecvBlockReq; sRecvTxsReq; sRecvDone; sSendBlock; sSendTxs; sServe)
open import Semantics.Replay using (module Traces)
open Traces leiosFetch using (HasTrace)

------------------------------------------------------------------------
-- The premise (B1)
------------------------------------------------------------------------

-- the EB hash a received request asks for, if the event is one
reqHash : E → Maybe ℕ
reqHash (Recv , MsgLeiosBlockRequest h _)        = just h
reqHash (Recv , MsgLeiosBlockTxsRequest h _ _ _) = just h
reqHash _                                        = nothing

-- an asked-for hash, if any, is held
Held : List ℕ → Maybe ℕ → Set
Held bs (just h) = h ∈ bs
Held bs nothing  = ⊤

-- B1's per-event premise: a received request asks for an EB in `bs` (`ebHash = id`)
ReqHeld : List ℕ → E → Set
ReqHeld bs e = Held bs (reqHash e)

-- WHY THE PREMISE IS NEEDED (B1).  With `bs = []`, the log trace
--   [Recv BlockRequest 7 1 , Send Block 7 0]
-- is a server-spec trace (`sRecvBlockReq`, `sServe`, `sSendBlock`), but
-- `serverModel []` has no run observed as it: after the report, thread A can
-- only read `stGetBody 7` off the store, the empty store offers no body read
-- (`offerBodies _ [] [] = Stop`), and the producer's Block state accepts
-- nothing but that thread's `lfpSendBlock` — the session is stuck, exactly
-- the wedge of `Parametric/Leios/Negative/FetchWedge.agda:238` (`wedge-stuck`).
-- Not mechanised here.

------------------------------------------------------------------------
-- The co-simulation relation: one canonical composite per spec state
------------------------------------------------------------------------

-- thread A at its loop head
Ah : Proc
Ah = lat bodyA bodyA

-- thread B at its loop head
Bh : Proc
Bh = lat bodyB bodyB

-- the composite chosen for each spec state; a busy state records that the
-- requested EB is held
data RelC (bs : Bodies) : Proc → St → Set₁ where
  -- Idle: the initial composite
  cIdle   : RelC bs (serverModel bs) sIdle
  -- BlockRequest (h , s) received, h held; the report is pending
  cBusyB  : ∀ {h s} → h ∈ bs
          → RelC bs (C (peerAfter (repB (h , s))) Ah Bh (bodyStore nS bs)) (sBusy (blockReq h s))
  -- BlockTxsRequest (h , s) received (bitmap chosen empty), h held; the report is pending
  cBusyT  : ∀ {h s} → h ∈ bs
          → RelC bs (C (peerAfter (repT ((h , s) , []))) Ah Bh (bodyStore nS bs)) (sBusy (blockTxsReq h s))
  -- thread A holds body h, the producer waits for it
  cReadyB : ∀ {h s}
          → RelC bs (C (peerAfter (serverStepP lS dS stBlock)) (lat bodyA (a2 h)) Bh (bodyStore nS bs)) (sReady (blockReq h s))
  -- thread B holds the reply for (h , s), the producer waits for it
  cReadyT : ∀ {h s}
          → RelC bs (C (peerAfter (serverStepP lS dS stBlockTxs)) Ah (lat bodyB (b2 (h , s))) (bodyStore nS bs)) (sReady (blockTxsReq h s))
  -- Done received
  cDone   : RelC bs (C (peerAfter doneR) Ah Bh (bodyStore nS bs)) sClosed

------------------------------------------------------------------------
-- Labels of the runs
------------------------------------------------------------------------

-- the producer receives `msg` on the wire
wireR : MessageLeiosFetchP → Event
wireR msg = evLabel Payload (output lS dS N2N_LeiosFetch) (tt , FromInitiator , tt , leiosFetchP msg)

-- the producer sends `msg` on the wire
wireS : MessageLeiosFetchP → Event
wireS msg = evLabel Payload (input lS dS N2N_LeiosFetch) (tt , FromResponder , tt , leiosFetchP msg)

------------------------------------------------------------------------
-- The clauses
------------------------------------------------------------------------

-- the spec's `sServe` (the unlogged report and store read): report, loop-back, read, drain
co-τ : ∀ {bs P s s′} → RelC bs P s → s -τ→ s′
     → Σ[ P′ ∈ Proc ] Σ[ t ∈ List Event ] (P ⟹∖√⟨ t ⟩ P′ × ObsS t [] × RelC bs P′ s′)
co-τ {bs} (cBusyB {h} {s} m) sServe with store-read bs m
... | c , stS , bk =
  _ , _ ,
  ∖√-ev (stepAt (apiL lfpReqBlockRequest (h , s))
          (liftPA ptt (λ ()) (p-out-fwd {d = DecEq-EBPoint}) (sVis refl refl) refl (store-quiet bs (λ ()))))
  (∖√-τ (liftτP (sSil refl))
  (∖√-ev (stepAt (getL h) (liftAS ptt (λ ()) (a1-fwd {q = h , s}) stS refl refl))
  (store-back bk)))
  , refl , cReadyB
co-τ {bs} (cBusyT {h} {s} m) sServe with store-read bs m
... | c , stS , bk =
  _ , _ ,
  ∖√-ev (stepAt (apiL lfpReqBlockTxsRequest ((h , s) , []))
          (liftPB ptt (λ ()) (p-out-fwd {d = DecEq-TxsRequest}) (sVis refl refl) refl (store-quiet bs (λ ()))))
  (∖√-τ (liftτP (sSil refl))
  (∖√-ev (stepAt (getL h) (liftBS ptt (λ ()) (b1-fwd {q = h , s}) stS refl refl))
  (store-back bk)))
  , refl , cReadyT

-- each spec event: a wire receive (recording the held fact), or reply command,
-- wire send and the two loop-backs
co-ev : ∀ {bs P s s′ e} → RelC bs P s → ReqHeld bs e → s -[ e ]→ s′
      → Σ[ P′ ∈ Proc ] Σ[ t ∈ List Event ] (P ⟹∖√⟨ t ⟩ P′ × ObsS t (e ∷ []) × RelC bs P′ s′)
co-ev {bs} cIdle m (sRecvBlockReq {h} {s}) =
  _ , _ ,
  ∖√-ev (stepAt (wireR (MsgLFPBlockRequest (h , s))) (liftP (λ ()) (λ ()) (sVis refl refl) refl (store-quiet bs (λ ()))))
  ∖√-refl
  , refl , cBusyB m
co-ev {bs} cIdle m (sRecvTxsReq {h} {s}) =
  _ , _ ,
  ∖√-ev (stepAt (wireR (MsgLFPBlockTxsRequest (h , s) [])) (liftP (λ ()) (λ ()) (sVis refl refl) refl (store-quiet bs (λ ()))))
  ∖√-refl
  , refl , cBusyT m
co-ev {bs} cIdle m sRecvDone =
  _ , _ ,
  ∖√-ev (stepAt (wireR MsgLFPDone) (liftP (λ ()) (λ ()) (sVis refl refl) refl (store-quiet bs (λ ()))))
  ∖√-refl
  , refl , cDone
co-ev {bs} (cReadyB {h}) m sSendBlock =
  _ , _ ,
  ∖√-ev (stepAt (apiL lfpSendBlock h) (liftPA ptt (λ ()) (sVis refl refl) a2-fwd refl (store-quiet bs (λ ()))))
  (∖√-ev (stepAt (wireS (MsgLFPBlock h)) (liftP (λ ()) (λ ()) p-snd-fwd refl (store-quiet bs (λ ()))))
  (∖√-τ (liftτP (sSil refl))
  (∖√-τ (liftτA (sSil refl))
   ∖√-refl)))
  , refl , cIdle
co-ev {bs} (cReadyT {h} {s}) m sSendTxs =
  _ , _ ,
  ∖√-ev (stepAt (apiL lfpSendBlockTxs ((h , s) , [])) (liftPB ptt (λ ()) (sVis refl refl) b2-fwd refl (store-quiet bs (λ ()))))
  (∖√-ev (stepAt (wireS (MsgLFPBlockTxs (h , s) [])) (liftP (λ ()) (λ ()) p-snd-fwd refl (store-quiet bs (λ ()))))
  (∖√-τ (liftτP (sSil refl))
  (∖√-τ (liftτB (sSil refl))
   ∖√-refl)))
  , refl , cIdle

------------------------------------------------------------------------
-- The theorems
------------------------------------------------------------------------

-- the server composite over the store holding `bs` co-simulates the spec, on held requests
serverCoSim : ∀ bs → BrS.CoSim leiosFetch clsS forget (RelC bs) (ReqHeld bs)
serverCoSim bs = record { co-τ = co-τ ; co-ev = co-ev }

-- SERVER COMPLETENESS: a server-spec trace asking only for held EBs is observed on a model run
server-complete : ∀ bs {es} → All (ReqHeld bs) es → HasTrace server₀ es
                → ∃[ t ] ∃[ M ] (serverModel bs ⟹∖√⟨ t ⟩ M × ObsS t es)
server-complete bs hs (_ , r) with BrS.complete leiosFetch clsS forget (serverCoSim bs) cIdle hs r
... | M , t , run , o , _ = t , M , run , o

-- adds an asked-for hash, if any, to a store
add : Maybe ℕ → List ℕ → List ℕ
add nothing  bs = bs
add (just h) bs = h ∷ bs

-- the hashes a trace requests (the store `server-bridge` picks)
reqs : List E → List ℕ
reqs []       = []
reqs (e ∷ es) = add (reqHash e) (reqs es)

-- an added hash is held
held-add : ∀ m bs → Held (add m bs) m
held-add nothing  bs = tt
held-add (just h) bs = here refl

-- adding a hash keeps every held hash held
held-wk : ∀ m n {bs} → Held bs n → Held (add m bs) n
held-wk nothing  n        hn = hn
held-wk (just h) nothing  hn = tt
held-wk (just h) (just x) hn = there hn

-- every request of a trace asks for one of the trace's requested hashes
all-held : ∀ es → All (ReqHeld (reqs es)) es
all-held []       = []
all-held (e ∷ es) = held-add (reqHash e) (reqs es) ∷ All.map (λ {e′} → held-wk (reqHash e) (reqHash e′)) (all-held es)

-- SERVER BRIDGE (B1): a log trace is a server-spec trace iff some body store's model shows it
server-bridge : ∀ {es} → HasTrace server₀ es ⇔ (∃[ bs ] ∃[ t ] ∃[ M ] (serverModel bs ⟹∖√⟨ t ⟩ M × ObsS t es))
server-bridge {es} =
  mk⇔ (λ h → reqs es , server-complete (reqs es) (all-held es) h)
      (λ { (bs , t , M , run , o) → server-sound bs run o })
