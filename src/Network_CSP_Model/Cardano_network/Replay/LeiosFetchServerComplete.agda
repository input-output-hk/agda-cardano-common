{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)

-- Counted server completeness under held body/table-transaction premises.
-- The total bridge chooses the requested bodies and pairs its model witness
-- with WireOK. Service performs the actual unit-transaction store reads.
-- Spec throws may still be matched by empty model runs: this is finite-trace
-- completeness, not a witness of connection teardown. Checked with --safe (B7a).
module Cardano_network.Replay.LeiosFetchServerComplete (k : ℕ) where

open import Data.List using (List; []; _∷_; _++_; length; map)
import Data.List.Properties as L
open import Data.Nat using (_<_; _+_)
import Data.Nat.Properties as N
open import Cardano_network.Replay.LeiosFetchWords using (decoderOffsets; offsets-decodable; decodable-all)
open import Cardano_network.Replay.LeiosFetchWire using (offsets)
open import Cardano_network.Replay.LeiosFetchWireOK using (WireOK; WireMsg; accepted-wire)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Process_Trees using (ExtI)
open import Cardano_network.Base using (N2N_LeiosFetch; FromInitiator; FromResponder)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Net replayParams
  using (Net_Api; output; input; lfpReqBlockRequest; lfpReqBlockTxsRequest; lfpSendBlock; lfpSendBlockTxs)
open import Cardano_network.Data replayParams
  using ( Payload; MessageLeiosFetchP; leiosFetchP; MsgLFPBlockRequest; MsgLFPBlock
        ; MsgLFPBlockTxsRequest; MsgLFPBlockTxs; MsgLFPDone; DecEq-EBPoint; DecEq-TxsRequest )
open import Cardano_network.LeiosFetchP replayParams using (serverStepP; stBlock; stBlockTxs)
open import Cardano_network.Replay.LeiosFetchServerModel using (Proc; Bodies; lS; dS; nS; serverModel; bodyStore; serveTxs; getTxEv)
open import Cardano_network.Replay.LeiosFetchServerParts using (C; peerAfter; lat; bodyA; bodyB; a2; b2)
open import Cardano_network.Replay.LeiosFetchServerRel k using (repB; repT; doneR; tq)
open import Cardano_network.Replay.LeiosFetchServerForward
open import Cardano_network.Replay.LeiosFetchServerSound k using (server-sound)
open import Cardano_network.Replay.LeiosFetchObs using (ObsS; clsS; forget; _≈♭_; recv-request)
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (Event; evLabel; sVis; sSil)
open import Semantics.Deadlock {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
import Semantics.Replay.Bridge {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as BrS

open import Cardano_network.Replay.LeiosFetchSession
  using ( St; E; Send; Recv; sIdle; sBusy; sReady; sClosed; sThrown; blockReq; blockTxsReq; server₀
        ; MsgLeiosBlockRequest; MsgLeiosBlockTxsRequest; module Spec )
open Spec k
  using (leiosFetch; _-[_]→_; _-τ→_; sRecvBlockReq; sRecvTxsReq; sRecvDone; sSendBlock; sSendTxs; sServe; sThrow)
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

-- Every requested offset is in the decoder-sized table, whose unit tx is held.
ReqOffsets : E → Set
ReqOffsets (_ , MsgLeiosBlockTxsRequest _ _ _ b) = All (_< decoderOffsets) (offsets b)
ReqOffsets _ = ⊤

-- Fixed-store completeness requires the body and each table transaction to be held.
ReqHeld : List ℕ → E → Set
ReqHeld bs e = Held bs (reqHash e) × ReqOffsets e

-- Wire decoding supplies table bounds; the replay store holds the unit tx at every entry.
wire-offsets : ∀ e → WireMsg e → ReqOffsets e
wire-offsets (_ , MsgLeiosBlockTxsRequest _ _ _ b) (valid , _) = decodable-all (offsets-decodable b valid)
wire-offsets (_ , Cardano_network.Replay.LeiosFetchSession.MsgLeiosBlockRequest _ _) w = tt
wire-offsets (_ , Cardano_network.Replay.LeiosFetchSession.MsgLeiosBlock _ _) w = tt
wire-offsets (_ , Cardano_network.Replay.LeiosFetchSession.MsgLeiosBlockTxs _ _) w = tt
wire-offsets (_ , Cardano_network.Replay.LeiosFetchSession.MsgLeiosDone) w = tt

-- WHY THE PREMISE IS NEEDED (B1).  With `bs = []`, the log trace
--   [Recv BlockRequest 7 1 , Send Block 7 0]
-- is a server-spec trace (`sRecvBlockReq`, `sServe`, `sSendBlock`), but
-- `serverModel []` has no run observed as it: after the report, thread A can
-- only obtain body 7 from `stGetBody 7`. The empty store instead offers
-- `stLacksBody 7`, stopping the shipped serving thread: it cannot command a Block.
-- `LeiosFetchBridgeSanity.unknownEBThrows` witnesses that thrown state.
-- `Negative/FetchWedge.wedge-stuck` retains the earlier blocking design as a
-- local negative control; `wedge-throws` is the shipped thread's counterpart.

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
  -- A decoded request records both the held body and bounds for each unit-tx table lookup.
  cBusyT : ∀ {q bm} → proj₁ q ∈ bs → All (_< decoderOffsets) bm →
    RelC bs (C (peerAfter (repT (q , bm))) Ah Bh (bodyStore nS bs)) (sBusy (tq (q , bm)))
  -- thread A holds body h, the producer waits for it
  cReadyB : ∀ {h s}
          → RelC bs (C (peerAfter (serverStepP lS dS stBlock)) (lat bodyA (a2 h)) Bh (bodyStore nS bs)) (sReady (blockReq h s))
  -- The ready indexed reply retains exactly the requested number of transactions.
  cReadyT : ∀ {q bm acc} → length (map proj₂ acc) ≡ length bm →
    RelC bs (C (peerAfter (serverStepP lS dS (stBlockTxs q bm))) Ah
      (lat bodyB (serveTxs nS lS dS q [] acc)) (bodyStore nS bs)) (sReady (tq (q , bm)))
  -- A thrown spec session has no further observations; keep the current model.
  cThrown : ∀ {P} → RelC bs P sThrown
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
-- Finish all held transaction lookups, preserving the exact accumulated count.
finish-txs : ∀ bs q bm acc {P Ta} → Quiet P (evLabel _ (getTxEv nS tt) tt) →
  Quiet Ta (evLabel _ (getTxEv nS tt) tt) → All (_< decoderOffsets) bm →
  Σ[ acc′ ∈ List (ℕ × Data.Unit.⊤) ] Σ[ t ∈ List Event ]
  (C P Ta (lat bodyB (serveTxs nS lS dS q bm acc)) (bodyStore nS bs) ⟹∖√⟨ t ⟩
     C P Ta (lat bodyB (serveTxs nS lS dS q [] acc′)) (bodyStore nS bs) ×
   ObsS t [] × length acc′ ≡ length acc + length bm)
finish-txs bs q [] acc qp qa [] = acc , [] , ∖√-refl , refl , sym (N.+-identityʳ (length acc))
finish-txs bs q (o ∷ os) acc qp qa (bound ∷ bounds) with finish-txs bs q os (acc ++ ((o , tt) ∷ [])) qp qa bounds
... | acc′ , t , run , obs , count = acc′ , evLabel _ (getTxEv nS tt) tt ∷ t ,
  ∖√-ev (stepAt (evLabel _ (getTxEv nS tt) tt)
    (liftBS ptt (λ ()) (work-fwd bound) (store-tx-read bs) qa qp))
    (BrS.⟹∖√-++ (store-back bRet) run) , obs ,
  trans count (trans (cong (_+ length os) (L.length-++ acc)) (N.+-assoc (length acc) 1 (length os)))

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
co-τ {bs} (cBusyT {q} {bm} m bounds) sServe with store-read bs m
... | c , stS , bk with finish-txs bs q bm [] {P = peerAfter (serverStepP lS dS (stBlockTxs q bm))} {Ta = Ah} refl refl bounds
... | acc , t , txRun , obs , count =
  _ , _ ,
  ∖√-ev (stepAt (apiL lfpReqBlockTxsRequest (q , bm))
    (liftPB ptt (λ ()) (p-out-fwd {d = DecEq-TxsRequest}) (sVis refl refl) refl (store-quiet bs (λ ()))))
  (∖√-τ (liftτP (sSil refl))
  (∖√-ev (stepAt (getL (proj₁ q)) (liftBS ptt (λ ()) (b1-any-fwd {q = q} {bm = bm}) stS refl refl))
  (BrS.⟹∖√-++ (store-back bk) txRun))) , obs ,
  cReadyT {q = q} {bm = bm} {acc = acc} (trans (L.length-map proj₂ acc) count)

co-τ (cBusyB _) sThrow = _ , [] , ∖√-refl , refl , cThrown
co-τ (cBusyT _ _) sThrow = _ , [] , ∖√-refl , refl , cThrown

-- each spec event: a wire receive (recording the held fact), or reply command,
-- wire send and the two loop-backs
co-ev : ∀ {bs P s s′ e} → RelC bs P s → ReqHeld bs e → s -[ e ]→ s′
      → Σ[ P′ ∈ Proc ] Σ[ t ∈ List Event ] (P ⟹∖√⟨ t ⟩ P′ × ObsS t (e ∷ []) × RelC bs P′ s′)
co-ev {bs} cIdle (m , _) (sRecvBlockReq {h} {s}) =
  _ , _ ,
  ∖√-ev (stepAt (wireR (MsgLFPBlockRequest (h , s))) (liftP (λ ()) (λ ()) (sVis refl refl) refl (store-quiet bs (λ ()))))
  ∖√-refl
  , refl , cBusyB m
co-ev {bs} cIdle (m , bounds) (sRecvTxsReq {h} {s} {n} {b} valid count) rewrite count =
  _ , _ ,
  ∖√-ev (stepAt (wireR (MsgLFPBlockTxsRequest (h , s) (offsets b)))
    (liftP (λ ()) (λ ()) (p-recvT-fwd (h , s) (offsets b) (offsets-decodable b valid)) refl (store-quiet bs (λ ()))))
    ∖√-refl , request-obs , cBusyT {q = h , s} {bm = offsets b} m bounds
  where
  -- Decoder-before-logging exposes this request's actual popcount.
  request-obs : ObsS (wireR (MsgLFPBlockTxsRequest (h , s) (offsets b)) ∷ [])
    ((Recv , MsgLeiosBlockTxsRequest h s (length (offsets b)) b) ∷ [])
  request-obs rewrite recv-request tt FromInitiator tt (h , s) (offsets b) (offsets-decodable b valid) = refl
co-ev {bs} cIdle m sRecvDone =
  _ , _ ,
  ∖√-ev (stepAt (wireR MsgLFPDone) (liftP (λ ()) (λ ()) (sVis refl refl) refl (store-quiet bs (λ ()))))
  ∖√-refl
  , refl , cDone
co-ev {bs} (cReadyB {h}) m (sSendBlock _) =
  _ , _ ,
  ∖√-ev (stepAt (apiL lfpSendBlock h) (liftPA ptt (λ ()) (sVis refl refl) a2-fwd refl (store-quiet bs (λ ()))))
  (∖√-ev (stepAt (wireS (MsgLFPBlock h)) (liftP (λ ()) (λ ()) p-snd-fwd refl (store-quiet bs (λ ()))))
  (∖√-τ (liftτP (sSil refl))
  (∖√-τ (liftτA (sSil refl))
   ∖√-refl)))
  , refl , cIdle
co-ev {bs} (cReadyT {q} {bm} {acc} count) m (sSendTxs _ _) =
  _ , _ ,
  ∖√-ev (stepAt (apiL lfpSendBlockTxs (q , acc)) (liftPB ptt (λ ()) (sVis refl refl) work-out-fwd refl (store-quiet bs (λ ()))))
  (∖√-ev (stepAt (wireS (MsgLFPBlockTxs (map proj₂ acc))) (liftP (λ ()) (λ ()) p-snd-fwd refl (store-quiet bs (λ ()))))
  (∖√-τ (liftτP (sSil refl))
  (∖√-τ (liftτB (sSil refl)) ∖√-refl))) ,
  cong (λ n → (Send , Cardano_network.Replay.LeiosFetchObs.txs♭ n) ∷ []) count , cIdle

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

-- Every requested hash appears in the inventory selected from this trace.
all-hashes : ∀ es → All (λ e → Held (reqs es) (reqHash e)) es
all-hashes [] = []
all-hashes (e ∷ es) = held-add (reqHash e) (reqs es) ∷
  All.map (λ {e′} → held-wk (reqHash e) (reqHash e′)) (all-hashes es)

-- Pair held hashes with decoder-established bounds for every table lookup.
held-with-wire : ∀ bs es → All (λ e → Held bs (reqHash e)) es → WireOK es → All (ReqHeld bs) es
held-with-wire bs [] [] [] = []
held-with-wire bs (e ∷ es) (held ∷ rest) (wire ∷ wires) =
  (held , wire-offsets e wire) ∷ held-with-wire bs es rest wires

-- The chosen inventory meets the extended premise for every admissible trace.
all-held : ∀ es → WireOK es → All (ReqHeld (reqs es)) es
all-held es = held-with-wire (reqs es) es (all-hashes es)

-- Exact counted server bridge, with forgotten wire fields explicitly constrained.
server-bridge : ∀ {es} → HasTrace server₀ es ⇔
  (WireOK es × ∃[ bs ] ∃[ t ] ∃[ M ] (serverModel bs ⟹∖√⟨ t ⟩ M × ObsS t es))
server-bridge = mk⇔ forward backward
  where
  -- Choose all requested bodies and use the decoded table bounds.
  forward : ∀ {es} → HasTrace server₀ es →
    WireOK es × ∃[ bs ] ∃[ t ] ∃[ M ] (serverModel bs ⟹∖√⟨ t ⟩ M × ObsS t es)
  forward {es} accepted with server-complete (reqs es) (all-held es (accepted-wire k accepted)) accepted
  ... | t , M , run , obs = accepted-wire k accepted , reqs es , t , M , run , obs

  -- Soundness spends the explicit wire premise on the observed log.
  backward : ∀ {es} → (WireOK es × ∃[ bs ] ∃[ t ] ∃[ M ]
    (serverModel bs ⟹∖√⟨ t ⟩ M × ObsS t es)) → HasTrace server₀ es
  backward (wire , bs , t , M , run , obs) = server-sound bs run obs wire
