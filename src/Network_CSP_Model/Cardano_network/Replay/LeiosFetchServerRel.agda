{-# OPTIONS --guardedness #-}

-- The counted server relation carries request lengths through body confirmation,
-- each unit-transaction lookup, the accumulated indexed reply and wire send.
-- Non-driving components may drain loop-back τs. Missing bodies relate stopped
-- threads to sThrown. Decoder failures are unlogged and leave the spec idle.
-- Every internal model τ leaves the spec unchanged. Checked with --safe (B7a).
open import Data.Nat using (ℕ; _+_; _<_)

module Cardano_network.Replay.LeiosFetchServerRel (k : ℕ) where

open import Data.List.Relation.Unary.All using (All)
open import Cardano_network.Replay.LeiosFetchWords using (decoderOffsets)
open import Data.List using ([]; List; length; map)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Process_Trees using (ExtI)
open import Cardano_network.Base using (FromResponder)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Net replayParams
  using (Net_Api; Net_Api-≟; ApiLPCar; lfpReqBlockRequest; lfpReqBlockTxsRequest; lfpSendBlock; lfpSendBlockTxs)
open import Cardano_network.Data replayParams
  using (Payload; MsgLFPBlock; MsgLFPBlockTxs; DecEq-EBPoint; DecEq-TxsRequest; DecEq-TxsReply)
open import Cardano_network.LeiosFetchP replayParams
  using (LFPEv; LFPEv-≟; apiLPev; doneLFP; stIdle; stBlock; stBlockTxs; stDone)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerLFP replayParams using (Rd; snd)
import CSP.Operators (Net_Api-≟ {Payload}) as Op
import CSP.Operators {E = LFPEv} LFPEv-≟ as LOp
open import Cardano_network.Replay.LeiosFetchServerModel using (Proc; Bodies; lS; dS; nS; serverModel; bodyStore; serveTxs)
open import Cardano_network.Replay.LeiosFetchServerParts
open import CSP.Laws.Traces.PrefixInversion (Net_Api-≟ {Payload}) using (loop-pfx-no-τ; loop-out-no-τ)
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_─[_]─►_; τ; ev; evl)

open import Cardano_network.Replay.LeiosFetchSession
  using (St; sIdle; sBusy; sReady; sClosed; sThrown; Req; blockReq; blockTxsReq; server₀; module Spec)
open Spec k using (leiosFetch)
open import Semantics.Replay using (module Traces)
open Traces leiosFetch using (_⇒⟨_⟩_; done)

------------------------------------------------------------------------
-- Vocabulary
------------------------------------------------------------------------

-- the spec's BlockRequest for a reported point
rq : ApiLPCar lfpReqBlockRequest → Req
rq q = blockReq (proj₁ q) (proj₂ q)

-- The replay request retains the number of offsets reported to the application.
tq : ApiLPCar lfpReqBlockTxsRequest → Req
tq (q , bm) = blockTxsReq (proj₁ q) (proj₂ q) (length bm)

-- the producer round after receiving a BlockRequest: report the point
repB : ApiLPCar lfpReqBlockRequest → Rd
repB q = LOp.Output ⦃ DecEq-EBPoint ⦄ (apiLPev lS dS lfpReqBlockRequest) q (LOp.Ret (inj₁ stBlock))

-- the producer round after receiving a BlockTxsRequest: report the point and bitmap
repT : ApiLPCar lfpReqBlockTxsRequest → Rd
repT qb = LOp.Output ⦃ DecEq-TxsRequest ⦄ (apiLPev lS dS lfpReqBlockTxsRequest) qb (LOp.Ret (inj₁ (stBlockTxs (proj₁ qb) (proj₂ qb))))

-- the producer round sending the Block `h`
sndB : ApiLPCar lfpSendBlock → Rd
sndB h = snd lS dS FromResponder (MsgLFPBlock h) stIdle

-- The producer round sends the accumulated transactions without their offsets.
sndT : ApiLPCar lfpSendBlockTxs → Rd
sndT (q , acc) = snd lS dS FromResponder (MsgLFPBlockTxs (map proj₂ acc)) stIdle

-- the producer round after receiving Done
doneR : Rd
doneR = doneLFP lS dS LOp.⟶₀ LOp.Ret (inj₁ stDone)

------------------------------------------------------------------------
-- The relation
------------------------------------------------------------------------

-- reachable composite states of `serverModel bs`, related to spec states
data Rel (bs : Bodies) : Proc → St → Set₁ where
  -- Idle: everything at rest
  rIdle   : ∀ {P Ta Tb S} → PRest stIdle P → ERest bodyA Ta → ERest bodyB Tb → SRest bs S
          → Rel bs (C P Ta Tb S) sIdle
  -- BlockRequest q received, report pending
  rReqB   : ∀ {Ta Tb S} q → ERest bodyA Ta → ERest bodyB Tb → SRest bs S
          → Rel bs (C (peerAfter (repB q)) Ta Tb S) (sBusy (rq q))
  -- q reported to thread A, which waits on the store
  rWaitB  : ∀ {P Tb S} q → PRest stBlock P → ERest bodyB Tb → SRest bs S
          → Rel bs (C P (lat bodyA (a1 q)) Tb S) (sBusy (rq q))
  -- thread A holds the body (its hash is the requested one): the reply is ready
  rReadyB : ∀ {P Tb S} q → PRest stBlock P → ERest bodyB Tb → SRest bs S
          → Rel bs (C P (lat bodyA (a2 (proj₁ q))) Tb S) (sReady (rq q))
  -- the producer is about to send the Block for q
  rSendB  : ∀ {Ta Tb S} q → ERest bodyA Ta → ERest bodyB Tb → SRest bs S
          → Rel bs (C (peerAfter (sndB (proj₁ q))) Ta Tb S) (sReady (rq q))
  -- BlockTxsRequest (q , bm) received, report pending
  rReqT   : ∀ {Ta Tb S} qb → All (_< decoderOffsets) (proj₂ qb) → ERest bodyA Ta → ERest bodyB Tb → SRest bs S
          → Rel bs (C (peerAfter (repT qb)) Ta Tb S) (sBusy (tq qb))
  -- (q , bm) reported to thread B, which waits on the store
  rWaitT  : ∀ {P Ta S} qb → All (_< decoderOffsets) (proj₂ qb) → PRest (stBlockTxs (proj₁ qb) (proj₂ qb)) P → ERest bodyA Ta → SRest bs S
          → Rel bs (C P Ta (lat bodyB (b1 qb)) S) (sBusy (tq qb))
  -- Transaction lookups accumulate exactly the requested count after body confirmation.
  rWorkT : ∀ {P Ta S} qb os acc → All (_< decoderOffsets) os →
    length acc + length os ≡ length (proj₂ qb) →
    PRest (stBlockTxs (proj₁ qb) (proj₂ qb)) P → ERest bodyA Ta → SRest bs S →
    Rel bs (C P Ta (lat bodyB (serveTxs nS lS dS (proj₁ qb) os acc)) S) (sReady (tq qb))
  -- The producer has received the complete indexed reply and will send its transactions.
  rSendT : ∀ {Ta Tb S} qb acc → length (map proj₂ acc) ≡ length (proj₂ qb) →
    ERest bodyA Ta → ERest bodyB Tb → SRest bs S →
    Rel bs (C (peerAfter (sndT (proj₁ qb , acc))) Ta Tb S) (sReady (tq qb))
  -- Done received: the producer's `done` has no partner, the composite only drains
  rDone   : ∀ {Ta Tb S} → ERest bodyA Ta → ERest bodyB Tb → SRest bs S
          → Rel bs (C (peerAfter doneR) Ta Tb S) sClosed

  -- A missing EB stops thread A; its producer remains waiting for that body.
  rThrownB : ∀ {P Tb S} → PRest stBlock P → ERest bodyB Tb → SRest bs S
           → Rel bs (C P (lat bodyA Op.Stop) Tb S) sThrown
  -- A missing EB or offset stops thread B; its producer remains waiting for txs.
  rThrownT : ∀ {P Ta S q bm} → PRest (stBlockTxs q bm) P → ERest bodyA Ta → SRest bs S
           → Rel bs (C P Ta (lat bodyB Op.Stop) S) sThrown

  -- A decoder failure stops the producer before either application report.
  rDecode : ∀ {Ta Tb S} → ERest bodyA Ta → ERest bodyB Tb → SRest bs S
          → Rel bs (C (peerAfter LOp.Stop) Ta Tb S) sIdle

-- the initial states are related
rel₀ : ∀ bs → Rel bs (serverModel bs) server₀
rel₀ bs = rIdle pHead eHead eHead sHead

-- The body producer cannot send while its stopped thread has no reply command.
thrownB-no-ev : ∀ {bs P Tb S} → PRest stBlock P → ERest bodyB Tb → SRest bs S →
  ∀ {e M′} → ¬ (C P (lat bodyA Op.Stop) Tb S ─[ ev (evl e) ]─► M′)
thrownB-no-ev pr eb ss st with comp-ev (prest-ns pr) alph-stop (alphB-rest eb) (srest-alph ss) st
... | eP na _ p with pblk-ev pr p
...   | _ , refl , _ = na _
thrownB-no-ev pr eb ss st | eAA _ _ a = stop-no-ev a
thrownB-no-ev pr eb ss st | eAB _ p b with pblk-ev pr p | erestB-ev eb b
... | _ , refl , _ | _ , eq , _ = case cong tag eq of λ ()
thrownB-no-ev pr eb ss st | eSA _ a _ = stop-no-ev a
thrownB-no-ev pr eb ss st | eSB se b _ with erestB-ev eb b
... | _ , refl , _ = se
thrownB-no-ev pr eb ss st | eBoth a _ = stop-no-ev a

-- The tx producer cannot send while its stopped thread has no reply command.
thrownT-no-ev : ∀ {bs P Ta S q bm} → PRest (stBlockTxs q bm) P → ERest bodyA Ta → SRest bs S →
  ∀ {e M′} → ¬ (C P Ta (lat bodyB Op.Stop) S ─[ ev (evl e) ]─► M′)
thrownT-no-ev pr ea ss st with comp-ev (prest-ns pr) (alphA-rest ea) alph-stop (srest-alph ss) st
... | eP na _ p with ptx-ev pr p
...   | _ , refl , _ = na _
thrownT-no-ev pr ea ss st | eAA _ p a with ptx-ev pr p | erestA-ev ea a
... | _ , refl , _ | _ , eq , _ = case cong tag eq of λ ()
thrownT-no-ev pr ea ss st | eAB _ _ b = stop-no-ev b
thrownT-no-ev pr ea ss st | eSA se a _ with erestA-ev ea a
... | _ , refl , _ = se
thrownT-no-ev pr ea ss st | eSB _ b _ = stop-no-ev b
thrownT-no-ev pr ea ss st | eBoth _ b = stop-no-ev b

-- Stopping the producer leaves both serving threads waiting for reports.
decode-no-ev : ∀ {bs Ta Tb S} → ERest bodyA Ta → ERest bodyB Tb → SRest bs S →
  ∀ {e M′} → ¬ (C (peerAfter LOp.Stop) Ta Tb S ─[ ev (evl e) ]─► M′)
decode-no-ev ea eb ss st with comp-ev peer-ns (alphA-rest ea) (alphB-rest eb) (srest-alph ss) st
... | eP _ _ p = p-stop-no-ev p
... | eAA _ p _ = p-stop-no-ev p
... | eAB _ p _ = p-stop-no-ev p
... | eSA se a _ with erestA-ev ea a
...   | _ , refl , _ = se
decode-no-ev ea eb ss st | eSB se b _ with erestB-ev eb b
... | _ , refl , _ = se
decode-no-ev ea eb ss st | eBoth a b with erestA-ev ea a | erestB-ev eb b
... | _ , refl , _ | _ , eq , _ = case cong tag eq of λ ()

------------------------------------------------------------------------
-- The τ clause
------------------------------------------------------------------------

-- a related state reached silently, the spec standing still
stay : ∀ {bs M s} → Rel bs M s → Σ[ s′ ∈ St ] (s ⇒⟨ [] ⟩ s′ × Rel bs M s′)
stay r = _ , done , r

-- every model τ keeps the relation with the spec standing still
sim-τ : ∀ {bs M M′ s} → Rel bs M s → M ─[ τ ]─► M′ → Σ[ s′ ∈ St ] (s ⇒⟨ [] ⟩ s′ × Rel bs M′ s′)
sim-τ (rIdle pr ea eb ss) st with comp-τ st
... | τP s′ = stay (rIdle (prest-τ pr s′) ea eb ss)
... | τA s′ = stay (rIdle pr (erestA-τ ea s′) eb ss)
... | τB s′ = stay (rIdle pr ea (erestB-τ eb s′) ss)
... | τS s′ = stay (rIdle pr ea eb (srest-τ ss s′))
sim-τ (rReqB q ea eb ss) st with comp-τ st
... | τP s′ = ⊥-elim (p-no-τ refl s′)
... | τA s′ = stay (rReqB q (erestA-τ ea s′) eb ss)
... | τB s′ = stay (rReqB q ea (erestB-τ eb s′) ss)
... | τS s′ = stay (rReqB q ea eb (srest-τ ss s′))
sim-τ (rWaitB q pr eb ss) st with comp-τ st
... | τP s′ = stay (rWaitB q (prest-τ pr s′) eb ss)
... | τA s′ = ⊥-elim (a1-no-τ {q} s′)
... | τB s′ = stay (rWaitB q pr (erestB-τ eb s′) ss)
... | τS s′ = stay (rWaitB q pr eb (srest-τ ss s′))
sim-τ (rReadyB q pr eb ss) st with comp-τ st
... | τP s′ = stay (rReadyB q (prest-τ pr s′) eb ss)
... | τA s′ = ⊥-elim (loop-out-no-τ _ _ _ _ s′)
... | τB s′ = stay (rReadyB q pr (erestB-τ eb s′) ss)
... | τS s′ = stay (rReadyB q pr eb (srest-τ ss s′))
sim-τ (rSendB q ea eb ss) st with comp-τ st
... | τP s′ = ⊥-elim (p-no-τ refl s′)
... | τA s′ = stay (rSendB q (erestA-τ ea s′) eb ss)
... | τB s′ = stay (rSendB q ea (erestB-τ eb s′) ss)
... | τS s′ = stay (rSendB q ea eb (srest-τ ss s′))
sim-τ (rReqT qb bounds ea eb ss) st with comp-τ st
... | τP s′ = ⊥-elim (p-no-τ refl s′)
... | τA s′ = stay (rReqT qb bounds (erestA-τ ea s′) eb ss)
... | τB s′ = stay (rReqT qb bounds ea (erestB-τ eb s′) ss)
... | τS s′ = stay (rReqT qb bounds ea eb (srest-τ ss s′))
sim-τ (rWaitT qb bounds pr ea ss) st with comp-τ st
... | τP s′ = stay (rWaitT qb bounds (prest-τ pr s′) ea ss)
... | τA s′ = stay (rWaitT qb bounds pr (erestA-τ ea s′) ss)
... | τB s′ = ⊥-elim (b1-no-τ {qb} s′)
... | τS s′ = stay (rWaitT qb bounds pr ea (srest-τ ss s′))
sim-τ (rWorkT qb os acc bounds count pr ea ss) st with comp-τ st
... | τP s′ = stay (rWorkT qb os acc bounds count (prest-τ pr s′) ea ss)
... | τA s′ = stay (rWorkT qb os acc bounds count pr (erestA-τ ea s′) ss)
... | τB s′ = ⊥-elim (work-no-τ bounds s′)
... | τS s′ = stay (rWorkT qb os acc bounds count pr ea (srest-τ ss s′))
sim-τ (rSendT qb acc count ea eb ss) st with comp-τ st
... | τP s′ = ⊥-elim (p-no-τ refl s′)
... | τA s′ = stay (rSendT qb acc count (erestA-τ ea s′) eb ss)
... | τB s′ = stay (rSendT qb acc count ea (erestB-τ eb s′) ss)
... | τS s′ = stay (rSendT qb acc count ea eb (srest-τ ss s′))
sim-τ (rDone ea eb ss) st with comp-τ st
... | τP s′ = ⊥-elim (p-no-τ refl s′)
... | τA s′ = stay (rDone (erestA-τ ea s′) eb ss)
... | τB s′ = stay (rDone ea (erestB-τ eb s′) ss)
... | τS s′ = stay (rDone ea eb (srest-τ ss s′))

sim-τ (rThrownB pr eb ss) st with comp-τ st
... | τP s′ = stay (rThrownB (prest-τ pr s′) eb ss)
... | τA s′ = ⊥-elim (stop-no-τ s′)
... | τB s′ = stay (rThrownB pr (erestB-τ eb s′) ss)
... | τS s′ = stay (rThrownB pr eb (srest-τ ss s′))
sim-τ (rThrownT pr ea ss) st with comp-τ st
... | τP s′ = stay (rThrownT (prest-τ pr s′) ea ss)
... | τA s′ = stay (rThrownT pr (erestA-τ ea s′) ss)
... | τB s′ = ⊥-elim (stop-no-τ s′)
... | τS s′ = stay (rThrownT pr ea (srest-τ ss s′))

sim-τ (rDecode ea eb ss) st with comp-τ st
... | τP s′ = ⊥-elim (p-no-τ refl s′)
... | τA s′ = stay (rDecode (erestA-τ ea s′) eb ss)
... | τB s′ = stay (rDecode ea (erestB-τ eb s′) ss)
... | τS s′ = stay (rDecode ea eb (srest-τ ss s′))
