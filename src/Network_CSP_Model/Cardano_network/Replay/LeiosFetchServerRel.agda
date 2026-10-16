{-# OPTIONS --guardedness #-}

-- The simulation relation of server soundness (trace-replay Phase 5,
-- Increment 1) and its τ clause.  `Rel bs M s` relates a reachable state
-- `M = C P Ta Tb S` of `serverModel bs` to the spec state `s`.  Ten shapes,
-- by the producer's phase (Idle; per request kind: report pending, thread
-- waiting on the store, reply ready, wire send pending; Done), each with the
-- components that are not driving the phase "at rest" (pending loop-back τs
-- allowed: `PRest`, `ERest`, `SRest`).  The spec's `sServe` is matched at the
-- store rendezvous that fixes the reply (`rWaitB → rReadyB`, `rWaitT → rReadyT`).
-- Every model τ is a loop-back or a store-internal τ and leaves the spec still.
-- Invariant 1 (B7a): checked with `agda --safe` on the command line.
open import Data.Nat using (ℕ)

module Cardano_network.Replay.LeiosFetchServerRel (k : ℕ) where

open import Data.List using ([])
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (refl)

open import Process_Trees using (ExtI)
open import Cardano_network.Base using (FromResponder)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Net replayParams
  using (Net_Api; Net_Api-≟; ApiLPCar; lfpReqBlockRequest; lfpReqBlockTxsRequest; lfpSendBlock)
open import Cardano_network.Data replayParams
  using (Payload; MsgLFPBlock; MsgLFPBlockTxs; DecEq-EBPoint; DecEq-TxsRequest; DecEq-TxsReply)
open import Cardano_network.LeiosFetchP replayParams
  using (LFPEv; LFPEv-≟; apiLPev; doneLFP; stIdle; stBlock; stBlockTxs; stDone)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerLFP replayParams using (Rd; snd)
import CSP.Operators {E = LFPEv} LFPEv-≟ as LOp
open import Cardano_network.Replay.LeiosFetchServerModel using (Proc; Bodies; lS; dS; nS; serverModel; bodyStore)
open import Cardano_network.Replay.LeiosFetchServerParts
open import CSP.Laws.Traces.PrefixInversion (Net_Api-≟ {Payload}) using (loop-pfx-no-τ; loop-out-no-τ)
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_─[_]─►_; τ)

open import Cardano_network.Replay.LeiosFetchSession
  using (St; sIdle; sBusy; sReady; sClosed; Req; blockReq; blockTxsReq; server₀; module Spec)
open Spec k using (leiosFetch)
open import Semantics.Replay using (module Traces)
open Traces leiosFetch using (_⇒⟨_⟩_; done)

------------------------------------------------------------------------
-- Vocabulary
------------------------------------------------------------------------

-- the spec's BlockRequest for a reported point
rq : ApiLPCar lfpReqBlockRequest → Req
rq q = blockReq (proj₁ q) (proj₂ q)

-- the spec's BlockTxsRequest for a reported point
tq : ApiLPCar lfpReqBlockRequest → Req
tq q = blockTxsReq (proj₁ q) (proj₂ q)

-- the producer round after receiving a BlockRequest: report the point
repB : ApiLPCar lfpReqBlockRequest → Rd
repB q = LOp.Output ⦃ DecEq-EBPoint ⦄ (apiLPev lS dS lfpReqBlockRequest) q (LOp.Ret (inj₁ stBlock))

-- the producer round after receiving a BlockTxsRequest: report the point and bitmap
repT : ApiLPCar lfpReqBlockTxsRequest → Rd
repT qb = LOp.Output ⦃ DecEq-TxsRequest ⦄ (apiLPev lS dS lfpReqBlockTxsRequest) qb (LOp.Ret (inj₁ stBlockTxs))

-- the producer round sending the Block `h`
sndB : ApiLPCar lfpSendBlock → Rd
sndB h = snd lS dS FromResponder (MsgLFPBlock h) stIdle

-- the producer round sending the (empty) BlockTxs for point `q`
sndT : ApiLPCar lfpReqBlockRequest → Rd
sndT q = snd lS dS FromResponder (MsgLFPBlockTxs q []) stIdle

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
  rReqT   : ∀ {Ta Tb S} qb → ERest bodyA Ta → ERest bodyB Tb → SRest bs S
          → Rel bs (C (peerAfter (repT qb)) Ta Tb S) (sBusy (tq (proj₁ qb)))
  -- (q , bm) reported to thread B, which waits on the store
  rWaitT  : ∀ {P Ta S} qb → PRest stBlockTxs P → ERest bodyA Ta → SRest bs S
          → Rel bs (C P Ta (lat bodyB (b1 qb)) S) (sBusy (tq (proj₁ qb)))
  -- thread B holds the reply for q: ready
  rReadyT : ∀ {P Ta S} q → PRest stBlockTxs P → ERest bodyA Ta → SRest bs S
          → Rel bs (C P Ta (lat bodyB (b2 q)) S) (sReady (tq q))
  -- the producer is about to send the BlockTxs for q
  rSendT  : ∀ {Ta Tb S} q → ERest bodyA Ta → ERest bodyB Tb → SRest bs S
          → Rel bs (C (peerAfter (sndT q)) Ta Tb S) (sReady (tq q))
  -- Done received: the producer's `done` has no partner, the composite only drains
  rDone   : ∀ {Ta Tb S} → ERest bodyA Ta → ERest bodyB Tb → SRest bs S
          → Rel bs (C (peerAfter doneR) Ta Tb S) sClosed

-- the initial states are related
rel₀ : ∀ bs → Rel bs (serverModel bs) server₀
rel₀ bs = rIdle pHead eHead eHead sHead

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
... | τA s′ = ⊥-elim (loop-pfx-no-τ _ _ _ s′)
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
sim-τ (rReqT qb ea eb ss) st with comp-τ st
... | τP s′ = ⊥-elim (p-no-τ refl s′)
... | τA s′ = stay (rReqT qb (erestA-τ ea s′) eb ss)
... | τB s′ = stay (rReqT qb ea (erestB-τ eb s′) ss)
... | τS s′ = stay (rReqT qb ea eb (srest-τ ss s′))
sim-τ (rWaitT qb pr ea ss) st with comp-τ st
... | τP s′ = stay (rWaitT qb (prest-τ pr s′) ea ss)
... | τA s′ = stay (rWaitT qb pr (erestA-τ ea s′) ss)
... | τB s′ = ⊥-elim (loop-pfx-no-τ _ _ _ s′)
... | τS s′ = stay (rWaitT qb pr ea (srest-τ ss s′))
sim-τ (rReadyT q pr ea ss) st with comp-τ st
... | τP s′ = stay (rReadyT q (prest-τ pr s′) ea ss)
... | τA s′ = stay (rReadyT q pr (erestA-τ ea s′) ss)
... | τB s′ = ⊥-elim (loop-out-no-τ ⦃ DecEq-TxsReply ⦄ _ _ _ _ s′)
... | τS s′ = stay (rReadyT q pr ea (srest-τ ss s′))
sim-τ (rSendT q ea eb ss) st with comp-τ st
... | τP s′ = ⊥-elim (p-no-τ refl s′)
... | τA s′ = stay (rSendT q (erestA-τ ea s′) eb ss)
... | τB s′ = stay (rSendT q ea (erestB-τ eb s′) ss)
... | τS s′ = stay (rSendT q ea eb (srest-τ ss s′))
sim-τ (rDone ea eb ss) st with comp-τ st
... | τP s′ = ⊥-elim (p-no-τ refl s′)
... | τA s′ = stay (rDone (erestA-τ ea s′) eb ss)
... | τB s′ = stay (rDone ea (erestB-τ eb s′) ss)
... | τS s′ = stay (rDone ea eb (srest-τ ss s′))
