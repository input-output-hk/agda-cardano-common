{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)

-- The visible clause of server soundness (trace-replay Phase 5, Increment 1).
-- Every visible step of a related composite is matched by the spec:
--   * the producer's wire receive (Idle) and wire send (Block / BlockTxs) by
--     exactly one spec event, equal under `clsS`/`forget`;
--   * the api rendezvous (report, reply command) by no spec move;
--   * the store rendezvous of the waiting thread by `sServe` — the body handed
--     over has the requested hash (`srest-get`, `ebHash = id`), which is what
--     makes the later Block carry the requested hash;
--   * the BlockTxs reply echoes the reported point (`b1-ev`, `b2-ev`).
-- Impossible rendezvous are refuted by the component alphabets (`AE`/`SE`) and,
-- between the two threads' api commands, by `tag`.
-- Invariant 1 (B7a): checked with `agda --safe` on the command line.
module Cardano_network.Replay.LeiosFetchServerSimEv (k : ℕ) where

open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Process_Trees using (ExtI)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Net replayParams using (Net_Api)
open import Cardano_network.Data replayParams using (Payload; DecEq-EBPoint; DecEq-TxsRequest)
open import Cardano_network.LeiosFetchP replayParams using (stIdle)
open import Cardano_network.Parametric.Leios.NoLivelock.PeerLFP replayParams
  using (SIdleV; siBlk; siTxs; siDone)
open import Cardano_network.Replay.LeiosFetchServerModel using (Proc; Bodies; lS; dS)
open import Cardano_network.Replay.LeiosFetchServerParts
open import Cardano_network.Replay.LeiosFetchServerRel k
open import Cardano_network.Replay.LeiosFetchObs using (ObsS)
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (Event; _─[_]─►_; ev; evl)

open import Cardano_network.Replay.LeiosFetchSession
  using (St; E; Send; Recv; MsgLeiosBlockRequest; MsgLeiosBlock; MsgLeiosBlockTxsRequest
        ; MsgLeiosBlockTxs; MsgLeiosDone; module Spec)
open Spec k
  using (leiosFetch; sRecvBlockReq; sRecvTxsReq; sRecvDone; sSendBlock; sSendTxs; sServe)
open import Semantics.Replay using (module Traces)
open Traces leiosFetch using (_⇒⟨_⟩_; done; tau; vis)

-- no Idle receive of the producer is an api label
idle-not-api : ∀ {x t′} → SIdleV lS dS x t′ → ¬ AE (renE x)
idle-not-api (siBlk _)   ()
idle-not-api (siTxs _ _) ()
idle-not-api siDone      ()

-- the matching spec run of one visible model step
Match : Bodies → Event → St → Proc → Set₁
Match bs e s M′ = Σ[ es ∈ List E ] Σ[ s′ ∈ St ] (ObsS (e ∷ []) es × s ⇒⟨ es ⟩ s′ × Rel bs M′ s′)

-- every visible model step is matched by the spec, observing the same
sim-ev : ∀ {bs M M′ s e} → Rel bs M s → M ─[ ev (evl e) ]─► M′ → Match bs e s M′

-- Idle: a wire receive starts a request (or closes)
sim-ev (rIdle pr ea eb ss) st with comp-ev (prest-ns pr) (alphA-rest ea) (alphB-rest eb) (srest-alph ss) st
... | eP _ _ stP with pidle-ev pr stP
...   | _ , _ , siBlk q , refl , refl =
        (Recv , MsgLeiosBlockRequest (proj₁ q) (proj₂ q)) ∷ [] , _ , refl , vis sRecvBlockReq done , rReqB q ea eb ss
...   | _ , _ , siTxs q bm , refl , refl =
        (Recv , MsgLeiosBlockTxsRequest (proj₁ q) (proj₂ q) 0 []) ∷ [] , _ , refl , vis sRecvTxsReq done , rReqT (q , bm) ea eb ss
...   | _ , _ , siDone , refl , refl =
        (Recv , MsgLeiosDone) ∷ [] , _ , refl , vis sRecvDone done , rDone ea eb ss
sim-ev (rIdle pr ea eb ss) st | eAA a stP _ with pidle-ev pr stP
... | _ , _ , sv , refl , _ = ⊥-elim (idle-not-api sv a)
sim-ev (rIdle pr ea eb ss) st | eAB a stP _ with pidle-ev pr stP
... | _ , _ , sv , refl , _ = ⊥-elim (idle-not-api sv a)
sim-ev (rIdle pr ea eb ss) st | eSA s stA _ with erestA-ev ea stA
... | _ , refl , _ = ⊥-elim s
sim-ev (rIdle pr ea eb ss) st | eSB s stB _ with erestB-ev eb stB
... | _ , refl , _ = ⊥-elim s
sim-ev (rIdle pr ea eb ss) st | eBoth stA stB with erestA-ev ea stA | erestB-ev eb stB
... | _ , refl , _ | _ , eq , _ = case cong tag eq of λ ()

-- BlockRequest received: the report reaches thread A
sim-ev (rReqB q ea eb ss) st with comp-ev peer-ns (alphA-rest ea) (alphB-rest eb) (srest-alph ss) st
... | eP na _ stP with p-out-ev ⦃ DecEq-EBPoint ⦄ stP
...   | refl , _ = ⊥-elim (na _)
sim-ev (rReqB q ea eb ss) st | eAA _ stP stA with p-out-ev ⦃ DecEq-EBPoint ⦄ stP | erestA-ev ea stA
... | refl , refl | _ , refl , refl = [] , _ , refl , done , rWaitB q pBack eb ss
sim-ev (rReqB q ea eb ss) st | eAB _ stP stB with p-out-ev ⦃ DecEq-EBPoint ⦄ stP | erestB-ev eb stB
... | refl , _ | _ , eq , _ = case cong tag eq of λ ()
sim-ev (rReqB q ea eb ss) st | eSA s stA _ with erestA-ev ea stA
... | _ , refl , _ = ⊥-elim s
sim-ev (rReqB q ea eb ss) st | eSB s stB _ with erestB-ev eb stB
... | _ , refl , _ = ⊥-elim s
sim-ev (rReqB q ea eb ss) st | eBoth stA stB with erestA-ev ea stA | erestB-ev eb stB
... | _ , refl , _ | _ , eq , _ = case cong tag eq of λ ()

-- thread A waits on the store: the body read fixes the reply (`sServe`)
sim-ev (rWaitB q pr eb ss) st with comp-ev (prest-ns pr) (alphA1 {q}) (alphB-rest eb) (srest-alph ss) st
... | eP na _ stP with pblk-ev pr stP
...   | _ , refl , _ = ⊥-elim (na _)
sim-ev (rWaitB q pr eb ss) st | eAA a _ stA with a1-ev {q} stA
... | _ , refl , _ = ⊥-elim a
sim-ev (rWaitB q pr eb ss) st | eAB _ stP stB with pblk-ev pr stP | erestB-ev eb stB
... | _ , refl , _ | _ , eq , _ = case cong tag eq of λ ()
sim-ev (rWaitB q pr eb ss) st | eSA _ stA stS with a1-ev {q} stA
... | x , refl , refl with srest-get {h = proj₁ q} ss stS
...   | refl , ss′ = [] , _ , refl , tau sServe done , rReadyB q pr eb ss′
sim-ev (rWaitB q pr eb ss) st | eSB s stB _ with erestB-ev eb stB
... | _ , refl , _ = ⊥-elim s
sim-ev (rWaitB q pr eb ss) st | eBoth stA stB with a1-ev {q} stA | erestB-ev eb stB
... | _ , refl , _ | _ , eq , _ = case cong tag eq of λ ()

-- reply ready: thread A commands the Block, which carries the requested hash
sim-ev (rReadyB q pr eb ss) st with comp-ev (prest-ns pr) (alphA2 {proj₁ q}) (alphB-rest eb) (srest-alph ss) st
... | eP na _ stP with pblk-ev pr stP
...   | _ , refl , _ = ⊥-elim (na _)
sim-ev (rReadyB q pr eb ss) st | eAA _ stP stA with pblk-ev pr stP | a2-ev {proj₁ q} stA
... | _ , refl , refl | refl , refl = [] , _ , refl , done , rSendB q eBack eb ss
sim-ev (rReadyB q pr eb ss) st | eAB _ stP stB with pblk-ev pr stP | erestB-ev eb stB
... | _ , refl , _ | _ , eq , _ = case cong tag eq of λ ()
sim-ev (rReadyB q pr eb ss) st | eSA s stA _ with a2-ev {proj₁ q} stA
... | refl , _ = ⊥-elim s
sim-ev (rReadyB q pr eb ss) st | eSB s stB _ with erestB-ev eb stB
... | _ , refl , _ = ⊥-elim s
sim-ev (rReadyB q pr eb ss) st | eBoth stA stB with a2-ev {proj₁ q} stA | erestB-ev eb stB
... | refl , _ | _ , eq , _ = case cong tag eq of λ ()

-- the producer sends the Block: the spec's `sSendBlock`
sim-ev (rSendB q ea eb ss) st with comp-ev peer-ns (alphA-rest ea) (alphB-rest eb) (srest-alph ss) st
... | eP _ _ stP with p-snd-ev stP
...   | refl , refl =
        (Send , MsgLeiosBlock (proj₁ q) 0) ∷ [] , _ , refl , vis sSendBlock done , rIdle pBack ea eb ss
sim-ev (rSendB q ea eb ss) st | eAA a stP _ with p-snd-ev stP
... | refl , _ = ⊥-elim a
sim-ev (rSendB q ea eb ss) st | eAB a stP _ with p-snd-ev stP
... | refl , _ = ⊥-elim a
sim-ev (rSendB q ea eb ss) st | eSA s stA _ with erestA-ev ea stA
... | _ , refl , _ = ⊥-elim s
sim-ev (rSendB q ea eb ss) st | eSB s stB _ with erestB-ev eb stB
... | _ , refl , _ = ⊥-elim s
sim-ev (rSendB q ea eb ss) st | eBoth stA stB with erestA-ev ea stA | erestB-ev eb stB
... | _ , refl , _ | _ , eq , _ = case cong tag eq of λ ()

-- BlockTxsRequest received: the report reaches thread B
sim-ev (rReqT qb ea eb ss) st with comp-ev peer-ns (alphA-rest ea) (alphB-rest eb) (srest-alph ss) st
... | eP na _ stP with p-out-ev ⦃ DecEq-TxsRequest ⦄ stP
...   | refl , _ = ⊥-elim (na _)
sim-ev (rReqT qb ea eb ss) st | eAA _ stP stA with p-out-ev ⦃ DecEq-TxsRequest ⦄ stP | erestA-ev ea stA
... | refl , _ | _ , eq , _ = case cong tag eq of λ ()
sim-ev (rReqT qb ea eb ss) st | eAB _ stP stB with p-out-ev ⦃ DecEq-TxsRequest ⦄ stP | erestB-ev eb stB
... | refl , refl | _ , refl , refl = [] , _ , refl , done , rWaitT qb pBack ea ss
sim-ev (rReqT qb ea eb ss) st | eSA s stA _ with erestA-ev ea stA
... | _ , refl , _ = ⊥-elim s
sim-ev (rReqT qb ea eb ss) st | eSB s stB _ with erestB-ev eb stB
... | _ , refl , _ = ⊥-elim s
sim-ev (rReqT qb ea eb ss) st | eBoth stA stB with erestA-ev ea stA | erestB-ev eb stB
... | _ , refl , _ | _ , eq , _ = case cong tag eq of λ ()

-- thread B waits on the store: the read confirms the EB, the reply echoes the point
sim-ev (rWaitT qb pr ea ss) st with comp-ev (prest-ns pr) (alphA-rest ea) (alphB1 {qb}) (srest-alph ss) st
... | eP na _ stP with ptx-ev pr stP
...   | _ , refl , _ = ⊥-elim (na _)
sim-ev (rWaitT qb pr ea ss) st | eAA _ stP stA with ptx-ev pr stP | erestA-ev ea stA
... | _ , refl , _ | _ , eq , _ = case cong tag eq of λ ()
sim-ev (rWaitT qb pr ea ss) st | eAB a _ stB with b1-ev {qb} stB
... | _ , refl , _ = ⊥-elim a
sim-ev (rWaitT qb pr ea ss) st | eSA s stA _ with erestA-ev ea stA
... | _ , refl , _ = ⊥-elim s
sim-ev (rWaitT qb pr ea ss) st | eSB _ stB stS with b1-ev {qb} stB
... | _ , refl , refl with srest-get {h = proj₁ (proj₁ qb)} ss stS
...   | _ , ss′ = [] , _ , refl , tau sServe done , rReadyT (proj₁ qb) pr ea ss′
sim-ev (rWaitT qb pr ea ss) st | eBoth stA stB with erestA-ev ea stA | b1-ev {qb} stB
... | _ , refl , _ | _ , eq , _ = case cong tag eq of λ ()

-- reply ready: thread B commands the BlockTxs for the reported point
sim-ev (rReadyT q pr ea ss) st with comp-ev (prest-ns pr) (alphA-rest ea) (alphB2 {q}) (srest-alph ss) st
... | eP na _ stP with ptx-ev pr stP
...   | _ , refl , _ = ⊥-elim (na _)
sim-ev (rReadyT q pr ea ss) st | eAA _ stP stA with ptx-ev pr stP | erestA-ev ea stA
... | _ , refl , _ | _ , eq , _ = case cong tag eq of λ ()
sim-ev (rReadyT q pr ea ss) st | eAB _ stP stB with ptx-ev pr stP | b2-ev {q} stB
... | _ , refl , refl | refl , refl = [] , _ , refl , done , rSendT q ea eBack ss
sim-ev (rReadyT q pr ea ss) st | eSA s stA _ with erestA-ev ea stA
... | _ , refl , _ = ⊥-elim s
sim-ev (rReadyT q pr ea ss) st | eSB s stB _ with b2-ev {q} stB
... | refl , _ = ⊥-elim s
sim-ev (rReadyT q pr ea ss) st | eBoth stA stB with erestA-ev ea stA | b2-ev {q} stB
... | _ , refl , _ | eq , _ = case cong tag eq of λ ()

-- the producer sends the BlockTxs: the spec's `sSendTxs`
sim-ev (rSendT q ea eb ss) st with comp-ev peer-ns (alphA-rest ea) (alphB-rest eb) (srest-alph ss) st
... | eP _ _ stP with p-snd-ev stP
...   | refl , refl =
        (Send , MsgLeiosBlockTxs (proj₁ q) (proj₂ q) 0 0 []) ∷ [] , _ , refl , vis sSendTxs done , rIdle pBack ea eb ss
sim-ev (rSendT q ea eb ss) st | eAA a stP _ with p-snd-ev stP
... | refl , _ = ⊥-elim a
sim-ev (rSendT q ea eb ss) st | eAB a stP _ with p-snd-ev stP
... | refl , _ = ⊥-elim a
sim-ev (rSendT q ea eb ss) st | eSA s stA _ with erestA-ev ea stA
... | _ , refl , _ = ⊥-elim s
sim-ev (rSendT q ea eb ss) st | eSB s stB _ with erestB-ev eb stB
... | _ , refl , _ = ⊥-elim s
sim-ev (rSendT q ea eb ss) st | eBoth stA stB with erestA-ev ea stA | erestB-ev eb stB
... | _ , refl , _ | _ , eq , _ = case cong tag eq of λ ()

-- after Done nothing visible can happen: `done` has no partner
sim-ev (rDone ea eb ss) st with comp-ev peer-ns (alphA-rest ea) (alphB-rest eb) (srest-alph ss) st
... | eP na _ stP with p-done-ev stP
...   | _ , refl = ⊥-elim (na _)
sim-ev (rDone ea eb ss) st | eAA _ stP stA with p-done-ev stP | erestA-ev ea stA
... | _ , refl | _ , eq , _ = case cong tag eq of λ ()
sim-ev (rDone ea eb ss) st | eAB _ stP stB with p-done-ev stP | erestB-ev eb stB
... | _ , refl | _ , eq , _ = case cong tag eq of λ ()
sim-ev (rDone ea eb ss) st | eSA s stA _ with erestA-ev ea stA
... | _ , refl , _ = ⊥-elim s
sim-ev (rDone ea eb ss) st | eSB s stB _ with erestB-ev eb stB
... | _ , refl , _ = ⊥-elim s
sim-ev (rDone ea eb ss) st | eBoth stA stB with erestA-ev ea stA | erestB-ev eb stB
... | _ , refl , _ | _ , eq , _ = case cong tag eq of λ ()
