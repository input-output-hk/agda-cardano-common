{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)

-- SERVER SOUNDNESS (trace-replay Phase 5, Increment 1; amendment B1, no premise):
-- every √-free run of `serverModel bs`, for every body store `bs`, is observed
-- (under `clsS`/`forget`) as a trace of the first-order server spec.
-- Obtained from the generic `Bridge.sound` with the simulation `Rel bs`
-- (`ServerRel`, `ServerSimEv`); the spec witness `sound` builds is then
-- swapped for the given `es` with the same observation (`trace-forget`: the
-- spec's steps read only what `forget` keeps).
-- Invariant 1 (B7a): checked with `agda --safe` on the command line.
module Cardano_network.Replay.ServerSound (k : ℕ) where

open import Data.List using (List; []; _∷_; map)
open import Data.List.Properties using (∷-injectiveˡ; ∷-injectiveʳ)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Process_Trees using (ExtI)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Net replayParams using (Net_Api)
open import Cardano_network.Data replayParams using (Payload)
open import Cardano_network.Replay.BridgeServer using (serverModel)
open import Cardano_network.Replay.Obs
  using (ObsS; clsS; forget; blockReq♭; block♭; txsReq♭; txs♭; done♭)
open import Cardano_network.Replay.ServerRel k using (Rel; rel₀; sim-τ)
open import Cardano_network.Replay.ServerSimEv k using (sim-ev)
open import Semantics.Deadlock {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_⟹∖√⟨_⟩_)
import Semantics.Replay.Bridge {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as BrS

open import Cardano_network.Replay.LeiosFetchSession
  using ( St; E; server₀; MsgLeiosBlockRequest; MsgLeiosBlock; MsgLeiosBlockTxsRequest
        ; MsgLeiosBlockTxs; MsgLeiosDone; module Spec )
open Spec k
open import Semantics.Replay using (module Traces)
open Traces leiosFetch using (_⇒⟨_⟩_; done; tau; vis; HasTrace)

------------------------------------------------------------------------
-- The spec reads only what `forget` keeps
------------------------------------------------------------------------

-- an event observed as a BlockRequest is that BlockRequest
f-br : ∀ {e d h s} → forget e ≡ (d , blockReq♭ h s) → e ≡ (d , MsgLeiosBlockRequest h s)
f-br {_ , MsgLeiosBlockRequest _ _}      refl = refl
f-br {_ , MsgLeiosBlock _ _}             ()
f-br {_ , MsgLeiosBlockTxsRequest _ _ _ _} ()
f-br {_ , MsgLeiosBlockTxs _ _ _ _ _}    ()
f-br {_ , MsgLeiosDone}                  ()

-- an event observed as a Block is a Block of some size
f-b : ∀ {e d h} → forget e ≡ (d , block♭ h) → Σ[ z ∈ ℕ ] e ≡ (d , MsgLeiosBlock h z)
f-b {_ , MsgLeiosBlockRequest _ _}      ()
f-b {_ , MsgLeiosBlock _ _}             refl = _ , refl
f-b {_ , MsgLeiosBlockTxsRequest _ _ _ _} ()
f-b {_ , MsgLeiosBlockTxs _ _ _ _ _}    ()
f-b {_ , MsgLeiosDone}                  ()

-- an event observed as a BlockTxsRequest is one, with some numTxs and bitmaps
f-tr : ∀ {e d h s} → forget e ≡ (d , txsReq♭ h s)
     → Σ[ n ∈ ℕ ] Σ[ b ∈ List (ℕ × ℕ) ] e ≡ (d , MsgLeiosBlockTxsRequest h s n b)
f-tr {_ , MsgLeiosBlockRequest _ _}      ()
f-tr {_ , MsgLeiosBlock _ _}             ()
f-tr {_ , MsgLeiosBlockTxsRequest _ _ _ _} refl = _ , _ , refl
f-tr {_ , MsgLeiosBlockTxs _ _ _ _ _}    ()
f-tr {_ , MsgLeiosDone}                  ()

-- an event observed as a BlockTxs is one, with some numTxs, size and bitmaps
f-t : ∀ {e d h s} → forget e ≡ (d , txs♭ h s)
    → Σ[ n ∈ ℕ ] Σ[ z ∈ ℕ ] Σ[ b ∈ List (ℕ × ℕ) ] e ≡ (d , MsgLeiosBlockTxs h s n z b)
f-t {_ , MsgLeiosBlockRequest _ _}      ()
f-t {_ , MsgLeiosBlock _ _}             ()
f-t {_ , MsgLeiosBlockTxsRequest _ _ _ _} ()
f-t {_ , MsgLeiosBlockTxs _ _ _ _ _}    refl = _ , _ , _ , refl
f-t {_ , MsgLeiosDone}                  ()

-- an event observed as Done is Done
f-d : ∀ {e d} → forget e ≡ (d , done♭) → e ≡ (d , MsgLeiosDone)
f-d {_ , MsgLeiosBlockRequest _ _}      ()
f-d {_ , MsgLeiosBlock _ _}             ()
f-d {_ , MsgLeiosBlockTxsRequest _ _ _ _} ()
f-d {_ , MsgLeiosBlockTxs _ _ _ _ _}    ()
f-d {_ , MsgLeiosDone}                  refl = refl

-- a spec step accepts any event with the same observation
step-forget : ∀ {s s′ e e′} → forget e ≡ forget e′ → s -[ e′ ]→ s′ → s -[ e ]→ s′
step-forget eq (cSendBlockReq lt) with f-br eq
... | refl = cSendBlockReq lt
step-forget eq (cSendTxsReq lt) with f-tr eq
... | _ , _ , refl = cSendTxsReq lt
step-forget eq cRecvBlock with f-b eq
... | _ , refl = cRecvBlock
step-forget eq cRecvTxs with f-t eq
... | _ , _ , _ , refl = cRecvTxs
step-forget eq cSendDone with f-d eq
... | refl = cSendDone
step-forget eq sRecvBlockReq with f-br eq
... | refl = sRecvBlockReq
step-forget eq sRecvTxsReq with f-tr eq
... | _ , _ , refl = sRecvTxsReq
step-forget eq sSendBlock with f-b eq
... | _ , refl = sSendBlock
step-forget eq sSendTxs with f-t eq
... | _ , _ , _ , refl = sSendTxs
step-forget eq sRecvDone with f-d eq
... | refl = sRecvDone

-- spec runs accept any trace with the same observation
trace-forget : ∀ {s s′ es es′} → map forget es ≡ map forget es′ → s ⇒⟨ es′ ⟩ s′ → s ⇒⟨ es ⟩ s′
trace-forget {es = []}    eq done = done
trace-forget {es = _ ∷ _} () done
trace-forget eq (tau st r) = tau st (trace-forget eq r)
trace-forget {es = []}    () (vis st r)
trace-forget {es = _ ∷ _} eq (vis st r) =
  vis (step-forget (∷-injectiveˡ eq) st) (trace-forget (∷-injectiveʳ eq) r)

------------------------------------------------------------------------
-- The theorem
------------------------------------------------------------------------

-- the spec simulates the server composite over the store holding `bs`
serverSim : ∀ bs → BrS.Sim leiosFetch clsS forget (Rel bs)
serverSim bs = record { sim-τ = sim-τ ; sim-ev = sim-ev }

-- SERVER SOUNDNESS: what the log can see of any run of `serverModel bs` is a server-spec trace
server-sound : ∀ bs {t M es} → serverModel bs ⟹∖√⟨ t ⟩ M → ObsS t es → HasTrace server₀ es
server-sound bs run o with BrS.sound leiosFetch clsS forget (serverSim bs) (rel₀ bs) run
... | _ , s′ , o′ , r , _ = s′ , trace-forget (trans (sym o) o′) r
