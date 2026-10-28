{-# OPTIONS --guardedness #-}

-- Fetch composition using the store-backed server of the existing soundness proof.
module Cardano_network.Replay.LeiosFetchPairedStoreModel where

open import Data.Nat using (ℕ)
open import Data.Unit using (⊤)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Class.DecEq using (_≟_)
open import Process_Trees using (PTree; ExtI)
open import Cardano_network.Base using (Dir; N2N_LeiosFetch)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Data replayParams using (Payload; DecEq-Payload)
open import Cardano_network.Net replayParams using (Link; Net_Api; input; output)
open import Cardano_network.LeiosFetchP replayParams using (Rr; LFPEv)
import Cardano_network.LeiosFetchPipe replayParams as Pipe
import Cardano_network.Parametric.Leios.PeersP replayParams as Peers
import CSP.Rename {E₁ = LFPEv} {E₂ = Net_Api Payload}
  Peers.ιLFP Peers.ιLFP⁻¹ Peers.ιLFP-linv as Rename
open import Cardano_network.Replay.LeiosFetchServerModel using (Bodies; serverModel)
open import CSP.AsyncPair.Flow using (Flow; application; send; receive)
import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as Local

-- Concrete queues retain the complete original model packet.
packetEq : DecidableEquality Payload
packetEq = _≟_

-- Only Fetch wire events affect this session's medium; store/API events stay local.
flow : Local.Event → Flow Payload
flow (Local.evLabel _ (input _ _ N2N_LeiosFetch) payload) = send payload
flow (Local.evLabel _ (output _ _ N2N_LeiosFetch) payload) = receive payload
flow _ = application

open import CSP.AsyncPair.Model (Net_Api Payload) (ExtI (Net_Api Payload)) Rr Payload packetEq flow public

-- Reuse the established injective rename on the existing pipelined client.
pipelinedClient : ℕ → Link → Dir → Proc
pipelinedClient k l d = Rename.renameMap (Pipe.pipe k l d)

-- The server endpoint is fixed exactly as in LeiosFetchServerModel (link zero, hi).
system : ℕ → Link → Dir → Bodies → PTree PairEv PairI ⊤
system k l d bs = compose (pipelinedClient k l d) (serverModel bs) empty
