{-# OPTIONS --guardedness #-}

-- Existing Fetch peer PTrees connected by two initially empty exact-payload FIFOs.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosFetchPairedModel (p : Params) where

open import Data.Nat using (ℕ)
open import Data.Unit using (⊤)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Class.DecEq using (_≟_)
open import Process_Trees using (PTree; ExtI)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Net p using (Link)
open import Cardano_network.Data p using (Payload; DecEq-Payload)
open import Cardano_network.LeiosFetchP p
  using (LFPEv; sendLFP; receiveLFP; Rr; LFPclientStClient; LFPserverStClient)
import Cardano_network.LeiosFetchPipe p as Pipe
open import CSP.AsyncPair.Flow using (Flow; application; send; receive)
import Semantics.LTS {E = LFPEv} {I = ExtI LFPEv} as Local

-- A packet is the full model payload, including its transport envelope.
packetEq : DecidableEquality Payload
packetEq = _≟_

-- Wire channels move packets; original API and done events remain peer-local.
flow : Local.Event → Flow Payload
flow (Local.evLabel _ (sendLFP _ _) payload) = send payload
flow (Local.evLabel _ (receiveLFP _ _) payload) = receive payload
flow _ = application

open import CSP.AsyncPair.Model LFPEv (ExtI LFPEv) Rr Payload packetEq flow public

-- Fetch uses its existing bounded client and original sequential server with free API handoffs.
system : ℕ → Link → Link → Dir → Dir → PTree PairEv PairI ⊤
system k cl sl cd sd = compose (Pipe.pipe k cl cd) (LFPserverStClient sl sd) empty
