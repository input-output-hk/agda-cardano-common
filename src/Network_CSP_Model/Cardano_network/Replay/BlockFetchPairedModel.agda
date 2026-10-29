{-# OPTIONS --guardedness #-}

-- BlockFetch instance of the shared exact-payload asynchronous PTree composition.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.BlockFetchPairedModel (p : Params) where
open import Relation.Binary.Definitions using (DecidableEquality)
open import Class.DecEq using (_≟_)
open import Process_Trees using (ExtI)
open import Cardano_network.Data p using (Payload; DecEq-Payload)
open import Cardano_network.BlockFetch p using (BFEv; Rr; sendBF; receiveBF)
open import CSP.AsyncPair.Flow using (application; send; receive) public
import CSP.AsyncPair.Flow as F
import Semantics.LTS {E = BFEv} {I = ExtI BFEv} as Local

-- Compare complete payloads, including time, mode and length metadata.
packetEq : DecidableEquality Payload
packetEq = _≟_

-- Classify local events as application actions, sends or receives.
Flow : Set
Flow = F.Flow Payload

-- Wire events update the medium; application actions preserve its queues.
flow : Local.Event → Flow
flow (Local.evLabel _ (sendBF _ _) payload) = send payload
flow (Local.evLabel _ (receiveBF _ _) payload) = receive payload
flow _ = application

open import CSP.AsyncPair.Model BFEv (ExtI BFEv) Rr Payload packetEq flow public
