{-# OPTIONS --guardedness #-}

-- TxSubmission2 instance of the shared exact-payload asynchronous PTree composition.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.TxSubmission2PairedModel (p : Params) where
open import Relation.Binary.Definitions using (DecidableEquality)
open import Class.DecEq using (_≟_)
open import Process_Trees using (ExtI)
open import Cardano_network.Data p using (Payload; DecEq-Payload)
open import Cardano_network.TxSubmission p using (TSEv; Rr; sendTS; receiveTS)
open import CSP.AsyncPair.Flow using (application; send; receive) public
import CSP.AsyncPair.Flow as F
import Semantics.LTS {E = TSEv} {I = ExtI TSEv} as Local

-- Compare complete payloads, including time, mode and length metadata.
packetEq : DecidableEquality Payload
packetEq = _≟_

-- Classify local events as application actions, sends or receives.
Flow : Set
Flow = F.Flow Payload

-- Wire events update the medium; application actions preserve its queues.
flow : Local.Event → Flow
flow (Local.evLabel _ (sendTS _ _) payload) = send payload
flow (Local.evLabel _ (receiveTS _ _) payload) = receive payload
flow _ = application

open import CSP.AsyncPair.Model TSEv (ExtI TSEv) Rr Payload packetEq flow public
