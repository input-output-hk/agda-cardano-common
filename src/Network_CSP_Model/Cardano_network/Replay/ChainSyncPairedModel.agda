{-# OPTIONS --guardedness #-}

-- ChainSync instance of the shared exact-payload asynchronous PTree composition.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.ChainSyncPairedModel (p : Params) where
open import Relation.Binary.Definitions using (DecidableEquality)
open import Class.DecEq using (_≟_)
open import Process_Trees using (ExtI)
open import Cardano_network.Data p using (Payload; DecEq-Payload)
open import Cardano_network.ChainSync p using (CSEv; Rr; sendCS; receiveCS)
open import CSP.AsyncPair.Flow using (application; send; receive) public
import CSP.AsyncPair.Flow as F
import Semantics.LTS {E = CSEv} {I = ExtI CSEv} as Local

-- Retain the previous full-payload equality, including the transport envelope.
packetEq : DecidableEquality Payload
packetEq = _≟_

-- Keep the original monomorphic ChainSync flow type as a compatibility alias.
Flow : Set
Flow = F.Flow Payload

-- Keep the existing interpretation of wire and application channels unchanged.
flow : Local.Event → Flow
flow (Local.evLabel _ (sendCS _ _) payload) = send payload
flow (Local.evLabel _ (receiveCS _ _) payload) = receive payload
flow _ = application

open import CSP.AsyncPair.Model CSEv (ExtI CSEv) Rr Payload packetEq flow public
