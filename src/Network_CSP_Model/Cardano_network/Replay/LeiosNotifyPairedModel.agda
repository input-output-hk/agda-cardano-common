{-# OPTIONS --guardedness #-}

-- Actual prototype peer PTrees connected by two initially empty exact-payload FIFOs.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosNotifyPairedModel (p : Params) where

open import Data.Nat using (ℕ)
import Cardano_network.LeiosNotifyPipe p as Pipe
open import Data.Unit using (⊤)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Class.DecEq using (_≟_)
open import Process_Trees using (PTree; ExtI)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Net p using (Link)
open import Cardano_network.Data p using (Payload; DecEq-Payload)
open import Cardano_network.LeiosNotifyP p
  using (LNPEv; sendLNP; receiveLNP; Rr; LNPclientStClient; LNPserverStClient)
open import CSP.AsyncPair.Flow using (Flow; application; send; receive)
import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv} as Local

-- A packet is the full model payload, including its transport envelope.
packetEq : DecidableEquality Payload
packetEq = _≟_

-- Wire channels move packets; original API and done events remain peer-local.
flow : Local.Event → Flow Payload
flow (Local.evLabel _ (sendLNP _ _) payload) = send payload
flow (Local.evLabel _ (receiveLNP _ _) payload) = receive payload
flow _ = application

open import CSP.AsyncPair.Model LNPEv (ExtI LNPEv) Rr Payload packetEq flow public

-- Preserve the product of the original depth-one peers as its existing entry point.
system : Link → Link → Dir → Dir → PTree PairEv PairI ⊤
system cl sl cd sd = compose (LNPclientStClient cl cd) (LNPserverStClient sl sd) empty

-- The new bounded peers share the same full-payload medium and endpoint tags.
pipelined-system : ℕ → Link → Link → Dir → Dir → PTree PairEv PairI ⊤
pipelined-system depth cl sl cd sd = compose (Pipe.client depth cl cd) (Pipe.server depth sl sd) empty
