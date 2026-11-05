{-# OPTIONS --safe #-}

-- One pending Send hook permits one recorded Receive ahead, independently in either direction.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.PacketCountPrecheck
  (Notification Return : Set) where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++; ++-identityʳ)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (_+_; _≤_; _≤?_)
open import Data.Nat.Properties using (m≤m+n; ≤-refl; ≤-trans)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; subst)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (_×-dec_)
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Notification Return as Rows
import Cardano_network.LeiosNotifyPipeLookahead.DriverConservation Notification Return as Conservation
import Cardano_network.Replay.LeiosNotifyPipeLookahead.PacketPrecheck Notification Return as Packet

-- The numerical argument is independent of message equality, constructors and payload representation.
module Counts (A : Set) where
  module P = Conservation.Packet A

  -- A single pending Send contributes either zero or exactly one additional committed packet.
  pending-bound : (sent : List A) (pending : Maybe A) →
    length (sent ++ P.pending pending) ≤ length sent + 1
  pending-bound sent nothing rewrite ++-identityʳ sent = m≤m+n (length sent) 1
  pending-bound sent (just value) rewrite length-++ sent {ys = value ∷ []} = ≤-refl

  -- Recorded receives form a prefix of all committed sends; pending Receive and FIFO remain suffixes.
  received-total : (sent received : List A) {ps pr : Maybe A} {queue : List A} → P.Balance sent received ps pr queue →
    length received ≤ length (sent ++ P.pending ps)
  received-total sent received {pr = pr} {queue} balance =
    subst (length received ≤_) (sym (cong length balance))
      (subst (length received ≤_) (sym (length-++ received {ys = P.pending pr ++ queue}))
        (m≤m+n (length received) (length (P.pending pr ++ queue))))

  -- Every balanced history has at most one more recorded receive than recorded sends.
  receive-bound : (sent received : List A) {ps pr : Maybe A} {queue : List A} → P.Balance sent received ps pr queue →
    length received ≤ length sent + 1
  receive-bound sent received {ps} {pr} {queue} balance = ≤-trans
    (received-total sent received {ps = ps} {pr = pr} {queue = queue} balance) (pending-bound sent ps)

module Commands = Counts D.ClientMessage
module Responses = Counts D.ServerMessage

-- Sends can exceed receives arbitrarily; only a receiver's lead is bounded by its peer's pending slot.
Pass : List Rows.ClientRow → List Rows.ServerRow → Set
Pass client server =
  length (Packet.serverReceives server) ≤ length (Packet.clientSends client) + 1 ×
  length (Packet.clientReceives client) ≤ length (Packet.serverSends server) + 1

-- Two natural-number decisions require neither Notification equality nor an inhabited Return carrier.
decide : (client : List Rows.ClientRow) (server : List Rows.ServerRow) → Dec (Pass client server)
decide client server =
  (length (Packet.serverReceives server) ≤? length (Packet.clientSends client) + 1) ×-dec
  (length (Packet.clientReceives client) ≤? length (Packet.serverSends server) + 1)

-- Exact source conservation and merge independence establish both bounds for every original fresh run.
necessary : ∀ {contract client server events target} → Rows.Merge client server events →
  D.Run contract D.initial events target → Pass client server
necessary {client = client} {server} {target = target} merged run =
  Commands.receive-bound (Packet.clientSends client) (Packet.serverReceives server)
    {ps = D.pendingClientSend target} {pr = D.pendingServerRecv target} {queue = D.clientToServer target}
    (Conservation.to-server balanced) ,
  Responses.receive-bound (Packet.serverSends server) (Packet.clientReceives client)
    {ps = D.pendingServerSend target} {pr = D.pendingClientRecv target} {queue = D.serverToClient target}
    (Conservation.to-client balanced)
  where
  -- Pending Send/Receive hooks and FIFO contents retain their exact original model values.
  balanced : Conservation.Balanced (Packet.extend Conservation.empty client server) target
  balanced = subst (λ history → Conservation.Balanced history target)
    (Packet.merge-history merged Conservation.empty) (Conservation.initial-conservation run)
