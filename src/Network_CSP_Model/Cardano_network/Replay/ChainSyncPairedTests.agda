{-# OPTIONS --safe #-}

-- Inhabited paired runs, exhaustive rejections, and a local-legality counterexample.
module Cardano_network.Replay.ChainSyncPairedTests where

open import Data.List using (List; []; _∷_; take)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.Replay.ChainSyncSession
import Cardano_network.Replay.ChainSyncPairedSession as P

-- The client pipelines while the server consumes requests sequentially.
clientRows : List E
clientRows = (Send , requestNext) ∷ (Send , requestNext) ∷
  (Recv , awaitReply) ∷ (Recv , rollForward) ∷ (Recv , rollBackward) ∷
  (Send , findIntersect) ∷ (Recv , intersectFound) ∷ (Send , doneK) ∷ []

-- Server-local order retains response handoffs before the next request.
serverRows : List E
serverRows = (Recv , requestNext) ∷ (Send , awaitReply) ∷ (Send , rollForward) ∷
  (Recv , requestNext) ∷ (Send , rollBackward) ∷
  (Recv , findIntersect) ∷ (Send , intersectFound) ∷ (Recv , doneK) ∷ []

-- A successful decision carries a concrete merged run with exact projections.
paired-run : P.Witness 2 (P.initial 2) clientRows serverRows
paired-run = toWitness {a? = P.witness? 2 (P.initial 2) clientRows serverRows} tt

-- The pipeline capacity remains independent of either network queue.
too-shallow : ¬ P.Compatible 1 (P.initial 1) clientRows serverRows
too-shallow = toWitnessFalse {a? = P.compatible? 1 (P.initial 1) clientRows serverRows} tt

-- One locally legal client receives a different response from the server's send.
mismatchedClient : List E
mismatchedClient = (Send , requestNext) ∷ (Recv , rollForward) ∷ []

-- RollBackward is individually legal at the server for the same request.
mismatchedServer : List E
mismatchedServer = (Recv , requestNext) ∷ (Send , rollBackward) ∷ []

-- Both local checks pass, so independent session replay cannot find the mismatch.
local-client : Spec.HasTrace 2 client initial mismatchedClient
local-client = toWitness {a? = Spec.check 2 client mismatchedClient} tt

-- The opposite endpoint is also locally legal.
local-server : Spec.HasTrace 2 server initial mismatchedServer
local-server = toWitness {a? = Spec.check 2 server mismatchedServer} tt

-- No order-preserving merge of those legal local traces satisfies the FIFO.
pair-mismatch : ¬ P.Witness 2 (P.initial 2) mismatchedClient mismatchedServer
pair-mismatch = toWitnessFalse {a? = P.witness? 2 (P.initial 2) mismatchedClient mismatchedServer} tt

-- EOF with transmitted-but-unconsumed work is accepted as a prefix.
inflight : P.Witness 2 (P.initial 2)
  ((Send , requestNext) ∷ (Send , requestNext) ∷ []) []
inflight = toWitness {a? = P.witness? 2 (P.initial 2)
  ((Send , requestNext) ∷ (Send , requestNext) ∷ []) []} tt

-- A receive cannot be justified by an uncaptured send at a fresh boundary.
missing-send : ¬ P.Compatible 2 (P.initial 2) [] ((Recv , requestNext) ∷ [])
missing-send = toWitnessFalse {a? = P.compatible? 2 (P.initial 2) [] ((Recv , requestNext) ∷ [])} tt

-- Zero disables RequestNext but permits intersection and closure.
zero-pair : P.Witness 0 (P.initial 0)
  ((Send , findIntersect) ∷ (Recv , intersectNotFound) ∷ (Send , doneK) ∷ [])
  ((Recv , findIntersect) ∷ (Send , intersectNotFound) ∷ (Recv , doneK) ∷ [])
zero-pair = toWitness {a? = P.witness? 0 (P.initial 0)
  ((Send , findIntersect) ∷ (Recv , intersectNotFound) ∷ (Send , doneK) ∷ [])
  ((Recv , findIntersect) ∷ (Send , intersectNotFound) ∷ (Recv , doneK) ∷ [])} tt

-- The witness projection retains every client row.
exact-client-order : P.project 2 client (P.Witness.events paired-run) ≡ clientRows
exact-client-order = P.Witness.clientOrder paired-run

-- Projecting the witness recovers a legal complete client input trace.
projected-client : Spec.HasTrace 2 client initial clientRows
projected-client = P.compatible-client 2 (P.fromWitness 2 paired-run)

-- Projecting it likewise recovers a legal server input trace.
projected-server : Spec.HasTrace 2 server initial serverRows
projected-server = P.compatible-server 2 (P.fromWitness 2 paired-run)

-- The concrete witness sends both pipelined requests before server consumption.
pipeline-first : take 2 (P.Witness.events paired-run) ≡
  ((client , Send , requestNext) ∷ (client , Send , requestNext) ∷ [])
pipeline-first = refl

-- Two locally legal replies still have to arrive in the server's FIFO order.
fifo-order : ¬ P.Compatible 2 (P.initial 2)
  ((Send , requestNext) ∷ (Send , requestNext) ∷ (Recv , rollForward) ∷ (Recv , rollBackward) ∷ [])
  ((Recv , requestNext) ∷ (Send , rollBackward) ∷ (Recv , requestNext) ∷ (Send , rollForward) ∷ [])
fifo-order = toWitnessFalse {a? = P.compatible? 2 (P.initial 2)
  ((Send , requestNext) ∷ (Send , requestNext) ∷ (Recv , rollForward) ∷ (Recv , rollBackward) ∷ [])
  ((Recv , requestNext) ∷ (Send , rollBackward) ∷ (Recv , requestNext) ∷ (Send , rollForward) ∷ [])} tt

-- Here the client can issue its next request while the server can send a reply.
both-ready : P.State 2
both-ready = P.paired (pending 1 canAwait) (pending 1 canAwait) [] []

-- Both possible first-row choices have inhabited paired executions.
both-choices : P.Witness 2 both-ready ((Send , requestNext) ∷ []) ((Send , rollForward) ∷ [])
both-choices = toWitness {a? = P.witness? 2 both-ready
  ((Send , requestNext) ∷ []) ((Send , rollForward) ∷ [])} tt

-- The other scheduling order is permitted by the independently checked machine.
server-first : P.HasTrace 2 both-ready
  ((server , Send , rollForward) ∷ (client , Send , requestNext) ∷ [])
server-first = toWitness {a? = P.checkOrdered 2 both-ready
  ((server , Send , rollForward) ∷ (client , Send , requestNext) ∷ [])} tt
