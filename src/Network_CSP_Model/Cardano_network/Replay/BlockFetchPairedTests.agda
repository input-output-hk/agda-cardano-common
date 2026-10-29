{-# OPTIONS --safe #-}

-- Inhabited BlockFetch paired executions and communication-specific rejections.
module Cardano_network.Replay.BlockFetchPairedTests where

open import Data.List using (List; []; _∷_; take)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.Replay.Common using (client; server)
open import Cardano_network.Replay.BlockFetchClientSession
import Cardano_network.Replay.BlockFetchServerSession as S
import Cardano_network.Replay.BlockFetchPairedSession as P

-- Two ranges are outstanding before any response; one batch contains two blocks.
clientRows : List E
clientRows = (Send , request) ∷ (Send , request) ∷
  (Recv , startBatch) ∷ (Recv , block) ∷ (Recv , block) ∷ (Recv , batchDone) ∷
  (Recv , noBlocks) ∷ (Send , clientDone) ∷ []

-- The sequential server finishes the first range before consuming the second.
serverRows : List E
serverRows = (Recv , request) ∷ (Send , startBatch) ∷ (Send , block) ∷
  (Send , block) ∷ (Send , batchDone) ∷ (Recv , request) ∷
  (Send , noBlocks) ∷ (Recv , clientDone) ∷ []

-- Acceptance supplies an actual merge, both exact projections, and its run.
paired-run : P.Witness 2 (P.initial 2) clientRows serverRows
paired-run = toWitness {a? = P.witness? 2 (P.initial 2) clientRows serverRows} tt

-- Reordering the merge cannot repair the client's own capacity violation.
too-shallow : ¬ P.Compatible 1 (P.initial 1) clientRows serverRows
too-shallow = toWitnessFalse {a? = P.compatible? 1 (P.initial 1) clientRows serverRows} tt

-- Every accepted paired client projection belongs to the original client model.
projected-client : Spec.HasTrace 2 initial clientRows
projected-client = P.compatible-client 2 (P.fromWitness 2 paired-run)

-- The server projection belongs to the existing sequential replay model.
projected-server : S.HasTrace S.idle serverRows
projected-server = P.compatible-server 2 (P.fromWitness 2 paired-run)

-- The witness includes both client sends before server request consumption.
pipeline-first : take 2 (P.Witness.events paired-run) ≡
  ((client , Send , request) ∷ (client , Send , request) ∷ [])
pipeline-first = refl

-- A complete batch is locally legal at the client.
mismatch-client : Spec.HasTrace 2 initial
  ((Send , request) ∷ (Recv , startBatch) ∷ (Recv , batchDone) ∷ [])
mismatch-client = toWitness {a? = Spec.check 2
  ((Send , request) ∷ (Recv , startBatch) ∷ (Recv , batchDone) ∷ [])} tt

-- NoBlocks is also locally legal at the server for the same range request.
mismatch-server : S.HasTrace S.idle ((Recv , request) ∷ (Send , noBlocks) ∷ [])
mismatch-server = toWitness {a? = S.check ((Recv , request) ∷ (Send , noBlocks) ∷ [])} tt

-- Independent local legality does not imply communication compatibility.
pair-mismatch : ¬ P.Compatible 2 (P.initial 2)
  ((Send , request) ∷ (Recv , startBatch) ∷ (Recv , batchDone) ∷ [])
  ((Recv , request) ∷ (Send , noBlocks) ∷ [])
pair-mismatch = toWitnessFalse {a? = P.compatible? 2 (P.initial 2)
  ((Send , request) ∷ (Recv , startBatch) ∷ (Recv , batchDone) ∷ [])
  ((Recv , request) ∷ (Send , noBlocks) ∷ [])} tt

-- Different locally valid batch outcomes must retain their cross-peer FIFO order.
fifo-order : ¬ P.Compatible 2 (P.initial 2)
  ((Send , request) ∷ (Send , request) ∷ (Recv , noBlocks) ∷
   (Recv , startBatch) ∷ (Recv , batchDone) ∷ [])
  ((Recv , request) ∷ (Send , startBatch) ∷ (Send , batchDone) ∷
   (Recv , request) ∷ (Send , noBlocks) ∷ [])
fifo-order = toWitnessFalse {a? = P.compatible? 2 (P.initial 2)
  ((Send , request) ∷ (Send , request) ∷ (Recv , noBlocks) ∷
   (Recv , startBatch) ∷ (Recv , batchDone) ∷ [])
  ((Recv , request) ∷ (Send , startBatch) ∷ (Send , batchDone) ∷
   (Recv , request) ∷ (Send , noBlocks) ∷ [])} tt

-- Wire queues may hold requests not yet consumed at EOF.
inflight : P.Witness 2 (P.initial 2) ((Send , request) ∷ (Send , request) ∷ []) []
inflight = toWitness {a? = P.witness? 2 (P.initial 2)
  ((Send , request) ∷ (Send , request) ∷ []) []} tt

-- A fresh session cannot receive a request that the opposite capture never sent.
missing-send : ¬ P.Compatible 2 (P.initial 2) [] ((Recv , request) ∷ [])
missing-send = toWitnessFalse {a? = P.compatible? 2 (P.initial 2) [] ((Recv , request) ∷ [])} tt

-- Zero capacity disables range requests but still permits idle closure.
zero-close : P.Witness 0 (P.initial 0) ((Send , clientDone) ∷ []) ((Recv , clientDone) ∷ [])
zero-close = toWitness {a? = P.witness? 0 (P.initial 0)
  ((Send , clientDone) ∷ []) ((Recv , clientDone) ∷ [])} tt

-- Server consumption of a second request while busy remains forbidden.
server-sequential : ¬ P.Compatible 2 (P.initial 2)
  ((Send , request) ∷ (Send , request) ∷ [])
  ((Recv , request) ∷ (Recv , request) ∷ [])
server-sequential = toWitnessFalse {a? = P.compatible? 2 (P.initial 2)
  ((Send , request) ∷ (Send , request) ∷ [])
  ((Recv , request) ∷ (Recv , request) ∷ [])} tt
