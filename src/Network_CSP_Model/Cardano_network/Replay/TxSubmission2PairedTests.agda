{-# OPTIONS --safe #-}

-- Paired TxSubmission2 witnesses retain reversed agency and strict control shapes.
module Cardano_network.Replay.TxSubmission2PairedTests where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Cardano_network.Replay.TxSubmission2Session
import Cardano_network.Replay.TxSubmission2PairedSession as P

-- The submitter handles the two request families sequentially before shutdown.
clientRows : List E
clientRows = (Send , init) ∷ (Recv , requestNonBlocking) ∷ (Send , replyIdsEmpty) ∷
  (Recv , requestTxs) ∷ (Send , replyTxs) ∷ (Recv , requestBlocking) ∷ (Send , doneK) ∷ []

-- The requester pipelines nonblocking work, then drains before blocking Done.
serverRows : List E
serverRows = (Recv , init) ∷ (Send , requestNonBlocking) ∷ (Send , requestTxs) ∷
  (Recv , replyIdsEmpty) ∷ (Recv , replyTxs) ∷ (Send , requestBlocking) ∷ (Recv , doneK) ∷ []

-- A single order-preserving merge realizes both distinct endpoint schedules.
paired-run : P.Witness 2 (P.initial 2) clientRows serverRows
paired-run = toWitness {a? = P.witness? 2 (P.initial 2) clientRows serverRows} tt

-- The capacity belongs to the requester/server, not the submitter/client.
too-shallow : ¬ P.Compatible 1 (P.initial 1) clientRows serverRows
too-shallow = toWitnessFalse {a? = P.compatible? 1 (P.initial 1) clientRows serverRows} tt

-- Accepted input projects to the original sequential submitter language.
projected-client : Spec.HasTrace 2 client initial clientRows
projected-client = P.compatible-client 2 (P.fromWitness 2 paired-run)

-- Accepted input also projects to the original bounded requester language.
projected-server : Spec.HasTrace 2 server initial serverRows
projected-server = P.compatible-server 2 (P.fromWitness 2 paired-run)

-- This nonempty reply is legal locally at the submitter.
mismatch-client : Spec.HasTrace 2 client initial
  ((Send , init) ∷ (Recv , requestNonBlocking) ∷ (Send , replyIdsNonEmpty) ∷ [])
mismatch-client = toWitness {a? = Spec.check 2 client
  ((Send , init) ∷ (Recv , requestNonBlocking) ∷ (Send , replyIdsNonEmpty) ∷ [])} tt

-- An empty nonblocking ID reply is independently legal at the requester.
mismatch-server : Spec.HasTrace 2 server initial
  ((Recv , init) ∷ (Send , requestNonBlocking) ∷ (Recv , replyIdsEmpty) ∷ [])
mismatch-server = toWitness {a? = Spec.check 2 server
  ((Recv , init) ∷ (Send , requestNonBlocking) ∷ (Recv , replyIdsEmpty) ∷ [])} tt

-- Cross-endpoint matching distinguishes empty from nonempty ID replies.
reply-mismatch : ¬ P.Compatible 2 (P.initial 2)
  ((Send , init) ∷ (Recv , requestNonBlocking) ∷ (Send , replyIdsNonEmpty) ∷ [])
  ((Recv , init) ∷ (Send , requestNonBlocking) ∷ (Recv , replyIdsEmpty) ∷ [])
reply-mismatch = toWitnessFalse {a? = P.compatible? 2 (P.initial 2)
  ((Send , init) ∷ (Recv , requestNonBlocking) ∷ (Send , replyIdsNonEmpty) ∷ [])
  ((Recv , init) ∷ (Send , requestNonBlocking) ∷ (Recv , replyIdsEmpty) ∷ [])} tt

-- A blocking receive cannot stand in for an opposite nonblocking request send.
blocking-mismatch : ¬ P.Compatible 2 (P.initial 2)
  ((Send , init) ∷ (Recv , requestBlocking) ∷ (Send , replyIdsNonEmpty) ∷ [])
  ((Recv , init) ∷ (Send , requestNonBlocking) ∷ (Recv , replyIdsNonEmpty) ∷ [])
blocking-mismatch = toWitnessFalse {a? = P.compatible? 2 (P.initial 2)
  ((Send , init) ∷ (Recv , requestBlocking) ∷ (Send , replyIdsNonEmpty) ∷ [])
  ((Recv , init) ∷ (Send , requestNonBlocking) ∷ (Recv , replyIdsNonEmpty) ∷ [])} tt

-- Different request families retain their FIFO order even with legal local runs.
fifo-order : ¬ P.Compatible 2 (P.initial 2)
  ((Send , init) ∷ (Recv , requestTxs) ∷ (Send , replyTxs) ∷
   (Recv , requestNonBlocking) ∷ (Send , replyIdsEmpty) ∷ [])
  ((Recv , init) ∷ (Send , requestNonBlocking) ∷ (Send , requestTxs) ∷
   (Recv , replyIdsEmpty) ∷ (Recv , replyTxs) ∷ [])
fifo-order = toWitnessFalse {a? = P.compatible? 2 (P.initial 2)
  ((Send , init) ∷ (Recv , requestTxs) ∷ (Send , replyTxs) ∷
   (Recv , requestNonBlocking) ∷ (Send , replyIdsEmpty) ∷ [])
  ((Recv , init) ∷ (Send , requestNonBlocking) ∷ (Send , requestTxs) ∷
   (Recv , replyIdsEmpty) ∷ (Recv , replyTxs) ∷ [])} tt

-- A request can remain in the server-to-client transport queue at EOF.
inflight : P.Witness 2 (P.initial 2) ((Send , init) ∷ [])
  ((Recv , init) ∷ (Send , requestTxs) ∷ [])
inflight = toWitness {a? = P.witness? 2 (P.initial 2) ((Send , init) ∷ [])
  ((Recv , init) ∷ (Send , requestTxs) ∷ [])} tt

-- Receiving Init still requires its actual opposite send at a fresh boundary.
missing-init-send : ¬ P.Compatible 2 (P.initial 2) [] ((Recv , init) ∷ [])
missing-init-send = toWitnessFalse {a? = P.compatible? 2 (P.initial 2) [] ((Recv , init) ∷ [])} tt

-- Zero asynchronous capacity still allows blocking work and submitter Done.
zero-blocking : P.Witness 0 (P.initial 0)
  ((Send , init) ∷ (Recv , requestBlocking) ∷ (Send , replyIdsNonEmpty) ∷
   (Recv , requestBlocking) ∷ (Send , doneK) ∷ [])
  ((Recv , init) ∷ (Send , requestBlocking) ∷ (Recv , replyIdsNonEmpty) ∷
   (Send , requestBlocking) ∷ (Recv , doneK) ∷ [])
zero-blocking = toWitness {a? = P.witness? 0 (P.initial 0)
  ((Send , init) ∷ (Recv , requestBlocking) ∷ (Send , replyIdsNonEmpty) ∷
   (Recv , requestBlocking) ∷ (Send , doneK) ∷ [])
  ((Recv , init) ∷ (Send , requestBlocking) ∷ (Recv , replyIdsNonEmpty) ∷
   (Send , requestBlocking) ∷ (Recv , doneK) ∷ [])} tt

-- A large requester bound cannot make submitter processing itself pipelined.
client-sequential : ¬ P.Compatible 100 (P.initial 100)
  ((Send , init) ∷ (Recv , requestNonBlocking) ∷ (Recv , requestTxs) ∷ [])
  ((Recv , init) ∷ (Send , requestNonBlocking) ∷ (Send , requestTxs) ∷ [])
client-sequential = toWitnessFalse {a? = P.compatible? 100 (P.initial 100)
  ((Send , init) ∷ (Recv , requestNonBlocking) ∷ (Recv , requestTxs) ∷ [])
  ((Recv , init) ∷ (Send , requestNonBlocking) ∷ (Send , requestTxs) ∷ [])} tt
