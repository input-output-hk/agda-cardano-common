{-# OPTIONS --guardedness #-}

-- Joint strict-submitter/requester witnesses, including pipelining and blocking.
module Cardano_network.Replay.TxSubmission2PairedBridgeTests where

open import Data.Fin using (zero)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Data.Maybe using (just; nothing)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.Base using (lo; hi; FromResponder; Blocking; NonBlocking)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Data replayParams
open import Cardano_network.Params using (Params)
open Params replayParams using (time₀; length₀)
open import Cardano_network.TxSubmission replayParams using (TSEv; sendTS; receiveTS)
open import Cardano_network.Replay.TxSubmission2Session
import Cardano_network.Replay.TxSubmission2PairedSession as R
import Cardano_network.Replay.TxSubmission2PairedTests as T
import Cardano_network.Replay.TxSubmission2PairedBridge replayParams as B
import Cardano_network.Replay.TxSubmission2PairedModel replayParams as Model
import Cardano_network.Replay.TxSubmission2PairedPackets replayParams as Packets
open import Process_Trees using (ExtI)
import Semantics.LTS {E = TSEv} {I = ExtI TSEv} as Local

-- The sequential client and pipelined server jointly realise both input logs.
paired-system : B.Inputs 2 zero zero lo hi tt T.clientRows T.serverRows
paired-system = B.checker-sound 2 zero zero lo hi tt T.paired-run

-- This reverse endpoint takes no block or transaction-ID witness argument.
unconditional-certificate : R.Witness 2 (R.initial 2) T.clientRows T.serverRows
unconditional-certificate with paired-system
... | t , tree , es , run , obs , co , so = B.model-certificate 2 zero zero lo hi run obs co so

-- The composed execution returns a certificate for exactly those endpoint rows.
roundtrip : R.Witness 2 (R.initial 2) T.clientRows T.serverRows
roundtrip = B.checker-complete 2 zero zero lo hi tt paired-system

-- The server-to-client FIFO can retain a request at the end of the capture.
inflight-system : B.Inputs 2 zero zero hi lo tt ((Send , init) ∷ [])
  ((Recv , init) ∷ (Send , requestTxs) ∷ [])
inflight-system = B.checker-sound 2 zero zero hi lo tt T.inflight

-- Blocking nonempty replies and Done are inhabited even at asynchronous depth zero.
zero-system : B.Inputs 0 zero zero lo hi tt
  ((Send , init) ∷ (Recv , requestBlocking) ∷ (Send , replyIdsNonEmpty) ∷
   (Recv , requestBlocking) ∷ (Send , doneK) ∷ [])
  ((Recv , init) ∷ (Send , requestBlocking) ∷ (Recv , replyIdsNonEmpty) ∷
   (Send , requestBlocking) ∷ (Recv , doneK) ∷ [])
zero-system = B.checker-sound 0 zero zero lo hi tt T.zero-blocking

-- The submitter's nonempty send cannot match the requester's empty receive.
mismatch-impossible : ¬ B.Inputs 2 zero zero lo hi tt
  ((Send , init) ∷ (Recv , requestNonBlocking) ∷ (Send , replyIdsNonEmpty) ∷ [])
  ((Recv , init) ∷ (Send , requestNonBlocking) ∷ (Recv , replyIdsEmpty) ∷ [])
mismatch-impossible input = T.reply-mismatch (B.inputs-sound 2 zero zero lo hi tt input)

-- No joint schedule can repair an overfull requester-local pipeline.
shallow-impossible : ¬ B.Inputs 1 zero zero lo hi tt T.clientRows T.serverRows
shallow-impossible input = T.too-shallow (B.inputs-sound 1 zero zero lo hi tt input)

-- Mixed request families cannot be reordered between the communicating peers.
fifo-impossible : ¬ B.Inputs 2 zero zero lo hi tt
  ((Send , init) ∷ (Recv , requestTxs) ∷ (Send , replyTxs) ∷
   (Recv , requestNonBlocking) ∷ (Send , replyIdsEmpty) ∷ [])
  ((Recv , init) ∷ (Send , requestNonBlocking) ∷ (Send , requestTxs) ∷
   (Recv , replyIdsEmpty) ∷ (Recv , replyTxs) ∷ [])
fifo-impossible input = T.fifo-order (B.inputs-sound 2 zero zero lo hi tt input)

-- A fresh requester cannot receive Init without the submitter's matching send.
missing-init-impossible : ¬ B.Inputs 2 zero zero lo hi tt [] ((Recv , init) ∷ [])
missing-init-impossible input = T.missing-init-send (B.inputs-sound 2 zero zero lo hi tt input)

-- Request parameters are retained by the native payload medium.
request-one : Payload
request-one = time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking 0 1)

-- Changing the requested count leaves its logged control shape unchanged.
request-two : Payload
request-two = time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking 0 2)

-- Replay observes nonblocking style but erases the exact requested count.
same-control : Packets.payloadKind request-one ≡ Packets.payloadKind request-two
same-control = refl

-- Requester/server sends append to the server-to-client full-payload FIFO.
full-enqueue : Model.serverGate (Local.evLabel _ (sendTS zero hi) request-one) Model.empty ≡
  just (Model.queues [] (request-one ∷ []))
full-enqueue = refl

-- The sequential client's receive cannot substitute a different request count.
wrong-payload : Model.clientGate (Local.evLabel _ (receiveTS zero lo) request-two)
  (Model.queues [] (request-one ∷ [])) ≡ nothing
wrong-payload = refl
