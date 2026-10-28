{-# OPTIONS --safe #-}

-- Inhabited exact-message pairs and a mismatch invisible to independent replay.
module Cardano_network.Replay.LeiosFetchPairedTests where
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Cardano_network.Replay.LeiosFetchSession
import Cardano_network.Replay.LeiosFetchPairedSession as P
open import Cardano_network.Replay.Common using (client; server)
import Cardano_network.Replay.LeiosFetchDecide as Decide
module C = Decide.Cert 1
module L = P.Local 1

-- A complete request/reply prefix at the client.
cs : List E
cs = (Send , MsgLeiosBlockRequest 10 4) ∷ (Recv , MsgLeiosBlock 10 20) ∷ []

-- Matching server events retain exactly the same response payload fields.
ss : List E
ss = (Recv , MsgLeiosBlockRequest 10 4) ∷ (Send , MsgLeiosBlock 10 20) ∷ []

-- A size mismatch changes no local agency or request-correlation condition.
mismatched : List E
mismatched = (Recv , MsgLeiosBlockRequest 10 4) ∷ (Send , MsgLeiosBlock 10 21) ∷ []

-- Acceptance contains an actual paired run and both exact input projections.
accepted : P.Witness 1 (P.initial 1) cs ss
accepted = toWitness {a? = P.witness? 1 (P.initial 1) cs ss} tt

-- Both the client and mismatched server are individually legal.
local-client : L.HasTrace client₀ cs
local-client = toWitness {a? = C.hasTrace? C.client-cert cs} tt

-- The response size is deliberately unconstrained in local replay.
local-server : L.HasTrace server₀ mismatched
local-server = toWitness {a? = C.hasTrace? C.server-cert mismatched} tt

-- Exact FIFO matching detects a mismatch that independent checks cannot.
rejected : ¬ P.Witness 1 (P.initial 1) cs mismatched
rejected = toWitnessFalse {a? = P.witness? 1 (P.initial 1) cs mismatched} tt

-- A receive without its sending endpoint's event cannot start a fresh pair.
missing-send : ¬ P.Compatible 1 (P.initial 1) [] ss
missing-send = toWitnessFalse {a? = P.compatible? 1 (P.initial 1) [] ss} tt

-- The accepted witness projects through the protocol-specific local proof.
projected-client : L.HasTrace client₀ cs
projected-client = P.compatible-client 1 (P.fromWitness 1 accepted)

-- Client pipelining does not license the responder to receive a second request.
server-sequential : ¬ P.Compatible 2 (P.initial 2)
  ((Send , MsgLeiosBlockRequest 1 3) ∷ (Send , MsgLeiosBlockRequest 2 4) ∷ [])
  ((Recv , MsgLeiosBlockRequest 1 3) ∷ (Recv , MsgLeiosBlockRequest 2 4) ∷ [])
server-sequential = toWitnessFalse {a? = P.compatible? 2 (P.initial 2)
  ((Send , MsgLeiosBlockRequest 1 3) ∷ (Send , MsgLeiosBlockRequest 2 4) ∷ [])
  ((Recv , MsgLeiosBlockRequest 1 3) ∷ (Recv , MsgLeiosBlockRequest 2 4) ∷ [])} tt

-- Transaction reply fields must match their send, but need not echo the request.
non-echo : P.Witness 1 (P.initial 1)
  ((Send , MsgLeiosBlockTxsRequest 1 3 2 []) ∷ (Recv , MsgLeiosBlockTxs 1 3 9 40 ((0 , 15) ∷ [])) ∷ [])
  ((Recv , MsgLeiosBlockTxsRequest 1 3 2 []) ∷ (Send , MsgLeiosBlockTxs 1 3 9 40 ((0 , 15) ∷ [])) ∷ [])
non-echo = toWitness {a? = P.witness? 1 (P.initial 1)
  ((Send , MsgLeiosBlockTxsRequest 1 3 2 []) ∷ (Recv , MsgLeiosBlockTxs 1 3 9 40 ((0 , 15) ∷ [])) ∷ [])
  ((Recv , MsgLeiosBlockTxsRequest 1 3 2 []) ∷ (Send , MsgLeiosBlockTxs 1 3 9 40 ((0 , 15) ∷ [])) ∷ [])} tt
