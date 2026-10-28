{-# OPTIONS --safe #-}

-- Inhabited exact-message pairs and a mismatch invisible to independent replay.
module Cardano_network.Replay.LeiosNotifyPairedTests where
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Cardano_network.Replay.LeiosNotifySession
import Cardano_network.Replay.LeiosNotifyPairedSession as P
open import Cardano_network.Replay.Common using (client; server)
import Cardano_network.Replay.LeiosNotifyPipeline as N

-- A complete request/reply prefix at the client.
cs : List E
cs = (Send , RequestNext) ∷ (Recv , BlockOffer 10 4 20) ∷ []

-- Matching server events retain exactly the same response payload fields.
ss : List E
ss = (Recv , RequestNext) ∷ (Send , BlockOffer 10 4 20) ∷ []

-- A size mismatch changes no local agency or request-correlation condition.
mismatched : List E
mismatched = (Recv , RequestNext) ∷ (Send , BlockOffer 10 4 21) ∷ []

-- Acceptance contains an actual paired run and both exact input projections.
accepted : P.Witness 1 (P.initial 1) cs ss
accepted = toWitness {a? = P.witness? 1 (P.initial 1) cs ss} tt

-- Both the client and mismatched server are individually legal.
local-client : Spec.HasTrace client idle cs
local-client = toWitness {a? = Spec.check client cs} tt

-- The response size is deliberately unconstrained in local replay.
local-server : Spec.HasTrace server idle mismatched
local-server = toWitness {a? = Spec.check server mismatched} tt

-- Exact FIFO matching detects a mismatch that independent checks cannot.
rejected : ¬ P.Witness 1 (P.initial 1) cs mismatched
rejected = toWitnessFalse {a? = P.witness? 1 (P.initial 1) cs mismatched} tt

-- A receive without its sending endpoint's event cannot start a fresh pair.
missing-send : ¬ P.Compatible 1 (P.initial 1) [] ss
missing-send = toWitnessFalse {a? = P.compatible? 1 (P.initial 1) [] ss} tt

-- The accepted witness projects through the protocol-specific local proof.
projected-client : N.Spec.HasTrace 1 client N.idle cs
projected-client = P.compatible-client 1 (P.fromWitness 1 accepted)

-- Two request credits can be outstanding at each Notify endpoint.
pipelined : P.Witness 2 (P.initial 2)
  ((Send , RequestNext) ∷ (Send , RequestNext) ∷ (Recv , Votes []) ∷ (Recv , Votes []) ∷ [])
  ((Recv , RequestNext) ∷ (Recv , RequestNext) ∷ (Send , Votes []) ∷ (Send , Votes []) ∷ [])
pipelined = toWitness {a? = P.witness? 2 (P.initial 2)
  ((Send , RequestNext) ∷ (Send , RequestNext) ∷ (Recv , Votes []) ∷ (Recv , Votes []) ∷ [])
  ((Recv , RequestNext) ∷ (Recv , RequestNext) ∷ (Send , Votes []) ∷ (Send , Votes []) ∷ [])} tt

-- FIFO order distinguishes notifications even when their kinds are identical.
reordered : ¬ P.Compatible 2 (P.initial 2)
  ((Send , RequestNext) ∷ (Send , RequestNext) ∷ (Recv , Votes []) ∷ (Recv , Votes ((1 , 2) ∷ [])) ∷ [])
  ((Recv , RequestNext) ∷ (Recv , RequestNext) ∷ (Send , Votes ((1 , 2) ∷ [])) ∷ (Send , Votes []) ∷ [])
reordered = toWitnessFalse {a? = P.compatible? 2 (P.initial 2)
  ((Send , RequestNext) ∷ (Send , RequestNext) ∷ (Recv , Votes []) ∷ (Recv , Votes ((1 , 2) ∷ [])) ∷ [])
  ((Recv , RequestNext) ∷ (Recv , RequestNext) ∷ (Send , Votes ((1 , 2) ∷ [])) ∷ (Send , Votes []) ∷ [])} tt
