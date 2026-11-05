{-# OPTIONS --guardedness #-}

-- Canonical summary-carrier native witnesses and refutations at every chosen fresh endpoint.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ServerAdapterNativeTests where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.Net exactParams using (Link)
import Cardano_network.Replay.LeiosNotifySession as Log
import Cardano_network.LeiosNotifyPipe exactParams as Payloads
import Cardano_network.LeiosNotifyPipeLookahead.Model Payloads.Notification as S
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ServerAdapter as A
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ServerAdapterNative as Bridge

-- A selected endpoint changes native channel identities without altering normalized agency.
module For (l : Link) (d : Dir) where
  module Node = Bridge.For S.nodeNext l d

  -- Exact optional metadata and ordered duplicate vote pairs have a native source realization.
  exact-payloads : Node.Accepted Log.server (A.present
    ((Log.Recv , Log.RequestNext) ∷ (Log.Recv , Log.RequestNext) ∷ (Log.Recv , Log.Quit) ∷
     (Log.Send , Log.BlockAnnouncement (just (17 , 23 , 31))) ∷
     (Log.Send , Log.Votes ((67 , 71) ∷ (73 , 79) ∷ (67 , 71) ∷ [])) ∷
     (Log.Send , Log.Done) ∷ []))
  exact-payloads = toWitness {a? = Node.decide Log.server _} tt

  -- Wrong native response agency cannot be hidden away by the normalization interface.
  wrong-agency : Node.Accepted Log.server (A.present
    ((Log.Recv , Log.RequestNext) ∷ (Log.Recv , Log.Canceled) ∷ [])) → ⊥
  wrong-agency = toWitnessFalse {a? = Node.decide Log.server _} tt

  -- Every native realization of pre-Quit node cancellation is excluded, not merely one schedule.
  early-node-cancel : Node.Accepted Log.server (A.present
    ((Log.Recv , Log.RequestNext) ∷ (Log.Send , Log.Canceled) ∷ [])) → ⊥
  early-node-cancel = toWitnessFalse {a? = Node.decide Log.server _} tt
