{-# OPTIONS --guardedness #-}

-- One-way native realization of the restricted production node policy.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverBridge (p : Params) where

open import Data.List using (map)
open import Data.Unit using (⊤)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Net p using (Link)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications p using (Notification)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverProperties Notification as Proof
import Cardano_network.LeiosNotifyPipeLookahead.DriverNetwork p ⊤ as Native
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverNetworkBridge p ⊤ as Bridge
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverEndpointBridge p ⊤ as Endpoints

-- Endpoint coordinates stay fixed throughout the policy witness and its wire realization.
module At (cl sl : Link) (cd sd : Dir) where
  module N = Native.At S.nodeNext cl sl cd sd
  module B = Bridge.At S.nodeNext cl sl cd sd
  module E = Endpoints.At S.nodeNext cl sl cd sd

  -- Every restricted node run has a native generic product trace with identical wire rows.
  realize : ∀ {s actions t} → Node.Run s actions t →
    N.tree (Node.driverState s) Native.Traces.⟹∖√⟨ map N.encode (Node.wireRows actions) ⟩
      N.tree (Node.driverState t)
  realize run = B.realize (Proof.driver run)

  -- The same witness gives both native endpoint executions with matching local record order.
  endpoints : ∀ {s actions t} → Node.Run s actions t →
    E.Endpoints (Node.driverState s) (Node.wireRows actions) (Node.driverState t)
  endpoints run = E.realize-endpoints (Proof.driver run)
