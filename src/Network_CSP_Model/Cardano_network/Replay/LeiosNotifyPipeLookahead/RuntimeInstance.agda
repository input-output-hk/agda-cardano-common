{-# OPTIONS --guardedness #-}

-- Share one exact instance across certificate chunks instead of specializing it per file.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.RuntimeInstance where

open import Data.Unit using (⊤)
open import Data.Fin using () renaming (zero to fzero)
open import Cardano_network.Base using (hi)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams) public
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams public
import Cardano_network.LeiosNotifyPipeLookahead.Model
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel
import Cardano_network.LeiosNotifyPipeLookahead.NodeModel
import Cardano_network.LeiosNotifyPipeLookahead.CreditModel
import Cardano_network.LeiosNotifyPipeLookahead.NodeClientModel
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel
import Cardano_network.LeiosNotifyPipeLookahead.DriverExecution
import Cardano_network.Replay.LeiosNotifyPipeLookahead.RuntimeCheck
import Cardano_network.Replay.LeiosNotifyPipeLookahead.RuntimeCertificates
import Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverBridge
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ExportFixtures
import Cardano_network.LeiosNotifyPipeLookahead.DriverNetwork

-- Each public alias names the same specialization in every generated chunk.
module S = Cardano_network.LeiosNotifyPipeLookahead.Model Notification
-- The pinned node returns unit.
module C = Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification ⊤
-- Transport records retain their independent driver state.
module D = Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤
-- Admission uses the production depth.
module Server = Cardano_network.LeiosNotifyPipeLookahead.NodeModel Notification 1000
-- The shared queue retains exact payloads.
module Q = Cardano_network.LeiosNotifyPipeLookahead.CreditModel Notification 1000
-- Normal and abnormal client outcomes remain separate.
module Client = Cardano_network.LeiosNotifyPipeLookahead.NodeClientModel Notification ⊤
-- The combined source policy is unchanged.
module N = Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification
-- Supplied schedule checking uses the same independent node rules.
module Check = Cardano_network.Replay.LeiosNotifyPipeLookahead.RuntimeCheck Notification notificationEq
-- Concatenation and local-server projections keep their exact indices.
module Assembly = Cardano_network.Replay.LeiosNotifyPipeLookahead.RuntimeCertificates Notification
-- Transport selectors are data, not trusted transition proofs.
module Exec = Cardano_network.LeiosNotifyPipeLookahead.DriverExecution Notification ⊤ notificationEq
-- The native bridge is specialized only once.
module Bridge = Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverBridge exactParams
-- Native realization fixes the same logical endpoint coordinates as the existing fixtures.
module B = Bridge.At fzero fzero hi hi
-- The paired tree's alphabet and trace relation are shared too.
module Native = Cardano_network.LeiosNotifyPipeLookahead.DriverNetwork exactParams ⊤
-- Exact row rendering remains independent of the untrusted planner.
module Export = Cardano_network.Replay.LeiosNotifyPipeLookahead.ExportFixtures
