{-# OPTIONS --guardedness #-}

-- Computed decisions and inhabited full-policy witnesses exercise the paired checker.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverDecideTests where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Notification ⊤ as Rows
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCore Notification as Core
import Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverDecide Notification notificationEq (votes []) as Checker
import Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverTests as Fixture

-- Empty files are accepted as the actual fresh source prefix.
empty-prefix : Checker.SourceTrace [] []
empty-prefix = toWitness {a? = Checker.decide [] []} tt

-- Forecast availability can justify an issued Request before any server log record.
request-server-eof : Checker.SourceTrace (Rows.sendCommand D.request ∷ []) []
request-server-eof = toWitness {a? = Checker.decide _ _} tt

-- A physical Request receive can precede its delayed client Send record.
receive-before-client-send : Checker.SourceTrace [] (Rows.receiveCommand D.request ∷ [])
receive-before-client-send = toWitness {a? = Checker.decide _ _} tt

-- Actual termination input enables the no-request Quit/Done exchange.
idle-shutdown : Checker.SourceTrace
  (Rows.sendCommand D.quit ∷ Rows.receiveResponse D.done ∷ [])
  (Rows.receiveCommand D.quit ∷ Rows.sendResponse D.done ∷ [])
idle-shutdown = toWitness {a? = Checker.decide _ _} tt

-- Done cannot be invented at the fresh server before any Quit receive.
unsolicited-done : Checker.SourceTrace [] (Rows.sendResponse D.done ∷ []) → ⊥
unsolicited-done = toWitnessFalse {a? = Checker.decide _ _} tt

-- Cancellation needs request credit even though it is a distinguished control reply.
unsolicited-canceled : Checker.SourceTrace [] (Rows.sendResponse (D.reply S.canceled) ∷ []) → ⊥
unsolicited-canceled = toWitnessFalse {a? = Checker.decide _ _} tt

-- The client observation order includes its delayed Request Send after receiving the normal reply.
delayed-client : List Rows.ClientRow
delayed-client = Rows.receiveResponse (D.reply (S.normal Fixture.sample)) ∷ Rows.sendCommand D.request ∷ []

-- The server retains its own Receive-before-Send order independently.
delayed-server : List Rows.ServerRow
delayed-server = Rows.receiveCommand D.request ∷ Rows.sendResponse (D.reply (S.normal Fixture.sample)) ∷ []

-- An existing actual full-policy run supplies the independent source proposition.
delayed-source : Checker.SourceTrace delayed-client delayed-server
delayed-source = _ , Rows.server (Rows.client (Rows.client (Rows.server Rows.empty))) ,
  Fixture.delayedState , Fixture.delayed-actions , Fixture.delayed-source , refl

module Delayed = Checker.For delayed-client delayed-server

-- Whole-input adequacy carries a real queued notification into the finite complete search language.
delayed-replay : Delayed.Pair.PairTrace Core.initial delayed-client delayed-server
delayed-replay = Delayed.source→replay delayed-source

-- Reconstruction retains a full original node run rather than only a generic driver witness.
delayed-roundtrip : Checker.SourceTrace delayed-client delayed-server
delayed-roundtrip = Delayed.replay→source delayed-replay

-- Graceful cancellation retains all local command and reply observations, including Done.
cancel-client : List Rows.ClientRow
cancel-client = Rows.sendCommand D.request ∷ Rows.sendCommand D.quit ∷
  Rows.receiveResponse (D.reply S.canceled) ∷ Rows.receiveResponse D.done ∷ []

-- The server's actual cancellation and its Done Send both remain present.
cancel-server : List Rows.ServerRow
cancel-server = Rows.receiveCommand D.request ∷ Rows.receiveCommand D.quit ∷
  Rows.sendResponse (D.reply S.canceled) ∷ Rows.sendResponse D.done ∷ []

-- This is the source run that publishes stop before handling the cancellation.
cancel-source : Checker.SourceTrace cancel-client cancel-server
cancel-source = _ , Rows.client (Rows.server (Rows.client (Rows.server
  (Rows.server (Rows.client (Rows.client (Rows.server Rows.empty))))))) ,
  Fixture.shutdownState , Fixture.shutdown-actions , Fixture.shutdown-source , refl

module Canceled = Checker.For cancel-client cancel-server

-- The finite menu restriction preserves the graceful Canceled control path.
cancel-replay : Canceled.Pair.PairTrace Core.initial cancel-client cancel-server
cancel-replay = Canceled.source→replay cancel-source

-- A roundtrip gives a fresh full-policy witness, with no assumption about actual external input truth.
cancel-roundtrip : Checker.SourceTrace cancel-client cancel-server
cancel-roundtrip = Canceled.replay→source cancel-replay
