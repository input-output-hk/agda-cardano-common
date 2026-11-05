{-# OPTIONS --safe #-}

-- Computed source decisions retain complete closed histories and exact payloads.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverSearchTests where

open import Data.Bool using (Bool; false; true)
import Data.Bool.Properties as Bool
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Bool ⊤ as Rows
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverDecide Bool Bool._≟_ false as Check

-- This endpoint records its actual Request Send before the ordinary reply.
normal-client : Bool → List Rows.ClientRow
normal-client value = Rows.sendCommand D.request ∷
  Rows.receiveResponse (D.reply (S.normal value)) ∷
  Rows.sendCommand D.quit ∷ Rows.receiveResponse D.done ∷ []

-- The corresponding server records Request, the exact reply, Quit and Done.
normal-server : Bool → List Rows.ServerRow
normal-server value = Rows.receiveCommand D.request ∷
  Rows.sendResponse (D.reply (S.normal value)) ∷
  Rows.receiveCommand D.quit ∷ Rows.sendResponse D.done ∷ []

-- The normal closed pair keeps Quit/Done and uses a value different from the representative.
normal-closed : Check.SourceTrace S.nodeNext (normal-client true) (normal-server true)
normal-closed = toWitness {a? = Check.decide S.nodeNext _ _} tt

-- The same source language endpoint remains available under the generic callback contract.
normal-generic : Check.SourceTrace S.genericNext (normal-client true) (normal-server true)
normal-generic = toWitness {a? = Check.decide S.genericNext _ _} tt

-- Busy shutdown sends Quit before receiving the owed cancellation and final Done.
cancel-client : List Rows.ClientRow
cancel-client = Rows.sendCommand D.request ∷ Rows.sendCommand D.quit ∷
  Rows.receiveResponse (D.reply S.canceled) ∷ Rows.receiveResponse D.done ∷ []

-- The server publishes shutdown before discharging the pending response.
cancel-server : List Rows.ServerRow
cancel-server = Rows.receiveCommand D.request ∷ Rows.receiveCommand D.quit ∷
  Rows.sendResponse (D.reply S.canceled) ∷ Rows.sendResponse D.done ∷ []

-- Cancellation after Quit is legal under the normal-only node callback contract.
cancel-closed : Check.SourceTrace S.nodeNext cancel-client cancel-server
cancel-closed = toWitness {a? = Check.decide S.nodeNext _ _} tt

-- A client response may precede its delayed Request Send without changing local order.
delayed-client : List Rows.ClientRow
delayed-client = Rows.receiveResponse (D.reply (S.normal true)) ∷
  Rows.sendCommand D.request ∷ Rows.sendCommand D.quit ∷ Rows.receiveResponse D.done ∷ []

-- Ordering still admits the established delayed-Send family through graceful shutdown.
delayed-closed : Check.SourceTrace S.nodeNext delayed-client (normal-server true)
delayed-closed = toWitness {a? = Check.decide S.nodeNext _ _} tt

-- A payload disagreement is rejected rather than repaired by the ordering heuristic.
wrong-client : List Rows.ClientRow
wrong-client = Rows.receiveResponse (D.reply (S.normal true)) ∷ []

-- The server's only logged ordinary notification is a different concrete value.
wrong-server : List Rows.ServerRow
wrong-server = Rows.receiveCommand D.request ∷
  Rows.sendResponse (D.reply (S.normal false)) ∷ []

-- Rejection is the original unrestricted source proposition, not absence from a heuristic path.
wrong-payload : Check.SourceTrace S.nodeNext wrong-client wrong-server → ⊥
wrong-payload = toWitnessFalse {a? = Check.decide S.nodeNext _ _} tt
