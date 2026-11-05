{-# OPTIONS --safe #-}

-- Exact endpoint necessary checks preserve real pending-Send prefixes and never replace paired replay.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.LocalPrecheckTests where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool Bool as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Bool Bool as Rows
import Cardano_network.LeiosNotifyPipeLookahead.DriverConservation Bool Bool as Conservation
import Cardano_network.Replay.LeiosNotifyPipeLookahead.LocalPrecheck Bool Bool as P
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverPrefixBoundsTests as Existing

-- This actual fresh prefix has both Receives recorded before either matching Send hook.
lead-client : List Rows.ClientRow
lead-client = Rows.receiveResponse (D.reply (S.normal false)) ∷ []

-- The server has recorded the Request but its reply Send hook is still pending too.
lead-server : List Rows.ServerRow
lead-server = Rows.receiveCommand D.request ∷ []

-- The original witnessed merge keeps the client and server local orders exactly.
lead-merge : Rows.Merge lead-client lead-server Existing.delayed-rows
lead-merge = Rows.server (Rows.client Rows.empty)

-- Sound projection accepts the real pending-hook race without an extra Return inhabitance premise.
lead-necessary : P.Pass S.nodeNext lead-client lead-server
lead-necessary = P.necessary lead-merge Existing.both-delayed-prefix

-- The executable local decisions also retain the valid receive-ahead EOF prefix.
lead-decided : P.Pass S.nodeNext lead-client lead-server
lead-decided = toWitness {a? = P.decide S.nodeNext _ _} tt

-- Generic client handlers accept Canceled even before shutdown; the server contract stays explicit.
generic-canceled : P.Pass S.genericNext
  (Rows.sendCommand D.request ∷ Rows.receiveResponse (D.reply S.canceled) ∷ [])
  (Rows.receiveCommand D.request ∷ Rows.sendResponse (D.reply S.canceled) ∷ [])
generic-canceled = toWitness {a? = P.decide S.genericNext _ _} tt

-- The node-next server contract excludes that entire pre-Quit local server cancellation language.
node-canceled-impossible : P.Pass S.nodeNext
  (Rows.sendCommand D.request ∷ Rows.receiveResponse (D.reply S.canceled) ∷ [])
  (Rows.receiveCommand D.request ∷ Rows.sendResponse (D.reply S.canceled) ∷ []) → ⊥
node-canceled-impossible = toWitnessFalse {a? = P.decide S.nodeNext _ _} tt

-- Source client control requires its Quit Send hook before the final Done Receive.
client-done-before-quit : P.Pass S.nodeNext
  (Rows.receiveResponse D.done ∷ Rows.sendCommand D.quit ∷ [])
  (Rows.receiveCommand D.quit ∷ Rows.sendResponse D.done ∷ []) → ⊥
client-done-before-quit = toWitnessFalse {a? = P.decide S.nodeNext _ _} tt

-- The server cannot send Done twice after its actual closed control transition.
duplicate-server-done : P.Pass S.nodeNext
  (Rows.sendCommand D.quit ∷ Rows.receiveResponse D.done ∷ [])
  (Rows.receiveCommand D.quit ∷ Rows.sendResponse D.done ∷ Rows.sendResponse D.done ∷ []) → ⊥
duplicate-server-done = toWitnessFalse {a? = P.decide S.nodeNext _ _} tt

-- Missing an owed reply before the server Done is rejected even with a locally valid client drain.
premature-server-done : P.Pass S.nodeNext
  (Rows.sendCommand D.request ∷ Rows.sendCommand D.quit ∷ Rows.receiveResponse (D.reply S.canceled) ∷ Rows.receiveResponse D.done ∷ [])
  (Rows.receiveCommand D.request ∷ Rows.receiveCommand D.quit ∷ Rows.sendResponse D.done ∷ []) → ⊥
premature-server-done = toWitnessFalse {a? = P.decide S.nodeNext _ _} tt

-- No client Request Send hook may appear after its own Quit hook.
client-request-after-quit : P.Pass S.genericNext
  (Rows.sendCommand D.quit ∷ Rows.sendCommand D.request ∷ []) [] → ⊥
client-request-after-quit = toWitnessFalse {a? = P.decide S.genericNext _ _} tt

-- The server reader likewise never records another Request after receiving Quit.
server-request-after-quit : P.Pass S.genericNext []
  (Rows.receiveCommand D.quit ∷ Rows.receiveCommand D.request ∷ []) → ⊥
server-request-after-quit = toWitnessFalse {a? = P.decide S.genericNext _ _} tt

-- These individually legal endpoint lists deliberately disagree on one exact normal payload.
wrong-client : List Rows.ClientRow
wrong-client = Rows.receiveResponse (D.reply (S.normal false)) ∷ []

-- The server's only recorded response is a different exact value.
wrong-server : List Rows.ServerRow
wrong-server = Rows.receiveCommand D.request ∷ Rows.sendResponse (D.reply (S.normal true)) ∷ []

-- Local success alone does not check packet agreement across the two endpoints.
local-success-insufficient : P.Pass S.nodeNext wrong-client wrong-server
local-success-insufficient = toWitness {a? = P.decide S.nodeNext _ _} tt

-- An unrestricted paired source witness still requires an actual merge and actual initial run.
PairedMismatch : S.Contract → Set
PairedMismatch contract = Σ[ events ∈ List D.Event ]
  (Rows.Merge wrong-client wrong-server events × Σ[ target ∈ D.State ] D.Run contract D.initial events target)

-- FIFO conservation refutes the mismatching pair in every possible endpoint merge.
no-paired-mismatch : ∀ contract → PairedMismatch contract → ⊥
no-paired-mismatch contract (_ , Rows.client (Rows.server (Rows.server Rows.empty)) , _ , source)
  with Conservation.to-client (Conservation.initial-conservation source)
... | ()
no-paired-mismatch contract (_ , Rows.server (Rows.client (Rows.server Rows.empty)) , _ , source)
  with Conservation.to-client (Conservation.initial-conservation source)
... | ()
no-paired-mismatch contract (_ , Rows.server (Rows.server (Rows.client Rows.empty)) , _ , source)
  with Conservation.to-client (Conservation.initial-conservation source)
... | ()

import Cardano_network.Replay.LeiosNotifyPipeLookahead.LocalPrecheck Bool ⊥ as EmptyReturn

-- Empty-prefix necessary checks remain executable with a genuinely empty Return carrier.
empty-return-prefix : EmptyReturn.Pass S.genericNext [] []
empty-return-prefix = toWitness {a? = EmptyReturn.decide S.genericNext [] []} tt
