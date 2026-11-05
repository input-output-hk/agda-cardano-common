{-# OPTIONS --safe #-}

-- Small computed decisions and larger explicit witnesses exercise the paired source checker.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverDecideTests where

open import Data.Bool using (Bool; false; true)
import Data.Bool.Properties as Bool
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Bool ⊤ as Rows
import Cardano_network.LeiosNotifyPipeLookahead.DriverBasis Bool ⊤ (false ∷ []) as B
import Cardano_network.LeiosNotifyPipeLookahead.DriverConservation Bool ⊤ as Conservation
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverDecide Bool Bool._≟_ false as Checker
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverBasisExecutionTests as Fixture

-- Empty files form an actual fresh zero-operation prefix.
empty-prefix : Checker.SourceTrace S.genericNext [] []
empty-prefix = toWitness {a? = Checker.decide S.genericNext [] []} tt

-- Client Send-Request may be the last record while the entire server file is still empty.
request-server-eof : Checker.SourceTrace S.genericNext (Rows.sendCommand D.request ∷ []) []
request-server-eof = toWitness {a? = Checker.decide S.genericNext _ _} tt

-- The opposite EOF race is legal: server Receive-Request may precede its client Send record.
receive-before-client-send : Checker.SourceTrace S.genericNext [] (Rows.receiveCommand D.request ∷ [])
receive-before-client-send = toWitness {a? = Checker.decide S.genericNext _ _} tt

-- A reply cannot be produced before any server Request receive record has advanced its source.
unmatched-reply : Checker.SourceTrace S.genericNext
  (Rows.receiveResponse (D.reply (S.normal false)) ∷ []) [] → ⊥
unmatched-reply = toWitnessFalse {a? = Checker.decide S.genericNext _ _} tt

-- Generic cancellation cannot invent an unsolicited server response either.
extra-canceled : Checker.SourceTrace S.genericNext []
  (Rows.sendResponse (D.reply S.canceled) ∷ []) → ⊥
extra-canceled = toWitnessFalse {a? = Checker.decide S.genericNext _ _} tt

-- Done cannot arrive before the client has sent Quit and entered its actual Done receiver.
initial-client-done : Checker.SourceTrace S.genericNext (Rows.receiveResponse D.done ∷ []) [] → ⊥
initial-client-done = toWitnessFalse {a? = Checker.decide S.genericNext _ _} tt

-- The server cannot send Done before recording the command that starts graceful shutdown.
initial-server-done : Checker.SourceTrace S.genericNext [] (Rows.sendResponse D.done ∷ []) → ⊥
initial-server-done = toWitnessFalse {a? = Checker.decide S.genericNext _ _} tt

-- The zero-request graceful path needs no dummy Quit receiver and is decided constructively.
idle-shutdown : Checker.SourceTrace S.nodeNext
  (Rows.sendCommand D.quit ∷ Rows.receiveResponse D.done ∷ [])
  (Rows.receiveCommand D.quit ∷ Rows.sendResponse D.done ∷ [])
idle-shutdown = toWitness {a? = Checker.decide S.nodeNext _ _} tt

-- Exact payload mismatch uses only three input rows, with the client Request Send still pending.
wrong-client : List Rows.ClientRow
wrong-client = Rows.receiveResponse (D.reply (S.normal true)) ∷ []

-- The sole server reply has a different concrete notification payload.
wrong-server : List Rows.ServerRow
wrong-server = Rows.receiveCommand D.request ∷ Rows.sendResponse (D.reply (S.normal false)) ∷ []

-- Every order-preserving merge contradicts exact packet conservation, without large search reduction.
wrong-payload : Checker.SourceTrace S.genericNext wrong-client wrong-server → ⊥
wrong-payload (_ , Rows.client (Rows.server (Rows.server Rows.empty)) , _ , run)
  with Conservation.to-client (Conservation.initial-conservation run)
... | ()
wrong-payload (_ , Rows.server (Rows.client (Rows.server Rows.empty)) , _ , run)
  with Conservation.to-client (Conservation.initial-conservation run)
... | ()
wrong-payload (_ , Rows.server (Rows.server (Rows.client Rows.empty)) , _ , run)
  with Conservation.to-client (Conservation.initial-conservation run)
... | ()

-- The larger delayed-Send schedule is exercised through an existing actual fresh source witness.
delayed-client : List Rows.ClientRow
delayed-client = Rows.receiveResponse (D.reply (S.normal false)) ∷ []

-- The server input ends after Request Receive, before its committed reply Send hook is emitted.
delayed-server : List Rows.ServerRow
delayed-server = Rows.receiveCommand D.request ∷ []

-- This merge preserves both local file orders while placing both Receive records first.
delayed-merge : Rows.Merge delayed-client delayed-server
  (D.serverRecv D.request ∷ D.clientRecv (D.reply (S.normal false)) ∷ [])
delayed-merge = Rows.server (Rows.client Rows.empty)

-- Membership restrictions erase to the same raw source run with both pending Send slots retained.
delayed-source : Checker.SourceTrace S.genericNext delayed-client delayed-server
delayed-source = _ , delayed-merge , Fixture.delayed-state , B.sound Fixture.both-delayed

-- Fixing the whole input gives the exact integration instance used by its public checker.
module Delayed = Checker.For S.genericNext delayed-client delayed-server

-- Whole-input adequacy transports that real raw source prefix into the finite basis search language.
delayed-basis : Delayed.Pair.PairTrace D.initial delayed-client delayed-server
delayed-basis = Delayed.source→basis delayed-source

-- Transporting back retains an actual raw initial run and an exact file-order merge witness.
delayed-roundtrip : Checker.SourceTrace S.genericNext delayed-client delayed-server
delayed-roundtrip = Delayed.basis→source delayed-basis
