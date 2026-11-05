{-# OPTIONS --safe #-}

-- Shutdown necessity rejects orphan Done while preserving actual completion with a delayed Send hook.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverShutdownPrecheckTests where

open import Data.Bool using (Bool; false)
import Data.Bool.Properties as Bool
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Bool ⊤ as Rows
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverDecide Bool Bool._≟_ false as Check
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ShutdownPrecheck Bool ⊤ as Shutdown
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ShutdownPrecheckTests as Concrete
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverDecideTests as Existing
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverCreditPrecheckTests as Previous

-- The previous four-guard counterexample remains available at its original interface.
orphan-four-pass : ∀ contract → Check.FullPrechecks contract Previous.close-client []
orphan-four-pass = Previous.close-four-pass

-- A client Done with no recorded server Quit now fails a directly proved necessary condition.
orphan-shutdown-fails : Shutdown.Pass Previous.close-client [] → ⊥
orphan-shutdown-fails = toWitnessFalse {a? = Shutdown.decide Previous.close-client []} tt

-- Public rejection retains the same unrestricted source proposition under either callback contract.
orphan-rejected : ∀ contract → Check.SourceTrace contract Previous.close-client [] → ⊥
orphan-rejected contract = toWitnessFalse {a? = Check.decide contract Previous.close-client []} tt

-- A real normal response with both Send hooks pending has no spurious shutdown obligation.
lead-necessary : Check.AllPrechecks S.genericNext Previous.lead-client Previous.lead-server
lead-necessary = Check.all-precheck-necessary Existing.delayed-source

-- Client completion does not require the server's final Send trace hook to have appeared already.
pending-done-server : List Rows.ServerRow
pending-done-server = Rows.receiveCommand D.quit ∷ []

-- An explicit original source execution independently witnesses Send-Done still unrecorded.
pending-done-source : Check.SourceTrace S.nodeNext Previous.close-client pending-done-server
pending-done-source = _ , Rows.client (Rows.server (Rows.client Rows.empty)) ,
  Concrete.late-target , Concrete.late-source S.nodeNext

-- Necessity applies to that source witness rather than assuming that guard success implies acceptance.
pending-done-necessary : Check.AllPrechecks S.nodeNext Previous.close-client pending-done-server
pending-done-necessary = Check.all-precheck-necessary pending-done-source

-- Public replay preserves the same valid pending final hook.
pending-done-public : Check.SourceTrace S.nodeNext Previous.close-client pending-done-server
pending-done-public = toWitness {a? = Check.decide S.nodeNext Previous.close-client pending-done-server} tt

-- The ordinary zero-request close also survives the fifth guard and still reaches complete replay.
idle-close-public : Check.SourceTrace S.nodeNext Previous.close-client
  (Rows.receiveCommand D.quit ∷ Rows.sendResponse D.done ∷ [])
idle-close-public = Existing.idle-shutdown

-- Three early-response/finish-Request rounds form individually valid client wire observations.
cycle-client : List Rows.ClientRow
cycle-client =
  Rows.receiveResponse (D.reply (S.normal false)) ∷ Rows.sendCommand D.request ∷
  Rows.receiveResponse (D.reply (S.normal false)) ∷ Rows.sendCommand D.request ∷
  Rows.receiveResponse (D.reply (S.normal false)) ∷ Rows.sendCommand D.request ∷ []

-- The server records every Request before publishing any Reply Send hook.
cycle-server : List Rows.ServerRow
cycle-server =
  Rows.receiveCommand D.request ∷ Rows.receiveCommand D.request ∷ Rows.receiveCommand D.request ∷
  Rows.sendResponse (D.reply (S.normal false)) ∷ Rows.sendResponse (D.reply (S.normal false)) ∷
  Rows.sendResponse (D.reply (S.normal false)) ∷ []

-- This gate proves only all-five-guard success; incompatibility needs a separate source-order argument.
cycle-five-pass : ∀ contract → Check.AllPrechecks contract cycle-client cycle-server
cycle-five-pass contract = toWitness {a? = Check.all-prechecks? contract cycle-client cycle-server} tt
