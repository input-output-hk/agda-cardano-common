{-# OPTIONS --safe #-}

-- Necessary guards refute original source traces without turning their success into acceptance.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverPrecheckTests where

open import Data.Bool using (Bool; true; false)
import Data.Bool.Properties as Bool
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (does; toWitness; toWitnessFalse)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Bool ⊤ as Rows
import Cardano_network.LeiosNotifyPipeLookahead.DriverConservation Bool ⊤ as Conservation
import Cardano_network.Replay.LeiosNotifyPipeLookahead.LocalPrecheck Bool ⊤ as Local
import Cardano_network.Replay.LeiosNotifyPipeLookahead.PacketPrecheck Bool ⊤ as Packet
import Cardano_network.Replay.LeiosNotifyPipeLookahead.PacketCountPrecheck Bool ⊤ as Count
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverDecide Bool Bool._≟_ false as Check
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverDecideTests as Existing

-- A response receive may precede its client Request Send record at unfinished EOF.
lead-client : List Rows.ClientRow
lead-client = Rows.receiveResponse (D.reply (S.normal false)) ∷ []

-- Its server has recorded Request Receive but can still have the reply Send hook pending.
lead-server : List Rows.ServerRow
lead-server = Rows.receiveCommand D.request ∷ []

-- This independently constructed actual source execution witnesses both delayed Send hooks.
lead-source : Check.SourceTrace S.genericNext lead-client lead-server
lead-source = Existing.delayed-source

-- Source necessity preserves that concrete Lead witness rather than imposing recorded-Send-first order.
lead-necessary : Check.Prechecks S.genericNext lead-client lead-server
lead-necessary = Check.precheck-necessary lead-source

-- The public decision still constructs a complete source witness after the cheap guards pass.
lead-computed : Check.SourceTrace S.genericNext lead-client lead-server
lead-computed = toWitness {a? = Check.decide S.genericNext lead-client lead-server} tt

-- The next recorded packet differs from the sole server reply, while both local peers are valid.
wrong-client : List Rows.ClientRow
wrong-client = Rows.receiveResponse (D.reply (S.normal true)) ∷ []

-- Exact source packet values remain distinct even though their notification kinds are the same.
wrong-server : List Rows.ServerRow
wrong-server = Rows.receiveCommand D.request ∷ Rows.sendResponse (D.reply (S.normal false)) ∷ []

-- Independent local validity cannot establish a joint exact-payload execution.
wrong-local-pass : Local.Pass S.nodeNext wrong-client wrong-server
wrong-local-pass = toWitness {a? = Local.decide S.nodeNext wrong-client wrong-server} tt

-- The packet-prefix guard refutes the inconsistent common packet head directly.
wrong-packet-fails : Packet.Pass wrong-client wrong-server → ⊥
wrong-packet-fails = toWitnessFalse {a? = Packet.decide Bool._≟_ wrong-client wrong-server} tt

-- Public rejection has the unchanged unrestricted source proposition and needs no paired branch search.
wrong-source-fails : Check.SourceTrace S.nodeNext wrong-client wrong-server → ⊥
wrong-source-fails = toWitnessFalse {a? = Check.decide S.nodeNext wrong-client wrong-server} tt

-- These two Request receive records have no corresponding client Send records at all.
two-requests : List Rows.ServerRow
two-requests = Rows.receiveCommand D.request ∷ Rows.receiveCommand D.request ∷ []

-- Both original necessary-only guards pass, under either callback contract.
two-requests-base-pass : ∀ contract → Check.BasePrechecks contract [] two-requests
two-requests-base-pass contract = toWitness {a? = Check.base-prechecks? contract [] two-requests} tt

-- The added exact pending-Send bound refutes this impossible receive count directly.
two-requests-count-fails : Count.Pass [] two-requests → ⊥
two-requests-count-fails = toWitnessFalse {a? = Count.decide [] two-requests} tt

-- Only one pending client Send can explain an unrecorded command, never two recorded receives.
two-requests-impossible : ∀ contract → Check.SourceTrace contract [] two-requests → ⊥
two-requests-impossible contract
  (_ , Rows.server (Rows.server Rows.empty) , D.pair c server cs sc nothing ps rc rs , source)
  with Conservation.to-server (Conservation.initial-conservation source)
... | ()
two-requests-impossible contract
  (_ , Rows.server (Rows.server Rows.empty) , D.pair c server cs sc (just message) ps rc rs , source)
  with Conservation.to-server (Conservation.initial-conservation source)
... | ()

-- The complete search backend still independently refutes the same source history.
backend-rejects : Check.SourceTrace S.nodeNext [] two-requests → ⊥
backend-rejects = toWitnessFalse {a? = Check.For.check S.nodeNext [] two-requests} tt

-- The public decision now uses the proved count refutation rather than requiring that search.
count-rejects : Check.SourceTrace S.nodeNext [] two-requests → ⊥
count-rejects = toWitnessFalse {a? = Check.decide S.nodeNext [] two-requests} tt

-- A local client can receive an early reply, while an empty local server trace remains valid.
unmatched-client : List Rows.ClientRow
unmatched-client = Rows.receiveResponse (D.reply (S.normal false)) ∷ []

-- All three guards allow this input: the common prefix is empty and the receive lead is exactly one.
unmatched-all-pass : ∀ contract → Check.Prechecks contract unmatched-client []
unmatched-all-pass contract = toWitness {a? = Check.prechecks? contract unmatched-client []} tt

-- The original three guards are insufficient; the later credit guard now refutes this source history.
fallback-generic-rejects : Check.SourceTrace S.genericNext unmatched-client [] → ⊥
fallback-generic-rejects = toWitnessFalse {a? = Check.decide S.genericNext unmatched-client []} tt

-- The original source history is also refuted under the node server callback contract.
fallback-node-rejects : Check.SourceTrace S.nodeNext unmatched-client [] → ⊥
fallback-node-rejects = toWitnessFalse {a? = Check.decide S.nodeNext unmatched-client []} tt

-- A Done record alone is an endpoint phase error, even though packet-prefix agreement is vacuous.
early-done-client : List Rows.ClientRow
early-done-client = Rows.receiveResponse D.done ∷ []

-- An absent sender suffix remains permitted by prefix conservation alone.
early-done-packet-pass : Packet.Pass early-done-client []
early-done-packet-pass = tt , tt

-- The local phase guard supplies exhaustive refutation of the same original source language.
early-done-source-fails : Check.SourceTrace S.nodeNext early-done-client [] → ⊥
early-done-source-fails = toWitnessFalse {a? = Check.decide S.nodeNext early-done-client []} tt

-- Empty input retains zero-operation prefix acceptance rather than forcing protocol termination.
empty-accepted : does (Check.decide S.nodeNext [] []) ≡ true
empty-accepted = refl
