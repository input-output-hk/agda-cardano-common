{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)

-- Exact bitmap server soundness, conditional on each logged message's decoder checks.
-- Counts and decoded request offsets are observed; client receive sizes use WireOK.
-- Checked with --safe on the command line (B7a).
module Cardano_network.Replay.LeiosFetchServerSound (k : ℕ) where

open import Data.Product using (∃-syntax; _×_; _,_)

open import Process_Trees using (ExtI)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Net replayParams using (Net_Api)
open import Cardano_network.Data replayParams using (Payload)
open import Cardano_network.Replay.LeiosFetchServerModel using (serverModel)
open import Cardano_network.Replay.LeiosFetchObs
  using (ObsS; clsS; forget)
open import Cardano_network.Replay.LeiosFetchWireOK using (WireOK)
open import Cardano_network.Replay.LeiosFetchServerRel k using (Rel; rel₀; sim-τ)
open import Cardano_network.Replay.LeiosFetchServerSimEv k using (sim-ev)
open import Semantics.Deadlock {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (_⟹∖√⟨_⟩_)
import Cardano_network.Replay.LeiosFetchWireBridge {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as BrS

open import Cardano_network.Replay.LeiosFetchSession
  using (server₀; module Spec)
open Spec k using (leiosFetch)
open import Semantics.Replay using (module Traces)
open Traces leiosFetch using (HasTrace)

-- the spec simulates the server composite over the store holding `bs`
serverSim : ∀ bs → BrS.Sim k clsS (Rel bs)
serverSim bs = record { sim-τ = sim-τ ; sim-ev = sim-ev }

-- Every model run matching an admissible exact-bitmap log is a legal server trace.
server-sound : ∀ bs {t M es} → serverModel bs ⟹∖√⟨ t ⟩ M → ObsS t es → WireOK es → HasTrace server₀ es
server-sound bs run obs wire with BrS.sound k clsS (Rel bs) (serverSim bs) (rel₀ bs) run obs wire
... | s′ , trace , related = s′ , trace
