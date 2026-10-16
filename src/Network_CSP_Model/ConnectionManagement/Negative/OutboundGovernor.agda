{-# OPTIONS --guardedness #-}

-- Completion races, in-progress exclusions and source polling priorities.
module ConnectionManagement.Negative.OutboundGovernor where

open import Data.Bool using (false; true)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
import ConnectionManagement.IGTypes as I
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.PeerActions as P
open import ConnectionManagement.Scenarios.Admission using (key₀)

p : PeerAddr
p = remote key₀
warm : G.State
warm = G.governorState (G.targets 1 1 1) ((p , G.known 0 0 nothing false true) ∷ [])
  ((p , G.established (ident 0) 0) ∷ []) [] [] [] [] [] []
activating : G.State
activating = G.mark G.activate (p ∷ []) warm
no-duplicate-promotion : G.choose 0 (p ∷ []) activating ≡ nothing
no-duplicate-promotion = refl
activation : G.Job
activation = G.job G.activate p (just (ident 0))
removed : G.State
removed = record activating { establishedPeers = [] }
late-success-does-not-resurrect : G.complete 5 60 10 (G.completion activation G.succeeded 0) removed ≡ removed
late-success-does-not-resurrect = refl
cancelled : G.State
cancelled = record removed { promotingWarm = [] }
late-failure-after-monitor-is-aborted : G.complete 5 60 10 (G.completion activation G.failed 10) cancelled ≡ cancelled
late-failure-after-monitor-is-aborted = refl

hot : G.State
hot = record warm { activePeers = p ∷ []; demotingHot = p ∷ [] }
timeout-keeps-established-and-active : G.complete 5 60 10
  (G.completion (G.job G.deactivate p (just (ident 0))) G.demotionTimedOut 0) hot ≡
  record hot { demotingHot = [] }
timeout-keeps-established-and-active = refl
synchronous-cooling-not-async : G.asyncDemotion p P.peerCooling hot ≡ false
synchronous-cooling-not-async = refl
cooling : G.State
cooling = G.applyMonitor 5 10 0 ((p , P.peerCooling) ∷ []) activating
cooling-retains-established : G.establishedPeers cooling ≡ G.establishedPeers activating
cooling-retains-established = refl
cooling-clears-promotion : G.promotingWarm cooling ≡ []
cooling-clears-promotion = refl
cooling-excluded-from-selection : G.eligible 10 G.activate cooling ≡ []
cooling-excluded-from-selection = refl
invalid-targets : G.sane (G.targets 1 0 1) ≡ false
invalid-targets = refl

-- Source awaitFirstResult first reads a result cell, then retries if it is
-- NotRunning/NotStarted. It does not skip that cell to a later ready result.
runs : Data.List.List P.ProtocolRun
runs = P.protocolRun (I.protocol 1 I.hot I.eagerly) (P.notRunning I.clean) (P.notRunning I.clean) ∷
  P.protocolRun (I.protocol 2 I.hot I.eagerly) (P.returned I.clean) P.running ∷ []
not-running-blocks-first-result : P.first I.hot runs ≡ nothing
not-running-blocks-first-result = refl
last-to-finish-accepts-retired : P.all I.hot runs ≡ just I.clean
last-to-finish-accepts-retired = refl

-- Starting a new run cannot retarget an old published result action.
oldRun : P.ProtocolRun
oldRun = P.protocolRun (I.protocol 1 I.hot I.eagerly) (P.returned I.clean) P.running
restart-retains-old-result : P.startRun I.hot 1 (oldRun ∷ []) ≡
  just (P.protocolRun (I.protocol 1 I.hot I.eagerly) P.running (P.returned I.clean) ∷ [])
restart-retains-old-result = refl
