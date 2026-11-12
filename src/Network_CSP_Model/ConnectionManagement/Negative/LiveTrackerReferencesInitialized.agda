{-# OPTIONS --guardedness #-}

-- Apply the initialized reference certificate to the same completed inner run
-- used by IGPendingQuiet's scheduled close. The run contains a real handler
-- birth, negotiated mux, cleanup and physical result, not an empty registry.
module ConnectionManagement.Negative.LiveTrackerReferencesInitialized where

open import ConnectionManagement.Negative.ServerPeers using (module Protocols)
open import Data.Maybe using (nothing; just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.GovernorPool as Prior
open import ConnectionManagement.Properties.LiveTrackerOwnersInitialized using (module Frontend)
open Protocols using (capability; initializer)
open Protocols.StartTrace.ScopedCM.Completion using
  (serverFinished; initialized-server-finish)
open Frontend I.bearerClosed Prior.classify capability using (Validity; from-initial)

-- The universal theorem supplies all references at this existing endpoint.
scheduled-close : Validity serverFinished
scheduled-close = from-initial _ _ initializer initialized-server-finish

import ConnectionManagement.Properties.LiveTrackerSnapshotsInitialized as Snapshot
import ConnectionManagement.MuxHandlerExit as Exit
import ConnectionManagement.MuxStartupUnwind as Unwind
import ConnectionManagement.Scenarios.Admission as A
import ConnectionManagement.State as Shared
open Snapshot.Frontend I.bearerClosed Prior.classify capability using (DescriptorReferences)
  renaming (Validity to SnapshotValidity; from-initial to snapshots-from-initial)
open Protocols.StartTrace using (traceError; selectedFault)
open Exit I.bearerClosed using (exitFrame; resultAvailable; asyncException)
open Unwind I.bearerClosed using (async; handedOff)

-- Extend the same initialized scheduled-close certificate with exact captures.
scheduled-snapshots : SnapshotValidity serverFinished
scheduled-snapshots = snapshots-from-initial _ _ initializer initialized-server-finish

-- The exit and fault rows are present: these applications exercise their
-- original descriptors after cleanup, physical publication and Server return.
scheduled-exit-capture : DescriptorReferences A.child₀ I.captured serverFinished
scheduled-exit-capture = Snapshot.Frontend.Validity.exits scheduled-snapshots A.child₀
  (exitFrame I.captured (resultAvailable (asyncException traceError) Shared.cleanupNormal) nothing) refl

scheduled-fault-capture : DescriptorReferences A.child₀ I.captured serverFinished
scheduled-fault-capture = Snapshot.Frontend.Validity.faults scheduled-snapshots A.child₀
  (selectedFault (async traceError) handedOff) refl

import ConnectionManagement.Properties.LivePromiseResultFrontend as Result
import ConnectionManagement.ServerPeers as Model
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
open import ConnectionManagement.Domain using (ident; duplex)
open import ConnectionManagement.Store using (lookup)
open Model.Protocols I.bearerClosed Prior.classify capability using (sourceOf)
open Protocols.StartTrace.ScopedCM.Completion using (finishPath)

-- Reuse the real cleanup/result/CM/Server suffix to transport the exact
-- negotiated promise result, rather than recomputing the endpoint result.
scheduled-published-result :
  lookup (Shared.handlerPromise I.captured)
    (Shared.handshakeResults (Machine.world (O.core (sourceOf serverFinished)))) ≡
    just (Shared.negotiated (ident 0) duplex)
scheduled-published-result = Result.Frontend.run-preserves I.bearerClosed Prior.classify
  (Shared.handlerPromise I.captured) (Shared.negotiated (ident 0) duplex) capability finishPath refl

import ConnectionManagement.Properties.LiveTrackerChainSteps as Chain
open Protocols.StartTrace using (failedMux)

-- A concrete allocation chain survives the scheduled failure and shutdown.
-- This fixture is separate from the still-open universal allocation invariant.
scheduled-handle-mux : Chain.Anchor I.captured I.ps duplex (ident 0) (ident 0)
  (Machine.inboundGovernor (O.core (sourceOf serverFinished)))
scheduled-handle-mux = record
  { handle-found = refl; mux-value = failedMux; mux-found = refl; mux-key = refl }
