{-# OPTIONS --guardedness #-}

-- Complete ownership preservation for the actual ServerPeers execution relation.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesExecution
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Maybe using (just)
open import Data.Product using (proj₁)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesReach as FullReachFacts
import ConnectionManagement.Properties.OwnedFramesQuietSteps as QuietFacts
import ConnectionManagement.Properties.OwnedFramesForkJob as ForkFacts
import ConnectionManagement.Properties.OwnedFramesJobSteps as JobsFacts
import ConnectionManagement.Properties.OwnedFramesFlagSteps as FlagsFacts
import ConnectionManagement.Properties.OwnedFramesPollSteps as PollFacts
import ConnectionManagement.Properties.OwnedFramesMonitorSteps as MonitorFacts
import ConnectionManagement.Properties.OwnedFramesMonitorFinished as FinishedFacts
import ConnectionManagement.Properties.OwnedFramesUnwindSteps as UnwindFacts
import ConnectionManagement.Properties.OwnedFramesPoolActions as PoolFacts
import ConnectionManagement.Properties.OwnedFramesCancellation as CancelFacts
import ConnectionManagement.Properties.OwnedFramesRecovery as RecoveryFacts
import ConnectionManagement.Properties.OwnedFramesForkMonitor as ForkMonitorFacts
import ConnectionManagement.Properties.OwnedFramesMonitorAdapters as AdaptersFacts
import ConnectionManagement.Properties.OwnedFramesEstablishment as EstablishmentFacts
import ConnectionManagement.Properties.OwnedFramesMonitorDetach as DetachFacts
import ConnectionManagement.Properties.OwnedFramesScopes as ScopesFacts
open Frames isBearerClosed isIOManagerError
open FullReachFacts isBearerClosed isIOManagerError public using (Reach; initial-reach)
private
  module FullReach = FullReachFacts isBearerClosed isIOManagerError
  module Quiet = QuietFacts isBearerClosed isIOManagerError
  module Fork = ForkFacts isBearerClosed isIOManagerError
  module Jobs = JobsFacts isBearerClosed isIOManagerError
  module Flags = FlagsFacts isBearerClosed isIOManagerError
  module Poll = PollFacts isBearerClosed isIOManagerError
  module Monitor = MonitorFacts isBearerClosed isIOManagerError
  module Finished = FinishedFacts isBearerClosed isIOManagerError
  module Unwind = UnwindFacts isBearerClosed isIOManagerError
  module Pool = PoolFacts isBearerClosed isIOManagerError
  module Cancel = CancelFacts isBearerClosed isIOManagerError
  module Recovery = RecoveryFacts isBearerClosed isIOManagerError
  module ForkMonitor = ForkMonitorFacts isBearerClosed isIOManagerError
  module Adapters = AdaptersFacts isBearerClosed isIOManagerError
  module Establishment = EstablishmentFacts isBearerClosed isIOManagerError
  module Detach = DetachFacts isBearerClosed isIOManagerError
  module Scopes = ScopesFacts isBearerClosed isIOManagerError

-- Raw peer core actions are excluded by K.rawPeerAllowed itself.
peer-core : ∀ a s {t} → K.step (K.peerStep (PS.run (GP.run (Sub.core a)))) s ≡ just t → Reach s → Reach t
peer-core a s eq held with K.peerOpen s
... | false = case eq of λ ()
... | true = case eq of λ ()

-- Every Sub.Action constructor is delegated to its concrete preservation layer.
subsystem-reach : ∀ a s {t} → K.step (K.peerStep (PS.run (GP.run a))) s ≡ just t → Reach s → Reach t
subsystem-reach (Sub.core a) = peer-core a
subsystem-reach Sub.publishPublicState s = Quiet.k-quiet-step (Sub.publishPublicState) s refl
subsystem-reach (Sub.sampleTime time) s = Quiet.k-quiet-step (Sub.sampleTime time) s refl
subsystem-reach (Sub.applyAt time) s = Quiet.k-quiet-step (Sub.applyAt time) s refl
subsystem-reach (Sub.setTargets desired) s = Quiet.k-quiet-step (Sub.setTargets desired) s refl
subsystem-reach (Sub.selectMonitor delays) s = Quiet.k-quiet-step (Sub.selectMonitor delays) s refl
subsystem-reach Sub.selectCompletion s = Quiet.k-quiet-step (Sub.selectCompletion) s refl
subsystem-reach Sub.selectTargets s = Quiet.k-quiet-step (Sub.selectTargets) s refl
subsystem-reach Sub.selectWakeup s = Quiet.k-quiet-step (Sub.selectWakeup) s refl
subsystem-reach Sub.registerWakeup s = Quiet.k-quiet-step (Sub.registerWakeup) s refl
subsystem-reach Sub.expireWakeup s = Quiet.k-quiet-step (Sub.expireWakeup) s refl
subsystem-reach Sub.cancelWakeup s = Quiet.k-quiet-step (Sub.cancelWakeup) s refl
subsystem-reach Sub.publishCounters s = Quiet.k-quiet-step (Sub.publishCounters) s refl
subsystem-reach Sub.traceSelection s = Quiet.k-quiet-step (Sub.traceSelection) s refl
subsystem-reach (Sub.selectPolicy picked) s = Quiet.k-quiet-step (Sub.selectPolicy picked) s refl
subsystem-reach Sub.registerJob s = Quiet.k-quiet-step (Sub.registerJob) s refl
subsystem-reach Sub.finishLaunch s = Quiet.k-quiet-step (Sub.finishLaunch) s refl
subsystem-reach (Sub.protocolResult ref n result) s = Quiet.k-quiet-step (Sub.protocolResult ref n result) s refl
subsystem-reach (Sub.publishInitiatorResult ref n) s = Quiet.k-quiet-step (Sub.publishInitiatorResult ref n) s refl
subsystem-reach (Sub.observeInitiatorFailure ref) s = Quiet.k-quiet-step (Sub.observeInitiatorFailure ref) s refl
subsystem-reach (Sub.forkJob w child sock) = Fork.k-fork w child sock
subsystem-reach (Sub.jobStep j a) = Jobs.k-job-step j a
subsystem-reach (Sub.enqueueCompletion j delay) s = Flags.k-flags (Sub.enqueueCompletion j delay) s refl
subsystem-reach (Sub.deregisterJob j) s = Flags.k-flags (Sub.deregisterJob j) s refl
subsystem-reach (Sub.pollPeer ref caller) = Poll.k-poll ref caller
subsystem-reach (Sub.monitorStep ref a) = Monitor.k-monitor-step ref a
subsystem-reach (Sub.monitorFinished ref) = Finished.k-finished ref

-- Every GP.Action constructor includes its actual pool/cancellation writes.
governor-reach : ∀ a s {t} → K.step (K.peerStep (PS.run a)) s ≡ just t → Reach s → Reach t
governor-reach (GP.run a) = subsystem-reach a
governor-reach (GP.handoff w) = Unwind.k-handoff w
governor-reach (GP.beginClose js) s = Pool.k-governor-pool (GP.beginClose js) s refl
governor-reach GP.requestCancel s = Pool.k-governor-pool (GP.requestCancel) s refl
governor-reach GP.join s = Pool.k-governor-pool (GP.join) s refl
governor-reach GP.finishClose s = Pool.k-governor-pool (GP.finishClose) s refl
governor-reach (GP.publishAsyncResult j) s = Pool.k-governor-pool (GP.publishAsyncResult j) s refl
governor-reach (GP.deliverCancellation err) = Cancel.k-ordinary-delivery err
governor-reach (GP.deliverOpenCancellation err) = Cancel.k-blocked-delivery err
governor-reach (GP.cleanup j a) = Unwind.k-cleanup j a
governor-reach (GP.bodyUnwound j) = Unwind.k-body-unwound j
governor-reach (GP.recoverCloseFailure j) = Recovery.k-recovery j
governor-reach (GP.deregisterCancelled j) = Flags.k-cancelled j

-- All PSA constructors, including both delivery modes, fork, poll and scopes.
peer-reach : ∀ a s {t} → K.step (K.peerStep a) s ≡ just t → Reach s → Reach t
peer-reach (PS.run a) = governor-reach a
peer-reach (PS.forkMonitor j w) = ForkMonitor.k-fork-monitor j w
peer-reach (PS.registerMonitor j) = Adapters.k-register-monitor j
peer-reach (PS.returnEstablishment j) = Establishment.k-return-establishment j
peer-reach (PS.finishEstablishment j) = Establishment.k-finish-establishment j
peer-reach (PS.monitorException j err) = Detach.k-monitor-exception j err
peer-reach (PS.commitMonitorError j) = Adapters.k-commit-error j
peer-reach (PS.finishMonitorError j) = Adapters.k-finish-error j
peer-reach (PS.finishMonitor j) = Adapters.k-finish-monitor j
peer-reach (PS.scope a) = Scopes.k-scope-step a
peer-reach (PS.beginMonitorClose js) s = Pool.k-monitor-pool (PS.beginMonitorClose js) s refl
peer-reach PS.requestMonitorCancel s = Pool.k-monitor-pool (PS.requestMonitorCancel) s refl
peer-reach PS.joinMonitor s = Pool.k-monitor-pool (PS.joinMonitor) s refl
peer-reach PS.finishMonitorClose s = Pool.k-monitor-pool (PS.finishMonitorClose) s refl
peer-reach (PS.deregisterMonitor j) s = Pool.k-monitor-pool (PS.deregisterMonitor j) s refl
peer-reach (PS.publishMonitorResult j) s = Pool.k-monitor-pool (PS.publishMonitorResult j) s refl
peer-reach (PS.deliverMonitorCancellation err) = Detach.k-monitor-cancel err
peer-reach (PS.deliverBlockedMonitorCancellation err) = Detach.k-monitor-blocked-cancel err
peer-reach (PS.monitorBodyUnwound j) = Adapters.k-monitor-body-unwound j

-- The three actual K transition kinds exhaust successful shared steps.
step-reach : ∀ a s {t} → K.step a s ≡ just t → Reach s → Reach t
step-reach (K.serverStep a) = FullReach.server-reach a
step-reach (K.coreStep a) = FullReach.core-reach a
step-reach (K.peerStep a) = peer-reach a

-- Finite executions preserve the full strengthened invariant by induction.
exec-reach : ∀ {s as t} → K.Executes s as t → Reach s → Reach t
exec-reach K.done held = held
exec-reach (K.next {s = s} {a = a} stepped rest) held = exec-reach rest (step-reach a s stepped held)

-- Every state reachable from an accepted empty-table initialization satisfies it.
reachable-reach : ∀ c g {s as t} → K.initial (O.initial c) g ≡ just s → K.Executes s as t → Reach t
reachable-reach c g initialized path = exec-reach path (initial-reach c g initialized)

-- The original unweakened acquisition (A) and release (R) clauses are a projection.
reachable-owned : ∀ c g {s as t} → K.initial (O.initial c) g ≡ just s → K.Executes s as t → Owned t
reachable-owned c g initialized path = proj₁ (reachable-reach c g initialized path)
