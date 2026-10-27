{-# OPTIONS --guardedness #-}

-- Finite normal and synchronous-failure paths. Policy choice, pool join, buffer
-- release and main-thread delivery are inputs; no source progress theorem.
module ConnectionManagement.CSP.HandlerOutcomes where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_; map; replicate)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Machine
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence
open import ConnectionManagement.CSP.Hiding
open import ConnectionManagement.CSP.HandlerLifecycle using (tracked; withMux; withQueue; cancelError; handlerPhase; muxStatus; cleanupSnapshot)
open import ConnectionManagement.CSP.IGRegistration using (registered; mid; proto; lifecycle; lifecycle-path)
open import ConnectionManagement.CSP.IGRuntime using (runningMux; jobRunning; startActions; start-path)
open import ConnectionManagement.CSP.Fixtures using (start; childLease)
open import ConnectionManagement.Scenarios.Admission using (child₀; key₀)
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.Cleanup as C
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

-- Local command-queue fixture: shutdown request provenance is not asserted.
stopBase : Configuration
stopBase = record jobRunning { inboundGovernor = IG.setMux mid
  (record runningMux { commands = M.shutdown ∷ [] }) (inboundGovernor jobRunning) }
stopMux : M.Mux
stopMux = record runningMux { status = M.stopped; runningJobs = []; callback = M.readActive M.muxStopped }
stopQueue : List IGEvent
stopQueue = inboundInfo (world jobRunning) ++ (muxFinished key₀ ∷ [])
n₀ n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈ : Configuration
n₀ = tracked L.monitoring stopBase
n₁ = withMux L.monitoring (record runningMux { status = M.stopping }) jobRunning
n₂ = withMux L.monitoring stopMux jobRunning
n₃ = withMux L.monitoring (record stopMux { callback = M.commitTrace true M.muxStopped }) jobRunning
n₄ = withQueue stopQueue (withMux L.monitoring
  (record stopMux { callback = M.returned; traceCounters = nothing }) jobRunning)
n₅ = tracked L.normalClosing n₄
n₆ = tracked L.normalClosed n₄
n₇ = tracked L.normalBodyExited n₄
n₈ = tracked L.finalizing (record n₄ { world = record (world n₄) { cleanups = (child₀ , cleanupAcquire) ∷ [] } })
normalActions : List Action
normalActions = handlerStep child₀ (L.attach cancelError) ∷ igStep (IG.monitorCommand mid) ∷
  igStep (IG.finishStop mid) ∷ igStep (IG.sampleTracer mid) ∷ igStep (IG.commitTracer mid) ∷
  handlerStep child₀ L.monitorReturned ∷ handlerStep child₀ L.jobPoolClosed ∷
  handlerStep child₀ L.finishBuffer ∷ handlerExit child₀ ∷ []
normal-path : Executes stopBase normalActions n₈
normal-path = next {c₁ = n₀} refl (next {c₁ = n₁} refl (next {c₁ = n₂} refl
  (next {c₁ = n₃} refl (next {c₁ = n₄} refl (next {c₁ = n₅} refl
  (next {c₁ = n₆} refl (next {c₁ = n₇} refl (next refl done))))))))
normal-hidden : traces (HiddenProcess stopBase) (map label (project normalActions))
normal-hidden = hidden-trace normal-path
stopped-is-not-body-exit : advance (handlerExit child₀) n₄ ≡ nothing
stopped-is-not-body-exit = refl
no-return-before-stop-tracer : advance (handlerStep child₀ L.monitorReturned) n₃ ≡ nothing
no-return-before-stop-tracer = refl
normal-no-policy : advance (handlerStep child₀ (L.choosePolicy L.shutdownPeer)) n₆ ≡ nothing
normal-no-policy = refl
normal-no-async-failure : advance (handlerStep child₀ L.publishAsyncFailure) n₆ ≡ nothing
normal-no-async-failure = refl

-- Synchronous mini-protocol failure is produced by the modeled job machinery.
err : ErrorId
err = errorId 42
failedJob failedMonitor : M.Mux
failedJob = record runningMux { runningJobs = []; finishedJobs = (1 , errored err) ∷ [] }
failedMonitor = record runningMux { runningJobs = []; status = M.failed err;
  callback = M.readActive (M.completed 1 (errored err)) }
errorQueue deadQueue : List IGEvent
errorQueue = inboundInfo (world jobRunning) ++
  (miniProtocolTerminated (terminatedProtocol key₀ mid proto duplex (errored err)) ∷ [])
deadQueue = errorQueue ++ (muxFinished key₀ ∷ [])
s₀ s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ : Configuration
s₀ = tracked L.monitoring jobRunning
s₁ = withMux L.monitoring failedJob jobRunning
s₂ = withMux L.monitoring (record failedJob { finishedJobs = []; completions = M.jobResult M.responderJob 1 (errored err) ∷ [] }) jobRunning
s₃ = withMux L.monitoring failedMonitor jobRunning
s₄ = withMux L.monitoring (record failedMonitor { callback = M.commitTrace true (M.completed 1 (errored err)) }) jobRunning
s₅ = withQueue errorQueue (withMux L.monitoring (record failedMonitor { callback = M.afterFailure; traceCounters = nothing }) jobRunning)
s₆ = withQueue errorQueue (withMux L.monitoring (record failedMonitor { callback = M.readActive M.muxStopped; traceCounters = nothing }) jobRunning)
s₇ = withQueue errorQueue (withMux L.monitoring (record failedMonitor { callback = M.commitTrace true M.muxStopped; traceCounters = nothing }) jobRunning)
s₈ = withQueue deadQueue (withMux L.monitoring (record failedMonitor { callback = M.returned; traceCounters = nothing }) jobRunning)
s₉ = tracked (L.syncClosing err) s₈
s₁₀ = tracked (L.syncClosed err) s₈
s₁₁ = tracked (L.classifying err) s₈
syncActions : List Action
syncActions = handlerStep child₀ (L.attach cancelError) ∷ igStep (IG.finishProtocol mid 1 (errored err)) ∷
  igStep (IG.publishJobResult mid 1) ∷ igStep (IG.monitorCompletion mid) ∷
  igStep (IG.sampleTracer mid) ∷ igStep (IG.commitTracer mid) ∷
  igStep (IG.monitorCommand mid) ∷ igStep (IG.sampleTracer mid) ∷ igStep (IG.commitTracer mid) ∷
  handlerStep child₀ L.monitorThrew ∷ handlerStep child₀ L.jobPoolClosed ∷ handlerStep child₀ L.finishBuffer ∷ []
sync-path : Executes jobRunning syncActions s₁₁
sync-path = next {c₁ = s₀} refl (next {c₁ = s₁} refl (next {c₁ = s₂} refl
  (next {c₁ = s₃} refl (next {c₁ = s₄} refl (next {c₁ = s₅} refl
  (next {c₁ = s₆} refl (next {c₁ = s₇} refl (next {c₁ = s₈} refl
  (next {c₁ = s₉} refl (next {c₁ = s₁₀} refl (next refl done)))))))))))
sync-composed-trace : traces (Process start) (map label (lifecycle ++ (startActions ++ syncActions)))
sync-composed-trace = trace-intro (exec-append lifecycle-path (exec-append start-path sync-path))
sync-hidden : traces (HiddenProcess jobRunning) (map label (project syncActions))
sync-hidden = hidden-trace sync-path
no-pool-close-before-dead : advance (handlerStep child₀ L.jobPoolClosed) s₇ ≡ nothing
no-pool-close-before-dead = refl
no-throw-before-dead : advance (handlerStep child₀ L.monitorThrew) s₇ ≡ nothing
no-throw-before-dead = refl
no-classifier-before-buffer : advance (handlerStep child₀ (L.choosePolicy L.shutdownNode)) s₁₀ ≡ nothing
no-classifier-before-buffer = refl
no-async-catch-on-sync : advance (handlerStep child₀ L.publishAsyncFailure) s₁₀ ≡ nothing
no-async-catch-on-sync = refl
sync-error-retained : muxStatus s₁₁ ≡ just (M.failed err)
sync-error-retained = refl

peerChosen peerExited peerCleanup nodePending nodeDelivered nodeExited nodeCleanup : Configuration
peerChosen = tracked (L.peerRethrow err) s₁₁
peerExited = tracked (L.peerBodyExited err) s₁₁
peerCleanup = tracked L.finalizing (record s₁₁ { world = record (world s₁₁) { cleanups = (child₀ , cleanupAcquire) ∷ [] } })
nodePending = tracked (L.nodeDelivery err) s₁₁
nodeDelivered = tracked (L.nodeRethrow err) s₁₁
nodeExited = tracked (L.nodeBodyExited err) s₁₁
nodeCleanup = peerCleanup
peerActions nodeActions : List Action
peerActions = handlerStep child₀ (L.choosePolicy L.shutdownPeer) ∷ handlerStep child₀ L.rethrow ∷ handlerExit child₀ ∷ []
nodeActions = handlerStep child₀ (L.choosePolicy L.shutdownNode) ∷ handlerStep child₀ L.nodeExceptionDelivered ∷
  handlerStep child₀ L.rethrow ∷ handlerExit child₀ ∷ []
peer-path : Executes s₁₁ peerActions peerCleanup
peer-path = next {c₁ = peerChosen} refl (next {c₁ = peerExited} refl (next refl done))
node-path : Executes s₁₁ nodeActions nodeCleanup
node-path = next {c₁ = nodePending} refl (next {c₁ = nodeDelivered} refl (next {c₁ = nodeExited} refl (next refl done)))
node-cleanup-trace : traces (Process jobRunning) (map label (syncActions ++ nodeActions))
node-cleanup-trace = trace-intro (exec-append sync-path node-path)
peer-composed-trace : traces (Process start)
  (map label (lifecycle ++ (startActions ++ (syncActions ++ peerActions))))
peer-composed-trace = trace-intro (exec-append lifecycle-path
  (exec-append start-path (exec-append sync-path peer-path)))
node-composed-trace : traces (Process start)
  (map label (lifecycle ++ (startActions ++ (syncActions ++ nodeActions))))
node-composed-trace = trace-intro (exec-append lifecycle-path
  (exec-append start-path (exec-append sync-path node-path)))
node-delivery-is-not-a-join : handlerPhase nodeDelivered ≡ just (L.nodeRethrow err)
node-delivery-is-not-a-join = refl
no-rethrow-before-node-delivery : advance (handlerStep child₀ L.rethrow) nodePending ≡ nothing
no-rethrow-before-node-delivery = refl
no-cleanup-before-node-delivery : ¬ traces (Process nodePending) (map label (handlerExit child₀ ∷ []))
no-cleanup-before-node-delivery = refused-extension done refl
peer-does-not-notify-node : advance (handlerStep child₀ L.nodeExceptionDelivered) peerChosen ≡ nothing
peer-does-not-notify-node = refl

-- Both Failed/Stopped may be visible while a synchronous notification blocks.
fullSync fullNormal : Configuration
fullSync = withQueue (replicate 100 inactivityTimeout) s₇
fullNormal = withQueue (replicate 100 inactivityTimeout) n₃
sync-backpressure : advance (igStep (IG.commitTracer mid)) fullSync ≡ nothing
sync-backpressure = refl
normal-backpressure : advance (igStep (IG.commitTracer mid)) fullNormal ≡ nothing
normal-backpressure = refl

-- Local failed-descriptor callback fixture. The sync catch does not write Failed
-- or emit a second Dead event when the tracer itself throws.
badTracer tracerClosing : Configuration
badTracer = withMux L.monitoring (record runningMux { callback = M.tracerFailed 99 }) jobRunning
tracerClosing = tracked (L.syncClosing err) badTracer
tracer-failure-path : Executes badTracer (handlerStep child₀ (L.tracerThrew err) ∷ []) tracerClosing
tracer-failure-path = next refl done
tracer-leaves-status : muxStatus tracerClosing ≡ just M.ready
tracer-leaves-status = refl
tracer-leaves-queue : inboundInfo (world tracerClosing) ≡ inboundInfo (world jobRunning)
tracer-leaves-queue = refl
tracer-does-not-resume : advance (igStep (IG.monitorCommand mid)) tracerClosing ≡ nothing
tracer-does-not-resume = refl
