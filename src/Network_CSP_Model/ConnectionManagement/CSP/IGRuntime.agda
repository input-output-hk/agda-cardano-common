{-# OPTIONS --guardedness #-}

-- Executable source-boundary regressions. Only the registration/maturity/start
-- paths below compose from the accepted-socket fixture; other states are local
-- transaction/interleaving fixtures, not source-reachable defect claims.
module ConnectionManagement.CSP.IGRuntime where

open import Process_Trees
open import Data.Integer using (+_; -[1+_])
open import Data.Nat using (ℕ)
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; map; replicate)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Machine
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence
open import ConnectionManagement.CSP.IGRegistration
open import ConnectionManagement.CSP.Fixtures using (start)
open import ConnectionManagement.Scenarios.Admission using (key₀; key₁)
open import ConnectionManagement.Scenarios.Handshake using (info)
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

-- Start real responder work only after command consumption and tracer return.
commandRead callbackEntered activeSampled traceCommitted statusRunning jobRunning : Configuration
commandRead = withIG registered
  (IG.setMux mid (record armedMux { commands = []; waiting = (1 , onDemand) ∷ [] }) (inboundGovernor registered)) []
callbackEntered = withIG registered
  (IG.setMux mid (record armedMux { commands = []; callback = M.readActive (M.started 1) }) (inboundGovernor registered)) []
activeSampled = withIG registered
  (IG.setMux mid (record armedMux { commands = []; callback = M.commitTrace true (M.started 1) }) (inboundGovernor registered)) []
startMessages : List IGEvent
startMessages = awakeRemote key₀ ∷ remotePromotedToHot key₀ ∷ []
traceCommitted = withIG registered
  (IG.setMux mid (record armedMux { commands = []; traceCounters = just (M.counters (+ 1) (+ 0)); callback = M.afterStart 1 }) (inboundGovernor registered)) startMessages
statusRunning = withIG registered
  (IG.setMux mid (record armedMux { commands = []; protocols = (1 , M.running) ∷ []; traceCounters = just (M.counters (+ 1) (+ 0)); callback = M.forkPending 1 }) (inboundGovernor registered)) startMessages
runningMux : M.Mux
runningMux = record armedMux { commands = []; protocols = (1 , M.running) ∷ []
  ; traceCounters = just (M.counters (+ 1) (+ 0)); runningJobs = 1 ∷ []; callback = M.returned }
jobRunning = withIG registered (IG.setMux mid runningMux (inboundGovernor registered)) startMessages

startActions : List Action
startActions = igStep (IG.monitorCommand mid) ∷ igStep (IG.startOnDemand mid 1) ∷
  igStep (IG.sampleTracer mid) ∷ igStep (IG.commitTracer mid) ∷
  igStep (IG.finishStart mid) ∷ igStep (IG.forkResponder mid) ∷ []
start-path : Executes registered startActions jobRunning
start-path = next {c₁ = commandRead} refl (next {c₁ = callbackEntered} refl
  (next {c₁ = activeSampled} refl (next {c₁ = traceCommitted} refl
  (next {c₁ = statusRunning} refl (next refl done)))))
start-trace : traces (Process start) (map label (lifecycle ++ startActions))
start-trace = trace-intro (exec-append lifecycle-path start-path)
no-job-before-fork : advance (igStep (IG.finishProtocol mid 1 clean)) statusRunning ≡ nothing
no-job-before-fork = refl

-- Subsequent batch readiness follows stored freshness and the captured clock.
maturityEvent : IGEvent
maturityEvent = maturedDuplexPeers ((remote key₀ , ident 0) ∷ []) []
m₀ m₁ m₂ m₃ m₄ m₅ : Configuration
m₀ = withIG registered (IG.setPC IG.sampleTime (inboundGovernor registered)) []
eLater : IG.Engine
eLater = record e₄ { lastTime = 910 }
eLaterTimer : IG.Engine
eLaterTimer = record eLater { timers = (ident 0 , ticking) ∷ (ident 1 , ticking) ∷ (ident 2 , ticking) ∷ [] }
m₁ = withIG registered (IG.runtimeState registeredState 2 (IG.armInactivity 910) eLater) []
m₂ = withIG registered (IG.runtimeState registeredState 3 (IG.awaitBatch 910 (ident 2)) eLaterTimer) []
m₃ = withIG registered (IG.runtimeState registeredState 3 (IG.readNext 910 (maturityEvent ∷ [])) eLaterTimer) []
matureState : IG.Published
matureState = IG.publishedStateOf (IG.connections registeredState) [] ((remote key₀ , ident 0) ∷ [])
m₄ = withIG registered (IG.runtimeState registeredState 3 (IG.publishDecision 910 [] matureState) eLaterTimer) []
m₅ = withIG registered (IG.runtimeState matureState 3 (IG.readNext 910 []) eLaterTimer) []
matureActions : List Action
matureActions = igStep IG.finishBatch ∷ igStep (IG.captureTime 910) ∷
  igStep IG.registerInactivity ∷ igStep IG.selectBatch ∷ igStep IG.readEvent ∷ igStep IG.commitDecision ∷ []
mature-path : Executes registered matureActions m₅
mature-path = next {c₁ = m₀} refl (next {c₁ = m₁} refl (next {c₁ = m₂} refl
  (next {c₁ = m₃} refl (next {c₁ = m₄} refl (next refl done)))))
subsequent-batch-trace : traces (Process start) (map label (lifecycle ++ matureActions))
subsequent-batch-trace = trace-intro (exec-append lifecycle-path mature-path)
not-mature-early : IG.maturity 909 registeredState ≡ nothing
not-mature-early = refl
no-truncated-negative-cutoff : IG.maturity 0
  (IG.published [] ((remote key₀ , freshPeer 0 (ident 0)) ∷ [])) ≡ nothing
no-truncated-negative-cutoff = refl

expiredEngine : IG.Engine
expiredEngine = record e₄ { timers = (ident 0 , expired) ∷ (ident 1 , expired) ∷ [] }
-- Deliberately reversed association-list order: source selection uses Ord keys.
ordered-first-expiry : IG.firstCommit expiredEngine
  ((key₁ , IG.registered info (ident 1)) ∷ (key₀ , IG.registered info (ident 1)) ∷ []) ≡ just key₀
ordered-first-expiry = refl
priorityInput priorityEnd : Configuration
priorityInput = withIG registered (IG.runtimeState registeredState 2 (IG.awaitBatch 910 (ident 0)) expiredEngine) (muxFinished key₀ ∷ [])
priorityEnd = withIG registered (IG.runtimeState registeredState 2 (IG.readNext 910 (maturityEvent ∷ muxFinished key₀ ∷ [])) expiredEngine) []
maturity-before-commit-queue-timeout : advance (igStep IG.selectBatch) priorityInput ≡ just priorityEnd
maturity-before-commit-queue-timeout = refl
commitInput commitEnd : Configuration
commitInput = withIG registered (IG.runtimeState registeredState 2 (IG.awaitBatch 10 (ident 0)) expiredEngine) (muxFinished key₀ ∷ [])
commitEnd = withIG registered (IG.runtimeState registeredState 2 (IG.readNext 10 (commitRemote key₀ ∷ muxFinished key₀ ∷ [])) expiredEngine) []
commit-before-queue-timeout : advance (igStep IG.selectBatch) commitInput ≡ just commitEnd
commit-before-queue-timeout = refl

-- A failed second start commits the first command/status, but no registration.
p₂ : Protocol
p₂ = protocol 2 established onDemand
busySecond : M.Mux
busySecond = record newMux { protocols = (1 , M.idle) ∷ (2 , M.demand) ∷ [] }
partial : M.Mux
partial = record busySecond { protocols = (1 , M.demand) ∷ (2 , M.demand) ∷ []; commands = M.startCommand proto ∷ [] }
partial-start-is-not-rollback : M.startBundle (proto ∷ p₂ ∷ []) busySecond
  ≡ M.startFailed 2 M.alreadyRunning partial
partial-start-is-not-rollback = refl
failureEngine : IG.Engine
failureEngine = record e₃ { handles = (ident 0 , M.handleState mid (proto ∷ p₂ ∷ []) duplex) ∷ []; muxes = (mid , busySecond) ∷ [] }
failureInput failedStart stopRequested : Configuration
failureInput = withIG prepared (record (inboundGovernor prepared) { execution = failureEngine }) []
failedStart = withIG prepared (IG.setPC (IG.stopAfterFailure 10 [] mid 2 M.alreadyRunning)
  (IG.setMux mid partial (inboundGovernor failureInput))) []
stopRequested = withIG prepared (IG.setPC (IG.readNext 10 [])
  (IG.setMux mid (record partial { commands = M.startCommand proto ∷ M.shutdown ∷ [] }) (inboundGovernor failureInput))) []
failed-start-path : Executes failureInput (igStep IG.runResponders ∷ igStep IG.requestFailedStop ∷ []) stopRequested
failed-start-path = next {c₁ = failedStart} refl (next refl done)
failed-start-no-registration : IG.connections (IG.publishedState (inboundGovernor failedStart)) ≡ []
failed-start-no-registration = refl
stopped-mux-rejects-start : M.startBundle (proto ∷ []) (record newMux { status = M.stopped })
  ≡ M.startFailed 1 M.shutdownError (record newMux { status = M.stopped })
stopped-mux-rejects-start = refl

-- A clean last-hot completion emits all three messages in the same STM as the
-- counter decrement. At occupancy 98 none can commit; a drain makes room.
endCallback : M.Mux
endCallback = record runningMux { protocols = (1 , M.idle) ∷ []; runningJobs = []; callback = M.commitTrace true (M.completed 1 clean) }
endMessages : List IGEvent
endMessages = miniProtocolTerminated (terminatedProtocol key₀ mid proto duplex clean) ∷
  remoteDemotedToWarm key₀ ∷ waitIdleRemote key₀ ∷ []
blocked drainedWhileBlocked endCommitted : Configuration
blocked = withIG registered (IG.setMux mid endCallback
  (IG.runtimeState registeredState 2 (IG.awaitBatch 10 (ident 0)) e₄)) (replicate 98 (muxFinished key₁))
drainedWhileBlocked = withIG registered (IG.setMux mid endCallback
  (IG.runtimeState registeredState 2 (IG.readNext 10 (replicate 98 (muxFinished key₁))) e₄)) []
endCommitted = withIG registered (IG.setMux mid (record endCallback { traceCounters = just (M.counters (+ 0) (+ 0)); callback = M.returned })
  (IG.runtimeState registeredState 2 (IG.readNext 10 (replicate 98 (muxFinished key₁))) e₄)) endMessages
whole-burst-retries : advance (igStep (IG.commitTracer mid)) blocked ≡ nothing
whole-burst-retries = refl
blocked-monitor-cannot-run : advance (igStep (IG.monitorCommand mid)) blocked ≡ nothing
blocked-monitor-cannot-run = refl
drain-unblocks-path : Executes blocked (igStep IG.selectBatch ∷ igStep (IG.commitTracer mid) ∷ []) endCommitted
drain-unblocks-path = next {c₁ = drainedWhileBlocked} refl (next refl done)
drain-unblocks-trace : traces (Process blocked) (map label (igStep IG.selectBatch ∷ igStep (IG.commitTracer mid) ∷ []))
drain-unblocks-trace = trace-intro drain-unblocks-path
no-partial-burst-trace : ¬ traces (Process blocked) (map label (igStep (IG.commitTracer mid) ∷ []))
no-partial-burst-trace = refused-extension done whole-burst-retries

-- Expired idle blocks a start tracer without changing its counter or queue.
expiredStart : Configuration
expiredStart = withIG activeSampled (record (inboundGovernor activeSampled)
  { execution = record (IG.execution (inboundGovernor activeSampled))
    { timers = (ident 0 , ticking) ∷ (ident 1 , expired) ∷ [] } }) []
expired-idle-blocks : advance (igStep (IG.commitTracer mid)) expiredStart ≡ nothing
expired-idle-blocks = refl

-- Callback active status was sampled before IG exit. The source's separate
-- final flush cannot prevent this already-sampled callback writing afterwards.
exiting flushed afterExitWrite : Configuration
exiting = withIG activeSampled (record (IG.setPC IG.exitFlush (inboundGovernor activeSampled))
  { execution = record (IG.execution (inboundGovernor activeSampled)) { active = false } }) []
flushed = withIG exiting (IG.setPC IG.exited (inboundGovernor exiting)) []
afterExitWrite = withIG flushed (IG.setMux mid
  (record armedMux { commands = []; traceCounters = just (M.counters (+ 1) (+ 0)); callback = M.afterStart 1 })
  (inboundGovernor flushed)) startMessages
sample-survives-exit : Executes activeSampled
  (igStep IG.deactivateIG ∷ igStep IG.flushOnExit ∷ igStep (IG.commitTracer mid) ∷ []) afterExitWrite
sample-survives-exit = next {c₁ = exiting} refl (next {c₁ = flushed} refl (next refl done))

-- Event key lookup captures the currently registered mux. The subsequent wait
-- keeps that identity even if the registration is removed/replaced elsewhere.
waitingForMux : Configuration
waitingForMux = withIG registered (IG.setPC (IG.waitStopped 10 [] key₀ mid registeredState) (inboundGovernor registered)) []
ready-mux-waits : advance (igStep IG.pollStopped) waitingForMux ≡ nothing
ready-mux-waits = refl
stoppedWait waitDone : Configuration
stoppedWait = withIG waitingForMux (IG.setMux mid (record armedMux { status = M.stopped }) (inboundGovernor waitingForMux)) []
waitDone = withIG stoppedWait (IG.setPC (IG.publishDecision 10 [] IG.emptyPublished) (inboundGovernor stoppedWait)) []
stopped-mux-prepares-unregister : advance (igStep IG.pollStopped) stoppedWait ≡ just waitDone
stopped-mux-prepares-unregister = refl

-- Old callback, new registration: use the old counters but capture the CURRENT
-- registration's mux/descriptor. Do not substitute the callback's mux identity.
newInfo : NewConnectionInfo
newInfo = newConnectionInfo inbound key₀ duplex (ident 1)
replacementState : IG.Published
replacementState = IG.published ((key₀ , IG.registered newInfo (ident 1)) ∷ []) []
overlapEngine : IG.Engine
overlapEngine = record e₄
  { handles = (ident 0 , M.handleState mid (proto ∷ []) duplex) ∷
              (ident 1 , M.handleState (ident 1) (proto ∷ []) duplex) ∷ []
  ; muxes = (mid , endCallback) ∷ (ident 1 , newMux) ∷ [] }
overlapConfig : Configuration
overlapConfig = withIG registered (IG.runtimeState replacementState 2 (IG.readNext 10 []) overlapEngine) []
newMuxCaptured : IGEvent
newMuxCaptured = miniProtocolTerminated (terminatedProtocol key₀ (ident 1) proto duplex clean)
overlapDone : Configuration
overlapDone = withIG overlapConfig (IG.setMux mid (record endCallback { traceCounters = just (M.counters (+ 0) (+ 0)); callback = M.returned })
  (inboundGovernor overlapConfig)) (newMuxCaptured ∷ remoteDemotedToWarm key₀ ∷ waitIdleRemote key₀ ∷ [])
old-counter-current-handle : advance (igStep (IG.commitTracer mid)) overlapConfig ≡ just overlapDone
old-counter-current-handle = refl

finishedEventReady currentMuxWait : Configuration
finishedEventReady = withIG overlapConfig (IG.setMux mid (record endCallback { status = M.stopped; callback = M.returned })
  (IG.setPC (IG.readNext 10 (muxFinished key₀ ∷ [])) (inboundGovernor overlapConfig))) []
currentMuxWait = withIG finishedEventReady
  (IG.setPC (IG.waitStopped 10 [] key₀ (ident 1) replacementState) (inboundGovernor finishedEventReady)) []
finished-event-captures-current-mux : advance (igStep IG.readEvent) finishedEventReady ≡ just currentMuxWait
finished-event-captures-current-mux = refl
old-stopped-does-not-unblock-new : advance (igStep IG.pollStopped) currentMuxWait ≡ nothing
old-stopped-does-not-unblock-new = refl

-- An unknown descriptor is an explicit tracer exception, not a stable retry.
missingDescriptorInput missingDescriptorFault : Configuration
missingDescriptorInput = withIG activeSampled
  (IG.setMux mid (record armedMux { callback = M.commitTrace true (M.started 99) }) (inboundGovernor activeSampled)) []
missingDescriptorFault = withIG missingDescriptorInput
  (IG.setMux mid (record armedMux { callback = M.tracerFailed 99 }) (inboundGovernor activeSampled)) []
missing-descriptor-throws : advance (igStep (IG.commitTracer mid)) missingDescriptorInput ≡ just missingDescriptorFault
missing-descriptor-throws = refl

-- Clean worker completion, JobPool result publication, and monitor processing
-- are three distinct boundaries. A new start cannot run before its command.
jobFinished resultPublished resultConsumed : Configuration
jobFinished = withIG jobRunning (IG.setMux mid
  (record runningMux { protocols = (1 , M.idle) ∷ []; runningJobs = []; finishedJobs = (1 , clean) ∷ [] })
  (inboundGovernor jobRunning)) startMessages
resultPublished = withIG jobRunning (IG.setMux mid
  (record runningMux { protocols = (1 , M.idle) ∷ []; runningJobs = []; completions = (1 , clean) ∷ [] })
  (inboundGovernor jobRunning)) startMessages
resultConsumed = withIG jobRunning (IG.setMux mid
  (record runningMux { protocols = (1 , M.idle) ∷ []; runningJobs = []; callback = M.readActive (M.completed 1 clean) })
  (inboundGovernor jobRunning)) startMessages
completion-publication-path : Executes jobRunning
  (igStep (IG.finishProtocol mid 1 clean) ∷ igStep (IG.publishJobResult mid 1) ∷ igStep (IG.monitorCompletion mid) ∷ []) resultConsumed
completion-publication-path = next {c₁ = jobFinished} refl (next {c₁ = resultPublished} refl (next refl done))
no-monitor-result-before-publication : advance (igStep (IG.monitorCompletion mid)) jobFinished ≡ nothing
no-monitor-result-before-publication = refl

-- Signed source counters must not be silently saturated at zero.
signed-underflow-is-preserved : M.decrease hot (M.counters (+ 0) (+ 0))
  ≡ M.counters (-[1+ 0 ]) (+ 0)
signed-underflow-is-preserved = refl
