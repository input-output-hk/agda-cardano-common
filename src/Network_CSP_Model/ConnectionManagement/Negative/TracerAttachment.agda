{-# OPTIONS --guardedness #-}

-- A2 allocation and callback controls on explicit conditional snapshots.
-- These inspect actual mode-aware steps, not source-reachability of the fixtures.
module ConnectionManagement.Negative.TracerAttachment where

open import Data.Bool using (true; false)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.IGTypes
open import ConnectionManagement.Store using (put)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as I
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.InformationChannel as Channel
import ConnectionManagement.Rules.PeerActions as P
import ConnectionManagement.CSP.Fixtures as Fixture
import ConnectionManagement.CSP.GovernorLifecycle as GovernorFixture
open import ConnectionManagement.Scenarios.Admission using (key₀)

-- A single supported eager protocol makes start/finish continuations explicit.
proto : Protocol
proto = protocol 1 hot eagerly
hid : HandleId
hid = ident 0
mid : MuxId
mid = ident 0
idleTimer : TimerId
idleTimer = ident 1
zeroCounters oneCounter : M.Counters
zeroCounters = M.counters (+ 0) (+ 0)
oneCounter = M.counters (+ 1) (+ 0)
fullQueue : List IGEvent
fullQueue = replicate Channel.capacity (muxFinished key₀)

-- Build the exact allocation outputs, with attachment independent of mutable
-- counters. The direct constructor's final field is the immutable attachment.
newMux : M.TracerAttachment → M.Mux
newMux attachment = M.muxState key₀ M.ready ((1 , M.idle) ∷ []) [] [] [] [] []
  (IG.initialCounters attachment) M.returned attachment
allocated : M.TracerAttachment → DataFlow → IG.Runtime
allocated attachment flow = record IG.initial { execution = record (IG.execution IG.initial)
  { handles = put hid (M.handleState mid (proto ∷ []) flow) (IG.handles (IG.execution IG.initial))
  ; muxes = put mid (newMux attachment) (IG.muxes (IG.execution IG.initial)) } }
outUni outInitiator outDuplex inUni : IG.Runtime
outUni = allocated M.noIGTracer unidirectional
outInitiator = allocated M.noIGTracer duplex
outDuplex = allocated M.igTracer duplex
inUni = allocated M.igTracer unidirectional

-- Outbound attachment needs both responder capability and duplex negotiation.
outbound-unidirectional-no-tracer : IG.step S.responderMode
  (IG.installOutboundHandle hid mid key₀ (proto ∷ []) unidirectional) IG.initial fullQueue ≡ just (outUni , fullQueue)
outbound-unidirectional-no-tracer = refl
outbound-initiator-no-tracer : IG.step S.noResponderMode
  (IG.installOutboundHandle hid mid key₀ (proto ∷ []) duplex) IG.initial fullQueue ≡ just (outInitiator , fullQueue)
outbound-initiator-no-tracer = refl
outbound-duplex-attaches : IG.step S.responderMode
  (IG.installOutboundHandle hid mid key₀ (proto ∷ []) duplex) IG.initial fullQueue ≡ just (outDuplex , fullQueue)
outbound-duplex-attaches = refl
inbound-unidirectional-attaches : IG.step S.responderMode
  (IG.installHandle hid mid key₀ (proto ∷ []) unidirectional) IG.initial fullQueue ≡ just (inUni , fullQueue)
inbound-unidirectional-attaches = refl

-- Both allocation paths retain freshness guards; no mode can overwrite IDs.
reused-handle-refused : IG.step S.responderMode
  (IG.installOutboundHandle hid (ident 2) key₀ (proto ∷ []) duplex) outUni [] ≡ nothing
reused-handle-refused = refl
reused-mux-refused : IG.step S.noResponderMode
  (IG.installOutboundHandle (ident 2) mid key₀ (proto ∷ []) duplex) outInitiator [] ≡ nothing
reused-mux-refused = refl

-- The no-tracer responder-capable engine runs its ordinary start/finish
-- continuations with the IG queue already full, never allocating counters.
plain commanded starting running jobRunning jobFinished resultPublished : M.Mux
plain = newMux M.noIGTracer
commanded = record plain { protocols = (1 , M.running) ∷ []; commands = M.startCommand proto ∷ [] }
starting = record commanded { commands = []; callback = M.afterStart 1 }
running = record starting { callback = M.forkPending 1 }
jobRunning = record running { runningJobs = 1 ∷ []; callback = M.returned }
jobFinished = record plain { finishedJobs = (1 , clean) ∷ [] }
resultPublished = record plain { completions = M.jobResult M.responderJob 1 clean ∷ [] }
start-command-is-enqueued : M.startOne proto plain ≡ M.startedAll commanded
start-command-is-enqueued = refl
absent-start-skips-callback : IG.step S.responderMode (IG.monitorCommand mid)
  (IG.setMux mid commanded outUni) fullQueue ≡ just (IG.setMux mid starting outUni , fullQueue)
absent-start-skips-callback = refl
absent-start-finishes : IG.step S.responderMode (IG.finishStart mid)
  (IG.setMux mid starting outUni) fullQueue ≡ just (IG.setMux mid running outUni , fullQueue)
absent-start-finishes = refl
absent-job-forks : IG.step S.responderMode (IG.forkResponder mid)
  (IG.setMux mid running outUni) fullQueue ≡ just (IG.setMux mid jobRunning outUni , fullQueue)
absent-job-forks = refl
absent-job-finishes : IG.step S.responderMode (IG.finishProtocol mid 1 clean)
  (IG.setMux mid jobRunning outUni) fullQueue ≡ just (IG.setMux mid jobFinished outUni , fullQueue)
absent-job-finishes = refl
absent-result-publishes : IG.step S.responderMode (IG.publishJobResult mid 1)
  (IG.setMux mid jobFinished outUni) fullQueue ≡ just (IG.setMux mid resultPublished outUni , fullQueue)
absent-result-publishes = refl
absent-completion-skips-tracer : IG.step S.responderMode (IG.monitorCompletion mid)
  (IG.setMux mid resultPublished outUni) fullQueue ≡ just (outUni , fullQueue)
absent-completion-skips-tracer = refl

-- Initiator-only protocol starts use the peer-action boundary, not responder
-- fork/start/result APIs. Their mux result still enters the shared FIFO.
initiatorPeer : P.Peer
initiatorPeer = P.initialPeer key₀ hid (M.handleState mid (proto ∷ []) duplex)
worldWithFullQueue : S.State
worldWithFullQueue = record (I.world Fixture.start) { inboundInfo = fullQueue }
initiator-start-uses-peer-action : P.step (P.startProtocol hot 1) initiatorPeer outInitiator worldWithFullQueue ≡
  just (record initiatorPeer { runs = P.protocolRun proto P.running P.notStarted ∷ [] } , outInitiator)
initiator-start-uses-peer-action = refl
initiatorClean initiatorError initiatorFailed : M.Mux
initiatorClean = record plain { completions = M.jobResult M.initiatorJob 1 clean ∷ [] }
initiatorError = record plain { completions = M.jobResult M.initiatorJob 1 (errored (errorId 7)) ∷ [] }
initiatorFailed = record plain { status = M.failed (errorId 7) }
initiator-clean-completion : IG.step S.noResponderMode (IG.monitorCompletion mid)
  (IG.setMux mid initiatorClean outInitiator) fullQueue ≡ just (outInitiator , fullQueue)
initiator-clean-completion = refl
initiator-error-completion : IG.step S.noResponderMode (IG.monitorCompletion mid)
  (IG.setMux mid initiatorError outInitiator) fullQueue ≡ just (IG.setMux mid initiatorFailed outInitiator , fullQueue)
initiator-error-completion = refl

-- Shared command/stop progress in either mode does not write MuxFinished when
-- this mux has no IG tracer, even though the IG channel has no free slot.
shutdown stopping stopped : M.Mux
shutdown = record plain { commands = M.shutdown ∷ [] }
stopping = record plain { status = M.stopping }
stopped = record plain { status = M.stopped }
absent-shutdown-command : IG.step S.responderMode (IG.monitorCommand mid)
  (IG.setMux mid shutdown outUni) fullQueue ≡ just (IG.setMux mid stopping outUni , fullQueue)
absent-shutdown-command = refl
absent-stop-finishes : IG.step S.responderMode (IG.finishStop mid)
  (IG.setMux mid stopping outUni) fullQueue ≡ just (IG.setMux mid stopped outUni , fullQueue)
absent-stop-finishes = refl
initiator-shutdown-command : IG.step S.noResponderMode (IG.monitorCommand mid)
  (IG.setMux mid shutdown outInitiator) fullQueue ≡ just (IG.setMux mid stopping outInitiator , fullQueue)
initiator-shutdown-command = refl
initiator-stop-finishes : IG.step S.noResponderMode (IG.finishStop mid)
  (IG.setMux mid stopping outInitiator) fullQueue ≡ just (IG.setMux mid stopped outInitiator , fullQueue)
initiator-stop-finishes = refl

-- A registered attached mux has ordinary transactional tracer behavior.
register : DataFlow → IG.Runtime → IG.Runtime
register flow r = record r
  { publishedState = IG.published ((key₀ , IG.registered (newConnectionInfo inbound key₀ flow hid) idleTimer) ∷ []) []
  ; execution = record (IG.execution r) { timers = (idleTimer , ticking) ∷ [] } }
attachedStart attachedStarted : M.Mux
attachedStart = record (newMux M.igTracer) { callback = M.commitTrace true (M.started 1) }
attachedStarted = record (newMux M.igTracer) { traceCounters = just oneCounter; callback = M.afterStart 1 }
duplex-tracer-full-retries : IG.step S.responderMode (IG.commitTracer mid)
  (IG.setMux mid attachedStart (register duplex outDuplex)) fullQueue ≡ nothing
duplex-tracer-full-retries = refl
duplex-tracer-commits : IG.step S.responderMode (IG.commitTracer mid)
  (IG.setMux mid attachedStart (register duplex outDuplex)) [] ≡
  just (IG.setMux mid attachedStarted (register duplex outDuplex) , awakeRemote key₀ ∷ remotePromotedToHot key₀ ∷ [])
duplex-tracer-commits = refl
inbound-unidirectional-still-traces : IG.step S.responderMode (IG.commitTracer mid)
  (IG.setMux mid attachedStart (register unidirectional inUni)) [] ≡
  just (IG.setMux mid attachedStarted (register unidirectional inUni) , awakeRemote key₀ ∷ remotePromotedToHot key₀ ∷ [])
inbound-unidirectional-still-traces = refl

-- Attachment remains when counters were cleared. In particular an attached
-- stopped mux still emits MuxFinished; counter absence is not tracer absence.
clearedStop clearedDone absentStop : M.Mux
clearedStop = record (newMux M.igTracer) { status = M.stopped; traceCounters = nothing; callback = M.commitTrace true M.muxStopped }
clearedDone = record clearedStop { callback = M.returned }
absentStop = record stopped { callback = M.commitTrace true M.muxStopped }
cleared-attached-emits-finished : IG.step S.responderMode (IG.commitTracer mid)
  (IG.setMux mid clearedStop outDuplex) [] ≡ just (IG.setMux mid clearedDone outDuplex , muxFinished key₀ ∷ [])
cleared-attached-emits-finished = refl
cleared-attached-full-retries : IG.step S.responderMode (IG.commitTracer mid)
  (IG.setMux mid clearedStop outDuplex) fullQueue ≡ nothing
cleared-attached-full-retries = refl
absent-stop-never-emits-finished : IG.step S.noResponderMode (IG.commitTracer mid)
  (IG.setMux mid absentStop outInitiator) fullQueue ≡ just (IG.setMux mid stopped outInitiator , fullQueue)
absent-stop-never-emits-finished = refl

-- Handcrafted callbacks cannot make an absent tracer consult active/readiness
-- or descriptor state. The paired attached snapshots expose each distinction.
withExpiredTimer : IG.Runtime → IG.Runtime
withExpiredTimer r = record r { execution = record (IG.execution r) { timers = (idleTimer , expired) ∷ [] } }
inactive : IG.Runtime → IG.Runtime
inactive r = record r { execution = record (IG.execution r) { active = false } }
noSample yesSample noSampleDone yesSampleDone : M.Mux
noSample = record plain { traceCounters = just oneCounter; callback = M.readActive (M.started 99) }
yesSample = record noSample { tracerAttachment = M.igTracer }
noSampleDone = record noSample { callback = M.afterStart 99 }
yesSampleDone = record yesSample { callback = M.commitTrace false (M.started 99) }
absent-sample-skips-active : IG.step S.responderMode (IG.sampleTracer mid)
  (IG.setMux mid noSample (inactive (register unidirectional outUni))) fullQueue ≡
  just (IG.setMux mid noSampleDone (inactive (register unidirectional outUni)) , fullQueue)
absent-sample-skips-active = refl
attached-sample-reads-active : IG.step S.responderMode (IG.sampleTracer mid)
  (IG.setMux mid yesSample (inactive (register duplex outDuplex))) fullQueue ≡
  just (IG.setMux mid yesSampleDone (inactive (register duplex outDuplex)) , fullQueue)
attached-sample-reads-active = refl
noExpired yesExpired noExpiredDone : M.Mux
noExpired = record plain { traceCounters = just zeroCounters; callback = M.commitTrace true (M.started 99) }
yesExpired = record noExpired { tracerAttachment = M.igTracer }
noExpiredDone = record noExpired { callback = M.afterStart 99 }
absent-commit-skips-readiness : IG.step S.responderMode (IG.commitTracer mid)
  (IG.setMux mid noExpired (withExpiredTimer (register unidirectional outUni))) fullQueue ≡
  just (IG.setMux mid noExpiredDone (withExpiredTimer (register unidirectional outUni)) , fullQueue)
absent-commit-skips-readiness = refl
attached-commit-checks-readiness : IG.step S.responderMode (IG.commitTracer mid)
  (IG.setMux mid yesExpired (withExpiredTimer (register duplex outDuplex))) fullQueue ≡ nothing
attached-commit-checks-readiness = refl
noDescriptor yesDescriptor noDescriptorDone yesDescriptorFault : M.Mux
noDescriptor = record plain { traceCounters = just oneCounter; callback = M.commitTrace true (M.started 99) }
yesDescriptor = record noDescriptor { tracerAttachment = M.igTracer }
noDescriptorDone = record noDescriptor { callback = M.afterStart 99 }
yesDescriptorFault = record yesDescriptor { callback = M.tracerFailed 99 }
absent-commit-skips-descriptor : IG.step S.responderMode (IG.commitTracer mid)
  (IG.setMux mid noDescriptor (register unidirectional outUni)) fullQueue ≡
  just (IG.setMux mid noDescriptorDone (register unidirectional outUni) , fullQueue)
absent-commit-skips-descriptor = refl
attached-commit-checks-descriptor : IG.step S.responderMode (IG.commitTracer mid)
  (IG.setMux mid yesDescriptor (register duplex outDuplex)) fullQueue ≡
  just (IG.setMux mid yesDescriptorFault (register duplex outDuplex) , fullQueue)
attached-commit-checks-descriptor = refl

-- Initiator-only mode does not gain an IG governor or responder job API.
batchReady : IG.Runtime
batchReady = IG.setPC (IG.awaitBatch 0 idleTimer) (register duplex outInitiator)
responder-batch-is-enabled : IG.step S.responderMode IG.selectBatch batchReady fullQueue ≡
  just (IG.setPC (IG.readNext 0 fullQueue) batchReady , [])
responder-batch-is-enabled = refl
no-responder-batch-refused : IG.step S.noResponderMode IG.selectBatch batchReady fullQueue ≡ nothing
no-responder-batch-refused = refl
no-responder-registration-refused : IG.step S.noResponderMode
  (IG.installHandle (ident 2) (ident 2) key₀ (proto ∷ []) duplex) outInitiator [] ≡ nothing
no-responder-registration-refused = refl
no-responder-timer-refused : IG.step S.noResponderMode (IG.expireTimer idleTimer) (register duplex outInitiator) [] ≡ nothing
no-responder-timer-refused = refl
no-responder-fork-refused : IG.step S.noResponderMode (IG.forkResponder mid)
  (IG.setMux mid running outInitiator) fullQueue ≡ nothing
no-responder-fork-refused = refl
no-responder-job-result-refused : IG.step S.noResponderMode (IG.publishJobResult mid 1)
  (IG.setMux mid jobFinished outInitiator) fullQueue ≡ nothing
no-responder-job-result-refused = refl

-- Shared engine access is also direction-sensitive: initiator-only mode cannot
-- consume a fabricated responder command or the responder head of the FIFO.
no-responder-start-command-refused : IG.step S.noResponderMode (IG.monitorCommand mid)
  (IG.setMux mid commanded outInitiator) fullQueue ≡ nothing
no-responder-start-command-refused = refl
no-responder-completion-head-refused : IG.step S.noResponderMode (IG.monitorCompletion mid)
  (IG.setMux mid resultPublished outInitiator) fullQueue ≡ nothing
no-responder-completion-head-refused = refl


-- The unchanged inbound alias uses the same freshness checks.
inbound-reused-handle-refused : IG.step S.responderMode
  (IG.installHandle hid (ident 2) key₀ (proto ∷ []) unidirectional) inUni [] ≡ nothing
inbound-reused-handle-refused = refl
inbound-reused-mux-refused : IG.step S.responderMode
  (IG.installHandle (ident 2) mid key₀ (proto ∷ []) unidirectional) inUni [] ≡ nothing
inbound-reused-mux-refused = refl


-- Check mode-aware dispatch as well as the raw engine. These conditional
-- snapshots carry the full queue through the real Machine/Subsystem layers.
initiatorMachine : I.Configuration
initiatorMachine = I.initial S.noResponderMode worldWithFullQueue
machine-outbound-allocation : I.advance
  (I.igStep (IG.installOutboundHandle hid mid key₀ (proto ∷ []) duplex)) initiatorMachine ≡
  just (record initiatorMachine { inboundGovernor = outInitiator })
machine-outbound-allocation = refl

failureMachine failedMachine : I.Configuration
failureMachine = record initiatorMachine { inboundGovernor = IG.setMux mid initiatorError outInitiator }
failedMachine = record initiatorMachine { inboundGovernor = IG.setMux mid initiatorFailed outInitiator }
initiatorSubsystem failedSubsystem : Sub.Configuration
initiatorSubsystem = Sub.initial (O.initial failureMachine) GovernorFixture.settings
failedSubsystem = Sub.initial (O.initial failedMachine) GovernorFixture.settings
subsystem-initiator-error-with-full-queue : Sub.advance
  (Sub.core (O.inbound (I.igStep (IG.monitorCompletion mid)))) initiatorSubsystem ≡ just failedSubsystem
subsystem-initiator-error-with-full-queue = refl
