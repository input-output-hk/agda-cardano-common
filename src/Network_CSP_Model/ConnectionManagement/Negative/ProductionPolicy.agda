{-# OPTIONS --guardedness #-}

-- Conditional production-policy profile controls. Captured faults and delivery
-- are tested separately from the current CM result table and completed shutdown.
-- These injected job/monitor snapshots are not source-reachability witnesses.
module ConnectionManagement.Negative.ProductionPolicy where

open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (put)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.OutboundCases as C
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.ProductionPolicy as Policy
import ConnectionManagement.CSP.GovernorLifecycle as Fixture
import ConnectionManagement.Properties.SubsystemMapUnique as Maps
import ConnectionManagement.Negative.SubsystemMapUnique as MapControls

-- The classifier is the fixed projection of source exception dynamic types for
-- this profile. Error identity 7 is IOManagerError-like; 8 is ordinary IO.
classify : ErrorId → Bool
classify (errorId 7) = true
classify _ = false
module Production = Policy.Profile classify
managerFault ordinaryIO : C.Fault
managerFault = C.ioFailure (errorId 7)
ordinaryIO = C.ioFailure (errorId 8)
job₀ : JobId
job₀ = ident 0
monitor₀ connection₀ : PeerConnectionId
monitor₀ = ident 4
connection₀ = ident 0
caller₀ child₀ : WorkerId
caller₀ = ident 20
child₀ = ident 21
socket₀ : SocketId
socket₀ = ident 20
work : G.Job
work = G.job G.establish Fixture.peerAddr nothing
frameAt : J.PC → J.Frame
frameAt pc = J.frame work caller₀ child₀ socket₀ connection₀ pc
jobAt : J.PC → Sub.JobFrame
jobAt pc = Sub.jobFrame (frameAt pc) false false

-- Model a returned CM fault independently of the fault captured by a job PC.
withReturned : C.Fault → Sub.Configuration → Sub.Configuration
withReturned fault c = record c { world = record (Sub.world c)
  { cm = record (J.cm (Sub.world c))
    { acquired = put caller₀ (C.raised fault) (O.acquired (J.cm (Sub.world c))) } } }
jobConfig : J.PC → C.Fault → Sub.Configuration
jobConfig pc returned = record (withReturned returned Fixture.c3)
  { jobs = (job₀ , jobAt pc) ∷ [] }
monitorConfig : J.PC → C.Fault → Sub.Configuration
monitorConfig pc returned = record (withReturned returned Fixture.c3)
  { monitors = (monitor₀ , frameAt pc) ∷ [] }

-- Every named CM fault is peer-local under the base production policy,
-- irrespective of any subsequently overwritten acquired-table entry.
connection-exists-node-refused : ∀ returned → Production.step
  (Policy.dispatch (Sub.jobStep job₀ J.chooseNodePolicy))
  (Production.initial (jobConfig (J.acquirePolicy C.connectionExists) returned)) ≡ nothing
connection-exists-node-refused returned = refl
forbidden-operation-node-refused : ∀ returned → Production.step
  (Policy.dispatch (Sub.jobStep job₀ J.chooseNodePolicy))
  (Production.initial (jobConfig (J.acquirePolicy C.forbiddenOperation) returned)) ≡ nothing
forbidden-operation-node-refused returned = refl
forbidden-connection-node-refused : ∀ returned → Production.step
  (Policy.dispatch (Sub.jobStep job₀ J.chooseNodePolicy))
  (Production.initial (jobConfig (J.acquirePolicy C.forbiddenConnection) returned)) ≡ nothing
forbidden-connection-node-refused returned = refl
inbound-not-found-node-refused : ∀ returned → Production.step
  (Policy.dispatch (Sub.jobStep job₀ J.chooseNodePolicy))
  (Production.initial (jobConfig (J.acquirePolicy C.inboundNotFound) returned)) ≡ nothing
inbound-not-found-node-refused returned = refl
impossible-state-node-refused : ∀ returned → Production.step
  (Policy.dispatch (Sub.jobStep job₀ J.chooseNodePolicy))
  (Production.initial (jobConfig (J.acquirePolicy C.impossibleState) returned)) ≡ nothing
impossible-state-node-refused returned = refl

-- Ordinary IO selects only ShutdownPeer; the classified manager fault selects
-- only ShutdownNode, despite using the same abstract ioFailure constructor.
ordinary-io-node-refused : Production.step (Policy.dispatch (Sub.jobStep job₀ J.chooseNodePolicy))
  (Production.initial (jobConfig (J.acquirePolicy ordinaryIO) ordinaryIO)) ≡ nothing
ordinary-io-node-refused = refl
ordinary-io-peer-allowed : Production.step (Policy.dispatch (Sub.jobStep job₀ J.choosePeerPolicy))
  (Production.initial (jobConfig (J.acquirePolicy ordinaryIO) ordinaryIO)) ≡
  just (Production.initial (jobConfig (J.complete G.failed) ordinaryIO))
ordinary-io-peer-allowed = refl
manager-peer-refused : Production.step (Policy.dispatch (Sub.jobStep job₀ J.choosePeerPolicy))
  (Production.initial (jobConfig (J.acquirePolicy managerFault) managerFault)) ≡ nothing
manager-peer-refused = refl
manager-node-allowed : Production.step (Policy.dispatch (Sub.jobStep job₀ J.chooseNodePolicy))
  (Production.initial (jobConfig (J.acquirePolicy managerFault) managerFault)) ≡
  just (Production.initial (jobConfig (J.nodeDelivery managerFault) managerFault))
manager-node-allowed = refl

-- collectAcquire freezes the fault. Later overwriting the caller's return table
-- cannot turn an ordinary fault fatal or make a captured fatal fault peer-local.
ordinaryCollected managerCollected : Sub.Configuration
ordinaryCollected = jobConfig (J.acquirePolicy ordinaryIO) ordinaryIO
managerCollected = jobConfig (J.acquirePolicy managerFault) managerFault
ordinary-fault-is-captured : Production.step (Policy.dispatch (Sub.jobStep job₀ J.collectAcquire))
  (Production.initial (jobConfig J.awaitAcquire ordinaryIO)) ≡ just (Production.initial ordinaryCollected)
ordinary-fault-is-captured = refl
manager-fault-is-captured : Production.step (Policy.dispatch (Sub.jobStep job₀ J.collectAcquire))
  (Production.initial (jobConfig J.awaitAcquire managerFault)) ≡ just (Production.initial managerCollected)
manager-fault-is-captured = refl
changedOrdinary changedManager : Sub.Configuration
changedOrdinary = withReturned managerFault ordinaryCollected
changedManager = withReturned C.connectionExists managerCollected
ordinary-capture-ignores-later-fatal-result : Production.step
  (Policy.dispatch (Sub.jobStep job₀ J.chooseNodePolicy)) (Production.initial changedOrdinary) ≡ nothing
ordinary-capture-ignores-later-fatal-result = refl
manager-capture-ignores-later-nonfatal-result : Production.step
  (Policy.dispatch (Sub.jobStep job₀ J.chooseNodePolicy)) (Production.initial changedManager) ≡
  just (Production.initial (jobConfig (J.nodeDelivery managerFault) C.connectionExists))
manager-capture-ignores-later-nonfatal-result = refl

-- Monitor jobs use the same captured-fault policy filter as governor jobs.
monitor-cannot-deliver-nonfatal-policy : Production.step
  (Policy.dispatch (Sub.monitorStep monitor₀ J.chooseNodePolicy))
  (Production.initial (monitorConfig (J.acquirePolicy C.connectionExists) managerFault)) ≡ nothing
monitor-cannot-deliver-nonfatal-policy = refl
monitor-cannot-select-peer-for-manager : Production.step
  (Policy.dispatch (Sub.monitorStep monitor₀ J.choosePeerPolicy))
  (Production.initial (monitorConfig (J.acquirePolicy managerFault) C.connectionExists)) ≡ nothing
monitor-cannot-select-peer-for-manager = refl
monitor-fatal-node-allowed : Production.step
  (Policy.dispatch (Sub.monitorStep monitor₀ J.chooseNodePolicy))
  (Production.initial (monitorConfig (J.acquirePolicy managerFault) C.connectionExists)) ≡
  just (Production.initial (monitorConfig (J.nodeDelivery managerFault) C.connectionExists))
monitor-fatal-node-allowed = refl
monitor-delivery-records-actor-and-capture : Production.step
  (Policy.dispatch (Sub.monitorStep monitor₀ J.deliverNodeException))
  (Production.initial (monitorConfig (J.nodeDelivery managerFault) C.connectionExists)) ≡
  just (Policy.observed (monitorConfig (J.nodeRethrow managerFault) C.connectionExists)
    (Policy.delivered (Policy.monitorDelivery monitor₀ managerFault)))
monitor-delivery-records-actor-and-capture = refl

-- Directly injected nodeDelivery/nodeRethrow PCs do not bypass classification.
nonfatal-direct-delivery-refused : Production.step
  (Policy.dispatch (Sub.jobStep job₀ J.deliverNodeException))
  (Production.initial (jobConfig (J.nodeDelivery C.connectionExists) managerFault)) ≡ nothing
nonfatal-direct-delivery-refused = refl
nonfatal-direct-rethrow-refused : Production.step
  (Policy.dispatch (Sub.monitorStep monitor₀ J.rethrowNodeException))
  (Production.initial (monitorConfig (J.nodeRethrow ordinaryIO) managerFault)) ≡ nothing
nonfatal-direct-rethrow-refused = refl

-- Successful throwTo delivery records the actor/fault but leaves local rethrow
-- pending. It neither completes the job nor instantly stops other subsystem work.
selected nodePending deliveryAcknowledged shutdownComplete : Policy.State
selected = Production.initial changedManager
nodePending = Production.initial (jobConfig (J.nodeDelivery managerFault) C.connectionExists)
deliveryAcknowledged = Policy.observed (jobConfig (J.nodeRethrow managerFault) C.connectionExists)
  (Policy.delivered (Policy.jobDelivery job₀ managerFault))
shutdownComplete = Policy.observed (Policy.machine deliveryAcknowledged)
  (Policy.stopped (Policy.jobDelivery job₀ managerFault))
node-selected : Production.step (Policy.dispatch (Sub.jobStep job₀ J.chooseNodePolicy)) selected ≡ just nodePending
node-selected = refl
node-delivered-before-rethrow : Production.step
  (Policy.dispatch (Sub.jobStep job₀ J.deliverNodeException)) nodePending ≡ just deliveryAcknowledged
node-delivered-before-rethrow = refl
no-shutdown-before-delivery : Production.step Policy.completeShutdown nodePending ≡ nothing
no-shutdown-before-delivery = refl
shutdown-before-local-rethrow : Production.step Policy.completeShutdown deliveryAcknowledged ≡ just shutdownComplete
shutdown-before-local-rethrow = refl

-- External input writes may interleave on either side of acknowledged delivery.
newTargets : G.Targets
newTargets = G.targets 2 1 1
pending-delivery-permits-unrelated-step : Production.step (Policy.dispatch (Sub.setTargets newTargets)) nodePending ≡
  just (Policy.observed (record (Policy.machine nodePending) { targetInput = newTargets }) Policy.live)
pending-delivery-permits-unrelated-step = refl
acknowledged-delivery-permits-unrelated-step : Production.step (Policy.dispatch (Sub.setTargets newTargets)) deliveryAcknowledged ≡
  just (Policy.observed (record (Policy.machine deliveryAcknowledged) { targetInput = newTargets })
    (Policy.delivered (Policy.jobDelivery job₀ managerFault)))
acknowledged-delivery-permits-unrelated-step = refl

-- If supervision has not completed, local rethrow can finish the job and its
-- failed completion can still be published before the explicit shutdown boundary.
locallyRethrown failureQueued : Policy.State
locallyRethrown = Policy.observed (jobConfig (J.complete G.failed) C.connectionExists)
  (Policy.delivered (Policy.jobDelivery job₀ managerFault))
failureQueued = Policy.observed
  (record (jobConfig (J.complete G.failed) C.connectionExists)
    { jobs = (job₀ , Sub.jobFrame (frameAt (J.complete G.failed)) true false) ∷ []
    ; completions = G.completion work G.failed 2 ∷ [] })
  (Policy.delivered (Policy.jobDelivery job₀ managerFault))
local-rethrow-after-delivery : Production.step
  (Policy.dispatch (Sub.jobStep job₀ J.rethrowNodeException)) deliveryAcknowledged ≡ just locallyRethrown
local-rethrow-after-delivery = refl
failed-completion-before-shutdown : Production.step
  (Policy.dispatch (Sub.enqueueCompletion job₀ 2)) locallyRethrown ≡ just failureQueued
failed-completion-before-shutdown = refl

-- Delivery does not yet complete the sender, so no failed completion can be
-- queued until its separate local rethrow step has returned the job result.
completion-before-rethrow-refused : Production.step
  (Policy.dispatch (Sub.enqueueCompletion job₀ 2)) deliveryAcknowledged ≡ nothing
completion-before-rethrow-refused = refl

-- The completed-supervision boundary disables every profile action, including
-- further delivery, local rethrow and a second shutdown-completion attempt.
all-actions-after-shutdown-refused : ∀ a → Production.step a shutdownComplete ≡ nothing
all-actions-after-shutdown-refused a = Production.stopped-step a
  (Policy.machine deliveryAcknowledged) (Policy.jobDelivery job₀ managerFault)
rethrow-after-shutdown-refused : Production.step
  (Policy.dispatch (Sub.jobStep job₀ J.rethrowNodeException)) shutdownComplete ≡ nothing
rethrow-after-shutdown-refused = refl

enqueue-after-shutdown-refused : Production.step
  (Policy.dispatch (Sub.enqueueCompletion job₀ 2)) shutdownComplete ≡ nothing
enqueue-after-shutdown-refused = refl

-- The raw subsystem intentionally keeps abstract policy choice and continued
-- execution. Its semantics are not silently replaced by this concrete profile.
raw-nonfatal-node-choice-remains : Sub.advance (Sub.jobStep job₀ J.chooseNodePolicy)
  (jobConfig (J.acquirePolicy C.connectionExists) C.connectionExists) ≡
  just (jobConfig (J.nodeDelivery C.connectionExists) C.connectionExists)
raw-nonfatal-node-choice-remains = refl
raw-machine-still-has-unrelated-step : Sub.advance (Sub.setTargets newTargets) (Policy.machine shutdownComplete) ≡
  just (record (Policy.machine shutdownComplete) { targetInput = newTargets })
raw-machine-still-has-unrelated-step = refl

-- Finite profile execution projects to real raw steps, erasing only the explicit
-- completed-shutdown stutter. Existing raw safety invariants lift unchanged.
shutdownPath : Production.Executes selected
  (Policy.dispatch (Sub.jobStep job₀ J.chooseNodePolicy) ∷
   Policy.dispatch (Sub.jobStep job₀ J.deliverNodeException) ∷ Policy.completeShutdown ∷ []) shutdownComplete
shutdownPath = Production.next node-selected
  (Production.next node-delivered-before-rethrow (Production.next shutdown-before-local-rethrow Production.done))
shutdown-path-projects : Sub.Executes (Policy.machine selected)
  (Sub.jobStep job₀ J.chooseNodePolicy ∷ Sub.jobStep job₀ J.deliverNodeException ∷ []) (Policy.machine shutdownComplete)
shutdown-path-projects = Production.exec-projects shutdownPath
module MapLift = Production.Lift Maps.Valid Maps.advance-preserves
selected-maps-valid : MapLift.Valid selected
selected-maps-valid = MapControls.initial-unique
shutdown-maps-valid : MapLift.Valid shutdownComplete
shutdown-maps-valid = MapLift.exec-preserves shutdownPath selected-maps-valid
