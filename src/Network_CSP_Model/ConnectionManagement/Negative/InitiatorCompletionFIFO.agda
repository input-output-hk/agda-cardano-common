{-# OPTIONS --guardedness #-}

-- Conditional source-boundary controls: both protocol directions share one
-- JobPool FIFO; actual results and queue publication remain separate steps.
module ConnectionManagement.Negative.InitiatorCompletionFIFO where

open import Data.Bool using (true; false)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.IGTypes
import ConnectionManagement.State as S
import ConnectionManagement.Machine as I
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.PeerActions as P
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.HandlerLifecycle as H
import ConnectionManagement.CSP.IGRegistration as F
import ConnectionManagement.CSP.GovernorLifecycle as Life
open import ConnectionManagement.Scenarios.Admission using (key₀; child₀)

-- Use an existing registration, a hot responder count, and a captured initiator
-- result for the SAME protocol number as the pending responder completion.
initiator : P.Peer
initiator = record (P.initialPeer key₀ (ident 0) (M.handleState F.mid (F.proto ∷ []) duplex))
  { status = P.peerHot
  ; runs = P.protocolRun F.proto (P.returned (errored (errorId 7))) P.running ∷ []
  ; pendingResults = (1 , errored (errorId 7)) ∷ [] }
queuedPeer : P.Peer
queuedPeer = record initiator { pendingResults = [] }

-- Explicit snapshots keep every proof a single local dispatcher step.
at : M.Mux → List IGEvent → P.Peer → Sub.Configuration
at m queue peer = record (Sub.initial (O.initial F.registered) Life.settings)
  { world = J.world (O.initial (record F.registered
    { inboundGovernor = IG.setMux F.mid m (I.inboundGovernor F.registered)
    ; world = record (I.world F.registered) { inboundInfo = queue } }))
    ((ident 0 , peer) ∷ []) }
core : IG.IGAction → Sub.Action
core a = Sub.core (O.inbound (I.igStep a))

pending mixed selected sampled committed failed sampledFailure stopped : M.Mux
pending = record F.newMux
  { traceCounters = just (M.counters (+ 1) (+ 0))
  ; waiting = (1 , onDemand) ∷ []
  ; completions = M.jobResult M.responderJob 1 clean ∷ [] }
mixed = record pending { completions = M.jobResult M.responderJob 1 clean ∷
  M.jobResult M.initiatorJob 1 (errored (errorId 7)) ∷ [] }
selected = record mixed { completions = M.jobResult M.initiatorJob 1 (errored (errorId 7)) ∷ []
  ; callback = M.readActive (M.completed 1 clean) }
sampled = record selected { callback = M.commitTrace true (M.completed 1 clean) }
committed = record sampled { traceCounters = just (M.counters (+ 0) (+ 0)); callback = M.returned }
failed = record committed { completions = []; status = M.failed (errorId 7); callback = M.readActive M.muxStopped }
sampledFailure = record failed { callback = M.commitTrace true M.muxStopped }
stopped = record sampledFailure { traceCounters = nothing; callback = M.returned }

responderEvents : List IGEvent
responderEvents = miniProtocolTerminated (terminatedProtocol key₀ F.mid F.proto duplex clean) ∷
  remoteDemotedToWarm key₀ ∷ waitIdleRemote key₀ ∷ []

-- Publishing the initiator result appends behind the earlier responder result.
publish-behind-responder : Sub.advance (Sub.publishInitiatorResult (ident 0) 0) (at pending [] initiator) ≡
  just (at mixed [] queuedPeer)
publish-behind-responder = refl
no-duplicate-publication : Sub.advance (Sub.publishInitiatorResult (ident 0) 0) (at mixed [] queuedPeer) ≡ nothing
no-duplicate-publication = refl
no-failure-overtaking : Sub.advance (Sub.observeInitiatorFailure (ident 0)) (at mixed [] queuedPeer) ≡ nothing
no-failure-overtaking = refl
no-command-overtaking : Sub.advance (core (IG.monitorCommand F.mid))
  (at (record mixed { commands = M.shutdown ∷ [] }) [] queuedPeer) ≡ nothing
no-command-overtaking = refl
no-demand-overtaking : Sub.advance (core (IG.startOnDemand F.mid 1)) (at mixed [] queuedPeer) ≡ nothing
no-demand-overtaking = refl

-- The earlier clean exit is traced and decrements its counter before the error.
select-responder : Sub.advance (core (IG.monitorCompletion F.mid)) (at mixed [] queuedPeer) ≡ just (at selected [] queuedPeer)
select-responder = refl
no-failure-during-responder-callback : Sub.advance (Sub.observeInitiatorFailure (ident 0)) (at selected [] queuedPeer) ≡ nothing
no-failure-during-responder-callback = refl
sample-responder : Sub.advance (core (IG.sampleTracer F.mid)) (at selected [] queuedPeer) ≡ just (at sampled [] queuedPeer)
sample-responder = refl
commit-responder : Sub.advance (core (IG.commitTracer F.mid)) (at sampled [] queuedPeer) ≡ just (at committed responderEvents queuedPeer)
commit-responder = refl
consume-initiator-error : Sub.advance (Sub.observeInitiatorFailure (ident 0)) (at committed responderEvents queuedPeer) ≡
  just (at failed responderEvents queuedPeer)
consume-initiator-error = refl
sample-initiator-stop : Sub.advance (core (IG.sampleTracer F.mid)) (at failed responderEvents queuedPeer) ≡
  just (at sampledFailure responderEvents queuedPeer)
sample-initiator-stop = refl
commit-initiator-stop : Sub.advance (core (IG.commitTracer F.mid)) (at sampledFailure responderEvents queuedPeer) ≡
  just (at stopped (miniProtocolTerminated (terminatedProtocol key₀ F.mid F.proto duplex clean) ∷
    remoteDemotedToWarm key₀ ∷ waitIdleRemote key₀ ∷ muxFinished key₀ ∷ []) queuedPeer)
commit-initiator-stop = refl

-- Initiator clean exits consume FIFO space but do not fabricate responder
-- termination events, protocol descriptor lookups or counter changes.
clean-initiator-no-responder-trace : Sub.advance (core (IG.monitorCompletion F.mid))
  (at (record pending { completions = M.jobResult M.initiatorJob 99 clean ∷ [] }) [] queuedPeer) ≡
  just (at (record pending { completions = [] }) [] queuedPeer)
clean-initiator-no-responder-trace = refl

-- A tracked pool close permits final job publication, but no monitor selection.
closing : Sub.Configuration → Sub.Configuration
closing c = record c { world = record (Sub.world c)
  { cm = record (J.cm (Sub.world c)) { core = record (O.core (J.cm (Sub.world c)))
    { handlerLifecycles = (child₀ , H.frame F.mid (errorId 0) H.poolClosing) ∷ [] } } } }
closing-can-publish : Sub.advance (Sub.publishInitiatorResult (ident 0) 0) (closing (at pending [] initiator)) ≡
  just (closing (at mixed [] queuedPeer))
closing-can-publish = refl
closing-cannot-observe-error : Sub.advance (Sub.observeInitiatorFailure (ident 0)) (closing (at committed responderEvents queuedPeer)) ≡ nothing
closing-cannot-observe-error = refl
closing-cannot-monitor : Sub.advance (core (IG.monitorCompletion F.mid)) (closing (at mixed [] queuedPeer)) ≡ nothing
closing-cannot-monitor = refl

-- Restart does not erase the captured earlier outcome waiting for publication.
restartedPeer : P.Peer
restartedPeer = record initiator
  { runs = P.protocolRun F.proto P.running (P.returned (errored (errorId 7))) ∷ [] }
restart-retains-pending : P.step (P.startProtocol hot 1) initiator
  (I.inboundGovernor F.registered) (I.world F.registered) ≡ just (restartedPeer , I.inboundGovernor F.registered)
restart-retains-pending = refl
publish-after-restart : Sub.advance (Sub.publishInitiatorResult (ident 0) 0) (at pending [] restartedPeer) ≡
  just (at mixed [] (record restartedPeer { pendingResults = [] }))
publish-after-restart = refl

-- Same-number jobs are selected by pending occurrence, not by protocol key:
-- the later job may return to JobPool first while the older one is preempted.
twoRuns : P.Peer
twoRuns = record restartedPeer { pendingResults = (1 , clean) ∷ (1 , errored (errorId 7)) ∷ [] }
later-run-publishes-first : Sub.advance (Sub.publishInitiatorResult (ident 0) 1) (at (record pending { completions = [] }) [] twoRuns) ≡
  just (at (record pending { completions = M.jobResult M.initiatorJob 1 (errored (errorId 7)) ∷ [] }) []
    (record twoRuns { pendingResults = (1 , clean) ∷ [] }))
later-run-publishes-first = refl
