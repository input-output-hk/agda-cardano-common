{-# OPTIONS --guardedness #-}

-- IG batches, registration and synchronous mux tracer integration at network
-- 96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d. Caller-run CM calls use the dispatcher.
module ConnectionManagement.Rules.IGRegistration where

open import Class.DecEq.Instances using (DecEq-ℕ)
open import Data.Integer using (+_; -[1+_])
open import Data.Nat using (ℕ; zero; suc; _+_; _≤?_; _<?_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import ConnectionManagement.ConnectionOrder public using (lexLess; addressCode; keyLess)
open import ConnectionManagement.Domain
open import ConnectionManagement.State using (ResponderMode; responderMode; noResponderMode)
open import ConnectionManagement.IGTypes public
open import ConnectionManagement.Store using (Store; lookup; put; delete)
import ConnectionManagement.Rules.IGBatch as Batch
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.TracerReadiness as Readiness

-- The default constructor retains the initial RemoteIdle projection.
data RemoteState : Set where
  remoteIdle : TimerId → RemoteState
  remoteCold remoteWarm remoteHot : RemoteState
record Registration : Set where
  constructor registration
  field notification : NewConnectionInfo
        remoteState : RemoteState
open Registration public
registered : NewConnectionInfo → TimerId → Registration
registered info t = registration info (remoteIdle t)

record Published : Set where
  constructor publishedStateOf
  field connections : Store ConnectionKey Registration
        freshPeers : Store PeerAddr FreshPeer
        maturePeers : Store PeerAddr HandleId
open Published public
published : Store ConnectionKey Registration → Store PeerAddr FreshPeer → Published
published cs fs = publishedStateOf cs fs []
emptyPublished : Published
emptyPublished = published [] []

data PC : Set where
  sampleTime exitFlush exited inCM : PC
  armInactivity : ℕ → PC
  awaitBatch : ℕ → TimerId → PC
  readNext : ℕ → List IGEvent → PC
  prepareNew : ℕ → NewConnectionInfo → List IGEvent → Published → PC
  startResponders : ℕ → NewConnectionInfo → List IGEvent → Published → TimerId → PC
  publishDecision : ℕ → List IGEvent → Published → PC
  stopAfterFailure : ℕ → List IGEvent → MuxId → ℕ → M.StartError → PC
  waitStopped : ℕ → List IGEvent → ConnectionKey → MuxId → Published → PC
  restartResponder : ℕ → List IGEvent → Terminated → PC
  awaitRemoteIdle : ℕ → ConnectionKey → List IGEvent → Published → PC
  needsCM : ℕ → List IGEvent → IGEvent → Published → PC

record Engine : Set where
  constructor engine
  field handles : Store HandleId M.Handle
        muxes : Store MuxId M.Mux
        timers : Store TimerId TimeoutFlag
        active : Bool
        lastTime : ℕ
open Engine public
emptyEngine : Engine
emptyEngine = engine [] [] [] true 0
record Runtime : Set where
  constructor runtimeState
  field publishedState : Published
        nextTimer : ℕ
        continuation : PC
        execution : Engine
open Runtime public
runtime : Published → ℕ → PC → Runtime
runtime old n pc = runtimeState old n pc emptyEngine
initial : Runtime
initial = runtime emptyPublished 0 sampleTime

data IGAction : Set where
  captureTime : ℕ → IGAction
  registerInactivity selectBatch readEvent registerIdleTimer runResponders
    commitDecision requestFailedStop finishBatch pollStopped restart
    deactivateIG flushOnExit : IGAction
  expireTimer : TimerId → IGAction
  -- Handler allocation and monitor/job progress remain explicit boundaries.
  installHandle installOutboundHandle : HandleId → MuxId → ConnectionKey → List Protocol → DataFlow → IGAction
  monitorCommand monitorCompletion sampleTracer commitTracer finishStart forkResponder finishStop : MuxId → IGAction
  startOnDemand : MuxId → ℕ → IGAction
  publishJobResult : MuxId → ℕ → IGAction
  publishJobOccurrence : MuxId → ℕ → IGAction
  recordMuxFailure : MuxId → ErrorId → IGAction
  recordMuxStopped traceMuxDead takeShutdownCommand recordMuxStopping completeMuxStopping enqueueMuxStop : MuxId → IGAction
  discardJobOccurrence : MuxId → ℕ → IGAction
  recordAsyncMuxFailure : MuxId → ErrorId → IGAction
  finishProtocol : MuxId → ℕ → RunResult → IGAction

Result = Runtime × List IGEvent

setPC : PC → Runtime → Runtime
setPC pc r = record r { continuation = pc }
setMux : MuxId → M.Mux → Runtime → Runtime
setMux mid m r = record r { execution = record (execution r) { muxes = put mid m (muxes (execution r)) } }

addFresh : ℕ → NewConnectionInfo → Published → Store PeerAddr FreshPeer
addFresh time info old with negotiatedFlow info
... | unidirectional = freshPeers old
... | duplex = put (remote (connectionKey info)) (freshPeer time (negotiatedHandle info)) (freshPeers old)

expiredTimer : TimerId → Engine → Bool
expiredTimer t e with lookup t (timers e)
... | just expired = true
... | _ = false

minimumKey : ConnectionKey → Maybe ConnectionKey → Maybe ConnectionKey
minimumKey k nothing = just k
minimumKey k (just other) with keyLess k other
... | true = just k
... | false = just other
firstCommit : Engine → Store ConnectionKey Registration → Maybe ConnectionKey
firstCommit e [] = nothing
firstCommit e ((k , reg) ∷ rest) with remoteState reg
... | remoteIdle t with expiredTimer t e
...   | true = minimumKey k (firstCommit e rest)
...   | false = firstCommit e rest
firstCommit e ((k , reg) ∷ rest) | _ = firstCommit e rest

-- The source threshold is 15 minutes. Natural timestamps represent seconds;
-- addition avoids truncating a negative cutoff to zero before time 900.
partitionMature : ℕ → Store PeerAddr FreshPeer → Store PeerAddr HandleId × Store PeerAddr FreshPeer
partitionMature time [] = [] , []
partitionMature time ((peer , f) ∷ fs) with partitionMature time fs | observedAt f + 900 ≤? time
... | matured , fresh | yes _ = (peer , versionFromHandle f) ∷ matured , fresh
... | matured , fresh | no _ = matured , (peer , f) ∷ fresh
maturity : ℕ → Published → Maybe IGEvent
maturity time old with partitionMature time (freshPeers old)
... | [] , _ = nothing
... | ms@(_ ∷ _) , fs = just (maturedDuplexPeers ms fs)
commitCandidate : Engine → Published → Maybe IGEvent
commitCandidate e old with firstCommit e (connections old)
... | nothing = nothing
... | just k = just (commitRemote k)
mergeMature : Store PeerAddr HandleId → Store PeerAddr HandleId → Store PeerAddr HandleId
mergeMature [] old = old
mergeMature ((k , h) ∷ xs) old = put k h (mergeMature xs old)

-- A handle provides the actual protocol bundle and mux reference. Missing
-- handles are malformed/unfinished setup, not a modeled source STM retry.
tracerView : ConnectionKey → Runtime → Maybe M.View
tracerView k r with lookup k (connections (publishedState r))
... | nothing = nothing
... | just reg with lookup (negotiatedHandle (notification reg)) (handles (execution r))
...   | nothing = nothing
...   | just h = just (M.view (M.muxRef h) (M.bundle h) (M.versionFlow h) (idleIsExpired (remoteState reg)))
  where
  idleIsExpired : RemoteState → Bool
  idleIsExpired (remoteIdle t) = expiredTimer t (execution r)
  idleIsExpired _ = false

-- Map.fromList/foldM visits protocol numbers in ascending order. Require a
-- strictly ordered bundle at the allocation boundary, rather than silently
-- choosing a different fold order or accepting duplicate protocol numbers.
orderedAfter : ℕ → List Protocol → Bool
orderedAfter n [] = true
orderedAfter n (p ∷ ps) with n <? number p
... | yes _ = orderedAfter (number p) ps
... | no _ = false
ordered : List Protocol → Bool
ordered [] = true
ordered (p ∷ ps) = orderedAfter (number p) ps

-- Selected execution profile supports independent on-demand and eager starts.
-- Grouped StartOnDemandAny scheduling requires a separate monitor continuation.
supported : List Protocol → Bool
supported [] = true
supported (p ∷ ps) with startMode p
... | onDemandAny = false
... | _ = supported ps

allocateTimer : PC → Runtime → Runtime
allocateTimer pc r = record r { nextTimer = suc (nextTimer r); continuation = pc
  ; execution = record (execution r) { timers = put (ident (nextTimer r)) ticking (timers (execution r)) } }

-- Current-state updates use the event's captured snapshot, as in loop decisions.
setRemote : ConnectionKey → RemoteState → Published → Published
setRemote k st old with lookup k (connections old)
... | nothing = old
... | just reg = record old { connections = put k (record reg { remoteState = st }) (connections old) }
unregister : ConnectionKey → Published → Published
unregister k old = record old { connections = delete k (connections old)
  ; freshPeers = delete (remote k) (freshPeers old); maturePeers = delete (remote k) (maturePeers old) }

readOne : ℕ → IGEvent → List IGEvent → Runtime → Runtime
readOne time (newConnection info) rest r with lookup (connectionKey info) (connections (publishedState r))
... | nothing = setPC (prepareNew time info rest (publishedState r)) r
... | just _ = setPC (publishDecision time rest (publishedState r)) r
readOne time (maturedDuplexPeers ms fs) rest r = setPC (publishDecision time rest
  (record (publishedState r) { freshPeers = fs; maturePeers = mergeMature ms (maturePeers (publishedState r)) })) r
readOne time inactivityTimeout rest r = setPC (readNext time rest) r
readOne time (remotePromotedToHot k) rest r = setPC (publishDecision time rest (setRemote k remoteHot (publishedState r))) r
readOne time (remoteDemotedToWarm k) rest r = setPC (publishDecision time rest (setRemote k remoteWarm (publishedState r))) r
readOne time (muxFinished k) rest r with lookup k (connections (publishedState r))
... | nothing = setPC (readNext time rest) r
... | just reg with lookup (negotiatedHandle (notification reg)) (handles (execution r))
...   | nothing = setPC (needsCM time rest (muxFinished k) (publishedState r)) r
...   | just h = setPC (waitStopped time rest k (M.muxRef h) (publishedState r)) r
readOne time (miniProtocolTerminated t) rest r with result t
... | errored _ = setPC (readNext time rest) r
... | clean with lookup (peer t) (connections (publishedState r))
...   | nothing = setPC (readNext time rest) r
...   | just _ = setPC (restartResponder time rest t) r
readOne time event rest r = setPC (needsCM time rest event (publishedState r)) r

-- Post-callback monitor continuations cannot run while the callback is blocked.
afterTrace : M.Trace → M.Callback
afterTrace (M.started n) = M.afterStart n
afterTrace (M.completed n clean) = M.returned
afterTrace (M.completed n (errored _)) = M.afterFailure
afterTrace M.muxStopped = M.returned

-- Inbound handlers always attach the IG tracer. Outbound handlers attach it
-- only when a responder-capable node negotiates duplex flow.
outboundTracer : ResponderMode → DataFlow → M.TracerAttachment
outboundTracer noResponderMode _ = M.noIGTracer
outboundTracer responderMode unidirectional = M.noIGTracer
outboundTracer responderMode duplex = M.igTracer

-- A missing tracer skips its entire callback, preserving monitor continuations.
traceCallback : M.Mux → M.Trace → M.Callback
traceCallback m tr with M.tracerAttachment m
... | M.noIGTracer = afterTrace tr
... | M.igTracer = M.readActive tr

-- Counters can later be cleared without changing attachment.
initialCounters : M.TracerAttachment → Maybe M.Counters
initialCounters M.noIGTracer = nothing
initialCounters M.igTracer = just (M.counters (+ 0) (+ 0))

-- Allocation retains the original freshness and protocol-bundle guards.
installWith : M.TracerAttachment → HandleId → MuxId → ConnectionKey → List Protocol → DataFlow →
  Runtime → List IGEvent → Maybe Result
installWith attachment hid mid k ps flow r queue
  with lookup hid (handles (execution r)) | lookup mid (muxes (execution r)) | ordered ps | supported ps
... | nothing | nothing | true | true = just (record r { execution = record (execution r)
      { handles = put hid (M.handleState mid ps flow) (handles (execution r))
      ; muxes = put mid (M.muxState k M.ready (map (λ p → number p , M.idle) ps) [] [] [] [] []
          (initialCounters attachment) M.returned attachment) (muxes (execution r)) } } , queue)
... | _ | _ | _ | _ = nothing

hasJob : ℕ → List ℕ → Bool
hasJob n [] = false
hasJob n (other ∷ rest) with n Data.Nat.≟ other
... | yes _ = true
... | no _ = hasJob n rest
removeJob : ℕ → List ℕ → List ℕ
removeJob n [] = []
removeJob n (other ∷ rest) with n Data.Nat.≟ other
... | yes _ = rest
... | no _ = other ∷ removeJob n rest

-- Map.! in the source tracer throws for an absent descriptor. Report this
-- explicitly instead of turning an exception into an apparent queue retry.
missingDescriptor : M.Trace → Maybe M.View → Maybe M.Counters → Maybe ℕ
missingDescriptor _ _ nothing = nothing
missingDescriptor _ nothing _ = nothing
missingDescriptor M.muxStopped _ _ = nothing
missingDescriptor (M.started n) (just v) (just rc) with M.findProtocol n (M.registeredBundle v)
... | nothing = just n
... | just _ = nothing
missingDescriptor (M.completed n _) (just v) (just rc) with M.findProtocol n (M.registeredBundle v)
... | nothing = just n
... | just _ = nothing

-- Remove exactly the indexed pending occurrence; protocol numbers may repeat.
takePending : ℕ → List (ℕ × RunResult) → Maybe ((ℕ × RunResult) × List (ℕ × RunResult))
takePending i [] = nothing
takePending zero (result ∷ rest) = just (result , rest)
takePending (suc i) (result ∷ rest) with takePending i rest
... | nothing = nothing
... | just (chosen , retained) = just (chosen , result ∷ retained)

stepWorker : IGAction → Runtime → List IGEvent → Maybe Result
-- IG exit is an environment exception/scope-exit boundary, not a free normal
-- loop decision. Source catch handler deactivates and then flushes in separate STMs.
stepWorker deactivateIG r queue with active (execution r)
... | false = nothing
... | true = just (record (setPC exitFlush r) { execution = record (execution r) { active = false } } , queue)
stepWorker flushOnExit r queue with continuation r
... | exitFlush = just (setPC exited r , [])
... | _ = nothing
stepWorker (captureTime time) r queue with continuation r
... | sampleTime with lastTime (execution r) ≤? time
...   | no _ = nothing
...   | yes _ = just (record (setPC (armInactivity time) r)
      { execution = record (execution r) { lastTime = time } } , queue)
stepWorker (captureTime time) r queue | _ = nothing
stepWorker registerInactivity r queue with continuation r
... | armInactivity time = just (allocateTimer (awaitBatch time (ident (nextTimer r))) r , queue)
... | _ = nothing
stepWorker selectBatch r queue with continuation r
... | awaitBatch time t with Batch.selectBatch (maturity time (publishedState r))
      (commitCandidate (execution r) (publishedState r)) (expiredTimer t (execution r)) inactivityTimeout queue
...   | nothing = nothing
...   | just chosen = just (setPC (readNext time (Batch.batch chosen)) r , Batch.remaining chosen)
stepWorker selectBatch r queue | _ = nothing
stepWorker readEvent r queue with continuation r
... | readNext time (ev ∷ rest) = just (readOne time ev rest r , queue)
... | _ = nothing
stepWorker registerIdleTimer r queue with continuation r
... | awaitRemoteIdle time k rest captured = just (allocateTimer
      (publishDecision time rest (setRemote k (remoteIdle (ident (nextTimer r))) captured)) r , queue)
... | prepareNew time info rest captured = just (allocateTimer
      (startResponders time info rest captured (ident (nextTimer r))) r , queue)
... | _ = nothing
stepWorker runResponders r queue with continuation r
... | startResponders time info rest captured t with lookup (negotiatedHandle info) (handles (execution r))
...   | nothing = nothing
...   | just h with lookup (M.muxRef h) (muxes (execution r))
...     | nothing = nothing
...     | just m with M.startBundle (M.bundle h) m
...       | M.startedAll updated = just (record (setMux (M.muxRef h) updated r)
          { publishedState = record captured
              { connections = put (connectionKey info) (registered info t) (connections captured)
              ; freshPeers = addFresh time info captured }
          ; continuation = readNext time rest } , queue)
...       | M.startFailed n err updated = just
          (setPC (stopAfterFailure time rest (M.muxRef h) n err) (setMux (M.muxRef h) updated r) , queue)
stepWorker runResponders r queue | _ = nothing
stepWorker commitDecision r queue with continuation r
... | publishDecision time rest captured = just (record r { publishedState = captured; continuation = readNext time rest } , queue)
... | _ = nothing
stepWorker requestFailedStop r queue with continuation r
... | stopAfterFailure time rest mid n err with lookup mid (muxes (execution r))
...   | nothing = nothing
...   | just m = just (setPC (readNext time rest)
        (setMux mid (record m { commands = M.commands m ++ (M.shutdown ∷ []) }) r) , queue)
stepWorker requestFailedStop r queue | _ = nothing
stepWorker finishBatch r queue with continuation r
... | readNext time [] = just (setPC sampleTime r , queue)
... | _ = nothing
stepWorker pollStopped r queue with continuation r
... | waitStopped time rest k mid captured with lookup mid (muxes (execution r))
...   | nothing = nothing
...   | just m with M.status m
...     | M.stopped = just (setPC (publishDecision time rest (unregister k captured)) r , queue)
...     | M.failed _ = just (setPC (publishDecision time rest (unregister k captured)) r , queue)
...     | _ = nothing
stepWorker pollStopped r queue | _ = nothing
stepWorker restart r queue with continuation r
... | restartResponder time rest t with lookup (capturedMux t) (muxes (execution r))
...   | nothing = nothing
...   | just m with M.startOne (descriptor t) m
...     | M.startedAll updated = just (setPC (readNext time rest) (setMux (capturedMux t) updated r) , queue)
...     | M.startFailed n err updated = just (setPC (stopAfterFailure time rest (capturedMux t) n err)
          (setMux (capturedMux t) updated r) , queue)
stepWorker restart r queue | _ = nothing
stepWorker (expireTimer t) r queue with lookup t (timers (execution r))
... | just ticking = just (record r { execution = record (execution r)
      { timers = put t expired (timers (execution r)) } } , queue)
... | _ = nothing
stepWorker (installHandle hid mid k ps flow) r queue = installWith M.igTracer hid mid k ps flow r queue
stepWorker (installOutboundHandle hid mid k ps flow) r queue =
  installWith (outboundTracer responderMode flow) hid mid k ps flow r queue
stepWorker (sampleTracer mid) r queue with lookup mid (muxes (execution r))
... | nothing = nothing
... | just m with M.tracerAttachment m | M.callback m
...   | M.noIGTracer | M.readActive tr = just (setMux mid (record m { callback = afterTrace tr }) r , queue)
...   | M.igTracer | M.readActive tr = just (setMux mid (record m { callback = M.commitTrace (active (execution r)) tr }) r , queue)
...   | _ | _ = nothing
stepWorker (commitTracer mid) r queue with lookup mid (muxes (execution r))
... | nothing = nothing
... | just m with M.tracerAttachment m | M.callback m
...   | M.noIGTracer | M.commitTrace flag tr = just (setMux mid (record m { callback = afterTrace tr }) r , queue)
...   | M.igTracer | M.commitTrace false tr = just (setMux mid (record m { callback = afterTrace tr }) r , queue)
...   | M.igTracer | M.commitTrace true tr with Readiness.prefixReady (M.key m) tr (tracerView (M.key m) r) (M.traceCounters m) queue
...     | false = nothing
...     | true with missingDescriptor tr (tracerView (M.key m) r) (M.traceCounters m)
...       | just n = just (setMux mid (record m { callback = M.tracerFailed n }) r , queue)
...       | nothing with M.traceSTM (M.key m) tr (tracerView (M.key m) r) (M.traceCounters m) queue
...         | nothing = nothing
...         | just (rc , q) = just (setMux mid (record m { traceCounters = rc; callback = afterTrace tr }) r , q)
stepWorker (commitTracer mid) r queue | just m | _ | _ = nothing
stepWorker (finishStart mid) r queue with lookup mid (muxes (execution r))
... | nothing = nothing
... | just m with M.callback m
...   | M.afterStart n = just (setMux mid (record m { protocols = put n M.running (M.protocols m); callback = M.forkPending n }) r , queue)
...   | _ = nothing
-- Job launch follows the on-demand status transaction. No completed job is
-- admitted solely because runMiniProtocolSTM has set an eager status Running.
stepWorker (forkResponder mid) r queue with lookup mid (muxes (execution r))
... | nothing = nothing
... | just m with M.callback m
...   | M.forkPending n = just (setMux mid (record m { runningJobs = n ∷ M.runningJobs m; callback = M.returned }) r , queue)
...   | _ = nothing
stepWorker (monitorCommand mid) r queue with lookup mid (muxes (execution r))
... | nothing = nothing
... | just m with M.callback m | M.status m | M.completions m | M.commands m
...   | M.returned | M.ready | [] | M.startCommand p ∷ rest with startMode p
...     | eagerly = just (setMux mid (record m { commands = rest; callback = traceCallback m (M.started (number p)) }) r , queue)
...     | mode = just (setMux mid (record m { commands = rest; waiting = put (number p) mode (M.waiting m) }) r , queue)
stepWorker (monitorCommand mid) r queue | just m | M.returned | M.ready | [] | M.shutdown ∷ rest =
  just (setMux mid (record m { commands = rest; status = M.stopping }) r , queue)
stepWorker (monitorCommand mid) r queue | just m | M.afterFailure | _ | _ | _ =
  just (setMux mid (record m { callback = traceCallback m M.muxStopped }) r , queue)
stepWorker (monitorCommand mid) r queue | just m | _ | _ | _ | _ = nothing
-- One FIFO contains both initiator and responder job results. Initiator
-- traces do not produce responder termination/counter events in the IG tracer.
stepWorker (monitorCompletion mid) r queue with lookup mid (muxes (execution r))
... | nothing = nothing
... | just m with M.callback m | M.status m | M.completions m
...   | M.returned | M.ready | M.jobResult M.responderJob n outcome ∷ rest with outcome
...     | clean = just (setMux mid (record m { completions = rest; callback = traceCallback m (M.completed n outcome) }) r , queue)
...     | errored err = just (setMux mid (record m { completions = rest; status = M.failed err; callback = traceCallback m (M.completed n outcome) }) r , queue)
stepWorker (monitorCompletion mid) r queue | just m | M.returned | M.ready | M.jobResult M.initiatorJob n outcome ∷ rest with outcome
... | clean = just (setMux mid (record m { completions = rest }) r , queue)
... | errored err = just (setMux mid (record m { completions = rest; status = M.failed err; callback = traceCallback m M.muxStopped }) r , queue)
stepWorker (monitorCompletion mid) r queue | just m | _ | _ | _ = nothing
-- A selected channel has traffic. Ordered selection among simultaneously ready
-- channels is outside this boundary; fixtures supply one traffic-ready channel.
stepWorker (startOnDemand mid n) r queue with lookup mid (muxes (execution r))
... | nothing = nothing
... | just m with M.callback m | M.status m | M.commands m | M.completions m | lookup n (M.waiting m)
...   | M.returned | M.ready | [] | [] | just onDemand = just (setMux mid
      (record m { waiting = delete n (M.waiting m); callback = traceCallback m (M.started n) }) r , queue)
...   | _ | _ | _ | _ | _ = nothing
-- A job can finish while a different callback blocks the monitor. Clean exit
-- includes the source egress-drained boundary; exceptional exit does not reset
-- the protocol status. Completion delivery is separate from this job outcome.
stepWorker (finishProtocol mid n outcome) r queue with lookup mid (muxes (execution r))
... | nothing = nothing
... | just m with lookup n (M.protocols m) | hasJob n (M.runningJobs m)
...   | just M.running | true with outcome
...     | clean = just (setMux mid (record m { protocols = put n M.idle (M.protocols m); runningJobs = removeJob n (M.runningJobs m); finishedJobs = M.finishedJobs m ++ ((n , outcome) ∷ []) }) r , queue)
...     | errored _ = just (setMux mid (record m { runningJobs = removeJob n (M.runningJobs m); finishedJobs = M.finishedJobs m ++ ((n , outcome) ∷ []) }) r , queue)
stepWorker (finishProtocol mid n outcome) r queue | just m | _ | _ = nothing
-- JobPool result publication follows jobAction/jobHandler return. It is not
-- fused with the protocol's completion/status transaction.
stepWorker (publishJobResult mid n) r queue with lookup mid (muxes (execution r))
... | nothing = nothing
... | just m with lookup n (M.finishedJobs m)
...   | nothing = nothing
...   | just outcome = just (setMux mid (record m
      { finishedJobs = delete n (M.finishedJobs m)
      ; completions = M.completions m ++ (M.jobResult M.responderJob n outcome ∷ []) }) r , queue)
-- Select a physical publication occurrence, preserving other runs of the same
-- protocol. JobPool publishes the particular returning job, not the oldest run
-- with that protocol number (JobPool.hs:156-164 at the source pin).
stepWorker (publishJobOccurrence mid i) r queue with lookup mid (muxes (execution r))
... | nothing = nothing
... | just m with takePending i (M.finishedJobs m)
...   | nothing = nothing
...   | just ((n , outcome) , retained) = just (setMux mid (record m
      { finishedJobs = retained
      ; completions = M.completions m ++ (M.jobResult M.responderJob n outcome ∷ []) }) r , queue)
-- Source monitor writes status before the Dead tracer (Mux.hs:460-488).
-- Typed adapters capture/consume their physical result separately.
stepWorker (recordMuxFailure mid err) r queue with lookup mid (muxes (execution r))
... | nothing = nothing
... | just m with M.status m | M.callback m
...   | M.ready | M.returned = just (setMux mid (record m { status = M.failed err }) r , queue)
...   | _ | _ = nothing
stepWorker (recordMuxStopped mid) r queue with lookup mid (muxes (execution r))
... | nothing = nothing
... | just m with M.status m | M.callback m
...   | M.ready | M.returned = just (setMux mid (record m { status = M.stopped }) r , queue)
...   | _ | _ = nothing
stepWorker (traceMuxDead mid) r queue with lookup mid (muxes (execution r))
... | nothing = nothing
... | just m with M.status m | M.callback m
...   | M.stopped | M.returned = just (setMux mid (record m { callback = traceCallback m M.muxStopped }) r , queue)
...   | M.failed err | M.returned = just (setMux mid (record m { callback = traceCallback m M.muxStopped }) r , queue)
...   | _ | _ = nothing
-- External Mux.stop merely enqueues CmdShutdown (Mux.hs:178-180), even when
-- the monitor is held or no physical startup has happened. It is not a monitor
-- access: HandlerLifecycle.muxAction deliberately leaves it unclassified.
stepWorker (enqueueMuxStop mid) r queue with lookup mid (muxes (execution r))
... | nothing = nothing
... | just m = just (setMux mid (record m { commands = M.commands m ++ (M.shutdown ∷ []) }) r , queue)
-- CmdShutdown is selected before TraceStopping and the status write
-- (Mux.hs:555-558). Its trace is ignored by the IG tracer.
stepWorker (takeShutdownCommand mid) r queue with lookup mid (muxes (execution r))
... | nothing = nothing
... | just m with M.status m | M.callback m | M.completions m | M.commands m
...   | M.ready | M.returned | [] | M.shutdown ∷ rest = just (setMux mid (record m { commands = rest }) r , queue)
...   | _ | _ | _ | _ = nothing
stepWorker (recordMuxStopping mid) r queue with lookup mid (muxes (execution r))
... | nothing = nothing
... | just m with M.status m | M.callback m
...   | M.ready | M.returned = just (setMux mid (record m { status = M.stopping }) r , queue)
...   | _ | _ = nothing
-- Graceful group/drain completion is distinct from the demuxer's ready→Stopped
-- decision. TraceStopped follows separately and is ignored by the IG tracer.
stepWorker (completeMuxStopping mid) r queue with lookup mid (muxes (execution r))
... | nothing = nothing
... | just m with M.status m | M.callback m
...   | M.stopping | M.returned = just (setMux mid (record m { status = M.stopped }) r , queue)
...   | _ | _ = nothing
-- Remove cancelled pending metadata only. Async cancellation produces no
-- JobPool error result; an adapter must establish that cancellation happened.
stepWorker (discardJobOccurrence mid i) r queue with lookup mid (muxes (execution r))
... | nothing = nothing
... | just m with takePending i (M.finishedJobs m)
...   | nothing = nothing
...   | just (chosen , retained) = just (setMux mid (record m { finishedJobs = retained }) r , queue)
-- The source async catch runs after the whole pool scope has unwound
-- (Mux.hs:275-278). That ordering is an adapter obligation, not this helper.
stepWorker (recordAsyncMuxFailure mid err) r queue with lookup mid (muxes (execution r))
... | nothing = nothing
... | just m with M.callback m
...   | M.returned = just (setMux mid (record m { status = M.failed err }) r , queue)
...   | _ = nothing
-- Completion of cancelGroup/egress drain is still an environment boundary.
stepWorker (finishStop mid) r queue with lookup mid (muxes (execution r))
... | nothing = nothing
... | just m with M.status m | M.callback m
...   | M.stopping | M.returned = just (setMux mid (record m { status = M.stopped; runningJobs = []; callback = traceCallback m M.muxStopped }) r , queue)
...   | _ | _ = nothing

-- Mux execution exists without an IG governor. Only these engine actions are
-- admitted in initiator-only mode; batch/registration/timer actions stay absent.
runtimeAction : IGAction → Bool
runtimeAction (monitorCommand _) = true
runtimeAction (monitorCompletion _) = true
runtimeAction (sampleTracer _) = true
runtimeAction (commitTracer _) = true
runtimeAction (finishStop _) = true
runtimeAction (recordMuxFailure _ _) = true
runtimeAction (recordMuxStopped _) = true
runtimeAction (traceMuxDead _) = true
runtimeAction (enqueueMuxStop _) = true
runtimeAction (takeShutdownCommand _) = true
runtimeAction (recordMuxStopping _) = true
runtimeAction (completeMuxStopping _) = true
runtimeAction (discardJobOccurrence _ _) = true
runtimeAction (recordAsyncMuxFailure _ _) = true
runtimeAction _ = false

-- In initiator-only mode, the shared monitor may consume initiator results
-- and shutdown, but cannot create or consume responder work from injected state.
runtimeAllowed : IGAction → Runtime → Bool
runtimeAllowed (monitorCommand mid) r with lookup mid (muxes (execution r))
... | nothing = false
... | just m with M.callback m
...   | M.afterFailure = true
...   | M.returned with M.commands m
...     | M.shutdown ∷ _ = true
...     | _ = false
runtimeAllowed (monitorCommand mid) r | just m | _ = false
runtimeAllowed (monitorCompletion mid) r with lookup mid (muxes (execution r))
... | nothing = false
... | just m with M.completions m
...   | M.jobResult M.initiatorJob _ _ ∷ _ = true
...   | _ = false
runtimeAllowed a r = runtimeAction a

step : ResponderMode → IGAction → Runtime → List IGEvent → Maybe Result
step noResponderMode (installOutboundHandle hid mid k ps flow) ig queue =
  installWith M.noIGTracer hid mid k ps flow ig queue
step noResponderMode a ig queue with runtimeAllowed a ig
... | true = stepWorker a ig queue
... | false = nothing
step responderMode a ig queue = stepWorker a ig queue
