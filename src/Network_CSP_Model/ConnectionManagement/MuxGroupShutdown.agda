{-# OPTIONS --guardedness #-}

-- Group cancellation/drain and the distinct whole queued-pool bracket close.
-- Source: Mux.hs:554-570, JobPool.hs:105-109,213-225 at the network pin.
-- Body unwind/drain observations are explicit; no buffer, CM finalizer, rethrow
-- or parent Async-result completion is inferred from this local coordinator.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.MuxGroupShutdown (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_; _∨_)
open import Data.Nat using (ℕ)
import Data.Nat as Nat
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (does; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain hiding (job)
open import ConnectionManagement.IGTypes using (clean; errored)
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.MuxResultMonitor as Monitor
module M = Monitor isBearerClosed
import ConnectionManagement.MuxProtocolJobs as ProtocolJobs
module P = ProtocolJobs
module U = P.U
module Startup = P.Startup
module Pool = P.Pool
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O

data Outcome : Set where
  normalExit : Outcome
  failedExit asyncExit : ErrorId → Outcome
data Phase : Set where
  idle shutdownSelected stoppingTraced stoppingWritten groupClosing draining
    drainReady stoppedTrace stoppedTracing monitorReturnedNormal : Phase
  ownerAborting : ErrorId → Phase
  wholeClosing wholeClosed scopeDone : Outcome → Phase
  asyncFailureWritten asyncDeadTracing : ErrorId → Phase
data CancelPC : Set where
  ready : CancelPC
  requested delivered : JobId → CancelPC
record Frame : Set where
  constructor frame
  field phase : Phase
        snapshot remaining joined : List JobId
        cancelPC : CancelPC
open Frame public
initialFrame : Frame
initialFrame = frame idle [] [] [] ready
record State : Set where
  constructor shutdownState
  field base : M.State
        controls : Store WorkerId Frame
open State public
initial : O.Configuration → Maybe State
initial c with M.initial c
... | nothing = nothing
... | just m = just (shutdownState m [])
source : State → O.Configuration
source s = M.source (base s)
setSource : O.Configuration → State → State
setSource c s = record s { base = M.setSource c (base s) }
poolAt : WorkerId → State → Pool.State
poolAt w s = M.poolAt w (base s)
setPool : WorkerId → U.Frame → Pool.State → State → State
setPool w f p s = record s { base = M.setPool w f p (base s) }
protocolState : State → P.State
protocolState s = M.base (base s)
setProtocols : P.State → State → State
setProtocols p s = record s { base = record (base s) { base = p } }
frameAt : WorkerId → State → Frame
frameAt w s with lookup w (controls s)
... | nothing = initialFrame
... | just f = f
setFrame : WorkerId → Frame → State → State
setFrame w f s = record s { controls = put w f (controls s) }
setPhase : WorkerId → Phase → State → State
setPhase w pc s = setFrame w (record (frameAt w s) { phase = pc }) s
ownerContext : WorkerId → State → Maybe (U.Frame × MuxId)
ownerContext w s = M.ownerContext w (base s)
viaSource : IG.IGAction → State → Maybe State
viaSource action s with O.advance (O.inbound (Machine.igStep action)) (source s)
... | nothing = nothing
... | just c = just (setSource c s)
viaPool : WorkerId → Pool.Action → State → Maybe State
viaPool w action s with ownerContext w s
... | nothing = nothing
... | just (f , mid) with Pool.step action (poolAt w s)
...   | nothing = nothing
...   | just p = just (setPool w f p s)

-- Only ordinary named stages use this comparison; error/outcome continuations
-- retain their captured values in the dedicated transition helpers below.
sameStage : Phase → Phase → Bool
sameStage idle idle = true
sameStage shutdownSelected shutdownSelected = true
sameStage stoppingTraced stoppingTraced = true
sameStage stoppingWritten stoppingWritten = true
sameStage groupClosing groupClosing = true
sameStage draining draining = true
sameStage drainReady drainReady = true
sameStage stoppedTrace stoppedTrace = true
sameStage stoppedTracing stoppedTracing = true
sameStage monitorReturnedNormal monitorReturnedNormal = true
sameStage _ _ = false
fromPhase : WorkerId → Phase → Phase → State → Maybe State
fromPhase w before after s with sameStage before (phase (frameAt w s))
... | false = nothing
... | true = just (setPhase w after s)
sourcePhase : WorkerId → Phase → Phase → (MuxId → IG.IGAction) → State → Maybe State
sourcePhase w before after action s with sameStage before (phase (frameAt w s)) | ownerContext w s
... | true | just (f , mid) with viaSource (action mid) s
...   | nothing = nothing
...   | just next = just (setPhase w after next)
sourcePhase w before after action s | _ | _ = nothing

-- Actual caller stop may enqueue before physical startup, during another actor's
-- trace, or after this monitor returned. It is not controller-owned progress.
requestStop : WorkerId → State → Maybe State
requestStop w s with lookup w (U.frames (P.base (protocolState s)))
... | nothing = nothing
... | just f with U.progress f
...   | U.promisePublished hid mid = viaSource (IG.enqueueMuxStop mid) s
...   | _ = nothing
selectStop : WorkerId → State → Maybe State
selectStop w s with phase (frameAt w s) | M.pcAt w (base s) | ownerContext w s
... | idle | M.waiting | just (f , mid) with P.noParent (poolAt w s) | P.noResults (poolAt w s)
...   | true | true with viaSource (IG.takeShutdownCommand mid) s
...     | nothing = nothing
...     | just next = just (setPhase w shutdownSelected next)
selectStop w s | idle | M.waiting | just (f , mid) | _ | _ = nothing
selectStop w s | _ | _ | _ = nothing

-- Read the MiniProtocolJob subset of CURRENT registration, not mutable local
-- activity flags, queued outcomes, or all historical handles. Order is supplied
-- as an exact unique permutation of that map traversal snapshot.
miniMember : WorkerId → JobId → State → Bool
miniMember w j s with lookup j (P.jobs (protocolState s))
... | nothing = false
... | just job = does (w ≟ Types.owner job)
miniEntries : WorkerId → List JobId → State → List JobId
miniEntries w [] s = []
miniEntries w (j ∷ rest) s with miniMember w j s
... | false = miniEntries w rest s
... | true = j ∷ miniEntries w rest s
registeredMini : WorkerId → State → List JobId
registeredMini w s = miniEntries w (Pool.registered (poolAt w s)) s
captureMini : WorkerId → List JobId → State → Maybe State
captureMini w order s with phase (frameAt w s) | Pool.sameSnapshot order (registeredMini w s) | P.noParent (poolAt w s)
... | stoppingWritten | true | true = just (setFrame w (frame groupClosing order order [] ready) s)
... | _ | _ | _ = nothing
requestGroup : WorkerId → State → Maybe State
requestGroup w s with phase (frameAt w s) | cancelPC (frameAt w s) | remaining (frameAt w s)
... | groupClosing | ready | j ∷ rest = just (setFrame w (record (frameAt w s) { cancelPC = requested j }) s)
... | _ | _ | _ = nothing

-- Synchronous jobHandler code is masked. Its captured error cannot be used to
-- invent another ordinary async delivery; normal return/publication may win.
childEligible : JobId → State → Bool
childEligible j s with lookup j (P.jobs (protocolState s))
... | nothing = false
... | just job with Types.phase job
...   | Types.executing = true
...   | Types.waitingEgress = true
...   | Types.resultCaptured clean = true
...   | Types.resultCaptured (errored _) = false
deliverMini : WorkerId → State → Maybe State
deliverMini w s with phase (frameAt w s) | cancelPC (frameAt w s) | remaining (frameAt w s)
... | groupClosing | requested j | current ∷ rest with j ≟ current | miniMember w j s | childEligible j s
...   | yes _ | true | true with viaPool w (Pool.interruptJob j) s
...     | nothing = nothing
...     | just next = just (setFrame w (record (frameAt w next) { cancelPC = delivered j }) next)
deliverMini w s | groupClosing | requested j | current ∷ rest | _ | _ | _ = nothing
deliverMini w s | _ | _ | _ = nothing
joinMiniHead : WorkerId → JobId → State → Maybe State
joinMiniHead w current s with remaining (frameAt w s) | lookup current (Pool.handles (poolAt w s))
... | head ∷ rest | just (Pool.resultAvailable exit) with current ≟ head
...   | yes _ = just (setFrame w (record (frameAt w s)
  { remaining = rest; joined = joined (frameAt w s) ++ (head ∷ []); cancelPC = ready }) s)
...   | no _ = nothing
joinMiniHead w current s | _ | _ = nothing
joinMini : WorkerId → State → Maybe State
joinMini w s with phase (frameAt w s) | cancelPC (frameAt w s)
... | groupClosing | requested j = joinMiniHead w j s
... | groupClosing | delivered j = joinMiniHead w j s
... | _ | _ = nothing
finishMini : WorkerId → State → Maybe State
finishMini w s with phase (frameAt w s) | cancelPC (frameAt w s) | remaining (frameAt w s)
... | groupClosing | ready | [] = just (setPhase w draining s)
... | _ | _ | _ = nothing

-- Resolve actual physical history independently of current map membership.
findOwner : JobId → Store WorkerId U.Frame → Maybe (WorkerId × U.Frame)
findOwner j [] = nothing
findOwner j ((w , f) ∷ rest) with lookup j (Pool.handles (Startup.pool (U.startup f)))
... | nothing = findOwner j rest
... | just _ = just (w , f)
ownerOf : JobId → State → Maybe (WorkerId × U.Frame)
ownerOf j s = findOwner j (U.frames (P.base (protocolState s)))
isInfra : JobId → U.Frame → Bool
isInfra j f with P.infraId Types.muxer (Startup.phase (U.startup f)) | P.infraId Types.demuxer (Startup.phase (U.startup f))
... | just m | just d = does (j ≟ m) ∨ does (j ≟ d)
... | just m | nothing = does (j ≟ m)
... | nothing | just d = does (j ≟ d)
... | nothing | nothing = false

-- This bookkeeping removes a ghost pending occurrence for a clean completion
-- already committed before AsyncCancelled. Idle/result-cell writes stay intact;
-- no JobPool result is fabricated. The source row is matched by physical ID's
-- ordinal plus captured number/outcome, never deleted by protocol number alone.
discardClean : JobId → Types.ProtocolJob → State → Maybe State
discardClean j job s with Types.direction job
... | Mux.initiatorJob = just s
... | Mux.responderJob with P.locate j (P.pendingAt (Types.owner job) (protocolState s)) | P.muxAt (Types.mux job) (protocolState s)
...   | just (index , kept) | just m with IG.takePending index (Mux.finishedJobs m)
...     | just ((n , result) , rest) with does (n Nat.≟ Types.protocolNumber job) ∧ P.sameOutcome clean result
...       | true with viaSource (IG.discardJobOccurrence (Types.mux job) index) s
...         | nothing = nothing
...         | just next = just (setProtocols (record (protocolState next)
  { pending = put (Types.owner job) kept (P.pending (protocolState next)) }) next)
discardClean j job s | Mux.responderJob | just (index , kept) | just m | just ((n , result) , rest) | false = nothing
discardClean j job s | Mux.responderJob | just (index , kept) | just m | nothing = nothing
discardClean j job s | Mux.responderJob | _ | _ = nothing
prepareUnwind : JobId → WorkerId → U.Frame → State → Maybe State
prepareUnwind j w f s with lookup j (P.jobs (protocolState s))
... | nothing with isInfra j f
...   | true = just s
...   | false = nothing
prepareUnwind j w f s | just job with does (w ≟ Types.owner job) | Types.phase job
...   | true | Types.executing = just s
...   | true | Types.waitingEgress = just s
...   | true | Types.resultCaptured clean = discardClean j job s
...   | _ | _ = nothing
unwindChild : JobId → State → Maybe State
unwindChild j s with ownerOf j s
... | nothing = nothing
... | just (w , f) with lookup j (Pool.handles (poolAt w s))
...   | just Pool.bodyUnwinding with prepareUnwind j w f s
...     | nothing = nothing
...     | just next with Pool.step (Pool.bodyUnwound j) (poolAt w next)
...       | nothing = nothing
...       | just p = just (setPool w f p next)
unwindChild j s | just (w , f) | _ = nothing

-- This separate observed replacement boundary models a synchronous exception
-- from body unwind replacing AsyncCancelled. Only an originally uncommitted
-- action can re-enter the real synchronous jobHandler; an error result is not
-- inserted merely because a cancellation was delivered.
replacementEligible : Types.BodyPhase → Bool
replacementEligible Types.executing = true
replacementEligible Types.waitingEgress = true
replacementEligible _ = false
replaceUnwind : JobId → ErrorId → State → Maybe State
replaceUnwind j err s with lookup j (P.jobs (protocolState s))
... | nothing = nothing
... | just job with replacementEligible (Types.phase job) | ownerOf j s
...   | true | just (w , f) with does (w ≟ Types.owner job) | Pool.step (Pool.resumeAfterUnwindError j) (poolAt w s)
...     | true | just p with P.step (P.protocolException j err) (protocolState (setPool w f p s))
...       | nothing = nothing
...       | just next = just (setProtocols next (setPool w f p s))
replaceUnwind j err s | just job | true | just (w , f) | _ | _ = nothing
replaceUnwind j err s | just job | _ | _ = nothing

-- Abort abandons the interruptible group/drain continuation. It neither joins
-- its unfinished cursor nor publishes Failed before the whole bracket closes.
ordinaryAbortStage : Phase → Bool
ordinaryAbortStage shutdownSelected = true
ordinaryAbortStage stoppingTraced = true
ordinaryAbortStage stoppingWritten = true
ordinaryAbortStage groupClosing = true
ordinaryAbortStage draining = true
ordinaryAbortStage drainReady = true
ordinaryAbortStage stoppedTrace = true
ordinaryAbortStage stoppedTracing = true
ordinaryAbortStage _ = false
abortStage : WorkerId → State → Bool
abortStage w s with phase (frameAt w s)
... | idle = M.localWaiting w (base s)
... | pc = ordinaryAbortStage pc
abortMonitor : WorkerId → ErrorId → State → Maybe State
abortMonitor w err s with abortStage w s | ownerContext w s | P.noParent (poolAt w s)
... | true | just (f , mid) | true with P.muxAt mid (protocolState s)
...   | just m with Mux.callback m
...     | Mux.returned = just (setPhase w (ownerAborting err) s)
...     | _ = nothing
abortMonitor w err s | true | just (f , mid) | true | nothing = nothing
abortMonitor w err s | _ | _ | _ = nothing
wholeOutcome : WorkerId → State → Maybe Outcome
wholeOutcome w s with phase (frameAt w s)
... | monitorReturnedNormal = just normalExit
... | ownerAborting err = just (asyncExit err)
... | idle with M.pcAt w (base s)
...   | M.finished M.normal = just normalExit
...   | M.finished (M.failed err) = just (failedExit err)
...   | _ = nothing
wholeOutcome w s | _ = nothing
beginWhole : WorkerId → List JobId → State → Maybe State
beginWhole w order s with wholeOutcome w s
... | nothing = nothing
... | just outcome with viaPool w (Pool.beginClose order) s
...   | nothing = nothing
...   | just next = just (setPhase w (wholeClosing outcome) next)
wholeAction : WorkerId → Pool.Action → State → Maybe State
wholeAction w action s with phase (frameAt w s)
... | wholeClosing outcome = viaPool w action s
... | _ = nothing
wholeDeliverable : WorkerId → JobId → U.Frame → State → Bool
wholeDeliverable w j f s with lookup j (P.jobs (protocolState s))
... | just job = does (w ≟ Types.owner job) ∧ childEligible j s
... | nothing = isInfra j f
deliverWholeChild : WorkerId → State → Maybe State
deliverWholeChild w s with phase (frameAt w s) | ownerContext w s | Pool.phase (poolAt w s)
... | wholeClosing outcome | just (f , mid) | Pool.cancelPending j with wholeDeliverable w j f s
...   | true = viaPool w Pool.deliverCancel s
...   | false = nothing
deliverWholeChild w s | _ | _ | _ = nothing
finishWhole : WorkerId → State → Maybe State
finishWhole w s with phase (frameAt w s)
... | wholeClosing outcome with viaPool w Pool.finishClose s
...   | nothing = nothing
...   | just next = just (setPhase w (wholeClosed outcome) next)
finishWhole w s | _ = nothing

-- Graceful TraceStopped must actually return before the monitor can leave.
-- Active sampling and its queue/counter transaction are separate source steps.
finishStopped : WorkerId → State → Maybe State
finishStopped w s with sameStage stoppedTracing (phase (frameAt w s)) | ownerContext w s
... | true | just (f , mid) with P.muxAt mid (protocolState s)
...   | just m with Mux.status m | Mux.callback m
...     | Mux.stopped | Mux.returned = just (setPhase w monitorReturnedNormal s)
...     | _ | _ = nothing
finishStopped w s | true | just (f , mid) | nothing = nothing
finishStopped w s | _ | _ = nothing

-- Async catch executes only AFTER the actual whole-pool close, overwriting a
-- prior Stopping/Stopped/Failed status before tracing Dead and returning here.
asyncFailure : WorkerId → State → Maybe State
asyncFailure w s with phase (frameAt w s) | Pool.phase (poolAt w s) | ownerContext w s
... | wholeClosed (asyncExit err) | Pool.closedPool | just (f , mid) with viaSource (IG.recordAsyncMuxFailure mid err) s
...   | nothing = nothing
...   | just next = just (setPhase w (asyncFailureWritten err) next)
asyncFailure w s | _ | _ | _ = nothing
asyncDead : WorkerId → State → Maybe State
asyncDead w s with phase (frameAt w s) | ownerContext w s
... | asyncFailureWritten err | just (f , mid) with viaSource (IG.traceMuxDead mid) s
...   | nothing = nothing
...   | just next = just (setPhase w (asyncDeadTracing err) next)
asyncDead w s | _ | _ = nothing
asyncTrace : Bool → WorkerId → State → Maybe State
asyncTrace sample w s with phase (frameAt w s) | ownerContext w s
... | asyncDeadTracing err | just (f , mid) with sample
...   | true = viaSource (IG.sampleTracer mid) s
...   | false = viaSource (IG.commitTracer mid) s
asyncTrace sample w s | _ | _ = nothing
finishAsync : WorkerId → State → Maybe State
finishAsync w s with phase (frameAt w s) | ownerContext w s | Pool.phase (poolAt w s)
... | asyncDeadTracing err | just (f , mid) | Pool.closedPool with P.muxAt mid (protocolState s)
...   | just m with Mux.callback m | M.finishMatches (M.failed err) (Mux.status m)
...     | Mux.returned | true = just (setPhase w (scopeDone (asyncExit err)) s)
...     | _ | _ = nothing
finishAsync w s | asyncDeadTracing err | just (f , mid) | Pool.closedPool | nothing = nothing
finishAsync w s | _ | _ | _ = nothing
finishOrdinary : WorkerId → State → Maybe State
finishOrdinary w s with phase (frameAt w s) | Pool.phase (poolAt w s)
... | wholeClosed normalExit | Pool.closedPool = just (setPhase w (scopeDone normalExit) s)
... | wholeClosed (failedExit err) | Pool.closedPool = just (setPhase w (scopeDone (failedExit err)) s)
... | _ | _ = nothing

-- Guard only this owner's controller. Independent child normal return and
-- publication remain enabled, but an actually interrupted body cannot resume
-- any of its pre-cancellation local/source continuations.
controllerOpen : WorkerId → State → Bool
controllerOpen w s = sameStage idle (phase (frameAt w s))
bodyRunning : JobId → State → Bool
bodyRunning j s with ownerOf j s
... | nothing = false
... | just (w , f) with lookup j (Pool.handles (poolAt w s))
...   | just Pool.bodyRunning = true
...   | _ = false
protocolAllowed : P.Action → State → Bool
protocolAllowed (P.control w _) s = controllerOpen w s
protocolAllowed (P.forkResponder w _ _) s = controllerOpen w s
protocolAllowed (P.forkInitiator w _ _ _) s = controllerOpen w s
protocolAllowed (P.protocolReturned j) s = bodyRunning j s
protocolAllowed (P.commitClean j) s = bodyRunning j s
protocolAllowed (P.protocolException j _) s = bodyRunning j s
protocolAllowed (P.returnProtocol j) s = bodyRunning j s
protocolAllowed (P.run (U.startupStep w _)) s = controllerOpen w s
protocolAllowed _ s = true
delegateAllowed : M.Action → State → Bool
delegateAllowed (M.run action) s = protocolAllowed action s
delegateAllowed (M.consume w) s = controllerOpen w s
delegateAllowed (M.handleSelected w) s = controllerOpen w s
delegateAllowed (M.sampleTracer w) s = controllerOpen w s
delegateAllowed (M.commitTracer w) s = controllerOpen w s
delegateAllowed (M.finishProtocolTrace w) s = controllerOpen w s
delegateAllowed (M.beginDead w) s = controllerOpen w s
delegateAllowed (M.finishDead w) s = controllerOpen w s
inherit : M.Action → State → Maybe State
inherit action s with delegateAllowed action s
... | false = nothing
... | true with M.step action (base s)
...   | nothing = nothing
...   | just next = just (record s { base = next })

data Action : Set where
  run : M.Action → Action
  requestShutdown selectShutdown observeStoppingTrace writeStopping requestGroupCancel deliverGroup
    joinGroup finishGroup drainEmpty timeout2Elapsed writeStopped observeTraceStopped
    sampleStoppedTracer commitStoppedTracer finishStoppedTrace : WorkerId → Action
  captureGroup : WorkerId → List JobId → Action
  finishChildUnwind : JobId → Action
  unwindReplacedBySync : JobId → ErrorId → Action
  abortOwner : WorkerId → ErrorId → Action
  beginWholeClose : WorkerId → List JobId → Action
  requestWholeCancel deliverWhole joinWhole finishWholeClose finishNormalScope writeAsyncFailure
    beginAsyncDead sampleAsyncTracer commitAsyncTracer finishAsyncDead : WorkerId → Action
step : Action → State → Maybe State
step (run action) s = inherit action s
step (requestShutdown w) s = requestStop w s
step (selectShutdown w) s = selectStop w s
step (observeStoppingTrace w) s = fromPhase w shutdownSelected stoppingTraced s
step (writeStopping w) s = sourcePhase w stoppingTraced stoppingWritten IG.recordMuxStopping s
step (captureGroup w order) s = captureMini w order s
step (requestGroupCancel w) s = requestGroup w s
step (deliverGroup w) s = deliverMini w s
step (joinGroup w) s = joinMini w s
step (finishGroup w) s = finishMini w s
step (drainEmpty w) s = fromPhase w draining drainReady s
step (timeout2Elapsed w) s = fromPhase w draining drainReady s
step (writeStopped w) s = sourcePhase w drainReady stoppedTrace IG.completeMuxStopping s
step (observeTraceStopped w) s = sourcePhase w stoppedTrace stoppedTracing IG.traceGracefulMuxStopped s
step (sampleStoppedTracer w) s = sourcePhase w stoppedTracing stoppedTracing IG.sampleTracer s
step (commitStoppedTracer w) s = sourcePhase w stoppedTracing stoppedTracing IG.commitTracer s
step (finishStoppedTrace w) s = finishStopped w s
step (finishChildUnwind j) s = unwindChild j s
step (unwindReplacedBySync j err) s = replaceUnwind j err s
step (abortOwner w err) s = abortMonitor w err s
step (beginWholeClose w order) s = beginWhole w order s
step (requestWholeCancel w) s = wholeAction w Pool.requestCancel s
step (deliverWhole w) s = deliverWholeChild w s
step (joinWhole w) s = wholeAction w Pool.join s
step (finishWholeClose w) s = finishWhole w s
step (finishNormalScope w) s = finishOrdinary w s
step (writeAsyncFailure w) s = asyncFailure w s
step (beginAsyncDead w) s = asyncDead w s
step (sampleAsyncTracer w) s = asyncTrace true w s
step (commitAsyncTracer w) s = asyncTrace false w s
step (finishAsyncDead w) s = finishAsync w s

-- Uninterruptible whole close is separate from the interruptible graceful
-- traversal. Closing certifies only its CURRENT registered snapshot; removed
-- historical handles and unfinished abandoned group cursors are not recaptured.
data Executes : State → List Action → State → Set where
  done : ∀ {s} → Executes s [] s
  next : ∀ {s s₁ s₂ a as} → step a s ≡ just s₁ → Executes s₁ as s₂ → Executes s (a ∷ as) s₂
