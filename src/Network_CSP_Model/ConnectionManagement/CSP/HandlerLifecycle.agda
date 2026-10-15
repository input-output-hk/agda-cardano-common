{-# OPTIONS --guardedness #-}

-- Derived async-cancellation path after opt-in attachment. Pool joins and buffer
-- unwind are environment completion inputs, not proofs of source progress.
module ConnectionManagement.CSP.HandlerLifecycle where

open import Data.Product using (_,_)
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; map; replicate)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Machine
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence
open import ConnectionManagement.CSP.Hiding
open import ConnectionManagement.CSP.InboundRelease using (after)
import ConnectionManagement.CSP.InboundRelease as Release
import ConnectionManagement.CSP.RemoteState as Remote
open import ConnectionManagement.CSP.IGRuntime using (runningMux)
import ConnectionManagement.Rules.Pruning as Prune
open import ConnectionManagement.CSP.IGRegistration using (lifecycle; lifecycle-path; mid; registeredState; armedMux; registered; e₃)
open import ConnectionManagement.CSP.Fixtures using (start; binding; childLease)
open import ConnectionManagement.Scenarios.Admission using (key₀; child₀)
import ConnectionManagement.Rules.HandlerLifecycle as Life
import ConnectionManagement.Rules.InboundRelease as R
import ConnectionManagement.Rules.RemoteState as RS
import ConnectionManagement.Rules.Cleanup as C
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.IGRegistration as IG
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

cancelError : ErrorId
cancelError = errorId 7
-- Anchor snapshots at the imported caller state; avoid repeated normalization
-- of long chains of `after` through the mux and lifecycle records.
tracked : Life.Phase → Configuration → Configuration
tracked phase c = record c { handlerLifecycles = (child₀ , Life.frame mid cancelError phase) ∷ [] }
withMux : Life.Phase → M.Mux → Configuration → Configuration
withMux phase m c = tracked phase (record c { inboundGovernor = IG.setMux mid m (inboundGovernor c) })
withQueue : List IGEvent → Configuration → Configuration
withQueue q c = record c { world = record (world c) { inboundInfo = q } }
failedMux sampledMux tracedMux : M.Mux
failedMux = record armedMux { status = M.failed cancelError ; callback = M.readActive M.muxStopped }
sampledMux = record failedMux { callback = M.commitTrace true M.muxStopped }
tracedMux = record failedMux { callback = M.returned ; traceCounters = nothing }
attached received joined failed sampled traced exited cleanupEntered : Configuration
attached = tracked Life.monitoring Release.requested
received = tracked Life.poolClosing Release.delivered
joined = tracked Life.poolClosed Release.delivered
failed = withMux Life.deadTracing failedMux Release.delivered
sampled = withMux Life.deadTracing sampledMux Release.delivered
traced = withQueue (muxFinished key₀ ∷ []) (withMux Life.deadTracing tracedMux Release.delivered)
exited = tracked Life.bodyExited traced
cleanupEntered = tracked Life.finalizing (record traced
  { world = record (world traced) { cleanups = (child₀ , cleanupAcquire) ∷ [] } })

unwindActions : List Action
unwindActions = handlerStep child₀ (Life.attach cancelError) ∷
  releaseStep (R.cancellationDelivered child₀) ∷ handlerStep child₀ Life.jobPoolClosed ∷
  handlerStep child₀ Life.publishAsyncFailure ∷ igStep (IG.sampleTracer mid) ∷
  igStep (IG.commitTracer mid) ∷ handlerStep child₀ Life.finishRethrow ∷ handlerExit child₀ ∷ []
unwind-path : Executes Release.requested unwindActions cleanupEntered
unwind-path = next {c₁ = attached} refl (next {c₁ = received} refl (next {c₁ = joined} refl
  (next {c₁ = failed} refl (next {c₁ = sampled} refl (next {c₁ = traced} refl
  (next {c₁ = exited} refl (next refl done)))))))
unwind-hidden : traces (HiddenProcess Release.requested) (map label (project unwindActions))
unwind-hidden = hidden-trace unwind-path

requestActions : List Action
requestActions = releaseStep R.transact ∷ releaseStep R.readCounters ∷ releaseStep R.requestCancellation ∷ []
request-path : Executes Release.b₆ requestActions Release.requested
request-path = next {c₁ = Release.written} refl (next {c₁ = Release.counted} refl (next refl done))
composed-unwind-trace : traces (Process start)
  (map label (lifecycle ++ (Release.batchActions ++ (requestActions ++ unwindActions))))
composed-unwind-trace = trace-intro (exec-append lifecycle-path
  (exec-append Release.batch-path (exec-append request-path unwind-path)))

handlerPhase : Configuration → Maybe Life.Phase
handlerPhase c with lookup child₀ (handlerLifecycles c)
... | nothing = nothing
... | just f = just (Life.phase f)
muxStatus : Configuration → Maybe M.Status
muxStatus c with lookup mid (IG.muxes (IG.execution (inboundGovernor c)))
... | nothing = nothing
... | just m = just (M.status m)
receipt-enters-pool-close : handlerPhase received ≡ just Life.poolClosing
receipt-enters-pool-close = refl
receipt-does-not-fail-mux : muxStatus received ≡ just M.ready
receipt-does-not-fail-mux = refl
receipt-does-not-start-cleanup : cleanups (world received) ≡ []
receipt-does-not-start-cleanup = refl
no-cleanup-before-unwind : advance (handlerExit child₀) received ≡ nothing
no-cleanup-before-unwind = refl
no-failure-before-join : advance (handlerStep child₀ Life.publishAsyncFailure) received ≡ nothing
no-failure-before-join = refl
no-old-monitor-after-delivery : advance (igStep (IG.monitorCommand mid)) received ≡ nothing
no-old-monitor-after-delivery = refl
joined-still-not-failed : muxStatus joined ≡ just M.ready
joined-still-not-failed = refl
failure-status : muxStatus failed ≡ just (M.failed cancelError)
failure-status = refl
status-before-dead-event : inboundInfo (world failed) ≡ []
status-before-dead-event = refl
dead-event-published : inboundInfo (world traced) ≡ muxFinished key₀ ∷ []
dead-event-published = refl
no-rethrow-before-tracer : advance (handlerStep child₀ Life.finishRethrow) sampled ≡ nothing
no-rethrow-before-tracer = refl
no-premature-cleanup-trace : ¬ traces (Process sampled) (map label (handlerExit child₀ ∷ []))
no-premature-cleanup-trace = refused-extension done refl

-- The release sender can return without waiting for pool joins or CM cleanup.
callerChecked callerReturned callerPublished : Configuration
callerChecked = tracked Life.poolClosing Release.checked
callerReturned = tracked Life.poolClosing Release.returned
callerPublished = tracked Life.poolClosing Release.published
caller-path : Executes received
  (releaseStep R.checkAssertion ∷ releaseStep R.returnToIG ∷ igStep IG.commitDecision ∷ []) callerPublished
caller-path = next {c₁ = callerChecked} refl (next {c₁ = callerReturned} refl (next refl done))
caller-return-does-not-join : handlerPhase callerPublished ≡ just Life.poolClosing
caller-return-does-not-join = refl

-- Async catch tracing can block after Failed is visible but before finally.
queueFull : Configuration
queueFull = record sampled { world = record (world sampled) { inboundInfo = replicate 100 inactivityTimeout } }
full-queue-blocks-dead-trace : advance (igStep (IG.commitTracer mid)) queueFull ≡ nothing
full-queue-blocks-dead-trace = refl
blocked-tracer-prevents-cleanup : advance (handlerExit child₀) queueFull ≡ nothing
blocked-tracer-prevents-cleanup = refl

-- Existing CM finalizer now follows the derived exit. Terminating retains its
-- binding through socket close and map publication, then waits for TIME_WAIT.
cleanupSnapshot : Configuration → ConnectionState → MapCell → SocketOwner → CleanupPC → Configuration
cleanupSnapshot cfg st cell owner pc = record cfg { world = record (world cfg)
  { cm = record (cm (world cfg)) { mapCell = cell ; entries = put (ident 0) st (entries (cm (world cfg))) }
  ; sockets = put (ident 0) owner (sockets (world cfg))
  ; cleanups = put child₀ pc (cleanups (world cfg)) } }
term : ConnectionState
term = terminating key₀ child₀ nothing
mapTaken selected socketClosed waiting ready finalized doneCleanup : Configuration
mapTaken = cleanupSnapshot cleanupEntered term (taken child₀) (handling child₀) (cleanupSelect childLease)
selected = cleanupSnapshot cleanupEntered term (taken child₀) (handling child₀) (cleanupClose childLease binding (timeWait term))
socketClosed = cleanupSnapshot cleanupEntered term (taken child₀) closed (cleanupPublish childLease binding (timeWait term))
waiting = cleanupSnapshot cleanupEntered term (full binding) closed (cleanupWaiting term)
ready = cleanupSnapshot cleanupEntered term (full binding) closed (cleanupFinalize term cleanupNormal)
finalized = cleanupSnapshot cleanupEntered (terminated nothing) (full []) closed (cleanupCount cleanupNormal)
doneCleanup = cleanupSnapshot cleanupEntered (terminated nothing) (full []) closed (cleanupDone cleanupNormal)
cleanupActions : List Action
cleanupActions = cleanupStep child₀ C.takeCleanupMap ∷ cleanupStep child₀ C.selectCleanupEntry ∷
  cleanupStep child₀ C.closeHandlerSocket ∷ cleanupStep child₀ C.publishCleanupMap ∷
  cleanupStep child₀ C.timeWaitElapsed ∷ cleanupStep child₀ C.finishTimeWait ∷
  cleanupStep child₀ C.readCleanupCounters ∷ []
cleanup-path : Executes cleanupEntered cleanupActions doneCleanup
cleanup-path = next {c₁ = mapTaken} refl (next {c₁ = selected} refl
  (next {c₁ = socketClosed} refl (next {c₁ = waiting} refl (next {c₁ = ready} refl
  (next {c₁ = finalized} refl (next refl done))))))
unwind-and-cleanup-trace : traces (Process Release.requested) (map label (unwindActions ++ cleanupActions))
unwind-and-cleanup-trace = trace-intro (exec-append unwind-path cleanup-path)
wait-state : lookup child₀ (cleanups (world waiting)) ≡ just (cleanupWaiting term)
wait-state = refl
cleanup-finished : lookup child₀ (cleanups (world doneCleanup)) ≡ just (cleanupDone cleanupNormal)
cleanup-finished = refl

-- A local self-pruning fixture exercises the same unwind with a running job.
-- This is conditional on the existing fixture, not a source reachability claim.
selfVictim : Prune.Candidate
selfVictim = Prune.candidate key₀ (ident 0) child₀ 5 true
setRemotePC : RS.PC → Configuration → Configuration
setRemotePC pc c = record c { remoteCall = Maybe.map (λ f → record f { pc = pc }) (remoteCall c) }
pAttached pChecked pRequested pDelivered pJoined pFailed pSampled pTraced pExited pCleanup : Configuration
-- Materialize the imported replay once, instead of expanding it in each step.
pBaseline : Configuration
pBaseline = record registered
  { world = record (world registered) { cm = record (cm (world registered))
      { entries = (ident 0 , terminated nothing) ∷ [] } }
  ; inboundGovernor = IG.runtimeState registeredState 3 IG.inCM
      (record e₃ { lastTime = 11 ; timers = (ident 0 , ticking) ∷ (ident 1 , ticking) ∷ (ident 2 , ticking) ∷ []
                 ; muxes = (mid , runningMux) ∷ [] })
  ; remoteCall = just (RS.frame RS.promote key₀ 11 (remotePromotedToHot key₀ ∷ []) registeredState RS.assertion
      (RS.success (outboundDup key₀ child₀ (ident 0) expired)) false (selfVictim ∷ []))
  ; promotionHardLimit = 0 ; pruningGeneration = 1 }
pBaseline-exact : Remote.p₁ ≡ pBaseline
pBaseline-exact = refl
pAttached = tracked Life.monitoring pBaseline
pChecked = setRemotePC (RS.cancellationNext (selfVictim ∷ [])) pAttached
pRequested = setRemotePC (RS.awaitDelivery selfVictim []) pChecked
pDelivered = tracked Life.poolClosing (setRemotePC (RS.cancellationNext []) pChecked)
pJoined = withMux Life.poolClosed (record runningMux { runningJobs = [] ; waiting = [] }) pDelivered
pFailed = withMux Life.deadTracing (record runningMux { runningJobs = [] ; waiting = [] ;
  status = M.failed cancelError ; callback = M.readActive M.muxStopped }) pDelivered
pSampled = withMux Life.deadTracing (record runningMux { runningJobs = [] ; waiting = [] ;
  status = M.failed cancelError ; callback = M.commitTrace true M.muxStopped }) pDelivered
pTraced = withQueue (muxFinished key₀ ∷ []) (withMux Life.deadTracing
  (record runningMux { runningJobs = [] ; waiting = [] ; status = M.failed cancelError ;
    callback = M.returned ; traceCounters = nothing }) pDelivered)
pExited = tracked Life.bodyExited pTraced
pCleanup = tracked Life.finalizing (record pTraced
  { world = record (world pTraced) { cleanups = (child₀ , cleanupAcquire) ∷ [] } })
prunedUnwindActions : List Action
prunedUnwindActions = handlerStep child₀ (Life.attach cancelError) ∷ remoteStep RS.checkAssertion ∷
  remoteStep RS.requestPruneCancellation ∷ remoteStep (RS.pruneCancellationDelivered child₀) ∷
  handlerStep child₀ Life.jobPoolClosed ∷ handlerStep child₀ Life.publishAsyncFailure ∷
  igStep (IG.sampleTracer mid) ∷ igStep (IG.commitTracer mid) ∷
  handlerStep child₀ Life.finishRethrow ∷ handlerExit child₀ ∷ []
pruned-unwind-path : Executes Remote.p₁ prunedUnwindActions pCleanup
pruned-unwind-path = next {c₁ = pAttached} refl (next {c₁ = pChecked} refl
  (next {c₁ = pRequested} refl (next {c₁ = pDelivered} refl (next {c₁ = pJoined} refl
  (next {c₁ = pFailed} refl (next {c₁ = pSampled} refl (next {c₁ = pTraced} refl
  (next {c₁ = pExited} refl (next refl done)))))))))
pTaken pSelected pClosed pCount pDone : Configuration
pTaken = cleanupSnapshot pCleanup (terminated nothing) (taken child₀) (handling child₀) (cleanupSelect childLease)
pSelected = cleanupSnapshot pCleanup (terminated nothing) (taken child₀) (handling child₀) (cleanupClose childLease [] countImmediately)
pClosed = cleanupSnapshot pCleanup (terminated nothing) (taken child₀) closed (cleanupPublish childLease [] countImmediately)
pCount = cleanupSnapshot pCleanup (terminated nothing) (full []) closed (cleanupCount cleanupNormal)
pDone = cleanupSnapshot pCleanup (terminated nothing) (full []) closed (cleanupDone cleanupNormal)
pruned-cleanup-path : Executes pCleanup
  (cleanupStep child₀ C.takeCleanupMap ∷ cleanupStep child₀ C.selectCleanupEntry ∷
   cleanupStep child₀ C.closeHandlerSocket ∷ cleanupStep child₀ C.publishCleanupMap ∷
   cleanupStep child₀ C.readCleanupCounters ∷ []) pDone
pruned-cleanup-path = next {c₁ = pTaken} refl (next {c₁ = pSelected} refl
  (next {c₁ = pClosed} refl (next {c₁ = pCount} refl (next refl done))))
pruning-skips-time-wait : advance (cleanupStep child₀ C.timeWaitElapsed) pCount ≡ nothing
pruning-skips-time-wait = refl
pruning-cleanup-finished : lookup child₀ (cleanups (world pDone)) ≡ just (cleanupDone cleanupNormal)
pruning-cleanup-finished = refl
