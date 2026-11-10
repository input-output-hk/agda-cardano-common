{-# OPTIONS --guardedness #-}

-- Increment 67: a release caller's cancellation lands in its target's TIME_WAIT
-- delay (network 2f1c154, Core.hs 2032 throwTo; 667-668 unmask threadDelay).
-- From the accepted TIME_WAIT snapshot (independent mux interruption, handler
-- finalizing in cleanupWaiting, CM shutdown at selected) with the pending
-- caller's delivering frame, the delivery interrupts the wait and acknowledges
-- the caller in one step; the caller returns, cleanup finishes, the handler
-- result is published and the CM wait completes.
--
-- Scope: these are handler-layer (W.step) edges only. Lifting the route into
-- the initialized Protocols runtime and retaining the birth packet
-- (TimeWaitChecks.retain) is an open gap: the embedding lift and the retained
-- run exhaust a 20 GB heap (PROJECT_STATE, increment 67).
module ConnectionManagement.Negative.ServerPeersReleaseTimeWait where

open import Data.Bool using (true; false)
open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain using (ident; errorId)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as Shared
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.OutboundRelease as Release
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.MuxHandlerExit as Exit
import ConnectionManagement.Negative.MuxResultMonitor as RF
import ConnectionManagement.Negative.GovernorPool as Prior
open import ConnectionManagement.Negative.ServerPeersOrigins using (module TimeWaitChecks; module ReleaseMuxChecks)
import ConnectionManagement.Properties.ServerPeersReleaseTimeWait as Facts

private
 module P = TimeWaitChecks.WaitingPrefix
 module X = TimeWaitChecks.Suffix
 module R = ReleaseMuxChecks
 module W = Exit RF.bearerClosed
 module OldCM = X.OldCM
 module TW = Facts RF.bearerClosed Prior.classify using (TimeWaitReceipt; timewait-observation; timewait-shutdown)

owner = R.owner
caller = R.caller
bodyError = X.bodyError
receiptError = errorId 98
fault = just (X.G.asyncExit receiptError)
outcome = Shared.cleanupError receiptError
delivery : W.Action
delivery = W.deliverReleaseTimeWait caller receiptError

-- Snapshots. The caller frame is reframed exactly as in increment 66.
waitingPhysical = P.waitingPhysical OldCM.selected
requestedPhysical = R.reframe (Release.delivering owner R.continuation) waitingPhysical
receivedPhysical = R.reframe R.continuation (X.state OldCM.selected X.finalizing fault (X.worldFinalize outcome))
returnedPhysical = R.returned (X.state OldCM.selected X.finalizing fault (X.worldFinalize outcome))
countPhysical = R.returned (X.state OldCM.selected X.finalizing fault (X.worldCount outcome))
donePhysical = R.returned (X.state OldCM.selected X.finalizing fault (X.worldDone outcome))
cleanedPhysical = R.returned (X.state OldCM.selected (W.cleanupComplete (W.asyncException bodyError) outcome) fault (X.worldDone outcome))
published : Close.State → W.State
published coordinator = R.returned (X.state coordinator (W.resultAvailable (W.asyncException bodyError) outcome) fault (X.worldDone outcome))

-- Handler-layer edges.
receipt : W.step delivery requestedPhysical ≡ just receivedPhysical
receipt = refl
finally : W.step (W.cleanup owner Cleanup.finishTimeWait) returnedPhysical ≡ just countPhysical
finally = refl
counters : W.step (W.cleanup owner Cleanup.readCleanupCounters) countPhysical ≡ just donePhysical
counters = refl
finish : W.step (W.finishCleanup owner) donePhysical ≡ just cleanedPhysical
finish = refl
publish : W.step (W.publishAsyncResult owner) cleanedPhysical ≡ just (published OldCM.selected)
publish = refl
-- CM shutdown then requests the already finished target and waits.
cmRequest : W.step (W.shutdownStep Close.requestCancellation) (published OldCM.selected) ≡ just (published OldCM.requested)
cmRequest = refl
cmFinished : W.step W.acknowledgeFinished (published OldCM.requested) ≡ just (published OldCM.acknowledged)
cmFinished = refl
traverse : W.step (W.shutdownStep Close.finishTraversal) (published OldCM.acknowledged) ≡ just (published OldCM.awaiting)
traverse = refl
wait : W.step (W.shutdownStep Close.finishClose) (published OldCM.awaiting) ≡ just (published OldCM.closed)
wait = refl

-- The receipt's facts, derived from the actual step.
receiptFacts : TW.TimeWaitReceipt caller receiptError requestedPhysical receivedPhysical
receiptFacts = TW.timewait-observation caller receiptError requestedPhysical receipt
receiptSameCM : W.shutdown receivedPhysical ≡ W.shutdown requestedPhysical
receiptSameCM = TW.timewait-shutdown receiptFacts
receiptHasNoResult : W.resultReady owner receivedPhysical ≡ false
receiptHasNoResult = refl
receiptLeavesCallerUnreturned : O.released (W.source receivedPhysical) ≡ []
receiptLeavesCallerUnreturned = refl
resultReturned : lookup caller (O.released (W.source returnedPhysical)) ≡ just R.result
resultReturned = refl
finalResult : W.resultReady owner (published OldCM.closed) ≡ true
finalResult = refl

-- Controls.
-- Before the caller's request there is no delivering frame to target.
prematureDelivery : W.step delivery waitingPhysical ≡ nothing
prematureDelivery = refl
-- The same delivery cannot happen twice.
duplicateDelivery : W.step delivery receivedPhysical ≡ nothing
duplicateDelivery = refl
-- A caller with no release frame has no target.
missingCaller : W.step (W.deliverReleaseTimeWait (ident 999) receiptError) requestedPhysical ≡ nothing
missingCaller = refl
-- While cleanup is still masked (before TIME_WAIT is entered), throwTo cannot land.
maskedCleanupPhysical = R.reframe (Release.delivering owner R.continuation) (P.finalizer OldCM.selected P.world4)
maskedCleanupRefused : W.step delivery maskedCleanupPhysical ≡ nothing
maskedCleanupRefused = refl
-- A handler whose captured start is no longer current is not a target.
staleCapturePhysical = R.reframe (Release.delivering owner R.continuation)
 (P.setWorld (record P.world5 { handlers = [] }) waitingPhysical)
staleCaptureRefused : W.step delivery staleCapturePhysical ≡ nothing
staleCaptureRefused = refl
-- Once CM shutdown has interrupted TIME_WAIT, the release delivery is refused.
afterShutdownInterruptPhysical = R.reframe (Release.delivering owner R.continuation) X.interruptedPhysical
afterShutdownInterruptRefused : W.step delivery afterShutdownInterruptPhysical ≡ nothing
afterShutdownInterruptRefused = refl
-- The finished-target acknowledgement does not replace the delivery.
finishedAckRefused : W.step (W.acknowledgeReleaseFinished caller) requestedPhysical ≡ nothing
finishedAckRefused = refl
