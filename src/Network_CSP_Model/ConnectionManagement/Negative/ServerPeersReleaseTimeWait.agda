{-# OPTIONS --guardedness #-}

-- Increment 67: a release caller's cancellation lands in its target's TIME_WAIT
-- delay (network 2f1c154, Core.hs 2032 throwTo; 667-668 unmask threadDelay).
-- From the accepted TIME_WAIT branch point (independent mux interruption,
-- handler finalizing in cleanupWaiting, CM shutdown at selected) the pending
-- caller requests cancellation; its delivery interrupts the wait and
-- acknowledges the caller in one step; the caller returns, cleanup finishes,
-- the handler result is published and the CM wait completes. The original
-- outbound birth packet and backing are retained throughout.
module ConnectionManagement.Negative.ServerPeersReleaseTimeWait where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
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
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.ServerAdmission as AdmissionModel
import ConnectionManagement.Properties.ServerPeersMuxEmbedding as Embedding
import ConnectionManagement.Negative.MuxResultMonitor as RF
import ConnectionManagement.Negative.GovernorPool as Prior
import ConnectionManagement.Negative.ServerPeers as PriorServer
open import ConnectionManagement.Negative.ServerPeersOrigins using (module TimeWaitChecks; module ReleaseMuxChecks)
import ConnectionManagement.Properties.ServerPeersReleaseTimeWait as Facts

-- The endpoint's names are opened, never aliased. An alias (module X = M) is
-- a module copy: comparing a copied step or advance with the original named
-- in a lemma type makes Agda evaluate both sides on these concrete states,
-- which exhausts a 20 GB heap. With the original names the lift is cheap.
open ReleaseMuxChecks using (module W; endpoint-up; trace-edge; reframe; returned; at; event; call; owner; caller; continuation; result)
open TimeWaitChecks.Suffix using (module OldCM; state; worldFinalize; worldCount; worldDone; finalizing; bodyError; branchpoint; interruptedPhysical)
open TimeWaitChecks.WaitingPrefix using (waitingPhysical; finalizer; world4; world5; setWorld)

private
 module E = Exit RF.bearerClosed using (Action; deliverReleaseTimeWait; cleanupComplete; asyncException; resultAvailable)
 module T = Combined.Protocols RF.bearerClosed Prior.classify PriorServer.Protocols.capability using (Event; Runs; advance; stop)
 module Emb = Embedding.Frontend RF.bearerClosed Prior.classify PriorServer.Protocols.capability using (Allowed; nextFront)
 module Adm = AdmissionModel RF.bearerClosed using (closingCM)
 module TW = Facts RF.bearerClosed Prior.classify using (TimeWaitReceipt; timewait-observation; timewait-shutdown)

receiptError = errorId 98
fault = just (TimeWaitChecks.Suffix.G.asyncExit receiptError)
outcome = Shared.cleanupError receiptError
delivery : E.Action
delivery = E.deliverReleaseTimeWait caller receiptError

-- Snapshots. The caller frame is reframed exactly as in increment 66.
startPhysical = waitingPhysical OldCM.selected
requestedPhysical = reframe (Release.delivering owner continuation) startPhysical
receivedPhysical = reframe continuation (state OldCM.selected finalizing fault (worldFinalize outcome))
returnedPhysical = returned (state OldCM.selected finalizing fault (worldFinalize outcome))
countPhysical = returned (state OldCM.selected finalizing fault (worldCount outcome))
donePhysical = returned (state OldCM.selected finalizing fault (worldDone outcome))
cleanedPhysical = returned (state OldCM.selected (E.cleanupComplete (E.asyncException bodyError) outcome) fault (worldDone outcome))
published : Close.State → W.State
published coordinator = returned (state coordinator (E.resultAvailable (E.asyncException bodyError) outcome) fault (worldDone outcome))

requested = at requestedPhysical
received = at receivedPhysical
final = at (published OldCM.closed)

-- One handler edge lifted through the embedding and prepended to a run, in the
-- endpoint's own runtime vocabulary.
edge : ∀ a before after {end events} → W.step a before ≡ just after →
 Emb.Allowed a before after TimeWaitChecks.ScopeClose.closedContext TimeWaitChecks.TerminatingPrefix.preparedFront
  Adm.closingCM false TimeWaitChecks.ScopeClose.publishedExit →
 Emb.nextFront a TimeWaitChecks.TerminatingPrefix.preparedFront ≡ TimeWaitChecks.TerminatingPrefix.preparedFront →
 T.Runs (at after) events end → T.Runs (at before) (event a ∷ events) end
edge a before after actual permitted copied path = trace-edge (event a) (at before) (at after) (at before) (at after) refl refl
 (endpoint-up a before {after = after} (at before) (at after) refl refl permitted copied actual) path

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

events : List T.Event
events = call Release.requestCancellation ∷ event delivery ∷ call Release.returnResult ∷
 event (W.cleanup owner Cleanup.finishTimeWait) ∷ event (W.cleanup owner Cleanup.readCleanupCounters) ∷
 event (W.finishCleanup owner) ∷ event (W.publishAsyncResult owner) ∷
 event (W.shutdownStep Close.requestCancellation) ∷ event W.acknowledgeFinished ∷
 event (W.shutdownStep Close.finishTraversal) ∷ event (W.shutdownStep Close.finishClose) ∷ []

-- The actual run from the accepted branch point: core caller calls by their
-- real guarded step, handler edges through the embedding with each of the six
-- permissions discharged on its concrete states.
abstract
 actual : T.Runs branchpoint events final
 actual =
  trace-edge (call Release.requestCancellation) (at startPhysical) requested branchpoint requested refl refl refl
  (edge delivery requestedPhysical receivedPhysical receipt (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
  (trace-edge (call Release.returnResult) received (at returnedPhysical) received (at returnedPhysical) refl refl refl
  (edge (W.cleanup owner Cleanup.finishTimeWait) returnedPhysical countPhysical finally (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
  (edge (W.cleanup owner Cleanup.readCleanupCounters) countPhysical donePhysical counters (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
  (edge (W.finishCleanup owner) donePhysical cleanedPhysical finish (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
  (edge (W.publishAsyncResult owner) cleanedPhysical (published OldCM.selected) publish (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
  (edge (W.shutdownStep Close.requestCancellation) (published OldCM.selected) (published OldCM.requested) cmRequest (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
  (edge W.acknowledgeFinished (published OldCM.requested) (published OldCM.acknowledged) cmFinished (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
  (edge (W.shutdownStep Close.finishTraversal) (published OldCM.acknowledged) (published OldCM.awaiting) traverse (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
  (edge (W.shutdownStep Close.finishClose) (published OldCM.awaiting) (published OldCM.closed) wait (record { delta-permission = refl; delta-tickets = refl; server-permission = refl; ig-permission = refl; shared-permission = refl; front-permission = refl }) refl
  T.stop))))))))))

 -- The accepted initialized branch extends by these actual events; the original
 -- outbound birth packet and backing are retained to the final CM wait.
 initialized : TimeWaitChecks.Retained final (TimeWaitChecks.branchIndex ++ events)
 initialized = TimeWaitChecks.retain actual TimeWaitChecks.branch

resourcesFinal = TimeWaitChecks.resources initialized

-- The receipt's facts, derived from the actual step.
receiptFacts : TW.TimeWaitReceipt caller receiptError requestedPhysical receivedPhysical
receiptFacts = TW.timewait-observation caller receiptError requestedPhysical refl
receiptSameCM : W.shutdown receivedPhysical ≡ W.shutdown requestedPhysical
receiptSameCM = TW.timewait-shutdown receiptFacts
receiptHasNoResult : W.resultReady owner receivedPhysical ≡ false
receiptHasNoResult = refl
receiptLeavesCallerUnreturned : O.released (W.source receivedPhysical) ≡ []
receiptLeavesCallerUnreturned = refl
resultReturned : lookup caller (O.released (W.source returnedPhysical)) ≡ just result
resultReturned = refl
finalResult : W.resultReady owner (published OldCM.closed) ≡ true
finalResult = refl

-- Controls.
-- Before the caller's request there is no delivering frame to target.
prematureDelivery : W.step delivery startPhysical ≡ nothing
prematureDelivery = refl
-- The same delivery cannot happen twice.
duplicateDelivery : W.step delivery receivedPhysical ≡ nothing
duplicateDelivery = refl
-- A caller with no release frame has no target.
missingCaller : W.step (E.deliverReleaseTimeWait (ident 999) receiptError) requestedPhysical ≡ nothing
missingCaller = refl
-- While cleanup is still masked (before TIME_WAIT is entered), throwTo cannot land.
maskedCleanupPhysical = reframe (Release.delivering owner continuation) (finalizer OldCM.selected world4)
maskedCleanupRefused : W.step delivery maskedCleanupPhysical ≡ nothing
maskedCleanupRefused = refl
-- A handler whose captured start is no longer current is not a target.
staleCapturePhysical = reframe (Release.delivering owner continuation)
 (setWorld (record world5 { handlers = [] }) startPhysical)
staleCaptureRefused : W.step delivery staleCapturePhysical ≡ nothing
staleCaptureRefused = refl
-- Once CM shutdown has interrupted TIME_WAIT, the release delivery is refused.
afterShutdownInterruptPhysical = reframe (Release.delivering owner continuation) interruptedPhysical
afterShutdownInterruptRefused : W.step delivery afterShutdownInterruptPhysical ≡ nothing
afterShutdownInterruptRefused = refl
-- The finished-target acknowledgement does not replace the delivery.
finishedAckRefused : W.step (W.acknowledgeReleaseFinished caller) requestedPhysical ≡ nothing
finishedAckRefused = refl
-- Raw core delivery is refused, and the caller cannot return before delivery.
rawDeliveryBypass : T.advance (call (Release.cancellationDelivered owner)) requested ≡ nothing
rawDeliveryBypass = refl
prematureReturn : T.advance (call Release.returnResult) requested ≡ nothing
prematureReturn = refl
