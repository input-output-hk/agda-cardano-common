{-# OPTIONS --guardedness #-}

-- Initialized buffer/trace/send cancellation and the same captured CM finally.
-- Each window names an OBSERVED interruptible operation, not arbitrary delivery
-- in masked code. No provider, main-thread or universal-progress theorem.
module ConnectionManagement.Negative.MuxExitCancellation where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (local)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.MuxExitCancellation as Cancellation
import ConnectionManagement.Properties.MuxExitCancellation as CancellationFacts
import ConnectionManagement.MuxHandlerExit as Exit
import ConnectionManagement.Properties.MuxHandlerExit as ExitFacts
import ConnectionManagement.Negative.MuxHandlerExit as Base
import ConnectionManagement.Negative.MuxHandlerExitOutcomes as Outcomes
import ConnectionManagement.Negative.MuxGroupShutdown as GF
import ConnectionManagement.Negative.MuxResultMonitor as RF
import ConnectionManagement.Negative.MuxProtocolJobs as Old
import ConnectionManagement.State as S
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.Cleanup as C
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.HandlerLifecycle as Life
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
private
  module X = Cancellation RF.bearerClosed
  module W = Exit RF.bearerClosed
  module Facts = CancellationFacts RF.bearerClosed
  module ExitProof = ExitFacts RF.bearerClosed
owner : WorkerId
owner = Old.owner
cancelErr traceErr : ErrorId
cancelErr = errorId 88
traceErr = errorId 99
start : X.State
start = Base.wrap (GF.wrap (RF.wrap Old.b0))
actual-initializer : X.initial (O.initial Old.F.start) ≡ just start
actual-initializer = refl
reading wait : Close.State
reading = Close.shutdownState Close.reading (ident 0 ∷ []) [] (owner ∷ [])
wait = Close.shutdownState Close.awaitResults (ident 0 ∷ []) [] (owner ∷ [])
buf0 buf1 buf2 buf3 buf4 buf5 buf6 buf7 buf8 : X.State
buf0 = Base.normal1
buf1 = W.setShutdown (Close.shutdownState Close.reading (ident 0 ∷ []) (ident 0 ∷ []) []) buf0
buf2 = W.setShutdown (Close.shutdownState (Close.sendReady (ident 0) owner) (ident 0 ∷ []) [] []) buf0
buf3 = W.setShutdown (Close.shutdownState (Close.awaitDelivery (ident 0) owner) (ident 0 ∷ []) [] []) buf0
buf4 = W.setShutdown reading (Base.plain GF.normal30 (W.bufferScope (W.G.asyncExit cancelErr)))
buf5 = W.setShutdown wait (Base.plain GF.normal30 (W.bufferScope (W.G.asyncExit cancelErr)))
buf6 = W.setShutdown wait (Base.plain GF.normal30 (W.bodyExited (W.asyncException cancelErr)))
buf7 = W.setShutdown wait (Base.at GF.normal30 (W.finalizing (W.asyncException cancelErr)) (Base.world1 (Base.world0 GF.normal30)))
buf8 = W.setShutdown wait (Base.at GF.normal30 (W.finalizing (W.asyncException cancelErr)) (Base.world2 (Base.world0 GF.normal30)))
buf9 : X.State
buf9 = W.setShutdown wait (Base.at GF.normal30 (W.finalizing (W.asyncException cancelErr)) (Base.world3 (Base.world0 GF.normal30)))
buf10 : X.State
buf10 = W.setShutdown wait (Base.at GF.normal30 (W.finalizing (W.asyncException cancelErr)) (Base.world4 (Base.world0 GF.normal30)))
buf11 : X.State
buf11 = W.setShutdown wait (Base.at GF.normal30 (W.finalizing (W.asyncException cancelErr)) (Base.world5 (Base.world0 GF.normal30)))
buf12 : X.State
buf12 = W.setShutdown wait (Base.at GF.normal30 (W.finalizing (W.asyncException cancelErr)) (Base.world6 (Base.world0 GF.normal30)))
buf13 buf14 buf15 : X.State
buf13 = W.setShutdown wait (Base.at GF.normal30 (W.cleanupComplete (W.asyncException cancelErr) S.cleanupNormal) (Base.world6 (Base.world0 GF.normal30)))
buf14 = W.setShutdown wait (Base.at GF.normal30 (W.resultAvailable (W.asyncException cancelErr) S.cleanupNormal) (Base.world6 (Base.world0 GF.normal30)))
buf15 = W.setShutdown (Close.shutdownState Close.closed (ident 0 ∷ []) [] (owner ∷ [])) buf14
buf-edge1 : X.step (X.run (W.shutdownStep Close.captureSnapshot)) buf0 ≡ just buf1
buf-edge1 = refl
buf-edge2 : X.step (X.run (W.shutdownStep Close.readEntry)) buf1 ≡ just buf2
buf-edge2 = refl
buf-edge3 : X.step (X.run (W.shutdownStep Close.requestCancellation)) buf2 ≡ just buf3
buf-edge3 = refl
buf-edge4 : X.step (X.deliverShutdown X.bufferBlock cancelErr) buf3 ≡ just buf4
buf-edge4 = refl
buf-edge5 : X.step (X.run (W.shutdownStep Close.finishTraversal)) buf4 ≡ just buf5
buf-edge5 = refl
buf-edge6 : X.step (X.run (W.observeBufferReturn owner)) buf5 ≡ just buf6
buf-edge6 = refl
buf-edge7 : X.step (X.run (W.enterFinalizer owner)) buf6 ≡ just buf7
buf-edge7 = refl
buf-edge8 : X.step (X.run (W.cleanup owner C.takeCleanupMap)) buf7 ≡ just buf8
buf-edge8 = refl
buf-edge9 : X.step (X.run (W.cleanup owner C.selectCleanupEntry)) buf8 ≡ just buf9
buf-edge9 = refl
buf-edge10 : X.step (X.run (W.cleanup owner C.closeHandlerSocket)) buf9 ≡ just buf10
buf-edge10 = refl
buf-edge11 : X.step (X.run (W.cleanup owner C.publishCleanupMap)) buf10 ≡ just buf11
buf-edge11 = refl
buf-edge12 : X.step (X.run (W.cleanup owner C.readCleanupCounters)) buf11 ≡ just buf12
buf-edge12 = refl
buf-edge13 : X.step (X.run (W.finishCleanup owner)) buf12 ≡ just buf13
buf-edge13 = refl
buf-edge14 : X.step (X.run (W.publishAsyncResult owner)) buf13 ≡ just buf14
buf-edge14 = refl
buf-edge15 : X.step (X.run (W.shutdownStep Close.finishClose)) buf14 ≡ just buf15
buf-edge15 = refl
bufActions : List X.Action
bufActions = (X.run (W.shutdownStep Close.captureSnapshot)) ∷ (X.run (W.shutdownStep Close.readEntry)) ∷ (X.run (W.shutdownStep Close.requestCancellation)) ∷ (X.deliverShutdown X.bufferBlock cancelErr) ∷ (X.run (W.shutdownStep Close.finishTraversal)) ∷ (X.run (W.observeBufferReturn owner)) ∷ (X.run (W.enterFinalizer owner)) ∷ (X.run (W.cleanup owner C.takeCleanupMap)) ∷ (X.run (W.cleanup owner C.selectCleanupEntry)) ∷ (X.run (W.cleanup owner C.closeHandlerSocket)) ∷ (X.run (W.cleanup owner C.publishCleanupMap)) ∷ (X.run (W.cleanup owner C.readCleanupCounters)) ∷ (X.run (W.finishCleanup owner)) ∷ (X.run (W.publishAsyncResult owner)) ∷ (X.run (W.shutdownStep Close.finishClose)) ∷ []
bufPath : X.Executes buf0 bufActions buf15
bufPath = (X.next buf-edge1 (X.next buf-edge2 (X.next buf-edge3 (X.next buf-edge4 (X.next buf-edge5 (X.next buf-edge6 (X.next buf-edge7 (X.next buf-edge8 (X.next buf-edge9 (X.next buf-edge10 (X.next buf-edge11 (X.next buf-edge12 (X.next buf-edge13 (X.next buf-edge14 (X.next buf-edge15 X.done)))))))))))))))
actionsOf : ∀ {s actions s′} → W.Executes s actions s′ → List W.Action
actionsOf {actions = actions} path = actions
abstract
  initialized-buffer-close : X.Executes start
    (map X.run (actionsOf Outcomes.initialized-buffer-entry) ++ bufActions) buf15
  initialized-buffer-close = Facts.append (Facts.lift Outcomes.initialized-buffer-entry) bufPath

buffer-delivery-still-awaits-provider : W.step (W.enterFinalizer owner) buf4 ≡ nothing
buffer-delivery-still-awaits-provider = refl
buffer-delivery-is-not-a-parent-result : W.resultReady owner buf4 ≡ false
buffer-delivery-is-not-a-parent-result = refl
buffer-cancel-does-not-retroactively-fail-mux : W.source buf6 ≡ W.source buf0
buffer-cancel-does-not-retroactively-fail-mux = refl
buffer-wait-cannot-skip-result : X.step (X.run (W.shutdownStep Close.finishClose)) buf13 ≡ nothing
buffer-wait-cannot-skip-result = refl
buffer-async-result-preserved : W.resultOf owner buf15 ≡ just (W.asyncException cancelErr)
buffer-async-result-preserved = refl
providerReplacement : X.State
providerReplacement = W.setShutdown reading (Base.plain GF.normal30 (W.classifying traceErr))
provider-cleanup-may-replace-cancellation : X.step (X.run (W.observeBufferException owner (W.G.failedExit traceErr))) buf4 ≡ just providerReplacement
provider-cleanup-may-replace-cancellation = refl

trace0 trace1 node0 node1 : X.State
trace0 = Base.sync1
trace1 = Base.plain GF.normal30 (W.bodyExited (W.asyncException cancelErr))
node0 = Base.node1
node1 = Base.plain GF.normal30 (W.bodyExited (W.asyncException cancelErr))
trace-edge : X.step (X.observeCancellation X.errorTraceBlock owner cancelErr) trace0 ≡ just trace1
trace-edge = refl
node-edge : X.step (X.observeCancellation X.nodeSendBlock owner cancelErr) node0 ≡ just node1
node-edge = refl
no-pure-policy-delivery : X.step (X.observeCancellation X.errorTraceBlock owner cancelErr) Base.sync0 ≡ nothing
no-pure-policy-delivery = refl
no-pure-peer-rethrow-delivery : X.step (X.observeCancellation X.errorTraceBlock owner cancelErr) Base.peer0 ≡ nothing
no-pure-peer-rethrow-delivery = refl
no-pure-node-rethrow-delivery : X.step (X.observeCancellation X.nodeSendBlock owner cancelErr) Base.node2 ≡ nothing
no-pure-node-rethrow-delivery = refl
no-bare-finalizer-delivery : X.step (X.observeCancellation X.bufferBlock owner cancelErr) Base.normal3 ≡ nothing
no-bare-finalizer-delivery = refl
no-result-delivery : X.step (X.observeCancellation X.bufferBlock owner cancelErr) Base.normal10 ≡ nothing
no-result-delivery = refl
cancelled-trace-cannot-return-to-policy : X.step (X.run (W.observeErrorTrace owner)) trace1 ≡ nothing
cancelled-trace-cannot-return-to-policy = refl
cancelled-send-cannot-invent-receipt : X.step (X.run (W.observeNodeDelivery owner)) node1 ≡ nothing
cancelled-send-cannot-invent-receipt = refl
cancelled-classifier-is-not-reclassified : X.step (X.run (W.choosePolicy owner Life.shutdownNode)) trace1 ≡ nothing
cancelled-classifier-is-not-reclassified = refl
tracerFailure : X.State
tracerFailure = Base.plain GF.normal30 (W.bodyExited (W.syncException traceErr))
tracer-exception-escapes-classifier : X.step (X.observeErrorTraceException owner traceErr) trace0 ≡ just tracerFailure
tracer-exception-escapes-classifier = refl
tracer-failure-is-not-old-peer-rethrow : X.step (X.run (W.rethrow owner)) tracerFailure ≡ nothing
tracer-failure-is-not-old-peer-rethrow = refl

-- Use the checked source cleanup with explicit flat intermediates; neither
-- cancellation in the classifier nor tracer failure bypasses that finalizer.
traceFinal : X.State
traceFinal = Base.at GF.normal30 (W.finalizing (W.asyncException cancelErr)) (Base.world1 (Base.world0 GF.normal30))
trace-enters-finalizer : X.step (X.run (W.enterFinalizer owner)) trace1 ≡ just traceFinal
trace-enters-finalizer = refl
tracerFinal : X.State
tracerFinal = Base.at GF.normal30 (W.finalizing (W.syncException traceErr)) (Base.world1 (Base.world0 GF.normal30))
tracer-enters-finalizer : X.step (X.run (W.enterFinalizer owner)) tracerFailure ≡ just tracerFinal
tracer-enters-finalizer = refl
traceActions : List X.Action
traceActions = X.run (W.observeBufferException owner (W.G.failedExit Old.err)) ∷
  X.run (W.choosePolicy owner Life.shutdownPeer) ∷ X.observeCancellation X.errorTraceBlock owner cancelErr ∷
  X.run (W.enterFinalizer owner) ∷ map X.run Outcomes.cleanupSuffixActions
nodeActions : List X.Action
nodeActions = X.run (W.observeBufferException owner (W.G.failedExit Old.err)) ∷
  X.run (W.choosePolicy owner Life.shutdownNode) ∷ X.run (W.observeErrorTrace owner) ∷
  X.observeCancellation X.nodeSendBlock owner cancelErr ∷ X.run (W.enterFinalizer owner) ∷ map X.run Outcomes.cleanupSuffixActions
failureActions : List X.Action
failureActions = X.run (W.observeBufferException owner (W.G.failedExit Old.err)) ∷
  X.run (W.choosePolicy owner Life.shutdownPeer) ∷ X.observeErrorTraceException owner traceErr ∷
  X.run (W.enterFinalizer owner) ∷ map X.run Outcomes.cleanupSuffixActions
asyncEnd syncEnd : X.State
asyncEnd = Base.at GF.normal30 (W.resultAvailable (W.asyncException cancelErr) S.cleanupNormal) (Base.world6 (Base.world0 GF.normal30))
syncEnd = Base.at GF.normal30 (W.resultAvailable (W.syncException traceErr) S.cleanupNormal) (Base.world6 (Base.world0 GF.normal30))
tracePath : X.Executes buf0 traceActions asyncEnd
tracePath = X.next Base.buffer-replacement (X.next Base.peer-policy
  (X.next trace-edge (X.next trace-enters-finalizer (Facts.lift (Outcomes.cleanupSuffix (W.asyncException cancelErr))))))
nodePath : X.Executes buf0 nodeActions asyncEnd
nodePath = X.next Base.buffer-replacement (X.next Base.node-policy (X.next Base.node-trace
  (X.next node-edge (X.next trace-enters-finalizer (Facts.lift (Outcomes.cleanupSuffix (W.asyncException cancelErr)))))))
failurePath : X.Executes buf0 failureActions syncEnd
failurePath = X.next Base.buffer-replacement (X.next Base.peer-policy
  (X.next tracer-exception-escapes-classifier (X.next tracer-enters-finalizer (Facts.lift (Outcomes.cleanupSuffix (W.syncException traceErr))))))
abstract
  initialized-trace-cancel : X.Executes start (map X.run (actionsOf Outcomes.initialized-buffer-entry) ++ traceActions) asyncEnd
  initialized-trace-cancel = Facts.append (Facts.lift Outcomes.initialized-buffer-entry) tracePath
  initialized-node-send-cancel : X.Executes start (map X.run (actionsOf Outcomes.initialized-buffer-entry) ++ nodeActions) asyncEnd
  initialized-node-send-cancel = Facts.append (Facts.lift Outcomes.initialized-buffer-entry) nodePath
  initialized-tracer-exception : X.Executes start (map X.run (actionsOf Outcomes.initialized-buffer-entry) ++ failureActions) syncEnd
  initialized-tracer-exception = Facts.append (Facts.lift Outcomes.initialized-buffer-entry) failurePath

buffer-capture-and-supply : Capture.Captures (X.source buf15) Data.Product.× Supply.Valid (X.source buf15)
buffer-capture-and-supply = Facts.from-initial-captures actual-initializer initialized-buffer-close ,
  Facts.from-initial-supply actual-initializer Old.Prior.initial-bounds initialized-buffer-close
buffer-source-and-pools : Facts.Paths start buf15
buffer-source-and-pools = Facts.exec-projects initialized-buffer-close
buffer-exact-delivery : Facts.ShutdownDelivery X.bufferBlock cancelErr buf3 buf4
buffer-exact-delivery = Facts.shutdown-observation X.bufferBlock cancelErr buf3 buf-edge4
trace-exact-delivery : Facts.Delivery X.errorTraceBlock owner cancelErr trace0 trace1
trace-exact-delivery = Facts.delivery-observation X.errorTraceBlock owner cancelErr trace0 trace-edge
buffer-physical-wait : ExitProof.PhysicalWait buf14 buf15
buffer-physical-wait = Facts.physical-wait buf14 buf-edge15

-- The same actual CM sender targets this observed errorTraceBlock operation.
traceCM0 : X.State
traceCM0 = trace0
traceCM1 : X.State
traceCM1 = W.setShutdown (Close.shutdownState Close.reading (ident 0 ∷ []) (ident 0 ∷ []) []) trace0
traceCM2 : X.State
traceCM2 = W.setShutdown (Close.shutdownState (Close.sendReady (ident 0) owner) (ident 0 ∷ []) [] []) trace0
traceCM3 : X.State
traceCM3 = W.setShutdown (Close.shutdownState (Close.awaitDelivery (ident 0) owner) (ident 0 ∷ []) [] []) trace0
traceCM4 : X.State
traceCM4 = W.setShutdown reading trace1
traceCM-edge1 : X.step (X.run (W.shutdownStep Close.captureSnapshot)) traceCM0 ≡ just traceCM1
traceCM-edge1 = refl
traceCM-edge2 : X.step (X.run (W.shutdownStep Close.readEntry)) traceCM1 ≡ just traceCM2
traceCM-edge2 = refl
traceCM-edge3 : X.step (X.run (W.shutdownStep Close.requestCancellation)) traceCM2 ≡ just traceCM3
traceCM-edge3 = refl
traceCM-edge4 : X.step (X.deliverShutdown X.errorTraceBlock cancelErr) traceCM3 ≡ just traceCM4
traceCM-edge4 = refl
traceCMActions : List X.Action
traceCMActions = (X.run (W.shutdownStep Close.captureSnapshot)) ∷ (X.run (W.shutdownStep Close.readEntry)) ∷ (X.run (W.shutdownStep Close.requestCancellation)) ∷ (X.deliverShutdown X.errorTraceBlock cancelErr) ∷ []
traceCMPath : X.Executes traceCM0 traceCMActions traceCM4
traceCMPath = (X.next traceCM-edge1 (X.next traceCM-edge2 (X.next traceCM-edge3 (X.next traceCM-edge4 X.done))))
traceCM-ack-is-not-result : W.resultReady owner traceCM4 ≡ false
traceCM-ack-is-not-result = refl
traceCM-exact-ack : Facts.ShutdownDelivery X.errorTraceBlock cancelErr traceCM3 traceCM4
traceCM-exact-ack = Facts.shutdown-observation X.errorTraceBlock cancelErr traceCM3 traceCM-edge4

-- The same actual CM sender targets this observed nodeSendBlock operation.
nodeCM0 : X.State
nodeCM0 = node0
nodeCM1 : X.State
nodeCM1 = W.setShutdown (Close.shutdownState Close.reading (ident 0 ∷ []) (ident 0 ∷ []) []) node0
nodeCM2 : X.State
nodeCM2 = W.setShutdown (Close.shutdownState (Close.sendReady (ident 0) owner) (ident 0 ∷ []) [] []) node0
nodeCM3 : X.State
nodeCM3 = W.setShutdown (Close.shutdownState (Close.awaitDelivery (ident 0) owner) (ident 0 ∷ []) [] []) node0
nodeCM4 : X.State
nodeCM4 = W.setShutdown reading node1
nodeCM-edge1 : X.step (X.run (W.shutdownStep Close.captureSnapshot)) nodeCM0 ≡ just nodeCM1
nodeCM-edge1 = refl
nodeCM-edge2 : X.step (X.run (W.shutdownStep Close.readEntry)) nodeCM1 ≡ just nodeCM2
nodeCM-edge2 = refl
nodeCM-edge3 : X.step (X.run (W.shutdownStep Close.requestCancellation)) nodeCM2 ≡ just nodeCM3
nodeCM-edge3 = refl
nodeCM-edge4 : X.step (X.deliverShutdown X.nodeSendBlock cancelErr) nodeCM3 ≡ just nodeCM4
nodeCM-edge4 = refl
nodeCMActions : List X.Action
nodeCMActions = (X.run (W.shutdownStep Close.captureSnapshot)) ∷ (X.run (W.shutdownStep Close.readEntry)) ∷ (X.run (W.shutdownStep Close.requestCancellation)) ∷ (X.deliverShutdown X.nodeSendBlock cancelErr) ∷ []
nodeCMPath : X.Executes nodeCM0 nodeCMActions nodeCM4
nodeCMPath = (X.next nodeCM-edge1 (X.next nodeCM-edge2 (X.next nodeCM-edge3 (X.next nodeCM-edge4 X.done))))
nodeCM-ack-is-not-result : W.resultReady owner nodeCM4 ≡ false
nodeCM-ack-is-not-result = refl
nodeCM-exact-ack : Facts.ShutdownDelivery X.nodeSendBlock cancelErr nodeCM3 nodeCM4
nodeCM-exact-ack = Facts.shutdown-observation X.nodeSendBlock cancelErr nodeCM3 nodeCM-edge4

traceEntryActions nodeEntryActions : List X.Action
traceEntryActions = X.run (W.observeBufferException owner (W.G.failedExit Old.err)) ∷ X.run (W.choosePolicy owner Life.shutdownPeer) ∷ []
nodeEntryActions = X.run (W.observeBufferException owner (W.G.failedExit Old.err)) ∷ X.run (W.choosePolicy owner Life.shutdownNode) ∷ X.run (W.observeErrorTrace owner) ∷ []
traceEntryPath : X.Executes buf0 traceEntryActions trace0
traceEntryPath = X.next Base.buffer-replacement (X.next Base.peer-policy X.done)
nodeEntryPath : X.Executes buf0 nodeEntryActions node0
nodeEntryPath = X.next Base.buffer-replacement (X.next Base.node-policy (X.next Base.node-trace X.done))
abstract
  initialized-trace-CM-delivery : X.Executes start
    ((map X.run (actionsOf Outcomes.initialized-buffer-entry) ++ traceEntryActions) ++ traceCMActions) traceCM4
  initialized-trace-CM-delivery = Facts.append
    (Facts.append (Facts.lift Outcomes.initialized-buffer-entry) traceEntryPath) traceCMPath
  initialized-node-send-CM-delivery : X.Executes start
    ((map X.run (actionsOf Outcomes.initialized-buffer-entry) ++ nodeEntryActions) ++ nodeCMActions) nodeCM4
  initialized-node-send-CM-delivery = Facts.append
    (Facts.append (Facts.lift Outcomes.initialized-buffer-entry) nodeEntryPath) nodeCMPath


buffer-window-is-not-tracer-window : X.step (X.observeCancellation X.errorTraceBlock owner cancelErr) buf0 ≡ nothing
buffer-window-is-not-tracer-window = refl
tracer-window-is-not-provider-window : X.step (X.observeCancellation X.bufferBlock owner cancelErr) trace0 ≡ nothing
tracer-window-is-not-provider-window = refl
