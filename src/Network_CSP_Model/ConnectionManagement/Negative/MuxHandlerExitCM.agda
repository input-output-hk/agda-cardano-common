{-# OPTIONS --guardedness #-}

-- Actual initialized exit paths; flat source snapshots retain the captured CM
-- finalizer and keep buffer/policy observations explicit. No replay claim.
module ConnectionManagement.Negative.MuxHandlerExitCM where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (local)
open import ConnectionManagement.Store using (put; lookup)
import ConnectionManagement.MuxHandlerExit as Exit
import ConnectionManagement.Properties.MuxHandlerExit as ExitFacts
import ConnectionManagement.Negative.MuxGroupShutdown as F
import ConnectionManagement.Negative.MuxResultMonitor as RF
import ConnectionManagement.Negative.MuxProtocolJobs as Old
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.State as S
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as Machine
import ConnectionManagement.Rules.Cleanup as C
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.HandlerLifecycle as Life
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
module W = Exit RF.bearerClosed
module Facts = ExitFacts RF.bearerClosed
module G = W.G
module Pool = W.Pool
module M = G.M
module P = G.P
import ConnectionManagement.Rules.MuxJobTypes as T
open import ConnectionManagement.Negative.MuxHandlerExit
-- CM shutdown's send is acknowledged at observed owner async delivery. Its
-- collective wait still blocks while the same handler unwinds the whole pool.
cm0 cm1 cm2 cm3 cm4 cm5 : W.State
cm0 = wrap F.normal7
cm1 = W.setShutdown (Close.shutdownState Close.reading (ident 0 ∷ []) (ident 0 ∷ []) []) cm0
cm2 = W.setShutdown (Close.shutdownState (Close.sendReady (ident 0) owner) (ident 0 ∷ []) [] []) cm0
cm3 = W.setShutdown (Close.shutdownState (Close.awaitDelivery (ident 0) owner) (ident 0 ∷ []) [] []) cm0
cm4 = W.setShutdown (Close.shutdownState Close.reading (ident 0 ∷ []) [] (owner ∷ [])) (wrap F.abortGroup1)
wait : Close.State
wait = Close.shutdownState Close.awaitResults (ident 0 ∷ []) [] (owner ∷ [])
cm5 = W.setShutdown wait (wrap F.abortGroup1)
cm-edge1 : W.step (W.shutdownStep Close.captureSnapshot) cm0 ≡ just cm1
cm-edge1 = refl
cm-edge2 : W.step (W.shutdownStep Close.readEntry) cm1 ≡ just cm2
cm-edge2 = refl
cm-edge3 : W.step (W.shutdownStep Close.requestCancellation) cm2 ≡ just cm3
cm-edge3 = refl
cm-edge4 : W.step (W.deliverShutdownMux err) cm3 ≡ just cm4
cm-edge4 = refl
cm-edge5 : W.step (W.shutdownStep Close.finishTraversal) cm4 ≡ just cm5
cm-edge5 = refl
ack-is-not-a-parent-result : W.resultReady owner cm4 ≡ false
ack-is-not-a-parent-result = refl
cm-wait-blocks-before-whole-close : W.step (W.shutdownStep Close.finishClose) cm5 ≡ nothing
cm-wait-blocks-before-whole-close = refl
no-raw-acknowledgment : W.step (W.shutdownStep Close.acknowledgeDelivery) cm3 ≡ nothing
no-raw-acknowledgment = refl
cmActions : List W.Action
cmActions = W.shutdownStep Close.captureSnapshot ∷ W.shutdownStep Close.readEntry ∷
  W.shutdownStep Close.requestCancellation ∷ W.deliverShutdownMux err ∷ W.shutdownStep Close.finishTraversal ∷ []
cmPath : W.Executes cm0 cmActions cm5
cmPath = W.next cm-edge1 (W.next cm-edge2 (W.next cm-edge3 (W.next cm-edge4 (W.next cm-edge5 W.done))))
unwind2 : W.State
unwind2 = W.setShutdown wait (wrap F.abortGroup2)
unwind-edge2 : W.step (W.run (G.beginWholeClose owner (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []))) cm5 ≡ just unwind2
unwind-edge2 = refl
unwind3 : W.State
unwind3 = W.setShutdown wait (wrap F.abortGroup3)
unwind-edge3 : W.step (W.run (G.requestWholeCancel owner)) unwind2 ≡ just unwind3
unwind-edge3 = refl
unwind4 : W.State
unwind4 = W.setShutdown wait (wrap F.abortGroup4)
unwind-edge4 : W.step (W.run (G.finishChildUnwind Old.j₁₀)) unwind3 ≡ just unwind4
unwind-edge4 = refl
unwind5 : W.State
unwind5 = W.setShutdown wait (wrap F.abortGroup5)
unwind-edge5 : W.step (W.run (G.run (M.run (P.deregisterProtocol Old.j₁₀)))) unwind4 ≡ just unwind5
unwind-edge5 = refl
unwind6 : W.State
unwind6 = W.setShutdown wait (wrap F.abortGroup6)
unwind-edge6 : W.step (W.run (G.run (M.run (P.asyncProtocolResult Old.j₁₀)))) unwind5 ≡ just unwind6
unwind-edge6 = refl
unwind7 : W.State
unwind7 = W.setShutdown wait (wrap F.abortGroup7)
unwind-edge7 : W.step (W.run (G.joinWhole owner)) unwind6 ≡ just unwind7
unwind-edge7 = refl
unwind8 : W.State
unwind8 = W.setShutdown wait (wrap F.abortGroup8)
unwind-edge8 : W.step (W.run (G.requestWholeCancel owner)) unwind7 ≡ just unwind8
unwind-edge8 = refl
unwind9 : W.State
unwind9 = W.setShutdown wait (wrap F.abortGroup9)
unwind-edge9 : W.step (W.run (G.deliverWhole owner)) unwind8 ≡ just unwind9
unwind-edge9 = refl
unwind10 : W.State
unwind10 = W.setShutdown wait (wrap F.abortGroup10)
unwind-edge10 : W.step (W.run (G.finishChildUnwind Old.j₁)) unwind9 ≡ just unwind10
unwind-edge10 = refl
unwind11 : W.State
unwind11 = W.setShutdown wait (wrap F.abortGroup11)
unwind-edge11 : W.step (W.run (G.run (M.run (P.deregisterInfra owner T.demuxer)))) unwind10 ≡ just unwind11
unwind-edge11 = refl
unwind12 : W.State
unwind12 = W.setShutdown wait (wrap F.abortGroup12)
unwind-edge12 : W.step (W.run (G.run (M.run (P.asyncInfraResult owner T.demuxer)))) unwind11 ≡ just unwind12
unwind-edge12 = refl
unwind13 : W.State
unwind13 = W.setShutdown wait (wrap F.abortGroup13)
unwind-edge13 : W.step (W.run (G.joinWhole owner)) unwind12 ≡ just unwind13
unwind-edge13 = refl
unwind14 : W.State
unwind14 = W.setShutdown wait (wrap F.abortGroup14)
unwind-edge14 : W.step (W.run (G.requestWholeCancel owner)) unwind13 ≡ just unwind14
unwind-edge14 = refl
unwind15 : W.State
unwind15 = W.setShutdown wait (wrap F.abortGroup15)
unwind-edge15 : W.step (W.run (G.deliverWhole owner)) unwind14 ≡ just unwind15
unwind-edge15 = refl
unwind16 : W.State
unwind16 = W.setShutdown wait (wrap F.abortGroup16)
unwind-edge16 : W.step (W.run (G.finishChildUnwind Old.j₀)) unwind15 ≡ just unwind16
unwind-edge16 = refl
unwind17 : W.State
unwind17 = W.setShutdown wait (wrap F.abortGroup17)
unwind-edge17 : W.step (W.run (G.run (M.run (P.deregisterInfra owner T.muxer)))) unwind16 ≡ just unwind17
unwind-edge17 = refl
unwind18 : W.State
unwind18 = W.setShutdown wait (wrap F.abortGroup18)
unwind-edge18 : W.step (W.run (G.run (M.run (P.asyncInfraResult owner T.muxer)))) unwind17 ≡ just unwind18
unwind-edge18 = refl
unwind19 : W.State
unwind19 = W.setShutdown wait (wrap F.abortGroup19)
unwind-edge19 : W.step (W.run (G.joinWhole owner)) unwind18 ≡ just unwind19
unwind-edge19 = refl
unwind20 : W.State
unwind20 = W.setShutdown wait (wrap F.abortGroup20)
unwind-edge20 : W.step (W.run (G.finishWholeClose owner)) unwind19 ≡ just unwind20
unwind-edge20 = refl
unwind21 : W.State
unwind21 = W.setShutdown wait (wrap F.abortGroup21)
unwind-edge21 : W.step (W.run (G.writeAsyncFailure owner)) unwind20 ≡ just unwind21
unwind-edge21 = refl
unwind22 : W.State
unwind22 = W.setShutdown wait (wrap F.abortGroup22)
unwind-edge22 : W.step (W.run (G.beginAsyncDead owner)) unwind21 ≡ just unwind22
unwind-edge22 = refl
unwind23 : W.State
unwind23 = W.setShutdown wait (wrap F.abortGroup23)
unwind-edge23 : W.step (W.run (G.sampleAsyncTracer owner)) unwind22 ≡ just unwind23
unwind-edge23 = refl
unwind24 : W.State
unwind24 = W.setShutdown wait (wrap F.abortGroup24)
unwind-edge24 : W.step (W.run (G.commitAsyncTracer owner)) unwind23 ≡ just unwind24
unwind-edge24 = refl
unwind25 : W.State
unwind25 = W.setShutdown wait (wrap F.abortGroup25)
unwind-edge25 : W.step (W.run (G.finishAsyncDead owner)) unwind24 ≡ just unwind25
unwind-edge25 = refl
unwindActions : List W.Action
unwindActions = (W.run (G.beginWholeClose owner (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []))) ∷ (W.run (G.requestWholeCancel owner)) ∷ (W.run (G.finishChildUnwind Old.j₁₀)) ∷ (W.run (G.run (M.run (P.deregisterProtocol Old.j₁₀)))) ∷ (W.run (G.run (M.run (P.asyncProtocolResult Old.j₁₀)))) ∷ (W.run (G.joinWhole owner)) ∷ (W.run (G.requestWholeCancel owner)) ∷ (W.run (G.deliverWhole owner)) ∷ (W.run (G.finishChildUnwind Old.j₁)) ∷ (W.run (G.run (M.run (P.deregisterInfra owner T.demuxer)))) ∷ (W.run (G.run (M.run (P.asyncInfraResult owner T.demuxer)))) ∷ (W.run (G.joinWhole owner)) ∷ (W.run (G.requestWholeCancel owner)) ∷ (W.run (G.deliverWhole owner)) ∷ (W.run (G.finishChildUnwind Old.j₀)) ∷ (W.run (G.run (M.run (P.deregisterInfra owner T.muxer)))) ∷ (W.run (G.run (M.run (P.asyncInfraResult owner T.muxer)))) ∷ (W.run (G.joinWhole owner)) ∷ (W.run (G.finishWholeClose owner)) ∷ (W.run (G.writeAsyncFailure owner)) ∷ (W.run (G.beginAsyncDead owner)) ∷ (W.run (G.sampleAsyncTracer owner)) ∷ (W.run (G.commitAsyncTracer owner)) ∷ (W.run (G.finishAsyncDead owner)) ∷ []
unwindPath : W.Executes cm5 unwindActions unwind25
unwindPath = (W.next unwind-edge2 (W.next unwind-edge3 (W.next unwind-edge4 (W.next unwind-edge5 (W.next unwind-edge6 (W.next unwind-edge7 (W.next unwind-edge8 (W.next unwind-edge9 (W.next unwind-edge10 (W.next unwind-edge11 (W.next unwind-edge12 (W.next unwind-edge13 (W.next unwind-edge14 (W.next unwind-edge15 (W.next unwind-edge16 (W.next unwind-edge17 (W.next unwind-edge18 (W.next unwind-edge19 (W.next unwind-edge20 (W.next unwind-edge21 (W.next unwind-edge22 (W.next unwind-edge23 (W.next unwind-edge24 (W.next unwind-edge25 W.done))))))))))))))))))))))))
settled1 : W.State
settled1 = W.setShutdown wait async1
settled-edge1 : W.step (W.beginExit owner) unwind25 ≡ just settled1
settled-edge1 = refl
settled2 : W.State
settled2 = W.setShutdown wait async2
settled-edge2 : W.step (W.observeBufferReturn owner) settled1 ≡ just settled2
settled-edge2 = refl
settled3 : W.State
settled3 = W.setShutdown wait async3
settled-edge3 : W.step (W.enterFinalizer owner) settled2 ≡ just settled3
settled-edge3 = refl
settled4 : W.State
settled4 = W.setShutdown wait async4
settled-edge4 : W.step (W.cleanup owner C.takeCleanupMap) settled3 ≡ just settled4
settled-edge4 = refl
settled5 : W.State
settled5 = W.setShutdown wait async5
settled-edge5 : W.step (W.cleanup owner C.selectCleanupEntry) settled4 ≡ just settled5
settled-edge5 = refl
settled6 : W.State
settled6 = W.setShutdown wait async6
settled-edge6 : W.step (W.cleanup owner C.closeHandlerSocket) settled5 ≡ just settled6
settled-edge6 = refl
settled7 : W.State
settled7 = W.setShutdown wait async7
settled-edge7 : W.step (W.cleanup owner C.publishCleanupMap) settled6 ≡ just settled7
settled-edge7 = refl
settled8 : W.State
settled8 = W.setShutdown wait async8
settled-edge8 : W.step (W.cleanup owner C.readCleanupCounters) settled7 ≡ just settled8
settled-edge8 = refl
settled9 : W.State
settled9 = W.setShutdown wait async9
settled-edge9 : W.step (W.finishCleanup owner) settled8 ≡ just settled9
settled-edge9 = refl
settled10 : W.State
settled10 = W.setShutdown wait async10
settled-edge10 : W.step (W.publishAsyncResult owner) settled9 ≡ just settled10
settled-edge10 = refl
settledPath : W.Executes unwind25 asyncActions settled10
settledPath = (W.next settled-edge1 (W.next settled-edge2 (W.next settled-edge3 (W.next settled-edge4 (W.next settled-edge5 (W.next settled-edge6 (W.next settled-edge7 (W.next settled-edge8 (W.next settled-edge9 (W.next settled-edge10 W.done))))))))))
cmClosed : W.State
cmClosed = W.setShutdown (Close.shutdownState Close.closed (ident 0 ∷ []) [] (owner ∷ [])) settled10
cm-close : W.step (W.shutdownStep Close.finishClose) settled10 ≡ just cmClosed
cm-close = refl
no-close-before-result-publication : W.step (W.shutdownStep Close.finishClose) settled9 ≡ nothing
no-close-before-result-publication = refl
abstract
  initialized-cm-close : W.Executes (wrap (F.wrap (RF.wrap Old.b0)))
    ((((map W.run (actionsOf F.initialized-running) ++ map W.run F.normalPrefix7Actions) ++ cmActions) ++ unwindActions) ++ asyncActions ++ (W.shutdownStep Close.finishClose ∷ [])) cmClosed
  initialized-cm-close = append
    (append (append (append (append (lift-path F.initialized-running refl)
      (lift-path F.normalPrefix7 refl)) cmPath) unwindPath) settledPath)
    (W.next cm-close W.done)


cm-physical-wait : Facts.PhysicalWait settled10 cmClosed
cm-physical-wait = Facts.physical-wait-observation settled10 cm-close
cm-projection : Facts.Paths (wrap (F.wrap (RF.wrap Old.b0))) cmClosed
cm-projection = Facts.exec-projects initialized-cm-close
cm-supply : Supply.Valid (W.source cmClosed)
cm-supply = Facts.from-initial-supply actual-initializer Old.Prior.initial-bounds initialized-cm-close

-- Conditional TIME_WAIT fixture: this starts at an already-entered finalizer,
-- not at the source initializer. Delivery must still execute its finally write.
twCaptured : S.ConnectionState
twCaptured = S.terminating (S.handlerKey Old.Prior.captured) owner nothing
twWorld0 twWorld1 twWorld2 twWorld3 : S.State
twWorld0 = record (world0 F.normal30)
  { cm = record (S.cm (world0 F.normal30)) { entries = (ident 0 , twCaptured) ∷ [] }
  ; sockets = put Old.Fixture.sock S.closed (S.sockets (world0 F.normal30))
  ; cleanups = (owner , S.cleanupWaiting twCaptured) ∷ [] }
twWorld1 = record twWorld0 { cleanups = (owner , S.cleanupFinalize twCaptured (S.cleanupError err)) ∷ [] }
twWorld2 = record twWorld1
  { cm = record (S.cm twWorld1) { mapCell = S.full []; entries = (ident 0 , S.terminated nothing) ∷ [] }
  ; cleanups = (owner , S.cleanupCount (S.cleanupError err)) ∷ [] }
twWorld3 = record twWorld2 { cleanups = (owner , S.cleanupDone (S.cleanupError err)) ∷ [] }
twAt : W.Phase → S.State → W.State
twAt pc world = record (at F.normal30 pc world)
  { exits = (owner , W.exitFrame Old.Prior.captured pc (just (G.asyncExit err))) ∷ [] }
twReading : Close.State
twReading = Close.shutdownState Close.reading (ident 0 ∷ []) [] (owner ∷ [])
tw0 tw1 tw2 tw3 tw4 tw5 : W.State
tw0 = W.setShutdown (Close.shutdownState (Close.awaitDelivery (ident 0) owner) (ident 0 ∷ []) [] [])
  (at F.normal30 (W.finalizing W.returned) twWorld0)
tw1 = W.setShutdown twReading (twAt (W.finalizing W.returned) twWorld1)
tw2 = W.setShutdown twReading (twAt (W.finalizing W.returned) twWorld2)
tw3 = W.setShutdown twReading (twAt (W.finalizing W.returned) twWorld3)
tw4 = W.setShutdown twReading (twAt (W.cleanupComplete W.returned (S.cleanupError err)) twWorld3)
tw5 = W.setShutdown twReading (twAt (W.resultAvailable W.returned (S.cleanupError err)) twWorld3)
timewait-delivery : W.step (W.deliverShutdownTimeWait err) tw0 ≡ just tw1
timewait-delivery = refl
timewait-finally : W.step (W.cleanup owner C.finishTimeWait) tw1 ≡ just tw2
timewait-finally = refl
timewait-counters : W.step (W.cleanup owner C.readCleanupCounters) tw2 ≡ just tw3
timewait-counters = refl
timewait-finish : W.step (W.finishCleanup owner) tw3 ≡ just tw4
timewait-finish = refl
timewait-result : W.step (W.publishAsyncResult owner) tw4 ≡ just tw5
timewait-result = refl
timewait-keeps-async-result : W.resultOf owner tw5 ≡ just (W.asyncException err)
timewait-keeps-async-result = refl
no-timewait-result-before-finally : W.step (W.publishAsyncResult owner) tw1 ≡ nothing
no-timewait-result-before-finally = refl
