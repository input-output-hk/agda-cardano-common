{-# OPTIONS --guardedness #-}

-- Initialized physical result paths and explicitly marked conditional controls.
-- Finished means the monitor continuation returned, never a pool/handler join.
module ConnectionManagement.Negative.MuxResultMonitor where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _≟_)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (worker; job; mux)
open import ConnectionManagement.IGTypes using (clean; errored)
import ConnectionManagement.Machine as Machine
open import ConnectionManagement.Scenarios.Admission using (key₀)
open import ConnectionManagement.Store using (put; lookup)
import ConnectionManagement.MuxResultMonitor as Model
import ConnectionManagement.MuxProtocolJobs as P
import ConnectionManagement.Rules.MuxJobTypes as T
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.Negative.MuxProtocolJobs as Old
module Pool = P.Pool
module U = P.U
-- Fixture classifier: 999 represents a dynamically classified BearerClosed.
-- Production use must supply that source exception-classification contract.
bearerClosed : ErrorId → Bool
bearerClosed err = does (ErrorId.errorNumber err ≟ 999)
module W = Model bearerClosed
owner : WorkerId
owner = Old.owner
closedError : ErrorId
closedError = errorId 999

wrap : P.State → W.State
wrap p = W.monitorState p []
empty-allowed : ∀ a p → W.delegateAllowed a (wrap p) ≡ true
empty-allowed (P.run a) p = refl
empty-allowed (P.forkResponder w j r) p = refl
empty-allowed (P.forkInitiator w j r n) p = refl
empty-allowed (P.registerProtocol j) p = refl
empty-allowed (P.protocolReturned j) p = refl
empty-allowed (P.commitClean j) p = refl
empty-allowed (P.returnProtocol j) p = refl
empty-allowed (P.publishProtocol j) p = refl
empty-allowed (P.deregisterProtocol j) p = refl
empty-allowed (P.asyncProtocolResult j) p = refl
empty-allowed (P.protocolException j e) p = refl
empty-allowed (P.infrastructureReturn w r e) p = refl
empty-allowed (P.publishInfra w r) p = refl
empty-allowed (P.deregisterInfra w r) p = refl
empty-allowed (P.asyncInfraResult w r) p = refl
empty-allowed (P.control w a) p = refl
lift-step : ∀ a p {q} → P.step a p ≡ just q → W.step (W.run a) (wrap p) ≡ just (wrap q)
lift-step a p eq rewrite empty-allowed a p | eq = refl
lift-path : ∀ {p actions q} → P.Executes p actions q → W.Executes (wrap p) (map W.run actions) (wrap q)
lift-path P.done = W.done
lift-path (P.next {s = p} {a = a} eq path) = W.next (lift-step a p eq) (lift-path path)
actual-initializer : W.initial (O.initial Old.F.start) ≡ just (wrap Old.b0)
actual-initializer = refl
abstract
  initialized-clean-head : W.Executes (wrap Old.b0)
    (map W.run (Old.startActions ++ Old.responderPathActions)) (wrap Old.r13)
  initialized-clean-head = lift-path Old.initialized-fast-responder
  initialized-running : W.Executes (wrap Old.b0) (map W.run Old.startActions) (wrap Old.z12)
  initialized-running = lift-path Old.initialized-start

-- Flat constructors avoid repeatedly normalizing whole prior wrapper states.
traceQueue : Mux.Trace → Mux.Mux → List IG.IGEvent → List IG.IGEvent
traceQueue tr m q with Mux.traceSTM key₀ tr
  (IG.tracerView key₀ (Machine.inboundGovernor (O.core (Old.sourceMux m q)))) (Mux.traceCounters m) q
... | just (rc , output) = output
... | nothing = q

clean0 : W.State
clean0 = wrap Old.r13
clean1 : W.State
clean1 = (W.monitorState (Old.snapshot (Old.sourceMux Old.publishedMux Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , Old.rJob (T.resultCaptured clean)) ∷ []) ((owner , []) ∷ [])) ((owner , W.selected Old.rPayload) ∷ []))
clean-edge1 : W.step (W.consume owner) clean0 ≡ just clean1
clean-edge1 = refl
clean2 : W.State
clean2 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.publishedMux { completions = []; callback = Mux.readActive (Mux.completed 1 clean) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , Old.rJob (T.resultCaptured clean)) ∷ []) ((owner , []) ∷ [])) ((owner , W.responderTracing clean) ∷ []))
clean-edge2 : W.step (W.handleSelected owner) clean1 ≡ just clean2
clean-edge2 = refl
clean3 : W.State
clean3 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.publishedMux { completions = []; callback = Mux.commitTrace true (Mux.completed 1 clean) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , Old.rJob (T.resultCaptured clean)) ∷ []) ((owner , []) ∷ [])) ((owner , W.responderTracing clean) ∷ []))
clean-edge3 : W.step (W.sampleTracer owner) clean2 ≡ just clean3
clean-edge3 = refl
clean4 : W.State
clean4 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.publishedMux { completions = []; callback = Mux.returned; traceCounters = just (Mux.counters (+ 0) (+ 0)) }) (traceQueue (Mux.completed 1 clean) (record Old.publishedMux { completions = []; callback = Mux.commitTrace true (Mux.completed 1 clean) }) Old.messages)) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , Old.rJob (T.resultCaptured clean)) ∷ []) ((owner , []) ∷ [])) ((owner , W.responderTracing clean) ∷ []))
clean-edge4 : W.step (W.commitTracer owner) clean3 ≡ just clean4
clean-edge4 = refl
clean5 : W.State
clean5 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.publishedMux { completions = []; callback = Mux.returned; traceCounters = just (Mux.counters (+ 0) (+ 0)) }) (traceQueue (Mux.completed 1 clean) (record Old.publishedMux { completions = []; callback = Mux.commitTrace true (Mux.completed 1 clean) }) Old.messages)) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , Old.rJob (T.resultCaptured clean)) ∷ []) ((owner , []) ∷ [])) ((owner , W.waiting) ∷ []))
clean-edge5 : W.step (W.finishProtocolTrace owner) clean4 ≡ just clean5
clean-edge5 = refl
cleanActions : List W.Action
cleanActions = (W.consume owner) ∷ (W.handleSelected owner) ∷ (W.sampleTracer owner) ∷ (W.commitTracer owner) ∷ (W.finishProtocolTrace owner) ∷ []
cleanPath : W.Executes clean0 cleanActions clean5
cleanPath = W.next clean-edge1 (W.next clean-edge2 (W.next clean-edge3 (W.next clean-edge4 (W.next clean-edge5 (W.done)))))

error0 error1 error2 error3 error4 error5 error6 error7 : W.State
error0 = wrap Old.z12
error1 = wrap Old.r1
error2 = wrap Old.r2
error3 = wrap Old.r3
error4 = wrap Old.r4
error5 = wrap Old.r5
error6 = wrap Old.r6
error7 = wrap Old.x0
error-edge1 : W.step (W.run (P.control owner P.selectCommand)) error0 ≡ just error1
error-edge1 = lift-step (P.control owner P.selectCommand) Old.z12 Old.responder1
error-edge2 : W.step (W.run (P.control owner (P.demand 1))) error1 ≡ just error2
error-edge2 = lift-step (P.control owner (P.demand 1)) Old.r1 Old.responder2
error-edge3 : W.step (W.run (P.control owner P.sampleTracer)) error2 ≡ just error3
error-edge3 = lift-step (P.control owner P.sampleTracer) Old.r2 Old.responder3
error-edge4 : W.step (W.run (P.control owner P.commitTracer)) error3 ≡ just error4
error-edge4 = lift-step (P.control owner P.commitTracer) Old.r3 Old.responder4
error-edge5 : W.step (W.run (P.control owner P.finishStart)) error4 ≡ just error5
error-edge5 = lift-step (P.control owner P.finishStart) Old.r4 Old.responder5
error-edge6 : W.step (W.run (P.forkResponder owner Old.j₁₀ Old.r₀)) error5 ≡ just error6
error-edge6 = lift-step (P.forkResponder owner Old.j₁₀ Old.r₀) Old.r5 Old.responder6
error-edge7 : W.step (W.run (P.registerProtocol Old.j₁₀)) error6 ≡ just error7
error-edge7 = lift-step (P.registerProtocol Old.j₁₀) Old.r6 Old.cross0
errorPrefixActions : List W.Action
errorPrefixActions = (W.run (P.control owner P.selectCommand) ∷ W.run (P.control owner (P.demand 1)) ∷ W.run (P.control owner P.sampleTracer) ∷ W.run (P.control owner P.commitTracer) ∷ W.run (P.control owner P.finishStart) ∷ W.run (P.forkResponder owner Old.j₁₀ Old.r₀) ∷ W.run (P.registerProtocol Old.j₁₀) ∷ [])
errorPrefixPath : W.Executes error0 errorPrefixActions error7
errorPrefixPath = W.next error-edge1 (W.next error-edge2 (W.next error-edge3 (W.next error-edge4 (W.next error-edge5 (W.next error-edge6 (W.next error-edge7 (W.done)))))))

errorTail0 : W.State
errorTail0 = error7
errorTail1 : W.State
errorTail1 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) [])
errorTail-edge1 : W.step (W.run (P.protocolException Old.j₁₀ Old.err)) errorTail0 ≡ just errorTail1
errorTail-edge1 = refl
errorTail2 : W.State
errorTail2 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyReturned (T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err))) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) [])
errorTail-edge2 : W.step (W.run (P.returnProtocol Old.j₁₀)) errorTail1 ≡ just errorTail2
errorTail-edge2 = refl
errorTail3 : W.State
errorTail3 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) [])
errorTail-edge3 : W.step (W.run (P.publishProtocol Old.j₁₀)) errorTail2 ≡ just errorTail3
errorTail-edge3 = refl
errorTail4 : W.State
errorTail4 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) ((owner , W.selected (T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err))) ∷ []))
errorTail-edge4 : W.step (W.consume owner) errorTail3 ≡ just errorTail4
errorTail-edge4 = refl
errorTail5 : W.State
errorTail5 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; completions = []; callback = Mux.readActive (Mux.completed 1 (errored Old.err)); status = Mux.failed Old.err }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) ((owner , W.responderTracing (errored Old.err)) ∷ []))
errorTail-edge5 : W.step (W.handleSelected owner) errorTail4 ≡ just errorTail5
errorTail-edge5 = refl
errorTail6 : W.State
errorTail6 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; completions = []; callback = Mux.commitTrace true (Mux.completed 1 (errored Old.err)); status = Mux.failed Old.err }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) ((owner , W.responderTracing (errored Old.err)) ∷ []))
errorTail-edge6 : W.step (W.sampleTracer owner) errorTail5 ≡ just errorTail6
errorTail-edge6 = refl
errorTail7 : W.State
errorTail7 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; completions = []; callback = Mux.afterFailure; status = Mux.failed Old.err; traceCounters = nothing }) (traceQueue (Mux.completed 1 (errored Old.err)) (record Old.m6 { runningJobs = []; finishedJobs = []; completions = []; callback = Mux.commitTrace true (Mux.completed 1 (errored Old.err)); status = Mux.failed Old.err }) Old.messages)) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) ((owner , W.responderTracing (errored Old.err)) ∷ []))
errorTail-edge7 : W.step (W.commitTracer owner) errorTail6 ≡ just errorTail7
errorTail-edge7 = refl
errorTail8 : W.State
errorTail8 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; completions = []; callback = Mux.afterFailure; status = Mux.failed Old.err; traceCounters = nothing }) (traceQueue (Mux.completed 1 (errored Old.err)) (record Old.m6 { runningJobs = []; finishedJobs = []; completions = []; callback = Mux.commitTrace true (Mux.completed 1 (errored Old.err)); status = Mux.failed Old.err }) Old.messages)) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) ((owner , W.deadReady (W.failed Old.err)) ∷ []))
errorTail-edge8 : W.step (W.finishProtocolTrace owner) errorTail7 ≡ just errorTail8
errorTail-edge8 = refl
errorTail9 : W.State
errorTail9 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; completions = []; callback = Mux.readActive Mux.muxStopped; status = Mux.failed Old.err; traceCounters = nothing }) (traceQueue (Mux.completed 1 (errored Old.err)) (record Old.m6 { runningJobs = []; finishedJobs = []; completions = []; callback = Mux.commitTrace true (Mux.completed 1 (errored Old.err)); status = Mux.failed Old.err }) Old.messages)) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) ((owner , W.deadTracing (W.failed Old.err)) ∷ []))
errorTail-edge9 : W.step (W.beginDead owner) errorTail8 ≡ just errorTail9
errorTail-edge9 = refl
errorTail10 : W.State
errorTail10 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; completions = []; callback = Mux.commitTrace true Mux.muxStopped; status = Mux.failed Old.err; traceCounters = nothing }) (traceQueue (Mux.completed 1 (errored Old.err)) (record Old.m6 { runningJobs = []; finishedJobs = []; completions = []; callback = Mux.commitTrace true (Mux.completed 1 (errored Old.err)); status = Mux.failed Old.err }) Old.messages)) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) ((owner , W.deadTracing (W.failed Old.err)) ∷ []))
errorTail-edge10 : W.step (W.sampleTracer owner) errorTail9 ≡ just errorTail10
errorTail-edge10 = refl
errorTail11 : W.State
errorTail11 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; completions = []; callback = Mux.returned; status = Mux.failed Old.err; traceCounters = nothing }) (traceQueue Mux.muxStopped (record Old.m6 { runningJobs = []; finishedJobs = []; completions = []; callback = Mux.commitTrace true Mux.muxStopped; status = Mux.failed Old.err; traceCounters = nothing }) (traceQueue (Mux.completed 1 (errored Old.err)) (record Old.m6 { runningJobs = []; finishedJobs = []; completions = []; callback = Mux.commitTrace true (Mux.completed 1 (errored Old.err)); status = Mux.failed Old.err }) Old.messages))) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) ((owner , W.deadTracing (W.failed Old.err)) ∷ []))
errorTail-edge11 : W.step (W.commitTracer owner) errorTail10 ≡ just errorTail11
errorTail-edge11 = refl
errorTail12 : W.State
errorTail12 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; completions = []; callback = Mux.returned; status = Mux.failed Old.err; traceCounters = nothing }) (traceQueue Mux.muxStopped (record Old.m6 { runningJobs = []; finishedJobs = []; completions = []; callback = Mux.commitTrace true Mux.muxStopped; status = Mux.failed Old.err; traceCounters = nothing }) (traceQueue (Mux.completed 1 (errored Old.err)) (record Old.m6 { runningJobs = []; finishedJobs = []; completions = []; callback = Mux.commitTrace true (Mux.completed 1 (errored Old.err)); status = Mux.failed Old.err }) Old.messages))) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) ((owner , W.finished (W.failed Old.err)) ∷ []))
errorTail-edge12 : W.step (W.finishDead owner) errorTail11 ≡ just errorTail12
errorTail-edge12 = refl
errorTailActions : List W.Action
errorTailActions = (W.run (P.protocolException Old.j₁₀ Old.err)) ∷ (W.run (P.returnProtocol Old.j₁₀)) ∷ (W.run (P.publishProtocol Old.j₁₀)) ∷ (W.consume owner) ∷ (W.handleSelected owner) ∷ (W.sampleTracer owner) ∷ (W.commitTracer owner) ∷ (W.finishProtocolTrace owner) ∷ (W.beginDead owner) ∷ (W.sampleTracer owner) ∷ (W.commitTracer owner) ∷ (W.finishDead owner) ∷ []
errorTailPath : W.Executes errorTail0 errorTailActions errorTail12
errorTailPath = W.next errorTail-edge1 (W.next errorTail-edge2 (W.next errorTail-edge3 (W.next errorTail-edge4 (W.next errorTail-edge5 (W.next errorTail-edge6 (W.next errorTail-edge7 (W.next errorTail-edge8 (W.next errorTail-edge9 (W.next errorTail-edge10 (W.next errorTail-edge11 (W.next errorTail-edge12 (W.done))))))))))))

initiatorClean0 : W.State
initiatorClean0 = error7
initiatorClean1 : W.State
initiatorClean1 = (W.monitorState (Old.snapshot (Old.sourceMux Old.m6 Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ (Old.j₁₁ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (just Old.j₁₁) Pool.openPool [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ (Old.j₁₁ , Old.iJob Old.r₁ T.executing) ∷ []) []) [])
initiatorClean-edge1 : W.step (W.run (P.forkInitiator owner Old.j₁₁ Old.r₁ 1)) initiatorClean0 ≡ just initiatorClean1
initiatorClean-edge1 = refl
initiatorClean2 : W.State
initiatorClean2 = (W.monitorState (Old.snapshot (Old.sourceMux Old.m6 Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ (Old.j₁₁ , Pool.bodyRunning) ∷ []) (Old.j₁₁ ∷ Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ (Old.j₁₁ , Old.iJob Old.r₁ T.executing) ∷ []) []) [])
initiatorClean-edge2 : W.step (W.run (P.registerProtocol Old.j₁₁)) initiatorClean1 ≡ just initiatorClean2
initiatorClean-edge2 = refl
initiatorClean3 : W.State
initiatorClean3 = (W.monitorState (Old.snapshot (Old.sourceMux Old.m6 Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ (Old.j₁₁ , Pool.bodyRunning) ∷ []) (Old.j₁₁ ∷ Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ (Old.j₁₁ , (T.protocolJob owner Old.mid Mux.initiatorJob 1 Old.r₁ (T.waitingEgress))) ∷ []) []) [])
initiatorClean-edge3 : W.step (W.run (P.protocolReturned Old.j₁₁)) initiatorClean2 ≡ just initiatorClean3
initiatorClean-edge3 = refl
initiatorClean4 : W.State
initiatorClean4 = (W.monitorState (Old.snapshot (Old.sourceMux Old.m6 Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ (Old.j₁₁ , Pool.bodyRunning) ∷ []) (Old.j₁₁ ∷ Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ (Old.j₁₁ , (T.protocolJob owner Old.mid Mux.initiatorJob 1 Old.r₁ (T.resultCaptured clean))) ∷ []) []) [])
initiatorClean-edge4 : W.step (W.run (P.commitClean Old.j₁₁)) initiatorClean3 ≡ just initiatorClean4
initiatorClean-edge4 = refl
initiatorClean5 : W.State
initiatorClean5 = (W.monitorState (Old.snapshot (Old.sourceMux Old.m6 Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ (Old.j₁₁ , Pool.bodyReturned (T.protocolCompletion Mux.initiatorJob 1 Old.r₁ clean)) ∷ []) (Old.j₁₁ ∷ Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ (Old.j₁₁ , (T.protocolJob owner Old.mid Mux.initiatorJob 1 Old.r₁ (T.resultCaptured clean))) ∷ []) []) [])
initiatorClean-edge5 : W.step (W.run (P.returnProtocol Old.j₁₁)) initiatorClean4 ≡ just initiatorClean5
initiatorClean-edge5 = refl
initiatorClean6 : W.State
initiatorClean6 = (W.monitorState (Old.snapshot (Old.sourceMux Old.m6 Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ (Old.j₁₁ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁₁ ∷ Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] ((T.protocolCompletion Mux.initiatorJob 1 Old.r₁ clean) ∷ [])) ((Old.j₁₀ , Old.rJob T.executing) ∷ (Old.j₁₁ , (T.protocolJob owner Old.mid Mux.initiatorJob 1 Old.r₁ (T.resultCaptured clean))) ∷ []) []) [])
initiatorClean-edge6 : W.step (W.run (P.publishProtocol Old.j₁₁)) initiatorClean5 ≡ just initiatorClean6
initiatorClean-edge6 = refl
initiatorClean7 : W.State
initiatorClean7 = (W.monitorState (Old.snapshot (Old.sourceMux Old.m6 Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ (Old.j₁₁ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁₁ ∷ Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ (Old.j₁₁ , (T.protocolJob owner Old.mid Mux.initiatorJob 1 Old.r₁ (T.resultCaptured clean))) ∷ []) []) ((owner , W.selected (T.protocolCompletion Mux.initiatorJob 1 Old.r₁ clean)) ∷ []))
initiatorClean-edge7 : W.step (W.consume owner) initiatorClean6 ≡ just initiatorClean7
initiatorClean-edge7 = refl
initiatorClean8 : W.State
initiatorClean8 = (W.monitorState (Old.snapshot (Old.sourceMux Old.m6 Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ (Old.j₁₁ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁₁ ∷ Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ (Old.j₁₁ , (T.protocolJob owner Old.mid Mux.initiatorJob 1 Old.r₁ (T.resultCaptured clean))) ∷ []) []) ((owner , W.initiatorTracing clean) ∷ []))
initiatorClean-edge8 : W.step (W.handleSelected owner) initiatorClean7 ≡ just initiatorClean8
initiatorClean-edge8 = refl
initiatorClean9 : W.State
initiatorClean9 = (W.monitorState (Old.snapshot (Old.sourceMux Old.m6 Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ (Old.j₁₁ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁₁ ∷ Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ (Old.j₁₁ , (T.protocolJob owner Old.mid Mux.initiatorJob 1 Old.r₁ (T.resultCaptured clean))) ∷ []) []) ((owner , W.waiting) ∷ []))
initiatorClean-edge9 : W.step (W.finishProtocolTrace owner) initiatorClean8 ≡ just initiatorClean9
initiatorClean-edge9 = refl
initiatorCleanActions : List W.Action
initiatorCleanActions = (W.run (P.forkInitiator owner Old.j₁₁ Old.r₁ 1)) ∷ (W.run (P.registerProtocol Old.j₁₁)) ∷ (W.run (P.protocolReturned Old.j₁₁)) ∷ (W.run (P.commitClean Old.j₁₁)) ∷ (W.run (P.returnProtocol Old.j₁₁)) ∷ (W.run (P.publishProtocol Old.j₁₁)) ∷ (W.consume owner) ∷ (W.handleSelected owner) ∷ (W.finishProtocolTrace owner) ∷ []
initiatorCleanPath : W.Executes initiatorClean0 initiatorCleanActions initiatorClean9
initiatorCleanPath = W.next initiatorClean-edge1 (W.next initiatorClean-edge2 (W.next initiatorClean-edge3 (W.next initiatorClean-edge4 (W.next initiatorClean-edge5 (W.next initiatorClean-edge6 (W.next initiatorClean-edge7 (W.next initiatorClean-edge8 (W.next initiatorClean-edge9 (W.done)))))))))

initiatorError0 : W.State
initiatorError0 = error7
initiatorError1 : W.State
initiatorError1 = (W.monitorState (Old.snapshot (Old.sourceMux Old.m6 Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ (Old.j₁₁ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) (just Old.j₁₁) Pool.openPool [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ (Old.j₁₁ , Old.iJob Old.r₁ T.executing) ∷ []) []) [])
initiatorError-edge1 : W.step (W.run (P.forkInitiator owner Old.j₁₁ Old.r₁ 1)) initiatorError0 ≡ just initiatorError1
initiatorError-edge1 = refl
initiatorError2 : W.State
initiatorError2 = (W.monitorState (Old.snapshot (Old.sourceMux Old.m6 Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ (Old.j₁₁ , Pool.bodyRunning) ∷ []) (Old.j₁₁ ∷ Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ (Old.j₁₁ , Old.iJob Old.r₁ T.executing) ∷ []) []) [])
initiatorError-edge2 : W.step (W.run (P.registerProtocol Old.j₁₁)) initiatorError1 ≡ just initiatorError2
initiatorError-edge2 = refl
initiatorError3 : W.State
initiatorError3 = (W.monitorState (Old.snapshot (Old.sourceMux Old.m6 Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ (Old.j₁₁ , Pool.bodyRunning) ∷ []) (Old.j₁₁ ∷ Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ (Old.j₁₁ , (T.protocolJob owner Old.mid Mux.initiatorJob 1 Old.r₁ (T.resultCaptured (errored Old.err)))) ∷ []) []) [])
initiatorError-edge3 : W.step (W.run (P.protocolException Old.j₁₁ Old.err)) initiatorError2 ≡ just initiatorError3
initiatorError-edge3 = refl
initiatorError4 : W.State
initiatorError4 = (W.monitorState (Old.snapshot (Old.sourceMux Old.m6 Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ (Old.j₁₁ , Pool.bodyReturned (T.protocolCompletion Mux.initiatorJob 1 Old.r₁ (errored Old.err))) ∷ []) (Old.j₁₁ ∷ Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ (Old.j₁₁ , (T.protocolJob owner Old.mid Mux.initiatorJob 1 Old.r₁ (T.resultCaptured (errored Old.err)))) ∷ []) []) [])
initiatorError-edge4 : W.step (W.run (P.returnProtocol Old.j₁₁)) initiatorError3 ≡ just initiatorError4
initiatorError-edge4 = refl
initiatorError5 : W.State
initiatorError5 = (W.monitorState (Old.snapshot (Old.sourceMux Old.m6 Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ (Old.j₁₁ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁₁ ∷ Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] ((T.protocolCompletion Mux.initiatorJob 1 Old.r₁ (errored Old.err)) ∷ [])) ((Old.j₁₀ , Old.rJob T.executing) ∷ (Old.j₁₁ , (T.protocolJob owner Old.mid Mux.initiatorJob 1 Old.r₁ (T.resultCaptured (errored Old.err)))) ∷ []) []) [])
initiatorError-edge5 : W.step (W.run (P.publishProtocol Old.j₁₁)) initiatorError4 ≡ just initiatorError5
initiatorError-edge5 = refl
initiatorError6 : W.State
initiatorError6 = (W.monitorState (Old.snapshot (Old.sourceMux Old.m6 Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ (Old.j₁₁ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁₁ ∷ Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ (Old.j₁₁ , (T.protocolJob owner Old.mid Mux.initiatorJob 1 Old.r₁ (T.resultCaptured (errored Old.err)))) ∷ []) []) ((owner , W.selected (T.protocolCompletion Mux.initiatorJob 1 Old.r₁ (errored Old.err))) ∷ []))
initiatorError-edge6 : W.step (W.consume owner) initiatorError5 ≡ just initiatorError6
initiatorError-edge6 = refl
initiatorError7 : W.State
initiatorError7 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { status = Mux.failed Old.err }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ (Old.j₁₁ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁₁ ∷ Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ (Old.j₁₁ , (T.protocolJob owner Old.mid Mux.initiatorJob 1 Old.r₁ (T.resultCaptured (errored Old.err)))) ∷ []) []) ((owner , W.initiatorTracing (errored Old.err)) ∷ []))
initiatorError-edge7 : W.step (W.handleSelected owner) initiatorError6 ≡ just initiatorError7
initiatorError-edge7 = refl
initiatorError8 : W.State
initiatorError8 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { status = Mux.failed Old.err }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ (Old.j₁₁ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁₁ ∷ Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ (Old.j₁₁ , (T.protocolJob owner Old.mid Mux.initiatorJob 1 Old.r₁ (T.resultCaptured (errored Old.err)))) ∷ []) []) ((owner , W.deadReady (W.failed Old.err)) ∷ []))
initiatorError-edge8 : W.step (W.finishProtocolTrace owner) initiatorError7 ≡ just initiatorError8
initiatorError-edge8 = refl
initiatorError9 : W.State
initiatorError9 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { status = Mux.failed Old.err; callback = Mux.readActive Mux.muxStopped }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ (Old.j₁₁ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁₁ ∷ Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ (Old.j₁₁ , (T.protocolJob owner Old.mid Mux.initiatorJob 1 Old.r₁ (T.resultCaptured (errored Old.err)))) ∷ []) []) ((owner , W.deadTracing (W.failed Old.err)) ∷ []))
initiatorError-edge9 : W.step (W.beginDead owner) initiatorError8 ≡ just initiatorError9
initiatorError-edge9 = refl
initiatorError10 : W.State
initiatorError10 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { status = Mux.failed Old.err; callback = Mux.commitTrace true Mux.muxStopped }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ (Old.j₁₁ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁₁ ∷ Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ (Old.j₁₁ , (T.protocolJob owner Old.mid Mux.initiatorJob 1 Old.r₁ (T.resultCaptured (errored Old.err)))) ∷ []) []) ((owner , W.deadTracing (W.failed Old.err)) ∷ []))
initiatorError-edge10 : W.step (W.sampleTracer owner) initiatorError9 ≡ just initiatorError10
initiatorError-edge10 = refl
initiatorError11 : W.State
initiatorError11 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { status = Mux.failed Old.err; callback = Mux.returned; traceCounters = nothing }) (traceQueue Mux.muxStopped (record Old.m6 { status = Mux.failed Old.err; callback = Mux.commitTrace true Mux.muxStopped }) Old.messages)) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ (Old.j₁₁ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁₁ ∷ Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ (Old.j₁₁ , (T.protocolJob owner Old.mid Mux.initiatorJob 1 Old.r₁ (T.resultCaptured (errored Old.err)))) ∷ []) []) ((owner , W.deadTracing (W.failed Old.err)) ∷ []))
initiatorError-edge11 : W.step (W.commitTracer owner) initiatorError10 ≡ just initiatorError11
initiatorError-edge11 = refl
initiatorError12 : W.State
initiatorError12 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { status = Mux.failed Old.err; callback = Mux.returned; traceCounters = nothing }) (traceQueue Mux.muxStopped (record Old.m6 { status = Mux.failed Old.err; callback = Mux.commitTrace true Mux.muxStopped }) Old.messages)) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ (Old.j₁₁ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁₁ ∷ Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , Old.rJob T.executing) ∷ (Old.j₁₁ , (T.protocolJob owner Old.mid Mux.initiatorJob 1 Old.r₁ (T.resultCaptured (errored Old.err)))) ∷ []) []) ((owner , W.finished (W.failed Old.err)) ∷ []))
initiatorError-edge12 : W.step (W.finishDead owner) initiatorError11 ≡ just initiatorError12
initiatorError-edge12 = refl
initiatorErrorActions : List W.Action
initiatorErrorActions = (W.run (P.forkInitiator owner Old.j₁₁ Old.r₁ 1)) ∷ (W.run (P.registerProtocol Old.j₁₁)) ∷ (W.run (P.protocolException Old.j₁₁ Old.err)) ∷ (W.run (P.returnProtocol Old.j₁₁)) ∷ (W.run (P.publishProtocol Old.j₁₁)) ∷ (W.consume owner) ∷ (W.handleSelected owner) ∷ (W.finishProtocolTrace owner) ∷ (W.beginDead owner) ∷ (W.sampleTracer owner) ∷ (W.commitTracer owner) ∷ (W.finishDead owner) ∷ []
initiatorErrorPath : W.Executes initiatorError0 initiatorErrorActions initiatorError12
initiatorErrorPath = W.next initiatorError-edge1 (W.next initiatorError-edge2 (W.next initiatorError-edge3 (W.next initiatorError-edge4 (W.next initiatorError-edge5 (W.next initiatorError-edge6 (W.next initiatorError-edge7 (W.next initiatorError-edge8 (W.next initiatorError-edge9 (W.next initiatorError-edge10 (W.next initiatorError-edge11 (W.next initiatorError-edge12 (W.done))))))))))))

muxer0 : W.State
muxer0 = wrap Old.z12
muxer1 : W.State
muxer1 = (W.monitorState (Old.snapshot (Old.sourceMux Old.G.armedMux []) (Pool.poolState ((Old.j₀ , Pool.bodyReturned (T.infraMuxer Old.err)) ∷ (Old.j₁ , Pool.bodyRunning) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) [] []) [])
muxer-edge1 : W.step (W.run (P.infrastructureReturn owner T.muxer Old.err)) muxer0 ≡ just muxer1
muxer-edge1 = refl
muxer2 : W.State
muxer2 = (W.monitorState (Old.snapshot (Old.sourceMux Old.G.armedMux []) (Pool.poolState ((Old.j₀ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁ , Pool.bodyRunning) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] ((T.infraMuxer Old.err) ∷ [])) [] []) [])
muxer-edge2 : W.step (W.run (P.publishInfra owner T.muxer)) muxer1 ≡ just muxer2
muxer-edge2 = refl
muxer3 : W.State
muxer3 = (W.monitorState (Old.snapshot (Old.sourceMux Old.G.armedMux []) (Pool.poolState ((Old.j₀ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁ , Pool.bodyRunning) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) [] []) ((owner , W.selected (T.infraMuxer Old.err)) ∷ []))
muxer-edge3 : W.step (W.consume owner) muxer2 ≡ just muxer3
muxer-edge3 = refl
muxer4 : W.State
muxer4 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.G.armedMux { status = Mux.failed Old.err }) []) (Pool.poolState ((Old.j₀ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁ , Pool.bodyRunning) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) [] []) ((owner , W.deadReady (W.failed Old.err)) ∷ []))
muxer-edge4 : W.step (W.handleSelected owner) muxer3 ≡ just muxer4
muxer-edge4 = refl
muxer5 : W.State
muxer5 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.G.armedMux { status = Mux.failed Old.err; callback = Mux.readActive Mux.muxStopped }) []) (Pool.poolState ((Old.j₀ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁ , Pool.bodyRunning) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) [] []) ((owner , W.deadTracing (W.failed Old.err)) ∷ []))
muxer-edge5 : W.step (W.beginDead owner) muxer4 ≡ just muxer5
muxer-edge5 = refl
muxer6 : W.State
muxer6 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.G.armedMux { status = Mux.failed Old.err; callback = Mux.commitTrace true Mux.muxStopped }) []) (Pool.poolState ((Old.j₀ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁ , Pool.bodyRunning) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) [] []) ((owner , W.deadTracing (W.failed Old.err)) ∷ []))
muxer-edge6 : W.step (W.sampleTracer owner) muxer5 ≡ just muxer6
muxer-edge6 = refl
muxer7 : W.State
muxer7 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.G.armedMux { status = Mux.failed Old.err; callback = Mux.returned; traceCounters = nothing }) (traceQueue Mux.muxStopped (record Old.G.armedMux { status = Mux.failed Old.err; callback = Mux.commitTrace true Mux.muxStopped }) [])) (Pool.poolState ((Old.j₀ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁ , Pool.bodyRunning) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) [] []) ((owner , W.deadTracing (W.failed Old.err)) ∷ []))
muxer-edge7 : W.step (W.commitTracer owner) muxer6 ≡ just muxer7
muxer-edge7 = refl
muxer8 : W.State
muxer8 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.G.armedMux { status = Mux.failed Old.err; callback = Mux.returned; traceCounters = nothing }) (traceQueue Mux.muxStopped (record Old.G.armedMux { status = Mux.failed Old.err; callback = Mux.commitTrace true Mux.muxStopped }) [])) (Pool.poolState ((Old.j₀ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁ , Pool.bodyRunning) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) [] []) ((owner , W.finished (W.failed Old.err)) ∷ []))
muxer-edge8 : W.step (W.finishDead owner) muxer7 ≡ just muxer8
muxer-edge8 = refl
muxerActions : List W.Action
muxerActions = (W.run (P.infrastructureReturn owner T.muxer Old.err)) ∷ (W.run (P.publishInfra owner T.muxer)) ∷ (W.consume owner) ∷ (W.handleSelected owner) ∷ (W.beginDead owner) ∷ (W.sampleTracer owner) ∷ (W.commitTracer owner) ∷ (W.finishDead owner) ∷ []
muxerPath : W.Executes muxer0 muxerActions muxer8
muxerPath = W.next muxer-edge1 (W.next muxer-edge2 (W.next muxer-edge3 (W.next muxer-edge4 (W.next muxer-edge5 (W.next muxer-edge6 (W.next muxer-edge7 (W.next muxer-edge8 (W.done))))))))

demux0 : W.State
demux0 = wrap Old.z12
demux1 : W.State
demux1 = (W.monitorState (Old.snapshot (Old.sourceMux Old.G.armedMux []) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyReturned (T.infraDemuxer closedError)) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) [] []) [])
demux-edge1 : W.step (W.run (P.infrastructureReturn owner T.demuxer closedError)) demux0 ≡ just demux1
demux-edge1 = refl
demux2 : W.State
demux2 = (W.monitorState (Old.snapshot (Old.sourceMux Old.G.armedMux []) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] ((T.infraDemuxer closedError) ∷ [])) [] []) [])
demux-edge2 : W.step (W.run (P.publishInfra owner T.demuxer)) demux1 ≡ just demux2
demux-edge2 = refl
demux3 : W.State
demux3 = (W.monitorState (Old.snapshot (Old.sourceMux Old.G.armedMux []) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) [] []) ((owner , W.selected (T.infraDemuxer closedError)) ∷ []))
demux-edge3 : W.step (W.consume owner) demux2 ≡ just demux3
demux-edge3 = refl
demux4 : W.State
demux4 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.G.armedMux { status = Mux.stopped }) []) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) [] []) ((owner , W.deadReady W.normal) ∷ []))
demux-edge4 : W.step (W.handleSelected owner) demux3 ≡ just demux4
demux-edge4 = refl
demux5 : W.State
demux5 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.G.armedMux { status = Mux.stopped; callback = Mux.readActive Mux.muxStopped }) []) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) [] []) ((owner , W.deadTracing W.normal) ∷ []))
demux-edge5 : W.step (W.beginDead owner) demux4 ≡ just demux5
demux-edge5 = refl
demux6 : W.State
demux6 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.G.armedMux { status = Mux.stopped; callback = Mux.commitTrace true Mux.muxStopped }) []) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) [] []) ((owner , W.deadTracing W.normal) ∷ []))
demux-edge6 : W.step (W.sampleTracer owner) demux5 ≡ just demux6
demux-edge6 = refl
demux7 : W.State
demux7 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.G.armedMux { status = Mux.stopped; callback = Mux.returned; traceCounters = nothing }) (traceQueue Mux.muxStopped (record Old.G.armedMux { status = Mux.stopped; callback = Mux.commitTrace true Mux.muxStopped }) [])) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) [] []) ((owner , W.deadTracing W.normal) ∷ []))
demux-edge7 : W.step (W.commitTracer owner) demux6 ≡ just demux7
demux-edge7 = refl
demux8 : W.State
demux8 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.G.armedMux { status = Mux.stopped; callback = Mux.returned; traceCounters = nothing }) (traceQueue Mux.muxStopped (record Old.G.armedMux { status = Mux.stopped; callback = Mux.commitTrace true Mux.muxStopped }) [])) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) [] []) ((owner , W.finished W.normal) ∷ []))
demux-edge8 : W.step (W.finishDead owner) demux7 ≡ just demux8
demux-edge8 = refl
demuxActions : List W.Action
demuxActions = (W.run (P.infrastructureReturn owner T.demuxer closedError)) ∷ (W.run (P.publishInfra owner T.demuxer)) ∷ (W.consume owner) ∷ (W.handleSelected owner) ∷ (W.beginDead owner) ∷ (W.sampleTracer owner) ∷ (W.commitTracer owner) ∷ (W.finishDead owner) ∷ []
demuxPath : W.Executes demux0 demuxActions demux8
demuxPath = W.next demux-edge1 (W.next demux-edge2 (W.next demux-edge3 (W.next demux-edge4 (W.next demux-edge5 (W.next demux-edge6 (W.next demux-edge7 (W.next demux-edge8 (W.done))))))))

race0 : W.State
race0 = error7
race1 : W.State
race1 = (W.monitorState (Old.snapshot (Old.sourceMux Old.m6 Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.waitingEgress))) ∷ []) []) [])
race-edge1 : W.step (W.run (P.protocolReturned Old.j₁₀)) race0 ≡ just race1
race-edge1 = refl
race2 : W.State
race2 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , clean) ∷ []); protocols = ((1 , Mux.idle) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) [])
race-edge2 : W.step (W.run (P.commitClean Old.j₁₀)) race1 ≡ just race2
race-edge2 = refl
race3 : W.State
race3 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , clean) ∷ []); protocols = ((1 , Mux.idle) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyReturned (T.infraDemuxer closedError)) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) [])
race-edge3 : W.step (W.run (P.infrastructureReturn owner T.demuxer closedError)) race2 ≡ just race3
race-edge3 = refl
race4 : W.State
race4 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , clean) ∷ []); protocols = ((1 , Mux.idle) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] ((T.infraDemuxer closedError) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) [])
race-edge4 : W.step (W.run (P.publishInfra owner T.demuxer)) race3 ≡ just race4
race-edge4 = refl
race5 : W.State
race5 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , clean) ∷ []); protocols = ((1 , Mux.idle) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) ((owner , W.selected (T.infraDemuxer closedError)) ∷ []))
race-edge5 : W.step (W.consume owner) race4 ≡ just race5
race-edge5 = refl
race6 : W.State
race6 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , clean) ∷ []); protocols = ((1 , Mux.idle) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁₀ , Pool.bodyReturned (T.protocolCompletion Mux.responderJob 1 Old.r₀ clean)) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) ((owner , W.selected (T.infraDemuxer closedError)) ∷ []))
race-edge6 : W.step (W.run (P.returnProtocol Old.j₁₀)) race5 ≡ just race6
race-edge6 = refl
race7 : W.State
race7 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; protocols = ((1 , Mux.idle) ∷ []); completions = ((Mux.jobResult Mux.responderJob 1 clean) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁₀ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ clean) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , []) ∷ [])) ((owner , W.selected (T.infraDemuxer closedError)) ∷ []))
race-edge7 : W.step (W.run (P.publishProtocol Old.j₁₀)) race6 ≡ just race7
race-edge7 = refl
race8 : W.State
race8 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; protocols = ((1 , Mux.idle) ∷ []); completions = ((Mux.jobResult Mux.responderJob 1 clean) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁₀ , Pool.deregistered Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ clean) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , []) ∷ [])) ((owner , W.selected (T.infraDemuxer closedError)) ∷ []))
race-edge8 : W.step (W.run (P.deregisterProtocol Old.j₁₀)) race7 ≡ just race8
race-edge8 = refl
race9 : W.State
race9 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; protocols = ((1 , Mux.idle) ∷ []); completions = ((Mux.jobResult Mux.responderJob 1 clean) ∷ []); status = Mux.stopped }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁₀ , Pool.deregistered Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ clean) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , []) ∷ [])) ((owner , W.deadReady W.normal) ∷ []))
race-edge9 : W.step (W.handleSelected owner) race8 ≡ just race9
race-edge9 = refl
race10 : W.State
race10 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; protocols = ((1 , Mux.idle) ∷ []); completions = ((Mux.jobResult Mux.responderJob 1 clean) ∷ []); status = Mux.stopped; callback = Mux.readActive Mux.muxStopped }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁₀ , Pool.deregistered Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ clean) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , []) ∷ [])) ((owner , W.deadTracing W.normal) ∷ []))
race-edge10 : W.step (W.beginDead owner) race9 ≡ just race10
race-edge10 = refl
race11 : W.State
race11 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; protocols = ((1 , Mux.idle) ∷ []); completions = ((Mux.jobResult Mux.responderJob 1 clean) ∷ []); status = Mux.stopped; callback = Mux.commitTrace true Mux.muxStopped }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁₀ , Pool.deregistered Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ clean) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , []) ∷ [])) ((owner , W.deadTracing W.normal) ∷ []))
race-edge11 : W.step (W.sampleTracer owner) race10 ≡ just race11
race-edge11 = refl
race12 : W.State
race12 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; protocols = ((1 , Mux.idle) ∷ []); completions = ((Mux.jobResult Mux.responderJob 1 clean) ∷ []); status = Mux.stopped; callback = Mux.returned; traceCounters = nothing }) (traceQueue Mux.muxStopped (record Old.m6 { runningJobs = []; finishedJobs = []; protocols = ((1 , Mux.idle) ∷ []); completions = ((Mux.jobResult Mux.responderJob 1 clean) ∷ []); status = Mux.stopped; callback = Mux.commitTrace true Mux.muxStopped }) Old.messages)) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁₀ , Pool.deregistered Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ clean) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , []) ∷ [])) ((owner , W.deadTracing W.normal) ∷ []))
race-edge12 : W.step (W.commitTracer owner) race11 ≡ just race12
race-edge12 = refl
race13 : W.State
race13 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; protocols = ((1 , Mux.idle) ∷ []); completions = ((Mux.jobResult Mux.responderJob 1 clean) ∷ []); status = Mux.stopped; callback = Mux.returned; traceCounters = nothing }) (traceQueue Mux.muxStopped (record Old.m6 { runningJobs = []; finishedJobs = []; protocols = ((1 , Mux.idle) ∷ []); completions = ((Mux.jobResult Mux.responderJob 1 clean) ∷ []); status = Mux.stopped; callback = Mux.commitTrace true Mux.muxStopped }) Old.messages)) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁₀ , Pool.deregistered Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ clean) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , []) ∷ [])) ((owner , W.finished W.normal) ∷ []))
race-edge13 : W.step (W.finishDead owner) race12 ≡ just race13
race-edge13 = refl
raceActions : List W.Action
raceActions = (W.run (P.protocolReturned Old.j₁₀)) ∷ (W.run (P.commitClean Old.j₁₀)) ∷ (W.run (P.infrastructureReturn owner T.demuxer closedError)) ∷ (W.run (P.publishInfra owner T.demuxer)) ∷ (W.consume owner) ∷ (W.run (P.returnProtocol Old.j₁₀)) ∷ (W.run (P.publishProtocol Old.j₁₀)) ∷ (W.run (P.deregisterProtocol Old.j₁₀)) ∷ (W.handleSelected owner) ∷ (W.beginDead owner) ∷ (W.sampleTracer owner) ∷ (W.commitTracer owner) ∷ (W.finishDead owner) ∷ []
racePath : W.Executes race0 raceActions race13
racePath = W.next race-edge1 (W.next race-edge2 (W.next race-edge3 (W.next race-edge4 (W.next race-edge5 (W.next race-edge6 (W.next race-edge7 (W.next race-edge8 (W.next race-edge9 (W.next race-edge10 (W.next race-edge11 (W.next race-edge12 (W.next race-edge13 (W.done)))))))))))))

errorHistory0 : W.State
errorHistory0 = error7
errorHistory1 : W.State
errorHistory1 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) [])
errorHistory-edge1 : W.step (W.run (P.protocolException Old.j₁₀ Old.err)) errorHistory0 ≡ just errorHistory1
errorHistory-edge1 = refl
errorHistory2 : W.State
errorHistory2 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyReturned (T.infraDemuxer closedError)) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) [])
errorHistory-edge2 : W.step (W.run (P.infrastructureReturn owner T.demuxer closedError)) errorHistory1 ≡ just errorHistory2
errorHistory-edge2 = refl
errorHistory3 : W.State
errorHistory3 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] ((T.infraDemuxer closedError) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) [])
errorHistory-edge3 : W.step (W.run (P.publishInfra owner T.demuxer)) errorHistory2 ≡ just errorHistory3
errorHistory-edge3 = refl
errorHistory4 : W.State
errorHistory4 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) ((owner , W.selected (T.infraDemuxer closedError)) ∷ []))
errorHistory-edge4 : W.step (W.consume owner) errorHistory3 ≡ just errorHistory4
errorHistory-edge4 = refl
errorHistory5 : W.State
errorHistory5 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁₀ , Pool.bodyReturned (T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err))) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) ((owner , W.selected (T.infraDemuxer closedError)) ∷ []))
errorHistory-edge5 : W.step (W.run (P.returnProtocol Old.j₁₀)) errorHistory4 ≡ just errorHistory5
errorHistory-edge5 = refl
errorHistory6 : W.State
errorHistory6 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁₀ , Pool.deregisterPending Pool.normalExit) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) ((owner , W.selected (T.infraDemuxer closedError)) ∷ []))
errorHistory-edge6 : W.step (W.run (P.publishProtocol Old.j₁₀)) errorHistory5 ≡ just errorHistory6
errorHistory-edge6 = refl
errorHistory7 : W.State
errorHistory7 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁₀ , Pool.deregistered Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) ((owner , W.selected (T.infraDemuxer closedError)) ∷ []))
errorHistory-edge7 : W.step (W.run (P.deregisterProtocol Old.j₁₀)) errorHistory6 ≡ just errorHistory7
errorHistory-edge7 = refl
errorHistory8 : W.State
errorHistory8 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []); status = Mux.stopped }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁₀ , Pool.deregistered Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) ((owner , W.deadReady W.normal) ∷ []))
errorHistory-edge8 : W.step (W.handleSelected owner) errorHistory7 ≡ just errorHistory8
errorHistory-edge8 = refl
errorHistory9 : W.State
errorHistory9 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []); status = Mux.stopped; callback = Mux.readActive Mux.muxStopped }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁₀ , Pool.deregistered Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) ((owner , W.deadTracing W.normal) ∷ []))
errorHistory-edge9 : W.step (W.beginDead owner) errorHistory8 ≡ just errorHistory9
errorHistory-edge9 = refl
errorHistory10 : W.State
errorHistory10 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []); status = Mux.stopped; callback = Mux.commitTrace true Mux.muxStopped }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁₀ , Pool.deregistered Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) ((owner , W.deadTracing W.normal) ∷ []))
errorHistory-edge10 : W.step (W.sampleTracer owner) errorHistory9 ≡ just errorHistory10
errorHistory-edge10 = refl
errorHistory11 : W.State
errorHistory11 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []); status = Mux.stopped; callback = Mux.returned; traceCounters = nothing }) (traceQueue Mux.muxStopped (record Old.m6 { runningJobs = []; finishedJobs = []; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []); status = Mux.stopped; callback = Mux.commitTrace true Mux.muxStopped }) Old.messages)) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁₀ , Pool.deregistered Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) ((owner , W.deadTracing W.normal) ∷ []))
errorHistory-edge11 : W.step (W.commitTracer owner) errorHistory10 ≡ just errorHistory11
errorHistory-edge11 = refl
errorHistory12 : W.State
errorHistory12 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = []; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []); status = Mux.stopped; callback = Mux.returned; traceCounters = nothing }) (traceQueue Mux.muxStopped (record Old.m6 { runningJobs = []; finishedJobs = []; completions = ((Mux.jobResult Mux.responderJob 1 (errored Old.err)) ∷ []); status = Mux.stopped; callback = Mux.commitTrace true Mux.muxStopped }) Old.messages)) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁₀ , Pool.deregistered Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] ((T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)) ∷ [])) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured (errored Old.err)))) ∷ []) ((owner , []) ∷ [])) ((owner , W.finished W.normal) ∷ []))
errorHistory-edge12 : W.step (W.finishDead owner) errorHistory11 ≡ just errorHistory12
errorHistory-edge12 = refl
errorHistoryActions : List W.Action
errorHistoryActions = (W.run (P.protocolException Old.j₁₀ Old.err)) ∷ (W.run (P.infrastructureReturn owner T.demuxer closedError)) ∷ (W.run (P.publishInfra owner T.demuxer)) ∷ (W.consume owner) ∷ (W.run (P.returnProtocol Old.j₁₀)) ∷ (W.run (P.publishProtocol Old.j₁₀)) ∷ (W.run (P.deregisterProtocol Old.j₁₀)) ∷ (W.handleSelected owner) ∷ (W.beginDead owner) ∷ (W.sampleTracer owner) ∷ (W.commitTracer owner) ∷ (W.finishDead owner) ∷ []
errorHistoryPath : W.Executes errorHistory0 errorHistoryActions errorHistory12
errorHistoryPath = W.next errorHistory-edge1 (W.next errorHistory-edge2 (W.next errorHistory-edge3 (W.next errorHistory-edge4 (W.next errorHistory-edge5 (W.next errorHistory-edge6 (W.next errorHistory-edge7 (W.next errorHistory-edge8 (W.next errorHistory-edge9 (W.next errorHistory-edge10 (W.next errorHistory-edge11 (W.next errorHistory-edge12 (W.done))))))))))))

busy0 : W.State
busy0 = race5
busy1 : W.State
busy1 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , clean) ∷ []); protocols = ((1 , Mux.idle) ∷ []); status = Mux.failed closedError }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) ((owner , W.deadReady (W.failed closedError)) ∷ []))
busy-edge1 : W.step (W.handleSelected owner) busy0 ≡ just busy1
busy-edge1 = refl
busy2 : W.State
busy2 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , clean) ∷ []); protocols = ((1 , Mux.idle) ∷ []); status = Mux.failed closedError; callback = Mux.readActive Mux.muxStopped }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) ((owner , W.deadTracing (W.failed closedError)) ∷ []))
busy-edge2 : W.step (W.beginDead owner) busy1 ≡ just busy2
busy-edge2 = refl
busy3 : W.State
busy3 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , clean) ∷ []); protocols = ((1 , Mux.idle) ∷ []); status = Mux.failed closedError; callback = Mux.commitTrace true Mux.muxStopped }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) ((owner , W.deadTracing (W.failed closedError)) ∷ []))
busy-edge3 : W.step (W.sampleTracer owner) busy2 ≡ just busy3
busy-edge3 = refl
busy4 : W.State
busy4 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , clean) ∷ []); protocols = ((1 , Mux.idle) ∷ []); status = Mux.failed closedError; callback = Mux.returned; traceCounters = nothing }) (traceQueue Mux.muxStopped (record Old.m6 { runningJobs = []; finishedJobs = ((1 , clean) ∷ []); protocols = ((1 , Mux.idle) ∷ []); status = Mux.failed closedError; callback = Mux.commitTrace true Mux.muxStopped }) Old.messages)) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) ((owner , W.deadTracing (W.failed closedError)) ∷ []))
busy-edge4 : W.step (W.commitTracer owner) busy3 ≡ just busy4
busy-edge4 = refl
busy5 : W.State
busy5 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.m6 { runningJobs = []; finishedJobs = ((1 , clean) ∷ []); protocols = ((1 , Mux.idle) ∷ []); status = Mux.failed closedError; callback = Mux.returned; traceCounters = nothing }) (traceQueue Mux.muxStopped (record Old.m6 { runningJobs = []; finishedJobs = ((1 , clean) ∷ []); protocols = ((1 , Mux.idle) ∷ []); status = Mux.failed closedError; callback = Mux.commitTrace true Mux.muxStopped }) Old.messages)) (Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁₀ , Pool.bodyRunning) ∷ []) (Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , (T.protocolJob owner Old.mid Mux.responderJob 1 Old.r₀ (T.resultCaptured clean))) ∷ []) ((owner , (Old.j₁₀ ∷ [])) ∷ [])) ((owner , W.finished (W.failed closedError)) ∷ []))
busy-edge5 : W.step (W.finishDead owner) busy4 ≡ just busy5
busy-edge5 = refl
busyActions : List W.Action
busyActions = (W.handleSelected owner) ∷ (W.beginDead owner) ∷ (W.sampleTracer owner) ∷ (W.commitTracer owner) ∷ (W.finishDead owner) ∷ []
busyPath : W.Executes busy0 busyActions busy5
busyPath = W.next busy-edge1 (W.next busy-edge2 (W.next busy-edge3 (W.next busy-edge4 (W.next busy-edge5 (W.done)))))

duringTrace0 : W.State
duringTrace0 = clean2
duringTrace1 : W.State
duringTrace1 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.publishedMux { completions = []; callback = Mux.readActive (Mux.completed 1 clean) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.bodyReturned (T.infraMuxer Old.err)) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] []) ((Old.j₁₀ , Old.rJob (T.resultCaptured clean)) ∷ []) ((owner , []) ∷ [])) ((owner , W.responderTracing clean) ∷ []))
duringTrace-edge1 : W.step (W.run (P.infrastructureReturn owner T.muxer Old.err)) duringTrace0 ≡ just duringTrace1
duringTrace-edge1 = refl
duringTrace2 : W.State
duringTrace2 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.publishedMux { completions = []; callback = Mux.readActive (Mux.completed 1 clean) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] ((T.infraMuxer Old.err) ∷ [])) ((Old.j₁₀ , Old.rJob (T.resultCaptured clean)) ∷ []) ((owner , []) ∷ [])) ((owner , W.responderTracing clean) ∷ []))
duringTrace-edge2 : W.step (W.run (P.publishInfra owner T.muxer)) duringTrace1 ≡ just duringTrace2
duringTrace-edge2 = refl
duringTrace3 : W.State
duringTrace3 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.publishedMux { completions = []; callback = Mux.commitTrace true (Mux.completed 1 clean) }) Old.messages) (Pool.poolState ((Old.j₀ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] ((T.infraMuxer Old.err) ∷ [])) ((Old.j₁₀ , Old.rJob (T.resultCaptured clean)) ∷ []) ((owner , []) ∷ [])) ((owner , W.responderTracing clean) ∷ []))
duringTrace-edge3 : W.step (W.sampleTracer owner) duringTrace2 ≡ just duringTrace3
duringTrace-edge3 = refl
duringTrace4 : W.State
duringTrace4 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.publishedMux { completions = []; callback = Mux.returned; traceCounters = just (Mux.counters (+ 0) (+ 0)) }) (traceQueue (Mux.completed 1 clean) (record Old.publishedMux { completions = []; callback = Mux.commitTrace true (Mux.completed 1 clean) }) Old.messages)) (Pool.poolState ((Old.j₀ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] ((T.infraMuxer Old.err) ∷ [])) ((Old.j₁₀ , Old.rJob (T.resultCaptured clean)) ∷ []) ((owner , []) ∷ [])) ((owner , W.responderTracing clean) ∷ []))
duringTrace-edge4 : W.step (W.commitTracer owner) duringTrace3 ≡ just duringTrace4
duringTrace-edge4 = refl
duringTrace5 : W.State
duringTrace5 = (W.monitorState (Old.snapshot (Old.sourceMux (record Old.publishedMux { completions = []; callback = Mux.returned; traceCounters = just (Mux.counters (+ 0) (+ 0)) }) (traceQueue (Mux.completed 1 clean) (record Old.publishedMux { completions = []; callback = Mux.commitTrace true (Mux.completed 1 clean) }) Old.messages)) (Pool.poolState ((Old.j₀ , Pool.deregisterPending Pool.normalExit) ∷ (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing Pool.openPool [] [] [] ((T.infraMuxer Old.err) ∷ [])) ((Old.j₁₀ , Old.rJob (T.resultCaptured clean)) ∷ []) ((owner , []) ∷ [])) ((owner , W.waiting) ∷ []))
duringTrace-edge5 : W.step (W.finishProtocolTrace owner) duringTrace4 ≡ just duringTrace5
duringTrace-edge5 = refl
duringTraceActions : List W.Action
duringTraceActions = (W.run (P.infrastructureReturn owner T.muxer Old.err)) ∷ (W.run (P.publishInfra owner T.muxer)) ∷ (W.sampleTracer owner) ∷ (W.commitTracer owner) ∷ (W.finishProtocolTrace owner) ∷ []
duringTracePath : W.Executes duringTrace0 duringTraceActions duringTrace5
duringTracePath = W.next duringTrace-edge1 (W.next duringTrace-edge2 (W.next duringTrace-edge3 (W.next duringTrace-edge4 (W.next duringTrace-edge5 (W.done)))))

clean-returns-to-waiting : W.pcAt owner clean5 ≡ W.waiting
clean-returns-to-waiting = refl
consumption-keeps-parent-async : B.threads (U.base (P.base (W.base clean1))) ≡ B.threads (U.base (P.base Old.r13))
consumption-keeps-parent-async = refl
parent-insertion-blocks-consumption : W.step (W.consume owner) (wrap Old.r10) ≡ nothing
parent-insertion-blocks-consumption = refl
held-command-refused : W.step (W.run (P.control owner P.selectCommand)) clean1 ≡ nothing
held-command-refused = refl
held-fork-refused : W.step (W.run (P.forkInitiator owner Old.j₁₁ Old.r₁ 1)) clean1 ≡ nothing
held-fork-refused = refl
held-cannot-consume-again : W.step (W.consume owner) clean1 ≡ nothing
held-cannot-consume-again = refl

muxer-always-fails-at-zero-mini : W.pcAt owner muxer8 ≡ W.finished (W.failed Old.err)
muxer-always-fails-at-zero-mini = refl
demux-zero-mini-stops : W.pcAt owner demux8 ≡ W.finished W.normal
demux-zero-mini-stops = refl
finished-is-not-pool-close : Pool.phase (W.poolAt owner demux8) ≡ Pool.openPool
finished-is-not-pool-close = refl

registered-at-dequeue : W.miniCount owner race5 ≡ 1
registered-at-dequeue = refl
metadata-clean-inactive : P.active owner Mux.responderJob 1 (P.jobs (W.base race5)) ≡ false
metadata-clean-inactive = refl
registered-at-handle : W.miniCount owner race8 ≡ 0
registered-at-handle = refl
late-count-normal-finish : W.pcAt owner race13 ≡ W.finished W.normal
late-count-normal-finish = refl
queued-tail-survives-finished : Pool.completions (W.poolAt owner race13) ≡ Old.rPayload ∷ []
queued-tail-survives-finished = refl
legacy-responder-tail-cannot-skip-physical-infra : W.pcAt owner race5 ≡ W.selected (T.infraDemuxer closedError)
legacy-responder-tail-cannot-skip-physical-infra = refl
clean-but-still-registered-fails : W.demuxFinish owner closedError race5 ≡ W.failed closedError
clean-but-still-registered-fails = refl

clean-inactive-still-fatal : W.pcAt owner busy5 ≡ W.finished (W.failed closedError)
clean-inactive-still-fatal = refl

removed-error-still-metadata-active : P.active owner Mux.responderJob 1 (P.jobs (W.base errorHistory7)) ≡ true
removed-error-still-metadata-active = refl
removed-error-not-group-member : W.miniCount owner errorHistory7 ≡ 0
removed-error-not-group-member = refl
removed-error-history-normal-demux : W.pcAt owner errorHistory12 ≡ W.finished W.normal
removed-error-history-normal-demux = refl
unconsumed-error-tail-retained : Pool.completions (W.poolAt owner errorHistory12) ≡
  T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err) ∷ []
unconsumed-error-tail-retained = refl

responder-failure-before-completion-trace : W.muxAt Old.mid errorTail5 ≡ just
  (record Old.m6 { status = Mux.failed Old.err; runningJobs = []
    ; callback = Mux.readActive (Mux.completed 1 (errored Old.err)) })
responder-failure-before-completion-trace = refl
responder-error-finished : W.pcAt owner errorTail12 ≡ W.finished (W.failed Old.err)
responder-error-finished = refl
new-result-survives-selected-callback : Pool.completions (W.poolAt owner duringTrace5) ≡ T.infraMuxer Old.err ∷ []
new-result-survives-selected-callback = refl
-- These two inspect delegation only; they do not conjure a second physical owner.
unrelated-owner-command-not-frozen : W.delegateAllowed (P.control (ident 999) P.selectCommand) clean2 ≡ true
unrelated-owner-command-not-frozen = refl
unrelated-owner-fork-not-frozen : W.delegateAllowed (P.forkInitiator (ident 999) Old.j₂₀ Old.r₃ 1) clean2 ≡ true
unrelated-owner-fork-not-frozen = refl
wrongGeneration : W.State
wrongGeneration = W.setPC owner (W.selected (T.protocolCompletion Mux.responderJob 1 (ident 999) clean)) (wrap Old.r13)
wrong-generation-refused : W.step (W.handleSelected owner) wrongGeneration ≡ nothing
wrong-generation-refused = refl
wrongProjection : W.State
wrongProjection = W.setSource (Old.sourceMux (record Old.publishedMux
  { completions = Mux.jobResult Mux.responderJob 1 (errored Old.err) ∷ [] }) Old.messages) clean1
wrong-projected-outcome-refused : W.step (W.handleSelected owner) wrongProjection ≡ nothing
wrong-projected-outcome-refused = refl

-- Conditional extra responder projection cannot replace a physical engine head.
wrongLegacy : W.State
wrongLegacy = W.setSource (Old.sourceMux Old.publishedMux Old.messages) muxer2
wrongLegacySelected : W.State
wrongLegacySelected = W.setPC owner (W.selected (T.infraMuxer Old.err))
  (W.setPool owner (Old.publishedFrame Old.s13)
    (record (W.poolAt owner wrongLegacy) { completions = [] }) wrongLegacy)
physical-head-cannot-skip-to-responder-projection : W.step (W.consume owner) wrongLegacy ≡ just wrongLegacySelected
physical-head-cannot-skip-to-responder-projection = refl

append : ∀ {s as t bs u} → W.Executes s as t → W.Executes t bs u → W.Executes s (as ++ bs) u
append W.done tail = tail
append (W.next eq path) tail = W.next eq (append path tail)
abstract
  initialized-clean-monitor : W.Executes (wrap Old.b0)
    (map W.run (Old.startActions ++ Old.responderPathActions) ++ cleanActions) clean5
  initialized-clean-monitor = append initialized-clean-head cleanPath
  initialized-error-prefix : W.Executes (wrap Old.b0)
    (map W.run Old.startActions ++ errorPrefixActions) error7
  initialized-error-prefix = append initialized-running errorPrefixPath
  initialized-responder-error : W.Executes (wrap Old.b0)
    ((map W.run Old.startActions ++ errorPrefixActions) ++ errorTailActions) errorTail12
  initialized-responder-error = append initialized-error-prefix errorTailPath
  initialized-initiator-clean : W.Executes (wrap Old.b0)
    ((map W.run Old.startActions ++ errorPrefixActions) ++ initiatorCleanActions) initiatorClean9
  initialized-initiator-clean = append initialized-error-prefix initiatorCleanPath
  initialized-initiator-error : W.Executes (wrap Old.b0)
    ((map W.run Old.startActions ++ errorPrefixActions) ++ initiatorErrorActions) initiatorError12
  initialized-initiator-error = append initialized-error-prefix initiatorErrorPath
  initialized-muxer-failure : W.Executes (wrap Old.b0)
    (map W.run Old.startActions ++ muxerActions) muxer8
  initialized-muxer-failure = append initialized-running muxerPath
  initialized-demux-normal : W.Executes (wrap Old.b0)
    (map W.run Old.startActions ++ demuxActions) demux8
  initialized-demux-normal = append initialized-running demuxPath
  initialized-late-count-race : W.Executes (wrap Old.b0)
    ((map W.run Old.startActions ++ errorPrefixActions) ++ raceActions) race13
  initialized-late-count-race = append initialized-error-prefix racePath
  initialized-error-history-normal : W.Executes (wrap Old.b0)
    ((map W.run Old.startActions ++ errorPrefixActions) ++ errorHistoryActions) errorHistory12
  initialized-error-history-normal = append initialized-error-prefix errorHistoryPath

responder-completion-must-return-before-Dead : W.step (W.beginDead owner) errorTail5 ≡ nothing
responder-completion-must-return-before-Dead = refl
responder-completion-returns-afterFailure : W.pcAt owner errorTail8 ≡ W.deadReady (W.failed Old.err)
responder-completion-returns-afterFailure = refl
initiator-clean-keeps-IG-source : W.source initiatorClean9 ≡ W.source error7
initiator-clean-keeps-IG-source = refl
initiator-error-ignores-completion-tracer : W.muxAt Old.mid initiatorError7 ≡ just
  (record Old.m6 { status = Mux.failed Old.err })
initiator-error-ignores-completion-tracer = refl
non-BearerClosed-at-zero-mini-fails : W.demuxFinish owner Old.err demux3 ≡ W.failed Old.err
non-BearerClosed-at-zero-mini-fails = refl

-- Generic proofs apply to the actual initializer and the same executed paths.
import ConnectionManagement.Properties.MuxResultMonitor as Proofs
module Facts = Proofs bearerClosed
import ConnectionManagement.Properties.MuxProtocolJobs as ProtocolFacts
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
initialized-race-projections : Facts.Paths (wrap Old.b0) race13
initialized-race-projections = Facts.exec-projects initialized-late-count-race
initialized-race-same-physical-pool : ProtocolFacts.PTrace Pool.initial (W.poolAt owner race13)
initialized-race-same-physical-pool = Facts.pool-from-initial actual-initializer initialized-late-count-race owner
initialized-race-captures : Capture.Captures (W.source race13)
initialized-race-captures = Facts.from-initial-captures actual-initializer initialized-late-count-race
initialized-race-supply : Supply.Valid (W.source race13)
initialized-race-supply = Facts.from-initial-supply actual-initializer Old.Prior.initial-bounds initialized-late-count-race

-- Prefix witnesses connect the branching controls to the same true initializer.
raceSelectedActions : List W.Action
raceSelectedActions = W.run (P.protocolReturned Old.j₁₀) ∷ W.run (P.commitClean Old.j₁₀) ∷
  W.run (P.infrastructureReturn owner T.demuxer closedError) ∷
  W.run (P.publishInfra owner T.demuxer) ∷ W.consume owner ∷ []
raceSelectedPath : W.Executes race0 raceSelectedActions race5
raceSelectedPath = W.next race-edge1 (W.next race-edge2 (W.next race-edge3 (W.next race-edge4 (W.next race-edge5 W.done))))
cleanSelectedActions : List W.Action
cleanSelectedActions = W.consume owner ∷ W.handleSelected owner ∷ []
cleanSelectedPath : W.Executes clean0 cleanSelectedActions clean2
cleanSelectedPath = W.next clean-edge1 (W.next clean-edge2 W.done)
abstract
  initialized-clean-inactive-but-registered : W.Executes (wrap Old.b0)
    (((map W.run Old.startActions ++ errorPrefixActions) ++ raceSelectedActions) ++ busyActions) busy5
  initialized-clean-inactive-but-registered = append
    (append initialized-error-prefix raceSelectedPath) busyPath
  initialized-result-during-callback : W.Executes (wrap Old.b0)
    ((map W.run (Old.startActions ++ Old.responderPathActions) ++ cleanSelectedActions) ++ duringTraceActions) duringTrace5
  initialized-result-during-callback = append
    (append initialized-clean-head cleanSelectedPath) duringTracePath
terminal-monitor-keeps-parent-thread-registry :
  B.threads (U.base (P.base (W.base demux8))) ≡ B.threads (U.base (P.base Old.z12))
terminal-monitor-keeps-parent-thread-registry = refl

raw-status-write-cannot-bypass-monitor : W.step
  (W.run (P.run (U.run (B.handler (H.run (Machine.igStep (IG.recordMuxFailure Old.mid Old.err)))))))
  (wrap Old.r13) ≡ nothing
raw-status-write-cannot-bypass-monitor = refl
raw-stopped-write-is-classified : P.rawIGAllowed (IG.recordMuxStopped Old.mid) ≡ false
raw-stopped-write-is-classified = refl
raw-dead-trace-is-classified : P.rawIGAllowed (IG.traceMuxDead Old.mid) ≡ false
raw-dead-trace-is-classified = refl

-- Local certificates retain the exact consumed head, matched source write,
-- handling-time group observation, and returned Dead callback.
actual-physical-dequeue : Facts.Dequeue owner clean0 clean1
actual-physical-dequeue = Facts.consume-observation owner clean0 clean-edge1
actual-responder-source-handle : Facts.Handle owner clean1 clean2
actual-responder-source-handle = Facts.handle-observation owner clean1 clean-edge2
failure-source-before-completion-trace : Facts.Handle owner errorTail4 errorTail5
failure-source-before-completion-trace = Facts.handle-observation owner errorTail4 errorTail-edge5
late-registered-count-handle : Facts.Handle owner race8 race9
late-registered-count-handle = Facts.handle-observation owner race8 race-edge9
normal-Dead-callback-returned : Facts.Finished owner demux7 demux8
normal-Dead-callback-returned = Facts.finish-observation owner demux7 demux-edge8
failed-Dead-callback-returned : Facts.Finished owner errorTail11 errorTail12
failed-Dead-callback-returned = Facts.finish-observation owner errorTail11 errorTail-edge12
