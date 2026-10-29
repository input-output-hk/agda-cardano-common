{-# OPTIONS --guardedness #-}

-- Initialized DeltaQ ordering in both directions, under the existing protocol
-- body/initiator/tracer contracts. No source-refinement/progress claim follows.
module ConnectionManagement.Negative.MuxDeltaQ where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (worker; mux; local)
open import ConnectionManagement.IGTypes using (clean; errored)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.MuxDeltaQ as Delta
import ConnectionManagement.Properties.MuxDeltaQCapture as CaptureProof
import ConnectionManagement.Properties.MuxDeltaQ as Proof
import ConnectionManagement.Properties.MuxDeltaQPrefix as PrefixProof
import ConnectionManagement.Negative.MuxProtocolJobs as Old
import ConnectionManagement.Negative.MuxResultMonitor as RF
import ConnectionManagement.Negative.MuxCallbackCancellation as C
import ConnectionManagement.Negative.MuxStartupUnwind as Prior
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.MuxJobTypes as T
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as Machine
import ConnectionManagement.State as Shared
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
module D = Delta RF.bearerClosed
module Facts = Proof RF.bearerClosed
module Captured = CaptureProof RF.bearerClosed
module Prefix = PrefixProof RF.bearerClosed
module R = D.R
module X = D.X
module W = D.W
module G = D.G
module M = D.M
module P = D.P
module Pool = D.Pool
owner : WorkerId
owner = Old.owner
wrapR : M.State → R.State
wrapR m = R.unwinding (W.handlerExitState (G.shutdownState m []) []) []
at : M.State → T.TypedResult → D.Phase → D.State
at m payload pc = D.deltaQState (wrapR m) ((owner , D.ticket payload pc) ∷ [])
empty : M.State → D.State
empty m = Prefix.wrap (wrapR m)
runM : M.Action → D.Action
runM a = D.run (D.wrapMonitor a)
cleanPayload errorPayload initiatorPayload initiatorErrorPayload : T.TypedResult
cleanPayload = Old.rPayload
errorPayload = T.protocolCompletion Mux.responderJob 1 Old.r₀ (errored Old.err)
initiatorPayload = T.protocolCompletion Mux.initiatorJob 1 Old.r₁ clean
initiatorErrorPayload = T.protocolCompletion Mux.initiatorJob 1 Old.r₁ (errored Old.err)
start : D.State
start = Prefix.wrap Prior.start
actual-initializer : D.initial (O.initial Old.F.start) ≡ just start
actual-initializer = refl
cleanPrefixActions : List R.Action
cleanPrefixActions = Prior.wrappedActions Old.startActions ++ C.prefixActions
abstract
  initialized-clean-head : D.Executes start (map D.run cleanPrefixActions) (empty RF.clean0)
  initialized-clean-head = Prefix.lift C.initialized-result
    (Prefix.append-tags (Prefix.tag-nested Old.startActions) (Prefix.tag-protocols Old.responderPathActions))

-- Actual protocol-only prefix to the registered responder, before its error.
errorPrefixP : List P.Action
errorPrefixP = P.control owner P.selectCommand ∷ P.control owner (P.demand 1) ∷
  P.control owner P.sampleTracer ∷ P.control owner P.commitTracer ∷ P.control owner P.finishStart ∷
  P.forkResponder owner Old.j₁₀ Old.r₀ ∷ P.registerProtocol Old.j₁₀ ∷ []
error-register : R.step (Prefix.rawProtocol (P.registerProtocol Old.j₁₀)) (wrapR RF.error6) ≡ just (wrapR RF.error7)
error-register = refl
errorPrefixR : R.Executes (wrapR RF.error0) (map Prefix.rawProtocol errorPrefixP) (wrapR RF.error7)
errorPrefixR = R.next C.prefix1 (R.next C.prefix2 (R.next C.prefix3 (R.next C.prefix4
  (R.next C.prefix5 (R.next C.prefix6 (R.next error-register R.done))))))
errorPrefixActions : List D.Action
errorPrefixActions = map D.run (Prior.wrappedActions Old.startActions) ++ map D.run (map Prefix.rawProtocol errorPrefixP)
abstract
  initialized-error-prefix : D.Executes start errorPrefixActions (empty RF.error7)
  initialized-error-prefix = Prefix.append (Prefix.lift C.initialized-monitor (Prefix.tag-nested Old.startActions))
    (Prefix.lift errorPrefixR (Prefix.tag-protocols errorPrefixP))
clean0 : D.State
clean0 = empty RF.clean0
clean1 : D.State
clean1 = at RF.clean1 (cleanPayload) D.captured
clean-edge1 : D.step (runM (M.consume owner)) clean0 ≡ just clean1
clean-edge1 = refl
clean2 : D.State
clean2 = at RF.clean2 (cleanPayload) D.captured
clean-edge2 : D.step (runM (M.handleSelected owner)) clean1 ≡ just clean2
clean-edge2 = refl
clean3 : D.State
clean3 = at RF.clean3 (cleanPayload) D.captured
clean-edge3 : D.step (runM (M.sampleTracer owner)) clean2 ≡ just clean3
clean-edge3 = refl
clean4 : D.State
clean4 = at RF.clean4 (cleanPayload) D.captured
clean-edge4 : D.step (runM (M.commitTracer owner)) clean3 ≡ just clean4
clean-edge4 = refl
cleanInvoked cleanReturned : D.State
cleanInvoked = at RF.clean4 (cleanPayload) D.invoked
cleanReturned = at RF.clean5 (cleanPayload) D.returned
clean-invoke : D.step (D.beginDeltaQ owner) clean4 ≡ just cleanInvoked
clean-invoke = refl
clean-return : D.step (D.observeReturn owner) cleanInvoked ≡ just cleanReturned
clean-return = refl
cleanActions : List D.Action
cleanActions = (runM (M.consume owner)) ∷ (runM (M.handleSelected owner)) ∷ (runM (M.sampleTracer owner)) ∷ (runM (M.commitTracer owner)) ∷ (D.beginDeltaQ owner) ∷ (D.observeReturn owner) ∷ []
cleanPath : D.Executes clean0 cleanActions cleanReturned
cleanPath = D.next clean-edge1 (D.next clean-edge2 (D.next clean-edge3 (D.next clean-edge4 (D.next clean-invoke (D.next clean-return (D.done))))))
errorTail0 : D.State
errorTail0 = empty RF.errorTail0
errorTail1 : D.State
errorTail1 = empty RF.errorTail1
errorTail-edge1 : D.step (runM (M.run (P.protocolException Old.j₁₀ Old.err))) errorTail0 ≡ just errorTail1
errorTail-edge1 = refl
errorTail2 : D.State
errorTail2 = empty RF.errorTail2
errorTail-edge2 : D.step (runM (M.run (P.returnProtocol Old.j₁₀))) errorTail1 ≡ just errorTail2
errorTail-edge2 = refl
errorTail3 : D.State
errorTail3 = empty RF.errorTail3
errorTail-edge3 : D.step (runM (M.run (P.publishProtocol Old.j₁₀))) errorTail2 ≡ just errorTail3
errorTail-edge3 = refl
errorTail4 : D.State
errorTail4 = at RF.errorTail4 (errorPayload) D.captured
errorTail-edge4 : D.step (runM (M.consume owner)) errorTail3 ≡ just errorTail4
errorTail-edge4 = refl
errorTail5 : D.State
errorTail5 = at RF.errorTail5 (errorPayload) D.captured
errorTail-edge5 : D.step (runM (M.handleSelected owner)) errorTail4 ≡ just errorTail5
errorTail-edge5 = refl
errorTail6 : D.State
errorTail6 = at RF.errorTail6 (errorPayload) D.captured
errorTail-edge6 : D.step (runM (M.sampleTracer owner)) errorTail5 ≡ just errorTail6
errorTail-edge6 = refl
errorTail7 : D.State
errorTail7 = at RF.errorTail7 (errorPayload) D.captured
errorTail-edge7 : D.step (runM (M.commitTracer owner)) errorTail6 ≡ just errorTail7
errorTail-edge7 = refl
errorTail8 : D.State
errorTail8 = at RF.errorTail8 (errorPayload) D.captured
errorTail-edge8 : D.step (runM (M.finishProtocolTrace owner)) errorTail7 ≡ just errorTail8
errorTail-edge8 = refl
errorTail9 : D.State
errorTail9 = at RF.errorTail9 (errorPayload) D.captured
errorTail-edge9 : D.step (runM (M.beginDead owner)) errorTail8 ≡ just errorTail9
errorTail-edge9 = refl
errorTail10 : D.State
errorTail10 = at RF.errorTail10 (errorPayload) D.captured
errorTail-edge10 : D.step (runM (M.sampleTracer owner)) errorTail9 ≡ just errorTail10
errorTail-edge10 = refl
errorTail11 : D.State
errorTail11 = at RF.errorTail11 (errorPayload) D.captured
errorTail-edge11 : D.step (runM (M.commitTracer owner)) errorTail10 ≡ just errorTail11
errorTail-edge11 = refl
errorTailInvoked errorTailReturned : D.State
errorTailInvoked = at RF.errorTail11 (errorPayload) D.invoked
errorTailReturned = at RF.errorTail12 (errorPayload) D.returned
errorTail-invoke : D.step (D.beginDeltaQ owner) errorTail11 ≡ just errorTailInvoked
errorTail-invoke = refl
errorTail-return : D.step (D.observeReturn owner) errorTailInvoked ≡ just errorTailReturned
errorTail-return = refl
errorTailActions : List D.Action
errorTailActions = (runM (M.run (P.protocolException Old.j₁₀ Old.err))) ∷ (runM (M.run (P.returnProtocol Old.j₁₀))) ∷ (runM (M.run (P.publishProtocol Old.j₁₀))) ∷ (runM (M.consume owner)) ∷ (runM (M.handleSelected owner)) ∷ (runM (M.sampleTracer owner)) ∷ (runM (M.commitTracer owner)) ∷ (runM (M.finishProtocolTrace owner)) ∷ (runM (M.beginDead owner)) ∷ (runM (M.sampleTracer owner)) ∷ (runM (M.commitTracer owner)) ∷ (D.beginDeltaQ owner) ∷ (D.observeReturn owner) ∷ []
errorTailPath : D.Executes errorTail0 errorTailActions errorTailReturned
errorTailPath = D.next errorTail-edge1 (D.next errorTail-edge2 (D.next errorTail-edge3 (D.next errorTail-edge4 (D.next errorTail-edge5 (D.next errorTail-edge6 (D.next errorTail-edge7 (D.next errorTail-edge8 (D.next errorTail-edge9 (D.next errorTail-edge10 (D.next errorTail-edge11 (D.next errorTail-invoke (D.next errorTail-return (D.done)))))))))))))
initiatorClean0 : D.State
initiatorClean0 = empty RF.initiatorClean0
initiatorClean1 : D.State
initiatorClean1 = empty RF.initiatorClean1
initiatorClean-edge1 : D.step (runM (M.run (P.forkInitiator owner Old.j₁₁ Old.r₁ 1))) initiatorClean0 ≡ just initiatorClean1
initiatorClean-edge1 = refl
initiatorClean2 : D.State
initiatorClean2 = empty RF.initiatorClean2
initiatorClean-edge2 : D.step (runM (M.run (P.registerProtocol Old.j₁₁))) initiatorClean1 ≡ just initiatorClean2
initiatorClean-edge2 = refl
initiatorClean3 : D.State
initiatorClean3 = empty RF.initiatorClean3
initiatorClean-edge3 : D.step (runM (M.run (P.protocolReturned Old.j₁₁))) initiatorClean2 ≡ just initiatorClean3
initiatorClean-edge3 = refl
initiatorClean4 : D.State
initiatorClean4 = empty RF.initiatorClean4
initiatorClean-edge4 : D.step (runM (M.run (P.commitClean Old.j₁₁))) initiatorClean3 ≡ just initiatorClean4
initiatorClean-edge4 = refl
initiatorClean5 : D.State
initiatorClean5 = empty RF.initiatorClean5
initiatorClean-edge5 : D.step (runM (M.run (P.returnProtocol Old.j₁₁))) initiatorClean4 ≡ just initiatorClean5
initiatorClean-edge5 = refl
initiatorClean6 : D.State
initiatorClean6 = empty RF.initiatorClean6
initiatorClean-edge6 : D.step (runM (M.run (P.publishProtocol Old.j₁₁))) initiatorClean5 ≡ just initiatorClean6
initiatorClean-edge6 = refl
initiatorClean7 : D.State
initiatorClean7 = at RF.initiatorClean7 (initiatorPayload) D.captured
initiatorClean-edge7 : D.step (runM (M.consume owner)) initiatorClean6 ≡ just initiatorClean7
initiatorClean-edge7 = refl
initiatorClean8 : D.State
initiatorClean8 = at RF.initiatorClean8 (initiatorPayload) D.captured
initiatorClean-edge8 : D.step (runM (M.handleSelected owner)) initiatorClean7 ≡ just initiatorClean8
initiatorClean-edge8 = refl
initiatorCleanTraceInvoked initiatorCleanTraceReturned : D.State
initiatorCleanTraceInvoked = at RF.initiatorClean8 initiatorPayload D.muxInvoked
initiatorCleanTraceReturned = at RF.initiatorClean8 initiatorPayload D.muxReturned
initiatorClean-mux-invoke : D.step (D.beginInitiatorTrace owner) initiatorClean8 ≡ just initiatorCleanTraceInvoked
initiatorClean-mux-invoke = refl
initiatorClean-mux-return : D.step (D.observeInitiatorReturn owner) initiatorCleanTraceInvoked ≡ just initiatorCleanTraceReturned
initiatorClean-mux-return = refl
initiatorCleanInvoked initiatorCleanReturned : D.State
initiatorCleanInvoked = at RF.initiatorClean8 (initiatorPayload) D.invoked
initiatorCleanReturned = at RF.initiatorClean9 (initiatorPayload) D.returned
initiatorClean-invoke : D.step (D.beginDeltaQ owner) initiatorCleanTraceReturned ≡ just initiatorCleanInvoked
initiatorClean-invoke = refl
initiatorClean-return : D.step (D.observeReturn owner) initiatorCleanInvoked ≡ just initiatorCleanReturned
initiatorClean-return = refl
initiatorCleanActions : List D.Action
initiatorCleanActions = (runM (M.run (P.forkInitiator owner Old.j₁₁ Old.r₁ 1))) ∷ (runM (M.run (P.registerProtocol Old.j₁₁))) ∷ (runM (M.run (P.protocolReturned Old.j₁₁))) ∷ (runM (M.run (P.commitClean Old.j₁₁))) ∷ (runM (M.run (P.returnProtocol Old.j₁₁))) ∷ (runM (M.run (P.publishProtocol Old.j₁₁))) ∷ (runM (M.consume owner)) ∷ (runM (M.handleSelected owner)) ∷ D.beginInitiatorTrace owner ∷ D.observeInitiatorReturn owner ∷ (D.beginDeltaQ owner) ∷ (D.observeReturn owner) ∷ []
initiatorCleanPath : D.Executes initiatorClean0 initiatorCleanActions initiatorCleanReturned
initiatorCleanPath = D.next initiatorClean-edge1 (D.next initiatorClean-edge2 (D.next initiatorClean-edge3 (D.next initiatorClean-edge4 (D.next initiatorClean-edge5 (D.next initiatorClean-edge6 (D.next initiatorClean-edge7 (D.next initiatorClean-edge8 (D.next initiatorClean-mux-invoke (D.next initiatorClean-mux-return (D.next initiatorClean-invoke (D.next initiatorClean-return (D.done))))))))))))
initiatorError0 : D.State
initiatorError0 = empty RF.initiatorError0
initiatorError1 : D.State
initiatorError1 = empty RF.initiatorError1
initiatorError-edge1 : D.step (runM (M.run (P.forkInitiator owner Old.j₁₁ Old.r₁ 1))) initiatorError0 ≡ just initiatorError1
initiatorError-edge1 = refl
initiatorError2 : D.State
initiatorError2 = empty RF.initiatorError2
initiatorError-edge2 : D.step (runM (M.run (P.registerProtocol Old.j₁₁))) initiatorError1 ≡ just initiatorError2
initiatorError-edge2 = refl
initiatorError3 : D.State
initiatorError3 = empty RF.initiatorError3
initiatorError-edge3 : D.step (runM (M.run (P.protocolException Old.j₁₁ Old.err))) initiatorError2 ≡ just initiatorError3
initiatorError-edge3 = refl
initiatorError4 : D.State
initiatorError4 = empty RF.initiatorError4
initiatorError-edge4 : D.step (runM (M.run (P.returnProtocol Old.j₁₁))) initiatorError3 ≡ just initiatorError4
initiatorError-edge4 = refl
initiatorError5 : D.State
initiatorError5 = empty RF.initiatorError5
initiatorError-edge5 : D.step (runM (M.run (P.publishProtocol Old.j₁₁))) initiatorError4 ≡ just initiatorError5
initiatorError-edge5 = refl
initiatorError6 : D.State
initiatorError6 = at RF.initiatorError6 (initiatorErrorPayload) D.captured
initiatorError-edge6 : D.step (runM (M.consume owner)) initiatorError5 ≡ just initiatorError6
initiatorError-edge6 = refl
initiatorError7 : D.State
initiatorError7 = at RF.initiatorError7 (initiatorErrorPayload) D.captured
initiatorError-edge7 : D.step (runM (M.handleSelected owner)) initiatorError6 ≡ just initiatorError7
initiatorError-edge7 = refl
initiatorError7a : D.State
initiatorError7a = at RF.initiatorError7 initiatorErrorPayload D.muxInvoked
initiatorError-mux-invoke : D.step (D.beginInitiatorTrace owner) initiatorError7 ≡ just initiatorError7a
initiatorError-mux-invoke = refl
initiatorError8 : D.State
initiatorError8 = at RF.initiatorError8 (initiatorErrorPayload) D.muxReturned
initiatorError-edge8 : D.step (D.observeInitiatorReturn owner) initiatorError7a ≡ just initiatorError8
initiatorError-edge8 = refl
initiatorError9 : D.State
initiatorError9 = at RF.initiatorError9 (initiatorErrorPayload) D.muxReturned
initiatorError-edge9 : D.step (runM (M.beginDead owner)) initiatorError8 ≡ just initiatorError9
initiatorError-edge9 = refl
initiatorError10 : D.State
initiatorError10 = at RF.initiatorError10 (initiatorErrorPayload) D.muxReturned
initiatorError-edge10 : D.step (runM (M.sampleTracer owner)) initiatorError9 ≡ just initiatorError10
initiatorError-edge10 = refl
initiatorError11 : D.State
initiatorError11 = at RF.initiatorError11 (initiatorErrorPayload) D.muxReturned
initiatorError-edge11 : D.step (runM (M.commitTracer owner)) initiatorError10 ≡ just initiatorError11
initiatorError-edge11 = refl
initiatorErrorInvoked initiatorErrorReturned : D.State
initiatorErrorInvoked = at RF.initiatorError11 (initiatorErrorPayload) D.invoked
initiatorErrorReturned = at RF.initiatorError12 (initiatorErrorPayload) D.returned
initiatorError-invoke : D.step (D.beginDeltaQ owner) initiatorError11 ≡ just initiatorErrorInvoked
initiatorError-invoke = refl
initiatorError-return : D.step (D.observeReturn owner) initiatorErrorInvoked ≡ just initiatorErrorReturned
initiatorError-return = refl
initiatorErrorActions : List D.Action
initiatorErrorActions = (runM (M.run (P.forkInitiator owner Old.j₁₁ Old.r₁ 1))) ∷ (runM (M.run (P.registerProtocol Old.j₁₁))) ∷ (runM (M.run (P.protocolException Old.j₁₁ Old.err))) ∷ (runM (M.run (P.returnProtocol Old.j₁₁))) ∷ (runM (M.run (P.publishProtocol Old.j₁₁))) ∷ (runM (M.consume owner)) ∷ (runM (M.handleSelected owner)) ∷ D.beginInitiatorTrace owner ∷ D.observeInitiatorReturn owner ∷ (runM (M.beginDead owner)) ∷ (runM (M.sampleTracer owner)) ∷ (runM (M.commitTracer owner)) ∷ (D.beginDeltaQ owner) ∷ (D.observeReturn owner) ∷ []
initiatorErrorPath : D.Executes initiatorError0 initiatorErrorActions initiatorErrorReturned
initiatorErrorPath = D.next initiatorError-edge1 (D.next initiatorError-edge2 (D.next initiatorError-edge3 (D.next initiatorError-edge4 (D.next initiatorError-edge5 (D.next initiatorError-edge6 (D.next initiatorError-edge7 (D.next initiatorError-mux-invoke (D.next initiatorError-edge8 (D.next initiatorError-edge9 (D.next initiatorError-edge10 (D.next initiatorError-edge11 (D.next initiatorError-invoke (D.next initiatorError-return (D.done))))))))))))))
muxer0 : D.State
muxer0 = empty RF.muxer0
muxer1 : D.State
muxer1 = empty RF.muxer1
muxer-edge1 : D.step (runM (M.run (P.infrastructureReturn owner T.muxer Old.err))) muxer0 ≡ just muxer1
muxer-edge1 = refl
muxer2 : D.State
muxer2 = empty RF.muxer2
muxer-edge2 : D.step (runM (M.run (P.publishInfra owner T.muxer))) muxer1 ≡ just muxer2
muxer-edge2 = refl
muxer3 : D.State
muxer3 = at RF.muxer3 (T.infraMuxer Old.err) D.captured
muxer-edge3 : D.step (runM (M.consume owner)) muxer2 ≡ just muxer3
muxer-edge3 = refl
muxer4 : D.State
muxer4 = at RF.muxer4 (T.infraMuxer Old.err) D.captured
muxer-edge4 : D.step (runM (M.handleSelected owner)) muxer3 ≡ just muxer4
muxer-edge4 = refl
muxer5 : D.State
muxer5 = at RF.muxer5 (T.infraMuxer Old.err) D.captured
muxer-edge5 : D.step (runM (M.beginDead owner)) muxer4 ≡ just muxer5
muxer-edge5 = refl
muxer6 : D.State
muxer6 = at RF.muxer6 (T.infraMuxer Old.err) D.captured
muxer-edge6 : D.step (runM (M.sampleTracer owner)) muxer5 ≡ just muxer6
muxer-edge6 = refl
muxer7 : D.State
muxer7 = at RF.muxer7 (T.infraMuxer Old.err) D.captured
muxer-edge7 : D.step (runM (M.commitTracer owner)) muxer6 ≡ just muxer7
muxer-edge7 = refl
muxer8 : D.State
muxer8 = at RF.muxer8 (T.infraMuxer Old.err) D.captured
muxer-edge8 : D.step (runM (M.finishDead owner)) muxer7 ≡ just muxer8
muxer-edge8 = refl
muxerActions : List D.Action
muxerActions = (runM (M.run (P.infrastructureReturn owner T.muxer Old.err))) ∷ (runM (M.run (P.publishInfra owner T.muxer))) ∷ (runM (M.consume owner)) ∷ (runM (M.handleSelected owner)) ∷ (runM (M.beginDead owner)) ∷ (runM (M.sampleTracer owner)) ∷ (runM (M.commitTracer owner)) ∷ (runM (M.finishDead owner)) ∷ []
muxerPath : D.Executes muxer0 muxerActions muxer8
muxerPath = D.next muxer-edge1 (D.next muxer-edge2 (D.next muxer-edge3 (D.next muxer-edge4 (D.next muxer-edge5 (D.next muxer-edge6 (D.next muxer-edge7 (D.next muxer-edge8 (D.done))))))))

abstract
  initialized-clean : D.Executes start (map D.run cleanPrefixActions ++ cleanActions) cleanReturned
  initialized-clean = Prefix.append initialized-clean-head cleanPath
  initialized-error : D.Executes start (errorPrefixActions ++ errorTailActions) errorTailReturned
  initialized-error = Prefix.append initialized-error-prefix errorTailPath
  initialized-initiator-clean : D.Executes start (errorPrefixActions ++ initiatorCleanActions) initiatorCleanReturned
  initialized-initiator-clean = Prefix.append initialized-error-prefix initiatorCleanPath
  initialized-initiator-error : D.Executes start (errorPrefixActions ++ initiatorErrorActions) initiatorErrorReturned
  initialized-initiator-error = Prefix.append initialized-error-prefix initiatorErrorPath
  initialized-infrastructure : D.Executes start (map D.run (Prior.wrappedActions Old.startActions) ++ muxerActions) muxer8
  initialized-infrastructure = Prefix.append (Prefix.lift C.initialized-monitor (Prefix.tag-nested Old.startActions)) muxerPath
clean-cannot-skip-DeltaQ : D.step (runM (M.finishProtocolTrace owner)) clean4 ≡ nothing
clean-cannot-skip-DeltaQ = refl
error-cannot-skip-DeltaQ : D.step (runM (M.finishDead owner)) errorTail11 ≡ nothing
error-cannot-skip-DeltaQ = refl
no-error-DeltaQ-before-Dead : D.step (D.beginDeltaQ owner) errorTail7 ≡ nothing
no-error-DeltaQ-before-Dead = refl
no-clean-DeltaQ-before-trace-return : D.step (D.beginDeltaQ owner) clean3 ≡ nothing
no-clean-DeltaQ-before-trace-return = refl
no-result-consumption-during-DeltaQ : D.step (runM (M.consume owner)) cleanInvoked ≡ nothing
no-result-consumption-during-DeltaQ = refl
no-whole-close-during-DeltaQ : D.step (D.run (R.run (X.run (W.run (G.beginWholeClose owner (Old.j₁ ∷ Old.j₀ ∷ [])))))) errorTailInvoked ≡ nothing
no-whole-close-during-DeltaQ = refl
no-DeltaQ-for-infrastructure : D.step (D.beginDeltaQ owner) muxer7 ≡ nothing
no-DeltaQ-for-infrastructure = refl
no-second-DeltaQ : D.step (D.beginDeltaQ owner) cleanReturned ≡ nothing
no-second-DeltaQ = refl
no-exception-without-invocation : D.step (D.observeException owner (R.sync (errorId 90))) clean4 ≡ nothing
no-exception-without-invocation = refl
clean-source-paths : Facts.Paths start cleanReturned
clean-source-paths = Facts.exec-projects initialized-clean
error-source-paths : Facts.Paths start errorTailReturned
error-source-paths = Facts.exec-projects initialized-error
clean-captures : Capture.Captures (D.source cleanReturned)
clean-captures = Facts.from-initial-captures actual-initializer initialized-clean
error-supply : Supply.Valid (D.source errorTailReturned)
error-supply = Facts.from-initial-supply actual-initializer Old.Prior.initial-bounds initialized-error

-- Tickets retain the exact consumed direction/number/generation/outcome.
clean-ticket-origin : Captured.CapturedHead owner clean0 clean1
clean-ticket-origin = Captured.consume-captures-head owner clean0 clean-edge1
initiator-ticket-origin : Captured.CapturedHead owner initiatorClean6 initiatorClean7
initiator-ticket-origin = Captured.consume-captures-head owner initiatorClean6 initiatorClean-edge7
infrastructure-ticket-origin : Captured.CapturedHead owner muxer2 muxer3
infrastructure-ticket-origin = Captured.consume-captures-head owner muxer2 muxer-edge3

initiator-cannot-skip-mux-tracer : D.step (D.beginDeltaQ owner) initiatorClean8 ≡ nothing
initiator-cannot-skip-mux-tracer = refl
initiator-error-cannot-skip-mux-tracer : D.step (runM (M.finishProtocolTrace owner)) initiatorError7 ≡ nothing
initiator-error-cannot-skip-mux-tracer = refl
legacy-mux-trace-failure-cannot-skip-invocation : D.step (D.run (R.observeFailure owner R.monitorTrace (errorId 90))) initiatorClean8 ≡ nothing
legacy-mux-trace-failure-cannot-skip-invocation = refl
initiator-clean-return-is-not-DeltaQ-return : M.pcAt owner (D.monitor initiatorCleanTraceReturned) ≡ M.initiatorTracing clean
initiator-clean-return-is-not-DeltaQ-return = refl
