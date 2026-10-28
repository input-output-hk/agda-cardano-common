{-# OPTIONS --guardedness #-}

-- Initialized async delivery in a held responder completion callback and after
-- a start callback's committed STM effects. Named async observations are inputs;
-- no timer/provider progress or source implementation refinement is inferred.
module ConnectionManagement.Negative.MuxCallbackCancellation where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import ConnectionManagement.Scenarios.Admission using (key₀)
open import ConnectionManagement.Domain hiding (worker; local; mux)
open import ConnectionManagement.IGTypes using (clean)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.MuxStartupUnwind as Unwind
import ConnectionManagement.Properties.MuxStartupUnwind as Proof
import ConnectionManagement.MuxExitCancellation as Cancellation
import ConnectionManagement.Properties.MuxExitCancellation as CancellationProof
import ConnectionManagement.MuxHandlerExit as Exit
import ConnectionManagement.Properties.MuxHandlerExit as ExitProof
import ConnectionManagement.Negative.MuxProtocolJobs as Old
import ConnectionManagement.Negative.MuxResultMonitor as RF
import ConnectionManagement.Negative.MuxGroupShutdown as GF
import ConnectionManagement.Negative.MuxStartupUnwind as Prior
import ConnectionManagement.Negative.MuxStartupUnwindFixtures as Fixture
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.MuxJobTypes as T
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.CMShutdown as Close
private
  module R = Unwind RF.bearerClosed
  module Facts = Proof RF.bearerClosed
  module X = Cancellation RF.bearerClosed
  module Cancel = CancellationProof RF.bearerClosed
  module W = Exit RF.bearerClosed
  module ExitFacts = ExitProof RF.bearerClosed
  module G = W.G
  module M = G.M
  module P = G.P
  module S = G.Startup
  module Pool = G.Pool
  module F = Fixture RF.bearerClosed Old.owner Old.Prior.captured Old.mid
owner : WorkerId
owner = Old.owner
err : ErrorId
err = errorId 89
wrapM : M.State → R.State
wrapM m = R.unwinding (W.handlerExitState (G.shutdownState m []) []) []
wrapAction : M.Action → R.Action
wrapAction a = R.run (X.run (W.run (G.run a)))
wrapP : P.Action → R.Action
wrapP a = wrapAction (M.run a)
fuse : ∀ actions → map R.run (map X.run (map W.run (map G.run actions))) ≡ map wrapAction actions
fuse [] = refl
fuse (a ∷ rest) rewrite fuse rest = refl
liftM : ∀ {m actions n} → M.Executes m actions n → GF.prefixAll actions ≡ true →
  ExitFacts.allSafe (map G.run actions) ≡ true →
  R.Executes (wrapM m) (map wrapAction actions) (wrapM n)
liftM {actions = actions} path safe exitSafe rewrite sym (fuse actions) = Facts.lift (Cancel.lift (ExitFacts.lift-path (GF.lift-path path safe) exitSafe))

-- The successful fork/body/result prefix remains the existing source path.
-- Each additional inherited step below retains its actual state-dependent guard.
abstract
  initialized-monitor : R.Executes Prior.start (Prior.wrappedActions Old.startActions) (F.wrapP Old.z12)
  initialized-monitor = Prior.liftP Old.initialized-start refl refl
prefix1 : R.step (wrapP (P.control owner P.selectCommand)) (F.wrapP Old.z12) ≡ just (F.wrapP Old.r1)
prefix1 = refl
prefix2 : R.step (wrapP (P.control owner (P.demand 1))) (F.wrapP Old.r1) ≡ just (F.wrapP Old.r2)
prefix2 = refl
prefix3 : R.step (wrapP (P.control owner P.sampleTracer)) (F.wrapP Old.r2) ≡ just (F.wrapP Old.r3)
prefix3 = refl
prefix4 : R.step (wrapP (P.control owner P.commitTracer)) (F.wrapP Old.r3) ≡ just (F.wrapP Old.r4)
prefix4 = refl
prefix5 : R.step (wrapP (P.control owner P.finishStart)) (F.wrapP Old.r4) ≡ just (F.wrapP Old.r5)
prefix5 = refl
prefix6 : R.step (wrapP (P.forkResponder owner Old.j₁₀ Old.r₀)) (F.wrapP Old.r5) ≡ just (F.wrapP Old.r6)
prefix6 = refl
prefix7 : R.step (wrapP (P.protocolReturned Old.j₁₀)) (F.wrapP Old.r6) ≡ just (F.wrapP Old.r7)
prefix7 = refl
prefix8 : R.step (wrapP (P.commitClean Old.j₁₀)) (F.wrapP Old.r7) ≡ just (F.wrapP Old.r8)
prefix8 = refl
prefix9 : R.step (wrapP (P.returnProtocol Old.j₁₀)) (F.wrapP Old.r8) ≡ just (F.wrapP Old.r9)
prefix9 = refl
prefix10 : R.step (wrapP (P.publishProtocol Old.j₁₀)) (F.wrapP Old.r9) ≡ just (F.wrapP Old.r10)
prefix10 = refl
prefix11 : R.step (wrapP (P.registerProtocol Old.j₁₀)) (F.wrapP Old.r10) ≡ just (F.wrapP Old.r11)
prefix11 = refl
prefix12 : R.step (wrapP (P.deregisterProtocol Old.j₁₀)) (F.wrapP Old.r11) ≡ just (F.wrapP Old.r12)
prefix12 = refl
prefix13 : R.step (wrapP (P.asyncProtocolResult Old.j₁₀)) (F.wrapP Old.r12) ≡ just (F.wrapP Old.r13)
prefix13 = refl
prefixActions : List R.Action
prefixActions = wrapP (P.control owner P.selectCommand) ∷ wrapP (P.control owner (P.demand 1)) ∷ wrapP (P.control owner P.sampleTracer) ∷ wrapP (P.control owner P.commitTracer) ∷ wrapP (P.control owner P.finishStart) ∷ wrapP (P.forkResponder owner Old.j₁₀ Old.r₀) ∷ wrapP (P.protocolReturned Old.j₁₀) ∷ wrapP (P.commitClean Old.j₁₀) ∷ wrapP (P.returnProtocol Old.j₁₀) ∷ wrapP (P.publishProtocol Old.j₁₀) ∷ wrapP (P.registerProtocol Old.j₁₀) ∷ wrapP (P.deregisterProtocol Old.j₁₀) ∷ wrapP (P.asyncProtocolResult Old.j₁₀) ∷ []
prefixPath : R.Executes (F.wrapP Old.z12) prefixActions (wrapM RF.clean0)
prefixPath = R.next prefix1 (R.next prefix2 (R.next prefix3 (R.next prefix4 (R.next prefix5 (R.next prefix6 (R.next prefix7 (R.next prefix8 (R.next prefix9 (R.next prefix10 (R.next prefix11 (R.next prefix12 (R.next prefix13 (R.done)))))))))))))
abstract
  initialized-result : R.Executes Prior.start (Prior.wrappedActions Old.startActions ++ prefixActions) (wrapM RF.clean0)
  initialized-result = Facts.append initialized-monitor prefixPath
heldActions : List M.Action
heldActions = M.consume owner ∷ M.handleSelected owner ∷ M.sampleTracer owner ∷ []
heldPath : M.Executes RF.clean0 heldActions RF.clean3
heldPath = M.next RF.clean-edge1 (M.next RF.clean-edge2 (M.next RF.clean-edge3 M.done))
abstract
  initialized-held : R.Executes Prior.start
    ((Prior.wrappedActions Old.startActions ++ prefixActions) ++ map wrapAction heldActions) (wrapM RF.clean3)
  initialized-held = Facts.append initialized-result (liftM heldPath refl refl)

-- Data-only flat snapshots avoid normalizing prior controller steps repeatedly.
heldMux : Mux.Mux
heldMux = record Old.publishedMux { completions = []; callback = Mux.commitTrace true (Mux.completed 1 clean) }
heldPool : Pool.State → Pool.State
heldPool p = record p { handles = Pool.handles p ++ ((Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) }
held : Mux.Mux → List Shared.IGEvent → Pool.State → R.PC → R.State
held m q pool pc = R.unwinding
  (W.handlerExitState (G.shutdownState
    (M.monitorState (Old.snapshot (Old.sourceMux m q) (heldPool pool)
      ((Old.j₁₀ , Old.rJob (T.resultCaptured clean)) ∷ []) ((owner , []) ∷ []))
      ((owner , M.responderTracing clean) ∷ [])) []) [])
  ((owner , R.fault Old.Prior.captured Old.mid (S.monitoring Old.j₀ Old.j₁)
    (Mux.callback heldMux) R.poolBody (R.async err) pc) ∷ [])
h0 : R.State
h0 = wrapM RF.clean3
h1 : R.State
h1 = held heldMux Old.messages Prior.k0 R.awaitingClose
h-edge1 : R.step (R.observeCancellation owner R.unmaskedMuxCallback err) h0 ≡ just h1
h-edge1 = refl
h2 : R.State
h2 = held heldMux Old.messages Prior.k1 R.closing
h-edge2 : R.step (R.beginClose owner (Old.j₁ ∷ Old.j₀ ∷ [])) h1 ≡ just h2
h-edge2 = refl
h3 : R.State
h3 = held heldMux Old.messages Prior.k2 R.closing
h-edge3 : R.step (R.requestCancel owner) h2 ≡ just h3
h-edge3 = refl
h4 : R.State
h4 = held heldMux Old.messages Prior.k3 R.closing
h-edge4 : R.step (R.deliverCancel owner) h3 ≡ just h4
h-edge4 = refl
h5 : R.State
h5 = held heldMux Old.messages Prior.k4 R.closing
h-edge5 : R.step (R.run (X.run (W.run (G.finishChildUnwind Old.j₁)))) h4 ≡ just h5
h-edge5 = refl
h6 : R.State
h6 = held heldMux Old.messages Prior.k5 R.closing
h-edge6 : R.step (wrapP (P.deregisterInfra owner T.demuxer)) h5 ≡ just h6
h-edge6 = refl
h7 : R.State
h7 = held heldMux Old.messages Prior.k6 R.closing
h-edge7 : R.step (wrapP (P.asyncInfraResult owner T.demuxer)) h6 ≡ just h7
h-edge7 = refl
h8 : R.State
h8 = held heldMux Old.messages Prior.k7 R.closing
h-edge8 : R.step (R.join owner) h7 ≡ just h8
h-edge8 = refl
h9 : R.State
h9 = held heldMux Old.messages Prior.k8 R.closing
h-edge9 : R.step (R.requestCancel owner) h8 ≡ just h9
h-edge9 = refl
h10 : R.State
h10 = held heldMux Old.messages Prior.k9 R.closing
h-edge10 : R.step (R.deliverCancel owner) h9 ≡ just h10
h-edge10 = refl
h11 : R.State
h11 = held heldMux Old.messages Prior.k10 R.closing
h-edge11 : R.step (R.run (X.run (W.run (G.finishChildUnwind Old.j₀)))) h10 ≡ just h11
h-edge11 = refl
h12 : R.State
h12 = held heldMux Old.messages Prior.k11 R.closing
h-edge12 : R.step (wrapP (P.deregisterInfra owner T.muxer)) h11 ≡ just h12
h-edge12 = refl
h13 : R.State
h13 = held heldMux Old.messages Prior.k12 R.closing
h-edge13 : R.step (wrapP (P.asyncInfraResult owner T.muxer)) h12 ≡ just h13
h-edge13 = refl
h14 : R.State
h14 = held heldMux Old.messages Prior.k13 R.closing
h-edge14 : R.step (R.join owner) h13 ≡ just h14
h-edge14 = refl
h15 : R.State
h15 = held heldMux Old.messages Prior.k14 R.poolClosed
h-edge15 : R.step (R.finishClose owner) h14 ≡ just h15
h-edge15 = refl
h16 : R.State
h16 = held (record heldMux { status = Mux.failed err }) Old.messages Prior.k14 R.asyncStatus
h-edge16 : R.step (R.writeAsyncFailure owner) h15 ≡ just h16
h-edge16 = refl
h17 : R.State
h17 = held (record heldMux { status = Mux.failed err; callback = Mux.readActive Mux.muxStopped }) Old.messages Prior.k14 R.asyncDead
h-edge17 : R.step (R.beginDead owner) h16 ≡ just h17
h-edge17 = refl
h18 : R.State
h18 = held (record heldMux { status = Mux.failed err; callback = Mux.commitTrace true Mux.muxStopped }) Old.messages Prior.k14 R.asyncDead
h-edge18 : R.step (R.sampleDead owner) h17 ≡ just h18
h-edge18 = refl
h19 : R.State
h19 = held (record heldMux { status = Mux.failed err; callback = Mux.returned; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ [])) Prior.k14 R.asyncDead
h-edge19 : R.step (R.commitDead owner) h18 ≡ just h19
h-edge19 = refl
h20 : R.State
h20 = held (record heldMux { status = Mux.failed err; callback = Mux.returned; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ [])) Prior.k14 R.readyBuffer
h-edge20 : R.step (R.finishDead owner) h19 ≡ just h20
h-edge20 = refl
h21 : R.State
h21 = F.withExit (W.bufferScope (G.asyncExit err)) (held (record heldMux { status = Mux.failed err; callback = Mux.returned; traceCounters = nothing }) (Old.messages ++ (Shared.muxFinished key₀ ∷ [])) Prior.k14 R.handedOff)
h-edge21 : R.step (R.handoff owner) h20 ≡ just h21
h-edge21 = refl
hActions : List R.Action
hActions = (R.observeCancellation owner R.unmaskedMuxCallback err) ∷ (R.beginClose owner (Old.j₁ ∷ Old.j₀ ∷ [])) ∷ (R.requestCancel owner) ∷ (R.deliverCancel owner) ∷ (R.run (X.run (W.run (G.finishChildUnwind Old.j₁)))) ∷ (wrapP (P.deregisterInfra owner T.demuxer)) ∷ (wrapP (P.asyncInfraResult owner T.demuxer)) ∷ (R.join owner) ∷ (R.requestCancel owner) ∷ (R.deliverCancel owner) ∷ (R.run (X.run (W.run (G.finishChildUnwind Old.j₀)))) ∷ (wrapP (P.deregisterInfra owner T.muxer)) ∷ (wrapP (P.asyncInfraResult owner T.muxer)) ∷ (R.join owner) ∷ (R.finishClose owner) ∷ (R.writeAsyncFailure owner) ∷ (R.beginDead owner) ∷ (R.sampleDead owner) ∷ (R.commitDead owner) ∷ (R.finishDead owner) ∷ (R.handoff owner) ∷ []
hPath : R.Executes h0 hActions h21
hPath = R.next h-edge1 (R.next h-edge2 (R.next h-edge3 (R.next h-edge4 (R.next h-edge5 (R.next h-edge6 (R.next h-edge7 (R.next h-edge8 (R.next h-edge9 (R.next h-edge10 (R.next h-edge11 (R.next h-edge12 (R.next h-edge13 (R.next h-edge14 (R.next h-edge15 (R.next h-edge16 (R.next h-edge17 (R.next h-edge18 (R.next h-edge19 (R.next h-edge20 (R.next h-edge21 (R.done)))))))))))))))))))))
abstract
  initialized-callback-close : R.Executes Prior.start
    (((Prior.wrappedActions Old.startActions ++ prefixActions) ++ map wrapAction heldActions) ++ hActions) h21
  initialized-callback-close = Facts.append initialized-held hPath
no-early-failed : R.step (R.writeAsyncFailure owner) h1 ≡ nothing
no-early-failed = refl
no-early-dead : R.step (R.beginDead owner) h15 ≡ nothing
no-early-dead = refl
no-abandoned-commit : R.step (wrapAction (M.commitTracer owner)) h1 ≡ nothing
no-abandoned-commit = refl
no-abandoned-monitor-return : R.step (wrapAction (M.finishProtocolTrace owner)) h1 ≡ nothing
no-abandoned-monitor-return = refl
no-premature-provider-handoff : R.step (R.handoff owner) h15 ≡ nothing
no-premature-provider-handoff = refl
held-result-still-held : M.pcAt owner (G.base (W.base (R.base h21))) ≡ M.responderTracing clean
held-result-still-held = refl
callback-not-returned-by-status-write : P.muxAt Old.mid (R.protocols h16) ≡ just (record heldMux { status = Mux.failed err })
callback-not-returned-by-status-write = refl
snapshot-keeps-abandoned-callback : lookup owner (R.faults h21) ≡ just
  (R.fault Old.Prior.captured Old.mid (S.monitoring Old.j₀ Old.j₁)
    (Mux.callback heldMux) R.poolBody (R.async err) R.handedOff)
snapshot-keeps-abandoned-callback = refl
old-completion-transaction-never-committed : Shared.inboundInfo (Machine.world (O.core (R.source h16))) ≡ Old.messages
old-completion-transaction-never-committed = refl
old-counters-not-decremented : Mux.traceCounters heldMux ≡ Mux.traceCounters Old.publishedMux
old-counters-not-decremented = refl
actual-whole-snapshot : Pool.snapshot (R.poolAt owner h21) ≡ Old.j₁ ∷ Old.j₀ ∷ []
actual-whole-snapshot = refl
no-physical-result-requeued : Pool.completions (R.poolAt owner h21) ≡ []
no-physical-result-requeued = refl
actual-initializer : R.initial (O.initial Old.F.start) ≡ just Prior.start
actual-initializer = refl
source-and-pool-paths : Facts.Paths Prior.start h21
source-and-pool-paths = Facts.exec-projects initialized-callback-close

-- The pre-existing successful-return helper is deliberately unchanged.
old-helper-refuses-abandoned-callback : IG.step Shared.responderMode (IG.recordAsyncMuxFailure Old.mid err)
  (Machine.inboundGovernor (O.core (R.source h15))) Old.messages ≡ nothing
old-helper-refuses-abandoned-callback = refl

-- Before the active read the same route retains the unsampled callback.
beforeActive : R.State
beforeActive = R.unwinding (R.base (wrapM RF.clean2))
  ((owner , R.fault Old.Prior.captured Old.mid (S.monitoring Old.j₀ Old.j₁)
    (Mux.readActive (Mux.completed 1 clean)) R.poolBody (R.async err) R.awaitingClose) ∷ [])
delivery-before-active-read : R.step (R.observeCancellation owner R.unmaskedMuxCallback err)
  (wrapM RF.clean2) ≡ just beforeActive
delivery-before-active-read = refl
ordinary-dead-refuses-abandoned-callback : IG.step Shared.responderMode (IG.traceMuxDead Old.mid)
  (Machine.inboundGovernor (O.core (R.source h16))) Old.messages ≡ nothing
ordinary-dead-refuses-abandoned-callback = refl
no-callback-delivery-before-handler-birth : R.step (R.observeCancellation owner R.unmaskedMuxCallback err) Prior.start ≡ nothing
no-callback-delivery-before-handler-birth = refl
