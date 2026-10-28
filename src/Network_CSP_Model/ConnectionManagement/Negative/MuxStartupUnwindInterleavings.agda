{-# OPTIONS --guardedness #-}

-- Initialized partial-startup failure, actual current registry close and the
-- captured CM finally. Trace/provider faults are explicit source observations.
module ConnectionManagement.Negative.MuxStartupUnwindInterleavings where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (local; mux; worker)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as Shared
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as Machine
import ConnectionManagement.MuxStartupUnwind as Unwind
import ConnectionManagement.Properties.MuxStartupUnwind as UnwindFacts
import ConnectionManagement.Negative.MuxStartupUnwindFixtures as Fixture
import ConnectionManagement.MuxExitCancellation as Cancellation
import ConnectionManagement.Properties.MuxExitCancellation as CancellationFacts
import ConnectionManagement.MuxHandlerExit as Exit
import ConnectionManagement.Properties.MuxHandlerExit as ExitFacts
import ConnectionManagement.Negative.MuxHandlerExitFixtures as CleanupFixtures
import ConnectionManagement.Negative.MuxProtocolJobs as Old
import ConnectionManagement.Negative.MuxResultMonitor as RF
import ConnectionManagement.Negative.MuxGroupShutdown as GF
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.MuxJobTypes as T
import ConnectionManagement.Rules.Cleanup as C
import ConnectionManagement.Rules.HandlerLifecycle as Life
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
private
  module R = Unwind RF.bearerClosed
  module Facts = UnwindFacts RF.bearerClosed
  module X = Cancellation RF.bearerClosed
  module W = Exit RF.bearerClosed
  module Cancel = CancellationFacts RF.bearerClosed
  module ExitProof = ExitFacts RF.bearerClosed
  module G = W.G
  module M = G.M
  module P = G.P
  module U = G.U
  module S = G.Startup
  module Pool = G.Pool
  module F = Fixture RF.bearerClosed Old.owner Old.Prior.captured Old.mid
  module Clean = CleanupFixtures RF.bearerClosed Old.owner Old.Prior.captured
import ConnectionManagement.Negative.MuxStartupUnwind as Main
import ConnectionManagement.Rules.IGRegistration as IG
open import ConnectionManagement.Scenarios.Admission using (key₀)
open import ConnectionManagement.Store using (put)
owner : WorkerId
owner = Old.owner
err : ErrorId
err = Main.err
startup7Actions : List P.Action
startup7Actions = P.run (U.startupStep owner S.allocateBuffer) ∷ P.run (U.startupStep owner S.createBearer) ∷
  P.run (U.startupStep owner S.enterRun) ∷ P.run (U.startupStep owner S.traceStarting) ∷
  P.run (U.startupStep owner S.allocateEgress) ∷ P.run (U.startupStep owner S.openPool) ∷
  P.run (U.startupStep owner (S.forkMuxer Old.j₀)) ∷ []
startup7Path : P.Executes Old.c11 startup7Actions Old.z7
startup7Path = P.next Old.startup1 (P.next Old.startup2 (P.next Old.startup3 (P.next Old.startup4
  (P.next Old.startup5 (P.next Old.startup6 (P.next Old.startup7 P.done))))))
abstract
  initialized-masked-gap : R.Executes Main.start
    (Main.wrappedActions (Main.callerActions ++ startup7Actions)) (F.wrapP Old.z7)
  initialized-masked-gap = Main.liftP (Old.append Main.callerPath startup7Path) refl refl
no-ordinary-async-delivery-in-masked-fork-gap : R.step (R.observeCancellation owner R.unmaskedStartup err) (F.wrapP Old.z7) ≡ nothing
no-ordinary-async-delivery-in-masked-fork-gap = refl
no-invented-failed-second-fork-before-insertion : R.step (R.observeFailure owner R.secondFork err) (F.wrapP Old.z7) ≡ nothing
no-invented-failed-second-fork-before-insertion = refl

gap1 gap2 gap3 gap4 closed : Pool.State
gap1 = record Old.firstFork { handles = (Old.j₀ , Pool.bodyReturned (T.infraMuxer Old.err)) ∷ [] }
gap2 = record Old.firstFork
  { handles = (Old.j₀ , Pool.deregisterPending Pool.normalExit) ∷ []; completions = T.infraMuxer Old.err ∷ [] }
gap3 = record gap2 { registered = Old.j₀ ∷ []; parentFork = nothing }
gap4 = record gap3 { handles = (Old.j₀ , Pool.deregistered Pool.normalExit) ∷ []; registered = [] }
emptyClosing : Pool.State
emptyClosing = record gap4 { phase = Pool.closing }
closed = record gap4 { phase = Pool.closedPool }
fromPool : S.PC → Pool.State → P.State
fromPool pc pool = Old.at (P.source Old.z7) (S.startupState pc pool) [] []
h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 : R.State
h0 = F.wrapP Old.z7
h1 = F.wrapP (fromPool (S.muxerForked Old.j₀) gap1)
h2 = F.wrapP (fromPool (S.muxerForked Old.j₀) gap2)
h3 = F.wrapP (fromPool (S.muxerRegistered Old.j₀) gap3)
h4 = F.wrapP (fromPool (S.muxerRegistered Old.j₀) gap4)
h5 = F.selected (fromPool (S.muxerRegistered Old.j₀) gap4) (S.muxerRegistered Old.j₀) Mux.returned R.poolBody (R.sync err) R.awaitingClose
h6 = F.selected (fromPool (S.muxerRegistered Old.j₀) emptyClosing) (S.muxerRegistered Old.j₀) Mux.returned R.poolBody (R.sync err) R.closing
h7 = F.selected (fromPool (S.muxerRegistered Old.j₀) closed) (S.muxerRegistered Old.j₀) Mux.returned R.poolBody (R.sync err) R.poolClosed
h8 = F.selected (fromPool (S.muxerRegistered Old.j₀) closed) (S.muxerRegistered Old.j₀) Mux.returned R.poolBody (R.sync err) R.readyBuffer
h9 = F.withExit (W.bufferScope (G.failedExit err)) (F.selected (fromPool (S.muxerRegistered Old.j₀) closed) (S.muxerRegistered Old.j₀) Mux.returned R.poolBody (R.sync err) R.handedOff)
h-edge1 : R.step (R.run (X.run (W.run (G.run (M.run (P.infrastructureReturn owner T.muxer Old.err)))))) h0 ≡ just h1
h-edge1 = refl
h-edge2 : R.step (R.run (X.run (W.run (G.run (M.run (P.publishInfra owner T.muxer)))))) h1 ≡ just h2
h-edge2 = refl
h-edge3 : R.step (R.run (X.run (W.run (G.run (M.run (P.run (U.startupStep owner S.registerMuxer))))))) h2 ≡ just h3
h-edge3 = refl
h-edge4 : R.step (R.run (X.run (W.run (G.run (M.run (P.deregisterInfra owner T.muxer)))))) h3 ≡ just h4
h-edge4 = refl
h-edge5 : R.step (R.observeFailure owner R.secondFork err) h4 ≡ just h5
h-edge5 = refl
h-edge6 : R.step (R.beginClose owner []) h5 ≡ just h6
h-edge6 = refl
h-edge7 : R.step (R.finishClose owner) h6 ≡ just h7
h-edge7 = refl
h-edge8 : R.step (R.continueSync owner) h7 ≡ just h8
h-edge8 = refl
h-edge9 : R.step (R.handoff owner) h8 ≡ just h9
h-edge9 = refl
hActions : List R.Action
hActions = (R.run (X.run (W.run (G.run (M.run (P.infrastructureReturn owner T.muxer Old.err)))))) ∷ (R.run (X.run (W.run (G.run (M.run (P.publishInfra owner T.muxer)))))) ∷ (R.run (X.run (W.run (G.run (M.run (P.run (U.startupStep owner S.registerMuxer))))))) ∷ (R.run (X.run (W.run (G.run (M.run (P.deregisterInfra owner T.muxer)))))) ∷ (R.observeFailure owner R.secondFork err) ∷ (R.beginClose owner []) ∷ (R.finishClose owner) ∷ (R.continueSync owner) ∷ (R.handoff owner) ∷ []
hPath : R.Executes h0 hActions h9
hPath = (R.next h-edge1 (R.next h-edge2 (R.next h-edge3 (R.next h-edge4 (R.next h-edge5 (R.next h-edge6 (R.next h-edge7 (R.next h-edge8 (R.next h-edge9 R.done)))))))))
abstract
  initialized-removed-history-close : R.Executes Main.start
    (Main.wrappedActions (Main.callerActions ++ startup7Actions) ++ hActions) h9
  initialized-removed-history-close = Facts.append initialized-masked-gap hPath
child-cannot-remove-before-parent-insert : R.step (R.run (X.run (W.run (G.run (M.run (P.deregisterInfra owner T.muxer)))))) h2 ≡ nothing
child-cannot-remove-before-parent-insert = refl
no-late-historical-recapture : R.step (R.beginClose owner (Old.j₀ ∷ [])) h5 ≡ nothing
no-late-historical-recapture = refl
removed-handle-is-not-an-Async-result : lookup Old.j₀ (Pool.handles (R.poolAt owner h9)) ≡ just (Pool.deregistered Pool.normalExit)
removed-handle-is-not-an-Async-result = refl
removed-history-not-snapshot : Pool.snapshot (R.poolAt owner h9) ≡ []
removed-history-not-snapshot = refl
physical-result-queue-preserved-without-monitor : Pool.completions (R.poolAt owner h9) ≡ T.infraMuxer Old.err ∷ []
physical-result-queue-preserved-without-monitor = refl

-- A real start-trace call before the mini-protocol fork. A synchronous custom
-- tracer exception does not fabricate a source callback return or Failed/Dead.
tracePrefixActions : List P.Action
tracePrefixActions = Old.startActions ++ (P.control owner P.selectCommand ∷ P.control owner (P.demand 1) ∷ [])
tracePrefixPath : P.Executes Old.b0 tracePrefixActions Old.r2
tracePrefixPath = Old.append Old.initialized-start (P.next Old.responder1 (P.next Old.responder2 P.done))
abstract
  initialized-trace-entry : R.Executes Main.start (Main.wrappedActions tracePrefixActions) (F.wrapP Old.r2)
  initialized-trace-entry = Main.liftP tracePrefixPath refl refl
tracePC : S.PC
tracePC = S.monitoring Old.j₀ Old.j₁
atTracePool : Pool.State → P.State
atTracePool pool = Old.at (P.source Old.r2) (S.startupState tracePC pool) [] []
failedTrace : Pool.State → R.PC → R.State
failedTrace pool pc = F.selected (atTracePool pool) tracePC (Mux.readActive (Mux.started 1)) R.poolBody (R.sync err) pc
t0 t1 : R.State
t0 = F.wrapP Old.r2
t1 = failedTrace Main.k0 R.awaitingClose
t-edge1 : R.step (R.observeFailure owner R.monitorTrace err) t0 ≡ just t1
t-edge1 = refl
t2 : R.State
t2 = failedTrace Main.k1 R.closing
t-edge2 : R.step (R.beginClose owner (Old.j₁ ∷ Old.j₀ ∷ [])) t1 ≡ just t2
t-edge2 = refl
t3 : R.State
t3 = failedTrace Main.k2 R.closing
t-edge3 : R.step (R.requestCancel owner) t2 ≡ just t3
t-edge3 = refl
t4 : R.State
t4 = failedTrace Main.k3 R.closing
t-edge4 : R.step (R.deliverCancel owner) t3 ≡ just t4
t-edge4 = refl
t5 : R.State
t5 = failedTrace Main.k4 R.closing
t-edge5 : R.step (R.run (X.run (W.run (G.finishChildUnwind Old.j₁)))) t4 ≡ just t5
t-edge5 = refl
t6 : R.State
t6 = failedTrace Main.k5 R.closing
t-edge6 : R.step (R.run (X.run (W.run (G.run (M.run (P.deregisterInfra owner T.demuxer)))))) t5 ≡ just t6
t-edge6 = refl
t7 : R.State
t7 = failedTrace Main.k6 R.closing
t-edge7 : R.step (R.run (X.run (W.run (G.run (M.run (P.asyncInfraResult owner T.demuxer)))))) t6 ≡ just t7
t-edge7 = refl
t8 : R.State
t8 = failedTrace Main.k7 R.closing
t-edge8 : R.step (R.join owner) t7 ≡ just t8
t-edge8 = refl
t9 : R.State
t9 = failedTrace Main.k8 R.closing
t-edge9 : R.step (R.requestCancel owner) t8 ≡ just t9
t-edge9 = refl
t10 : R.State
t10 = failedTrace Main.k9 R.closing
t-edge10 : R.step (R.deliverCancel owner) t9 ≡ just t10
t-edge10 = refl
t11 : R.State
t11 = failedTrace Main.k10 R.closing
t-edge11 : R.step (R.run (X.run (W.run (G.finishChildUnwind Old.j₀)))) t10 ≡ just t11
t-edge11 = refl
t12 : R.State
t12 = failedTrace Main.k11 R.closing
t-edge12 : R.step (R.run (X.run (W.run (G.run (M.run (P.deregisterInfra owner T.muxer)))))) t11 ≡ just t12
t-edge12 = refl
t13 : R.State
t13 = failedTrace Main.k12 R.closing
t-edge13 : R.step (R.run (X.run (W.run (G.run (M.run (P.asyncInfraResult owner T.muxer)))))) t12 ≡ just t13
t-edge13 = refl
t14 : R.State
t14 = failedTrace Main.k13 R.closing
t-edge14 : R.step (R.join owner) t13 ≡ just t14
t-edge14 = refl
t15 : R.State
t15 = failedTrace Main.k14 R.poolClosed
t-edge15 : R.step (R.finishClose owner) t14 ≡ just t15
t-edge15 = refl
t16 t17 : R.State
t16 = failedTrace Main.k14 R.readyBuffer
t17 = F.withExit (W.bufferScope (G.failedExit err)) (failedTrace Main.k14 R.handedOff)
t-edge16 : R.step (R.continueSync owner) t15 ≡ just t16
t-edge16 = refl
t-edge17 : R.step (R.handoff owner) t16 ≡ just t17
t-edge17 = refl
tActions : List R.Action
tActions = (R.observeFailure owner R.monitorTrace err) ∷ (R.beginClose owner (Old.j₁ ∷ Old.j₀ ∷ [])) ∷ (R.requestCancel owner) ∷ (R.deliverCancel owner) ∷ (R.run (X.run (W.run (G.finishChildUnwind Old.j₁)))) ∷ (R.run (X.run (W.run (G.run (M.run (P.deregisterInfra owner T.demuxer)))))) ∷ (R.run (X.run (W.run (G.run (M.run (P.asyncInfraResult owner T.demuxer)))))) ∷ (R.join owner) ∷ (R.requestCancel owner) ∷ (R.deliverCancel owner) ∷ (R.run (X.run (W.run (G.finishChildUnwind Old.j₀)))) ∷ (R.run (X.run (W.run (G.run (M.run (P.deregisterInfra owner T.muxer)))))) ∷ (R.run (X.run (W.run (G.run (M.run (P.asyncInfraResult owner T.muxer)))))) ∷ (R.join owner) ∷ (R.finishClose owner) ∷ (R.continueSync owner) ∷ (R.handoff owner) ∷ []
tPath : R.Executes t0 tActions t17
tPath = (R.next t-edge1 (R.next t-edge2 (R.next t-edge3 (R.next t-edge4 (R.next t-edge5 (R.next t-edge6 (R.next t-edge7 (R.next t-edge8 (R.next t-edge9 (R.next t-edge10 (R.next t-edge11 (R.next t-edge12 (R.next t-edge13 (R.next t-edge14 (R.next t-edge15 (R.next t-edge16 (R.next t-edge17 R.done)))))))))))))))))
abstract
  initialized-tracer-failure-close : R.Executes Main.start (Main.wrappedActions tracePrefixActions ++ tActions) t17
  initialized-tracer-failure-close = Facts.append initialized-trace-entry tPath
no-abandoned-callback-return : P.muxAt Old.mid (R.protocols t17) ≡ just Old.m2
no-abandoned-callback-return = refl
no-abandoned-tracer-read : R.step (R.run (X.run (W.run (G.run (M.run (P.control owner P.sampleTracer)))))) t1 ≡ nothing
no-abandoned-tracer-read = refl
no-start-fork-after-tracer-fault : R.step (R.run (X.run (W.run (G.run (M.run (P.forkResponder owner Old.j₁₀ Old.r₀)))))) t1 ≡ nothing
no-start-fork-after-tracer-fault = refl
no-miniprotocol-was-created : P.jobs (R.protocols t17) ≡ []
no-miniprotocol-was-created = refl

-- Conditional successor-registration view: not an initialized second-handler
-- history. The actual interpreter must record descriptor failure first; a
-- pending STM commit alone is not such a source exception certificate.
replacementInfo : Shared.NewConnectionInfo
replacementInfo = Shared.newConnectionInfo outbound key₀ duplex (ident 1)
retarget : O.Configuration → O.Configuration
retarget c = record c { core = record (O.core c) { inboundGovernor = replaced } }
  where
  old : IG.Runtime
  old = Machine.inboundGovernor (O.core c)
  replaced : IG.Runtime
  replaced = record old
    { publishedState = record (IG.publishedState old)
        { connections = put key₀ (IG.registered replacementInfo (ident 1)) (IG.connections (IG.publishedState old)) }
    ; execution = record (IG.execution old)
        { handles = put (ident 1) (Mux.handleState (ident 1) [] duplex) (IG.handles (IG.execution old))
        ; muxes = put (ident 1) (record Old.G.newMux { protocols = [] }) (IG.muxes (IG.execution old)) } }
conditionalSource0 conditionalSource1 : O.Configuration
conditionalSource0 = retarget (P.source Old.r3)
conditionalSource1 = record conditionalSource0 { core = record (O.core conditionalSource0)
  { inboundGovernor = IG.setMux Old.mid (record Old.m3 { callback = Mux.tracerFailed 1 }) (Machine.inboundGovernor (O.core conditionalSource0)) } }
c0 c1 c2 : R.State
c0 = F.wrapP (Old.at conditionalSource0 (S.startupState tracePC Old.engines) [] [])
c1 = F.wrapP (Old.at conditionalSource1 (S.startupState tracePC Old.engines) [] [])
c2 = F.selected (Old.at conditionalSource1 (S.startupState tracePC Old.engines) [] []) tracePC (Mux.tracerFailed 1) R.poolBody (R.sync err) R.awaitingClose
pending-STM-is-not-proved-thrown : R.step (R.observeFailure owner R.monitorTrace err) c0 ≡ nothing
pending-STM-is-not-proved-thrown = refl
actual-descriptor-failure : R.step (R.run (X.run (W.run (G.run (M.run (P.control owner P.commitTracer)))))) c0 ≡ just c1
actual-descriptor-failure = refl
verified-failure-enters-unwind : R.step (R.observeFailure owner R.monitorTrace err) c1 ≡ just c2
verified-failure-enters-unwind = refl
conditional-failure-rolls-back-trace-publish : Shared.inboundInfo (Machine.world (O.core (R.source c1))) ≡ []
conditional-failure-rolls-back-trace-publish = refl
conditional-failure-does-not-return-callback : P.muxAt Old.mid (R.protocols c2) ≡ just (record Old.m3 { callback = Mux.tracerFailed 1 })
conditional-failure-does-not-return-callback = refl
historical-source-pools : Facts.Paths Main.start h9
historical-source-pools = Facts.exec-projects initialized-removed-history-close
tracer-source-pools : Facts.Paths Main.start t17
tracer-source-pools = Facts.exec-projects initialized-tracer-failure-close
