{-# OPTIONS --guardedness #-}

-- Initialized initiator mux-tracer exceptions with a live responder in the
-- same physical pool. No initiator-return, Dead or DeltaQ is fabricated;
-- named tracer/provider outcomes remain inputs, not universal progress claims.
module ConnectionManagement.Negative.MuxInitiatorTraceEffects where

open import Data.Bool using (true; false)
open import Data.Nat using (ℕ)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; _++_; map; take)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (worker; mux; local)
open import ConnectionManagement.IGTypes using (RunResult; clean; errored)
open import ConnectionManagement.Store using (Store; lookup)
open import ConnectionManagement.Scenarios.Admission using (key₀)
import ConnectionManagement.Negative.MuxDeltaQ as Base
import ConnectionManagement.Negative.MuxProtocolJobs as Old
import ConnectionManagement.Negative.MuxResultMonitor as RF
import ConnectionManagement.Negative.MuxPoolCloseFixtures as PoolFixtures
import ConnectionManagement.Negative.MuxStartupUnwindFixtures as Fixture
import ConnectionManagement.Negative.MuxHandlerExitFixtures as CleanupFixtures
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.MuxJobTypes as T
import ConnectionManagement.Rules.HandlerLifecycle as Life
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as Machine
import ConnectionManagement.State as Shared
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
module D = Base.D
module Facts = Base.Facts
module Prefix = Base.Prefix
module R = D.R
module X = D.X
module W = D.W
module G = D.G
module M = D.M
module P = D.P
module S = G.Startup
module Pool = D.Pool
module Tail = PoolFixtures Old.j₀ Old.j₁
-- Data-only snapshots: each use below is justified by an actual transition.
module K where
  order : List JobId
  order = Old.j₁₀ ∷ Old.j₁ ∷ Old.j₀ ∷ []
  live : Pool.State
  live = record Tail.k0 { handles = Pool.handles Tail.k0 ++ ((Old.j₁₀ , Pool.bodyRunning) ∷ [])
    ; registered = order }
  pending : Pool.ThreadPhase → Pool.ClosePC → List JobId → Pool.State
  pending body phase registry = record live
    { handles = Pool.handles Tail.k0 ++ ((Old.j₁₀ , body) ∷ [])
    ; registered = registry; phase = phase; snapshot = order; remaining = order }
  r0 r1 r2 r3 r4 r5 : Pool.State
  r0 = pending Pool.bodyRunning Pool.closing order
  r1 = pending Pool.bodyRunning (Pool.cancelPending Old.j₁₀) order
  r2 = pending Pool.bodyUnwinding (Pool.joinPending Old.j₁₀) order
  r3 = pending (Pool.deregisterPending Pool.cancelledExit) (Pool.joinPending Old.j₁₀) order
  r4 = pending (Pool.deregistered Pool.cancelledExit) (Pool.joinPending Old.j₁₀) (Old.j₁ ∷ Old.j₀ ∷ [])
  r5 = pending (Pool.resultAvailable Pool.cancelledExit) (Pool.joinPending Old.j₁₀) (Old.j₁ ∷ Old.j₀ ∷ [])
  extend : Pool.State → Pool.State
  extend p = record p
    { handles = Pool.handles p ++ ((Old.j₁₀ , Pool.resultAvailable Pool.cancelledExit) ∷ [])
    ; snapshot = Old.j₁₀ ∷ Pool.snapshot p; joined = Old.j₁₀ ∷ Pool.joined p }
  k0 : Pool.State
  k0 = live
  k1 : Pool.State
  k1 = extend Tail.k1
  k2 : Pool.State
  k2 = extend Tail.k2
  k3 : Pool.State
  k3 = extend Tail.k3
  k4 : Pool.State
  k4 = extend Tail.k4
  k5 : Pool.State
  k5 = extend Tail.k5
  k6 : Pool.State
  k6 = extend Tail.k6
  k7 : Pool.State
  k7 = extend Tail.k7
  k8 : Pool.State
  k8 = extend Tail.k8
  k9 : Pool.State
  k9 = extend Tail.k9
  k10 : Pool.State
  k10 = extend Tail.k10
  k11 : Pool.State
  k11 = extend Tail.k11
  k12 : Pool.State
  k12 = extend Tail.k12
  k13 : Pool.State
  k13 = extend Tail.k13
  k14 : Pool.State
  k14 = extend Tail.k14
module F = Fixture RF.bearerClosed Old.owner Old.Prior.captured Old.mid
module Clean = CleanupFixtures RF.bearerClosed Old.owner Old.Prior.captured
owner : WorkerId
owner = Old.owner
err : ErrorId
err = errorId 90

data Origin : Set where
  cleanCompletion errorCompletion : Origin
outcome : Origin → RunResult
outcome cleanCompletion = clean
outcome errorCompletion = errored Old.err
payload : Origin → T.TypedResult
payload origin = T.protocolCompletion Mux.initiatorJob 1 Old.r₁ (outcome origin)
status : Origin → Mux.Status
status cleanCompletion = Mux.ready
status errorCompletion = Mux.failed Old.err
counters : Origin → Maybe Mux.Counters
counters _ = Mux.traceCounters Old.m6
mux : Origin → Mux.Mux
mux origin = record Old.m6 { status = status origin }
queue : Origin → List Shared.IGEvent
queue _ = Old.messages
pc : Origin → M.PC
pc origin = M.initiatorTracing (outcome origin)
extraPool : Pool.State → Pool.State
extraPool pool = record pool { handles = Pool.handles pool ++ ((Old.j₁₁ , Pool.resultAvailable Pool.normalExit) ∷ []) }
raw : Origin → Mux.Mux → List Shared.IGEvent → Pool.State → R.State
raw origin m q pool = R.unwinding
  (W.handlerExitState (G.shutdownState (M.monitorState
    (Old.snapshot (Old.sourceMux m q) pool
      ((Old.j₁₀ , Old.rJob T.executing) ∷
       (Old.j₁₁ , T.protocolJob owner Old.mid Mux.initiatorJob 1 Old.r₁ (T.resultCaptured (outcome origin))) ∷ []) [])
      ((owner , pc origin) ∷ [])) []) []) []
withTicket : Origin → D.Phase → R.State → D.State
withTicket origin stage r = D.deltaQState r ((owner , D.ticket (payload origin) stage) ∷ [])
ready : Origin → D.State
ready origin = withTicket origin D.muxInvoked (raw origin (mux origin) (queue origin) (extraPool K.k0))
selected : Origin → R.Exception → R.PC → Mux.Mux → List Shared.IGEvent → Pool.State → D.State
selected origin result stage m q pool = withTicket origin D.throwing (record (raw origin m q (extraPool pool))
  { faults = (owner , R.fault Old.Prior.captured Old.mid (S.monitoring Old.j₀ Old.j₁)
      Mux.returned R.poolBody result stage) ∷ [] })

initiatorCleanUntil : D.Executes Base.initiatorClean0 (take 9 Base.initiatorCleanActions) Base.initiatorCleanTraceInvoked
initiatorCleanUntil = D.next Base.initiatorClean-edge1 (D.next Base.initiatorClean-edge2 (D.next Base.initiatorClean-edge3 (D.next Base.initiatorClean-edge4 (D.next Base.initiatorClean-edge5 (D.next Base.initiatorClean-edge6 (D.next Base.initiatorClean-edge7 (D.next Base.initiatorClean-edge8 (D.next Base.initiatorClean-mux-invoke (D.done)))))))))
initiatorErrorUntil : D.Executes Base.initiatorError0 (take 8 Base.initiatorErrorActions) Base.initiatorError7a
initiatorErrorUntil = D.next Base.initiatorError-edge1 (D.next Base.initiatorError-edge2 (D.next Base.initiatorError-edge3 (D.next Base.initiatorError-edge4 (D.next Base.initiatorError-edge5 (D.next Base.initiatorError-edge6 (D.next Base.initiatorError-edge7 (D.next Base.initiatorError-mux-invoke (D.done))))))))
invoked : Origin → D.State
invoked cleanCompletion = Base.initiatorCleanTraceInvoked
invoked errorCompletion = Base.initiatorError7a
reaping : Origin → D.State
reaping origin = withTicket origin D.muxInvoked
  (raw origin (mux origin) (queue origin)
    (record (extraPool K.k0) { handles = Pool.handles K.k0 ++ ((Old.j₁₁ , Pool.deregistered Pool.normalExit) ∷ []) }))
reap1 : ∀ origin → D.step (Base.runM (M.run (P.deregisterProtocol Old.j₁₁))) (invoked origin) ≡ just (reaping origin)
reap1 cleanCompletion = refl
reap1 errorCompletion = refl
reap2 : ∀ origin → D.step (Base.runM (M.run (P.asyncProtocolResult Old.j₁₁))) (reaping origin) ≡ just (ready origin)
reap2 origin = refl
reapActions : List D.Action
reapActions = Base.runM (M.run (P.deregisterProtocol Old.j₁₁)) ∷ Base.runM (M.run (P.asyncProtocolResult Old.j₁₁)) ∷ []
headActions : Origin → List D.Action
headActions cleanCompletion = take 9 Base.initiatorCleanActions
headActions errorCompletion = take 8 Base.initiatorErrorActions
readyActions : Origin → List D.Action
readyActions origin = Base.errorPrefixActions ++ (headActions origin ++ reapActions)
abstract
  initialized-invoked : ∀ origin → D.Executes Base.start (Base.errorPrefixActions ++ headActions origin) (invoked origin)
  initialized-invoked cleanCompletion = Prefix.append Base.initialized-error-prefix initiatorCleanUntil
  initialized-invoked errorCompletion = Prefix.append Base.initialized-error-prefix initiatorErrorUntil
  initialized-ready : ∀ origin → D.Executes Base.start (readyActions origin) (ready origin)
  initialized-ready cleanCompletion = Prefix.append Base.initialized-error-prefix
    (Prefix.append initiatorCleanUntil (D.next (reap1 cleanCompletion) (D.next (reap2 cleanCompletion) D.done)))
  initialized-ready errorCompletion = Prefix.append Base.initialized-error-prefix
    (Prefix.append initiatorErrorUntil (D.next (reap1 errorCompletion) (D.next (reap2 errorCompletion) D.done)))
observe-exception : ∀ origin result → D.step (D.observeInitiatorException owner result) (ready origin) ≡ just
  (selected origin result R.awaitingClose (mux origin) (queue origin) K.k0)
observe-exception cleanCompletion result = refl
observe-exception errorCompletion result = refl

-- One actual close proof is parametric in both the old completion and the
-- newly observed exception. Only the explicit observation's class differs.
module Close (origin : Origin) (result : R.Exception) where
  f0 : D.State
  f0 = ready origin
  f1 : D.State
  f1 = selected origin result R.awaitingClose (mux origin) (queue origin) K.k0
  edge1 : D.step (D.observeInitiatorException owner result) f0 ≡ just f1
  edge1 = observe-exception origin result
  c0 : D.State
  c0 = selected origin result R.closing (mux origin) (queue origin) K.r0
  child0 : D.step (D.run (R.beginClose owner K.order)) f1 ≡ just c0
  child0 = refl
  c1 : D.State
  c1 = selected origin result R.closing (mux origin) (queue origin) K.r1
  child1 : D.step (D.run (R.requestCancel owner)) c0 ≡ just c1
  child1 = refl
  c2 : D.State
  c2 = selected origin result R.closing (mux origin) (queue origin) K.r2
  child2 : D.step (D.run (R.deliverCancel owner)) c1 ≡ just c2
  child2 = refl
  c3 : D.State
  c3 = selected origin result R.closing (mux origin) (queue origin) K.r3
  child3 : D.step (D.run (R.run (X.run (W.run (G.finishChildUnwind Old.j₁₀))))) c2 ≡ just c3
  child3 = refl
  c4 : D.State
  c4 = selected origin result R.closing (mux origin) (queue origin) K.r4
  child4 : D.step (Base.runM (M.run (P.deregisterProtocol Old.j₁₀))) c3 ≡ just c4
  child4 = refl
  c5 : D.State
  c5 = selected origin result R.closing (mux origin) (queue origin) K.r5
  child5 : D.step (Base.runM (M.run (P.asyncProtocolResult Old.j₁₀))) c4 ≡ just c5
  child5 = refl
  f2 : D.State
  f2 = selected origin result R.closing (mux origin) (queue origin) K.k1
  child6 : D.step (D.run (R.join owner)) c5 ≡ just f2
  child6 = refl
  f3 : D.State
  f3 = selected origin result R.closing (mux origin) (queue origin) K.k2
  edge3 : D.step (D.run (R.requestCancel owner)) f2 ≡ just f3
  edge3 = refl
  f4 : D.State
  f4 = selected origin result R.closing (mux origin) (queue origin) K.k3
  edge4 : D.step (D.run (R.deliverCancel owner)) f3 ≡ just f4
  edge4 = refl
  f5 : D.State
  f5 = selected origin result R.closing (mux origin) (queue origin) K.k4
  edge5 : D.step (D.run (R.run (X.run (W.run (G.finishChildUnwind Old.j₁))))) f4 ≡ just f5
  edge5 = refl
  f6 : D.State
  f6 = selected origin result R.closing (mux origin) (queue origin) K.k5
  edge6 : D.step (Base.runM (M.run (P.deregisterInfra owner T.demuxer))) f5 ≡ just f6
  edge6 = refl
  f7 : D.State
  f7 = selected origin result R.closing (mux origin) (queue origin) K.k6
  edge7 : D.step (Base.runM (M.run (P.asyncInfraResult owner T.demuxer))) f6 ≡ just f7
  edge7 = refl
  f8 : D.State
  f8 = selected origin result R.closing (mux origin) (queue origin) K.k7
  edge8 : D.step (D.run (R.join owner)) f7 ≡ just f8
  edge8 = refl
  f9 : D.State
  f9 = selected origin result R.closing (mux origin) (queue origin) K.k8
  edge9 : D.step (D.run (R.requestCancel owner)) f8 ≡ just f9
  edge9 = refl
  f10 : D.State
  f10 = selected origin result R.closing (mux origin) (queue origin) K.k9
  edge10 : D.step (D.run (R.deliverCancel owner)) f9 ≡ just f10
  edge10 = refl
  f11 : D.State
  f11 = selected origin result R.closing (mux origin) (queue origin) K.k10
  edge11 : D.step (D.run (R.run (X.run (W.run (G.finishChildUnwind Old.j₀))))) f10 ≡ just f11
  edge11 = refl
  f12 : D.State
  f12 = selected origin result R.closing (mux origin) (queue origin) K.k11
  edge12 : D.step (Base.runM (M.run (P.deregisterInfra owner T.muxer))) f11 ≡ just f12
  edge12 = refl
  f13 : D.State
  f13 = selected origin result R.closing (mux origin) (queue origin) K.k12
  edge13 : D.step (Base.runM (M.run (P.asyncInfraResult owner T.muxer))) f12 ≡ just f13
  edge13 = refl
  f14 : D.State
  f14 = selected origin result R.closing (mux origin) (queue origin) K.k13
  edge14 : D.step (D.run (R.join owner)) f13 ≡ just f14
  edge14 = refl
  f15 : D.State
  f15 = selected origin result R.poolClosed (mux origin) (queue origin) K.k14
  edge15 : D.step (D.run (R.finishClose owner)) f14 ≡ just f15
  edge15 = refl
  actions : List D.Action
  actions = (D.observeInitiatorException owner result) ∷ (D.run (R.beginClose owner K.order)) ∷ (D.run (R.requestCancel owner)) ∷ (D.run (R.deliverCancel owner)) ∷ (D.run (R.run (X.run (W.run (G.finishChildUnwind Old.j₁₀))))) ∷ (Base.runM (M.run (P.deregisterProtocol Old.j₁₀))) ∷ (Base.runM (M.run (P.asyncProtocolResult Old.j₁₀))) ∷ (D.run (R.join owner)) ∷ (D.run (R.requestCancel owner)) ∷ (D.run (R.deliverCancel owner)) ∷ (D.run (R.run (X.run (W.run (G.finishChildUnwind Old.j₁))))) ∷ (Base.runM (M.run (P.deregisterInfra owner T.demuxer))) ∷ (Base.runM (M.run (P.asyncInfraResult owner T.demuxer))) ∷ (D.run (R.join owner)) ∷ (D.run (R.requestCancel owner)) ∷ (D.run (R.deliverCancel owner)) ∷ (D.run (R.run (X.run (W.run (G.finishChildUnwind Old.j₀))))) ∷ (Base.runM (M.run (P.deregisterInfra owner T.muxer))) ∷ (Base.runM (M.run (P.asyncInfraResult owner T.muxer))) ∷ (D.run (R.join owner)) ∷ (D.run (R.finishClose owner)) ∷ []
  path : D.Executes f0 actions f15
  path = D.next edge1 (D.next child0 (D.next child1 (D.next child2 (D.next child3 (D.next child4 (D.next child5 (D.next child6 (D.next edge3 (D.next edge4 (D.next edge5 (D.next edge6 (D.next edge7 (D.next edge8 (D.next edge9 (D.next edge10 (D.next edge11 (D.next edge12 (D.next edge13 (D.next edge14 (D.next edge15 (D.done)))))))))))))))))))))
  abstract
    initialized : D.Executes Base.start (readyActions origin ++ actions) f15
    initialized = Prefix.append (initialized-ready origin) path
  snapshot-includes-live-responder : Pool.snapshot (D.poolAt owner f15) ≡ K.order
  snapshot-includes-live-responder = refl
  all-snapshot-results : ∀ j → j ∈ Pool.snapshot (D.poolAt owner f15) →
    Facts.Base.PoolFacts.Terminal (D.poolAt owner f15) j
  all-snapshot-results = Facts.whole-closed-from-initial Base.actual-initializer initialized owner refl
  no-DeltaQ-after-first-leg-throw : D.step (D.beginDeltaQ owner) f1 ≡ nothing
  no-DeltaQ-after-first-leg-throw = refl
  no-join-before-responder-result : D.step (D.run (R.join owner)) c4 ≡ nothing
  no-join-before-responder-result = refl
  no-return-after-throw : D.step (D.observeInitiatorReturn owner) f1 ≡ nothing
  no-return-after-throw = refl
  no-early-buffer-handoff : D.step (D.run (R.handoff owner)) f1 ≡ nothing
  no-early-buffer-handoff = refl
  no-early-Failed : D.step (D.run (R.writeAsyncFailure owner)) f1 ≡ nothing
  no-early-Failed = refl

module Sync (origin : Origin) where
  module C = Close origin (R.sync err)
  s15 : D.State
  s15 = C.f15
  endBase : R.PC → D.State
  endBase stage = selected origin (R.sync err) stage (mux origin) (queue origin) K.k14
  exit : W.Phase → D.State
  exit stage = record (endBase R.handedOff) { base = F.withExit stage (D.base (endBase R.handedOff)) }
  cleanup : W.Phase → Shared.State → D.State
  cleanup stage world = record (exit stage) { base = F.withWorld world (D.base (exit stage)) }
  s16 : D.State
  s16 = endBase R.readyBuffer
  edge16 : D.step (D.run (R.continueSync owner)) s15 ≡ just s16
  edge16 = refl
  s17 : D.State
  s17 = exit (W.bufferScope (G.failedExit err))
  edge17 : D.step (D.run (R.handoff owner)) s16 ≡ just s17
  edge17 = refl
  s18 : D.State
  s18 = exit (W.classifying err)
  edge18 : D.step (D.run (R.run (X.run (W.observeBufferReturn owner)))) s17 ≡ just s18
  edge18 = refl
  s19 : D.State
  s19 = exit (W.errorTracing err Life.shutdownPeer)
  edge19 : D.step (D.run (R.run (X.run (W.choosePolicy owner Life.shutdownPeer)))) s18 ≡ just s19
  edge19 = refl
  s20 : D.State
  s20 = exit (W.peerRethrow err)
  edge20 : D.step (D.run (R.run (X.run (W.observeErrorTrace owner)))) s19 ≡ just s20
  edge20 = refl
  s21 : D.State
  s21 = exit (W.bodyExited (W.peerException err))
  edge21 : D.step (D.run (R.run (X.run (W.rethrow owner)))) s20 ≡ just s21
  edge21 = refl
  s22 : D.State
  s22 = cleanup (W.finalizing (W.peerException err)) (Clean.world1 (F.shared (D.base s17)))
  edge22 : D.step (D.run (R.run (X.run (W.enterFinalizer owner)))) s21 ≡ just s22
  edge22 = refl
  s23 : D.State
  s23 = cleanup (W.finalizing (W.peerException err)) (Clean.world2 (F.shared (D.base s17)))
  edge23 : D.step (D.run (R.run (X.run (W.cleanup owner Cleanup.takeCleanupMap)))) s22 ≡ just s23
  edge23 = refl
  s24 : D.State
  s24 = cleanup (W.finalizing (W.peerException err)) (Clean.world3 (F.shared (D.base s17)))
  edge24 : D.step (D.run (R.run (X.run (W.cleanup owner Cleanup.selectCleanupEntry)))) s23 ≡ just s24
  edge24 = refl
  s25 : D.State
  s25 = cleanup (W.finalizing (W.peerException err)) (Clean.world4 (F.shared (D.base s17)))
  edge25 : D.step (D.run (R.run (X.run (W.cleanup owner Cleanup.closeHandlerSocket)))) s24 ≡ just s25
  edge25 = refl
  s26 : D.State
  s26 = cleanup (W.finalizing (W.peerException err)) (Clean.world5 (F.shared (D.base s17)))
  edge26 : D.step (D.run (R.run (X.run (W.cleanup owner Cleanup.publishCleanupMap)))) s25 ≡ just s26
  edge26 = refl
  s27 : D.State
  s27 = cleanup (W.finalizing (W.peerException err)) (Clean.world6 (F.shared (D.base s17)))
  edge27 : D.step (D.run (R.run (X.run (W.cleanup owner Cleanup.readCleanupCounters)))) s26 ≡ just s27
  edge27 = refl
  s28 : D.State
  s28 = cleanup (W.cleanupComplete (W.peerException err) Shared.cleanupNormal) (Clean.world6 (F.shared (D.base s17)))
  edge28 : D.step (D.run (R.run (X.run (W.finishCleanup owner)))) s27 ≡ just s28
  edge28 = refl
  s29 : D.State
  s29 = cleanup (W.resultAvailable (W.peerException err) Shared.cleanupNormal) (Clean.world6 (F.shared (D.base s17)))
  edge29 : D.step (D.run (R.run (X.run (W.publishAsyncResult owner)))) s28 ≡ just s29
  edge29 = refl
  actions : List D.Action
  actions = (D.run (R.continueSync owner)) ∷ (D.run (R.handoff owner)) ∷ (D.run (R.run (X.run (W.observeBufferReturn owner)))) ∷ (D.run (R.run (X.run (W.choosePolicy owner Life.shutdownPeer)))) ∷ (D.run (R.run (X.run (W.observeErrorTrace owner)))) ∷ (D.run (R.run (X.run (W.rethrow owner)))) ∷ (D.run (R.run (X.run (W.enterFinalizer owner)))) ∷ (D.run (R.run (X.run (W.cleanup owner Cleanup.takeCleanupMap)))) ∷ (D.run (R.run (X.run (W.cleanup owner Cleanup.selectCleanupEntry)))) ∷ (D.run (R.run (X.run (W.cleanup owner Cleanup.closeHandlerSocket)))) ∷ (D.run (R.run (X.run (W.cleanup owner Cleanup.publishCleanupMap)))) ∷ (D.run (R.run (X.run (W.cleanup owner Cleanup.readCleanupCounters)))) ∷ (D.run (R.run (X.run (W.finishCleanup owner)))) ∷ (D.run (R.run (X.run (W.publishAsyncResult owner)))) ∷ []
  path : D.Executes s15 actions s29
  path = D.next edge16 (D.next edge17 (D.next edge18 (D.next edge19 (D.next edge20 (D.next edge21 (D.next edge22 (D.next edge23 (D.next edge24 (D.next edge25 (D.next edge26 (D.next edge27 (D.next edge28 (D.next edge29 (D.done))))))))))))))
  abstract
    initialized : D.Executes Base.start ((readyActions origin ++ C.actions) ++ actions) s29
    initialized = Prefix.append C.initialized path
  status-not-rewritten : P.muxAt Old.mid (R.protocols (D.base s29)) ≡ just (mux origin)
  status-not-rewritten = refl
  no-new-IG-publication : Shared.inboundInfo (Machine.world (O.core (D.source s29))) ≡ queue origin
  no-new-IG-publication = refl
  captures : Capture.Captures (D.source s29)
  captures = Facts.from-initial-captures Base.actual-initializer initialized
  supply : Supply.Valid (D.source s29)
  supply = Facts.from-initial-supply Base.actual-initializer Old.Prior.initial-bounds initialized
  replacement-result : lookup owner (W.exits (R.base (D.base s29))) ≡ just
    (W.exitFrame Old.Prior.captured (W.resultAvailable (W.peerException err) Shared.cleanupNormal) nothing)
  replacement-result = refl
  physical-parent-ready : W.resultReady owner (R.base (D.base s29)) ≡ true
  physical-parent-ready = refl

-- Neither initiator trace has published an IG notification. Async catch adds
-- Dead only after actual pool close, retaining the existing awake/promote queue.
asyncAt : Origin → R.PC → Mux.Callback → Maybe Mux.Counters → List Shared.IGEvent → D.State
asyncAt origin stage callback rc q = selected origin (R.async err) stage
  (record (mux origin) { status = Mux.failed err; callback = callback; traceCounters = rc }) q K.k14
async-commit : ∀ origin → D.step (D.run (R.commitDead owner))
  (asyncAt origin R.asyncDead (Mux.commitTrace true Mux.muxStopped) (counters origin) (queue origin)) ≡ just
  (asyncAt origin R.asyncDead Mux.returned nothing (queue origin ++ (Shared.muxFinished key₀ ∷ [])))
async-commit cleanCompletion = refl
async-commit errorCompletion = refl

module Async (origin : Origin) where
  module C = Close origin (R.async err)
  a15 : D.State
  a15 = C.f15
  afterDead : R.PC → D.State
  afterDead stage = asyncAt origin stage Mux.returned nothing (queue origin ++ (Shared.muxFinished key₀ ∷ []))
  exit : W.Phase → D.State
  exit stage = record (afterDead R.handedOff) { base = F.withExit stage (D.base (afterDead R.handedOff)) }
  cleanup : W.Phase → Shared.State → D.State
  cleanup stage world = record (exit stage) { base = F.withWorld world (D.base (exit stage)) }
  a16 : D.State
  a16 = asyncAt origin R.asyncStatus Mux.returned (counters origin) (queue origin)
  edge16 : D.step (D.run (R.writeAsyncFailure owner)) a15 ≡ just a16
  edge16 = refl
  a17 : D.State
  a17 = asyncAt origin R.asyncDead (Mux.readActive Mux.muxStopped) (counters origin) (queue origin)
  edge17 : D.step (D.run (R.beginDead owner)) a16 ≡ just a17
  edge17 = refl
  a18 : D.State
  a18 = asyncAt origin R.asyncDead (Mux.commitTrace true Mux.muxStopped) (counters origin) (queue origin)
  edge18 : D.step (D.run (R.sampleDead owner)) a17 ≡ just a18
  edge18 = refl
  a19 : D.State
  a19 = afterDead R.asyncDead
  edge19 : D.step (D.run (R.commitDead owner)) a18 ≡ just a19
  edge19 = async-commit origin
  a20 : D.State
  a20 = afterDead R.readyBuffer
  edge20 : D.step (D.run (R.finishDead owner)) a19 ≡ just a20
  edge20 = refl
  a21 : D.State
  a21 = exit (W.bufferScope (G.asyncExit err))
  edge21 : D.step (D.run (R.handoff owner)) a20 ≡ just a21
  edge21 = refl
  a22 : D.State
  a22 = exit (W.bodyExited (W.asyncException err))
  edge22 : D.step (D.run (R.run (X.run (W.observeBufferReturn owner)))) a21 ≡ just a22
  edge22 = refl
  a23 : D.State
  a23 = cleanup (W.finalizing (W.asyncException err)) (Clean.world1 (F.shared (D.base a21)))
  edge23 : D.step (D.run (R.run (X.run (W.enterFinalizer owner)))) a22 ≡ just a23
  edge23 = refl
  a24 : D.State
  a24 = cleanup (W.finalizing (W.asyncException err)) (Clean.world2 (F.shared (D.base a21)))
  edge24 : D.step (D.run (R.run (X.run (W.cleanup owner Cleanup.takeCleanupMap)))) a23 ≡ just a24
  edge24 = refl
  a25 : D.State
  a25 = cleanup (W.finalizing (W.asyncException err)) (Clean.world3 (F.shared (D.base a21)))
  edge25 : D.step (D.run (R.run (X.run (W.cleanup owner Cleanup.selectCleanupEntry)))) a24 ≡ just a25
  edge25 = refl
  a26 : D.State
  a26 = cleanup (W.finalizing (W.asyncException err)) (Clean.world4 (F.shared (D.base a21)))
  edge26 : D.step (D.run (R.run (X.run (W.cleanup owner Cleanup.closeHandlerSocket)))) a25 ≡ just a26
  edge26 = refl
  a27 : D.State
  a27 = cleanup (W.finalizing (W.asyncException err)) (Clean.world5 (F.shared (D.base a21)))
  edge27 : D.step (D.run (R.run (X.run (W.cleanup owner Cleanup.publishCleanupMap)))) a26 ≡ just a27
  edge27 = refl
  a28 : D.State
  a28 = cleanup (W.finalizing (W.asyncException err)) (Clean.world6 (F.shared (D.base a21)))
  edge28 : D.step (D.run (R.run (X.run (W.cleanup owner Cleanup.readCleanupCounters)))) a27 ≡ just a28
  edge28 = refl
  a29 : D.State
  a29 = cleanup (W.cleanupComplete (W.asyncException err) Shared.cleanupNormal) (Clean.world6 (F.shared (D.base a21)))
  edge29 : D.step (D.run (R.run (X.run (W.finishCleanup owner)))) a28 ≡ just a29
  edge29 = refl
  a30 : D.State
  a30 = cleanup (W.resultAvailable (W.asyncException err) Shared.cleanupNormal) (Clean.world6 (F.shared (D.base a21)))
  edge30 : D.step (D.run (R.run (X.run (W.publishAsyncResult owner)))) a29 ≡ just a30
  edge30 = refl
  actions : List D.Action
  actions = (D.run (R.writeAsyncFailure owner)) ∷ (D.run (R.beginDead owner)) ∷ (D.run (R.sampleDead owner)) ∷ (D.run (R.commitDead owner)) ∷ (D.run (R.finishDead owner)) ∷ (D.run (R.handoff owner)) ∷ (D.run (R.run (X.run (W.observeBufferReturn owner)))) ∷ (D.run (R.run (X.run (W.enterFinalizer owner)))) ∷ (D.run (R.run (X.run (W.cleanup owner Cleanup.takeCleanupMap)))) ∷ (D.run (R.run (X.run (W.cleanup owner Cleanup.selectCleanupEntry)))) ∷ (D.run (R.run (X.run (W.cleanup owner Cleanup.closeHandlerSocket)))) ∷ (D.run (R.run (X.run (W.cleanup owner Cleanup.publishCleanupMap)))) ∷ (D.run (R.run (X.run (W.cleanup owner Cleanup.readCleanupCounters)))) ∷ (D.run (R.run (X.run (W.finishCleanup owner)))) ∷ (D.run (R.run (X.run (W.publishAsyncResult owner)))) ∷ []
  path : D.Executes a15 actions a30
  path = D.next edge16 (D.next edge17 (D.next edge18 (D.next edge19 (D.next edge20 (D.next edge21 (D.next edge22 (D.next edge23 (D.next edge24 (D.next edge25 (D.next edge26 (D.next edge27 (D.next edge28 (D.next edge29 (D.next edge30 (D.done)))))))))))))))
  abstract
    initialized : D.Executes Base.start ((readyActions origin ++ C.actions) ++ actions) a30
    initialized = Prefix.append C.initialized path
  preserves-and-appends : Shared.inboundInfo (Machine.world (O.core (D.source a30))) ≡
    queue origin ++ (Shared.muxFinished key₀ ∷ [])
  preserves-and-appends = refl
  physical-parent-ready : W.resultReady owner (R.base (D.base a30)) ≡ true
  physical-parent-ready = refl
  preserves-captured-result : lookup owner (D.tickets a30) ≡ just (D.ticket (payload origin) D.throwing)
  preserves-captured-result = refl
  captures : Capture.Captures (D.source a30)
  captures = Facts.from-initial-captures Base.actual-initializer initialized
  supply : Supply.Valid (D.source a30)
  supply = Facts.from-initial-supply Base.actual-initializer Old.Prior.initial-bounds initialized

module CleanSync = Sync cleanCompletion
module ErrorSync = Sync errorCompletion
module CleanAsync = Async cleanCompletion
module ErrorAsync = Async errorCompletion
-- These are possible source-profile executions, not a deployed-tracer bug claim.
clean-sync-retains-live-responder-metadata-after-result : P.muxAt Old.mid (R.protocols (D.base CleanSync.s29)) ≡ just (mux cleanCompletion)
clean-sync-retains-live-responder-metadata-after-result = CleanSync.status-not-rewritten
sync-replaces-protocol-error : lookup owner (W.exits (R.base (D.base ErrorSync.s29))) ≡ just
  (W.exitFrame Old.Prior.captured (W.resultAvailable (W.peerException err) Shared.cleanupNormal) nothing)
sync-replaces-protocol-error = ErrorSync.replacement-result

-- Initialized counterexample to a proposed unconditional shutdown invariant:
-- physical completion alone need not change Ready or responder trace metadata.
-- Callback/provider/policy observations remain premises; no deployed deadlock
-- follows from this finite execution, especially with old IG events still queued.
clean-sync-status : Mux.status (mux cleanCompletion) ≡ Mux.ready
clean-sync-status = refl
clean-sync-responder-count : Mux.traceCounters (mux cleanCompletion) ≡ just (Mux.counters (+ 1) (+ 0))
clean-sync-responder-count = refl
clean-sync-responder-running-metadata : Mux.runningJobs (mux cleanCompletion) ≡ 1 ∷ []
clean-sync-responder-running-metadata = refl
clean-sync-responder-physically-cancelled : lookup Old.j₁₀ (Pool.handles (D.poolAt owner CleanSync.s29)) ≡ just (Pool.resultAvailable Pool.cancelledExit)
clean-sync-responder-physically-cancelled = refl
clean-sync-pool-closed : Pool.phase (D.poolAt owner CleanSync.s29) ≡ Pool.closedPool
clean-sync-pool-closed = refl
clean-sync-parent-ready : W.resultReady owner (R.base (D.base CleanSync.s29)) ≡ true
clean-sync-parent-ready = refl
