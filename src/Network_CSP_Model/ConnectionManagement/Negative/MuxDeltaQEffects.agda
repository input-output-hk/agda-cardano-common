{-# OPTIONS --guardedness #-}

-- Initialized synchronous/asynchronous DeltaQ exceptions after clean completion
-- and after the error branch's committed Dead trace. All close steps are real;
-- named tracer/provider outcomes remain inputs, not universal progress claims.
module ConnectionManagement.Negative.MuxDeltaQEffects where

open import Data.Bool using (true; false)
open import Data.Nat using (ℕ)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; _++_; map; take)
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
module K = PoolFixtures Old.j₀ Old.j₁
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
payload origin = T.protocolCompletion Mux.responderJob 1 Old.r₀ (outcome origin)
status : Origin → Mux.Status
status cleanCompletion = Mux.ready
status errorCompletion = Mux.failed Old.err
counters : Origin → Maybe Mux.Counters
counters cleanCompletion = just (Mux.counters (+ 0) (+ 0))
counters errorCompletion = nothing
protocols : Origin → Store ℕ Mux.ProtocolStatus
protocols cleanCompletion = Mux.protocols Old.publishedMux
protocols errorCompletion = Mux.protocols Old.m6
mux : Origin → Mux.Mux
mux origin = record Old.m6
  { protocols = protocols origin; runningJobs = []; finishedJobs = []; completions = []
  ; callback = Mux.returned; status = status origin; traceCounters = counters origin }
queue : Origin → List Shared.IGEvent
queue cleanCompletion = Shared.inboundInfo (Machine.world (O.core (M.source RF.clean4)))
queue errorCompletion = Shared.inboundInfo (Machine.world (O.core (M.source RF.errorTail11)))
pc : Origin → M.PC
pc cleanCompletion = M.responderTracing clean
pc errorCompletion = M.deadTracing (M.failed Old.err)
extraPool : Pool.State → Pool.State
extraPool pool = record pool { handles = Pool.handles pool ++ ((Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []) }
raw : Origin → Mux.Mux → List Shared.IGEvent → Pool.State → R.State
raw origin m q pool = R.unwinding
  (W.handlerExitState (G.shutdownState (M.monitorState
    (Old.snapshot (Old.sourceMux m q) pool ((Old.j₁₀ , Old.rJob (T.resultCaptured (outcome origin))) ∷ [])
      ((owner , []) ∷ [])) ((owner , pc origin) ∷ [])) []) []) []
withTicket : Origin → D.Phase → R.State → D.State
withTicket origin stage r = D.deltaQState r ((owner , D.ticket (payload origin) stage) ∷ [])
ready : Origin → D.State
ready origin = withTicket origin D.invoked (raw origin (mux origin) (queue origin) (extraPool K.k0))
selected : Origin → R.Exception → R.PC → Mux.Mux → List Shared.IGEvent → Pool.State → D.State
selected origin result stage m q pool = withTicket origin D.throwing (record (raw origin m q (extraPool pool))
  { faults = (owner , R.fault Old.Prior.captured Old.mid (S.monitoring Old.j₀ Old.j₁)
      Mux.returned R.poolBody result stage) ∷ [] })

-- Reap the independently returned protocol while DeltaQ is invoked. This is
-- actual masked deregistration/result publication, not deletion of history.
errorReaped : D.State
errorReaped = withTicket errorCompletion D.invoked
  (raw errorCompletion (mux errorCompletion) (queue errorCompletion)
    (record (extraPool K.k0) { handles = (Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷
      (Old.j₁₀ , Pool.deregistered Pool.normalExit) ∷ [] }))
reap1 : D.step (Base.runM (M.run (P.deregisterProtocol Old.j₁₀))) Base.errorTailInvoked ≡ just errorReaped
reap1 = refl
reap2 : D.step (Base.runM (M.run (P.asyncProtocolResult Old.j₁₀))) errorReaped ≡ just (ready errorCompletion)
reap2 = refl
reapActions : List D.Action
reapActions = Base.runM (M.run (P.deregisterProtocol Old.j₁₀)) ∷ Base.runM (M.run (P.asyncProtocolResult Old.j₁₀)) ∷ []
cleanUntil : D.Executes Base.clean0 (take 5 Base.cleanActions) Base.cleanInvoked
cleanUntil = D.next Base.clean-edge1 (D.next Base.clean-edge2 (D.next Base.clean-edge3
  (D.next Base.clean-edge4 (D.next Base.clean-invoke D.done))))
errorUntil : D.Executes Base.errorTail0 (take 12 Base.errorTailActions) Base.errorTailInvoked
errorUntil = D.next Base.errorTail-edge1 (D.next Base.errorTail-edge2 (D.next Base.errorTail-edge3
  (D.next Base.errorTail-edge4 (D.next Base.errorTail-edge5 (D.next Base.errorTail-edge6
  (D.next Base.errorTail-edge7 (D.next Base.errorTail-edge8 (D.next Base.errorTail-edge9
  (D.next Base.errorTail-edge10 (D.next Base.errorTail-edge11 (D.next Base.errorTail-invoke D.done)))))))))))
readyActions : Origin → List D.Action
readyActions cleanCompletion = map D.run Base.cleanPrefixActions ++ take 5 Base.cleanActions
readyActions errorCompletion = Base.errorPrefixActions ++ (take 12 Base.errorTailActions ++ reapActions)
abstract
  initialized-ready : ∀ origin → D.Executes Base.start (readyActions origin) (ready origin)
  initialized-ready cleanCompletion = Prefix.append Base.initialized-clean-head cleanUntil
  initialized-ready errorCompletion = Prefix.append Base.initialized-error-prefix
    (Prefix.append errorUntil (D.next reap1 (D.next reap2 D.done)))

observe-exception : ∀ origin result → D.step (D.observeException owner result) (ready origin) ≡ just
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
  edge1 : D.step (D.observeException owner result) f0 ≡ just f1
  edge1 = observe-exception origin result
  f2 : D.State
  f2 = selected origin result R.closing (mux origin) (queue origin) K.k1
  edge2 : D.step (D.run (R.beginClose owner (Old.j₁ ∷ Old.j₀ ∷ []))) f1 ≡ just f2
  edge2 = refl
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
  actions = (D.observeException owner result) ∷ (D.run (R.beginClose owner (Old.j₁ ∷ Old.j₀ ∷ []))) ∷ (D.run (R.requestCancel owner)) ∷ (D.run (R.deliverCancel owner)) ∷ (D.run (R.run (X.run (W.run (G.finishChildUnwind Old.j₁))))) ∷ (Base.runM (M.run (P.deregisterInfra owner T.demuxer))) ∷ (Base.runM (M.run (P.asyncInfraResult owner T.demuxer))) ∷ (D.run (R.join owner)) ∷ (D.run (R.requestCancel owner)) ∷ (D.run (R.deliverCancel owner)) ∷ (D.run (R.run (X.run (W.run (G.finishChildUnwind Old.j₀))))) ∷ (Base.runM (M.run (P.deregisterInfra owner T.muxer))) ∷ (Base.runM (M.run (P.asyncInfraResult owner T.muxer))) ∷ (D.run (R.join owner)) ∷ (D.run (R.finishClose owner)) ∷ []
  path : D.Executes f0 actions f15
  path = D.next edge1 (D.next edge2 (D.next edge3 (D.next edge4 (D.next edge5 (D.next edge6 (D.next edge7 (D.next edge8 (D.next edge9 (D.next edge10 (D.next edge11 (D.next edge12 (D.next edge13 (D.next edge14 (D.next edge15 (D.done)))))))))))))))
  abstract
    initialized : D.Executes Base.start (readyActions origin ++ actions) f15
    initialized = Prefix.append (initialized-ready origin) path
  no-return-after-throw : D.step (D.observeReturn owner) f1 ≡ nothing
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

-- Both source branches have room for the new catch's notification. Their
-- different already committed queues are retained, including a previous Dead.
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
clean-sync-can-retain-Ready-after-handler-result : P.muxAt Old.mid (R.protocols (D.base CleanSync.s29)) ≡ just (mux cleanCompletion)
clean-sync-can-retain-Ready-after-handler-result = CleanSync.status-not-rewritten
sync-replaces-protocol-error : lookup owner (W.exits (R.base (D.base ErrorSync.s29))) ≡ just
  (W.exitFrame Old.Prior.captured (W.resultAvailable (W.peerException err) Shared.cleanupNormal) nothing)
sync-replaces-protocol-error = ErrorSync.replacement-result
