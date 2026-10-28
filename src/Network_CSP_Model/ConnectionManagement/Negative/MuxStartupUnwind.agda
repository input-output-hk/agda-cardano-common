{-# OPTIONS --guardedness #-}

-- Initialized partial-startup failure, actual current registry close and the
-- captured CM finally. Trace/provider faults are explicit source observations.
module ConnectionManagement.Negative.MuxStartupUnwind where

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
owner : WorkerId
owner = Old.owner
err : ErrorId
err = errorId 88
wrappedActions : List P.Action → List R.Action
wrappedActions actions = map R.run (map X.run (map W.run (map G.run (map M.run actions))))
liftP : ∀ {p actions q} → P.Executes p actions q → GF.prefixAll (map M.run actions) ≡ true →
  ExitProof.allSafe (map G.run (map M.run actions)) ≡ true →
  R.Executes (F.wrapP p) (wrappedActions actions) (F.wrapP q)
liftP path safe oldSafe = Facts.lift (Cancel.lift (ExitProof.lift-path (GF.lift-path (RF.lift-path path) safe) oldSafe))
start : R.State
start = F.wrapP Old.b0
actual-initializer : R.initial (O.initial Old.F.start) ≡ just start
actual-initializer = refl
publicationActions : List P.Action
publicationActions = Old.birthPathActions ++ Old.publicationPathActions
publicationPath : P.Executes Old.b0 publicationActions Old.b15
publicationPath = Old.append Old.birthPath Old.publicationPath
callerActions : List P.Action
callerActions = publicationActions ++ Old.callerPathActions
callerPath : P.Executes Old.b0 callerActions Old.c11
callerPath = Old.append publicationPath Old.callerPath
beforeMatureActions : List P.Action
beforeMatureActions = P.run (U.startupStep owner S.allocateBuffer) ∷ P.run (U.startupStep owner S.createBearer) ∷
  P.run (U.startupStep owner S.enterRun) ∷ P.run (U.startupStep owner S.traceStarting) ∷
  P.run (U.startupStep owner S.allocateEgress) ∷ P.run (U.startupStep owner S.openPool) ∷
  P.run (U.startupStep owner (S.forkMuxer Old.j₀)) ∷ P.run (U.startupStep owner S.registerMuxer) ∷
  P.run (U.startupStep owner (S.forkDemuxer Old.j₁)) ∷ P.run (U.startupStep owner S.registerDemuxer) ∷ []
beforeMaturePath : P.Executes Old.c11 beforeMatureActions Old.z10
beforeMaturePath = P.next Old.startup1 (P.next Old.startup2 (P.next Old.startup3 (P.next Old.startup4
  (P.next Old.startup5 (P.next Old.startup6 (P.next Old.startup7 (P.next Old.startup8
  (P.next Old.startup9 (P.next Old.startup10 P.done)))))))))
initialMatureActions : List P.Action
initialMatureActions = callerActions ++ beforeMatureActions
abstract
  initialized-before-mature : R.Executes start (wrappedActions initialMatureActions) (F.wrapP Old.z10)
  initialized-before-mature = liftP (Old.append callerPath beforeMaturePath) refl refl

-- Every pool snapshot below is explicit. Neither source startup phase nor
-- callback is advanced to fabricate a successful monitor entry.
k0 : Pool.State
k0 = Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing (Pool.openPool) ([]) ([]) ([]) []
k1 : Pool.State
k1 = Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing (Pool.closing) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) ([]) []
k2 : Pool.State
k2 = Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyRunning) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing (Pool.cancelPending Old.j₁) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) ([]) []
k3 : Pool.State
k3 = Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.bodyUnwinding) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing (Pool.joinPending Old.j₁) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) ([]) []
k4 : Pool.State
k4 = Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregisterPending Pool.cancelledExit) ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) nothing (Pool.joinPending Old.j₁) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) ([]) []
k5 : Pool.State
k5 = Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.deregistered Pool.cancelledExit) ∷ []) (Old.j₀ ∷ []) nothing (Pool.joinPending Old.j₁) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) ([]) []
k6 : Pool.State
k6 = Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₀ ∷ []) nothing (Pool.joinPending Old.j₁) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₁ ∷ Old.j₀ ∷ []) ([]) []
k7 : Pool.State
k7 = Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₀ ∷ []) nothing (Pool.closing) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₀ ∷ []) (Old.j₁ ∷ []) []
k8 : Pool.State
k8 = Pool.poolState ((Old.j₀ , Pool.bodyRunning) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₀ ∷ []) nothing (Pool.cancelPending Old.j₀) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₀ ∷ []) (Old.j₁ ∷ []) []
k9 : Pool.State
k9 = Pool.poolState ((Old.j₀ , Pool.bodyUnwinding) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₀ ∷ []) nothing (Pool.joinPending Old.j₀) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₀ ∷ []) (Old.j₁ ∷ []) []
k10 : Pool.State
k10 = Pool.poolState ((Old.j₀ , Pool.deregisterPending Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ []) (Old.j₀ ∷ []) nothing (Pool.joinPending Old.j₀) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₀ ∷ []) (Old.j₁ ∷ []) []
k11 : Pool.State
k11 = Pool.poolState ((Old.j₀ , Pool.deregistered Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ []) ([]) nothing (Pool.joinPending Old.j₀) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₀ ∷ []) (Old.j₁ ∷ []) []
k12 : Pool.State
k12 = Pool.poolState ((Old.j₀ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ []) ([]) nothing (Pool.joinPending Old.j₀) (Old.j₁ ∷ Old.j₀ ∷ []) (Old.j₀ ∷ []) (Old.j₁ ∷ []) []
k13 : Pool.State
k13 = Pool.poolState ((Old.j₀ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ []) ([]) nothing (Pool.closing) (Old.j₁ ∷ Old.j₀ ∷ []) ([]) (Old.j₁ ∷ Old.j₀ ∷ []) []
k14 : Pool.State
k14 = Pool.poolState ((Old.j₀ , Pool.resultAvailable Pool.cancelledExit) ∷ (Old.j₁ , Pool.resultAvailable Pool.cancelledExit) ∷ []) ([]) nothing (Pool.closedPool) (Old.j₁ ∷ Old.j₀ ∷ []) ([]) (Old.j₁ ∷ Old.j₀ ∷ []) []
partialPC : S.PC
partialPC = S.demuxerRegistered Old.j₀ Old.j₁
atPool : Pool.State → P.State
atPool pool = Old.at (P.source Old.z10) (S.startupState partialPC pool) [] []
failed : Pool.State → R.PC → R.State
failed pool pc = F.selected (atPool pool) partialPC Mux.returned R.poolBody (R.sync err) pc
m0 m1 : R.State
m0 = F.wrapP Old.z10
m1 = failed k0 R.awaitingClose
m-edge1 : R.step (R.observeFailure owner R.matureTrace err) m0 ≡ just m1
m-edge1 = refl
m2 : R.State
m2 = failed k1 R.closing
m-edge2 : R.step (R.beginClose owner (Old.j₁ ∷ Old.j₀ ∷ [])) m1 ≡ just m2
m-edge2 = refl
m3 : R.State
m3 = failed k2 R.closing
m-edge3 : R.step (R.requestCancel owner) m2 ≡ just m3
m-edge3 = refl
m4 : R.State
m4 = failed k3 R.closing
m-edge4 : R.step (R.deliverCancel owner) m3 ≡ just m4
m-edge4 = refl
m5 : R.State
m5 = failed k4 R.closing
m-edge5 : R.step (R.run (X.run (W.run (G.finishChildUnwind Old.j₁)))) m4 ≡ just m5
m-edge5 = refl
m6 : R.State
m6 = failed k5 R.closing
m-edge6 : R.step (R.run (X.run (W.run (G.run (M.run (P.deregisterInfra owner T.demuxer)))))) m5 ≡ just m6
m-edge6 = refl
m7 : R.State
m7 = failed k6 R.closing
m-edge7 : R.step (R.run (X.run (W.run (G.run (M.run (P.asyncInfraResult owner T.demuxer)))))) m6 ≡ just m7
m-edge7 = refl
m8 : R.State
m8 = failed k7 R.closing
m-edge8 : R.step (R.join owner) m7 ≡ just m8
m-edge8 = refl
m9 : R.State
m9 = failed k8 R.closing
m-edge9 : R.step (R.requestCancel owner) m8 ≡ just m9
m-edge9 = refl
m10 : R.State
m10 = failed k9 R.closing
m-edge10 : R.step (R.deliverCancel owner) m9 ≡ just m10
m-edge10 = refl
m11 : R.State
m11 = failed k10 R.closing
m-edge11 : R.step (R.run (X.run (W.run (G.finishChildUnwind Old.j₀)))) m10 ≡ just m11
m-edge11 = refl
m12 : R.State
m12 = failed k11 R.closing
m-edge12 : R.step (R.run (X.run (W.run (G.run (M.run (P.deregisterInfra owner T.muxer)))))) m11 ≡ just m12
m-edge12 = refl
m13 : R.State
m13 = failed k12 R.closing
m-edge13 : R.step (R.run (X.run (W.run (G.run (M.run (P.asyncInfraResult owner T.muxer)))))) m12 ≡ just m13
m-edge13 = refl
m14 : R.State
m14 = failed k13 R.closing
m-edge14 : R.step (R.join owner) m13 ≡ just m14
m-edge14 = refl
m15 : R.State
m15 = failed k14 R.poolClosed
m-edge15 : R.step (R.finishClose owner) m14 ≡ just m15
m-edge15 = refl
m16 m17 m18 m19 m20 m21 : R.State
m16 = failed k14 R.readyBuffer
m17 = F.withExit (W.bufferScope (G.failedExit err)) (failed k14 R.handedOff)
m18 = F.withExit (W.classifying err) (failed k14 R.handedOff)
m19 = F.withExit (W.errorTracing err Life.shutdownPeer) (failed k14 R.handedOff)
m20 = F.withExit (W.peerRethrow err) (failed k14 R.handedOff)
m21 = F.withExit (W.bodyExited (W.peerException err)) (failed k14 R.handedOff)
m-edge16 : R.step (R.continueSync owner) m15 ≡ just m16
m-edge16 = refl
m-edge17 : R.step (R.handoff owner) m16 ≡ just m17
m-edge17 = refl
m-edge18 : R.step (R.run (X.run (W.observeBufferReturn owner))) m17 ≡ just m18
m-edge18 = refl
m-edge19 : R.step (R.run (X.run (W.choosePolicy owner Life.shutdownPeer))) m18 ≡ just m19
m-edge19 = refl
m-edge20 : R.step (R.run (X.run (W.observeErrorTrace owner))) m19 ≡ just m20
m-edge20 = refl
m-edge21 : R.step (R.run (X.run (W.rethrow owner))) m20 ≡ just m21
m-edge21 = refl
m22 : R.State
m22 = F.withWorld (Clean.world1 (F.shared m17)) (F.withExit (W.finalizing (W.peerException err)) (failed k14 R.handedOff))
m23 : R.State
m23 = F.withWorld (Clean.world2 (F.shared m17)) (F.withExit (W.finalizing (W.peerException err)) (failed k14 R.handedOff))
m24 : R.State
m24 = F.withWorld (Clean.world3 (F.shared m17)) (F.withExit (W.finalizing (W.peerException err)) (failed k14 R.handedOff))
m25 : R.State
m25 = F.withWorld (Clean.world4 (F.shared m17)) (F.withExit (W.finalizing (W.peerException err)) (failed k14 R.handedOff))
m26 : R.State
m26 = F.withWorld (Clean.world5 (F.shared m17)) (F.withExit (W.finalizing (W.peerException err)) (failed k14 R.handedOff))
m27 : R.State
m27 = F.withWorld (Clean.world6 (F.shared m17)) (F.withExit (W.finalizing (W.peerException err)) (failed k14 R.handedOff))
m28 m29 : R.State
m28 = F.withWorld (Clean.world6 (F.shared m17)) (F.withExit (W.cleanupComplete (W.peerException err) Shared.cleanupNormal) (failed k14 R.handedOff))
m29 = F.withWorld (Clean.world6 (F.shared m17)) (F.withExit (W.resultAvailable (W.peerException err) Shared.cleanupNormal) (failed k14 R.handedOff))
m-edge22 : R.step (R.run (X.run (W.enterFinalizer owner))) m21 ≡ just m22
m-edge22 = refl
m-edge23 : R.step (R.run (X.run (W.cleanup owner C.takeCleanupMap))) m22 ≡ just m23
m-edge23 = refl
m-edge24 : R.step (R.run (X.run (W.cleanup owner C.selectCleanupEntry))) m23 ≡ just m24
m-edge24 = refl
m-edge25 : R.step (R.run (X.run (W.cleanup owner C.closeHandlerSocket))) m24 ≡ just m25
m-edge25 = refl
m-edge26 : R.step (R.run (X.run (W.cleanup owner C.publishCleanupMap))) m25 ≡ just m26
m-edge26 = refl
m-edge27 : R.step (R.run (X.run (W.cleanup owner C.readCleanupCounters))) m26 ≡ just m27
m-edge27 = refl
m-edge28 : R.step (R.run (X.run (W.finishCleanup owner))) m27 ≡ just m28
m-edge28 = refl
m-edge29 : R.step (R.run (X.run (W.publishAsyncResult owner))) m28 ≡ just m29
m-edge29 = refl
mActions : List R.Action
mActions = (R.observeFailure owner R.matureTrace err) ∷ (R.beginClose owner (Old.j₁ ∷ Old.j₀ ∷ [])) ∷ (R.requestCancel owner) ∷ (R.deliverCancel owner) ∷ (R.run (X.run (W.run (G.finishChildUnwind Old.j₁)))) ∷ (R.run (X.run (W.run (G.run (M.run (P.deregisterInfra owner T.demuxer)))))) ∷ (R.run (X.run (W.run (G.run (M.run (P.asyncInfraResult owner T.demuxer)))))) ∷ (R.join owner) ∷ (R.requestCancel owner) ∷ (R.deliverCancel owner) ∷ (R.run (X.run (W.run (G.finishChildUnwind Old.j₀)))) ∷ (R.run (X.run (W.run (G.run (M.run (P.deregisterInfra owner T.muxer)))))) ∷ (R.run (X.run (W.run (G.run (M.run (P.asyncInfraResult owner T.muxer)))))) ∷ (R.join owner) ∷ (R.finishClose owner) ∷ (R.continueSync owner) ∷ (R.handoff owner) ∷ (R.run (X.run (W.observeBufferReturn owner))) ∷ (R.run (X.run (W.choosePolicy owner Life.shutdownPeer))) ∷ (R.run (X.run (W.observeErrorTrace owner))) ∷ (R.run (X.run (W.rethrow owner))) ∷ (R.run (X.run (W.enterFinalizer owner))) ∷ (R.run (X.run (W.cleanup owner C.takeCleanupMap))) ∷ (R.run (X.run (W.cleanup owner C.selectCleanupEntry))) ∷ (R.run (X.run (W.cleanup owner C.closeHandlerSocket))) ∷ (R.run (X.run (W.cleanup owner C.publishCleanupMap))) ∷ (R.run (X.run (W.cleanup owner C.readCleanupCounters))) ∷ (R.run (X.run (W.finishCleanup owner))) ∷ (R.run (X.run (W.publishAsyncResult owner))) ∷ []
mPath : R.Executes m0 mActions m29
mPath = (R.next m-edge1 (R.next m-edge2 (R.next m-edge3 (R.next m-edge4 (R.next m-edge5 (R.next m-edge6 (R.next m-edge7 (R.next m-edge8 (R.next m-edge9 (R.next m-edge10 (R.next m-edge11 (R.next m-edge12 (R.next m-edge13 (R.next m-edge14 (R.next m-edge15 (R.next m-edge16 (R.next m-edge17 (R.next m-edge18 (R.next m-edge19 (R.next m-edge20 (R.next m-edge21 (R.next m-edge22 (R.next m-edge23 (R.next m-edge24 (R.next m-edge25 (R.next m-edge26 (R.next m-edge27 (R.next m-edge28 (R.next m-edge29 R.done)))))))))))))))))))))))))))))
abstract
  initialized-mature-failure-result : R.Executes start (wrappedActions initialMatureActions ++ mActions) m29
  initialized-mature-failure-result = Facts.append initialized-before-mature mPath

actual-partial-phase-survives-result : R.owner owner m29 ≡ just (Old.publishedFrame (S.startupState partialPC k14))
actual-partial-phase-survives-result = refl
sync-failure-does-not-invent-status : R.source m17 ≡ R.source m0
sync-failure-does-not-invent-status = refl
no-startup-resumption : R.step (R.run (X.run (W.run (G.run (M.run (P.run (U.startupStep owner S.traceMature))))))) m1 ≡ nothing
no-startup-resumption = refl
no-handoff-before-pool-close : R.step (R.handoff owner) m1 ≡ nothing
no-handoff-before-pool-close = refl
no-fake-async-catch : R.step (R.writeAsyncFailure owner) m15 ≡ nothing
no-fake-async-catch = refl
no-parent-result-at-pool-close : W.resultReady owner (R.base m15) ≡ false
no-parent-result-at-pool-close = refl
peer-error-after-real-finally : W.resultOf owner (R.base m29) ≡ just (W.peerException err)
peer-error-after-real-finally = refl
mature-source-and-pools : Facts.Paths start m29
mature-source-and-pools = Facts.exec-projects initialized-mature-failure-result
mature-captures : Capture.Captures (R.source m29)
mature-captures = Facts.from-initial-captures actual-initializer initialized-mature-failure-result
mature-supply : Supply.Valid (R.source m29)
mature-supply = Facts.from-initial-supply actual-initializer Old.Prior.initial-bounds initialized-mature-failure-result
