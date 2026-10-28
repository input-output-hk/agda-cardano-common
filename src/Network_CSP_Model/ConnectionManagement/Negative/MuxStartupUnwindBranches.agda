{-# OPTIONS --guardedness #-}

-- Initialized partial-startup failure, actual current registry close and the
-- captured CM finally. Trace/provider faults are explicit source observations.
module ConnectionManagement.Negative.MuxStartupUnwindBranches where

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
owner : WorkerId
owner = Old.owner
err : ErrorId
err = Main.err
beforeBearerActions : List P.Action
beforeBearerActions = P.run (U.startupStep owner S.allocateBuffer) ∷ []
beforeBearerPath : P.Executes Old.c11 beforeBearerActions Old.z1
beforeBearerPath = P.next Old.startup1 P.done
abstract
  initialized-buffer-ready : R.Executes Main.start
    (Main.wrappedActions (Main.callerActions ++ beforeBearerActions)) (F.wrapP Old.z1)
  initialized-buffer-ready = Main.liftP (Old.append Main.callerPath beforeBearerPath) refl refl
  initialized-published : R.Executes Main.start (Main.wrappedActions Main.callerActions) (F.wrapP Old.c11)
  initialized-published = Main.liftP Main.callerPath refl refl

b0 b1 b2 b3 b4 b5 b6 : R.State
b0 = F.wrapP Old.z1
b1 = F.selected Old.z1 S.bufferReady Mux.returned R.bufferOnly (R.sync err) R.readyBuffer
b2 = F.withExit (W.bufferScope (G.failedExit err)) (F.selected Old.z1 S.bufferReady Mux.returned R.bufferOnly (R.sync err) R.handedOff)
b3 = F.withExit (W.classifying err) (F.selected Old.z1 S.bufferReady Mux.returned R.bufferOnly (R.sync err) R.handedOff)
b4 = F.withExit (W.errorTracing err Life.shutdownPeer) (F.selected Old.z1 S.bufferReady Mux.returned R.bufferOnly (R.sync err) R.handedOff)
b5 = F.withExit (W.peerRethrow err) (F.selected Old.z1 S.bufferReady Mux.returned R.bufferOnly (R.sync err) R.handedOff)
b6 = F.withExit (W.bodyExited (W.peerException err)) (F.selected Old.z1 S.bufferReady Mux.returned R.bufferOnly (R.sync err) R.handedOff)
b-edge1 : R.step (R.observeFailure owner R.bearerSetup err) b0 ≡ just b1
b-edge1 = refl
b-edge2 : R.step (R.handoff owner) b1 ≡ just b2
b-edge2 = refl
b-edge3 : R.step (R.run (X.run (W.observeBufferReturn owner))) b2 ≡ just b3
b-edge3 = refl
b-edge4 : R.step (R.run (X.run (W.choosePolicy owner Life.shutdownPeer))) b3 ≡ just b4
b-edge4 = refl
b-edge5 : R.step (R.run (X.run (W.observeErrorTrace owner))) b4 ≡ just b5
b-edge5 = refl
b-edge6 : R.step (R.run (X.run (W.rethrow owner))) b5 ≡ just b6
b-edge6 = refl
b7 : R.State
b7 = F.withWorld (Clean.world1 (F.shared b2)) (F.withExit (W.finalizing (W.peerException err)) (F.selected Old.z1 S.bufferReady Mux.returned R.bufferOnly (R.sync err) R.handedOff))
b8 : R.State
b8 = F.withWorld (Clean.world2 (F.shared b2)) (F.withExit (W.finalizing (W.peerException err)) (F.selected Old.z1 S.bufferReady Mux.returned R.bufferOnly (R.sync err) R.handedOff))
b9 : R.State
b9 = F.withWorld (Clean.world3 (F.shared b2)) (F.withExit (W.finalizing (W.peerException err)) (F.selected Old.z1 S.bufferReady Mux.returned R.bufferOnly (R.sync err) R.handedOff))
b10 : R.State
b10 = F.withWorld (Clean.world4 (F.shared b2)) (F.withExit (W.finalizing (W.peerException err)) (F.selected Old.z1 S.bufferReady Mux.returned R.bufferOnly (R.sync err) R.handedOff))
b11 : R.State
b11 = F.withWorld (Clean.world5 (F.shared b2)) (F.withExit (W.finalizing (W.peerException err)) (F.selected Old.z1 S.bufferReady Mux.returned R.bufferOnly (R.sync err) R.handedOff))
b12 : R.State
b12 = F.withWorld (Clean.world6 (F.shared b2)) (F.withExit (W.finalizing (W.peerException err)) (F.selected Old.z1 S.bufferReady Mux.returned R.bufferOnly (R.sync err) R.handedOff))
b13 b14 : R.State
b13 = F.withWorld (Clean.world6 (F.shared b2)) (F.withExit (W.cleanupComplete (W.peerException err) Shared.cleanupNormal) (F.selected Old.z1 S.bufferReady Mux.returned R.bufferOnly (R.sync err) R.handedOff))
b14 = F.withWorld (Clean.world6 (F.shared b2)) (F.withExit (W.resultAvailable (W.peerException err) Shared.cleanupNormal) (F.selected Old.z1 S.bufferReady Mux.returned R.bufferOnly (R.sync err) R.handedOff))
b-edge7 : R.step (R.run (X.run (W.enterFinalizer owner))) b6 ≡ just b7
b-edge7 = refl
b-edge8 : R.step (R.run (X.run (W.cleanup owner C.takeCleanupMap))) b7 ≡ just b8
b-edge8 = refl
b-edge9 : R.step (R.run (X.run (W.cleanup owner C.selectCleanupEntry))) b8 ≡ just b9
b-edge9 = refl
b-edge10 : R.step (R.run (X.run (W.cleanup owner C.closeHandlerSocket))) b9 ≡ just b10
b-edge10 = refl
b-edge11 : R.step (R.run (X.run (W.cleanup owner C.publishCleanupMap))) b10 ≡ just b11
b-edge11 = refl
b-edge12 : R.step (R.run (X.run (W.cleanup owner C.readCleanupCounters))) b11 ≡ just b12
b-edge12 = refl
b-edge13 : R.step (R.run (X.run (W.finishCleanup owner))) b12 ≡ just b13
b-edge13 = refl
b-edge14 : R.step (R.run (X.run (W.publishAsyncResult owner))) b13 ≡ just b14
b-edge14 = refl
bActions : List R.Action
bActions = (R.observeFailure owner R.bearerSetup err) ∷ (R.handoff owner) ∷ (R.run (X.run (W.observeBufferReturn owner))) ∷ (R.run (X.run (W.choosePolicy owner Life.shutdownPeer))) ∷ (R.run (X.run (W.observeErrorTrace owner))) ∷ (R.run (X.run (W.rethrow owner))) ∷ (R.run (X.run (W.enterFinalizer owner))) ∷ (R.run (X.run (W.cleanup owner C.takeCleanupMap))) ∷ (R.run (X.run (W.cleanup owner C.selectCleanupEntry))) ∷ (R.run (X.run (W.cleanup owner C.closeHandlerSocket))) ∷ (R.run (X.run (W.cleanup owner C.publishCleanupMap))) ∷ (R.run (X.run (W.cleanup owner C.readCleanupCounters))) ∷ (R.run (X.run (W.finishCleanup owner))) ∷ (R.run (X.run (W.publishAsyncResult owner))) ∷ []
bPath : R.Executes b0 bActions b14
bPath = (R.next b-edge1 (R.next b-edge2 (R.next b-edge3 (R.next b-edge4 (R.next b-edge5 (R.next b-edge6 (R.next b-edge7 (R.next b-edge8 (R.next b-edge9 (R.next b-edge10 (R.next b-edge11 (R.next b-edge12 (R.next b-edge13 (R.next b-edge14 R.done))))))))))))))
abstract
  initialized-bearer-failure-result : R.Executes Main.start
    (Main.wrappedActions (Main.callerActions ++ beforeBearerActions) ++ bActions) b14
  initialized-bearer-failure-result = Facts.append initialized-buffer-ready bPath
bearer-failure-does-not-close-unused-pool : Pool.phase (R.poolAt owner b14) ≡ Pool.openPool
bearer-failure-does-not-close-unused-pool = refl
bearer-failure-has-no-physical-jobs : Pool.handles (R.poolAt owner b14) ≡ []
bearer-failure-has-no-physical-jobs = refl
bearer-failure-still-runs-CM-finally : W.resultOf owner (R.base b14) ≡ just (W.peerException err)
bearer-failure-still-runs-CM-finally = refl
no-fake-pool-snapshot : R.step (R.beginClose owner []) b1 ≡ nothing
no-fake-pool-snapshot = refl
no-buffer-skip-after-bearer-failure : R.step (R.run (X.run (W.enterFinalizer owner))) b2 ≡ nothing
no-buffer-skip-after-bearer-failure = refl

p0 p1 p2 : R.State
p0 = F.wrapP Old.c11
p1 = F.selected Old.c11 S.published Mux.returned R.beforeBuffer (R.sync err) R.readyBody
p2 = F.withExit (W.classifying err) (F.selected Old.c11 S.published Mux.returned R.beforeBuffer (R.sync err) R.handedOff)
provider-acquisition-failed : R.step (R.observeFailure owner R.bufferAcquire err) p0 ≡ just p1
provider-acquisition-failed = refl
provider-failure-before-callback : R.step (R.handoff owner) p1 ≡ just p2
provider-failure-before-callback = refl
no-fictional-provider-callback-return : R.step (R.run (X.run (W.observeBufferReturn owner))) p2 ≡ nothing
no-fictional-provider-callback-return = refl
abstract
  initialized-acquisition-failure : R.Executes Main.start
    (Main.wrappedActions Main.callerActions ++ (R.observeFailure owner R.bufferAcquire err ∷ R.handoff owner ∷ [])) p2
  initialized-acquisition-failure = Facts.append initialized-published (R.next provider-acquisition-failed (R.next provider-failure-before-callback R.done))
beforePoolActions : List P.Action
beforePoolActions = P.run (U.startupStep owner S.allocateBuffer) ∷ P.run (U.startupStep owner S.createBearer) ∷ P.run (U.startupStep owner S.enterRun) ∷ P.run (U.startupStep owner S.traceStarting) ∷ P.run (U.startupStep owner S.allocateEgress) ∷ P.run (U.startupStep owner S.openPool) ∷ []
beforePoolPath : P.Executes Old.c11 beforePoolActions Old.z6
beforePoolPath = (P.next Old.startup1 (P.next Old.startup2 (P.next Old.startup3 (P.next Old.startup4 (P.next Old.startup5 (P.next Old.startup6 P.done))))))
abstract
  initialized-empty-pool : R.Executes Main.start
    (Main.wrappedActions (Main.callerActions ++ beforePoolActions)) (F.wrapP Old.z6)
  initialized-empty-pool = Main.liftP (Old.append Main.callerPath beforePoolPath) refl refl
emptyClosing emptyClosed : Pool.State
emptyClosing = record Pool.initial { phase = Pool.closing }
emptyClosed = record Pool.initial { phase = Pool.closedPool }
baseMux failedMux deadMux sampledMux endedMux : Mux.Mux
baseMux = Old.G.armedMux
failedMux = record baseMux { status = Mux.failed err }
deadMux = record failedMux { callback = Mux.readActive Mux.muxStopped }
sampledMux = record failedMux { callback = Mux.commitTrace true Mux.muxStopped }
endedMux = record failedMux { traceCounters = nothing }
atAsync : Mux.Mux → Pool.State → List Shared.IGEvent → P.State
atAsync m pool queue = Old.at (Old.sourceMux m queue) (S.startupState S.poolReady pool) [] []
a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : R.State
a0 = F.wrapP Old.z6
a1 = F.selected (atAsync baseMux Pool.initial []) S.poolReady Mux.returned R.poolBody (R.async err) R.awaitingClose
a2 = F.selected (atAsync baseMux emptyClosing []) S.poolReady Mux.returned R.poolBody (R.async err) R.closing
a3 = F.selected (atAsync baseMux emptyClosed []) S.poolReady Mux.returned R.poolBody (R.async err) R.poolClosed
a4 = F.selected (atAsync failedMux emptyClosed []) S.poolReady Mux.returned R.poolBody (R.async err) R.asyncStatus
a5 = F.selected (atAsync deadMux emptyClosed []) S.poolReady Mux.returned R.poolBody (R.async err) R.asyncDead
a6 = F.selected (atAsync sampledMux emptyClosed []) S.poolReady Mux.returned R.poolBody (R.async err) R.asyncDead
a7 = F.selected (atAsync endedMux emptyClosed (Shared.muxFinished (Shared.handlerKey Old.Prior.captured) ∷ [])) S.poolReady Mux.returned R.poolBody (R.async err) R.asyncDead
a8 = F.selected (atAsync endedMux emptyClosed (Shared.muxFinished (Shared.handlerKey Old.Prior.captured) ∷ [])) S.poolReady Mux.returned R.poolBody (R.async err) R.readyBuffer
a9 = F.withExit (W.bufferScope (G.asyncExit err)) (F.selected (atAsync endedMux emptyClosed (Shared.muxFinished (Shared.handlerKey Old.Prior.captured) ∷ [])) S.poolReady Mux.returned R.poolBody (R.async err) R.handedOff)
a10 = F.withExit (W.bodyExited (W.asyncException err)) (F.selected (atAsync endedMux emptyClosed (Shared.muxFinished (Shared.handlerKey Old.Prior.captured) ∷ [])) S.poolReady Mux.returned R.poolBody (R.async err) R.handedOff)
a-edge1 : R.step (R.observeCancellation owner R.unmaskedStartup err) a0 ≡ just a1
a-edge1 = refl
a-edge2 : R.step (R.beginClose owner []) a1 ≡ just a2
a-edge2 = refl
a-edge3 : R.step (R.finishClose owner) a2 ≡ just a3
a-edge3 = refl
a-edge4 : R.step (R.writeAsyncFailure owner) a3 ≡ just a4
a-edge4 = refl
a-edge5 : R.step (R.beginDead owner) a4 ≡ just a5
a-edge5 = refl
a-edge6 : R.step (R.sampleDead owner) a5 ≡ just a6
a-edge6 = refl
a-edge7 : R.step (R.commitDead owner) a6 ≡ just a7
a-edge7 = refl
a-edge8 : R.step (R.finishDead owner) a7 ≡ just a8
a-edge8 = refl
a-edge9 : R.step (R.handoff owner) a8 ≡ just a9
a-edge9 = refl
a-edge10 : R.step (R.run (X.run (W.observeBufferReturn owner))) a9 ≡ just a10
a-edge10 = refl
a11 : R.State
a11 = F.withWorld (Clean.world1 (F.shared a9)) (F.withExit (W.finalizing (W.asyncException err)) (F.selected (atAsync endedMux emptyClosed (Shared.muxFinished (Shared.handlerKey Old.Prior.captured) ∷ [])) S.poolReady Mux.returned R.poolBody (R.async err) R.handedOff))
a12 : R.State
a12 = F.withWorld (Clean.world2 (F.shared a9)) (F.withExit (W.finalizing (W.asyncException err)) (F.selected (atAsync endedMux emptyClosed (Shared.muxFinished (Shared.handlerKey Old.Prior.captured) ∷ [])) S.poolReady Mux.returned R.poolBody (R.async err) R.handedOff))
a13 : R.State
a13 = F.withWorld (Clean.world3 (F.shared a9)) (F.withExit (W.finalizing (W.asyncException err)) (F.selected (atAsync endedMux emptyClosed (Shared.muxFinished (Shared.handlerKey Old.Prior.captured) ∷ [])) S.poolReady Mux.returned R.poolBody (R.async err) R.handedOff))
a14 : R.State
a14 = F.withWorld (Clean.world4 (F.shared a9)) (F.withExit (W.finalizing (W.asyncException err)) (F.selected (atAsync endedMux emptyClosed (Shared.muxFinished (Shared.handlerKey Old.Prior.captured) ∷ [])) S.poolReady Mux.returned R.poolBody (R.async err) R.handedOff))
a15 : R.State
a15 = F.withWorld (Clean.world5 (F.shared a9)) (F.withExit (W.finalizing (W.asyncException err)) (F.selected (atAsync endedMux emptyClosed (Shared.muxFinished (Shared.handlerKey Old.Prior.captured) ∷ [])) S.poolReady Mux.returned R.poolBody (R.async err) R.handedOff))
a16 : R.State
a16 = F.withWorld (Clean.world6 (F.shared a9)) (F.withExit (W.finalizing (W.asyncException err)) (F.selected (atAsync endedMux emptyClosed (Shared.muxFinished (Shared.handlerKey Old.Prior.captured) ∷ [])) S.poolReady Mux.returned R.poolBody (R.async err) R.handedOff))
a17 a18 : R.State
a17 = F.withWorld (Clean.world6 (F.shared a9)) (F.withExit (W.cleanupComplete (W.asyncException err) Shared.cleanupNormal) (F.selected (atAsync endedMux emptyClosed (Shared.muxFinished (Shared.handlerKey Old.Prior.captured) ∷ [])) S.poolReady Mux.returned R.poolBody (R.async err) R.handedOff))
a18 = F.withWorld (Clean.world6 (F.shared a9)) (F.withExit (W.resultAvailable (W.asyncException err) Shared.cleanupNormal) (F.selected (atAsync endedMux emptyClosed (Shared.muxFinished (Shared.handlerKey Old.Prior.captured) ∷ [])) S.poolReady Mux.returned R.poolBody (R.async err) R.handedOff))
a-edge11 : R.step (R.run (X.run (W.enterFinalizer owner))) a10 ≡ just a11
a-edge11 = refl
a-edge12 : R.step (R.run (X.run (W.cleanup owner C.takeCleanupMap))) a11 ≡ just a12
a-edge12 = refl
a-edge13 : R.step (R.run (X.run (W.cleanup owner C.selectCleanupEntry))) a12 ≡ just a13
a-edge13 = refl
a-edge14 : R.step (R.run (X.run (W.cleanup owner C.closeHandlerSocket))) a13 ≡ just a14
a-edge14 = refl
a-edge15 : R.step (R.run (X.run (W.cleanup owner C.publishCleanupMap))) a14 ≡ just a15
a-edge15 = refl
a-edge16 : R.step (R.run (X.run (W.cleanup owner C.readCleanupCounters))) a15 ≡ just a16
a-edge16 = refl
a-edge17 : R.step (R.run (X.run (W.finishCleanup owner))) a16 ≡ just a17
a-edge17 = refl
a-edge18 : R.step (R.run (X.run (W.publishAsyncResult owner))) a17 ≡ just a18
a-edge18 = refl
aActions : List R.Action
aActions = (R.observeCancellation owner R.unmaskedStartup err) ∷ (R.beginClose owner []) ∷ (R.finishClose owner) ∷ (R.writeAsyncFailure owner) ∷ (R.beginDead owner) ∷ (R.sampleDead owner) ∷ (R.commitDead owner) ∷ (R.finishDead owner) ∷ (R.handoff owner) ∷ (R.run (X.run (W.observeBufferReturn owner))) ∷ (R.run (X.run (W.enterFinalizer owner))) ∷ (R.run (X.run (W.cleanup owner C.takeCleanupMap))) ∷ (R.run (X.run (W.cleanup owner C.selectCleanupEntry))) ∷ (R.run (X.run (W.cleanup owner C.closeHandlerSocket))) ∷ (R.run (X.run (W.cleanup owner C.publishCleanupMap))) ∷ (R.run (X.run (W.cleanup owner C.readCleanupCounters))) ∷ (R.run (X.run (W.finishCleanup owner))) ∷ (R.run (X.run (W.publishAsyncResult owner))) ∷ []
aPath : R.Executes a0 aActions a18
aPath = (R.next a-edge1 (R.next a-edge2 (R.next a-edge3 (R.next a-edge4 (R.next a-edge5 (R.next a-edge6 (R.next a-edge7 (R.next a-edge8 (R.next a-edge9 (R.next a-edge10 (R.next a-edge11 (R.next a-edge12 (R.next a-edge13 (R.next a-edge14 (R.next a-edge15 (R.next a-edge16 (R.next a-edge17 (R.next a-edge18 R.done))))))))))))))))))
abstract
  initialized-startup-async-result : R.Executes Main.start
    (Main.wrappedActions (Main.callerActions ++ beforePoolActions) ++ aActions) a18
  initialized-startup-async-result = Facts.append initialized-empty-pool aPath
no-early-async-status : R.step (R.writeAsyncFailure owner) a1 ≡ nothing
no-early-async-status = refl
no-fake-sync-escape : R.step (R.continueSync owner) a3 ≡ nothing
no-fake-sync-escape = refl
no-parent-result-at-Dead : W.resultReady owner (R.base a7) ≡ false
no-parent-result-at-Dead = refl
async-startup-result-keeps-error-class : W.resultOf owner (R.base a18) ≡ just (W.asyncException err)
async-startup-result-keeps-error-class = refl
no-physical-engine-was-invented : Pool.handles (R.poolAt owner a18) ≡ []
no-physical-engine-was-invented = refl
no-physical-startup-success-was-invented : R.owner owner a18 ≡ just (Old.publishedFrame (S.startupState S.poolReady emptyClosed))
no-physical-startup-success-was-invented = refl
bearer-source-pools : Facts.Paths Main.start b14
bearer-source-pools = Facts.exec-projects initialized-bearer-failure-result
async-source-pools : Facts.Paths Main.start a18
async-source-pools = Facts.exec-projects initialized-startup-async-result
async-captures : Capture.Captures (R.source a18)
async-captures = Facts.from-initial-captures Main.actual-initializer initialized-startup-async-result
async-supply : Supply.Valid (R.source a18)
async-supply = Facts.from-initial-supply Main.actual-initializer Old.Prior.initial-bounds initialized-startup-async-result
