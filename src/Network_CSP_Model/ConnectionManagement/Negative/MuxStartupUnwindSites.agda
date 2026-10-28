{-# OPTIONS --guardedness #-}

-- Initialized partial-startup failure, actual current registry close and the
-- captured CM finally. Trace/provider faults are explicit source observations.
module ConnectionManagement.Negative.MuxStartupUnwindSites where

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
import ConnectionManagement.Negative.MuxStartupUnwindBranches as Branch
import Data.List as List
owner : WorkerId
owner = Old.owner
err : ErrorId
err = Main.err
bufferAcquireBefore bufferAcquireAfter : R.State
bufferAcquireBefore = F.wrapP Old.c11
bufferAcquireAfter = F.selected Old.c11 (S.published) Mux.returned R.beforeBuffer (R.sync err) R.readyBody
bufferAcquire-step : R.step (R.observeFailure owner R.bufferAcquire err) bufferAcquireBefore ≡ just bufferAcquireAfter
bufferAcquire-step = refl
bufferAcquirePrefix : P.Executes Old.c11 (List.take 0 Old.startupPathActions) Old.c11
bufferAcquirePrefix =  P.done
abstract
  initialized-bufferAcquire : R.Executes Main.start
    (Main.wrappedActions (Main.callerActions ++ List.take 0 Old.startupPathActions) ++ (R.observeFailure owner R.bufferAcquire err ∷ [])) bufferAcquireAfter
  initialized-bufferAcquire = Facts.append (Main.liftP (Old.append Main.callerPath bufferAcquirePrefix) refl refl) (R.next bufferAcquire-step R.done)
bearerSetupBefore bearerSetupAfter : R.State
bearerSetupBefore = F.wrapP Old.z1
bearerSetupAfter = F.selected Old.z1 (S.bufferReady) Mux.returned R.bufferOnly (R.sync err) R.readyBuffer
bearerSetup-step : R.step (R.observeFailure owner R.bearerSetup err) bearerSetupBefore ≡ just bearerSetupAfter
bearerSetup-step = refl
bearerSetupPrefix : P.Executes Old.c11 (List.take 1 Old.startupPathActions) Old.z1
bearerSetupPrefix = (P.next Old.startup1 P.done)
abstract
  initialized-bearerSetup : R.Executes Main.start
    (Main.wrappedActions (Main.callerActions ++ List.take 1 Old.startupPathActions) ++ (R.observeFailure owner R.bearerSetup err ∷ [])) bearerSetupAfter
  initialized-bearerSetup = Facts.append (Main.liftP (Old.append Main.callerPath bearerSetupPrefix) refl refl) (R.next bearerSetup-step R.done)
startingTraceBefore startingTraceAfter : R.State
startingTraceBefore = F.wrapP Old.z3
startingTraceAfter = F.selected Old.z3 (S.runEntered) Mux.returned R.bufferOnly (R.sync err) R.readyBuffer
startingTrace-step : R.step (R.observeFailure owner R.startingTrace err) startingTraceBefore ≡ just startingTraceAfter
startingTrace-step = refl
startingTracePrefix : P.Executes Old.c11 (List.take 3 Old.startupPathActions) Old.z3
startingTracePrefix = (P.next Old.startup1 (P.next Old.startup2 (P.next Old.startup3 P.done)))
abstract
  initialized-startingTrace : R.Executes Main.start
    (Main.wrappedActions (Main.callerActions ++ List.take 3 Old.startupPathActions) ++ (R.observeFailure owner R.startingTrace err ∷ [])) startingTraceAfter
  initialized-startingTrace = Facts.append (Main.liftP (Old.append Main.callerPath startingTracePrefix) refl refl) (R.next startingTrace-step R.done)
egressSetupBefore egressSetupAfter : R.State
egressSetupBefore = F.wrapP Old.z4
egressSetupAfter = F.selected Old.z4 (S.startingTraced) Mux.returned R.bufferOnly (R.sync err) R.readyBuffer
egressSetup-step : R.step (R.observeFailure owner R.egressSetup err) egressSetupBefore ≡ just egressSetupAfter
egressSetup-step = refl
egressSetupPrefix : P.Executes Old.c11 (List.take 4 Old.startupPathActions) Old.z4
egressSetupPrefix = (P.next Old.startup1 (P.next Old.startup2 (P.next Old.startup3 (P.next Old.startup4 P.done))))
abstract
  initialized-egressSetup : R.Executes Main.start
    (Main.wrappedActions (Main.callerActions ++ List.take 4 Old.startupPathActions) ++ (R.observeFailure owner R.egressSetup err ∷ [])) egressSetupAfter
  initialized-egressSetup = Facts.append (Main.liftP (Old.append Main.callerPath egressSetupPrefix) refl refl) (R.next egressSetup-step R.done)
poolAcquireBefore poolAcquireAfter : R.State
poolAcquireBefore = F.wrapP Old.z5
poolAcquireAfter = F.selected Old.z5 (S.egressReady) Mux.returned R.bufferOnly (R.sync err) R.readyBuffer
poolAcquire-step : R.step (R.observeFailure owner R.poolAcquire err) poolAcquireBefore ≡ just poolAcquireAfter
poolAcquire-step = refl
poolAcquirePrefix : P.Executes Old.c11 (List.take 5 Old.startupPathActions) Old.z5
poolAcquirePrefix = (P.next Old.startup1 (P.next Old.startup2 (P.next Old.startup3 (P.next Old.startup4 (P.next Old.startup5 P.done)))))
abstract
  initialized-poolAcquire : R.Executes Main.start
    (Main.wrappedActions (Main.callerActions ++ List.take 5 Old.startupPathActions) ++ (R.observeFailure owner R.poolAcquire err ∷ [])) poolAcquireAfter
  initialized-poolAcquire = Facts.append (Main.liftP (Old.append Main.callerPath poolAcquirePrefix) refl refl) (R.next poolAcquire-step R.done)
firstForkBefore firstForkAfter : R.State
firstForkBefore = F.wrapP Old.z6
firstForkAfter = F.selected Old.z6 (S.poolReady) Mux.returned R.poolBody (R.sync err) R.awaitingClose
firstFork-step : R.step (R.observeFailure owner R.firstFork err) firstForkBefore ≡ just firstForkAfter
firstFork-step = refl
firstForkPrefix : P.Executes Old.c11 (List.take 6 Old.startupPathActions) Old.z6
firstForkPrefix = (P.next Old.startup1 (P.next Old.startup2 (P.next Old.startup3 (P.next Old.startup4 (P.next Old.startup5 (P.next Old.startup6 P.done))))))
abstract
  initialized-firstFork : R.Executes Main.start
    (Main.wrappedActions (Main.callerActions ++ List.take 6 Old.startupPathActions) ++ (R.observeFailure owner R.firstFork err ∷ [])) firstForkAfter
  initialized-firstFork = Facts.append (Main.liftP (Old.append Main.callerPath firstForkPrefix) refl refl) (R.next firstFork-step R.done)
secondForkBefore secondForkAfter : R.State
secondForkBefore = F.wrapP Old.z8
secondForkAfter = F.selected Old.z8 (S.muxerRegistered Old.j₀) Mux.returned R.poolBody (R.sync err) R.awaitingClose
secondFork-step : R.step (R.observeFailure owner R.secondFork err) secondForkBefore ≡ just secondForkAfter
secondFork-step = refl
secondForkPrefix : P.Executes Old.c11 (List.take 8 Old.startupPathActions) Old.z8
secondForkPrefix = (P.next Old.startup1 (P.next Old.startup2 (P.next Old.startup3 (P.next Old.startup4 (P.next Old.startup5 (P.next Old.startup6 (P.next Old.startup7 (P.next Old.startup8 P.done))))))))
abstract
  initialized-secondFork : R.Executes Main.start
    (Main.wrappedActions (Main.callerActions ++ List.take 8 Old.startupPathActions) ++ (R.observeFailure owner R.secondFork err ∷ [])) secondForkAfter
  initialized-secondFork = Facts.append (Main.liftP (Old.append Main.callerPath secondForkPrefix) refl refl) (R.next secondFork-step R.done)
matureTraceBefore matureTraceAfter : R.State
matureTraceBefore = F.wrapP Old.z10
matureTraceAfter = F.selected Old.z10 (S.demuxerRegistered Old.j₀ Old.j₁) Mux.returned R.poolBody (R.sync err) R.awaitingClose
matureTrace-step : R.step (R.observeFailure owner R.matureTrace err) matureTraceBefore ≡ just matureTraceAfter
matureTrace-step = refl
matureTracePrefix : P.Executes Old.c11 (List.take 10 Old.startupPathActions) Old.z10
matureTracePrefix = (P.next Old.startup1 (P.next Old.startup2 (P.next Old.startup3 (P.next Old.startup4 (P.next Old.startup5 (P.next Old.startup6 (P.next Old.startup7 (P.next Old.startup8 (P.next Old.startup9 (P.next Old.startup10 P.done))))))))))
abstract
  initialized-matureTrace : R.Executes Main.start
    (Main.wrappedActions (Main.callerActions ++ List.take 10 Old.startupPathActions) ++ (R.observeFailure owner R.matureTrace err ∷ [])) matureTraceAfter
  initialized-matureTrace = Facts.append (Main.liftP (Old.append Main.callerPath matureTracePrefix) refl refl) (R.next matureTrace-step R.done)
timeoutSetupBefore timeoutSetupAfter : R.State
timeoutSetupBefore = F.wrapP Old.z11
timeoutSetupAfter = F.selected Old.z11 (S.matureTraced Old.j₀ Old.j₁) Mux.returned R.poolBody (R.sync err) R.awaitingClose
timeoutSetup-step : R.step (R.observeFailure owner R.timeoutSetup err) timeoutSetupBefore ≡ just timeoutSetupAfter
timeoutSetup-step = refl
timeoutSetupPrefix : P.Executes Old.c11 (List.take 11 Old.startupPathActions) Old.z11
timeoutSetupPrefix = (P.next Old.startup1 (P.next Old.startup2 (P.next Old.startup3 (P.next Old.startup4 (P.next Old.startup5 (P.next Old.startup6 (P.next Old.startup7 (P.next Old.startup8 (P.next Old.startup9 (P.next Old.startup10 (P.next Old.startup11 P.done)))))))))))
abstract
  initialized-timeoutSetup : R.Executes Main.start
    (Main.wrappedActions (Main.callerActions ++ List.take 11 Old.startupPathActions) ++ (R.observeFailure owner R.timeoutSetup err ∷ [])) timeoutSetupAfter
  initialized-timeoutSetup = Facts.append (Main.liftP (Old.append Main.callerPath timeoutSetupPrefix) refl refl) (R.next timeoutSetup-step R.done)

-- The ignored graceful trace sites are inside the acquired pool as well.
stopBefore stopAfter stoppedBefore stoppedAfter : R.State
stopBefore = Facts.wrap (W.handlerExitState GF.normal2 [])
stopAfter = F.mark (W.handlerExitState GF.normal2 []) (S.monitoring Old.j₀ Old.j₁) Mux.returned R.poolBody (R.sync err) R.awaitingClose
stoppedBefore = Facts.wrap (W.handlerExitState GF.normal14 [])
stoppedAfter = F.mark (W.handlerExitState GF.normal14 []) (S.monitoring Old.j₀ Old.j₁) Mux.returned R.poolBody (R.sync err) R.awaitingClose
stop-tracer-failure : R.step (R.observeFailure owner R.stoppingTrace err) stopBefore ≡ just stopAfter
stop-tracer-failure = refl
stopped-tracer-failure : R.step (R.observeFailure owner R.stoppedTrace err) stoppedBefore ≡ just stoppedAfter
stopped-tracer-failure = refl
stopActions : List G.Action
stopActions = G.requestShutdown owner ∷ G.selectShutdown owner ∷ []
stopPrefix : G.Executes GF.normal0 stopActions GF.normal2
stopPrefix = G.next GF.normal-edge1 (G.next GF.normal-edge2 G.done)
stoppedActions : List G.Action
stoppedActions = GF.normalPrefix12Actions ++ (G.drainEmpty owner ∷ G.writeStopped owner ∷ [])
stoppedPrefix : G.Executes GF.normal0 stoppedActions GF.normal14
stoppedPrefix = GF.append GF.normalPrefix12 (G.next GF.normal-edge13 (G.next GF.normal-edge14 G.done))
wrapG : G.State → R.State
wrapG g = Facts.wrap (W.handlerExitState g [])
liftG : ∀ {g actions g′} → G.Executes g actions g′ → ExitProof.allSafe actions ≡ true →
  R.Executes (wrapG g) (map R.run (map X.run (map W.run actions))) (wrapG g′)
liftG path safe = Facts.lift (Cancel.lift (ExitProof.lift-path path safe))
groupActionsOf : ∀ {g actions g′} → G.Executes g actions g′ → List G.Action
groupActionsOf {actions = actions} path = actions
abstract
  initialized-stop-tracer-failure : R.Executes Main.start
    ((map R.run (map X.run (map W.run (groupActionsOf GF.initialized-running))) ++ map R.run (map X.run (map W.run stopActions))) ++ (R.observeFailure owner R.stoppingTrace err ∷ [])) stopAfter
  initialized-stop-tracer-failure = Facts.append (Facts.append (liftG GF.initialized-running refl) (liftG stopPrefix refl)) (R.next stop-tracer-failure R.done)

-- The async catch's own tracer is outside that catch handler. Its synchronous
-- failure replaces the original async error without a second Failed write.
newError : ErrorId
newError = errorId 99
deadFailure deadHandoff : R.State
deadFailure = F.selected (Branch.atAsync Branch.deadMux Branch.emptyClosed []) S.poolReady Mux.returned R.poolBody (R.sync newError) R.readyBuffer
deadHandoff = F.withExit (W.bufferScope (G.failedExit newError)) (F.selected (Branch.atAsync Branch.deadMux Branch.emptyClosed []) S.poolReady Mux.returned R.poolBody (R.sync newError) R.handedOff)
dead-tracer-exception : R.step (R.observeDeadTraceException owner newError) Branch.a5 ≡ just deadFailure
dead-tracer-exception = refl
dead-tracer-rethrow : R.step (R.handoff owner) deadFailure ≡ just deadHandoff
dead-tracer-rethrow = refl
no-second-async-catch : R.step (R.writeAsyncFailure owner) deadFailure ≡ nothing
no-second-async-catch = refl
original-status-survives-replacement : R.source deadHandoff ≡ R.source Branch.a5
original-status-survives-replacement = refl
no-failure-after-IG-read-without-interpreter-evidence : R.step (R.observeDeadTraceException owner newError) Branch.a6 ≡ nothing
no-failure-after-IG-read-without-interpreter-evidence = refl
no-dead-trace-return-after-exception : R.step (R.finishDead owner) deadFailure ≡ nothing
no-dead-trace-return-after-exception = refl
asyncBeforeDeadActions : List R.Action
asyncBeforeDeadActions = R.observeCancellation owner R.unmaskedStartup err ∷ R.beginClose owner [] ∷ R.finishClose owner ∷ R.writeAsyncFailure owner ∷ R.beginDead owner ∷ []
asyncBeforeDead : R.Executes Branch.a0 asyncBeforeDeadActions Branch.a5
asyncBeforeDead = R.next Branch.a-edge1 (R.next Branch.a-edge2 (R.next Branch.a-edge3 (R.next Branch.a-edge4 (R.next Branch.a-edge5 R.done))))
abstract
  initialized-dead-tracer-replacement : R.Executes Main.start
    ((Main.wrappedActions (Main.callerActions ++ Branch.beforePoolActions) ++ asyncBeforeDeadActions) ++ (R.observeDeadTraceException owner newError ∷ R.handoff owner ∷ [])) deadHandoff
  initialized-dead-tracer-replacement = Facts.append (Facts.append Branch.initialized-empty-pool asyncBeforeDead)
    (R.next dead-tracer-exception (R.next dead-tracer-rethrow R.done))

abstract
  initialized-stopped-tracer-failure : R.Executes Main.start
    ((map R.run (map X.run (map W.run (groupActionsOf GF.initialized-running))) ++ map R.run (map X.run (map W.run stoppedActions))) ++ (R.observeFailure owner R.stoppedTrace err ∷ [])) stoppedAfter
  initialized-stopped-tracer-failure = Facts.append
    (Facts.append (liftG GF.initialized-running refl) (liftG stoppedPrefix refl))
    (R.next stopped-tracer-failure R.done)

-- This is BEFORE the withJobPool expression's async catch, inside restored
-- Mx.run at TraceStarting. No mux Failed/Dead or pool close is manufactured.
preCatch preCatchHandoff : R.State
preCatch = F.selected Old.z3 S.runEntered Mux.returned R.bufferOnly (R.async err) R.readyBuffer
preCatchHandoff = F.withExit (W.bufferScope (G.asyncExit err)) (F.selected Old.z3 S.runEntered Mux.returned R.bufferOnly (R.async err) R.handedOff)
pre-catch-delivery : R.step (R.observeCancellation owner R.unmaskedStartup err) startingTraceBefore ≡ just preCatch
pre-catch-delivery = refl
pre-catch-handoff : R.step (R.handoff owner) preCatch ≡ just preCatchHandoff
pre-catch-handoff = refl
pre-catch-does-not-enter-later-catch : R.step (R.writeAsyncFailure owner) preCatch ≡ nothing
pre-catch-does-not-enter-later-catch = refl
pre-catch-source-status-preserved : R.source preCatchHandoff ≡ R.source startingTraceBefore
pre-catch-source-status-preserved = refl
abstract
  initialized-pre-catch-cancellation : R.Executes Main.start
    (Main.wrappedActions (Main.callerActions ++ List.take 3 Old.startupPathActions) ++
      (R.observeCancellation owner R.unmaskedStartup err ∷ R.handoff owner ∷ [])) preCatchHandoff
  initialized-pre-catch-cancellation = Facts.append
    (Main.liftP (Old.append Main.callerPath startingTracePrefix) refl refl)
    (R.next pre-catch-delivery (R.next pre-catch-handoff R.done))
