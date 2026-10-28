{-# OPTIONS --guardedness #-}

-- Initialized partial-startup failure, actual current registry close and the
-- captured CM finally. Trace/provider faults are explicit source observations.
module ConnectionManagement.Negative.MuxStartupUnwindCM where

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
import ConnectionManagement.Rules.CMShutdown as Close
owner : WorkerId
owner = Old.owner
err : ErrorId
err = Main.err
reading wait : Close.State
reading = Close.shutdownState Close.reading (ident 0 ∷ []) [] (owner ∷ [])
wait = Close.shutdownState Close.awaitResults (ident 0 ∷ []) [] (owner ∷ [])
q0 q1 q2 q3 q4 q5 : R.State
q0 = Branch.a0
q1 = F.withShutdown (Close.shutdownState Close.reading (ident 0 ∷ []) (ident 0 ∷ []) []) q0
q2 = F.withShutdown (Close.shutdownState (Close.sendReady (ident 0) owner) (ident 0 ∷ []) [] []) q0
q3 = F.withShutdown (Close.shutdownState (Close.awaitDelivery (ident 0) owner) (ident 0 ∷ []) [] []) q0
q4 = F.withShutdown reading Branch.a1
q5 = F.withShutdown wait Branch.a1
q-edge1 : R.step (R.run (X.run (W.shutdownStep Close.captureSnapshot))) q0 ≡ just q1
q-edge1 = refl
q-edge2 : R.step (R.run (X.run (W.shutdownStep Close.readEntry))) q1 ≡ just q2
q-edge2 = refl
q-edge3 : R.step (R.run (X.run (W.shutdownStep Close.requestCancellation))) q2 ≡ just q3
q-edge3 = refl
q-edge4 : R.step (R.deliverShutdown R.unmaskedStartup err) q3 ≡ just q4
q-edge4 = refl
q-edge5 : R.step (R.run (X.run (W.shutdownStep Close.finishTraversal))) q4 ≡ just q5
q-edge5 = refl
qActions : List R.Action
qActions = R.run (X.run (W.shutdownStep Close.captureSnapshot)) ∷ R.run (X.run (W.shutdownStep Close.readEntry)) ∷
  R.run (X.run (W.shutdownStep Close.requestCancellation)) ∷ R.deliverShutdown R.unmaskedStartup err ∷
  R.run (X.run (W.shutdownStep Close.finishTraversal)) ∷ []
qPath : R.Executes q0 qActions q5
qPath = R.next q-edge1 (R.next q-edge2 (R.next q-edge3 (R.next q-edge4 (R.next q-edge5 R.done))))
send-ack-is-not-joined-pool : Pool.phase (R.poolAt owner q4) ≡ Pool.openPool
send-ack-is-not-joined-pool = refl
send-ack-is-not-parent-result : W.resultReady owner (R.base q4) ≡ false
send-ack-is-not-parent-result = refl
wait-refuses-before-pool-unwind : R.step (R.run (X.run (W.shutdownStep Close.finishClose))) q5 ≡ nothing
wait-refuses-before-pool-unwind = refl
u2 : R.State
u2 = F.withShutdown wait Branch.a2
u-edge2 : R.step (R.beginClose owner []) q5 ≡ just u2
u-edge2 = refl
u3 : R.State
u3 = F.withShutdown wait Branch.a3
u-edge3 : R.step (R.finishClose owner) u2 ≡ just u3
u-edge3 = refl
u4 : R.State
u4 = F.withShutdown wait Branch.a4
u-edge4 : R.step (R.writeAsyncFailure owner) u3 ≡ just u4
u-edge4 = refl
u5 : R.State
u5 = F.withShutdown wait Branch.a5
u-edge5 : R.step (R.beginDead owner) u4 ≡ just u5
u-edge5 = refl
u6 : R.State
u6 = F.withShutdown wait Branch.a6
u-edge6 : R.step (R.sampleDead owner) u5 ≡ just u6
u-edge6 = refl
u7 : R.State
u7 = F.withShutdown wait Branch.a7
u-edge7 : R.step (R.commitDead owner) u6 ≡ just u7
u-edge7 = refl
u8 : R.State
u8 = F.withShutdown wait Branch.a8
u-edge8 : R.step (R.finishDead owner) u7 ≡ just u8
u-edge8 = refl
u9 : R.State
u9 = F.withShutdown wait Branch.a9
u-edge9 : R.step (R.handoff owner) u8 ≡ just u9
u-edge9 = refl
u10 : R.State
u10 = F.withShutdown wait Branch.a10
u-edge10 : R.step (R.run (X.run (W.observeBufferReturn owner))) u9 ≡ just u10
u-edge10 = refl
u11 : R.State
u11 = F.withShutdown wait Branch.a11
u-edge11 : R.step (R.run (X.run (W.enterFinalizer owner))) u10 ≡ just u11
u-edge11 = refl
u12 : R.State
u12 = F.withShutdown wait Branch.a12
u-edge12 : R.step (R.run (X.run (W.cleanup owner C.takeCleanupMap))) u11 ≡ just u12
u-edge12 = refl
u13 : R.State
u13 = F.withShutdown wait Branch.a13
u-edge13 : R.step (R.run (X.run (W.cleanup owner C.selectCleanupEntry))) u12 ≡ just u13
u-edge13 = refl
u14 : R.State
u14 = F.withShutdown wait Branch.a14
u-edge14 : R.step (R.run (X.run (W.cleanup owner C.closeHandlerSocket))) u13 ≡ just u14
u-edge14 = refl
u15 : R.State
u15 = F.withShutdown wait Branch.a15
u-edge15 : R.step (R.run (X.run (W.cleanup owner C.publishCleanupMap))) u14 ≡ just u15
u-edge15 = refl
u16 : R.State
u16 = F.withShutdown wait Branch.a16
u-edge16 : R.step (R.run (X.run (W.cleanup owner C.readCleanupCounters))) u15 ≡ just u16
u-edge16 = refl
u17 : R.State
u17 = F.withShutdown wait Branch.a17
u-edge17 : R.step (R.run (X.run (W.finishCleanup owner))) u16 ≡ just u17
u-edge17 = refl
u18 : R.State
u18 = F.withShutdown wait Branch.a18
u-edge18 : R.step (R.run (X.run (W.publishAsyncResult owner))) u17 ≡ just u18
u-edge18 = refl
uActions : List R.Action
uActions = (R.beginClose owner []) ∷ (R.finishClose owner) ∷ (R.writeAsyncFailure owner) ∷ (R.beginDead owner) ∷ (R.sampleDead owner) ∷ (R.commitDead owner) ∷ (R.finishDead owner) ∷ (R.handoff owner) ∷ (R.run (X.run (W.observeBufferReturn owner))) ∷ (R.run (X.run (W.enterFinalizer owner))) ∷ (R.run (X.run (W.cleanup owner C.takeCleanupMap))) ∷ (R.run (X.run (W.cleanup owner C.selectCleanupEntry))) ∷ (R.run (X.run (W.cleanup owner C.closeHandlerSocket))) ∷ (R.run (X.run (W.cleanup owner C.publishCleanupMap))) ∷ (R.run (X.run (W.cleanup owner C.readCleanupCounters))) ∷ (R.run (X.run (W.finishCleanup owner))) ∷ (R.run (X.run (W.publishAsyncResult owner))) ∷ []
uPath : R.Executes q5 uActions u18
uPath = (R.next u-edge2 (R.next u-edge3 (R.next u-edge4 (R.next u-edge5 (R.next u-edge6 (R.next u-edge7 (R.next u-edge8 (R.next u-edge9 (R.next u-edge10 (R.next u-edge11 (R.next u-edge12 (R.next u-edge13 (R.next u-edge14 (R.next u-edge15 (R.next u-edge16 (R.next u-edge17 (R.next u-edge18 R.done)))))))))))))))))
done : R.State
done = F.withShutdown (Close.shutdownState Close.closed (ident 0 ∷ []) [] (owner ∷ [])) u18
cm-close : R.step (R.run (X.run (W.shutdownStep Close.finishClose))) u18 ≡ just done
cm-close = refl
no-premature-cm-close : R.step (R.run (X.run (W.shutdownStep Close.finishClose))) u17 ≡ nothing
no-premature-cm-close = refl
abstract
  initialized-startup-CM-shutdown : R.Executes Main.start
    (((Main.wrappedActions (Main.callerActions ++ Branch.beforePoolActions) ++ qActions) ++ uActions) ++ (R.run (X.run (W.shutdownStep Close.finishClose)) ∷ [])) done
  initialized-startup-CM-shutdown = Facts.append
    (Facts.append (Facts.append Branch.initialized-empty-pool qPath) uPath)
    (R.next cm-close R.done)
source-and-pools : Facts.Paths Main.start done
source-and-pools = Facts.exec-projects initialized-startup-CM-shutdown
physical-final-wait : ExitProof.PhysicalWait (R.base u18) (R.base done)
physical-final-wait = Facts.physical-wait u18 cm-close
actual-startup-was-never-successful : R.owner owner done ≡ just (Old.publishedFrame (S.startupState S.poolReady Branch.emptyClosed))
actual-startup-was-never-successful = refl
startup-async-result-survives-CM-wait : W.resultOf owner (R.base done) ≡ just (W.asyncException err)
startup-async-result-survives-CM-wait = refl
