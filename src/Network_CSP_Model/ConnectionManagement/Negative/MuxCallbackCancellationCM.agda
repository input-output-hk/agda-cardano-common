{-# OPTIONS --guardedness #-}

-- Initialized async delivery in a held responder completion callback and after
-- a start callback's committed STM effects. Named async observations are inputs;
-- no timer/provider progress or source implementation refinement is inferred.
module ConnectionManagement.Negative.MuxCallbackCancellationCM where

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
import ConnectionManagement.MuxHandlerExit as Exit
import ConnectionManagement.Properties.MuxHandlerExit as ExitProof
import ConnectionManagement.Negative.MuxCallbackCancellation as Held
import ConnectionManagement.Negative.MuxHandlerExitFixtures as CleanupFixtures
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
import ConnectionManagement.Negative.MuxProtocolJobs as Old
import ConnectionManagement.Negative.MuxResultMonitor as RF
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
wrapAction : M.Action → R.Action
wrapAction a = R.run (X.run (W.run (G.run a)))
wrapP : P.Action → R.Action
wrapP a = wrapAction (M.run a)
module Clean = CleanupFixtures RF.bearerClosed Old.owner Old.Prior.captured
reading wait : Close.State
reading = Close.shutdownState Close.reading (ident 0 ∷ []) [] (owner ∷ [])
wait = Close.shutdownState Close.awaitResults (ident 0 ∷ []) [] (owner ∷ [])
q0 q1 q2 q3 q4 q5 : R.State
q0 = Held.h0
q1 = F.withShutdown (Close.shutdownState Close.reading (ident 0 ∷ []) (ident 0 ∷ []) []) q0
q2 = F.withShutdown (Close.shutdownState (Close.sendReady (ident 0) owner) (ident 0 ∷ []) [] []) q0
q3 = F.withShutdown (Close.shutdownState (Close.awaitDelivery (ident 0) owner) (ident 0 ∷ []) [] []) q0
q4 = F.withShutdown reading Held.h1
q5 = F.withShutdown wait Held.h1
q-edge1 : R.step (R.run (X.run (W.shutdownStep Close.captureSnapshot))) q0 ≡ just q1
q-edge1 = refl
q-edge2 : R.step (R.run (X.run (W.shutdownStep Close.readEntry))) q1 ≡ just q2
q-edge2 = refl
q-edge3 : R.step (R.run (X.run (W.shutdownStep Close.requestCancellation))) q2 ≡ just q3
q-edge3 = refl
q-edge4 : R.step (R.deliverShutdown R.unmaskedMuxCallback Held.err) q3 ≡ just q4
q-edge4 = refl
q-edge5 : R.step (R.run (X.run (W.shutdownStep Close.finishTraversal))) q4 ≡ just q5
q-edge5 = refl
qActions : List R.Action
qActions = R.run (X.run (W.shutdownStep Close.captureSnapshot)) ∷ R.run (X.run (W.shutdownStep Close.readEntry)) ∷
  R.run (X.run (W.shutdownStep Close.requestCancellation)) ∷ R.deliverShutdown R.unmaskedMuxCallback Held.err ∷
  R.run (X.run (W.shutdownStep Close.finishTraversal)) ∷ []
qPath : R.Executes q0 qActions q5
qPath = R.next q-edge1 (R.next q-edge2 (R.next q-edge3 (R.next q-edge4 (R.next q-edge5 R.done))))
no-result-at-delivery : W.resultReady owner (R.base q4) ≡ false
no-result-at-delivery = refl
no-result-at-wait : R.step (R.run (X.run (W.shutdownStep Close.finishClose))) q5 ≡ nothing
no-result-at-wait = refl
u2 : R.State
u2 = F.withShutdown wait Held.h2
u-edge2 : R.step (R.beginClose owner (Old.j₁ ∷ Old.j₀ ∷ [])) q5 ≡ just u2
u-edge2 = refl
u3 : R.State
u3 = F.withShutdown wait Held.h3
u-edge3 : R.step (R.requestCancel owner) u2 ≡ just u3
u-edge3 = refl
u4 : R.State
u4 = F.withShutdown wait Held.h4
u-edge4 : R.step (R.deliverCancel owner) u3 ≡ just u4
u-edge4 = refl
u5 : R.State
u5 = F.withShutdown wait Held.h5
u-edge5 : R.step (R.run (X.run (W.run (G.finishChildUnwind Old.j₁)))) u4 ≡ just u5
u-edge5 = refl
u6 : R.State
u6 = F.withShutdown wait Held.h6
u-edge6 : R.step (wrapP (P.deregisterInfra owner T.demuxer)) u5 ≡ just u6
u-edge6 = refl
u7 : R.State
u7 = F.withShutdown wait Held.h7
u-edge7 : R.step (wrapP (P.asyncInfraResult owner T.demuxer)) u6 ≡ just u7
u-edge7 = refl
u8 : R.State
u8 = F.withShutdown wait Held.h8
u-edge8 : R.step (R.join owner) u7 ≡ just u8
u-edge8 = refl
u9 : R.State
u9 = F.withShutdown wait Held.h9
u-edge9 : R.step (R.requestCancel owner) u8 ≡ just u9
u-edge9 = refl
u10 : R.State
u10 = F.withShutdown wait Held.h10
u-edge10 : R.step (R.deliverCancel owner) u9 ≡ just u10
u-edge10 = refl
u11 : R.State
u11 = F.withShutdown wait Held.h11
u-edge11 : R.step (R.run (X.run (W.run (G.finishChildUnwind Old.j₀)))) u10 ≡ just u11
u-edge11 = refl
u12 : R.State
u12 = F.withShutdown wait Held.h12
u-edge12 : R.step (wrapP (P.deregisterInfra owner T.muxer)) u11 ≡ just u12
u-edge12 = refl
u13 : R.State
u13 = F.withShutdown wait Held.h13
u-edge13 : R.step (wrapP (P.asyncInfraResult owner T.muxer)) u12 ≡ just u13
u-edge13 = refl
u14 : R.State
u14 = F.withShutdown wait Held.h14
u-edge14 : R.step (R.join owner) u13 ≡ just u14
u-edge14 = refl
u15 : R.State
u15 = F.withShutdown wait Held.h15
u-edge15 : R.step (R.finishClose owner) u14 ≡ just u15
u-edge15 = refl
u16 : R.State
u16 = F.withShutdown wait Held.h16
u-edge16 : R.step (R.writeAsyncFailure owner) u15 ≡ just u16
u-edge16 = refl
u17 : R.State
u17 = F.withShutdown wait Held.h17
u-edge17 : R.step (R.beginDead owner) u16 ≡ just u17
u-edge17 = refl
u18 : R.State
u18 = F.withShutdown wait Held.h18
u-edge18 : R.step (R.sampleDead owner) u17 ≡ just u18
u-edge18 = refl
u19 : R.State
u19 = F.withShutdown wait Held.h19
u-edge19 : R.step (R.commitDead owner) u18 ≡ just u19
u-edge19 = refl
u20 : R.State
u20 = F.withShutdown wait Held.h20
u-edge20 : R.step (R.finishDead owner) u19 ≡ just u20
u-edge20 = refl
u21 : R.State
u21 = F.withShutdown wait Held.h21
u-edge21 : R.step (R.handoff owner) u20 ≡ just u21
u-edge21 = refl
uActions : List R.Action
uActions = (R.beginClose owner (Old.j₁ ∷ Old.j₀ ∷ [])) ∷ (R.requestCancel owner) ∷ (R.deliverCancel owner) ∷ (R.run (X.run (W.run (G.finishChildUnwind Old.j₁)))) ∷ (wrapP (P.deregisterInfra owner T.demuxer)) ∷ (wrapP (P.asyncInfraResult owner T.demuxer)) ∷ (R.join owner) ∷ (R.requestCancel owner) ∷ (R.deliverCancel owner) ∷ (R.run (X.run (W.run (G.finishChildUnwind Old.j₀)))) ∷ (wrapP (P.deregisterInfra owner T.muxer)) ∷ (wrapP (P.asyncInfraResult owner T.muxer)) ∷ (R.join owner) ∷ (R.finishClose owner) ∷ (R.writeAsyncFailure owner) ∷ (R.beginDead owner) ∷ (R.sampleDead owner) ∷ (R.commitDead owner) ∷ (R.finishDead owner) ∷ (R.handoff owner) ∷ []
uPath : R.Executes q5 uActions u21
uPath = R.next u-edge2 (R.next u-edge3 (R.next u-edge4 (R.next u-edge5 (R.next u-edge6 (R.next u-edge7 (R.next u-edge8 (R.next u-edge9 (R.next u-edge10 (R.next u-edge11 (R.next u-edge12 (R.next u-edge13 (R.next u-edge14 (R.next u-edge15 (R.next u-edge16 (R.next u-edge17 (R.next u-edge18 (R.next u-edge19 (R.next u-edge20 (R.next u-edge21 (R.done))))))))))))))))))))
-- Buffer exit and the captured CM finally are real remaining operations.
n0 : R.State
n0 = u21
n1 : R.State
n1 = F.withExit (W.bodyExited (W.asyncException Held.err)) n0
n-edge1 : R.step (R.run (X.run (W.observeBufferReturn owner))) n0 ≡ just n1
n-edge1 = refl
n2 : R.State
n2 = F.withWorld (Clean.world1 (F.shared n0)) (F.withExit (W.finalizing (W.asyncException Held.err)) n0)
n-edge2 : R.step (R.run (X.run (W.enterFinalizer owner))) n1 ≡ just n2
n-edge2 = refl
n3 : R.State
n3 = F.withWorld (Clean.world2 (F.shared n0)) (F.withExit (W.finalizing (W.asyncException Held.err)) n0)
n-edge3 : R.step (R.run (X.run (W.cleanup owner Cleanup.takeCleanupMap))) n2 ≡ just n3
n-edge3 = refl
n4 : R.State
n4 = F.withWorld (Clean.world3 (F.shared n0)) (F.withExit (W.finalizing (W.asyncException Held.err)) n0)
n-edge4 : R.step (R.run (X.run (W.cleanup owner Cleanup.selectCleanupEntry))) n3 ≡ just n4
n-edge4 = refl
n5 : R.State
n5 = F.withWorld (Clean.world4 (F.shared n0)) (F.withExit (W.finalizing (W.asyncException Held.err)) n0)
n-edge5 : R.step (R.run (X.run (W.cleanup owner Cleanup.closeHandlerSocket))) n4 ≡ just n5
n-edge5 = refl
n6 : R.State
n6 = F.withWorld (Clean.world5 (F.shared n0)) (F.withExit (W.finalizing (W.asyncException Held.err)) n0)
n-edge6 : R.step (R.run (X.run (W.cleanup owner Cleanup.publishCleanupMap))) n5 ≡ just n6
n-edge6 = refl
n7 : R.State
n7 = F.withWorld (Clean.world6 (F.shared n0)) (F.withExit (W.finalizing (W.asyncException Held.err)) n0)
n-edge7 : R.step (R.run (X.run (W.cleanup owner Cleanup.readCleanupCounters))) n6 ≡ just n7
n-edge7 = refl
n8 : R.State
n8 = F.withWorld (Clean.world6 (F.shared n0)) (F.withExit (W.cleanupComplete (W.asyncException Held.err) Shared.cleanupNormal) n0)
n-edge8 : R.step (R.run (X.run (W.finishCleanup owner))) n7 ≡ just n8
n-edge8 = refl
n9 : R.State
n9 = F.withWorld (Clean.world6 (F.shared n0)) (F.withExit (W.resultAvailable (W.asyncException Held.err) Shared.cleanupNormal) n0)
n-edge9 : R.step (R.run (X.run (W.publishAsyncResult owner))) n8 ≡ just n9
n-edge9 = refl
nActions : List R.Action
nActions = (R.run (X.run (W.observeBufferReturn owner))) ∷ (R.run (X.run (W.enterFinalizer owner))) ∷ (R.run (X.run (W.cleanup owner Cleanup.takeCleanupMap))) ∷ (R.run (X.run (W.cleanup owner Cleanup.selectCleanupEntry))) ∷ (R.run (X.run (W.cleanup owner Cleanup.closeHandlerSocket))) ∷ (R.run (X.run (W.cleanup owner Cleanup.publishCleanupMap))) ∷ (R.run (X.run (W.cleanup owner Cleanup.readCleanupCounters))) ∷ (R.run (X.run (W.finishCleanup owner))) ∷ (R.run (X.run (W.publishAsyncResult owner))) ∷ []
nPath : R.Executes n0 nActions n9
nPath = R.next n-edge1 (R.next n-edge2 (R.next n-edge3 (R.next n-edge4 (R.next n-edge5 (R.next n-edge6 (R.next n-edge7 (R.next n-edge8 (R.next n-edge9 (R.done)))))))))
closed : R.State
closed = F.withShutdown (Close.shutdownState Close.closed (ident 0 ∷ []) [] (owner ∷ [])) n9
close-edge : R.step (R.run (X.run (W.shutdownStep Close.finishClose))) n9 ≡ just closed
close-edge = refl
prefixActions : List R.Action
prefixActions = (Prior.wrappedActions Old.startActions ++ Held.prefixActions) ++ map Held.wrapAction Held.heldActions
allActions : List R.Action
allActions = prefixActions ++ (qActions ++ (uActions ++ (nActions ++ (R.run (X.run (W.shutdownStep Close.finishClose)) ∷ []))))
abstract
  initialized-callback-CM-result : R.Executes Prior.start allActions closed
  initialized-callback-CM-result = Facts.append Held.initialized-held
    (Facts.append qPath (Facts.append uPath (Facts.append nPath (R.next close-edge R.done))))
actual-physical-wait : ExitFacts.PhysicalWait (R.base n9) (R.base closed)
actual-physical-wait = Facts.physical-wait n9 close-edge
no-result-at-buffer-exit : W.resultReady owner (R.base n1) ≡ false
no-result-at-buffer-exit = refl
no-result-at-cleanup-end : W.resultReady owner (R.base n8) ≡ false
no-result-at-cleanup-end = refl
actual-parent-result : W.resultReady owner (R.base n9) ≡ true
actual-parent-result = refl
initialized-captures : Capture.Captures (R.source closed)
initialized-captures = Facts.from-initial-captures Held.actual-initializer initialized-callback-CM-result
initialized-supply : Supply.Valid (R.source closed)
initialized-supply = Facts.from-initial-supply Held.actual-initializer Old.Prior.initial-bounds initialized-callback-CM-result
source-and-pool-paths : Facts.Paths Prior.start closed
source-and-pool-paths = Facts.exec-projects initialized-callback-CM-result
