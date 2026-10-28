{-# OPTIONS --guardedness #-}

-- Actual initialized exit paths; flat source snapshots retain the captured CM
-- finalizer and keep buffer/policy observations explicit. No replay claim.
module ConnectionManagement.Negative.MuxHandlerExit where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (local)
open import ConnectionManagement.Store using (put; lookup)
import ConnectionManagement.MuxHandlerExit as Exit
import ConnectionManagement.Properties.MuxHandlerExit as ExitFacts
import ConnectionManagement.Negative.MuxGroupShutdown as F
import ConnectionManagement.Negative.MuxResultMonitor as RF
import ConnectionManagement.Negative.MuxProtocolJobs as Old
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.State as S
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as Machine
import ConnectionManagement.Rules.Cleanup as C
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.HandlerLifecycle as Life
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
private
  module W = Exit RF.bearerClosed
private
  module Facts = ExitFacts RF.bearerClosed
private
  module G = W.G
private
  module Pool = W.Pool
private
  module M = G.M
private
  module P = G.P
import ConnectionManagement.Rules.MuxJobTypes as T
owner : WorkerId
owner = Old.owner
err : ErrorId
err = Old.err
wrap : G.State → W.State
wrap g = W.handlerExitState g []
open Facts public using (allSafe; lift-step; lift-path; append)
actionsOf : ∀ {g actions g′} → G.Executes g actions g′ → List G.Action
actionsOf {actions = actions} path = actions
actual-initializer : W.initial (O.initial Old.F.start) ≡ just (wrap (F.wrap (RF.wrap Old.b0)))
actual-initializer = refl
import ConnectionManagement.Negative.MuxHandlerExitFixtures as Fixtures
module X = Fixtures RF.bearerClosed owner Old.Prior.captured
open X public using (at; plain; world0; world1; world2; world3; world4; world5; world6; table; lease)
normal0 : W.State
normal0 = wrap F.normal30
normal1 : W.State
normal1 = plain F.normal30 (W.bufferScope G.normalExit)
normal2 : W.State
normal2 = plain F.normal30 (W.bodyExited W.returned)
normal3 : W.State
normal3 = at F.normal30 (W.finalizing W.returned) (world1 (world0 F.normal30))
normal4 : W.State
normal4 = at F.normal30 (W.finalizing W.returned) (world2 (world0 F.normal30))
normal5 : W.State
normal5 = at F.normal30 (W.finalizing W.returned) (world3 (world0 F.normal30))
normal6 : W.State
normal6 = at F.normal30 (W.finalizing W.returned) (world4 (world0 F.normal30))
normal7 : W.State
normal7 = at F.normal30 (W.finalizing W.returned) (world5 (world0 F.normal30))
normal8 : W.State
normal8 = at F.normal30 (W.finalizing W.returned) (world6 (world0 F.normal30))
normal9 : W.State
normal9 = at F.normal30 (W.cleanupComplete W.returned S.cleanupNormal) (world6 (world0 F.normal30))
normal10 : W.State
normal10 = at F.normal30 (W.resultAvailable W.returned S.cleanupNormal) (world6 (world0 F.normal30))
normal-edge1 : W.step (W.beginExit owner) normal0 ≡ just normal1
normal-edge1 = refl
normal-edge2 : W.step (W.observeBufferReturn owner) normal1 ≡ just normal2
normal-edge2 = refl
normal-edge3 : W.step (W.enterFinalizer owner) normal2 ≡ just normal3
normal-edge3 = refl
normal-edge4 : W.step (W.cleanup owner C.takeCleanupMap) normal3 ≡ just normal4
normal-edge4 = refl
normal-edge5 : W.step (W.cleanup owner C.selectCleanupEntry) normal4 ≡ just normal5
normal-edge5 = refl
normal-edge6 : W.step (W.cleanup owner C.closeHandlerSocket) normal5 ≡ just normal6
normal-edge6 = refl
normal-edge7 : W.step (W.cleanup owner C.publishCleanupMap) normal6 ≡ just normal7
normal-edge7 = refl
normal-edge8 : W.step (W.cleanup owner C.readCleanupCounters) normal7 ≡ just normal8
normal-edge8 = refl
normal-edge9 : W.step (W.finishCleanup owner) normal8 ≡ just normal9
normal-edge9 = refl
normal-edge10 : W.step (W.publishAsyncResult owner) normal9 ≡ just normal10
normal-edge10 = refl
normalActions : List W.Action
normalActions = (W.beginExit owner) ∷ (W.observeBufferReturn owner) ∷ (W.enterFinalizer owner) ∷ (W.cleanup owner C.takeCleanupMap) ∷ (W.cleanup owner C.selectCleanupEntry) ∷ (W.cleanup owner C.closeHandlerSocket) ∷ (W.cleanup owner C.publishCleanupMap) ∷ (W.cleanup owner C.readCleanupCounters) ∷ (W.finishCleanup owner) ∷ (W.publishAsyncResult owner) ∷ []
normalPath : W.Executes normal0 normalActions normal10
normalPath = (W.next normal-edge1 (W.next normal-edge2 (W.next normal-edge3 (W.next normal-edge4 (W.next normal-edge5 (W.next normal-edge6 (W.next normal-edge7 (W.next normal-edge8 (W.next normal-edge9 (W.next normal-edge10 W.done))))))))))
abstract
  initialized-normal : W.Executes (wrap (F.wrap (RF.wrap Old.b0)))
    (map W.run (actionsOf F.initialized-normal-close) ++ normalActions) normal10
  initialized-normal = append (lift-path F.initialized-normal-close refl) normalPath
async0 : W.State
async0 = wrap F.abortGroup25
async1 : W.State
async1 = plain F.abortGroup25 (W.bufferScope (G.asyncExit err))
async2 : W.State
async2 = plain F.abortGroup25 (W.bodyExited (W.asyncException err))
async3 : W.State
async3 = at F.abortGroup25 (W.finalizing (W.asyncException err)) (world1 (world0 F.abortGroup25))
async4 : W.State
async4 = at F.abortGroup25 (W.finalizing (W.asyncException err)) (world2 (world0 F.abortGroup25))
async5 : W.State
async5 = at F.abortGroup25 (W.finalizing (W.asyncException err)) (world3 (world0 F.abortGroup25))
async6 : W.State
async6 = at F.abortGroup25 (W.finalizing (W.asyncException err)) (world4 (world0 F.abortGroup25))
async7 : W.State
async7 = at F.abortGroup25 (W.finalizing (W.asyncException err)) (world5 (world0 F.abortGroup25))
async8 : W.State
async8 = at F.abortGroup25 (W.finalizing (W.asyncException err)) (world6 (world0 F.abortGroup25))
async9 : W.State
async9 = at F.abortGroup25 (W.cleanupComplete (W.asyncException err) S.cleanupNormal) (world6 (world0 F.abortGroup25))
async10 : W.State
async10 = at F.abortGroup25 (W.resultAvailable (W.asyncException err) S.cleanupNormal) (world6 (world0 F.abortGroup25))
async-edge1 : W.step (W.beginExit owner) async0 ≡ just async1
async-edge1 = refl
async-edge2 : W.step (W.observeBufferReturn owner) async1 ≡ just async2
async-edge2 = refl
async-edge3 : W.step (W.enterFinalizer owner) async2 ≡ just async3
async-edge3 = refl
async-edge4 : W.step (W.cleanup owner C.takeCleanupMap) async3 ≡ just async4
async-edge4 = refl
async-edge5 : W.step (W.cleanup owner C.selectCleanupEntry) async4 ≡ just async5
async-edge5 = refl
async-edge6 : W.step (W.cleanup owner C.closeHandlerSocket) async5 ≡ just async6
async-edge6 = refl
async-edge7 : W.step (W.cleanup owner C.publishCleanupMap) async6 ≡ just async7
async-edge7 = refl
async-edge8 : W.step (W.cleanup owner C.readCleanupCounters) async7 ≡ just async8
async-edge8 = refl
async-edge9 : W.step (W.finishCleanup owner) async8 ≡ just async9
async-edge9 = refl
async-edge10 : W.step (W.publishAsyncResult owner) async9 ≡ just async10
async-edge10 = refl
asyncActions : List W.Action
asyncActions = (W.beginExit owner) ∷ (W.observeBufferReturn owner) ∷ (W.enterFinalizer owner) ∷ (W.cleanup owner C.takeCleanupMap) ∷ (W.cleanup owner C.selectCleanupEntry) ∷ (W.cleanup owner C.closeHandlerSocket) ∷ (W.cleanup owner C.publishCleanupMap) ∷ (W.cleanup owner C.readCleanupCounters) ∷ (W.finishCleanup owner) ∷ (W.publishAsyncResult owner) ∷ []
asyncPath : W.Executes async0 asyncActions async10
asyncPath = (W.next async-edge1 (W.next async-edge2 (W.next async-edge3 (W.next async-edge4 (W.next async-edge5 (W.next async-edge6 (W.next async-edge7 (W.next async-edge8 (W.next async-edge9 (W.next async-edge10 W.done))))))))))
abstract
  initialized-async : W.Executes (wrap (F.wrap (RF.wrap Old.b0)))
    (map W.run (actionsOf F.initialized-abortGroup) ++ asyncActions) async10
  initialized-async = append (lift-path F.initialized-abortGroup refl) asyncPath

-- A buffer-provider exception replaces the mux outcome after pool closure.
sync0 sync1 peer0 peer1 peer2 node0 node1 node2 node3 : W.State
sync0 = plain F.normal30 (W.classifying err)
sync1 = plain F.normal30 (W.errorTracing err Life.shutdownPeer)
peer0 = plain F.normal30 (W.peerRethrow err)
peer1 = plain F.normal30 (W.bodyExited (W.peerException err))
peer2 = at F.normal30 (W.finalizing (W.peerException err)) (world1 (world0 F.normal30))
node0 = plain F.normal30 (W.errorTracing err Life.shutdownNode)
node1 = plain F.normal30 (W.nodeDelivery err)
node2 = plain F.normal30 (W.nodeRethrow err)
node3 = plain F.normal30 (W.bodyExited (W.syncException err))
buffer-replacement : W.step (W.observeBufferException owner (G.failedExit err)) normal1 ≡ just sync0
buffer-replacement = refl
peer-policy : W.step (W.choosePolicy owner Life.shutdownPeer) sync0 ≡ just sync1
peer-policy = refl
peer-trace : W.step (W.observeErrorTrace owner) sync1 ≡ just peer0
peer-trace = refl
peer-wrap-rethrow : W.step (W.rethrow owner) peer0 ≡ just peer1
peer-wrap-rethrow = refl
peer-enters-real-finalizer : W.step (W.enterFinalizer owner) peer1 ≡ just peer2
peer-enters-real-finalizer = refl
node-policy : W.step (W.choosePolicy owner Life.shutdownNode) sync0 ≡ just node0
node-policy = refl
node-trace : W.step (W.observeErrorTrace owner) node0 ≡ just node1
node-trace = refl
node-delivery : W.step (W.observeNodeDelivery owner) node1 ≡ just node2
node-delivery = refl
node-original-rethrow : W.step (W.rethrow owner) node2 ≡ just node3
node-original-rethrow = refl
no-node-rethrow-before-delivery : W.step (W.rethrow owner) node1 ≡ nothing
no-node-rethrow-before-delivery = refl
no-classify-async : W.step (W.choosePolicy owner Life.shutdownNode) async2 ≡ nothing
no-classify-async = refl
no-finalizer-before-buffer : W.step (W.enterFinalizer owner) normal1 ≡ nothing
no-finalizer-before-buffer = refl
no-result-before-cleanup : W.step (W.publishAsyncResult owner) normal3 ≡ nothing
no-result-before-cleanup = refl
no-result-at-cleanupDone : W.resultReady owner normal8 ≡ false
no-result-at-cleanupDone = refl
physical-result-after-explicit-publication : W.resultReady owner normal10 ≡ true
physical-result-after-explicit-publication = refl
no-exception-to-success-observation : W.step (W.observeBufferException owner G.normalExit) async1 ≡ nothing
no-exception-to-success-observation = refl
pool-local-done-is-not-parent-result : W.resultReady owner normal0 ≡ false
pool-local-done-is-not-parent-result = refl
no-cleanup-with-active-pool : W.step (W.beginExit owner) (wrap F.normal7) ≡ nothing
no-cleanup-with-active-pool = refl
no-raw-finalizer : W.step (W.run (G.run (G.M.run (G.P.run (G.U.run (B.handler (H.enterFinalizer owner))))))) normal1 ≡ nothing
no-raw-finalizer = refl
cleanup-overrides-normal : W.effectiveResult W.returned (S.cleanupError err) (just (G.failedExit err)) ≡ just (W.syncException err)
cleanup-overrides-normal = refl
cleanup-overrides-async : W.effectiveResult (W.asyncException err) (S.cleanupError err) (just (G.failedExit err)) ≡ just (W.syncException err)
cleanup-overrides-async = refl
cleanup-overrides-peer-wrapper : W.effectiveResult (W.peerException err) (S.cleanupError err) (just (G.failedExit err)) ≡ just (W.syncException err)
cleanup-overrides-peer-wrapper = refl
