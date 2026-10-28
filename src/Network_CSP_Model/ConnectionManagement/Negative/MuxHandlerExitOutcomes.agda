{-# OPTIONS --guardedness #-}

-- Actual initialized exit paths; flat source snapshots retain the captured CM
-- finalizer and keep buffer/policy observations explicit. No replay claim.
module ConnectionManagement.Negative.MuxHandlerExitOutcomes where

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
module W = Exit RF.bearerClosed
module Facts = ExitFacts RF.bearerClosed
module G = W.G
module Pool = W.Pool
module M = G.M
module P = G.P
import ConnectionManagement.Rules.MuxJobTypes as T
open import ConnectionManagement.Negative.MuxHandlerExit
faulted : W.State → W.State
faulted s = record s { exits = (owner , W.exitFrame Old.Prior.captured
  (case lookup owner (W.exits s) of λ { (just f) → W.phase f; nothing → W.bodyExited W.returned })
  (just (G.failedExit err))) ∷ [] }

-- Socket-close failure restores the captured map before the Async result.
failedWorld1 failedWorld2 : S.State
failedWorld1 = record (world3 (world0 F.normal30))
  { sockets = put Old.Fixture.sock (S.closeUncertain err) (S.sockets (world0 F.normal30))
  ; cleanups = (owner , S.cleanupRestore lease err) ∷ [] }
failedWorld2 = record failedWorld1
  { cm = record (S.cm failedWorld1) { mapCell = S.full table }
  ; cleanups = (owner , S.cleanupDone (S.cleanupError err)) ∷ [] }
failed1 failed2 failed3 failed4 : W.State
failed1 = faulted (at F.normal30 (W.finalizing W.returned) failedWorld1)
failed2 = faulted (at F.normal30 (W.finalizing W.returned) failedWorld2)
failed3 = faulted (at F.normal30 (W.cleanupComplete W.returned (S.cleanupError err)) failedWorld2)
failed4 = faulted (at F.normal30 (W.resultAvailable W.returned (S.cleanupError err)) failedWorld2)
fail-close : W.step (W.cleanup owner (C.failSocketClose err)) normal5 ≡ just failed1
fail-close = refl
restore-map : W.step (W.cleanup owner C.restoreCleanupMap) failed1 ≡ just failed2
restore-map = refl
finish-failed-cleanup : W.step (W.finishCleanup owner) failed2 ≡ just failed3
finish-failed-cleanup = refl
publish-failed-result : W.step (W.publishAsyncResult owner) failed3 ≡ just failed4
publish-failed-result = refl
no-publish-before-map-restoration : W.step (W.publishAsyncResult owner) failed1 ≡ nothing
no-publish-before-map-restoration = refl
no-repeat-result : W.step (W.publishAsyncResult owner) normal10 ≡ nothing
no-repeat-result = refl

-- Both policy outcomes run the same real CM finalizer with different bodies.
cleanupSuffixActions : List W.Action
cleanupSuffixActions = W.cleanup owner C.takeCleanupMap ∷ W.cleanup owner C.selectCleanupEntry ∷
  W.cleanup owner C.closeHandlerSocket ∷ W.cleanup owner C.publishCleanupMap ∷
  W.cleanup owner C.readCleanupCounters ∷ W.finishCleanup owner ∷ W.publishAsyncResult owner ∷ []
cleanupSuffix : ∀ result → W.Executes (at F.normal30 (W.finalizing result) (world1 (world0 F.normal30)))
  cleanupSuffixActions (at F.normal30 (W.resultAvailable result S.cleanupNormal) (world6 (world0 F.normal30)))
cleanupSuffix result = (W.next {s₁ = at F.normal30 (W.finalizing result) (world2 (world0 F.normal30))} refl
  (W.next {s₁ = at F.normal30 (W.finalizing result) (world3 (world0 F.normal30))} refl
  (W.next {s₁ = at F.normal30 (W.finalizing result) (world4 (world0 F.normal30))} refl
  (W.next {s₁ = at F.normal30 (W.finalizing result) (world5 (world0 F.normal30))} refl
  (W.next {s₁ = at F.normal30 (W.finalizing result) (world6 (world0 F.normal30))} refl
  (W.next {s₁ = at F.normal30 (W.cleanupComplete result S.cleanupNormal) (world6 (world0 F.normal30))} refl
  (W.next {s₁ = at F.normal30 (W.resultAvailable result S.cleanupNormal) (world6 (world0 F.normal30))} refl W.done)))))))
peerActions : List W.Action
peerActions = W.observeBufferException owner (G.failedExit err) ∷ W.choosePolicy owner Life.shutdownPeer ∷
  W.observeErrorTrace owner ∷ W.rethrow owner ∷ W.enterFinalizer owner ∷ []
peerPath : W.Executes normal1 peerActions peer2
peerPath = W.next buffer-replacement (W.next peer-policy (W.next peer-trace (W.next peer-wrap-rethrow (W.next peer-enters-real-finalizer W.done))))
nodeFinal : W.State
nodeFinal = at F.normal30 (W.finalizing (W.syncException err)) (world1 (world0 F.normal30))
node-enters-finalizer : W.step (W.enterFinalizer owner) node3 ≡ just nodeFinal
node-enters-finalizer = refl
nodeActions : List W.Action
nodeActions = W.observeBufferException owner (G.failedExit err) ∷ W.choosePolicy owner Life.shutdownNode ∷
  W.observeErrorTrace owner ∷ W.observeNodeDelivery owner ∷ W.rethrow owner ∷ W.enterFinalizer owner ∷ []
nodePath : W.Executes normal1 nodeActions nodeFinal
nodePath = W.next buffer-replacement (W.next node-policy (W.next node-trace (W.next node-delivery (W.next node-original-rethrow (W.next node-enters-finalizer W.done)))))
abstract
  initialized-buffer-entry : W.Executes (wrap (F.wrap (RF.wrap Old.b0)))
    (map W.run (actionsOf F.initialized-normal-close) ++ (W.beginExit owner ∷ [])) normal1
  initialized-buffer-entry = append (lift-path F.initialized-normal-close refl) (W.next normal-edge1 W.done)
  initialized-peer-result : W.Executes (wrap (F.wrap (RF.wrap Old.b0)))
    ((map W.run (actionsOf F.initialized-normal-close) ++ (W.beginExit owner ∷ [])) ++ peerActions ++ cleanupSuffixActions)
    (at F.normal30 (W.resultAvailable (W.peerException err) S.cleanupNormal) (world6 (world0 F.normal30)))
  initialized-peer-result = append initialized-buffer-entry (append peerPath (cleanupSuffix (W.peerException err)))
  initialized-node-result : W.Executes (wrap (F.wrap (RF.wrap Old.b0)))
    ((map W.run (actionsOf F.initialized-normal-close) ++ (W.beginExit owner ∷ [])) ++ nodeActions ++ cleanupSuffixActions)
    (at F.normal30 (W.resultAvailable (W.syncException err) S.cleanupNormal) (world6 (world0 F.normal30)))
  initialized-node-result = append initialized-buffer-entry (append nodePath (cleanupSuffix (W.syncException err)))
  initialized-failed-cleanup : W.Executes (wrap (F.wrap (RF.wrap Old.b0)))
    ((map W.run (actionsOf F.initialized-normal-close) ++
      (W.beginExit owner ∷ W.observeBufferReturn owner ∷ W.enterFinalizer owner ∷
       W.cleanup owner C.takeCleanupMap ∷ W.cleanup owner C.selectCleanupEntry ∷ [])) ++
      (W.cleanup owner (C.failSocketClose err) ∷ W.cleanup owner C.restoreCleanupMap ∷
       W.finishCleanup owner ∷ W.publishAsyncResult owner ∷ [])) failed4
  initialized-failed-cleanup = append
    (append (lift-path F.initialized-normal-close refl)
      (W.next normal-edge1 (W.next normal-edge2 (W.next normal-edge3 (W.next normal-edge4 (W.next normal-edge5 W.done))))))
    (W.next fail-close (W.next restore-map (W.next finish-failed-cleanup (W.next publish-failed-result W.done))))

normal-publication : Facts.Publication owner normal9 normal10
normal-publication = Facts.publication-observation owner normal9 normal-edge10
failed-publication : Facts.Publication owner failed3 failed4
failed-publication = Facts.publication-observation owner failed3 publish-failed-result
normal-projection : Facts.Paths (wrap (F.wrap (RF.wrap Old.b0))) normal10
normal-projection = Facts.exec-projects initialized-normal
normal-captures : Capture.Captures (W.source normal10)
normal-captures = Facts.from-initial-captures actual-initializer initialized-normal

normal-parent-value : W.resultOf owner normal10 ≡ just W.returned
normal-parent-value = refl
async-parent-value : W.resultOf owner async10 ≡ just (W.asyncException err)
async-parent-value = refl
failed-finalizer-parent-value : W.resultOf owner failed4 ≡ just (W.syncException err)
failed-finalizer-parent-value = refl
no-parent-value-at-cleanupDone : W.resultOf owner normal8 ≡ nothing
no-parent-value-at-cleanupDone = refl
async-finalizer-keeps-exception-class : W.effectiveResult (W.peerException err) (S.cleanupError err)
  (just (G.asyncExit err)) ≡ just (W.asyncException err)
async-finalizer-keeps-exception-class = refl
unclassified-finalizer-cannot-complete : W.effectiveResult W.returned (S.cleanupError err) nothing ≡ nothing
unclassified-finalizer-cannot-complete = refl
