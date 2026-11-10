{-# OPTIONS --guardedness #-}

-- Actual permitted peer actions leave the shared cleanup store unchanged. Raw
-- core aliases are excluded by the shared dispatcher (the permission is the one
-- of InboundOriginPeers); the proof adapts that module's admission-table cases.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.CleanupPeers (io : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Function using (case_of_)
open import ConnectionManagement.Domain using (WorkerId; JobId)
open import ConnectionManagement.Store using (Store; lookup)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.IGRegistration
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Rules.ProductionPolicy as Policy
import ConnectionManagement.Properties.CallerCancellation as Writer
import ConnectionManagement.Properties.CleanupWriters as Core
import ConnectionManagement.Properties.InboundOriginPeers as Origin
import ConnectionManagement.Properties.PeerJobInvariant as JobLift
import ConnectionManagement.Properties.SubsystemInvariant as SubLift
import ConnectionManagement.Properties.PeerSupervisionSupply as PeerLift
import ConnectionManagement.Properties.GovernorPoolSupply as GovernorSupply
import ConnectionManagement.PeerSupervision as Supervision
module PS = Supervision io
module GP = PS.GP
module Pool = GP.Pool
private module Gov = GovernorSupply io using (restore-cm)
private module Lift = PeerLift io using (View; module StepLift)

-- The shared frontend's permission, which rejects every raw peer-side core alias.
open Origin io using (SubAllowed; GovernorAllowed; Allowed)

module For (original : Store WorkerId S.CleanupPC) where
 Q : A.Runtime → S.State → Set
 Q runtime world = S.cleanups world ≡ original
 Observe : CM.Configuration → Set
 Observe c = Q (CM.acquiring c) (M.world (CM.core c))

 -- Job execution starts CM calls, without writing cleanup records.
 begin-acquire : ∀ worker request c {next} → CM.advance (CM.beginAcquire worker request) c ≡ just next → Observe c → Observe next
 begin-acquire worker request c actual valid with lookup worker (CM.acquiring c) | lookup worker (CM.releasing c)
 ... | nothing | nothing = case just-injective actual of λ { refl → valid }
 ... | just _ | _ = case actual of λ ()
 ... | nothing | just _ = case actual of λ ()
 begin-release : ∀ worker key c {next} → CM.advance (CM.beginRelease worker key) c ≡ just next → Observe c → Observe next
 begin-release worker key c actual valid with lookup worker (CM.acquiring c) | lookup worker (CM.releasing c)
 ... | nothing | nothing = case just-injective actual of λ { refl → valid }
 ... | just _ | _ = case actual of λ ()
 ... | nothing | just _ = case actual of λ ()
 private module Jobs = JobLift.BeginLift Q begin-acquire begin-release using (step-preserves)

 -- This monitor operation can change IG/CM entries but not cleanup records.
 monitor-preserves : ∀ mid c {next} → CM.advance (CM.inbound (M.igStep (ConnectionManagement.Rules.IGRegistration.monitorCompletion mid))) c ≡ just next → Observe c → Observe next
 monitor-preserves mid c actual valid with M.advance
   (M.igStep (ConnectionManagement.Rules.IGRegistration.monitorCompletion mid)) (CM.core c) in advanced
 ... | nothing = case actual of λ ()
 ... | just next = case just-injective actual of λ { refl → trans
   (Core.machine-same (M.igStep (ConnectionManagement.Rules.IGRegistration.monitorCompletion mid)) (CM.core c) advanced tt) valid }
 private
  module RawSub = SubLift.StepLift Q Jobs.step-preserves monitor-preserves (λ _ → ⊥) (λ action c ()) using (Allowed; advance-preserves)
 sub-permission : ∀ action → SubAllowed action → RawSub.Allowed action
 sub-permission (Sub.core action) ()
 sub-permission Sub.publishPublicState _ = tt
 sub-permission (Sub.sampleTime _) _ = tt
 sub-permission (Sub.applyAt _) _ = tt
 sub-permission (Sub.setTargets _) _ = tt
 sub-permission (Sub.selectMonitor _) _ = tt
 sub-permission Sub.selectCompletion _ = tt
 sub-permission Sub.selectTargets _ = tt
 sub-permission Sub.selectWakeup _ = tt
 sub-permission Sub.registerWakeup _ = tt
 sub-permission Sub.expireWakeup _ = tt
 sub-permission Sub.cancelWakeup _ = tt
 sub-permission Sub.publishCounters _ = tt
 sub-permission Sub.traceSelection _ = tt
 sub-permission (Sub.selectPolicy _) _ = tt
 sub-permission (Sub.forkJob _ _ _) _ = tt
 sub-permission Sub.registerJob _ = tt
 sub-permission Sub.finishLaunch _ = tt
 sub-permission (Sub.jobStep _ _) _ = tt
 sub-permission (Sub.enqueueCompletion _ _) _ = tt
 sub-permission (Sub.deregisterJob _) _ = tt
 sub-permission (Sub.protocolResult _ _ _) _ = tt
 sub-permission (Sub.publishInitiatorResult _ _) _ = tt
 sub-permission (Sub.pollPeer _ _) _ = tt
 sub-permission (Sub.monitorStep _ _) _ = tt
 sub-permission (Sub.monitorFinished _) _ = tt
 sub-permission (Sub.observeInitiatorFailure _) _ = tt

 Valid : GP.State → Set
 Valid s = Observe (GP.cm s)
 raw-preserves : ∀ action s {next} → SubAllowed action → GP.Production.step (Policy.dispatch action) (GP.source s) ≡ just next →
   Valid s → Q (CM.acquiring (J.cm (Sub.world (Policy.machine next)))) (M.world (CM.core (J.cm (Sub.world (Policy.machine next)))))
 raw-preserves action s permission actual valid with GP.Production.step-projects (Policy.dispatch action) (GP.source s) actual
 ... | Sub.next stepped Sub.done = RawSub.advance-preserves action (GP.machine s) (sub-permission action permission) stepped valid

 -- Detached cleanup uses an actual acquisition writer; only its cleanup
 -- projection is unchanged, not the entire shared world.
 cleanup-law : ∀ action frame c {nextFrame next} → Cancel.step action frame c ≡ just (nextFrame , next) → Observe c → Observe next
 cleanup-law action frame c actual valid with Writer.step-writer action frame c actual
 ... | Writer.writer active activeAfter world before source frameEq configurationEq = trans
   (cong (λ configuration → S.cleanups (M.world (CM.core configuration))) configurationEq)
   (trans (Core.acquire-cleanups (Cancel.caller frame) (M.responder (CM.core c)) (Cancel.acquireAction action) active (M.world (CM.core c)) source) valid)
 start-law : ∀ worker err context c {frame next} → Cancel.start worker err context c ≡ just (frame , next) → Observe c → Observe next
 start-law worker err context c actual valid = trans
   (cong (λ core → S.cleanups (M.world core)) (Writer.start-core worker err context c actual)) valid
 delivery-valid : ∀ blocked err s {s′} → GP.deliver blocked err s ≡ just s′ → Valid s → Valid s′
 delivery-valid blocked err s eq valid with Pool.phase (GP.pool s)
 ... | Pool.cancelPending j with lookup j (Sub.jobs (GP.machine s)) | Pool.step Pool.deliverCancel (GP.pool s)
 ...   | just jf | just p′ with Cancel.start (J.caller (Sub.execution jf)) err
     (GP.deliveryContext blocked (GP.region (J.caller (Sub.execution jf)) s)) (GP.cm s) in started
 ...     | just (f , c′) = case just-injective eq of λ { refl →
   start-law (J.caller (Sub.execution jf)) err
     (GP.deliveryContext blocked (GP.region (J.caller (Sub.execution jf)) s)) (GP.cm s) started valid }
 ...     | nothing = case eq of λ ()
 delivery-valid blocked err s eq valid | Pool.cancelPending j | nothing | _ = case eq of λ ()
 delivery-valid blocked err s eq valid | Pool.cancelPending j | just jf | nothing = case eq of λ ()
 delivery-valid blocked err s eq valid | Pool.openPool = case eq of λ ()
 delivery-valid blocked err s eq valid | Pool.closing = case eq of λ ()
 delivery-valid blocked err s eq valid | Pool.closedPool = case eq of λ ()
 delivery-valid blocked err s eq valid | Pool.joinPending j = case eq of λ ()

 restore-valid : ∀ f s → Valid s → Valid (record s { source = record (GP.source s) { machine = GP.restoreCold f (GP.machine s) } })
 restore-valid f s valid = subst Observe (sym (Gov.restore-cm f (GP.machine s))) valid

 step-preserves : ∀ action s {s′} → GovernorAllowed action → GP.step action s ≡ just s′ → Valid s → Valid s′
 step-preserves (GP.run action) s permission eq valid with GP.normalPool action s | GP.Production.step (Policy.dispatch action) (GP.source s) in sourceStep
 ... | just p′ | just source′ with GP.noteReturn action (Policy.machine source′) p′
 ...   | just p″ = case just-injective eq of λ { refl → raw-preserves action s permission sourceStep valid }
 ...   | nothing = case eq of λ ()
 step-preserves (GP.run action) s permission eq valid | nothing | _ = case eq of λ ()
 step-preserves (GP.run action) s permission eq valid | just p′ | nothing = case eq of λ ()
 step-preserves (GP.cleanup j action) s permission eq valid with lookup j (GP.unwinding s)
 ... | nothing = case eq of λ ()
 ... | just f with Cancel.step action f (GP.cm s) in cleaned
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , c′) = case just-injective eq of λ { refl → cleanup-law action f (GP.cm s) cleaned valid }
 step-preserves (GP.deliverCancellation err) s permission eq valid = delivery-valid false err s eq valid
 step-preserves (GP.deliverOpenCancellation err) s permission eq valid = delivery-valid true err s eq valid
 step-preserves (GP.handoff w) s permission eq valid with GP.region w s | lookup w (CM.acquiring (GP.cm s))
 ... | Cancel.forkedBeforeHandoff | just f with A.pc f
 ...   | A.connectedCommit _ _ _ = case just-injective eq of λ { refl → valid }
 step-preserves (GP.handoff w) s permission eq valid | Cancel.forkedBeforeHandoff | just f | A.selecting = case eq of λ ()
 step-preserves (GP.handoff w) s permission eq valid | Cancel.forkedBeforeHandoff | just f | (A.count next) = case eq of λ ()
 step-preserves (GP.handoff w) s permission eq valid | Cancel.forkedBeforeHandoff | just f | (A.allocatePromise e) = case eq of λ ()
 step-preserves (GP.handoff w) s permission eq valid | Cancel.forkedBeforeHandoff | just f | (A.openSocket e pid) = case eq of λ ()
 step-preserves (GP.handoff w) s permission eq valid | Cancel.forkedBeforeHandoff | just f | (A.configureSocket e pid) = case eq of λ ()
 step-preserves (GP.handoff w) s permission eq valid | Cancel.forkedBeforeHandoff | just f | (A.bindSocket e pid) = case eq of λ ()
 step-preserves (GP.handoff w) s permission eq valid | Cancel.forkedBeforeHandoff | just f | (A.connectSocket e pid) = case eq of λ ()
 step-preserves (GP.handoff w) s permission eq valid | Cancel.forkedBeforeHandoff | just f | (A.localAddress e pid) = case eq of λ ()
 step-preserves (GP.handoff w) s permission eq valid | Cancel.forkedBeforeHandoff | just f | (A.updateAddress e pid key) = case eq of λ ()
 step-preserves (GP.handoff w) s permission eq valid | Cancel.forkedBeforeHandoff | just f | (A.forkHandler e pid key) = case eq of λ ()
 step-preserves (GP.handoff w) s permission eq valid | Cancel.forkedBeforeHandoff | just f | (A.awaitResult e pid key) = case eq of λ ()
 step-preserves (GP.handoff w) s permission eq valid | Cancel.forkedBeforeHandoff | just f | (A.commitResult e key result) = case eq of λ ()
 step-preserves (GP.handoff w) s permission eq valid | Cancel.forkedBeforeHandoff | just f | (A.waitingInbound e key) = case eq of λ ()
 step-preserves (GP.handoff w) s permission eq valid | Cancel.forkedBeforeHandoff | just f | (A.closeError e err) = case eq of λ ()
 step-preserves (GP.handoff w) s permission eq valid | Cancel.forkedBeforeHandoff | just f | (A.removeError e err) = case eq of λ ()
 step-preserves (GP.handoff w) s permission eq valid | Cancel.forkedBeforeHandoff | just f | (A.complete result) = case eq of λ ()
 step-preserves (GP.handoff w) s permission eq valid | Cancel.forkedBeforeHandoff | nothing = case eq of λ ()
 step-preserves (GP.handoff w) s permission eq valid | Cancel.ordinary | _ = case eq of λ ()
 step-preserves (GP.handoff w) s permission eq valid | Cancel.protectedCleanup | _ = case eq of λ ()
 step-preserves (GP.handoff w) s permission eq valid | Cancel.interruptibleOpen | _ = case eq of λ ()
 step-preserves (GP.beginClose order) s permission eq valid with Pool.step (Pool.beginClose order) (GP.pool s) in advanced
 ... | nothing = case eq of λ ()
 ... | just p′ = case just-injective eq of λ { refl → valid }
 step-preserves GP.requestCancel s permission eq valid with Pool.step Pool.requestCancel (GP.pool s) in advanced
 ... | nothing = case eq of λ ()
 ... | just p′ = case just-injective eq of λ { refl → valid }
 step-preserves GP.join s permission eq valid with Pool.step Pool.join (GP.pool s) in advanced
 ... | nothing = case eq of λ ()
 ... | just p′ = case just-injective eq of λ { refl → valid }
 step-preserves GP.finishClose s permission eq valid with Pool.step Pool.finishClose (GP.pool s) in advanced
 ... | nothing = case eq of λ ()
 ... | just p′ = case just-injective eq of λ { refl → valid }
 step-preserves (GP.publishAsyncResult j) s permission eq valid with Pool.step (Pool.publishAsyncResult j) (GP.pool s) in advanced
 ... | nothing = case eq of λ ()
 ... | just p′ = case just-injective eq of λ { refl → valid }
 step-preserves (GP.bodyUnwound j) s permission eq valid with lookup j (GP.unwinding s) | lookup j (Sub.jobs (GP.machine s))
 ... | just f | just jf with Cancel.pc f
 ...   | Cancel.finished Cancel.abandoned with Pool.step (Pool.bodyUnwound j) (GP.pool s) in advanced
 ...     | just p′ = case just-injective eq of λ { refl → restore-valid (Sub.execution jf) s valid }
 ...     | nothing = case eq of λ ()
 step-preserves (GP.bodyUnwound j) s permission eq valid | just f | just jf | Cancel.finished Cancel.cleanupComplete with Pool.step (Pool.bodyUnwound j) (GP.pool s) in advanced
 ... | just p′ = case just-injective eq of λ { refl → restore-valid (Sub.execution jf) s valid }
 ... | nothing = case eq of λ ()
 step-preserves (GP.bodyUnwound j) s permission eq valid | just f | just jf | Cancel.cleaning active = case eq of λ ()
 step-preserves (GP.bodyUnwound j) s permission eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) = case eq of λ ()
 step-preserves (GP.bodyUnwound j) s permission eq valid | nothing | _ = case eq of λ ()
 step-preserves (GP.bodyUnwound j) s permission eq valid | just f | nothing = case eq of λ ()
 step-preserves (GP.recoverCloseFailure j) s permission eq valid with lookup j (GP.unwinding s) | lookup j (Sub.jobs (GP.machine s))
 ... | just f | just jf with Cancel.pc f | Cancel.original f | J.pc (Sub.execution jf)
 ...   | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring _ | J.awaitAcquire with Pool.step (Pool.resumeAfterUnwindError j) (GP.pool s) in advanced
 ...     | just p′ = case just-injective eq of λ { refl → valid }
 ...     | nothing = case eq of λ ()
 step-preserves (GP.recoverCloseFailure j) s permission eq valid | just f | just jf | Cancel.cleaning active | _ | _ = case eq of λ ()
 step-preserves (GP.recoverCloseFailure j) s permission eq valid | just f | just jf | Cancel.finished Cancel.abandoned | _ | _ = case eq of λ ()
 step-preserves (GP.recoverCloseFailure j) s permission eq valid | just f | just jf | Cancel.finished Cancel.cleanupComplete | _ | _ = case eq of λ ()
 step-preserves (GP.recoverCloseFailure j) s permission eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.noCaller | _ = case eq of λ ()
 step-preserves (GP.recoverCloseFailure j) s permission eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.releasing active | _ = case eq of λ ()
 step-preserves (GP.recoverCloseFailure j) s permission eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.begin = case eq of λ ()
 step-preserves (GP.recoverCloseFailure j) s permission eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.startBundle t ns) = case eq of λ ()
 step-preserves (GP.recoverCloseFailure j) s permission eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.publishBundle t) = case eq of λ ()
 step-preserves (GP.recoverCloseFailure j) s permission eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.markWarm = case eq of λ ()
 step-preserves (GP.recoverCloseFailure j) s permission eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.forkMonitor = case eq of λ ()
 step-preserves (GP.recoverCloseFailure j) s permission eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.finishActivation = case eq of λ ()
 step-preserves (GP.recoverCloseFailure j) s permission eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.awaitHot = case eq of λ ()
 step-preserves (GP.recoverCloseFailure j) s permission eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.awaitAll = case eq of λ ()
 step-preserves (GP.recoverCloseFailure j) s permission eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.callRelease = case eq of λ ()
 step-preserves (GP.recoverCloseFailure j) s permission eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.awaitRelease = case eq of λ ()
 step-preserves (GP.recoverCloseFailure j) s permission eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.delayFailure = case eq of λ ()
 step-preserves (GP.recoverCloseFailure j) s permission eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.awaitCold result) = case eq of λ ()
 step-preserves (GP.recoverCloseFailure j) s permission eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.complete result) = case eq of λ ()
 step-preserves (GP.recoverCloseFailure j) s permission eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.acquirePolicy fault) = case eq of λ ()
 step-preserves (GP.recoverCloseFailure j) s permission eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.nodeDelivery fault) = case eq of λ ()
 step-preserves (GP.recoverCloseFailure j) s permission eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.nodeRethrow fault) = case eq of λ ()
 step-preserves (GP.recoverCloseFailure j) s permission eq valid | nothing | _ = case eq of λ ()
 step-preserves (GP.recoverCloseFailure j) s permission eq valid | just f | nothing = case eq of λ ()
 step-preserves (GP.deregisterCancelled j) s permission eq valid with lookup j (Sub.jobs (GP.machine s)) | Pool.step (Pool.deregister j) (GP.pool s) in advanced
 ... | just jf | just p′ with lookup j (Pool.handles (GP.pool s))
 ...   | just (Pool.deregisterPending Pool.cancelledExit) = case just-injective eq of λ { refl → valid }
 step-preserves (GP.deregisterCancelled j) s permission eq valid | just jf | just p′ | nothing = case eq of λ ()
 step-preserves (GP.deregisterCancelled j) s permission eq valid | just jf | just p′ | just Pool.bodyRunning = case eq of λ ()
 step-preserves (GP.deregisterCancelled j) s permission eq valid | just jf | just p′ | just (Pool.bodyReturned result) = case eq of λ ()
 step-preserves (GP.deregisterCancelled j) s permission eq valid | just jf | just p′ | just Pool.bodyUnwinding = case eq of λ ()
 step-preserves (GP.deregisterCancelled j) s permission eq valid | just jf | just p′ | just (Pool.deregisterPending Pool.normalExit) = case eq of λ ()
 step-preserves (GP.deregisterCancelled j) s permission eq valid | just jf | just p′ | just (Pool.deregistered ex) = case eq of λ ()
 step-preserves (GP.deregisterCancelled j) s permission eq valid | just jf | just p′ | just (Pool.resultAvailable ex) = case eq of λ ()
 step-preserves (GP.deregisterCancelled j) s permission eq valid | nothing | _ = case eq of λ ()
 step-preserves (GP.deregisterCancelled j) s permission eq valid | just jf | nothing = case eq of λ ()




 -- Reuse the existing physical monitor/scope cases with the real permission.
 Predicate : Lift.View → Set
 Predicate (runtime , world , detached) = Q runtime world
 private module Peers = Lift.StepLift Predicate GovernorAllowed step-preserves using (Allowed; step-preserves)
 peer-permission : ∀ action → Allowed action → Peers.Allowed action
 peer-permission (PS.run action) permission = permission
 peer-permission (PS.forkMonitor _ _) _ = tt
 peer-permission (PS.registerMonitor _) _ = tt
 peer-permission (PS.returnEstablishment _) _ = tt
 peer-permission (PS.finishEstablishment _) _ = tt
 peer-permission (PS.monitorException _ _) _ = tt
 peer-permission (PS.commitMonitorError _) _ = tt
 peer-permission (PS.finishMonitorError _) _ = tt
 peer-permission (PS.finishMonitor _) _ = tt
 peer-permission (PS.scope _) _ = tt
 peer-permission (PS.beginMonitorClose _) _ = tt
 peer-permission PS.requestMonitorCancel _ = tt
 peer-permission PS.joinMonitor _ = tt
 peer-permission PS.finishMonitorClose _ = tt
 peer-permission (PS.deliverMonitorCancellation _) _ = tt
 peer-permission (PS.deliverBlockedMonitorCancellation _) _ = tt
 peer-permission (PS.monitorBodyUnwound _) _ = tt
 peer-permission (PS.deregisterMonitor _) _ = tt
 peer-permission (PS.publishMonitorResult _) _ = tt
 peer-preserves : ∀ action s {next} → Allowed action → PS.step action s ≡ just next →
   Q (CM.acquiring (PS.cm s)) (PS.shared s) → Q (CM.acquiring (PS.cm next)) (PS.shared next)
 peer-preserves action s permission = Peers.step-preserves action s (peer-permission action permission)

-- Fix the observed initial table; the result takes no invariant premise.
cleanups-same : ∀ action s {next} → Allowed action → PS.step action s ≡ just next →
 S.cleanups (PS.shared next) ≡ S.cleanups (PS.shared s)
cleanups-same action s permission actual = For.peer-preserves (S.cleanups (PS.shared s)) action s permission actual refl
