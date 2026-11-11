{-# OPTIONS --guardedness #-}

-- GovernorPoolCM's lifting tree with a precise acquired-table write premise.
-- The existing generic lift permits an arbitrary replacement table, which is
-- too broad for uniqueness. Recovery actually performs exactly one put.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesGovernorLift (isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import ConnectionManagement.Domain using (ident)
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as I
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Properties.MachineQuiet as Quiet
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundCases as Cases
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Rules.ProductionPolicy as Policy
import ConnectionManagement.GovernorPool as Governor
import ConnectionManagement.Properties.CallerCancellation as Writer
import ConnectionManagement.Properties.GovernorPoolSupply as GovernorSupply
import ConnectionManagement.Properties.SubsystemCM as SubLift
import ConnectionManagement.Properties.PeerJobCM as JobLift
module GP = Governor isIOManagerError
module Pool = GP.Pool
private module Supply = GovernorSupply isIOManagerError using (restore-cm)

module StepLift
  (Predicate : CM.Configuration → Set)
  (ig-write : ∀ c g → Quiet.SameControl (I.inboundGovernor (CM.core c)) g → Predicate c → Predicate (record c { core = record (CM.core c) { inboundGovernor = g } }))
  (begin-acquire : ∀ worker request c {c′} → CM.advance (CM.beginAcquire worker request) c ≡ just c′ → Predicate c → Predicate c′)
  (begin-release : ∀ worker key c {c′} → CM.advance (CM.beginRelease worker key) c ≡ just c′ → Predicate c → Predicate c′)
  (monitor-preserve : ∀ mid c {c′} → CM.advance (CM.inbound (I.igStep (IG.monitorCompletion mid))) c ≡ just c′ → Predicate c → Predicate c′)
  (PermitCore : CM.Action → Set)
  (core-preserve : ∀ a c {c′} → PermitCore a → CM.advance a c ≡ just c′ → Predicate c → Predicate c′)
  (cancel-start : ∀ w err context c {f c′} → Cancel.start w err context c ≡ just (f , c′) → Predicate c → Predicate c′)
  (world-write : ∀ c world → Predicate c → Predicate (record c { core = I.replaceWorld (CM.core c) world }))
  (acquired-write : ∀ c w value → Predicate c → Predicate (record c { acquired = put w value (CM.acquired c) })) where

  private
    module Jobs = JobLift.BeginLift Predicate ig-write begin-acquire begin-release
    module Steps = SubLift.StepLift Predicate ig-write Jobs.step-preserves monitor-preserve PermitCore core-preserve

  -- Only a raw core action needs a permission.
  Allowed : GP.Action → Set
  Allowed (GP.run action) = Steps.Allowed action
  Allowed _ = Data.Unit.⊤
    where import Data.Unit

  -- One production dispatch is one real subsystem step.
  run-preserves : ∀ action source {source′} → Steps.Allowed action →
    GP.Production.step (Policy.dispatch action) source ≡ just source′ →
    Predicate (J.cm (Sub.world (Policy.machine source))) → Predicate (J.cm (Sub.world (Policy.machine source′)))
  run-preserves action source permission eq valid with GP.Production.step-projects (Policy.dispatch action) source eq
  ... | Sub.next advanced Sub.done = Steps.advance-preserves action (Policy.machine source) permission advanced valid

  -- Cancellation cleanup writes only the shared world.
  cleanup-preserves : ∀ action f c {f′ c′} → Cancel.step action f c ≡ just (f′ , c′) → Predicate c → Predicate c′
  cleanup-preserves action f c eq valid with Writer.step-writer action f c eq
  ... | Writer.writer active active′ shared′ before source frame refl = world-write c shared′ valid

  delivery-preserves : ∀ blocked err s {s′} → GP.deliver blocked err s ≡ just s′ → Predicate (GP.cm s) → Predicate (GP.cm s′)
  delivery-preserves blocked err s eq valid with Pool.phase (GP.pool s)
  ... | Pool.cancelPending j with lookup j (Sub.jobs (GP.machine s)) | Pool.step Pool.deliverCancel (GP.pool s)
  ...   | just jf | just p′ with Cancel.start (J.caller (Sub.execution jf)) err
      (GP.deliveryContext blocked (GP.region (J.caller (Sub.execution jf)) s)) (GP.cm s) in started
  ...     | just (f , c′) = case just-injective eq of λ { refl → cancel-start (J.caller (Sub.execution jf)) err
    (GP.deliveryContext blocked (GP.region (J.caller (Sub.execution jf)) s)) (GP.cm s) started valid }
  ...     | nothing = case eq of λ ()
  delivery-preserves blocked err s eq valid | Pool.cancelPending j | nothing | _ = case eq of λ ()
  delivery-preserves blocked err s eq valid | Pool.cancelPending j | just jf | nothing = case eq of λ ()
  delivery-preserves blocked err s eq valid | Pool.openPool = case eq of λ ()
  delivery-preserves blocked err s eq valid | Pool.closing = case eq of λ ()
  delivery-preserves blocked err s eq valid | Pool.closedPool = case eq of λ ()
  delivery-preserves blocked err s eq valid | Pool.joinPending j = case eq of λ ()

  step-preserves : ∀ action s {s′} → Allowed action → GP.step action s ≡ just s′ → Predicate (GP.cm s) → Predicate (GP.cm s′)
  step-preserves (GP.run action) s permission eq valid with GP.normalPool action s | GP.Production.step (Policy.dispatch action) (GP.source s) in sourceStep
  ... | just p′ | just source′ with GP.noteReturn action (Policy.machine source′) p′
  ...   | just p″ = case just-injective eq of λ { refl → run-preserves action (GP.source s) permission sourceStep valid }
  ...   | nothing = case eq of λ ()
  step-preserves (GP.run action) s permission eq valid | nothing | _ = case eq of λ ()
  step-preserves (GP.run action) s permission eq valid | just p′ | nothing = case eq of λ ()
  step-preserves (GP.cleanup j action) s permission eq valid with lookup j (GP.unwinding s)
  ... | nothing = case eq of λ ()
  ... | just f with Cancel.step action f (GP.cm s) in cleaned
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , c′) = case just-injective eq of λ { refl → cleanup-preserves action f (GP.cm s) cleaned valid }
  step-preserves (GP.deliverCancellation err) s permission eq valid = delivery-preserves false err s eq valid
  step-preserves (GP.deliverOpenCancellation err) s permission eq valid = delivery-preserves true err s eq valid
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
  ...     | just p′ = case just-injective eq of λ { refl → subst Predicate (sym (Supply.restore-cm (Sub.execution jf) (GP.machine s))) valid }
  ...     | nothing = case eq of λ ()
  step-preserves (GP.bodyUnwound j) s permission eq valid | just f | just jf | Cancel.finished Cancel.cleanupComplete with Pool.step (Pool.bodyUnwound j) (GP.pool s) in advanced
  ... | just p′ = case just-injective eq of λ { refl → subst Predicate (sym (Supply.restore-cm (Sub.execution jf) (GP.machine s))) valid }
  ... | nothing = case eq of λ ()
  step-preserves (GP.bodyUnwound j) s permission eq valid | just f | just jf | Cancel.cleaning active = case eq of λ ()
  step-preserves (GP.bodyUnwound j) s permission eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) = case eq of λ ()
  step-preserves (GP.bodyUnwound j) s permission eq valid | nothing | _ = case eq of λ ()
  step-preserves (GP.bodyUnwound j) s permission eq valid | just f | nothing = case eq of λ ()
  step-preserves (GP.recoverCloseFailure j) s permission eq valid with lookup j (GP.unwinding s) | lookup j (Sub.jobs (GP.machine s))
  ... | just f | just jf with Cancel.pc f | Cancel.original f | J.pc (Sub.execution jf)
  ...   | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring _ | J.awaitAcquire with Pool.step (Pool.resumeAfterUnwindError j) (GP.pool s) in advanced
  ...     | just p′ = case just-injective eq of λ { refl → acquired-write (GP.cm s) (Cancel.caller f) (Cases.raised (Cases.ioFailure err)) valid }
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
