{-# OPTIONS --guardedness #-}

-- Supply bounds through coupled governor execution, including every detached
-- caller cleanup capture and every still-active ordinary acquisition frame.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool; true; false)
module ConnectionManagement.Properties.GovernorPoolSupply (isIOManagerError : ErrorId → Bool) where

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; []; map)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (Store; lookup)
open import ConnectionManagement.Properties.Stores using (put-values; delete-values)
open import ConnectionManagement.Properties.Counters using (lookup-all)
open import ConnectionManagement.Properties.Entries using (Present)
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as I
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Rules.ProductionPolicy as Policy
import ConnectionManagement.GovernorPool as Governor
module GP = Governor isIOManagerError
module Pool = GP.Pool
import ConnectionManagement.Properties.CallerCancellation as Writer
import ConnectionManagement.Properties.CallerCancellationCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Runtime
import ConnectionManagement.Properties.OutboundRuntimeCapture as RawCapture
import ConnectionManagement.Properties.SubsystemSupply as RawSupply
import ConnectionManagement.Properties.StateRetention as StateRetention
import ConnectionManagement.Properties.IGTableRetention as Tables
import ConnectionManagement.Properties.OutboundWorldInvariant as OutboundLift
import ConnectionManagement.Properties.SubsystemWorldInvariant as SubLift

shared : GP.State → S.State
shared s = I.world (CM.core (GP.cm s))
Detached : Store JobId Cancel.Frame → S.State → Set
Detached frames world = All (λ binding → Capture.Valid (proj₂ binding) world) frames

-- Both ordinary and detached frames are needed in the closed induction invariant.
Valid : GP.State → Set
Valid s = RawSupply.Valid (GP.machine s) × Detached (GP.unwinding s) (shared s)
Bounded : GP.State → Set
Bounded s = SupplyBounds (shared s)

module Raw = GP.Production.Lift RawSupply.Valid RawSupply.advance-preserves

-- The existing general writer lifts retain allocated entries through every
-- source action, including other actors' shared-state changes.
module Entry (e : EntryId) where
  Predicate : S.State → IG.Runtime → Set
  Predicate world ig = Present e (S.entries (S.cm world))
  stable : ∀ {s s′ ig ig′} → StateRetention.Retains s s′ → Tables.Retains ig ig′ →
    Predicate s ig → Predicate s′ ig′
  stable retained tables = StateRetention.entriesRetained retained e
  module Outbound = OutboundLift.Lift Predicate stable
  module Combined = SubLift.Lift Predicate Outbound.advance-preserves (λ tables present → present)
  module Production = GP.Production.Lift Combined.Valid Combined.advance-preserves

raw-retains : ∀ action s {source′} → GP.Production.step (Policy.dispatch action) (GP.source s) ≡ just source′ →
  ∀ e → Present e (S.entries (S.cm (shared s))) →
    Present e (S.entries (S.cm (I.world (CM.core (J.cm (Sub.world (Policy.machine source′)))))))
raw-retains action s eq e = Entry.Production.step-preserves e (Policy.dispatch action) (GP.source s) eq

retained : ∀ frames world world′ →
  (∀ e → Present e (S.entries (S.cm world)) → Present e (S.entries (S.cm world′))) →
  Detached frames world → Detached frames world′
retained frames world world′ keeps = map (λ { {x = j , f} → Capture.retained-valid f world world′ keeps })

-- PeerCold restoration is a real peer-runtime write; its CM observation is exact.
restore-cm : ∀ f c → J.cm (Sub.world (GP.restoreCold f c)) ≡ J.cm (Sub.world c)
restore-cm f c with G.kind (J.work f) | J.pc f
... | G.establish | J.begin = refl
... | G.establish | J.complete result = refl
restore-cm f c | G.establish | J.awaitAcquire with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-cm f c | G.establish | (J.startBundle t ns) with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-cm f c | G.establish | (J.publishBundle t) with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-cm f c | G.establish | J.markWarm with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-cm f c | G.establish | J.forkMonitor with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-cm f c | G.establish | J.finishActivation with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-cm f c | G.establish | J.awaitHot with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-cm f c | G.establish | J.awaitAll with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-cm f c | G.establish | J.callRelease with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-cm f c | G.establish | J.awaitRelease with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-cm f c | G.establish | J.delayFailure with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-cm f c | G.establish | (J.awaitCold result) with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-cm f c | G.establish | (J.acquirePolicy fault) with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-cm f c | G.establish | (J.nodeDelivery fault) with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-cm f c | G.establish | (J.nodeRethrow fault) with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = refl
... | just peer = refl
restore-cm f c | G.forget | _ = refl
restore-cm f c | G.activate | _ = refl
restore-cm f c | G.close | _ = refl
restore-cm f c | G.deactivate | _ = refl

-- Starting cancellation transfers a valid capture without changing shared stores.
delivery-valid : ∀ blocked err s {s′} → GP.deliver blocked err s ≡ just s′ → Valid s → Valid s′
delivery-valid blocked err s eq (raw , detached) with Pool.phase (GP.pool s)
... | Pool.cancelPending j with lookup j (Sub.jobs (GP.machine s)) | Pool.step Pool.deliverCancel (GP.pool s)
...   | just jf | just p′ with Cancel.start (J.caller (Sub.execution jf)) err
    (GP.deliveryContext blocked (GP.region (J.caller (Sub.execution jf)) s)) (GP.cm s) in started
...     | just (f , c′) = case just-injective eq of λ { refl →
  (proj₁ (Capture.start-valid (J.caller (Sub.execution jf)) err
    (GP.deliveryContext blocked (GP.region (J.caller (Sub.execution jf)) s)) (GP.cm s) started (proj₁ raw)) ,
   subst (λ core → SupplyBounds (I.world core))
    (sym (Writer.start-core (J.caller (Sub.execution jf)) err
      (GP.deliveryContext blocked (GP.region (J.caller (Sub.execution jf)) s)) (GP.cm s) started)) (proj₂ raw)) ,
  put-values (λ f → Capture.Valid f (I.world (CM.core c′))) j f (GP.unwinding s)
    (proj₂ (Capture.start-valid (J.caller (Sub.execution jf)) err
      (GP.deliveryContext blocked (GP.region (J.caller (Sub.execution jf)) s)) (GP.cm s) started (proj₁ raw)))
    (subst (λ core → Detached (GP.unwinding s) (I.world core))
      (sym (Writer.start-core (J.caller (Sub.execution jf)) err
        (GP.deliveryContext blocked (GP.region (J.caller (Sub.execution jf)) s)) (GP.cm s) started)) detached) }
...     | nothing = case eq of λ ()
delivery-valid blocked err s eq valid | Pool.cancelPending j | nothing | _ = case eq of λ ()
delivery-valid blocked err s eq valid | Pool.cancelPending j | just jf | nothing = case eq of λ ()
delivery-valid blocked err s eq valid | Pool.openPool = case eq of λ ()
delivery-valid blocked err s eq valid | Pool.closing = case eq of λ ()
delivery-valid blocked err s eq valid | Pool.closedPool = case eq of λ ()
delivery-valid blocked err s eq valid | Pool.joinPending j = case eq of λ ()

restore-valid : ∀ f s → Valid s → Valid (record s { source = record (GP.source s) { machine = GP.restoreCold f (GP.machine s) } })
restore-valid f s (raw , detached) =
  subst Runtime.Valid (sym (restore-cm f (GP.machine s))) raw ,
  subst (λ c → Detached (GP.unwinding s) (I.world (CM.core c))) (sym (restore-cm f (GP.machine s))) detached

-- All source, cleanup and scope bookkeeping actions preserve the combined invariant.
step-preserves : ∀ action s {s′} → GP.step action s ≡ just s′ → Valid s → Valid s′
step-preserves (GP.run action) s eq (raw , detached) with GP.normalPool action s | GP.Production.step (Policy.dispatch action) (GP.source s) in sourceStep
... | just p′ | just source′ with GP.noteReturn action (Policy.machine source′) p′
...   | just p″ = case just-injective eq of λ { refl →
  Raw.step-preserves (Policy.dispatch action) (GP.source s) sourceStep raw ,
  retained (GP.unwinding s) (shared s) _ (raw-retains action s sourceStep) detached }
...   | nothing = case eq of λ ()
step-preserves (GP.run action) s eq valid | nothing | _ = case eq of λ ()
step-preserves (GP.run action) s eq valid | just p′ | nothing = case eq of λ ()
step-preserves (GP.cleanup j action) s eq (raw , detached) with lookup j (GP.unwinding s) in found
... | nothing = case eq of λ ()
... | just f with Cancel.step action f (GP.cm s) in cleaned
...   | nothing = case eq of λ ()
...   | just (f′ , c′) = case just-injective eq of λ { refl →
  (Capture.step-runtime action f (GP.cm s) cleaned (proj₁ raw) ,
   Capture.step-bounds action f (GP.cm s) cleaned
     (lookup-all (λ f → Capture.Valid f (shared s)) j (GP.unwinding s) detached found) (proj₂ raw)) ,
  put-values (λ f → Capture.Valid f (I.world (CM.core c′))) j f′ (GP.unwinding s)
    (Capture.step-valid action f (GP.cm s) cleaned
      (lookup-all (λ f → Capture.Valid f (shared s)) j (GP.unwinding s) detached found))
    (retained (GP.unwinding s) (shared s) _ (Capture.step-retains action f (GP.cm s) cleaned) detached) }
step-preserves (GP.deliverCancellation err) s eq valid = delivery-valid false err s eq valid
step-preserves (GP.deliverOpenCancellation err) s eq valid = delivery-valid true err s eq valid
step-preserves (GP.handoff w) s eq valid with GP.region w s | lookup w (CM.acquiring (GP.cm s))
... | Cancel.forkedBeforeHandoff | just f with A.pc f
...   | A.connectedCommit _ _ _ = case just-injective eq of λ { refl → valid }
step-preserves (GP.handoff w) s eq valid | Cancel.forkedBeforeHandoff | just f | A.selecting = case eq of λ ()
step-preserves (GP.handoff w) s eq valid | Cancel.forkedBeforeHandoff | just f | (A.count next) = case eq of λ ()
step-preserves (GP.handoff w) s eq valid | Cancel.forkedBeforeHandoff | just f | (A.allocatePromise e) = case eq of λ ()
step-preserves (GP.handoff w) s eq valid | Cancel.forkedBeforeHandoff | just f | (A.openSocket e pid) = case eq of λ ()
step-preserves (GP.handoff w) s eq valid | Cancel.forkedBeforeHandoff | just f | (A.configureSocket e pid) = case eq of λ ()
step-preserves (GP.handoff w) s eq valid | Cancel.forkedBeforeHandoff | just f | (A.bindSocket e pid) = case eq of λ ()
step-preserves (GP.handoff w) s eq valid | Cancel.forkedBeforeHandoff | just f | (A.connectSocket e pid) = case eq of λ ()
step-preserves (GP.handoff w) s eq valid | Cancel.forkedBeforeHandoff | just f | (A.localAddress e pid) = case eq of λ ()
step-preserves (GP.handoff w) s eq valid | Cancel.forkedBeforeHandoff | just f | (A.updateAddress e pid key) = case eq of λ ()
step-preserves (GP.handoff w) s eq valid | Cancel.forkedBeforeHandoff | just f | (A.forkHandler e pid key) = case eq of λ ()
step-preserves (GP.handoff w) s eq valid | Cancel.forkedBeforeHandoff | just f | (A.awaitResult e pid key) = case eq of λ ()
step-preserves (GP.handoff w) s eq valid | Cancel.forkedBeforeHandoff | just f | (A.commitResult e key result) = case eq of λ ()
step-preserves (GP.handoff w) s eq valid | Cancel.forkedBeforeHandoff | just f | (A.waitingInbound e key) = case eq of λ ()
step-preserves (GP.handoff w) s eq valid | Cancel.forkedBeforeHandoff | just f | (A.closeError e err) = case eq of λ ()
step-preserves (GP.handoff w) s eq valid | Cancel.forkedBeforeHandoff | just f | (A.removeError e err) = case eq of λ ()
step-preserves (GP.handoff w) s eq valid | Cancel.forkedBeforeHandoff | just f | (A.complete result) = case eq of λ ()
step-preserves (GP.handoff w) s eq valid | Cancel.forkedBeforeHandoff | nothing = case eq of λ ()
step-preserves (GP.handoff w) s eq valid | Cancel.ordinary | _ = case eq of λ ()
step-preserves (GP.handoff w) s eq valid | Cancel.protectedCleanup | _ = case eq of λ ()
step-preserves (GP.handoff w) s eq valid | Cancel.interruptibleOpen | _ = case eq of λ ()
step-preserves (GP.beginClose order) s eq valid with Pool.step (Pool.beginClose order) (GP.pool s) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → valid }
step-preserves GP.requestCancel s eq valid with Pool.step Pool.requestCancel (GP.pool s) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → valid }
step-preserves GP.join s eq valid with Pool.step Pool.join (GP.pool s) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → valid }
step-preserves GP.finishClose s eq valid with Pool.step Pool.finishClose (GP.pool s) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → valid }
step-preserves (GP.publishAsyncResult j) s eq valid with Pool.step (Pool.publishAsyncResult j) (GP.pool s) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → valid }
step-preserves (GP.bodyUnwound j) s eq valid with lookup j (GP.unwinding s) | lookup j (Sub.jobs (GP.machine s))
... | just f | just jf with Cancel.pc f
...   | Cancel.finished Cancel.abandoned with Pool.step (Pool.bodyUnwound j) (GP.pool s) in advanced
...     | just p′ = case just-injective eq of λ { refl → restore-valid (Sub.execution jf) s valid }
...     | nothing = case eq of λ ()
step-preserves (GP.bodyUnwound j) s eq valid | just f | just jf | Cancel.finished Cancel.cleanupComplete with Pool.step (Pool.bodyUnwound j) (GP.pool s) in advanced
... | just p′ = case just-injective eq of λ { refl → restore-valid (Sub.execution jf) s valid }
... | nothing = case eq of λ ()
step-preserves (GP.bodyUnwound j) s eq valid | just f | just jf | Cancel.cleaning active = case eq of λ ()
step-preserves (GP.bodyUnwound j) s eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) = case eq of λ ()
step-preserves (GP.bodyUnwound j) s eq valid | nothing | _ = case eq of λ ()
step-preserves (GP.bodyUnwound j) s eq valid | just f | nothing = case eq of λ ()
step-preserves (GP.recoverCloseFailure j) s eq valid with lookup j (GP.unwinding s) | lookup j (Sub.jobs (GP.machine s))
... | just f | just jf with Cancel.pc f | Cancel.original f | J.pc (Sub.execution jf)
...   | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring _ | J.awaitAcquire with Pool.step (Pool.resumeAfterUnwindError j) (GP.pool s) in advanced
...     | just p′ = case just-injective eq of λ { refl → proj₁ valid , delete-values (λ f → Capture.Valid f (shared s)) j (GP.unwinding s) (proj₂ valid) }
...     | nothing = case eq of λ ()
step-preserves (GP.recoverCloseFailure j) s eq valid | just f | just jf | Cancel.cleaning active | _ | _ = case eq of λ ()
step-preserves (GP.recoverCloseFailure j) s eq valid | just f | just jf | Cancel.finished Cancel.abandoned | _ | _ = case eq of λ ()
step-preserves (GP.recoverCloseFailure j) s eq valid | just f | just jf | Cancel.finished Cancel.cleanupComplete | _ | _ = case eq of λ ()
step-preserves (GP.recoverCloseFailure j) s eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.noCaller | _ = case eq of λ ()
step-preserves (GP.recoverCloseFailure j) s eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.releasing active | _ = case eq of λ ()
step-preserves (GP.recoverCloseFailure j) s eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.begin = case eq of λ ()
step-preserves (GP.recoverCloseFailure j) s eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.startBundle t ns) = case eq of λ ()
step-preserves (GP.recoverCloseFailure j) s eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.publishBundle t) = case eq of λ ()
step-preserves (GP.recoverCloseFailure j) s eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.markWarm = case eq of λ ()
step-preserves (GP.recoverCloseFailure j) s eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.forkMonitor = case eq of λ ()
step-preserves (GP.recoverCloseFailure j) s eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.finishActivation = case eq of λ ()
step-preserves (GP.recoverCloseFailure j) s eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.awaitHot = case eq of λ ()
step-preserves (GP.recoverCloseFailure j) s eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.awaitAll = case eq of λ ()
step-preserves (GP.recoverCloseFailure j) s eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.callRelease = case eq of λ ()
step-preserves (GP.recoverCloseFailure j) s eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.awaitRelease = case eq of λ ()
step-preserves (GP.recoverCloseFailure j) s eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.delayFailure = case eq of λ ()
step-preserves (GP.recoverCloseFailure j) s eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.awaitCold result) = case eq of λ ()
step-preserves (GP.recoverCloseFailure j) s eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.complete result) = case eq of λ ()
step-preserves (GP.recoverCloseFailure j) s eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.acquirePolicy fault) = case eq of λ ()
step-preserves (GP.recoverCloseFailure j) s eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.nodeDelivery fault) = case eq of λ ()
step-preserves (GP.recoverCloseFailure j) s eq valid | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.nodeRethrow fault) = case eq of λ ()
step-preserves (GP.recoverCloseFailure j) s eq valid | nothing | _ = case eq of λ ()
step-preserves (GP.recoverCloseFailure j) s eq valid | just f | nothing = case eq of λ ()
step-preserves (GP.deregisterCancelled j) s eq valid with lookup j (Sub.jobs (GP.machine s)) | Pool.step (Pool.deregister j) (GP.pool s) in advanced
... | just jf | just p′ with lookup j (Pool.handles (GP.pool s))
...   | just (Pool.deregisterPending Pool.cancelledExit) = case just-injective eq of λ { refl → valid }
step-preserves (GP.deregisterCancelled j) s eq valid | just jf | just p′ | nothing = case eq of λ ()
step-preserves (GP.deregisterCancelled j) s eq valid | just jf | just p′ | just Pool.bodyRunning = case eq of λ ()
step-preserves (GP.deregisterCancelled j) s eq valid | just jf | just p′ | just (Pool.bodyReturned result) = case eq of λ ()
step-preserves (GP.deregisterCancelled j) s eq valid | just jf | just p′ | just Pool.bodyUnwinding = case eq of λ ()
step-preserves (GP.deregisterCancelled j) s eq valid | just jf | just p′ | just (Pool.deregisterPending Pool.normalExit) = case eq of λ ()
step-preserves (GP.deregisterCancelled j) s eq valid | just jf | just p′ | just (Pool.deregistered ex) = case eq of λ ()
step-preserves (GP.deregisterCancelled j) s eq valid | just jf | just p′ | just (Pool.resultAvailable ex) = case eq of λ ()
step-preserves (GP.deregisterCancelled j) s eq valid | nothing | _ = case eq of λ ()
step-preserves (GP.deregisterCancelled j) s eq valid | just jf | nothing = case eq of λ ()


exec-preserves : ∀ {s actions s′} → GP.Executes s actions s′ → Valid s → Valid s′
exec-preserves GP.done valid = valid
exec-preserves (GP.next {s = s} {a = a} eq path) valid = exec-preserves path (step-preserves a s eq valid)

initial-valid : ∀ c g → SupplyBounds (I.world c) → Valid (GP.initial (CM.initial c) g)
initial-valid c g bounded = RawSupply.initial-valid c g bounded , []

from-initial-valid : ∀ {c g actions s} → SupplyBounds (I.world c) →
  GP.Executes (GP.initial (CM.initial c) g) actions s → Valid s
from-initial-valid {c} {g} bounded path = exec-preserves path (initial-valid c g bounded)

-- Every finite coupled execution retains both bounds and all cleanup captures.
from-initial : ∀ {c g actions s} → SupplyBounds (I.world c) →
  GP.Executes (GP.initial (CM.initial c) g) actions s → Bounded s
from-initial bounded path = proj₂ (proj₁ (from-initial-valid bounded path))
