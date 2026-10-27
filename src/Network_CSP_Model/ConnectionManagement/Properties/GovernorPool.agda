{-# OPTIONS --guardedness #-}

-- Pool projection of the coupled governor execution. Real CM cleanup writes
-- remain in the source machine; only its separate pool component is projected.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.GovernorPool (isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.ProductionPolicy as Policy
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.GovernorPool as Governor
module GP = Governor isIOManagerError
module Pool = GP.Pool
import ConnectionManagement.Properties.JobPoolClose as CloseProof
module Close = CloseProof GP.Body

-- A real projected path may contain zero, one, or several primitive actions.
Trace : Pool.State → Pool.State → Set
Trace p p′ = Σ (List Pool.Action) (λ actions → Pool.Executes p actions p′)

idle : ∀ p {p′} → just p ≡ just p′ → Trace p p′
idle p eq = case just-injective eq of λ { refl → [] , Pool.done }
one : ∀ a p {p′} → Pool.step a p ≡ just p′ → Trace p p′
one a p eq = (a ∷ []) , Pool.next eq Pool.done
append : ∀ {p as p₁ bs p₂} → Pool.Executes p as p₁ → Pool.Executes p₁ bs p₂ → Pool.Executes p (as ++ bs) p₂
append Pool.done right = right
append (Pool.next eq left) right = Pool.next eq (append left right)
compose : ∀ {p p₁ p₂} → Trace p p₁ → Trace p₁ p₂ → Trace p p₂
compose (as , left) (bs , right) = (as ++ bs) , append left right

-- Normal source actions have precisely the coupled pool effects.
normal-trace : ∀ a s {p′} → GP.normalPool a s ≡ just p′ → Trace (GP.pool s) p′
normal-trace (Sub.forkJob w child sock) s eq with GP.ownerOpen (GP.pool s)
... | true = one (Pool.fork (ident (Sub.nextJob (GP.machine s)))) (GP.pool s) eq
... | false = case eq of λ ()
normal-trace Sub.registerJob s eq with Sub.pc (GP.machine s) | Pool.parentFork (GP.pool s)
... | Sub.register j rest | just k with j ≟ k
...   | yes _ = one Pool.register (GP.pool s) eq
...   | no _ = case eq of λ ()
normal-trace Sub.registerJob s eq | Sub.publishPublic | _ = case eq of λ ()
normal-trace Sub.registerJob s eq | Sub.sampleInputs | _ = case eq of λ ()
normal-trace Sub.registerJob s eq | Sub.prepareWait | _ = case eq of λ ()
normal-trace Sub.registerJob s eq | Sub.selecting | _ = case eq of λ ()
normal-trace Sub.registerJob s eq | (Sub.cancelTimer picked) | _ = case eq of λ ()
normal-trace Sub.registerJob s eq | (Sub.apply picked) | _ = case eq of λ ()
normal-trace Sub.registerJob s eq | (Sub.publishView work) | _ = case eq of λ ()
normal-trace Sub.registerJob s eq | (Sub.traceDecision work) | _ = case eq of λ ()
normal-trace Sub.registerJob s eq | (Sub.launch work) | _ = case eq of λ ()
normal-trace Sub.registerJob s eq | (Sub.completionAssertionFailed result) | _ = case eq of λ ()
normal-trace Sub.registerJob s eq | Sub.register j rest | nothing = case eq of λ ()
normal-trace (Sub.enqueueCompletion j delay) s eq with lookup j (Pool.handles (GP.pool s))
... | just (Pool.bodyReturned captured) with GP.returnedBody j (GP.machine s) captured
...   | true = one (Pool.publishCompletion j) (GP.pool s) eq
...   | false = case eq of λ ()
normal-trace (Sub.enqueueCompletion j delay) s eq | nothing = case eq of λ ()
normal-trace (Sub.enqueueCompletion j delay) s eq | just Pool.bodyRunning = case eq of λ ()
normal-trace (Sub.enqueueCompletion j delay) s eq | just Pool.bodyUnwinding = case eq of λ ()
normal-trace (Sub.enqueueCompletion j delay) s eq | just (Pool.deregisterPending ex) = case eq of λ ()
normal-trace (Sub.enqueueCompletion j delay) s eq | just (Pool.deregistered ex) = case eq of λ ()
normal-trace (Sub.enqueueCompletion j delay) s eq | just (Pool.resultAvailable ex) = case eq of λ ()
normal-trace (Sub.deregisterJob j) s eq = one (Pool.deregister j) (GP.pool s) eq
normal-trace (Sub.jobStep j action) s eq with GP.running j (GP.pool s)
... | true = idle (GP.pool s) eq
... | false = case eq of λ ()
normal-trace (Sub.core action) s eq with GP.coreAllowed action s
... | true = idle (GP.pool s) eq
... | false = case eq of λ ()
normal-trace Sub.publishPublicState s eq with GP.ownerOpen (GP.pool s)
... | true = idle (GP.pool s) eq
... | false = case eq of λ ()
normal-trace (Sub.sampleTime t) s eq with GP.ownerOpen (GP.pool s)
... | true = idle (GP.pool s) eq
... | false = case eq of λ ()
normal-trace (Sub.applyAt t) s eq with GP.ownerOpen (GP.pool s)
... | true = idle (GP.pool s) eq
... | false = case eq of λ ()
normal-trace (Sub.setTargets t) s eq = idle (GP.pool s) eq
normal-trace (Sub.selectMonitor delay) s eq with GP.ownerOpen (GP.pool s)
... | true = idle (GP.pool s) eq
... | false = case eq of λ ()
normal-trace Sub.selectCompletion s eq with GP.ownerOpen (GP.pool s)
... | true = idle (GP.pool s) eq
... | false = case eq of λ ()
normal-trace Sub.selectTargets s eq with GP.ownerOpen (GP.pool s)
... | true = idle (GP.pool s) eq
... | false = case eq of λ ()
normal-trace Sub.selectWakeup s eq with GP.ownerOpen (GP.pool s)
... | true = idle (GP.pool s) eq
... | false = case eq of λ ()
normal-trace Sub.registerWakeup s eq with GP.ownerOpen (GP.pool s)
... | true = idle (GP.pool s) eq
... | false = case eq of λ ()
normal-trace Sub.expireWakeup s eq = idle (GP.pool s) eq
normal-trace Sub.cancelWakeup s eq with GP.ownerOpen (GP.pool s)
... | true = idle (GP.pool s) eq
... | false = case eq of λ ()
normal-trace Sub.publishCounters s eq with GP.ownerOpen (GP.pool s)
... | true = idle (GP.pool s) eq
... | false = case eq of λ ()
normal-trace Sub.traceSelection s eq with GP.ownerOpen (GP.pool s)
... | true = idle (GP.pool s) eq
... | false = case eq of λ ()
normal-trace (Sub.selectPolicy picked) s eq with GP.ownerOpen (GP.pool s)
... | true = idle (GP.pool s) eq
... | false = case eq of λ ()
normal-trace Sub.finishLaunch s eq with GP.ownerOpen (GP.pool s)
... | true = idle (GP.pool s) eq
... | false = case eq of λ ()
normal-trace (Sub.protocolResult ref n result) s eq = idle (GP.pool s) eq
normal-trace (Sub.publishInitiatorResult ref i) s eq = idle (GP.pool s) eq
normal-trace (Sub.pollPeer ref w) s eq = idle (GP.pool s) eq
normal-trace (Sub.monitorStep ref a) s eq = idle (GP.pool s) eq
normal-trace (Sub.monitorFinished ref) s eq = idle (GP.pool s) eq
normal-trace (Sub.observeInitiatorFailure ref) s eq = idle (GP.pool s) eq

-- A body-return observation is an actual primitive return, not a terminal result.
return-trace : ∀ a c p {p′} → GP.noteReturn a c p ≡ just p′ → Trace p p′
return-trace (Sub.jobStep j action) c p eq with lookup j (Sub.jobs c)
... | nothing = case eq of λ ()
... | just jf with J.pc (Sub.execution jf)
...   | J.complete result = one (Pool.bodyReturnedWith j (GP.body j (J.work (Sub.execution jf)) result)) p eq
...   | J.begin = idle p eq
...   | J.awaitAcquire = idle p eq
...   | J.startBundle t ns = idle p eq
...   | J.publishBundle t = idle p eq
...   | J.markWarm = idle p eq
...   | J.forkMonitor = idle p eq
...   | J.finishActivation = idle p eq
...   | J.awaitHot = idle p eq
...   | J.awaitAll = idle p eq
...   | J.callRelease = idle p eq
...   | J.awaitRelease = idle p eq
...   | J.delayFailure = idle p eq
...   | J.awaitCold result = idle p eq
...   | J.acquirePolicy fault = idle p eq
...   | J.nodeDelivery fault = idle p eq
...   | J.nodeRethrow fault = idle p eq
return-trace (Sub.core a) c p eq = idle p eq
return-trace (Sub.forkJob w child sock) c p eq = idle p eq
return-trace Sub.registerJob c p eq = idle p eq
return-trace (Sub.enqueueCompletion j delay) c p eq = idle p eq
return-trace (Sub.deregisterJob j) c p eq = idle p eq
return-trace Sub.publishPublicState c p eq = idle p eq
return-trace (Sub.sampleTime t) c p eq = idle p eq
return-trace (Sub.applyAt t) c p eq = idle p eq
return-trace (Sub.setTargets t) c p eq = idle p eq
return-trace (Sub.selectMonitor delay) c p eq = idle p eq
return-trace Sub.selectCompletion c p eq = idle p eq
return-trace Sub.selectTargets c p eq = idle p eq
return-trace Sub.selectWakeup c p eq = idle p eq
return-trace Sub.registerWakeup c p eq = idle p eq
return-trace Sub.expireWakeup c p eq = idle p eq
return-trace Sub.cancelWakeup c p eq = idle p eq
return-trace Sub.publishCounters c p eq = idle p eq
return-trace Sub.traceSelection c p eq = idle p eq
return-trace (Sub.selectPolicy picked) c p eq = idle p eq
return-trace Sub.finishLaunch c p eq = idle p eq
return-trace (Sub.protocolResult ref n result) c p eq = idle p eq
return-trace (Sub.publishInitiatorResult ref i) c p eq = idle p eq
return-trace (Sub.pollPeer ref w) c p eq = idle p eq
return-trace (Sub.monitorStep ref a) c p eq = idle p eq
return-trace (Sub.monitorFinished ref) c p eq = idle p eq
return-trace (Sub.observeInitiatorFailure ref) c p eq = idle p eq

-- Cancellation delivery changes only the captured current pool thread.
deliver-trace : ∀ blocked err s {s′} → GP.deliver blocked err s ≡ just s′ → Trace (GP.pool s) (GP.pool s′)
deliver-trace blocked err s eq with Pool.phase (GP.pool s)
... | Pool.cancelPending j with lookup j (Sub.jobs (GP.machine s)) | Pool.step Pool.deliverCancel (GP.pool s) in delivered
...   | just jf | just p′ with Cancel.start (J.caller (Sub.execution jf)) err
    (GP.deliveryContext blocked (GP.region (J.caller (Sub.execution jf)) s)) (GP.cm s)
...     | just (f , c′) = case just-injective eq of λ { refl → one Pool.deliverCancel (GP.pool s) delivered }
...     | nothing = case eq of λ ()
deliver-trace blocked err s eq | Pool.cancelPending j | nothing | _ = case eq of λ ()
deliver-trace blocked err s eq | Pool.cancelPending j | just jf | nothing = case eq of λ ()
deliver-trace blocked err s eq | Pool.openPool = case eq of λ ()
deliver-trace blocked err s eq | Pool.closing = case eq of λ ()
deliver-trace blocked err s eq | Pool.closedPool = case eq of λ ()
deliver-trace blocked err s eq | (Pool.joinPending k) = case eq of λ ()

-- Every accepted coupled step has a real finite primitive pool projection.
step-projects : ∀ a s {s′} → GP.step a s ≡ just s′ → Trace (GP.pool s) (GP.pool s′)
step-projects (GP.run action) s eq with GP.normalPool action s in normal | GP.Production.step (Policy.dispatch action) (GP.source s)
... | just p′ | just c′ with GP.noteReturn action (Policy.machine c′) p′ in returned
...   | just p″ = case just-injective eq of λ { refl → compose (normal-trace action s normal) (return-trace action (Policy.machine c′) p′ returned) }
...   | nothing = case eq of λ ()
step-projects (GP.run action) s eq | nothing | _ = case eq of λ ()
step-projects (GP.run action) s eq | just p′ | nothing = case eq of λ ()
step-projects (GP.handoff w) s eq with GP.region w s | lookup w (CM.acquiring (GP.cm s))
... | Cancel.forkedBeforeHandoff | just f with A.pc f
...   | A.connectedCommit _ _ _ = case just-injective eq of λ { refl → [] , Pool.done }
step-projects (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | A.selecting = case eq of λ ()
step-projects (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.count next) = case eq of λ ()
step-projects (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.allocatePromise e) = case eq of λ ()
step-projects (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.openSocket e pid) = case eq of λ ()
step-projects (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.configureSocket e pid) = case eq of λ ()
step-projects (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.bindSocket e pid) = case eq of λ ()
step-projects (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.connectSocket e pid) = case eq of λ ()
step-projects (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.localAddress e pid) = case eq of λ ()
step-projects (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.updateAddress e pid key) = case eq of λ ()
step-projects (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.forkHandler e pid key) = case eq of λ ()
step-projects (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.awaitResult e pid key) = case eq of λ ()
step-projects (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.commitResult e key result) = case eq of λ ()
step-projects (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.waitingInbound e key) = case eq of λ ()
step-projects (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.closeError e err) = case eq of λ ()
step-projects (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.removeError e err) = case eq of λ ()
step-projects (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | just f | (A.complete result) = case eq of λ ()
step-projects (GP.handoff w) s eq | Cancel.forkedBeforeHandoff | nothing = case eq of λ ()
step-projects (GP.handoff w) s eq | Cancel.ordinary | _ = case eq of λ ()
step-projects (GP.handoff w) s eq | Cancel.protectedCleanup | _ = case eq of λ ()
step-projects (GP.handoff w) s eq | Cancel.interruptibleOpen | _ = case eq of λ ()
step-projects (GP.beginClose order) s eq with Pool.step (Pool.beginClose order) (GP.pool s) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → one (Pool.beginClose order) (GP.pool s) advanced }
step-projects GP.requestCancel s eq with Pool.step Pool.requestCancel (GP.pool s) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → one Pool.requestCancel (GP.pool s) advanced }
step-projects GP.join s eq with Pool.step Pool.join (GP.pool s) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → one Pool.join (GP.pool s) advanced }
step-projects GP.finishClose s eq with Pool.step Pool.finishClose (GP.pool s) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → one Pool.finishClose (GP.pool s) advanced }
step-projects (GP.publishAsyncResult j) s eq with Pool.step (Pool.publishAsyncResult j) (GP.pool s) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → one (Pool.publishAsyncResult j) (GP.pool s) advanced }
step-projects (GP.deliverCancellation err) s eq = deliver-trace false err s eq
step-projects (GP.deliverOpenCancellation err) s eq = deliver-trace true err s eq
step-projects (GP.cleanup j action) s eq with lookup j (GP.unwinding s)
... | nothing = case eq of λ ()
... | just f with Cancel.step action f (GP.cm s)
...   | nothing = case eq of λ ()
...   | just (f′ , c′) = case just-injective eq of λ { refl → [] , Pool.done }
step-projects (GP.bodyUnwound j) s eq with lookup j (GP.unwinding s) | lookup j (Sub.jobs (GP.machine s))
... | just f | just jf with Cancel.pc f
...   | Cancel.finished Cancel.abandoned with Pool.step (Pool.bodyUnwound j) (GP.pool s) in advanced
...     | just p′ = case just-injective eq of λ { refl → one (Pool.bodyUnwound j) (GP.pool s) advanced }
...     | nothing = case eq of λ ()
step-projects (GP.bodyUnwound j) s eq | just f | just jf | Cancel.finished Cancel.cleanupComplete with Pool.step (Pool.bodyUnwound j) (GP.pool s) in advanced
... | just p′ = case just-injective eq of λ { refl → one (Pool.bodyUnwound j) (GP.pool s) advanced }
... | nothing = case eq of λ ()
step-projects (GP.bodyUnwound j) s eq | just f | just jf | Cancel.cleaning active = case eq of λ ()
step-projects (GP.bodyUnwound j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) = case eq of λ ()
step-projects (GP.bodyUnwound j) s eq | nothing | _ = case eq of λ ()
step-projects (GP.bodyUnwound j) s eq | just f | nothing = case eq of λ ()
step-projects (GP.recoverCloseFailure j) s eq with lookup j (GP.unwinding s) | lookup j (Sub.jobs (GP.machine s))
... | just f | just jf with Cancel.pc f | Cancel.original f | J.pc (Sub.execution jf)
...   | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring _ | J.awaitAcquire with Pool.step (Pool.resumeAfterUnwindError j) (GP.pool s) in advanced
...     | just p′ = case just-injective eq of λ { refl → one (Pool.resumeAfterUnwindError j) (GP.pool s) advanced }
...     | nothing = case eq of λ ()
step-projects (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.cleaning active | _ | _ = case eq of λ ()
step-projects (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished Cancel.abandoned | _ | _ = case eq of λ ()
step-projects (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished Cancel.cleanupComplete | _ | _ = case eq of λ ()
step-projects (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.noCaller | _ = case eq of λ ()
step-projects (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.releasing active | _ = case eq of λ ()
step-projects (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.begin = case eq of λ ()
step-projects (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.startBundle t ns) = case eq of λ ()
step-projects (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.publishBundle t) = case eq of λ ()
step-projects (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.markWarm = case eq of λ ()
step-projects (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.forkMonitor = case eq of λ ()
step-projects (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.finishActivation = case eq of λ ()
step-projects (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.awaitHot = case eq of λ ()
step-projects (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.awaitAll = case eq of λ ()
step-projects (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.callRelease = case eq of λ ()
step-projects (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.awaitRelease = case eq of λ ()
step-projects (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.delayFailure = case eq of λ ()
step-projects (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.awaitCold result) = case eq of λ ()
step-projects (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.complete result) = case eq of λ ()
step-projects (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.acquirePolicy fault) = case eq of λ ()
step-projects (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.nodeDelivery fault) = case eq of λ ()
step-projects (GP.recoverCloseFailure j) s eq | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.nodeRethrow fault) = case eq of λ ()
step-projects (GP.recoverCloseFailure j) s eq | nothing | _ = case eq of λ ()
step-projects (GP.recoverCloseFailure j) s eq | just f | nothing = case eq of λ ()
step-projects (GP.deregisterCancelled j) s eq with lookup j (Sub.jobs (GP.machine s)) | Pool.step (Pool.deregister j) (GP.pool s) in advanced
... | just jf | just p′ with lookup j (Pool.handles (GP.pool s)) | one (Pool.deregister j) (GP.pool s) advanced
...   | just (Pool.deregisterPending Pool.cancelledExit) | projected = case just-injective eq of λ { refl → projected }
step-projects (GP.deregisterCancelled j) s eq | just jf | just p′ | nothing | _ = case eq of λ ()
step-projects (GP.deregisterCancelled j) s eq | just jf | just p′ | just Pool.bodyRunning | _ = case eq of λ ()
step-projects (GP.deregisterCancelled j) s eq | just jf | just p′ | just (Pool.bodyReturned result) | _ = case eq of λ ()
step-projects (GP.deregisterCancelled j) s eq | just jf | just p′ | just Pool.bodyUnwinding | _ = case eq of λ ()
step-projects (GP.deregisterCancelled j) s eq | just jf | just p′ | just (Pool.deregisterPending Pool.normalExit) | _ = case eq of λ ()
step-projects (GP.deregisterCancelled j) s eq | just jf | just p′ | just (Pool.deregistered ex) | _ = case eq of λ ()
step-projects (GP.deregisterCancelled j) s eq | just jf | just p′ | just (Pool.resultAvailable ex) | _ = case eq of λ ()
step-projects (GP.deregisterCancelled j) s eq | nothing | _ = case eq of λ ()
step-projects (GP.deregisterCancelled j) s eq | just jf | nothing = case eq of λ ()

-- Concatenate existential primitive traces across arbitrary finite interleavings.
exec-projects : ∀ {s actions s′} → GP.Executes s actions s′ → Trace (GP.pool s) (GP.pool s′)
exec-projects GP.done = [] , Pool.done
exec-projects (GP.next {s = s} {a = a} eq path) = compose (step-projects a s eq) (exec-projects path)

-- Closure certifies only this governor pool's captured Async handles. Actual
-- caller cleanup is in the coupled run; outer scopes and eventuality are absent.
from-initial : ∀ {c g actions s} → GP.Executes (GP.initial c g) actions s →
  Pool.phase (GP.pool s) ≡ Pool.closedPool →
  ∀ j → j ∈ Pool.snapshot (GP.pool s) → Close.Terminal (GP.pool s) j
from-initial path closed with exec-projects path
... | actions , projected = Close.from-initial projected closed
