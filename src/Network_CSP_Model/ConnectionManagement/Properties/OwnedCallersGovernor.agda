{-# OPTIONS --guardedness #-}

-- Physical governor operations preserve the additional no-foreign invariant.
-- The unchanged Reach proof remains responsible for live-handle ownership.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedCallersGovernor
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import ConnectionManagement.Domain using (ident)
open import ConnectionManagement.Store using (lookup; put; delete)
open import ConnectionManagement.Properties.OutboundKeys using (same-refl)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Rules.OutboundCases as Cases
import ConnectionManagement.Rules.ProductionPolicy as Policy
import ConnectionManagement.Properties.OwnedCallersBase as Base
import ConnectionManagement.Properties.OwnedCallersSubsystem as LogicalFacts
import ConnectionManagement.Properties.OwnedCallersCancel as CancelNF
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
import ConnectionManagement.Properties.OwnedFramesForkJob as ForkFacts
import ConnectionManagement.Properties.OwnedFramesCancel as CancelFacts
import ConnectionManagement.Properties.OwnedFramesUnwindSteps as UnwindFacts
open Base isBearerClosed isIOManagerError using
  (module PS; module GP; module C; PeerNF; same-source; copy-peer; job-update)
open Frames isBearerClosed isIOManagerError using (Inv)
private
  module L = LogicalFacts isBearerClosed isIOManagerError
  module D = CancelNF isBearerClosed isIOManagerError
  module X = Auxiliary isBearerClosed isIOManagerError
  module Fork = ForkFacts isBearerClosed isIOManagerError
  module Unwind = UnwindFacts isBearerClosed isIOManagerError

-- The peer path refuses raw subsystem core aliases; other governor actions stay.
allowed : GP.Action → Bool
allowed (GP.run a) = L.allowed a
allowed _ = true

-- The actual normalPool fork guard, rather than a job-supply assumption, is used.
fork-fresh : ∀ a s {p} → GP.normalPool a (PS.governor s) ≡ just p → L.ForkFresh a s
fork-fresh (Sub.forkJob w child sock) s eq with GP.ownerOpen (GP.pool (PS.governor s))
... | false = case eq of λ ()
... | true = Fork.pool-fresh (ident (Sub.nextJob (PS.machine s))) (GP.pool (PS.governor s)) eq
fork-fresh (Sub.core a) s eq = tt
fork-fresh Sub.publishPublicState s eq = tt
fork-fresh (Sub.sampleTime t) s eq = tt
fork-fresh (Sub.applyAt t) s eq = tt
fork-fresh (Sub.setTargets desired) s eq = tt
fork-fresh (Sub.selectMonitor delays) s eq = tt
fork-fresh Sub.selectCompletion s eq = tt
fork-fresh Sub.selectTargets s eq = tt
fork-fresh Sub.selectWakeup s eq = tt
fork-fresh Sub.registerWakeup s eq = tt
fork-fresh Sub.expireWakeup s eq = tt
fork-fresh Sub.cancelWakeup s eq = tt
fork-fresh Sub.publishCounters s eq = tt
fork-fresh Sub.traceSelection s eq = tt
fork-fresh (Sub.selectPolicy picked) s eq = tt
fork-fresh Sub.registerJob s eq = tt
fork-fresh Sub.finishLaunch s eq = tt
fork-fresh (Sub.jobStep j a) s eq = tt
fork-fresh (Sub.enqueueCompletion j delay) s eq = tt
fork-fresh (Sub.deregisterJob j) s eq = tt
fork-fresh (Sub.protocolResult ref n result) s eq = tt
fork-fresh (Sub.publishInitiatorResult ref n) s eq = tt
fork-fresh (Sub.pollPeer ref w) s eq = tt
fork-fresh (Sub.monitorStep ref a) s eq = tt
fork-fresh (Sub.monitorFinished ref) s eq = tt
fork-fresh (Sub.observeInitiatorFailure ref) s eq = tt

-- Production erasure exposes the actual logical step, and noteReturn/regions
-- do not alter the source frames, job callers or physical monitor workers.
run-safe : ∀ a s {g′} → L.allowed a ≡ true → GP.step (GP.run a) (PS.governor s) ≡ just g′ →
  Inv (PS.cm s) (C.capture s) → X.Aux (C.capture s) → PeerNF s → PeerNF (record s { governor = g′ })
run-safe a s ok eq inv aux held with GP.normalPool a (PS.governor s) in pooled |
  GP.Production.step (Policy.dispatch a) (GP.source (PS.governor s)) in dispatched
... | just p′ | just c′ with GP.noteReturn a (Policy.machine c′) p′
...   | nothing = case eq of λ ()
...   | just p″ with GP.Production.step-projects (Policy.dispatch a) (GP.source (PS.governor s)) dispatched
...     | Sub.next advanced Sub.done = case just-injective eq of λ { refl →
  L.sub-safe a s ok advanced (fork-fresh a s pooled) inv aux held }
run-safe a s ok eq inv aux held | nothing | _ = case eq of λ ()
run-safe a s ok eq inv aux held | just _ | nothing = case eq of λ ()

-- Delivery removes at most the cursor caller's frame and keeps ownership tables.
deliver-safe : ∀ blocked err s {g′} → GP.deliver blocked err (PS.governor s) ≡ just g′ →
  PeerNF s → PeerNF (record s { governor = g′ })
deliver-safe blocked err s eq held with GP.Pool.phase (GP.pool (PS.governor s))
... | GP.Pool.cancelPending j with lookup j (Sub.jobs (PS.machine s)) | GP.Pool.step GP.Pool.deliverCancel (GP.pool (PS.governor s))
...   | just jf | just p′ with Cancel.start (J.caller (Sub.execution jf)) err
  (GP.deliveryContext blocked (GP.region (J.caller (Sub.execution jf)) (PS.governor s))) (PS.cm s) in started
...     | nothing = case eq of λ ()
...     | just (f , c′) = case just-injective eq of λ { refl → D.start-nf (J.caller (Sub.execution jf)) err (GP.deliveryContext blocked (GP.region (J.caller (Sub.execution jf)) (PS.governor s))) (PS.cm s) started (C.capture s) held }
deliver-safe blocked err s eq held | GP.Pool.cancelPending j | nothing | _ = case eq of λ ()
deliver-safe blocked err s eq held | GP.Pool.cancelPending j | just _ | nothing = case eq of λ ()
deliver-safe blocked err s eq held | GP.Pool.openPool = case eq of λ ()
deliver-safe blocked err s eq held | GP.Pool.closing = case eq of λ ()
deliver-safe blocked err s eq held | GP.Pool.closedPool = case eq of λ ()
deliver-safe blocked err s eq held | (GP.Pool.joinPending j) = case eq of λ ()

-- Detached cleanup uses the already-proved key-preserving primitive effect.
cleanup-safe : ∀ j a s {g′} → GP.step (GP.cleanup j a) (PS.governor s) ≡ just g′ → PeerNF s → PeerNF (record s { governor = g′ })
cleanup-safe j a s eq held with lookup j (GP.unwinding (PS.governor s))
... | nothing = case eq of λ ()
... | just f with Cancel.step a f (PS.cm s) in cleaned
...   | nothing = case eq of λ ()
...   | just (f′ , c′) = case just-injective eq of λ { refl → same-source {k = C.capture s} (CancelFacts.cleanup-keys a f (PS.cm s) cleaned) held }

-- Restoring a peer's diagnostic state leaves caller tables unchanged.
restore-nf : ∀ f s → PeerNF s → PeerNF (record s { governor = record (PS.governor s)
  { source = record (GP.source (PS.governor s)) { machine = GP.restoreCold f (PS.machine s) } } })
restore-nf f s held = copy-peer s (record s { governor = record (PS.governor s) { source = record (GP.source (PS.governor s)) { machine = GP.restoreCold f (PS.machine s) } } }) (proj₁ effect) (proj₁ (proj₂ effect)) refl held
  where effect = Unwind.restore-effect f (PS.machine s)

-- Handoff changes only a region, outside all NoForeign observations.
handoff-safe : ∀ w s {g′} → GP.step (GP.handoff w) (PS.governor s) ≡ just g′ → PeerNF s → PeerNF (record s { governor = g′ })
handoff-safe w s eq held with GP.region w (PS.governor s) | lookup w (O.acquiring (PS.cm s))
... | Cancel.forkedBeforeHandoff | just f with A.pc f
...   | A.connectedCommit e promise key = case just-injective eq of λ { refl → held }
handoff-safe w s eq held | Cancel.forkedBeforeHandoff | just f | A.selecting = case eq of λ ()
handoff-safe w s eq held | Cancel.forkedBeforeHandoff | just f | (A.count next) = case eq of λ ()
handoff-safe w s eq held | Cancel.forkedBeforeHandoff | just f | (A.allocatePromise e) = case eq of λ ()
handoff-safe w s eq held | Cancel.forkedBeforeHandoff | just f | (A.openSocket e pid) = case eq of λ ()
handoff-safe w s eq held | Cancel.forkedBeforeHandoff | just f | (A.configureSocket e pid) = case eq of λ ()
handoff-safe w s eq held | Cancel.forkedBeforeHandoff | just f | (A.bindSocket e pid) = case eq of λ ()
handoff-safe w s eq held | Cancel.forkedBeforeHandoff | just f | (A.connectSocket e pid) = case eq of λ ()
handoff-safe w s eq held | Cancel.forkedBeforeHandoff | just f | (A.localAddress e pid) = case eq of λ ()
handoff-safe w s eq held | Cancel.forkedBeforeHandoff | just f | (A.updateAddress e pid key) = case eq of λ ()
handoff-safe w s eq held | Cancel.forkedBeforeHandoff | just f | (A.forkHandler e pid key) = case eq of λ ()
handoff-safe w s eq held | Cancel.forkedBeforeHandoff | just f | (A.awaitResult e pid key) = case eq of λ ()
handoff-safe w s eq held | Cancel.forkedBeforeHandoff | just f | (A.commitResult e key result) = case eq of λ ()
handoff-safe w s eq held | Cancel.forkedBeforeHandoff | just f | (A.waitingInbound e key) = case eq of λ ()
handoff-safe w s eq held | Cancel.forkedBeforeHandoff | just f | (A.closeError e err) = case eq of λ ()
handoff-safe w s eq held | Cancel.forkedBeforeHandoff | just f | (A.removeError e err) = case eq of λ ()
handoff-safe w s eq held | Cancel.forkedBeforeHandoff | just f | (A.complete result) = case eq of λ ()
handoff-safe w s eq held | Cancel.forkedBeforeHandoff | nothing = case eq of λ ()
handoff-safe w s eq held | Cancel.ordinary | _ = case eq of λ ()
handoff-safe w s eq held | Cancel.protectedCleanup | _ = case eq of λ ()
handoff-safe w s eq held | Cancel.interruptibleOpen | _ = case eq of λ ()


-- Physical unwind completion changes pool metadata and restores only peer state.
body-safe : ∀ j s {g′} → GP.step (GP.bodyUnwound j) (PS.governor s) ≡ just g′ → PeerNF s → PeerNF (record s { governor = g′ })
body-safe j s eq held with lookup j (GP.unwinding (PS.governor s)) | lookup j (Sub.jobs (PS.machine s))
... | just f | just jf with Cancel.pc f
...   | Cancel.finished Cancel.abandoned with GP.Pool.step (GP.Pool.bodyUnwound j) (GP.pool (PS.governor s)) in unwound
...     | just p′ = case just-injective eq of λ { refl → restore-nf (Sub.execution jf)
  (record s { governor = record (PS.governor s) { pool = p′ } })
  held }
...     | nothing = case eq of λ ()
body-safe j s eq held | just f | just jf | Cancel.finished Cancel.cleanupComplete with GP.Pool.step (GP.Pool.bodyUnwound j) (GP.pool (PS.governor s)) in unwound
... | just p′ = case just-injective eq of λ { refl → restore-nf (Sub.execution jf)
  (record s { governor = record (PS.governor s) { pool = p′ } })
  held }
... | nothing = case eq of λ ()
body-safe j s eq held | just f | just jf | Cancel.cleaning active = case eq of λ ()
body-safe j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) = case eq of λ ()
body-safe j s eq held | nothing | _ = case eq of λ ()
body-safe j s eq held | just f | nothing = case eq of λ ()


-- Recovery changes only a result cell and detached/pool metadata.
recovery-safe : ∀ j s {g′} → GP.step (GP.recoverCloseFailure j) (PS.governor s) ≡ just g′ → PeerNF s → PeerNF (record s { governor = g′ })
recovery-safe j s eq held with lookup j (GP.unwinding (PS.governor s)) in found | lookup j (Sub.jobs (PS.machine s))
... | just f | just jf with Cancel.pc f | Cancel.original f | J.pc (Sub.execution jf)
...   | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring _ | J.awaitAcquire with
  GP.Pool.step (GP.Pool.resumeAfterUnwindError j) (GP.pool (PS.governor s)) in resumed
...     | just p′ = case just-injective eq of λ { refl → held }
...     | nothing = case eq of λ ()
recovery-safe j s eq held | just f | just jf | Cancel.cleaning active | _ | _ = case eq of λ ()
recovery-safe j s eq held | just f | just jf | Cancel.finished Cancel.abandoned | _ | _ = case eq of λ ()
recovery-safe j s eq held | just f | just jf | Cancel.finished Cancel.cleanupComplete | _ | _ = case eq of λ ()
recovery-safe j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.noCaller | _ = case eq of λ ()
recovery-safe j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.releasing active | _ = case eq of λ ()
recovery-safe j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.begin = case eq of λ ()
recovery-safe j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.startBundle t ns) = case eq of λ ()
recovery-safe j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.publishBundle t) = case eq of λ ()
recovery-safe j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.markWarm = case eq of λ ()
recovery-safe j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.forkMonitor = case eq of λ ()
recovery-safe j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.finishActivation = case eq of λ ()
recovery-safe j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.awaitHot = case eq of λ ()
recovery-safe j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.awaitAll = case eq of λ ()
recovery-safe j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.callRelease = case eq of λ ()
recovery-safe j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.awaitRelease = case eq of λ ()
recovery-safe j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.delayFailure = case eq of λ ()
recovery-safe j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.awaitCold result) = case eq of λ ()
recovery-safe j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.complete result) = case eq of λ ()
recovery-safe j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.acquirePolicy fault) = case eq of λ ()
recovery-safe j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.nodeDelivery fault) = case eq of λ ()
recovery-safe j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.nodeRethrow fault) = case eq of λ ()
recovery-safe j s eq held | nothing | _ = case eq of λ ()
recovery-safe j s eq held | just f | nothing = case eq of λ ()


-- Cancelled deregistration retains the row's caller, changing only a flag.
cancelled-safe : ∀ j s {g′} → GP.step (GP.deregisterCancelled j) (PS.governor s) ≡ just g′ → PeerNF s → PeerNF (record s { governor = g′ })
cancelled-safe j s eq held with lookup j (Sub.jobs (PS.machine s)) in saved | GP.Pool.step (GP.Pool.deregister j) (GP.pool (PS.governor s))
... | just old | just p′ with lookup j (GP.Pool.handles (GP.pool (PS.governor s)))
...   | just (GP.Pool.deregisterPending GP.Pool.cancelledExit) = case just-injective eq of λ { refl →
  job-update (PS.cm s) (C.capture s) j old (record old { deregistered = true }) saved refl held }
cancelled-safe j s eq held | just old | just p′ | nothing = case eq of λ ()
cancelled-safe j s eq held | just old | just p′ | just GP.Pool.bodyRunning = case eq of λ ()
cancelled-safe j s eq held | just old | just p′ | just GP.Pool.bodyUnwinding = case eq of λ ()
cancelled-safe j s eq held | just old | just p′ | just (GP.Pool.bodyReturned result) = case eq of λ ()
cancelled-safe j s eq held | just old | just p′ | just (GP.Pool.deregisterPending GP.Pool.normalExit) = case eq of λ ()
cancelled-safe j s eq held | just old | just p′ | just (GP.Pool.deregistered exit) = case eq of λ ()
cancelled-safe j s eq held | just old | just p′ | just (GP.Pool.resultAvailable exit) = case eq of λ ()
cancelled-safe j s eq held | nothing | _ = case eq of λ ()
cancelled-safe j s eq held | just _ | nothing = case eq of λ ()

-- Every physical governor action retains the actual source guards.
governor-safe : ∀ a s {g′} → allowed a ≡ true → GP.step a (PS.governor s) ≡ just g′ →
  Inv (PS.cm s) (C.capture s) → X.Aux (C.capture s) → PeerNF s → PeerNF (record s { governor = g′ })
governor-safe (GP.run a) s ok eq inv aux held = run-safe a s ok eq inv aux held
governor-safe (GP.handoff w) s ok eq inv aux held = handoff-safe w s eq held
governor-safe (GP.deliverCancellation err) s ok eq inv aux held = deliver-safe false err s eq held
governor-safe (GP.deliverOpenCancellation err) s ok eq inv aux held = deliver-safe true err s eq held
governor-safe (GP.cleanup j a) s ok eq inv aux held = cleanup-safe j a s eq held
governor-safe (GP.bodyUnwound j) s ok eq inv aux held = body-safe j s eq held
governor-safe (GP.recoverCloseFailure j) s ok eq inv aux held = recovery-safe j s eq held
governor-safe (GP.deregisterCancelled j) s ok eq inv aux held = cancelled-safe j s eq held
governor-safe (GP.beginClose js) s ok eq inv aux held with GP.Pool.step (GP.Pool.beginClose js) (GP.pool (PS.governor s))
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → held }
governor-safe GP.requestCancel s ok eq inv aux held with GP.Pool.step GP.Pool.requestCancel (GP.pool (PS.governor s))
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → held }
governor-safe GP.join s ok eq inv aux held with GP.Pool.step GP.Pool.join (GP.pool (PS.governor s))
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → held }
governor-safe GP.finishClose s ok eq inv aux held with GP.Pool.step GP.Pool.finishClose (GP.pool (PS.governor s))
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → held }
governor-safe (GP.publishAsyncResult j) s ok eq inv aux held with GP.Pool.step (GP.Pool.publishAsyncResult j) (GP.pool (PS.governor s))
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → held }
