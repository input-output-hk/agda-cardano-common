{-# OPTIONS --guardedness #-}

-- Whole-CM content observers through actual governor and peer supervision.
-- IG tables and shared publication stores remain part of the observation.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.LiveTrackerContentPeers
 (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import Function using (case_of_)
open import ConnectionManagement.Domain using (WorkerId; HandleId)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.HandlerResourceFacts using (Facts; from-resources; to-resources)
open import ConnectionManagement.Properties.HandlerResources using (Resources; original)
import ConnectionManagement.Properties.HandlerResources as BirthResources
import ConnectionManagement.Properties.Entries as Entries
import ConnectionManagement.Properties.ServerPeersMonitorJoins as MonitorJoins
import ConnectionManagement.Properties.ServerPeers as SharedFacts
import ConnectionManagement.Rules.CM as InboundCM
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.MuxPublicationUnwind as PhysicalModel
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.HandlerSupervision as RawHandler
import ConnectionManagement.OutboundHandlerSupervision as OutboundHandler
open import ConnectionManagement.Domain using (EntryId; PromiseId; ident)
open import ConnectionManagement.Properties.Entries using (lookup-put)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as I
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Rules.ProductionPolicy as Policy
import ConnectionManagement.Rules.PeerActions as Peer
open import ConnectionManagement.IGTypes using (number)
import ConnectionManagement.Properties.SubsystemCapture as SubCapture
import ConnectionManagement.Properties.CallerCancellationCapture as CancelCapture
import ConnectionManagement.Properties.SubsystemResources as SubResources
import ConnectionManagement.Properties.OutboundAcquireResources as Acquire
import ConnectionManagement.Properties.CallerCancellation as Writer
import ConnectionManagement.Properties.GovernorPoolSupply as GovernorSupply
import ConnectionManagement.Properties.PeerSupervisionSupply as PeerLift
import ConnectionManagement.Properties.ServerIGExitInvariants as ServerResources
import ConnectionManagement.Properties.ServerIGExit as ExitFacts
import ConnectionManagement.Properties.OutboundRuntimeCapture as RuntimeCapture
import ConnectionManagement.Properties.OutboundCapture as FrameCapture
import ConnectionManagement.Properties.HandlerSupervision as RawFacts
open import ConnectionManagement.Properties.Counters using (lookup-all)
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.PeerContext as Context
import ConnectionManagement.PeerSupervision as Supervision
private
 module K = Combined isBearerClosed isIOManagerError
 module E = Exit isBearerClosed
 module PS = Supervision isIOManagerError
 module GP = PS.GP
 module Pool = GP.Pool
 module C = Context isIOManagerError
 module Gov = GovernorSupply isIOManagerError
 module SupplyLift = PeerLift isIOManagerError

import ConnectionManagement.Properties.PeerSupervisionCM as PeerCM
-- Whole-CM observers retain IG tables as well as shared promise contents.
module Observer
 (Q : CM.Configuration → Set)
 (raw-law : ∀ action s {t} → Sub.advance action s ≡ just t → Q (J.cm (Sub.world s)) → Q (J.cm (Sub.world t)))
 (cleanup-law : ∀ action f c {f′ c′} → Cancel.step action f c ≡ just (f′ , c′) → Q c → Q c′)
 (start-law : ∀ w err context c {f c′} → Cancel.start w err context c ≡ just (f , c′) → Q c → Q c′)
 (acquired-law : ∀ c acquired → Q c → Q (record c { acquired = acquired })) where
 Observe : CM.Configuration → Set
 Observe = Q
 RawValid : Sub.Configuration → Set
 RawValid c = Observe (J.cm (Sub.world c))
 module Raw = GP.Production.Lift RawValid raw-law
 Valid : GP.State → Set
 Valid s = Observe (GP.cm s)
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

 step-preserves : ∀ action s {s′} → GP.step action s ≡ just s′ → Valid s → Valid s′
 step-preserves (GP.run action) s eq valid with GP.normalPool action s | GP.Production.step (Policy.dispatch action) (GP.source s) in sourceStep
 ... | just p′ | just source′ with GP.noteReturn action (Policy.machine source′) p′
 ...   | just p″ = case just-injective eq of λ { refl → Raw.step-preserves (Policy.dispatch action) (GP.source s) sourceStep valid }
 ...   | nothing = case eq of λ ()
 step-preserves (GP.run action) s eq valid | nothing | _ = case eq of λ ()
 step-preserves (GP.run action) s eq valid | just p′ | nothing = case eq of λ ()
 step-preserves (GP.cleanup j action) s eq valid with lookup j (GP.unwinding s)
 ... | nothing = case eq of λ ()
 ... | just f with Cancel.step action f (GP.cm s) in cleaned
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , c′) = case just-injective eq of λ { refl → cleanup-law action f (GP.cm s) cleaned valid }
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
 ...     | just p′ = case just-injective eq of λ { refl → acquired-law (GP.cm s) _ valid }
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



 -- Peer scope/monitor bookkeeping reuses the same observer proof as supply.
 module Peers = PeerCM.Lift isIOManagerError Observe step-preserves start-law

import ConnectionManagement.MuxProtocolJobs as ProtocolModel
import ConnectionManagement.Properties.LiveTrackerFrameContent as Frames
import ConnectionManagement.Properties.SubsystemWorldInvariant as SubWorld
import ConnectionManagement.Properties.OutboundAcquireEffects as AcquireEffects
import ConnectionManagement.Properties.SharedStateEffects as Effects
import ConnectionManagement.Properties.IGTableRetention as Table
import ConnectionManagement.Properties.HandlerAnchors as Anchors
import ConnectionManagement.Rules.IGRegistration as IG

module For (worker : WorkerId) (frame : ProtocolModel.U.Frame) where
 module Fixed = Frames.Fixed worker frame
 Observe : CM.Configuration → Set
 Observe c = Fixed.Predicate (I.world (CM.core c)) (I.inboundGovernor (CM.core c))
 module Subsystem = SubWorld.Lift Fixed.Predicate Fixed.advance-preserves
   (λ tables → Fixed.stable (record
     { handlersRetained = λ _ _ found → found; resultsRetained = λ _ _ found → found
     ; entriesRetained = λ _ found → found; socketsRetained = λ _ found → found }) tables)
 cleanup-preserves : ∀ action f c {f′ c′} → Cancel.step action f c ≡ just (f′ , c′) → Observe c → Observe c′
 cleanup-preserves action f c actual valid with Writer.step-writer action f c actual
 ... | Writer.writer active active′ shared′ before source frameEq machineEq = subst Observe (sym machineEq)
   (Fixed.stable
     (Effects.to-retains (AcquireEffects.step-effects (Cancel.caller f) (I.responder (CM.core c))
       (Cancel.acquireAction action) active (I.world (CM.core c)) source))
     (Table.from-anchors (Anchors.anchors-refl _)) valid)
 start-preserves : ∀ w err context c {f c′} → Cancel.start w err context c ≡ just (f , c′) → Observe c → Observe c′
 start-preserves w err context c actual valid = subst
   (λ core → Fixed.Predicate (I.world core) (I.inboundGovernor core))
   (sym (Writer.start-core w err context c actual)) valid
 module Lift = Observer Observe Subsystem.advance-preserves cleanup-preserves start-preserves (λ c acquired valid → valid)
 preserves : ∀ a s {t} → PS.step a s ≡ just t → Frames.Content worker frame (PS.cm s) → Frames.Content worker frame (PS.cm t)
 preserves a s {t} actual valid = Frames.Fixed.from worker frame (PS.cm t)
   (Lift.Peers.step-preserves a s actual (Frames.Fixed.to worker frame (PS.cm s) valid))
