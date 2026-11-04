{-# OPTIONS --guardedness #-}

-- Fixed historical handler resources through the real shared frontend. Socket
-- presence does not assert live ownership, map membership or eventual shutdown.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerPeersHandlerResources
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
 module Lift = PeerLift isIOManagerError

-- Lift any predicate of the active acquisition runtime and shared world.
-- Metadata cases are shared by fixed resources and capture-only preservation.
module Observer
 (Q : A.Runtime → S.State → Set)
 (raw-law : ∀ action s {t} → Sub.advance action s ≡ just t →
   Q (CM.acquiring (J.cm (Sub.world s))) (I.world (CM.core (J.cm (Sub.world s)))) →
   Q (CM.acquiring (J.cm (Sub.world t))) (I.world (CM.core (J.cm (Sub.world t)))))
 (cleanup-law : ∀ action f c {f′ c′} → Cancel.step action f c ≡ just (f′ , c′) →
   Q (CM.acquiring c) (I.world (CM.core c)) → Q (CM.acquiring c′) (I.world (CM.core c′)))
 (start-law : ∀ w err context c {f c′} → Cancel.start w err context c ≡ just (f , c′) →
   Q (CM.acquiring c) (I.world (CM.core c)) → Q (CM.acquiring c′) (I.world (CM.core c′)))
 (server-law : ∀ action s {t} → E.step action s ≡ just t →
   Q (CM.acquiring (E.source s)) (I.world (CM.core (E.source s))) →
   Q (CM.acquiring (E.source t)) (I.world (CM.core (E.source t)))) where
 Observe : CM.Configuration → Set
 Observe c = Q (CM.acquiring c) (I.world (CM.core c))
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
 ...     | just p′ = case just-injective eq of λ { refl → valid }
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
 Predicate : Lift.View → Set
 Predicate (runtime , world , _) = Q runtime world
 module Peers = Lift.Lift Predicate step-preserves

 Shared : K.State → Set
 Shared s = Observe (K.source s)
 shared-step : ∀ action s {t} → K.step action s ≡ just t → Shared s → Shared t
 shared-step (K.serverStep a) s eq valid with K.serverAllowed a s
 ... | false = case eq of λ ()
 ... | true with E.step a (K.server s) in advanced
 ...   | nothing = case eq of λ ()
 ...   | just e = case just-injective eq of λ { refl → server-law a (K.server s) advanced valid }
 shared-step (K.peerStep a) s eq valid with K.peerOpen s ∧ K.peerAllowed a s
 ... | false = case eq of λ ()
 ... | true with PS.step a (K.peers s) in advanced
 ...   | nothing = case eq of λ ()
 ...   | just p = case just-injective eq of λ { refl → Peers.step-preserves a (K.peers s) advanced valid }
 shared-step (K.coreStep a) s eq valid with K.coreAllowed a s
 ... | false = case eq of λ ()
 ... | true with E.step (K.coreAction a) (K.server s) in advanced
 ...   | nothing = case eq of λ ()
 ...   | just e = case just-injective eq of λ { refl → server-law (K.coreAction a) (K.server s) advanced valid }

 module Frontend (canInitiate : HandleId → ℕ → Bool) where
  private module T = K.Protocols canInitiate
  Holds : T.Runtime → Set
  Holds s = Shared (T.base s)
  cache-preserves : ∀ rid r result f b → Shared b → Shared (T.cacheResult rid r result f b)
  cache-preserves rid r result f b valid with T.latest (T.owner r) (number (T.descriptor r)) (T.calls f)
  ... | nothing = valid
  ... | just (current , _) with current ≟ rid
  ...   | no _ = valid
  ...   | yes _ with lookup (T.peerRef r) (C.SubContext.peers (C.subsystem (K.context b)))
  ...     | nothing = valid
  ...     | just peer with Peer.handleRef peer ≟ T.handleRef r | Peer.muxRef peer ≟ T.mux r
  ...       | yes _ | yes _ with Peer.finishRun (number (T.descriptor r)) result (Peer.runs peer)
  ...         | nothing = valid
  ...         | just rs = valid
  cache-preserves rid r result f b valid | just (current , _) | yes _ | just peer | no _ | _ = valid
  cache-preserves rid r result f b valid | just (current , _) | yes _ | just peer | yes _ | no _ = valid
  enact-preserves : ∀ plan s {t} → T.enact plan s ≡ just t → Holds s → Holds t
  enact-preserves (T.inherit a f) s eq valid with K.step a (T.base s) in advanced
  ... | nothing = case eq of λ ()
  ... | just b = case just-injective eq of λ { refl → shared-step a (T.base s) advanced valid }
  enact-preserves (T.caller a f) s eq valid with PS.step a (K.peers (T.base s)) in advanced
  ... | nothing = case eq of λ ()
  ... | just p = case just-injective eq of λ { refl → Peers.step-preserves a (K.peers (T.base s)) advanced valid }
  enact-preserves (T.local f) s eq valid = case just-injective eq of λ { refl → valid }
  enact-preserves (T.reading r) s eq valid = case just-injective eq of λ { refl → valid }
  enact-preserves (T.traceFault w rid result fs) s eq valid = case just-injective eq of λ { refl → valid }
  enact-preserves (T.deliverTraceFault w rid result fs coordinator) s eq valid = case just-injective eq of λ { refl → valid }
  enact-preserves (T.birth w capturedFrame pool j rid r f) s eq valid = case just-injective eq of λ { refl → valid }
  enact-preserves (T.complete a rid r result) s eq valid with K.step a (T.base s) in advanced
  ... | nothing = case eq of λ ()
  ... | just b = case just-injective eq of λ { refl → cache-preserves rid r result (T.front s) b (shared-step a (T.base s) advanced valid) }
  advance-preserves : ∀ event s {t} → T.advance event s ≡ just t → Holds s → Holds t
  advance-preserves event s eq valid with T.choose event s
  ... | nothing = case eq of λ ()
  ... | just plan = enact-preserves plan s eq valid
  run-preserves : ∀ {s events t} → T.Runs s events t → Holds s → Holds t
  run-preserves T.stop valid = valid
  run-preserves (T.more {s = s} {a = a} eq rest) valid = run-preserves rest (advance-preserves a s eq valid)

-- The original fixed-resource API specializes the shared observer lift.
module For (q : WorkerId) (captured : S.HandlerStart) where
 cleanup-preserves : ∀ action f c {f′ c′} → Cancel.step action f c ≡ just (f′ , c′) →
   Facts q captured (I.world (CM.core c)) → Facts q captured (I.world (CM.core c′))
 cleanup-preserves action f c eq valid with Writer.step-writer action f c eq
 ... | Writer.writer active active′ shared′ before source frameEq machineEq = subst
   (λ out → Facts q captured (I.world (CM.core out))) (sym machineEq)
   (Acquire.For.step-retains q captured (Cancel.caller f) (I.responder (CM.core c))
     (Cancel.acquireAction action) active (I.world (CM.core c)) valid source)

 start-preserves : ∀ w err context c {f c′} → Cancel.start w err context c ≡ just (f , c′) →
   Facts q captured (I.world (CM.core c)) → Facts q captured (I.world (CM.core c′))
 start-preserves w err context c actual valid = subst (λ core → Facts q captured (I.world core))
   (sym (Writer.start-core w err context c actual)) valid
 open Observer (λ _ world → Facts q captured world)
   (SubResources.For.advance-preserves q captured) cleanup-preserves start-preserves
   (ServerResources.For.step-preserves isBearerClosed q captured) public

-- Cancellation removes an active caller but retains every remaining capture.
-- Its detached interpreter needs no supply/validity premise for that retention.
module Captures where
 start-preserves : ∀ w err context c {f c′} → Cancel.start w err context c ≡ just (f , c′) →
   RuntimeCapture.Captures c → RuntimeCapture.Captures c′
 start-preserves w err context c actual valid = proj₁ (CancelCapture.start-valid w err context c actual valid)
 open Observer RuntimeCapture.RuntimeValid SubCapture.advance-preserves CancelCapture.step-runtime
   start-preserves (ServerResources.captures-step isBearerClosed) public

-- A successful promise-allocation step exposes the actual new cell and next PC.
allocated-frame : ∀ w req heldLease c {c′} →
 lookup w (S.admissions (I.world c)) ≡ just (S.admissionWorker req (S.prepare heldLease)) →
 I.advance (I.admissionStep w Admission.allocatePromise) c ≡ just c′ →
 lookup w (S.admissions (I.world c′)) ≡
   just (S.admissionWorker req (S.selectEntry heldLease (ident (S.nextPromise (I.world c))))) ×
 (ident (S.nextPromise (I.world c))) ∈ S.promises (I.world c′)
allocated-frame w req heldLease c found actual rewrite found with just-injective actual
... | refl = lookup-put w _ (S.admissions (I.world c)) , here refl

-- The successful source fork establishes this exact descriptor and socket row.
fork-facts : ∀ w req heldLease promise entry c {c′} →
 lookup w (S.admissions (I.world c)) ≡ just (S.admissionWorker req (S.forkHandler heldLease promise entry)) →
 Entries.Present entry (S.entries (S.cm (I.world c))) →
 I.advance (I.admissionStep w Admission.fork) c ≡ just c′ →
 Facts (S.child req) (S.handlerStart entry (S.socketRef req) promise (S.key req)) (I.world c′)
fork-facts w req heldLease promise entry c found present actual rewrite found
 with lookup (S.child req) (S.handlers (I.world c)) | lookup (S.child req) (S.admissions (I.world c))
... | just _ | _ = case actual of λ ()
... | nothing | just _ = case actual of λ ()
... | nothing | nothing with just-injective actual
...   | refl = lookup-put (S.child req) _ (S.handlers (I.world c)) , present ,
 (_ , lookup-put (S.socketRef req) (S.handling (S.child req)) (S.sockets (I.world c)))

-- The real selection/fork pair derives entry and socket presence, with no
-- supplied Resources, heap-coherence, supply or ownership certificate.
selected-fork-facts : ∀ w req heldLease promise c {selected born} →
 lookup w (S.admissions (I.world c)) ≡ just (S.admissionWorker req (S.selectEntry heldLease promise)) →
 I.advance (I.admissionStep w Admission.chooseEntry) c ≡ just selected →
 I.advance (I.admissionStep w Admission.fork) selected ≡ just born →
 Σ EntryId (λ entry → Facts (S.child req) (S.handlerStart entry (S.socketRef req) promise (S.key req)) (I.world born))
selected-fork-facts w req heldLease promise c found chosen forked rewrite found
 with InboundCM.selectInbound heldLease req (S.cm (I.world c)) in choice
... | nothing = case chosen of λ ()
... | just InboundCM.denied with just-injective chosen
...   | refl rewrite lookup-put w (S.admissionWorker req (S.reject heldLease S.forbidden)) (S.admissions (I.world c)) = case forked of λ ()
selected-fork-facts w req heldLease promise c found chosen forked | just (InboundCM.selected entry cm′) with just-injective chosen
... | refl = entry , fork-facts w req heldLease promise entry next selectedPC present forked
 where
 next = I.replaceWorld c (Admission.setPC w (S.admissionWorker req (S.selectEntry heldLease promise)) (S.forkHandler heldLease promise entry) (record (I.world c) { cm = cm′ }))
 selectedPC = lookup-put w (S.admissionWorker req (S.forkHandler heldLease promise entry)) (S.admissions (I.world c))
 present = BirthResources.selected-exists heldLease req (S.cm (I.world c)) choice

-- Outbound allocation and fork expose exact source references without assuming
-- a Resources certificate. Entry existence comes from acquisition captures.
outbound-allocated-frame : ∀ caller req entry c {c′} →
 lookup caller (CM.acquiring c) ≡ just (A.frame req (A.allocatePromise entry)) →
 CM.advance (CM.acquire caller A.newPromise) c ≡ just c′ →
 lookup caller (CM.acquiring c′) ≡ just (A.frame req (A.openSocket entry (ident (S.nextPromise (I.world (CM.core c)))))) ×
 ident (S.nextPromise (I.world (CM.core c))) ∈ S.promises (I.world (CM.core c′))
outbound-allocated-frame caller req entry c owned actual rewrite owned
 with lookup (ident (S.nextPromise (I.world (CM.core c)))) (S.handshakeResults (I.world (CM.core c)))
... | just _ = case actual of λ ()
... | nothing with just-injective actual
...   | refl = lookup-put caller _ (CM.acquiring c) , here refl

outbound-fork-facts : ∀ caller req entry promise key c {c′} →
 lookup caller (CM.acquiring c) ≡ just (A.frame req (A.forkHandler entry promise key)) →
 Entries.Present entry (S.entries (S.cm (I.world (CM.core c)))) →
 CM.advance (CM.acquire caller A.forkOK) c ≡ just c′ →
 Facts (A.child req) (S.handlerStart entry (A.socketRef req) promise key) (I.world (CM.core c′))
outbound-fork-facts caller req entry promise key c owned present actual rewrite owned
 with lookup (A.child req) (S.handlers (I.world (CM.core c)))
... | just _ = case actual of λ ()
... | nothing with just-injective actual
...   | refl = lookup-put (A.child req) _ (S.handlers (I.world (CM.core c))) , present ,
 (_ , lookup-put (A.socketRef req) (S.handling (A.child req)) (S.sockets (I.world (CM.core c))))

module Frontend (canInitiate : HandleId → ℕ → Bool) where
 private
  module T = K.Protocols canInitiate
  module ServerModel = Server isBearerClosed
  module Certificates = MonitorJoins isBearerClosed isIOManagerError
  module Joins = Certificates.Frontend canInitiate
  module N = PhysicalModel isBearerClosed
  module W = N.W
  module Group = W.G
  module Monitor = Group.M
  module Jobs = Group.P
  module Mux = Jobs.U
 shared : T.Runtime → S.State
 shared state = I.world (CM.core (K.source (T.base state)))
 core : T.Runtime → I.Configuration
 core state = CM.core (K.source (T.base state))
 event : WorkerId → Admission.AdmissionAction → T.Event
 event w action = T.dispatch (K.serverStep (E.run (ServerModel.run (ServerModel.runMachine (I.admissionStep w action)))))

 -- Each layer exposes its enabled inherited operation with its own guard.
 physical-inherited : ∀ action s {t} → W.step (W.run action) s ≡ just t →
   Group.step action (W.base s) ≡ just (W.base t)
 physical-inherited action s eq with W.delegateAllowed action
 ... | false = case eq of λ ()
 ... | true with Group.step action (W.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → refl }
 group-inherited : ∀ action s {t} → Group.step (Group.run action) s ≡ just t →
   Monitor.step action (Group.base s) ≡ just (Group.base t)
 group-inherited action s eq with Group.delegateAllowed action s
 ... | false = case eq of λ ()
 ... | true with Monitor.step action (Group.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → refl }
 monitor-inherited : ∀ action s {t} → Monitor.step (Monitor.run action) s ≡ just t →
   Jobs.step action (Monitor.base s) ≡ just (Monitor.base t)
 monitor-inherited action s eq with Monitor.delegateAllowed action s
 ... | false = case eq of λ ()
 ... | true with Jobs.step action (Monitor.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → refl }
 jobs-inherited : ∀ action s {t} → Jobs.step (Jobs.run action) s ≡ just t →
   Mux.step action (Jobs.base s) ≡ just (Jobs.base t)
 jobs-inherited action s eq with Jobs.inheritedAllowed action
 ... | false = case eq of λ ()
 ... | true with Mux.step action (Jobs.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → refl }

 -- Birth adds provenance metadata but does not replace the physical source.
 birth-base : ∀ birth s → Mux.base (Mux.noteBirth birth s) ≡ Mux.base s
 birth-base nothing s = refl
 birth-base (just _) s = refl
 mux-inherited : ∀ action s {t} → Mux.step (Mux.run action) s ≡ just t →
   OutboundHandler.step action (Mux.base s) ≡ just (Mux.base t)
 mux-inherited action s eq with Mux.baseAllowed action s ∧ Mux.birthFresh (Mux.birth action (Mux.base s)) (Mux.origins s)
 ... | false = case eq of λ ()
 ... | true with OutboundHandler.step action (Mux.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl →
   cong just (sym (birth-base (Mux.birth action (Mux.base s)) (record s { base = next }))) }
 outbound-inherited : ∀ action s {t} → OutboundHandler.step (OutboundHandler.handler action) s ≡ just t →
   RawHandler.step action (OutboundHandler.view s) ≡ just (OutboundHandler.view t)
 outbound-inherited action s eq with OutboundHandler.handlerAllowed action s
 ... | false = case eq of λ ()
 ... | true with RawHandler.step action (OutboundHandler.view s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → refl }

 raw-view : T.Runtime → RawHandler.State
 raw-view state = OutboundHandler.view (Mux.base (Jobs.base (Monitor.base (Group.base (W.base (Joins.physical state))))))
 raw-action : WorkerId → Admission.AdmissionAction → W.Action
 raw-action w action = W.run (Group.run (Monitor.run (Jobs.run (Mux.run (OutboundHandler.handler (RawHandler.run (I.admissionStep w action)))))))
 handler-lower : ∀ w action s {t} → T.advance (event w action) s ≡ just t →
   RawHandler.step (RawHandler.run (I.admissionStep w action)) (raw-view s) ≡ just (raw-view t)
 handler-lower w action s actual = outbound-inherited hAction b
   (mux-inherited bAction u (jobs-inherited uAction p (monitor-inherited pAction m
     (group-inherited mAction g (physical-inherited gAction x
       (Joins.physical-lower (raw-action w action) s actual))))))
   where
   hAction = RawHandler.run (I.admissionStep w action)
   bAction = OutboundHandler.handler hAction
   uAction = Mux.run bAction
   pAction = Jobs.run uAction
   mAction = Monitor.run pAction
   gAction = Group.run mAction
   x = Joins.physical s
   g = W.base x
   m = Group.base g
   p = Monitor.base m
   u = Jobs.base p
   b = Mux.base u

 dispatch-lower : ∀ action s {t} → RawHandler.dispatch action s ≡ just t →
   I.advance action (RawHandler.source s) ≡ just (RawHandler.source t)
 dispatch-lower action s eq with I.advance action (RawHandler.source s) in actual
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → refl }

 -- Fork also registers a physical thread. Retain the primitive computation
 -- behind a record boundary so lookup case splits do not rewrite its identity.
 record ForkObservation (w : WorkerId) (before after : RawHandler.State) : Set where
  field
   returnedCore : I.Configuration
   primitiveStep : I.advance (I.admissionStep w Admission.fork) (RawHandler.source before) ≡ just returnedCore
   sourceShape : RawHandler.source after ≡ returnedCore
 observe-fork : ∀ w s {t} → RawHandler.forkAdmission w s ≡ just t → ForkObservation w s t
 observe-fork w s eq with lookup w (S.admissions (I.world (RawHandler.source s)))
 ... | nothing = case eq of λ ()
 ... | just request with lookup (S.child (S.request request)) (RawHandler.threads s)
 ...   | just previous = case eq of λ ()
 ...   | nothing with I.advance (I.admissionStep w Admission.fork) (RawHandler.source s) in actual
 ...     | nothing = case eq of λ ()
 ...     | just next with lookup (S.child (S.request request)) (S.handlers (I.world next))
 ...       | nothing = case eq of λ ()
 ...       | just captured = record
   { returnedCore = next; primitiveStep = actual
   ; sourceShape = cong RawHandler.source (sym (just-injective eq)) }
 fork-handler-lower : ∀ w s {t} → RawHandler.forkAdmission w s ≡ just t →
   I.advance (I.admissionStep w Admission.fork) (RawHandler.source s) ≡ just (RawHandler.source t)
 fork-handler-lower w s eq = trans (ForkObservation.primitiveStep observation)
   (cong just (sym (ForkObservation.sourceShape observation)))
   where observation = observe-fork w s eq

 allocation-lower : ∀ w s {t} → T.advance (event w Admission.allocatePromise) s ≡ just t →
   I.advance (I.admissionStep w Admission.allocatePromise) (core s) ≡ just (core t)
 allocation-lower w s actual = dispatch-lower (I.admissionStep w Admission.allocatePromise) (raw-view s)
   (handler-lower w Admission.allocatePromise s actual)
 selection-lower : ∀ w s {t} → T.advance (event w Admission.chooseEntry) s ≡ just t →
   I.advance (I.admissionStep w Admission.chooseEntry) (core s) ≡ just (core t)
 selection-lower w s actual = dispatch-lower (I.admissionStep w Admission.chooseEntry) (raw-view s)
   (handler-lower w Admission.chooseEntry s actual)
 fork-lower : ∀ w s {t} → T.advance (event w Admission.fork) s ≡ just t →
   I.advance (I.admissionStep w Admission.fork) (core s) ≡ just (core t)
 fork-lower w s actual = fork-handler-lower w (raw-view s) (handler-lower w Admission.fork s actual)

 -- Common acquisition calls have their own guarded frontend dispatch route.
 data AcquisitionCall : Set where
  beginCall : WorkerId → A.Request → AcquisitionCall
  acquireCall : WorkerId → A.Action → AcquisitionCall
 command : AcquisitionCall → CM.Action
 command (beginCall caller req) = CM.beginAcquire caller req
 command (acquireCall caller action) = CM.acquire caller action
 call-event : AcquisitionCall → T.Event
 call-event action = T.dispatch (K.coreStep (command action))
 outbound-physical-action : CM.Action → W.Action
 outbound-physical-action action = W.run (Group.run (Monitor.run (Jobs.run (Mux.run (OutboundHandler.outbound action)))))
 call-shape : ∀ action → K.coreAction (command action) ≡ Joins.handler-action (outbound-physical-action (command action))
 call-shape (beginCall caller req) = refl
 call-shape (acquireCall caller action) = refl

 core-delegated : ∀ action s {t} → T.advance (T.dispatch (K.coreStep action)) s ≡ just t →
   E.step (K.coreAction action) (K.server (T.base s)) ≡ just (K.server (T.base t))
 core-delegated action s eq with SharedFacts.Protocols.dispatch-observation isBearerClosed isIOManagerError canInitiate (K.coreStep action) s eq
 ... | b , advanced , same with same
 ...   | refl with K.coreAllowed action (T.base s)
 ...     | false = case advanced of λ ()
 ...     | true with E.step (K.coreAction action) (K.server (T.base s)) in actual
 ...       | nothing = case advanced of λ ()
 ...       | just next = case just-injective advanced of λ { refl → refl }
 call-physical-lower : ∀ action s {t} → T.advance (call-event action) s ≡ just t →
   W.step (outbound-physical-action (command action)) (Joins.physical s) ≡ just (Joins.physical t)
 call-physical-lower action s {t} actual = Joins.network-physical (outbound-physical-action (command action))
   (ServerModel.base (E.base (K.server (T.base s))))
   (Joins.ig-network _ (K.server (T.base s))
     (subst (λ a → E.step a (K.server (T.base s)) ≡ just _) (call-shape action) (core-delegated (command action) s actual)))

 outbound-view : T.Runtime → OutboundHandler.State
 outbound-view state = Mux.base (Jobs.base (Monitor.base (Group.base (W.base (Joins.physical state)))))
 call-base-lower : ∀ action s {t} → T.advance (call-event action) s ≡ just t →
   OutboundHandler.step (OutboundHandler.outbound (command action)) (outbound-view s) ≡ just (outbound-view t)
 call-base-lower action s actual = mux-inherited bAction u (jobs-inherited uAction p
   (monitor-inherited pAction m (group-inherited mAction g (physical-inherited gAction x (call-physical-lower action s actual)))))
   where
   bAction = OutboundHandler.outbound (command action)
   uAction = Mux.run bAction
   pAction = Jobs.run uAction
   mAction = Monitor.run pAction
   gAction = Group.run mAction
   x = Joins.physical s
   g = W.base x
   m = Group.base g
   p = Monitor.base m
   u = Jobs.base p

 record OutboundForkObservation (caller : WorkerId) (before after : OutboundHandler.State) : Set where
  field
   returnedSource : CM.Configuration
   primitiveStep : CM.advance (CM.acquire caller A.forkOK) (OutboundHandler.source before) ≡ just returnedSource
   sourceShape : OutboundHandler.source after ≡ returnedSource
 observe-outbound-fork : ∀ caller s {t} → OutboundHandler.forkOutbound caller s ≡ just t → OutboundForkObservation caller s t
 observe-outbound-fork caller s eq with lookup caller (CM.acquiring (OutboundHandler.source s))
 ... | nothing = case eq of λ ()
 ... | just activeFrame with OutboundHandler.freshChild (A.child (A.req activeFrame)) s
 ...   | false = case eq of λ ()
 ...   | true with CM.advance (CM.acquire caller A.forkOK) (OutboundHandler.source s) in actual
 ...     | nothing = case eq of λ ()
 ...     | just next with lookup (A.child (A.req activeFrame)) (S.handlers (I.world (CM.core next)))
 ...       | nothing = case eq of λ ()
 ...       | just captured = record
   { returnedSource = next; primitiveStep = actual
   ; sourceShape = cong OutboundHandler.source (sym (just-injective eq)) }
 outbound-fork-lower : ∀ caller s {t} → OutboundHandler.forkOutbound caller s ≡ just t →
   CM.advance (CM.acquire caller A.forkOK) (OutboundHandler.source s) ≡ just (OutboundHandler.source t)
 outbound-fork-lower caller s eq = trans (OutboundForkObservation.primitiveStep observation)
   (cong just (sym (OutboundForkObservation.sourceShape observation)))
   where observation = observe-outbound-fork caller s eq
 dispatch-outbound-lower : ∀ action s {t} → OutboundHandler.dispatchOutbound action s ≡ just t →
   CM.advance action (OutboundHandler.source s) ≡ just (OutboundHandler.source t)
 dispatch-outbound-lower action s eq with OutboundHandler.outboundAllowed action s
 ... | false = case eq of λ ()
 ... | true with CM.advance action (OutboundHandler.source s)
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → refl }

 -- Reflect the executable fork recognizer, rather than assuming a raw plan.
 fork-caller-reflect : ∀ action caller → OutboundHandler.forkCaller action ≡ just caller → action ≡ CM.acquire caller A.forkOK
 fork-caller-reflect (CM.acquire caller A.forkOK) other eq = cong (λ w → CM.acquire w A.forkOK) (just-injective eq)
 fork-caller-reflect (CM.acquire caller (A.select choice)) other ()
 fork-caller-reflect (CM.acquire caller (A.readCounters)) other ()
 fork-caller-reflect (CM.acquire caller (A.newPromise)) other ()
 fork-caller-reflect (CM.acquire caller (A.openOK)) other ()
 fork-caller-reflect (CM.acquire caller (A.configureOK)) other ()
 fork-caller-reflect (CM.acquire caller (A.bindOK)) other ()
 fork-caller-reflect (CM.acquire caller (A.connectOK)) other ()
 fork-caller-reflect (CM.acquire caller (A.gotLocal address)) other ()
 fork-caller-reflect (CM.acquire caller (A.updateLocalAddress)) other ()
 fork-caller-reflect (CM.acquire caller (A.commitConnected)) other ()
 fork-caller-reflect (CM.acquire caller (A.readResult)) other ()
 fork-caller-reflect (CM.acquire caller (A.commitHandshake)) other ()
 fork-caller-reflect (CM.acquire caller (A.returnResult)) other ()
 fork-caller-reflect (CM.acquire caller (A.failIO err)) other ()
 fork-caller-reflect (CM.acquire caller (A.closeFailed err)) other ()
 fork-caller-reflect (CM.acquire caller (A.closeOK)) other ()
 fork-caller-reflect (CM.acquire caller (A.removeReservation)) other ()
 fork-caller-reflect (CM.acquire caller (A.waitNegotiated)) other ()
 fork-caller-reflect (CM.inbound action) other ()
 fork-caller-reflect (CM.beginAcquire caller req) other ()
 fork-caller-reflect (CM.beginRelease caller key) other ()
 fork-caller-reflect (CM.release caller action) other ()
 outbound-source-lower : ∀ action s {t} → OutboundHandler.step (OutboundHandler.outbound action) s ≡ just t →
   CM.advance action (OutboundHandler.source s) ≡ just (OutboundHandler.source t)
 outbound-source-lower action s actual with OutboundHandler.forkCaller action in chosen
 ... | nothing = dispatch-outbound-lower action s actual
 ... | just caller = trans (cong (λ a → CM.advance a (OutboundHandler.source s)) (fork-caller-reflect action caller chosen))
   (outbound-fork-lower caller s actual)
 call-source-lower : ∀ action s {t} → T.advance (call-event action) s ≡ just t →
   CM.advance (command action) (K.source (T.base s)) ≡ just (K.source (T.base t))
 call-source-lower action s actual = outbound-source-lower (command action) (outbound-view s) (call-base-lower action s actual)

 -- Acquisition-only prefixes permit arbitrary callers on this common route;
 -- post-birth resource retention still permits every enabled frontend event.
 data AcquisitionRuns : T.Runtime → List AcquisitionCall → T.Runtime → Set where
  acquisitionDone : ∀ {s} → AcquisitionRuns s [] s
  acquisitionNext : ∀ {s t u action actions} → T.advance (call-event action) s ≡ just t →
    AcquisitionRuns t actions u → AcquisitionRuns s (action ∷ actions) u
 acquisition-events : ∀ {s actions t} → AcquisitionRuns s actions t → T.Runs s (map call-event actions) t
 acquisition-events acquisitionDone = T.stop
 acquisition-events (acquisitionNext {action = action} actual rest) = T.more {a = call-event action} actual (acquisition-events rest)
 acquisition-source : ∀ {s actions t} → AcquisitionRuns s actions t → CM.Executes (K.source (T.base s)) (map command actions) (K.source (T.base t))
 acquisition-source acquisitionDone = CM.done
 acquisition-source (acquisitionNext {s = s} {action = action} actual rest) = CM.next {a = command action} (call-source-lower action s actual) (acquisition-source rest)
 acquisition-append : ∀ {s actions t tail u} → AcquisitionRuns s actions t → AcquisitionRuns t tail u → AcquisitionRuns s (actions ++ tail) u
 acquisition-append acquisitionDone right = right
 acquisition-append (acquisitionNext actual rest) right = acquisitionNext actual (acquisition-append rest right)
 initialized-source : ∀ c g {start} → T.initialize c g ≡ just start → K.source (T.base start) ≡ c
 initialized-source c g actual with E.initial c in server
 ... | nothing = case actual of λ ()
 ... | just e = case just-injective actual of λ { refl → ExitFacts.initial-source isBearerClosed c server }
 initialized-captures : ∀ {c g start actions current} → T.initialize (CM.initial c) g ≡ just start →
   AcquisitionRuns start actions current → RuntimeCapture.Captures (K.source (T.base current))
 initialized-captures {c} {g} init path = RuntimeCapture.exec-preserves
   (subst RuntimeCapture.Captures (sym (initialized-source (CM.initial c) g init)) (RuntimeCapture.initial-valid c)) (acquisition-source path)

 -- Every enabled frontend plan preserves active acquisition captures. The
 -- initializer supplies the empty runtime; no supply/resource premise is added.
 initialized-frontend-captures : ∀ {c g start events current} → T.initialize (CM.initial c) g ≡ just start →
   T.Runs start events current → RuntimeCapture.Captures (K.source (T.base current))
 initialized-frontend-captures {c} {g} init path = Captures.Frontend.run-preserves canInitiate path
   (subst RuntimeCapture.Captures (sym (initialized-source (CM.initial c) g init)) (RuntimeCapture.initial-valid c))

 -- This occurrence certificate retains both checked views of the same real
 -- events: frontend permissions and primitive source steps at identical states.
 -- It is not inversion of an arbitrary later handler lookup.
 record Origin (start current : T.Runtime) (worker : WorkerId) : Set where
  field
   configuration : CM.Configuration
   governor : G.State
   initialized : T.initialize configuration governor ≡ just start
   before allocated selected born : T.Runtime
   parent : WorkerId
   request : S.Admission
   heldLease : S.Lease
   child-matches : S.child request ≡ worker
   prefix suffix : List T.Event
   prefix-run : T.Runs start prefix before
   before-PC : lookup parent (S.admissions (shared before)) ≡ just (S.admissionWorker request (S.prepare heldLease))
   allocation-event : T.advance (event parent Admission.allocatePromise) before ≡ just allocated
   selection-event : T.advance (event parent Admission.chooseEntry) allocated ≡ just selected
   fork-event : T.advance (event parent Admission.fork) selected ≡ just born
   allocation-source : I.advance (I.admissionStep parent Admission.allocatePromise) (core before) ≡ just (core allocated)
   selection-source : I.advance (I.admissionStep parent Admission.chooseEntry) (core allocated) ≡ just (core selected)
   fork-source : I.advance (I.admissionStep parent Admission.fork) (core selected) ≡ just (core born)
   promise : PromiseId
   promise-is-fresh-input : promise ≡ ident (S.nextPromise (shared before))
   promise-allocated : promise ∈ S.promises (shared allocated)
   entry : EntryId
   captured : S.HandlerStart
   descriptor : captured ≡ S.handlerStart entry (S.socketRef request) promise (S.key request)
   at-fork : Facts worker captured (shared born)
   suffix-run : T.Runs born suffix current
   retained : Facts worker captured (shared current)

 initialized-inbound-origin : ∀ {c g start before allocated selected born current prefix suffix}
   w req heldLease → T.initialize c g ≡ just start → T.Runs start prefix before →
   lookup w (S.admissions (shared before)) ≡ just (S.admissionWorker req (S.prepare heldLease)) →
   T.advance (event w Admission.allocatePromise) before ≡ just allocated →
   T.advance (event w Admission.chooseEntry) allocated ≡ just selected →
   T.advance (event w Admission.fork) selected ≡ just born →
   I.advance (I.admissionStep w Admission.allocatePromise) (core before) ≡ just (core allocated) →
   I.advance (I.admissionStep w Admission.chooseEntry) (core allocated) ≡ just (core selected) →
   I.advance (I.admissionStep w Admission.fork) (core selected) ≡ just (core born) →
   T.Runs born suffix current → Origin start current (S.child req)
 initialized-inbound-origin {c} {g} {before = before} {allocated} {selected} {born} {prefix = prefix} {suffix}
   w req heldLease init prefix-run owned allocatedEvent selectedEvent forkEvent allocatedSource selectedSource forkSource suffix-run
   with allocated-frame w req heldLease (core before) owned allocatedSource
 ... | selected-PC , promise-present with selected-fork-facts w req heldLease (ident (S.nextPromise (shared before)))
     (core allocated) selected-PC selectedSource forkSource
 ...   | entry , resources = record
   { configuration = c; governor = g; initialized = init
   ; before = before; allocated = allocated; selected = selected; born = born
   ; parent = w; request = req; heldLease = heldLease; child-matches = refl
   ; prefix = prefix; suffix = suffix; prefix-run = prefix-run; before-PC = owned
   ; allocation-event = allocatedEvent; selection-event = selectedEvent; fork-event = forkEvent
   ; allocation-source = allocatedSource; selection-source = selectedSource; fork-source = forkSource
   ; promise = ident (S.nextPromise (shared before)); promise-is-fresh-input = refl; promise-allocated = promise-present
   ; entry = entry; captured = S.handlerStart entry (S.socketRef req) (ident (S.nextPromise (shared before))) (S.key req)
   ; descriptor = refl; at-fork = resources; suffix-run = suffix-run
   ; retained = For.Frontend.run-preserves (S.child req) _ canInitiate suffix-run resources }

 -- The frontend-only constructor derives all three primitive equations;
 -- the earlier paired-view theorem and complete Origin record stay unchanged.
 initialized-inbound-origin-from-frontend : ∀ {c g start before allocated selected born current prefix suffix}
   w req heldLease → T.initialize c g ≡ just start → T.Runs start prefix before →
   lookup w (S.admissions (shared before)) ≡ just (S.admissionWorker req (S.prepare heldLease)) →
   T.advance (event w Admission.allocatePromise) before ≡ just allocated →
   T.advance (event w Admission.chooseEntry) allocated ≡ just selected →
   T.advance (event w Admission.fork) selected ≡ just born →
   T.Runs born suffix current → Origin start current (S.child req)
 initialized-inbound-origin-from-frontend {before = before} {allocated} {selected}
   w req heldLease init prefix-run owned allocatedEvent selectedEvent forkEvent suffix-run =
   initialized-inbound-origin w req heldLease init prefix-run owned allocatedEvent selectedEvent forkEvent
     (allocation-lower w before allocatedEvent) (selection-lower w allocated selectedEvent)
     (fork-lower w selected forkEvent) suffix-run

 -- Later execution retains the same initialization, actual birth and descriptor.
 extend : ∀ {start before after worker events} → T.Runs before events after → Origin start before worker → Origin start after worker
 extend {events = events} path history = record
   { configuration = Origin.configuration history
   ; governor = Origin.governor history
   ; initialized = Origin.initialized history
   ; before = Origin.before history
   ; allocated = Origin.allocated history
   ; selected = Origin.selected history
   ; born = Origin.born history
   ; parent = Origin.parent history
   ; request = Origin.request history
   ; heldLease = Origin.heldLease history
   ; child-matches = Origin.child-matches history
   ; prefix = Origin.prefix history
   ; prefix-run = Origin.prefix-run history
   ; before-PC = Origin.before-PC history
   ; allocation-event = Origin.allocation-event history
   ; selection-event = Origin.selection-event history
   ; fork-event = Origin.fork-event history
   ; allocation-source = Origin.allocation-source history
   ; selection-source = Origin.selection-source history
   ; fork-source = Origin.fork-source history
   ; promise = Origin.promise history
   ; promise-is-fresh-input = Origin.promise-is-fresh-input history
   ; promise-allocated = Origin.promise-allocated history
   ; entry = Origin.entry history
   ; captured = Origin.captured history
   ; descriptor = Origin.descriptor history
   ; at-fork = Origin.at-fork history
   ; suffix = Origin.suffix history ++ events
   ; suffix-run = SharedFacts.Protocols.append-protocols isBearerClosed isIOManagerError canInitiate (Origin.suffix-run history) path
   ; retained = For.Frontend.run-preserves _ (Origin.captured history) canInitiate path (Origin.retained history) }

 -- Both boundary certificates are derived from actual enabled frontend events.
 -- No physical publication/wait or resource certificate is supplied by callers.
 record AtPublication (start before after : T.Runtime) (worker : WorkerId) : Set where
  field
   prior : Origin start before worker
   following : Origin start after worker
   actual : T.advance (Joins.handler-event (W.publishAsyncResult worker)) before ≡ just after
   physical : Certificates.Handler.Publication worker (Joins.physical before) (Joins.physical after)
 publication-origin : ∀ {start before after worker} → Origin start before worker →
   T.advance (Joins.handler-event (W.publishAsyncResult worker)) before ≡ just after → AtPublication start before after worker
 publication-origin {before = before} {worker = worker} history actual = record
   { prior = history; following = extend (T.more {a = Joins.handler-event (W.publishAsyncResult worker)} actual T.stop) history; actual = actual
   ; physical = Joins.physical-publication worker before actual }

 record AtWait (start before after : T.Runtime) (worker : WorkerId) : Set where
  field
   prior : Origin start before worker
   following : Origin start after worker
   actual : T.advance (Joins.handler-event (W.shutdownStep Close.finishClose)) before ≡ just after
   collected : worker ∈ Close.collected (W.shutdown (Joins.physical after))
   physical : Certificates.Handler.PhysicalWait (Joins.physical before) (Joins.physical after)
 wait-origin : ∀ {start before after worker} → Origin start before worker →
   T.advance (Joins.handler-event (W.shutdownStep Close.finishClose)) before ≡ just after →
   worker ∈ Close.collected (W.shutdown (Joins.physical after)) → AtWait start before after worker
 wait-origin {before = before} history actual collected = record
   { prior = history; following = extend (T.more {a = Joins.handler-event (W.shutdownStep Close.finishClose)} actual T.stop) history; actual = actual; collected = collected
   ; physical = Joins.physical-wait before actual }

 -- Determinism removes an already certified prefix without replaying it.
 discard-prefix : ∀ {start middle current prefix suffix} → T.Runs start prefix middle →
   T.Runs start (prefix ++ suffix) current → T.Runs middle suffix current
 discard-prefix T.stop whole = whole
 discard-prefix (T.more first tail) (T.more second rest)
   with just-injective (trans (sym first) second)
 ... | refl = discard-prefix tail rest

 -- Outbound histories derive the entry capture from initialized acquisition
 -- execution. Prefixes use that route; every frontend event is allowed later.
 record OutboundOrigin (start current : T.Runtime) (worker : WorkerId) : Set where
  field
   configuration : I.Configuration
   governor : G.State
   initialized : T.initialize (CM.initial configuration) governor ≡ just start
   before allocated beforeFork born : T.Runtime
   parent : WorkerId
   request : A.Request
   entry : EntryId
   key : ConnectionManagement.Domain.ConnectionKey
   child-matches : A.child request ≡ worker
   prefix route : List AcquisitionCall
   prefix-run : AcquisitionRuns start prefix before
   before-PC : lookup parent (CM.acquiring (K.source (T.base before))) ≡ just (A.frame request (A.allocatePromise entry))
   allocation-event : T.advance (call-event (acquireCall parent A.newPromise)) before ≡ just allocated
   route-run : AcquisitionRuns allocated route beforeFork
   fork-PC : lookup parent (CM.acquiring (K.source (T.base beforeFork))) ≡ just (A.frame request (A.forkHandler entry (ident (S.nextPromise (shared before))) key))
   fork-event : T.advance (call-event (acquireCall parent A.forkOK)) beforeFork ≡ just born
   allocation-source : CM.advance (CM.acquire parent A.newPromise) (K.source (T.base before)) ≡ just (K.source (T.base allocated))
   fork-source : CM.advance (CM.acquire parent A.forkOK) (K.source (T.base beforeFork)) ≡ just (K.source (T.base born))
   promise-allocated : ident (S.nextPromise (shared before)) ∈ S.promises (shared allocated)
   captured : S.HandlerStart
   descriptor : captured ≡ S.handlerStart entry (A.socketRef request) (ident (S.nextPromise (shared before))) key
   at-fork : Facts worker captured (shared born)
   suffix : List T.Event
   suffix-run : T.Runs born suffix current
   retained : Facts worker captured (shared current)

 initialized-outbound-origin : ∀ {c g start before allocated beforeFork born current prefix route suffix}
   caller req entry key → T.initialize (CM.initial c) g ≡ just start →
   AcquisitionRuns start prefix before →
   lookup caller (CM.acquiring (K.source (T.base before))) ≡ just (A.frame req (A.allocatePromise entry)) →
   T.advance (call-event (acquireCall caller A.newPromise)) before ≡ just allocated →
   AcquisitionRuns allocated route beforeFork →
   lookup caller (CM.acquiring (K.source (T.base beforeFork))) ≡ just (A.frame req (A.forkHandler entry (ident (S.nextPromise (shared before))) key)) →
   T.advance (call-event (acquireCall caller A.forkOK)) beforeFork ≡ just born →
   T.Runs born suffix current → OutboundOrigin start current (A.child req)
 initialized-outbound-origin {c} {g} {before = before} {allocated} {beforeFork} {born} {prefix = prefix} {route} {suffix}
   caller req entry key init prefix-run owned allocation route-run forkPC forkEvent suffix-run = record
   { configuration = c; governor = g; initialized = init
   ; before = before; allocated = allocated; beforeFork = beforeFork; born = born
   ; parent = caller; request = req; entry = entry; key = key; child-matches = refl
   ; prefix = prefix; route = route; prefix-run = prefix-run; before-PC = owned
   ; allocation-event = allocation; route-run = route-run; fork-PC = forkPC; fork-event = forkEvent
   ; allocation-source = allocatedSource; fork-source = forkSource
   ; promise-allocated = proj₂ (outbound-allocated-frame caller req entry (K.source (T.base before)) owned allocatedSource)
   ; captured = captured; descriptor = refl; at-fork = resources
   ; suffix = suffix; suffix-run = suffix-run
   ; retained = For.Frontend.run-preserves (A.child req) captured canInitiate suffix-run resources }
   where
   allocatedSource = call-source-lower (acquireCall caller A.newPromise) before allocation
   forkSource = call-source-lower (acquireCall caller A.forkOK) beforeFork forkEvent
   captured = S.handlerStart entry (A.socketRef req) (ident (S.nextPromise (shared before))) key
   captures = initialized-captures init (acquisition-append prefix-run (acquisitionNext {action = acquireCall caller A.newPromise} allocation route-run))
   present = lookup-all (λ f → FrameCapture.Valid f (shared beforeFork)) caller (CM.acquiring (K.source (T.base beforeFork))) captures forkPC
   resources = outbound-fork-facts caller req entry (ident (S.nextPromise (shared before))) key (K.source (T.base beforeFork)) forkPC present forkSource

 extend-outbound : ∀ {start before after worker events} → T.Runs before events after → OutboundOrigin start before worker → OutboundOrigin start after worker
 extend-outbound {events = events} path history = record
   { configuration = OutboundOrigin.configuration history; governor = OutboundOrigin.governor history; initialized = OutboundOrigin.initialized history
   ; before = OutboundOrigin.before history; allocated = OutboundOrigin.allocated history; beforeFork = OutboundOrigin.beforeFork history; born = OutboundOrigin.born history
   ; parent = OutboundOrigin.parent history; request = OutboundOrigin.request history; entry = OutboundOrigin.entry history; key = OutboundOrigin.key history
   ; child-matches = OutboundOrigin.child-matches history; prefix = OutboundOrigin.prefix history; route = OutboundOrigin.route history
   ; prefix-run = OutboundOrigin.prefix-run history; before-PC = OutboundOrigin.before-PC history; allocation-event = OutboundOrigin.allocation-event history
   ; route-run = OutboundOrigin.route-run history; fork-PC = OutboundOrigin.fork-PC history; fork-event = OutboundOrigin.fork-event history
   ; allocation-source = OutboundOrigin.allocation-source history; fork-source = OutboundOrigin.fork-source history; promise-allocated = OutboundOrigin.promise-allocated history
   ; captured = OutboundOrigin.captured history; descriptor = OutboundOrigin.descriptor history; at-fork = OutboundOrigin.at-fork history
   ; suffix = OutboundOrigin.suffix history ++ events
   ; suffix-run = SharedFacts.Protocols.append-protocols isBearerClosed isIOManagerError canInitiate (OutboundOrigin.suffix-run history) path
   ; retained = For.Frontend.run-preserves _ (OutboundOrigin.captured history) canInitiate path (OutboundOrigin.retained history) }

 -- Pre-handshake publication still uses the raw physical handler. Coordinator
 -- waits use the guarded outer route and its combined physical result oracle.
 handler-action : RawHandler.Action → W.Action
 handler-action action = W.run (Group.run (Monitor.run (Jobs.run (Mux.run (OutboundHandler.handler action)))))
 handler-event : RawHandler.Action → T.Event
 handler-event action = Joins.handler-event (handler-action action)
 handler-action-lower : ∀ action s {t} → T.advance (handler-event action) s ≡ just t →
   RawHandler.step action (raw-view s) ≡ just (raw-view t)
 handler-action-lower action s actual = outbound-inherited action b
   (mux-inherited bAction u (jobs-inherited uAction p (monitor-inherited pAction m
     (group-inherited mAction g (physical-inherited gAction x (Joins.physical-lower (handler-action action) s actual))))))
   where
   bAction = OutboundHandler.handler action
   uAction = Mux.run bAction
   pAction = Jobs.run uAction
   mAction = Monitor.run pAction
   gAction = Group.run mAction
   x = Joins.physical s
   g = W.base x
   m = Group.base g
   p = Monitor.base m
   u = Jobs.base p
   b = Mux.base u

 record OutboundAtPublication (start before after : T.Runtime) (worker : WorkerId) : Set where
  field
   prior : OutboundOrigin start before worker
   following : OutboundOrigin start after worker
   actual : T.advance (handler-event (RawHandler.publishAsyncResult worker)) before ≡ just after
   physical : RawFacts.ResultPublication worker (raw-view before) (raw-view after)
 outbound-publication-origin : ∀ {start before after worker} → OutboundOrigin start before worker →
   T.advance (handler-event (RawHandler.publishAsyncResult worker)) before ≡ just after → OutboundAtPublication start before after worker
 outbound-publication-origin {before = before} {worker = worker} history actual = record
   { prior = history; following = extend-outbound (T.more {a = handler-event (RawHandler.publishAsyncResult worker)} actual T.stop) history
   ; actual = actual; physical = RawFacts.publication-observation worker (raw-view before) (handler-action-lower (RawHandler.publishAsyncResult worker) before actual) }

 record OutboundAtWait (start before after : T.Runtime) (worker : WorkerId) : Set where
  field
   prior : OutboundOrigin start before worker
   following : OutboundOrigin start after worker
   actual : T.advance (Joins.handler-event (W.shutdownStep Close.finishClose)) before ≡ just after
   collected : worker ∈ Close.collected (W.shutdown (Joins.physical after))
   physical : Certificates.Handler.PhysicalWait (Joins.physical before) (Joins.physical after)
 outbound-wait-origin : ∀ {start before after worker} → OutboundOrigin start before worker →
   T.advance (Joins.handler-event (W.shutdownStep Close.finishClose)) before ≡ just after →
   worker ∈ Close.collected (W.shutdown (Joins.physical after)) → OutboundAtWait start before after worker
 outbound-wait-origin {before = before} history actual collected = record
   { prior = history; following = extend-outbound (T.more {a = Joins.handler-event (W.shutdownStep Close.finishClose)} actual T.stop) history
   ; actual = actual; collected = collected
   ; physical = Joins.physical-wait before actual }

 -- General histories admit arbitrary enabled frontend interference before
 -- allocation and between allocation and fork; the acquisition-only API stays.
 module OutboundFrontend where
  record History (start current : T.Runtime) (worker : WorkerId) : Set where
   field
    configuration : I.Configuration
    governor : G.State
    initialized : T.initialize (CM.initial configuration) governor ≡ just start
    before allocated beforeFork born : T.Runtime
    parent : WorkerId
    request : A.Request
    entry : EntryId
    key : ConnectionManagement.Domain.ConnectionKey
    child-matches : A.child request ≡ worker
    prefix route : List T.Event
    prefix-run : T.Runs start prefix before
    before-PC : lookup parent (CM.acquiring (K.source (T.base before))) ≡ just (A.frame request (A.allocatePromise entry))
    allocation-event : T.advance (call-event (acquireCall parent A.newPromise)) before ≡ just allocated
    route-run : T.Runs allocated route beforeFork
    fork-PC : lookup parent (CM.acquiring (K.source (T.base beforeFork))) ≡ just (A.frame request (A.forkHandler entry (ident (S.nextPromise (shared before))) key))
    fork-event : T.advance (call-event (acquireCall parent A.forkOK)) beforeFork ≡ just born
    allocation-source : CM.advance (CM.acquire parent A.newPromise) (K.source (T.base before)) ≡ just (K.source (T.base allocated))
    fork-source : CM.advance (CM.acquire parent A.forkOK) (K.source (T.base beforeFork)) ≡ just (K.source (T.base born))
    promise-allocated : ident (S.nextPromise (shared before)) ∈ S.promises (shared allocated)
    captured : S.HandlerStart
    descriptor : captured ≡ S.handlerStart entry (A.socketRef request) (ident (S.nextPromise (shared before))) key
    at-fork : Facts worker captured (shared born)
    suffix : List T.Event
    suffix-run : T.Runs born suffix current
    retained : Facts worker captured (shared current)

  initialize-history : ∀ {c g start before allocated beforeFork born current prefix route suffix}
    caller req entry key → T.initialize (CM.initial c) g ≡ just start →
    T.Runs start prefix before →
    lookup caller (CM.acquiring (K.source (T.base before))) ≡ just (A.frame req (A.allocatePromise entry)) →
    T.advance (call-event (acquireCall caller A.newPromise)) before ≡ just allocated →
    T.Runs allocated route beforeFork →
    lookup caller (CM.acquiring (K.source (T.base beforeFork))) ≡ just (A.frame req (A.forkHandler entry (ident (S.nextPromise (shared before))) key)) →
    T.advance (call-event (acquireCall caller A.forkOK)) beforeFork ≡ just born →
    T.Runs born suffix current → History start current (A.child req)
  initialize-history {c} {g} {before = before} {allocated} {beforeFork} {born} {prefix = prefix} {route} {suffix}
    caller req entry key init prefix-run owned allocation route-run forkPC forkEvent suffix-run = record
    { configuration = c; governor = g; initialized = init
    ; before = before; allocated = allocated; beforeFork = beforeFork; born = born
    ; parent = caller; request = req; entry = entry; key = key; child-matches = refl
    ; prefix = prefix; route = route; prefix-run = prefix-run; before-PC = owned
    ; allocation-event = allocation; route-run = route-run; fork-PC = forkPC; fork-event = forkEvent
    ; allocation-source = allocatedSource; fork-source = forkSource
    ; promise-allocated = proj₂ (outbound-allocated-frame caller req entry (K.source (T.base before)) owned allocatedSource)
    ; captured = captured; descriptor = refl; at-fork = resources
    ; suffix = suffix; suffix-run = suffix-run
    ; retained = For.Frontend.run-preserves (A.child req) captured canInitiate suffix-run resources }
    where
    allocatedSource = call-source-lower (acquireCall caller A.newPromise) before allocation
    forkSource = call-source-lower (acquireCall caller A.forkOK) beforeFork forkEvent
    captured = S.handlerStart entry (A.socketRef req) (ident (S.nextPromise (shared before))) key
    captures = initialized-frontend-captures init (SharedFacts.Protocols.append-protocols isBearerClosed isIOManagerError canInitiate prefix-run (T.more {a = call-event (acquireCall caller A.newPromise)} allocation route-run))
    present = lookup-all (λ f → FrameCapture.Valid f (shared beforeFork)) caller (CM.acquiring (K.source (T.base beforeFork))) captures forkPC
    resources = outbound-fork-facts caller req entry (ident (S.nextPromise (shared before))) key (K.source (T.base beforeFork)) forkPC present forkSource

  extend-history : ∀ {start before after worker events} → T.Runs before events after → History start before worker → History start after worker
  extend-history {events = events} path history = record
    { configuration = History.configuration history; governor = History.governor history; initialized = History.initialized history
    ; before = History.before history; allocated = History.allocated history; beforeFork = History.beforeFork history; born = History.born history
    ; parent = History.parent history; request = History.request history; entry = History.entry history; key = History.key history
    ; child-matches = History.child-matches history; prefix = History.prefix history; route = History.route history
    ; prefix-run = History.prefix-run history; before-PC = History.before-PC history; allocation-event = History.allocation-event history
    ; route-run = History.route-run history; fork-PC = History.fork-PC history; fork-event = History.fork-event history
    ; allocation-source = History.allocation-source history; fork-source = History.fork-source history; promise-allocated = History.promise-allocated history
    ; captured = History.captured history; descriptor = History.descriptor history; at-fork = History.at-fork history
    ; suffix = History.suffix history ++ events
    ; suffix-run = SharedFacts.Protocols.append-protocols isBearerClosed isIOManagerError canInitiate (History.suffix-run history) path
    ; retained = For.Frontend.run-preserves _ (History.captured history) canInitiate path (History.retained history) }

  record AtResult (start before after : T.Runtime) (worker : WorkerId) : Set where
   field
    prior : History start before worker
    following : History start after worker
    actual : T.advance (handler-event (RawHandler.publishAsyncResult worker)) before ≡ just after
    physical : RawFacts.ResultPublication worker (raw-view before) (raw-view after)
  publication-history : ∀ {start before after worker} → History start before worker →
    T.advance (handler-event (RawHandler.publishAsyncResult worker)) before ≡ just after → AtResult start before after worker
  publication-history {before = before} {worker = worker} history actual = record
    { prior = history; following = extend-history (T.more {a = handler-event (RawHandler.publishAsyncResult worker)} actual T.stop) history
    ; actual = actual; physical = RawFacts.publication-observation worker (raw-view before) (handler-action-lower (RawHandler.publishAsyncResult worker) before actual) }

  record AtCMWait (start before after : T.Runtime) (worker : WorkerId) : Set where
   field
    prior : History start before worker
    following : History start after worker
    actual : T.advance (Joins.handler-event (W.shutdownStep Close.finishClose)) before ≡ just after
    collected : worker ∈ Close.collected (W.shutdown (Joins.physical after))
    physical : Certificates.Handler.PhysicalWait (Joins.physical before) (Joins.physical after)
  wait-history : ∀ {start before after worker} → History start before worker →
    T.advance (Joins.handler-event (W.shutdownStep Close.finishClose)) before ≡ just after →
    worker ∈ Close.collected (W.shutdown (Joins.physical after)) → AtCMWait start before after worker
  wait-history {before = before} history actual collected = record
    { prior = history; following = extend-history (T.more {a = Joins.handler-event (W.shutdownStep Close.finishClose)} actual T.stop) history
    ; actual = actual; collected = collected
    ; physical = Joins.physical-wait before actual }


import ConnectionManagement.Properties.HandlerBirthBacking as HandlerBirth
import ConnectionManagement.MuxHandlerExit as HandlerExitModel
import ConnectionManagement.Properties.MuxHandlerExit as HandlerExitFacts

-- Keep the birth proof independent of this observation layer. These boundaries
-- reuse the existing opaque handler lowering, publication and wait facts.
module BackedShutdown (canInitiate : HandleId → ℕ → Bool) where
 open import ConnectionManagement.Domain using (EntryId)
 private module T = Combined.Protocols isBearerClosed isIOManagerError canInitiate using (Event; Runs; Runtime; advance; initialize; more; stop)
 private module WaitFacts = HandlerExitFacts isBearerClosed using (PhysicalWait)
 import Data.List.Relation.Unary.All as All
 private module Back = HandlerBirth.Frontend isBearerClosed isIOManagerError canInitiate using (Backing; ForkStep; capture-of-found; follow; initialized-birth; physical-state)
 ack-event : ErrorId → T.Event
 ack-event err = Frontend.handler-event canInitiate (RawHandler.deliverShutdownHandshake err)
 result-event : WorkerId → T.Event
 result-event w = Frontend.handler-event canInitiate (RawHandler.publishAsyncResult w)
 wait-event : T.Event
 wait-event = MonitorJoins.Frontend.handler-event isBearerClosed isIOManagerError canInitiate
   (HandlerExitModel.shutdownStep Close.finishClose)
 ack-events : List T.Event → ErrorId → List T.Event
 ack-events prefix err = prefix ++ (ack-event err ∷ [])
 result-events : List T.Event → ErrorId → List T.Event → WorkerId → List T.Event
 result-events prefix err cleanup w = (ack-events prefix err ++ cleanup) ++ (result-event w ∷ [])
 wait-events : List T.Event → ErrorId → List T.Event → WorkerId → List T.Event → List T.Event
 wait-events prefix err cleanup w traversal = (result-events prefix err cleanup w ++ traversal) ++ (wait-event ∷ [])
 -- The receipt exposes the actual post-delivery CM acknowledgement. It does
 -- not manufacture an Async result or satisfy the collective wait.
 record HandshakeReceipt (err : ErrorId) (before after : RawHandler.State) : Set where
  constructor handshake-receipt
  field
   entry : EntryId
   worker : WorkerId
   delivered : RawHandler.State
   awaiting : Close.phase (RawHandler.shutdown before) ≡ Close.awaitDelivery entry worker
   delivery : RawHandler.deliverHandshake worker err before ≡ just delivered
   acknowledgement : RawHandler.acknowledge delivered ≡ just after
   primitive-ack : Close.step (S.cm (I.world (RawHandler.source delivered)))
     (λ w → RawHandler.resultReady w delivered) Close.acknowledgeDelivery (RawHandler.shutdown delivered) ≡ just (RawHandler.shutdown after)
 acknowledge-lower : ∀ s {t} → RawHandler.acknowledge s ≡ just t →
   Close.step (S.cm (I.world (RawHandler.source s))) (λ w → RawHandler.resultReady w s)
     Close.acknowledgeDelivery (RawHandler.shutdown s) ≡ just (RawHandler.shutdown t)
 acknowledge-lower s actual with Close.step (S.cm (I.world (RawHandler.source s)))
   (λ w → RawHandler.resultReady w s) Close.acknowledgeDelivery (RawHandler.shutdown s)
 ... | nothing = case actual of λ ()
 ... | just next = case just-injective actual of λ { refl → refl }
 receipt-observation : ∀ err s {t} → RawHandler.step (RawHandler.deliverShutdownHandshake err) s ≡ just t → HandshakeReceipt err s t
 receipt-observation err s actual with Close.phase (RawHandler.shutdown s) in awaited
 ... | Close.awaitDelivery e w with RawHandler.deliverHandshake w err s in delivered
 ...   | nothing = case actual of λ ()
 ...   | just next = handshake-receipt e w next awaited delivered actual (acknowledge-lower next actual)
 receipt-observation err s actual | Close.initial = case actual of λ ()
 receipt-observation err s actual | Close.reading = case actual of λ ()
 receipt-observation err s actual | Close.sendReady e w = case actual of λ ()
 receipt-observation err s actual | Close.awaitResults = case actual of λ ()
 receipt-observation err s actual | Close.closed = case actual of λ ()
 recipient-is : ∀ {e e′ w w′} → Close.awaitDelivery e w ≡ Close.awaitDelivery e′ w′ → w ≡ w′
 recipient-is refl = refl
 -- One initialized certificate spans delivery receipt, actual result
 -- publication and the final wait's real pre-wait physical-result oracle.
 record InitializedShutdown (start current : T.Runtime) (w : WorkerId) (captured : S.HandlerStart) : Set where
  field
   configuration : CM.Configuration
   governor : G.State
   initialized : T.initialize configuration governor ≡ just start
   beforeAck afterAck beforeResult afterResult beforeWait : T.Runtime
   prefix cleanup traversal : List T.Event
   error : ErrorId
   prefix-run : T.Runs start prefix beforeAck
   birth : Back.Backing start beforeAck prefix w captured
   acknowledgement-event : T.advance (ack-event error) beforeAck ≡ just afterAck
   receipt : HandshakeReceipt error (Frontend.raw-view canInitiate beforeAck) (Frontend.raw-view canInitiate afterAck)
   delivered-to : HandshakeReceipt.worker receipt ≡ w
   acknowledged : Back.Backing start afterAck (ack-events prefix error) w captured
   ack-follows : acknowledged ≡ Back.follow (T.more {a = ack-event error} acknowledgement-event T.stop) birth
   cleanup-run : T.Runs afterAck cleanup beforeResult
   publication-event : T.advance (result-event w) beforeResult ≡ just afterResult
   publication : RawFacts.ResultPublication w (Frontend.raw-view canInitiate beforeResult) (Frontend.raw-view canInitiate afterResult)
   publication-capture : RawHandler.captured (RawFacts.registered publication) ≡ captured
   published : Back.Backing start afterResult (result-events prefix error cleanup w) w captured
   result-follows : published ≡ Back.follow (T.more {a = result-event w} publication-event T.stop) (Back.follow cleanup-run acknowledged)
   traversal-run : T.Runs afterResult traversal beforeWait
   wait-event-actual : T.advance wait-event beforeWait ≡ just current
   collected : w ∈ Close.collected (HandlerExitModel.shutdown isBearerClosed
     (MonitorJoins.Frontend.physical isBearerClosed isIOManagerError canInitiate current))
   physical-wait : WaitFacts.PhysicalWait
     (MonitorJoins.Frontend.physical isBearerClosed isIOManagerError canInitiate beforeWait)
     (MonitorJoins.Frontend.physical isBearerClosed isIOManagerError canInitiate current)
   at-wait : Back.Backing start current (wait-events prefix error cleanup w traversal) w captured
   wait-follows : at-wait ≡ Back.follow (T.more {a = wait-event} wait-event-actual T.stop) (Back.follow traversal-run published)
 initialized-handshake-shutdown : ∀ {c g start beforeAck afterAck beforeResult afterResult beforeWait current prefix cleanup traversal entry w thread err} →
   T.initialize c g ≡ just start → T.Runs start prefix beforeAck →
   lookup w (OutboundHandler.threads (Back.physical-state beforeAck)) ≡ just thread →
   Close.phase (RawHandler.shutdown (Frontend.raw-view canInitiate beforeAck)) ≡ Close.awaitDelivery entry w →
   T.advance (ack-event err) beforeAck ≡ just afterAck → T.Runs afterAck cleanup beforeResult →
   T.advance (result-event w) beforeResult ≡ just afterResult → T.Runs afterResult traversal beforeWait →
   T.advance wait-event beforeWait ≡ just current →
   w ∈ Close.collected (HandlerExitModel.shutdown isBearerClosed
     (MonitorJoins.Frontend.physical isBearerClosed isIOManagerError canInitiate current)) →
   InitializedShutdown start current w (RawHandler.captured thread)
 initialized-handshake-shutdown {c} {g} {start} {beforeAck} {afterAck} {beforeResult} {afterResult} {beforeWait} {current}
   {prefix} {cleanup} {traversal} {entry} {w} {thread} {err}
   init prefixRun found awaiting ack cleanupRun returned traversalRun waited member = record
   { configuration = c; governor = g; initialized = init
   ; beforeAck = beforeAck; afterAck = afterAck; beforeResult = beforeResult; afterResult = afterResult; beforeWait = beforeWait
   ; prefix = prefix; cleanup = cleanup; traversal = traversal; error = err; prefix-run = prefixRun
   ; birth = initialBirth; acknowledgement-event = ack; receipt = received
   ; delivered-to = recipient-is (trans (sym (HandshakeReceipt.awaiting received)) awaiting)
   ; acknowledged = acked; ack-follows = refl; cleanup-run = cleanupRun
   ; publication-event = returned; publication = result
   ; publication-capture = Back.capture-of-found beforePublication (RawFacts.found-before result)
   ; published = published; result-follows = refl; traversal-run = traversalRun; wait-event-actual = waited
   ; collected = member; physical-wait = MonitorJoins.Frontend.physical-wait isBearerClosed isIOManagerError canInitiate beforeWait waited
   ; at-wait = finished; wait-follows = refl }
   where
   initialBirth : Back.Backing start beforeAck prefix w (RawHandler.captured thread)
   initialBirth = Back.initialized-birth {c = c} {g = g} {start = start} {events = prefix} {current = beforeAck} {w = w} {thread = thread} init prefixRun found
   received : HandshakeReceipt err (Frontend.raw-view canInitiate beforeAck) (Frontend.raw-view canInitiate afterAck)
   received = receipt-observation err (Frontend.raw-view canInitiate beforeAck)
     (Frontend.handler-action-lower canInitiate (RawHandler.deliverShutdownHandshake err) beforeAck ack)
   acked : Back.Backing start afterAck (ack-events prefix err) w (RawHandler.captured thread)
   acked = Back.follow (T.more {a = ack-event err} ack T.stop) initialBirth
   beforePublication : Back.Backing start beforeResult (ack-events prefix err ++ cleanup) w (RawHandler.captured thread)
   beforePublication = Back.follow cleanupRun acked
   result : RawFacts.ResultPublication w (Frontend.raw-view canInitiate beforeResult) (Frontend.raw-view canInitiate afterResult)
   result = RawFacts.publication-observation w (Frontend.raw-view canInitiate beforeResult)
     (Frontend.handler-action-lower canInitiate (RawHandler.publishAsyncResult w) beforeResult returned)
   published : Back.Backing start afterResult (result-events prefix err cleanup w) w (RawHandler.captured thread)
   published = Back.follow (T.more {a = result-event w} returned T.stop) beforePublication
   beforeFinalWait : Back.Backing start beforeWait (result-events prefix err cleanup w ++ traversal) w (RawHandler.captured thread)
   beforeFinalWait = Back.follow traversalRun published
   finished : Back.Backing start current (wait-events prefix err cleanup w traversal) w (RawHandler.captured thread)
   finished = Back.follow (T.more {a = wait-event} waited T.stop) beforeFinalWait

 -- Transport equations keep the exact chosen fork, not merely a descriptor
 -- compatible with a different birth at a later boundary.
 birth-command : ∀ {start current events w captured} → Back.Backing start current events w captured → OutboundHandler.Action
 birth-command history = Back.ForkStep.command (Back.Backing.operation history)
 follow-command : ∀ {start before after events tail w captured} (path : T.Runs before tail after)
   (history : Back.Backing start before events w captured) → birth-command (Back.follow path history) ≡ birth-command history
 follow-command path history = refl
 same-birth-command : ∀ {start current w captured} (history : InitializedShutdown start current w captured) →
   birth-command (InitializedShutdown.at-wait history) ≡ birth-command (InitializedShutdown.birth history)
 same-birth-command {current = current} {w = w} history = trans (cong birth-command (InitializedShutdown.wait-follows history))
   (trans (follow-command waitTrace (Back.follow (InitializedShutdown.traversal-run history) (InitializedShutdown.published history)))
   (trans (follow-command (InitializedShutdown.traversal-run history) (InitializedShutdown.published history))
   (trans (cong birth-command (InitializedShutdown.result-follows history))
   (trans (follow-command resultTrace (Back.follow (InitializedShutdown.cleanup-run history) (InitializedShutdown.acknowledged history)))
   (trans (follow-command (InitializedShutdown.cleanup-run history) (InitializedShutdown.acknowledged history))
   (trans (cong birth-command (InitializedShutdown.ack-follows history))
     (follow-command ackTrace (InitializedShutdown.birth history))))))))
   where
   ackTrace : T.Runs (InitializedShutdown.beforeAck history) (ack-event (InitializedShutdown.error history) ∷ []) (InitializedShutdown.afterAck history)
   ackTrace = T.more {a = ack-event (InitializedShutdown.error history)} (InitializedShutdown.acknowledgement-event history) T.stop
   resultTrace : T.Runs (InitializedShutdown.beforeResult history) (result-event w ∷ []) (InitializedShutdown.afterResult history)
   resultTrace = T.more {a = result-event w} (InitializedShutdown.publication-event history) T.stop
   waitTrace : T.Runs (InitializedShutdown.beforeWait history) (wait-event ∷ []) current
   waitTrace = T.more {a = wait-event} (InitializedShutdown.wait-event-actual history) T.stop

 -- The result is read from the actual pre-wait oracle, for a captured worker.
 result-at-final-wait : ∀ {start current w captured} (history : InitializedShutdown start current w captured) →
   HandlerExitModel.resultReady isBearerClosed w
     (MonitorJoins.Frontend.physical isBearerClosed isIOManagerError canInitiate (InitializedShutdown.beforeWait history)) ≡ true
 result-at-final-wait history = All.lookup (WaitFacts.PhysicalWait.observed-results (InitializedShutdown.physical-wait history))
   (InitializedShutdown.collected history)
