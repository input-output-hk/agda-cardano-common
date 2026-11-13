{-# OPTIONS --guardedness #-}

-- Control coverage through every group writer, retaining actual component facts.
open import Data.Bool using (Bool)
open import ConnectionManagement.Domain using (ErrorId)
module ConnectionManagement.Properties.LiveTrackerAuxControlGroup (isBearerClosed : ErrorId → Bool) where
open import Data.Bool using (true; false; _∧_)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no; does)
open import Class.DecEq using (_≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import ConnectionManagement.Domain using (WorkerId; DecEq-Id)
open import ConnectionManagement.Store using (Store; lookup)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as Machine
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as WireMux
import ConnectionManagement.MuxProtocolJobs as P
import ConnectionManagement.MuxGroupShutdown as Group
import ConnectionManagement.Properties.MuxGroupShutdown as GroupProperties
import ConnectionManagement.Properties.LiveTrackerAuxContent as Content
import ConnectionManagement.Properties.LiveTrackerAuxGroup as Core
import ConnectionManagement.Properties.LiveTrackerAuxMonitor as MonitorFacts
import ConnectionManagement.Properties.LiveTrackerAuxControls as ControlsFacts
import ConnectionManagement.Properties.LiveTrackerAuxUpdates as Updates
import ConnectionManagement.Properties.LiveTrackerAuxTransport as Transport
module W = Group isBearerClosed
module M = W.M
module U = P.U
module Pool = P.Pool
module Up = Updates isBearerClosed
module T = Transport isBearerClosed
module A = Content isBearerClosed
module MF = MonitorFacts isBearerClosed
open ControlsFacts isBearerClosed using (Controls; current; phase-preserves; rows-kept; capture-preserves; request-preserves; deliver-preserves; join-preserves; via-pool-preserves; via-pool-kept)
Rows : Store WorkerId W.Frame → P.State → Set
Rows rows p = All (λ { (w , row) → A.ControlContent w row p }) rows
Base : W.State → Set
Base s = Up.Valid (W.protocolState s) × MF.PCs (M.pcs (W.base s)) (W.protocolState s)
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.IGTypes
import Data.Nat
module ControlStore where
 Same : W.State → W.State → Set
 Same s t = W.controls t ≡ W.controls s
 composePCs : ∀ {s t u} → Same s t → Same t u → Same s u
 composePCs first second = trans second first
 via-source-projects : ∀ a s {t} → W.viaSource a s ≡ just t → Same s t
 via-source-projects a s eq with O.advance (O.inbound (Machine.igStep a)) (W.source s)
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → refl }
 pool-step : ∀ w f a s {p} → Pool.step a (W.poolAt w s) ≡ just p → Same s (W.setPool w f p s)
 pool-step w f a s eq = refl
 discard-projects : ∀ j job s {s′} → W.discardClean j job s ≡ just s′ → Same s s′
 discard-projects j job s eq with Types.direction job
 ... | WireMux.initiatorJob = case just-injective eq of λ { refl → refl }
 ... | WireMux.responderJob with P.locate j (P.pendingAt (Types.owner job) (W.protocolState s)) | P.muxAt (Types.mux job) (W.protocolState s)
 ...   | just (index , kept) | just m with IG.takePending index (WireMux.finishedJobs m)
 ...     | just ((n , result) , rest) with does (n Data.Nat.≟ Types.protocolNumber job) ∧ P.sameOutcome ConnectionManagement.IGTypes.clean result
 ...       | true with W.viaSource (IG.discardJobOccurrence (Types.mux job) index) s in advanced
 ...         | nothing = case eq of λ ()
 ...         | just next = case just-injective eq of λ { refl → via-source-projects (IG.discardJobOccurrence (Types.mux job) index) s advanced }
 discard-projects j job s eq | WireMux.responderJob | just (index , kept) | just m | just ((n , result) , rest) | false = case eq of λ ()
 discard-projects j job s eq | WireMux.responderJob | just (index , kept) | just m | nothing = case eq of λ ()
 discard-projects j job s eq | WireMux.responderJob | nothing | _ = case eq of λ ()
 discard-projects j job s eq | WireMux.responderJob | just pair | nothing = case eq of λ ()
 prepare-projects : ∀ j w f s {s′} → W.prepareUnwind j w f s ≡ just s′ → Same s s′
 prepare-projects j w f s eq with lookup j (P.jobs (W.protocolState s))
 ... | nothing with W.isInfra j f
 ...   | true = case just-injective eq of λ { refl → refl }
 ...   | false = case eq of λ ()
 prepare-projects j w f s eq | just job with does (w ≟ Types.owner job) | Types.phase job
 ... | true | Types.executing = case just-injective eq of λ { refl → refl }
 ... | true | Types.waitingEgress = case just-injective eq of λ { refl → refl }
 ... | true | Types.resultCaptured ConnectionManagement.IGTypes.clean = discard-projects j job s eq
 ... | true | Types.resultCaptured (ConnectionManagement.IGTypes.errored err) = case eq of λ ()
 ... | false | _ = case eq of λ ()
 unwind-projects : ∀ j s {s′} → W.unwindChild j s ≡ just s′ → Same s s′
 unwind-projects j s eq with W.ownerOf j s
 ... | nothing = case eq of λ ()
 ... | just (w , f) with lookup j (Pool.handles (W.poolAt w s))
 ...   | just Pool.bodyUnwinding with W.prepareUnwind j w f s in prepared
 ...     | nothing = case eq of λ ()
 ...     | just next with Pool.step (Pool.bodyUnwound j) (W.poolAt w next) in advanced
 ...       | nothing = case eq of λ ()
 ...       | just p = case just-injective eq of λ { refl → prepare-projects j w f s prepared }
 unwind-projects j s eq | just (w , f) | nothing = case eq of λ ()
 unwind-projects j s eq | just (w , f) | just Pool.bodyRunning = case eq of λ ()
 unwind-projects j s eq | just (w , f) | just (Pool.bodyReturned result) = case eq of λ ()
 unwind-projects j s eq | just (w , f) | just (Pool.deregisterPending exit) = case eq of λ ()
 unwind-projects j s eq | just (w , f) | just (Pool.deregistered exit) = case eq of λ ()
 unwind-projects j s eq | just (w , f) | just (Pool.resultAvailable exit) = case eq of λ ()
 replacement-projects : ∀ j err s {s′} → W.replaceUnwind j err s ≡ just s′ → Same s s′
 replacement-projects j err s eq with lookup j (P.jobs (W.protocolState s))
 ... | nothing = case eq of λ ()
 ... | just job with W.replacementEligible (Types.phase job) | W.ownerOf j s
 ...   | true | just (w , f) with does (w ≟ Types.owner job) | Pool.step (Pool.resumeAfterUnwindError j) (W.poolAt w s) in advanced
 ...     | true | just p with P.step (P.protocolException j err) (W.protocolState (W.setPool w f p s)) in captured
 ...       | nothing = case eq of λ ()
 ...       | just next = case just-injective eq of λ { refl → refl }
 replacement-projects j err s eq | just job | true | just (w , f) | false | _ = case eq of λ ()
 replacement-projects j err s eq | just job | true | just (w , f) | true | nothing = case eq of λ ()
 replacement-projects j err s eq | just job | false | _ = case eq of λ ()
 replacement-projects j err s eq | just job | true | nothing = case eq of λ ()

unchanged : ∀ a s {t} → W.step a s ≡ just t → W.controls t ≡ W.controls s → Base s → Controls s → Controls t
unchanged a s {t} actual same (core , pcs) controls = subst (λ rows → Rows rows (W.protocolState t)) (sym same)
 (proj₂ (proj₂ (Core.For.step-preserves isBearerClosed (Rows (W.controls s)) (rows-kept _) a s actual (core , pcs , controls))))
inherited : ∀ a s {t} → W.inherit a s ≡ just t → Base s → Controls s → Controls t
inherited a s eq (core , pcs) controls with W.delegateAllowed a s
... | false = case eq of λ ()
... | true with M.step a (W.base s) in actual
...   | nothing = case eq of λ ()
...   | just m = case just-injective eq of λ { refl → proj₂ (proj₂ (MF.For.step-preserves (Rows (W.controls s)) (rows-kept _) a (W.base s) actual (core , pcs , controls))) }

source-kept : ∀ action s {t} → W.viaSource action s ≡ just t → T.Retains (W.protocolState s) (W.protocolState t)
source-kept action s eq with O.advance (O.inbound (Machine.igStep action)) (W.source s)
... | nothing = case eq of λ ()
... | just c = case just-injective eq of λ { refl → T.source c (W.protocolState s) }
source-owner : ∀ w {s} → A.Owner w (W.protocolState s) → ∀ action (q : W.State) {t} → W.viaSource action q ≡ just t → q ≡ s → A.Owner w (W.protocolState t)
source-owner w own action s actual refl = proj₁ (T.Retains.owners (source-kept action s actual) w own)
pool-owner : ∀ w action s {t} → W.viaPool w action s ≡ just t → A.Owner w (W.protocolState t)
pool-owner w action s eq with W.ownerContext w s in context
... | nothing = case eq of λ ()
... | just (f , mid) with Pool.step action (W.poolAt w s) in actual
...   | nothing = case eq of λ ()
...   | just pool = case just-injective eq of λ { refl → proj₁ (T.Retains.owners (Up.pool-retains w f pool (W.protocolState s)
 (MF.owner-frame w (W.base s) context) (Up.Kernel.handles-retained action (W.poolAt w s) actual)) w (A.owner-context w (W.base s) context)) }
active : ∀ before pc → W.sameStage before pc ≡ true → W.sameStage before W.idle ≡ false → pc ≢ W.idle
active before pc matches nonidle idle = case trans (sym matches) (trans (cong (W.sameStage before) idle) nonidle) of λ ()

module Local where
 record CIPaths (s t : W.State) : Set where
  constructor paths
  field preserves : Controls s → Controls t
 ci-idle : ∀ s → CIPaths s s
 ci-idle s = paths (λ good → good)
 ci-compose : ∀ {s t u} → CIPaths s t → CIPaths t u → CIPaths s u
 ci-compose first second = paths (λ good → CIPaths.preserves second (CIPaths.preserves first good))
 ci-phase-paths : ∀ w pc s → (Controls s → A.Owner w (W.protocolState s)) → CIPaths s (W.setPhase w pc s)
 ci-phase-paths w pc s own = paths (λ good → phase-preserves w pc s (own good) good)
 ci-phase-after : ∀ w pc {s t} → CIPaths s t → (Controls t → A.Owner w (W.protocolState t)) → CIPaths s (W.setPhase w pc t)
 ci-phase-after w pc {t = t} path own = ci-compose path (ci-phase-paths w pc t own)
 ci-via-source-projects : ∀ action s {t} → W.viaSource action s ≡ just t → CIPaths s t
 ci-via-source-projects action s eq with O.advance (O.inbound (Machine.igStep action)) (W.source s)
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → paths (rows-kept _ (T.source c (W.protocolState s))) }
 ci-via-pool-projects : ∀ w action s {t} → W.viaPool w action s ≡ just t → (∀ C → Up.Kernel.NewReturn action C) → CIPaths s t
 ci-via-pool-projects w action s actual new = paths (via-pool-preserves w action s actual)
 ci-from-phase-projects : ∀ w before after s {s′} → W.fromPhase w before after s ≡ just s′ → W.sameStage before W.idle ≡ false → CIPaths s s′
 ci-from-phase-projects w before after s eq nonidle with W.sameStage before (W.phase (W.frameAt w s)) in matches
 ... | false = case eq of λ ()
 ... | true = case just-injective eq of λ { refl → ci-phase-paths w after s (λ good → A.ControlContent.owner-reference (current w s (active before (W.phase (W.frameAt w s)) matches nonidle) good)) }
 ci-source-phase-projects : ∀ w before after action s {s′} → W.sourcePhase w before after action s ≡ just s′ → CIPaths s s′
 ci-source-phase-projects w before after action s eq with W.sameStage before (W.phase (W.frameAt w s)) | W.ownerContext w s in context
 ... | true | just (f , mid) with W.viaSource (action mid) s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-phase-after w after (ci-via-source-projects (action mid) s advanced) (λ good → source-owner w (A.owner-context w (W.base s) context) (action mid) s advanced refl) }
 ci-source-phase-projects w before after action s eq | false | _ = case eq of λ ()
 ci-source-phase-projects w before after action s eq | true | nothing = case eq of λ ()
 ci-request-projects : ∀ w s {s′} → W.requestStop w s ≡ just s′ → CIPaths s s′
 ci-request-projects w s eq with lookup w (U.frames (P.base (W.protocolState s)))
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f
 ...   | U.promisePublished hid mid = ci-via-source-projects (IG.enqueueMuxStop mid) s eq
 ...   | (U.handshakePending helperPC) = case eq of λ ()
 ...   | U.returnedSuccess = case eq of λ ()
 ...   | U.handleAllocated hid mid = case eq of λ ()
 -- Counter retirement writes only the actual IG registry at scopeDone.
 ci-retire-projects : ∀ w s {s′} → W.retireFor w s ≡ just s′ → CIPaths s s′
 ci-retire-projects w s eq with W.retireAllowed (W.phase (W.frameAt w s))
 ... | false = case eq of λ ()
 ... | true with lookup w (U.frames (P.base (W.protocolState s)))
 ...   | nothing = case eq of λ ()
 ...   | just f with U.progress f
 ...     | U.promisePublished hid mid = ci-via-source-projects (IG.retireCells mid) s eq
 ...     | (U.handshakePending helperPC) = case eq of λ ()
 ...     | U.returnedSuccess = case eq of λ ()
 ...     | U.handleAllocated hid mid = case eq of λ ()
 ci-select-projects : ∀ w s {s′} → W.selectStop w s ≡ just s′ → CIPaths s s′
 ci-select-projects w s eq with W.phase (W.frameAt w s) in stage | M.pcAt w (W.base s) | W.ownerContext w s in context
 ... | W.idle | M.waiting | just (f , mid) with P.noParent (W.poolAt w s) | P.noResults (W.poolAt w s)
 ...   | true | true with W.viaSource (IG.takeShutdownCommand mid) s in advanced
 ...     | nothing = case eq of λ ()
 ...     | just next = case just-injective eq of λ { refl → ci-phase-after w W.shutdownSelected (ci-via-source-projects (IG.takeShutdownCommand mid) s advanced) (λ good → source-owner w (A.owner-context w (W.base s) context) (IG.takeShutdownCommand mid) s advanced refl) }
 ci-select-projects w s eq | W.idle | M.waiting | just (f , mid) | false | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.waiting | just (f , mid) | true | false = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.waiting | nothing = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.selected item | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.responderTracing result | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.initiatorTracing result | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.deadReady outcome | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.deadTracing outcome | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.finished outcome | _ = case eq of λ ()
 ci-select-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.groupClosing | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.draining | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-finish-group-projects : ∀ w s {s′} → W.finishMini w s ≡ just s′ → CIPaths s s′
 ci-finish-group-projects w s eq with W.phase (W.frameAt w s) in stage | W.cancelPC (W.frameAt w s) | W.remaining (W.frameAt w s)
 ... | W.groupClosing | W.ready | [] = case just-injective eq of λ { refl → ci-phase-paths w W.draining s (λ good → A.ControlContent.owner-reference (current w s (λ idle → case trans (sym stage) idle of λ ()) good)) }
 ... | W.groupClosing | W.ready | _ ∷ _ = case eq of λ ()
 ... | W.groupClosing | W.requested j | _ = case eq of λ ()
 ... | W.groupClosing | W.delivered j | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.idle | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.draining | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-abort-projects : ∀ w err s {s′} → W.abortMonitor w err s ≡ just s′ → CIPaths s s′
 ci-abort-projects w err s eq with W.abortStage w s | W.ownerContext w s in context | P.noParent (W.poolAt w s)
 ... | true | just (f , mid) | true with P.muxAt mid (W.protocolState s)
 ...   | just m with WireMux.callback m
 ...     | WireMux.returned = case just-injective eq of λ { refl → ci-phase-paths w (W.ownerAborting err) s (λ good → A.owner-context w (W.base s) context) }
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | WireMux.readActive tr = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | WireMux.commitTrace active tr = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | WireMux.afterStart n = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | WireMux.forkPending n = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | WireMux.afterFailure = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | WireMux.tracerFailed n = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | nothing = case eq of λ ()
 ci-abort-projects w err s eq | false | _ | _ = case eq of λ ()
 ci-abort-projects w err s eq | true | nothing | _ = case eq of λ ()
 ci-abort-projects w err s eq | true | just pair | false = case eq of λ ()
 ci-begin-whole-projects : ∀ w order s {s′} → W.beginWhole w order s ≡ just s′ → CIPaths s s′
 ci-begin-whole-projects w order s eq with W.wholeOutcome w s
 ... | nothing = case eq of λ ()
 ... | just outcome with W.viaPool w (Pool.beginClose order) s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-phase-after w (W.wholeClosing outcome) (ci-via-pool-projects w (Pool.beginClose order) s advanced (λ C → tt)) (λ good → pool-owner w (Pool.beginClose order) s advanced) }
 ci-whole-action-projects : ∀ w action s {s′} → W.wholeAction w action s ≡ just s′ → (∀ C → Up.Kernel.NewReturn action C) → CIPaths s s′
 ci-whole-action-projects w action s eq new with W.phase (W.frameAt w s)
 ... | W.wholeClosing outcome = ci-via-pool-projects w action s eq new
 ci-whole-action-projects w action s eq new | W.idle = case eq of λ ()
 ci-whole-action-projects w action s eq new | W.shutdownSelected = case eq of λ ()
 ci-whole-action-projects w action s eq new | W.stoppingTraced = case eq of λ ()
 ci-whole-action-projects w action s eq new | W.stoppingWritten = case eq of λ ()
 ci-whole-action-projects w action s eq new | W.groupClosing = case eq of λ ()
 ci-whole-action-projects w action s eq new | W.draining = case eq of λ ()
 ci-whole-action-projects w action s eq new | W.drainReady = case eq of λ ()
 ci-whole-action-projects w action s eq new | W.stoppedTrace = case eq of λ ()
 ci-whole-action-projects w action s eq new | W.stoppedTracing = case eq of λ ()
 ci-whole-action-projects w action s eq new | W.monitorReturnedNormal = case eq of λ ()
 ci-whole-action-projects w action s eq new | W.ownerAborting err = case eq of λ ()
 ci-whole-action-projects w action s eq new | W.wholeClosed outcome = case eq of λ ()
 ci-whole-action-projects w action s eq new | W.asyncFailureWritten err = case eq of λ ()
 ci-whole-action-projects w action s eq new | W.asyncDeadTracing err = case eq of λ ()
 ci-whole-action-projects w action s eq new | W.scopeDone outcome = case eq of λ ()
 ci-whole-delivery-projects : ∀ w s {s′} → W.deliverWholeChild w s ≡ just s′ → CIPaths s s′
 ci-whole-delivery-projects w s eq with W.phase (W.frameAt w s) in stage | W.ownerContext w s in context | Pool.phase (W.poolAt w s)
 ... | W.wholeClosing outcome | just (f , mid) | Pool.cancelPending j with W.wholeDeliverable w j f s
 ...   | true = ci-via-pool-projects w Pool.deliverCancel s eq (λ C → tt)
 ...   | false = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.wholeClosing outcome | nothing | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.idle | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.groupClosing | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.draining | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.wholeClosing outcome | just (f , mid) | Pool.openPool = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.wholeClosing outcome | just (f , mid) | Pool.closing = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.wholeClosing outcome | just (f , mid) | Pool.closedPool = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.wholeClosing outcome | just (f , mid) | Pool.joinPending j = case eq of λ ()
 ci-finish-whole-projects : ∀ w s {s′} → W.finishWhole w s ≡ just s′ → CIPaths s s′
 ci-finish-whole-projects w s eq with W.phase (W.frameAt w s)
 ... | W.wholeClosing outcome with W.viaPool w Pool.finishClose s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-phase-after w (W.wholeClosed outcome) (ci-via-pool-projects w Pool.finishClose s advanced (λ C → tt)) (λ good → pool-owner w Pool.finishClose s advanced) }
 ci-finish-whole-projects w s eq | W.idle = case eq of λ ()
 ci-finish-whole-projects w s eq | W.shutdownSelected = case eq of λ ()
 ci-finish-whole-projects w s eq | W.stoppingTraced = case eq of λ ()
 ci-finish-whole-projects w s eq | W.stoppingWritten = case eq of λ ()
 ci-finish-whole-projects w s eq | W.groupClosing = case eq of λ ()
 ci-finish-whole-projects w s eq | W.draining = case eq of λ ()
 ci-finish-whole-projects w s eq | W.drainReady = case eq of λ ()
 ci-finish-whole-projects w s eq | W.stoppedTrace = case eq of λ ()
 ci-finish-whole-projects w s eq | W.stoppedTracing = case eq of λ ()
 ci-finish-whole-projects w s eq | W.monitorReturnedNormal = case eq of λ ()
 ci-finish-whole-projects w s eq | W.ownerAborting err = case eq of λ ()
 ci-finish-whole-projects w s eq | W.wholeClosed outcome = case eq of λ ()
 ci-finish-whole-projects w s eq | W.asyncFailureWritten err = case eq of λ ()
 ci-finish-whole-projects w s eq | W.asyncDeadTracing err = case eq of λ ()
 ci-finish-whole-projects w s eq | W.scopeDone outcome = case eq of λ ()
 ci-async-failure-projects : ∀ w s {s′} → W.asyncFailure w s ≡ just s′ → CIPaths s s′
 ci-async-failure-projects w s eq with W.phase (W.frameAt w s) in stage | Pool.phase (W.poolAt w s) | W.ownerContext w s in context
 ... | W.wholeClosed (W.asyncExit err) | Pool.closedPool | just (f , mid) with W.viaSource (IG.recordAsyncMuxFailure mid err) s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-phase-after w (W.asyncFailureWritten err) (ci-via-source-projects (IG.recordAsyncMuxFailure mid err) s advanced) (λ good → source-owner w (A.owner-context w (W.base s) context) (IG.recordAsyncMuxFailure mid err) s advanced refl) }
 ci-async-failure-projects w s eq | W.wholeClosed W.normalExit | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.wholeClosed (W.failedExit err) | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.wholeClosed (W.asyncExit err) | Pool.closedPool | nothing = case eq of λ ()
 ci-async-failure-projects w s eq | W.idle | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.groupClosing | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.draining | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.wholeClosed (W.asyncExit err) | Pool.openPool | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.wholeClosed (W.asyncExit err) | Pool.closing | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.wholeClosed (W.asyncExit err) | Pool.cancelPending j | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.wholeClosed (W.asyncExit err) | Pool.joinPending j | _ = case eq of λ ()
 ci-async-dead-projects : ∀ w s {s′} → W.asyncDead w s ≡ just s′ → CIPaths s s′
 ci-async-dead-projects w s eq with W.phase (W.frameAt w s) in stage | W.ownerContext w s in context
 ... | W.asyncFailureWritten err | just (f , mid) with W.viaSource (IG.traceMuxDead mid) s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-phase-after w (W.asyncDeadTracing err) (ci-via-source-projects (IG.traceMuxDead mid) s advanced) (λ good → source-owner w (A.owner-context w (W.base s) context) (IG.traceMuxDead mid) s advanced refl) }
 ci-async-dead-projects w s eq | W.asyncFailureWritten err | nothing = case eq of λ ()
 ci-async-dead-projects w s eq | W.idle | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.shutdownSelected | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.stoppingTraced | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.stoppingWritten | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.groupClosing | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.draining | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.drainReady | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.stoppedTrace | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.stoppedTracing | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.monitorReturnedNormal | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.ownerAborting err | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.wholeClosing outcome | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.wholeClosed outcome | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.asyncDeadTracing err | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.scopeDone outcome | _ = case eq of λ ()
 ci-async-trace-projects : ∀ sample w s {s′} → W.asyncTrace sample w s ≡ just s′ → CIPaths s s′
 ci-async-trace-projects sample w s eq with W.phase (W.frameAt w s) in stage | W.ownerContext w s in context
 ... | W.asyncDeadTracing err | just (f , mid) with sample
 ...   | true = ci-via-source-projects (IG.sampleTracer mid) s eq
 ...   | false = ci-via-source-projects (IG.commitTracer mid) s eq
 ci-async-trace-projects sample w s eq | W.asyncDeadTracing err | nothing = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.idle | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.shutdownSelected | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.stoppingTraced | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.stoppingWritten | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.groupClosing | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.draining | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.drainReady | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.stoppedTrace | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.stoppedTracing | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.monitorReturnedNormal | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.ownerAborting err | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.wholeClosing outcome | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.wholeClosed outcome | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.asyncFailureWritten err | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.scopeDone outcome | _ = case eq of λ ()
 ci-finish-async-projects : ∀ w s {s′} → W.finishAsync w s ≡ just s′ → CIPaths s s′
 ci-finish-async-projects w s eq with W.phase (W.frameAt w s) in stage | W.ownerContext w s in context | Pool.phase (W.poolAt w s)
 ... | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool with P.muxAt mid (W.protocolState s)
 ...   | just m with WireMux.callback m | M.finishMatches (M.failed err) (WireMux.status m)
 ...     | WireMux.returned | true = case just-injective eq of λ { refl → ci-phase-paths w (W.scopeDone (W.asyncExit err)) s (λ good → A.owner-context w (W.base s) context) }
 ...     | WireMux.returned | false = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | WireMux.readActive tr | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | WireMux.commitTrace active tr | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | WireMux.afterStart n | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | WireMux.forkPending n | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | WireMux.afterFailure | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | WireMux.tracerFailed n | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | nothing = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | nothing | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.idle | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.groupClosing | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.draining | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.openPool = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closing = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.cancelPending j = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.joinPending j = case eq of λ ()
 ci-finish-ordinary-projects : ∀ w s {s′} → W.finishOrdinary w s ≡ just s′ → CIPaths s s′
 ci-finish-ordinary-projects w s eq with W.phase (W.frameAt w s) in stage | Pool.phase (W.poolAt w s)
 ... | W.wholeClosed W.normalExit | Pool.closedPool = case just-injective eq of λ { refl → ci-phase-paths w (W.scopeDone W.normalExit) s (λ good → A.ControlContent.owner-reference (current w s (λ idle → case trans (sym stage) idle of λ ()) good)) }
 ... | W.wholeClosed (W.failedExit err) | Pool.closedPool = case just-injective eq of λ { refl → ci-phase-paths w (W.scopeDone (W.failedExit err)) s (λ good → A.ControlContent.owner-reference (current w s (λ idle → case trans (sym stage) idle of λ ()) good)) }
 ... | W.wholeClosed (W.asyncExit err) | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.idle | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.shutdownSelected | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.stoppingTraced | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.stoppingWritten | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.groupClosing | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.draining | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.drainReady | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.stoppedTrace | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.stoppedTracing | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.monitorReturnedNormal | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.ownerAborting err | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosing outcome | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.asyncFailureWritten err | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.asyncDeadTracing err | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.scopeDone outcome | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed W.normalExit | Pool.openPool = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed W.normalExit | Pool.closing = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed W.normalExit | Pool.cancelPending j = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed W.normalExit | Pool.joinPending j = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed (W.failedExit err) | Pool.openPool = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed (W.failedExit err) | Pool.closing = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed (W.failedExit err) | Pool.cancelPending j = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed (W.failedExit err) | Pool.joinPending j = case eq of λ ()
 ci-finish-stopped-projects : ∀ w s {s′} → W.finishStopped w s ≡ just s′ → CIPaths s s′
 ci-finish-stopped-projects w s eq with W.sameStage W.stoppedTracing (W.phase (W.frameAt w s)) | W.ownerContext w s in context
 ... | true | just (f , mid) with P.muxAt mid (W.protocolState s)
 ...   | just m with WireMux.status m | WireMux.callback m
 ...     | WireMux.stopped | WireMux.returned = case just-injective eq of λ { refl → ci-phase-paths w W.monitorReturnedNormal s (λ good → A.owner-context w (W.base s) context) }
 ...     | WireMux.stopped | WireMux.readActive tr = case eq of λ ()
 ...     | WireMux.stopped | WireMux.commitTrace flag tr = case eq of λ ()
 ...     | WireMux.stopped | WireMux.afterStart n = case eq of λ ()
 ...     | WireMux.stopped | WireMux.forkPending n = case eq of λ ()
 ...     | WireMux.stopped | WireMux.afterFailure = case eq of λ ()
 ...     | WireMux.stopped | WireMux.tracerFailed n = case eq of λ ()
 ...     | WireMux.ready | _ = case eq of λ ()
 ...     | WireMux.stopping | _ = case eq of λ ()
 ...     | WireMux.failed err | _ = case eq of λ ()
 ci-finish-stopped-projects w s eq | true | just (f , mid) | nothing = case eq of λ ()
 ci-finish-stopped-projects w s eq | false | _ = case eq of λ ()
 ci-finish-stopped-projects w s eq | true | nothing = case eq of λ ()

 step-preserves : ∀ action s {s′} → W.step action s ≡ just s′ → Base s → Controls s → Controls s′
 step-preserves (W.run action) s eq core = inherited action s eq core
 step-preserves (W.requestShutdown w) s eq core = CIPaths.preserves (ci-request-projects w s eq)
 step-preserves (W.retireCounters w) s eq core = CIPaths.preserves (ci-retire-projects w s eq)
 step-preserves (W.selectShutdown w) s eq core = CIPaths.preserves (ci-select-projects w s eq)
 step-preserves (W.observeStoppingTrace w) s eq core = CIPaths.preserves (ci-from-phase-projects w W.shutdownSelected W.stoppingTraced s eq refl)
 step-preserves (W.writeStopping w) s eq core = CIPaths.preserves (ci-source-phase-projects w W.stoppingTraced W.stoppingWritten IG.recordMuxStopping s eq)
 step-preserves (W.captureGroup w order) s eq core = capture-preserves w order s eq (proj₁ core)
 step-preserves (W.requestGroupCancel w) s eq core = request-preserves w s eq
 step-preserves (W.deliverGroup w) s eq core = deliver-preserves w s eq
 step-preserves (W.joinGroup w) s eq core = join-preserves w s eq
 step-preserves (W.finishGroup w) s eq core = CIPaths.preserves (ci-finish-group-projects w s eq)
 step-preserves (W.drainEmpty w) s eq core = CIPaths.preserves (ci-from-phase-projects w W.draining W.drainReady s (GroupProperties.drain-phase isBearerClosed w s eq) refl)
 step-preserves (W.timeout2Elapsed w) s eq core = CIPaths.preserves (ci-from-phase-projects w W.draining W.drainReady s eq refl)
 step-preserves (W.writeStopped w) s eq core = CIPaths.preserves (ci-source-phase-projects w W.drainReady W.stoppedTrace IG.completeMuxStopping s eq)
 step-preserves (W.observeTraceStopped w) s eq core = CIPaths.preserves (ci-source-phase-projects w W.stoppedTrace W.stoppedTracing IG.traceGracefulMuxStopped s eq)
 step-preserves (W.sampleStoppedTracer w) s eq core = CIPaths.preserves (ci-source-phase-projects w W.stoppedTracing W.stoppedTracing IG.sampleTracer s eq)
 step-preserves (W.commitStoppedTracer w) s eq core = CIPaths.preserves (ci-source-phase-projects w W.stoppedTracing W.stoppedTracing IG.commitTracer s eq)
 step-preserves (W.finishStoppedTrace w) s eq core = CIPaths.preserves (ci-finish-stopped-projects w s eq)
 step-preserves (W.finishChildUnwind j) s eq core = unchanged (W.finishChildUnwind j) s eq (ControlStore.unwind-projects j s eq) core
 step-preserves (W.unwindReplacedBySync j err) s eq core = unchanged (W.unwindReplacedBySync j err) s eq (ControlStore.replacement-projects j err s eq) core
 step-preserves (W.abortOwner w err) s eq core = CIPaths.preserves (ci-abort-projects w err s eq)
 step-preserves (W.beginWholeClose w order) s eq core = CIPaths.preserves (ci-begin-whole-projects w order s eq)
 step-preserves (W.requestWholeCancel w) s eq core = CIPaths.preserves (ci-whole-action-projects w Pool.requestCancel s eq (λ C → tt))
 step-preserves (W.deliverWhole w) s eq core = CIPaths.preserves (ci-whole-delivery-projects w s eq)
 step-preserves (W.joinWhole w) s eq core = CIPaths.preserves (ci-whole-action-projects w Pool.join s eq (λ C → tt))
 step-preserves (W.finishWholeClose w) s eq core = CIPaths.preserves (ci-finish-whole-projects w s eq)
 step-preserves (W.finishNormalScope w) s eq core = CIPaths.preserves (ci-finish-ordinary-projects w s eq)
 step-preserves (W.writeAsyncFailure w) s eq core = CIPaths.preserves (ci-async-failure-projects w s eq)
 step-preserves (W.beginAsyncDead w) s eq core = CIPaths.preserves (ci-async-dead-projects w s eq)
 step-preserves (W.sampleAsyncTracer w) s eq core = CIPaths.preserves (ci-async-trace-projects true w s eq)
 step-preserves (W.commitAsyncTracer w) s eq core = CIPaths.preserves (ci-async-trace-projects false w s eq)
 step-preserves (W.finishAsyncDead w) s eq core = CIPaths.preserves (ci-finish-async-projects w s eq)

import ConnectionManagement.Properties.LiveTrackerAuxProtocol as ProtocolFacts
module For (Obs : P.State → Set) (stable : ∀ {s t} → T.Retains s t → Obs s → Obs t) where
 Observer : ∀ pcs rows → P.State → Set
 Observer pcs rows p = MF.PCs pcs p × (Rows rows p × Obs p)
 observer : ∀ pcs rows {s t} → T.Retains s t → Observer pcs rows s → Observer pcs rows t
 observer pcs rows kept (covered , controls , old) =
   Data.List.Relation.Unary.All.map (λ { {w , pc} → T.pc-kept kept w pc }) covered , rows-kept rows kept controls , stable kept old
 Valid : W.State → Set
 Valid s = Up.Valid (W.protocolState s) × Observer (M.pcs (W.base s)) (W.controls s) (W.protocolState s)
 source-valid : ∀ c s → Valid s → Valid (W.setSource c s)
 source-valid c s = ProtocolFacts.For.source-valid isBearerClosed (Observer (M.pcs (W.base s)) (W.controls s)) (observer _ _) c (W.protocolState s)
 step-preserves : ∀ a s {t} → W.step a s ≡ just t → Valid s → Valid t
 step-preserves a s actual (core , pcs , controls , old) =
   proj₁ next , proj₁ (proj₂ next) , Local.step-preserves a s actual (core , pcs) controls , proj₂ (proj₂ next)
  where next = Core.For.step-preserves isBearerClosed Obs stable a s actual (core , pcs , old)
