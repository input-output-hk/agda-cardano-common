{-# OPTIONS --guardedness #-}

-- Group operations retain joint core/PC content and any certified observer.
open import Data.Bool using (Bool)
open import ConnectionManagement.Domain using (ErrorId)
module ConnectionManagement.Properties.LiveTrackerAuxGroup (isBearerClosed : ErrorId → Bool) where
open import Data.Bool using (true; false; _∧_)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no; does)
open import Class.DecEq using (_≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as Machine
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as WireMux
import ConnectionManagement.MuxProtocolJobs as P
import ConnectionManagement.MuxGroupShutdown as Group
import ConnectionManagement.Properties.MuxGroupShutdown as GroupProperties
import ConnectionManagement.Properties.LiveTrackerAuxMonitor as MonitorFacts
import ConnectionManagement.Properties.LiveTrackerAuxProtocol as ProtocolFacts
import ConnectionManagement.Properties.LiveTrackerAuxCancellation as Cancellation
import ConnectionManagement.Properties.LiveTrackerAuxUpdates as Updates
import ConnectionManagement.Properties.LiveTrackerAuxTransport as Transport
module W = Group isBearerClosed
module M = W.M
module U = P.U
module Pool = P.Pool
module Up = Updates isBearerClosed
module T = Transport isBearerClosed
module MF = MonitorFacts isBearerClosed

import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.IGTypes
import Data.Nat

-- Cancellation preparation edits no monitor PCs, even on clean-result discard.
module PCStore where
 Same : W.State → W.State → Set
 Same s t = M.pcs (W.base t) ≡ M.pcs (W.base s)
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
module For (Obs : P.State → Set) (stable : ∀ {s t} → T.Retains s t → Obs s → Obs t) where
 Observer : ∀ rows → P.State → Set
 Observer rows s = MF.PCs rows s × Obs s
 observer : ∀ rows {s t} → T.Retains s t → Observer rows s → Observer rows t
 observer rows kept (pcs , observed) = All.map (λ { {w , pc} → T.pc-kept kept w pc }) pcs , stable kept observed
 Valid : W.State → Set
 Valid s = Up.Valid (W.protocolState s) × Observer (M.pcs (W.base s)) (W.protocolState s)
 module Lower = MF.For Obs stable
 -- Group actions preserve the PC store except inherited monitor actions.
 source-valid : ∀ c s → Valid s → Valid (W.setSource c s)
 source-valid c s = ProtocolFacts.For.source-valid isBearerClosed (Observer (M.pcs (W.base s))) (observer _) c (W.protocolState s)
 module CancelFor (rows : ConnectionManagement.Store.Store ConnectionManagement.Domain.WorkerId M.PC) = Cancellation.For isBearerClosed (Observer rows) (observer rows)
 record CIPaths (s t : W.State) : Set where
  constructor paths
  field preserves : Valid s → Valid t
 ci-idle : ∀ s → CIPaths s s
 ci-idle s = paths (λ valid → valid)
 ci-compose : ∀ {s t u} → CIPaths s t → CIPaths t u → CIPaths s u
 ci-compose first second = paths (λ valid → CIPaths.preserves second (CIPaths.preserves first valid))
 ci-frame-paths : ∀ w f s → CIPaths s (W.setFrame w f s)
 ci-frame-paths w f s = paths (λ valid → valid)
 ci-phase-paths : ∀ w pc s → CIPaths s (W.setPhase w pc s)
 ci-phase-paths w pc s = ci-frame-paths w _ s
 ci-phase-after : ∀ w pc {before after} → CIPaths before after → CIPaths before (W.setPhase w pc after)
 ci-phase-after w pc {after = after} path = ci-compose path (ci-phase-paths w pc after)
 ci-frame-after : ∀ w f {before after} → CIPaths before after → CIPaths before (W.setFrame w f after)
 ci-frame-after w f {after = after} path = ci-compose path (ci-frame-paths w f after)
 ci-via-source-projects : ∀ action s {t} → W.viaSource action s ≡ just t → CIPaths s t
 ci-via-source-projects action s actual with O.advance (O.inbound (Machine.igStep action)) (W.source s)
 ... | nothing = case actual of λ ()
 ... | just c = case just-injective actual of λ { refl → paths (source-valid c s) }
 ci-via-pool-projects : ∀ w action s {t} → W.viaPool w action s ≡ just t →
   (∀ C → Up.Kernel.NewReturn action C) → CIPaths s t
 ci-via-pool-projects w action s actual new = paths (proof actual)
  where
  proof : ∀ {t} → W.viaPool w action s ≡ just t → Valid s → Valid t
  proof eq valid with W.ownerContext w s in context
  ... | nothing = case eq of λ ()
  ... | just (f , mid) with Pool.step action (W.poolAt w s) in advanced
  ...   | nothing = case eq of λ ()
  ...   | just pool = case just-injective eq of λ { refl → ProtocolFacts.For.pool-valid isBearerClosed (Observer (M.pcs (W.base s))) (observer _) w f action (W.protocolState s)
    (MF.owner-frame w (W.base s) context) advanced (new _) valid }
 inherited : ∀ a s {t} → W.inherit a s ≡ just t → Valid s → Valid t
 inherited a s eq valid with W.delegateAllowed a s
 ... | false = case eq of λ ()
 ... | true with M.step a (W.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just m = case just-injective eq of λ { refl → Lower.step-preserves a (W.base s) actual valid }
 ci-from-phase-projects : ∀ w before after s {s′} → W.fromPhase w before after s ≡ just s′ → CIPaths s s′
 ci-from-phase-projects w before after s eq with W.sameStage before (W.phase (W.frameAt w s))
 ... | false = case eq of λ ()
 ... | true = case just-injective eq of λ { refl → ci-phase-paths w after s }
 ci-source-phase-projects : ∀ w before after action s {s′} → W.sourcePhase w before after action s ≡ just s′ → CIPaths s s′
 ci-source-phase-projects w before after action s eq with W.sameStage before (W.phase (W.frameAt w s)) | W.ownerContext w s
 ... | true | just (f , mid) with W.viaSource (action mid) s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-phase-after w after (ci-via-source-projects (action mid) s advanced) }
 ci-source-phase-projects w before after action s eq | false | _ = case eq of λ ()
 ci-source-phase-projects w before after action s eq | true | nothing = case eq of λ ()
 ci-request-projects : ∀ w s {s′} → W.requestStop w s ≡ just s′ → CIPaths s s′
 ci-request-projects w s eq with lookup w (U.frames (P.base (W.protocolState s)))
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f
 ...   | U.promisePublished hid mid = ci-via-source-projects (IG.enqueueMuxStop mid) s eq
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
 ...     | U.returnedSuccess = case eq of λ ()
 ...     | U.handleAllocated hid mid = case eq of λ ()
 ci-select-projects : ∀ w s {s′} → W.selectStop w s ≡ just s′ → CIPaths s s′
 ci-select-projects w s eq with W.phase (W.frameAt w s) | M.pcAt w (W.base s) | W.ownerContext w s
 ... | W.idle | M.waiting | just (f , mid) with P.noParent (W.poolAt w s) | P.noResults (W.poolAt w s)
 ...   | true | true with W.viaSource (IG.takeShutdownCommand mid) s in advanced
 ...     | nothing = case eq of λ ()
 ...     | just next = case just-injective eq of λ { refl → ci-phase-after w W.shutdownSelected (ci-via-source-projects (IG.takeShutdownCommand mid) s advanced) }
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
 ci-capture-projects : ∀ w order s {s′} → W.captureMini w order s ≡ just s′ → CIPaths s s′
 ci-capture-projects w order s eq with W.phase (W.frameAt w s) | Pool.sameSnapshot order (W.registeredMini w s) | P.noParent (W.poolAt w s)
 ... | W.stoppingWritten | true | true = case just-injective eq of λ { refl → ci-frame-paths w _ s }
 ... | W.stoppingWritten | false | _ = case eq of λ ()
 ... | W.stoppingWritten | true | false = case eq of λ ()
 ci-capture-projects w order s eq | W.idle | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.groupClosing | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.draining | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-request-group-projects : ∀ w s {s′} → W.requestGroup w s ≡ just s′ → CIPaths s s′
 ci-request-group-projects w s eq with W.phase (W.frameAt w s) | W.cancelPC (W.frameAt w s) | W.remaining (W.frameAt w s)
 ... | W.groupClosing | W.ready | j ∷ rest = case just-injective eq of λ { refl → ci-frame-paths w _ s }
 ... | W.groupClosing | W.ready | [] = case eq of λ ()
 ... | W.groupClosing | W.requested j | _ = case eq of λ ()
 ... | W.groupClosing | W.delivered j | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.idle | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.draining | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-deliver-group-projects : ∀ w s {s′} → W.deliverMini w s ≡ just s′ → CIPaths s s′
 ci-deliver-group-projects w s eq with W.phase (W.frameAt w s) | W.cancelPC (W.frameAt w s) | W.remaining (W.frameAt w s)
 ... | W.groupClosing | W.requested j | current ∷ rest with j ≟ current | W.miniMember w j s | W.childEligible j s
 ...   | yes same | true | true with W.viaPool w (Pool.interruptJob j) s in advanced
 ...     | nothing = case eq of λ ()
 ...     | just next = case just-injective eq of λ { refl → ci-frame-after w _ (ci-via-pool-projects w (Pool.interruptJob j) s advanced (λ C → tt)) }
 ci-deliver-group-projects w s eq | W.groupClosing | W.requested j | current ∷ rest | no apart | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.groupClosing | W.requested j | current ∷ rest | yes same | false | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.groupClosing | W.requested j | current ∷ rest | yes same | true | false = case eq of λ ()
 ci-deliver-group-projects w s eq | W.groupClosing | W.requested j | [] = case eq of λ ()
 ci-deliver-group-projects w s eq | W.groupClosing | W.ready | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.groupClosing | W.delivered j | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.idle | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.draining | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-join-head-projects : ∀ w current s {s′} → W.joinMiniHead w current s ≡ just s′ → CIPaths s s′
 ci-join-head-projects w current s eq with W.remaining (W.frameAt w s) | lookup current (Pool.handles (W.poolAt w s))
 ... | head ∷ rest | just (Pool.resultAvailable exit) with current ≟ head
 ...   | yes same = case just-injective eq of λ { refl → ci-frame-paths w _ s }
 ...   | no apart = case eq of λ ()
 ci-join-head-projects w current s eq | [] | _ = case eq of λ ()
 ci-join-head-projects w current s eq | _ ∷ _ | nothing = case eq of λ ()
 ci-join-head-projects w current s eq | _ ∷ _ | just Pool.bodyRunning = case eq of λ ()
 ci-join-head-projects w current s eq | _ ∷ _ | just (Pool.bodyReturned result) = case eq of λ ()
 ci-join-head-projects w current s eq | _ ∷ _ | just Pool.bodyUnwinding = case eq of λ ()
 ci-join-head-projects w current s eq | _ ∷ _ | just (Pool.deregisterPending exit) = case eq of λ ()
 ci-join-head-projects w current s eq | _ ∷ _ | just (Pool.deregistered exit) = case eq of λ ()
 ci-join-group-projects : ∀ w s {s′} → W.joinMini w s ≡ just s′ → CIPaths s s′
 ci-join-group-projects w s eq with W.phase (W.frameAt w s) | W.cancelPC (W.frameAt w s)
 ... | W.groupClosing | W.requested j = ci-join-head-projects w j s eq
 ... | W.groupClosing | W.delivered j = ci-join-head-projects w j s eq
 ... | W.groupClosing | W.ready = case eq of λ ()
 ci-join-group-projects w s eq | W.idle | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.shutdownSelected | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.stoppingTraced | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.stoppingWritten | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.draining | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.drainReady | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.stoppedTrace | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.stoppedTracing | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.monitorReturnedNormal | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.ownerAborting err | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.wholeClosing outcome | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.wholeClosed outcome | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.asyncFailureWritten err | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.asyncDeadTracing err | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.scopeDone outcome | _ = case eq of λ ()
 ci-finish-group-projects : ∀ w s {s′} → W.finishMini w s ≡ just s′ → CIPaths s s′
 ci-finish-group-projects w s eq with W.phase (W.frameAt w s) | W.cancelPC (W.frameAt w s) | W.remaining (W.frameAt w s)
 ... | W.groupClosing | W.ready | [] = case just-injective eq of λ { refl → ci-phase-paths w W.draining s }
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
 ci-unwind-projects : ∀ j s {t} → W.unwindChild j s ≡ just t → CIPaths s t
 ci-unwind-projects j s actual = paths (λ valid → let good = CancelFor.unwind-preserves (M.pcs (W.base s)) j s actual valid in
   proj₁ good , subst (λ rows → Observer rows _) (sym (PCStore.unwind-projects j s actual)) (proj₂ good))
 ci-replacement-projects : ∀ j err s {t} → W.replaceUnwind j err s ≡ just t → CIPaths s t
 ci-replacement-projects j err s actual = paths (λ valid → let good = CancelFor.replacement-preserves (M.pcs (W.base s)) j err s actual valid in
   proj₁ good , subst (λ rows → Observer rows _) (sym (PCStore.replacement-projects j err s actual)) (proj₂ good))
 ci-abort-projects : ∀ w err s {s′} → W.abortMonitor w err s ≡ just s′ → CIPaths s s′
 ci-abort-projects w err s eq with W.abortStage w s | W.ownerContext w s | P.noParent (W.poolAt w s)
 ... | true | just (f , mid) | true with P.muxAt mid (W.protocolState s)
 ...   | just m with WireMux.callback m
 ...     | WireMux.returned = case just-injective eq of λ { refl → ci-phase-paths w (W.ownerAborting err) s }
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
 ...   | just next = case just-injective eq of λ { refl → ci-phase-after w (W.wholeClosing outcome) (ci-via-pool-projects w (Pool.beginClose order) s advanced (λ C → tt)) }
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
 ci-whole-delivery-projects w s eq with W.phase (W.frameAt w s) | W.ownerContext w s | Pool.phase (W.poolAt w s)
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
 ...   | just next = case just-injective eq of λ { refl → ci-phase-after w (W.wholeClosed outcome) (ci-via-pool-projects w Pool.finishClose s advanced (λ C → tt)) }
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
 ci-async-failure-projects w s eq with W.phase (W.frameAt w s) | Pool.phase (W.poolAt w s) | W.ownerContext w s
 ... | W.wholeClosed (W.asyncExit err) | Pool.closedPool | just (f , mid) with W.viaSource (IG.recordAsyncMuxFailure mid err) s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-phase-after w (W.asyncFailureWritten err) (ci-via-source-projects (IG.recordAsyncMuxFailure mid err) s advanced) }
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
 ci-async-dead-projects w s eq with W.phase (W.frameAt w s) | W.ownerContext w s
 ... | W.asyncFailureWritten err | just (f , mid) with W.viaSource (IG.traceMuxDead mid) s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-phase-after w (W.asyncDeadTracing err) (ci-via-source-projects (IG.traceMuxDead mid) s advanced) }
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
 ci-async-trace-projects sample w s eq with W.phase (W.frameAt w s) | W.ownerContext w s
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
 ci-finish-async-projects w s eq with W.phase (W.frameAt w s) | W.ownerContext w s | Pool.phase (W.poolAt w s)
 ... | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool with P.muxAt mid (W.protocolState s)
 ...   | just m with WireMux.callback m | M.finishMatches (M.failed err) (WireMux.status m)
 ...     | WireMux.returned | true = case just-injective eq of λ { refl → ci-phase-paths w (W.scopeDone (W.asyncExit err)) s }
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
 ci-finish-ordinary-projects w s eq with W.phase (W.frameAt w s) | Pool.phase (W.poolAt w s)
 ... | W.wholeClosed W.normalExit | Pool.closedPool = case just-injective eq of λ { refl → ci-phase-paths w (W.scopeDone W.normalExit) s }
 ... | W.wholeClosed (W.failedExit err) | Pool.closedPool = case just-injective eq of λ { refl → ci-phase-paths w (W.scopeDone (W.failedExit err)) s }
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
 ci-finish-stopped-projects w s eq with W.sameStage W.stoppedTracing (W.phase (W.frameAt w s)) | W.ownerContext w s
 ... | true | just (f , mid) with P.muxAt mid (W.protocolState s)
 ...   | just m with WireMux.status m | WireMux.callback m
 ...     | WireMux.stopped | WireMux.returned = case just-injective eq of λ { refl → ci-phase-paths w W.monitorReturnedNormal s }
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

 step-preserves : ∀ action s {s′} → W.step action s ≡ just s′ → Valid s → Valid s′
 step-preserves (W.run action) s eq = inherited action s eq
 step-preserves (W.requestShutdown w) s eq = CIPaths.preserves (ci-request-projects w s eq)
 step-preserves (W.retireCounters w) s eq = CIPaths.preserves (ci-retire-projects w s eq)
 step-preserves (W.selectShutdown w) s eq = CIPaths.preserves (ci-select-projects w s eq)
 step-preserves (W.observeStoppingTrace w) s eq = CIPaths.preserves (ci-from-phase-projects w W.shutdownSelected W.stoppingTraced s eq)
 step-preserves (W.writeStopping w) s eq = CIPaths.preserves (ci-source-phase-projects w W.stoppingTraced W.stoppingWritten IG.recordMuxStopping s eq)
 step-preserves (W.captureGroup w order) s eq = CIPaths.preserves (ci-capture-projects w order s eq)
 step-preserves (W.requestGroupCancel w) s eq = CIPaths.preserves (ci-request-group-projects w s eq)
 step-preserves (W.deliverGroup w) s eq = CIPaths.preserves (ci-deliver-group-projects w s eq)
 step-preserves (W.joinGroup w) s eq = CIPaths.preserves (ci-join-group-projects w s eq)
 step-preserves (W.finishGroup w) s eq = CIPaths.preserves (ci-finish-group-projects w s eq)
 step-preserves (W.drainEmpty w) s eq = CIPaths.preserves (ci-from-phase-projects w W.draining W.drainReady s (GroupProperties.drain-phase isBearerClosed w s eq))
 step-preserves (W.timeout2Elapsed w) s eq = CIPaths.preserves (ci-from-phase-projects w W.draining W.drainReady s eq)
 step-preserves (W.writeStopped w) s eq = CIPaths.preserves (ci-source-phase-projects w W.drainReady W.stoppedTrace IG.completeMuxStopping s eq)
 step-preserves (W.observeTraceStopped w) s eq = CIPaths.preserves (ci-source-phase-projects w W.stoppedTrace W.stoppedTracing IG.traceGracefulMuxStopped s eq)
 step-preserves (W.sampleStoppedTracer w) s eq = CIPaths.preserves (ci-source-phase-projects w W.stoppedTracing W.stoppedTracing IG.sampleTracer s eq)
 step-preserves (W.commitStoppedTracer w) s eq = CIPaths.preserves (ci-source-phase-projects w W.stoppedTracing W.stoppedTracing IG.commitTracer s eq)
 step-preserves (W.finishStoppedTrace w) s eq = CIPaths.preserves (ci-finish-stopped-projects w s eq)
 step-preserves (W.finishChildUnwind j) s eq = CIPaths.preserves (ci-unwind-projects j s eq)
 step-preserves (W.unwindReplacedBySync j err) s eq = CIPaths.preserves (ci-replacement-projects j err s eq)
 step-preserves (W.abortOwner w err) s eq = CIPaths.preserves (ci-abort-projects w err s eq)
 step-preserves (W.beginWholeClose w order) s eq = CIPaths.preserves (ci-begin-whole-projects w order s eq)
 step-preserves (W.requestWholeCancel w) s eq = CIPaths.preserves (ci-whole-action-projects w Pool.requestCancel s eq (λ C → tt))
 step-preserves (W.deliverWhole w) s eq = CIPaths.preserves (ci-whole-delivery-projects w s eq)
 step-preserves (W.joinWhole w) s eq = CIPaths.preserves (ci-whole-action-projects w Pool.join s eq (λ C → tt))
 step-preserves (W.finishWholeClose w) s eq = CIPaths.preserves (ci-finish-whole-projects w s eq)
 step-preserves (W.finishNormalScope w) s eq = CIPaths.preserves (ci-finish-ordinary-projects w s eq)
 step-preserves (W.writeAsyncFailure w) s eq = CIPaths.preserves (ci-async-failure-projects w s eq)
 step-preserves (W.beginAsyncDead w) s eq = CIPaths.preserves (ci-async-dead-projects w s eq)
 step-preserves (W.sampleAsyncTracer w) s eq = CIPaths.preserves (ci-async-trace-projects true w s eq)
 step-preserves (W.commitAsyncTracer w) s eq = CIPaths.preserves (ci-async-trace-projects false w s eq)
 step-preserves (W.finishAsyncDead w) s eq = CIPaths.preserves (ci-finish-async-projects w s eq)
