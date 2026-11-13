{-# OPTIONS --guardedness #-}

-- Caller bookkeeping through mux group shutdown: its own actions write the
-- source only by inbound dispatcher steps or a lower protocol-job step.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.SourceKeysGroup (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (_≟_)
import Data.Nat as Nat
open import ConnectionManagement.Domain hiding (job)
open import ConnectionManagement.IGTypes using (RunResult; clean; errored)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.MuxGroupShutdown as Group
open import ConnectionManagement.Properties.OutboundKeys
import ConnectionManagement.Properties.SourceKeysProtocol as ProtocolKeys
import ConnectionManagement.Properties.SourceKeysMonitor as MonitorKeys
private
  module G = Group isBearerClosed
  module M = G.M
  module P = G.P
  module U = G.U
  module Pool = G.Pool
  module Lower = MonitorKeys isBearerClosed

rootG : G.Action → Maybe O.Action
rootG (G.run a) = Lower.rootM a
rootG _ = nothing
Same : G.State → G.State → Set
Same s s′ = KeySame (G.source s) (G.source s′)

inherit-keys : ∀ a s {s′} → G.inherit a s ≡ just s′ → Effect (Lower.rootM a) (G.source s) (G.source s′)
inherit-keys a s eq with G.delegateAllowed a s
... | false = case eq of λ ()
... | true with M.step a (G.base s) in stepped
...   | nothing = case eq of λ ()
...   | just next = case just-injective eq of λ { refl → Lower.step-keysM a (G.base s) stepped }
via-keys : ∀ act s {s′} → G.viaSource act s ≡ just s′ → Same s s′
via-keys act s eq with O.advance (O.inbound (Machine.igStep act)) (G.source s) in advanced
... | nothing = case eq of λ ()
... | just c = case just-injective eq of λ { refl → nonkey (O.inbound (Machine.igStep act)) (G.source s) refl advanced }
pool-keys : ∀ w act s {s′} → G.viaPool w act s ≡ just s′ → Same s s′
pool-keys w act s eq with G.ownerContext w s
... | nothing = case eq of λ ()
... | just (f , mid) with Pool.step act (G.poolAt w s)
...   | nothing = case eq of λ ()
...   | just p = case just-injective eq of λ { refl → same-refl _ }
from-keys : ∀ w before after s {s′} → G.fromPhase w before after s ≡ just s′ → Same s s′
from-keys w before after s eq with G.sameStage before (G.phase (G.frameAt w s))
... | false = case eq of λ ()
... | true = case just-injective eq of λ { refl → same-refl _ }
source-phase-keys : ∀ w before after act s {s′} → G.sourcePhase w before after act s ≡ just s′ → Same s s′
source-phase-keys w before after act s eq with G.sameStage before (G.phase (G.frameAt w s)) | G.ownerContext w s
... | true | just (f , mid) with G.viaSource (act mid) s in via
...   | nothing = case eq of λ ()
...   | just next = case just-injective eq of λ { refl → via-keys (act mid) s via }
source-phase-keys w before after act s eq | true | nothing = case eq of λ ()
source-phase-keys w before after act s eq | false | _ = case eq of λ ()
request-stop-keys : ∀ w s {s′} → G.requestStop w s ≡ just s′ → Same s s′
request-stop-keys w s eq with lookup w (U.frames (P.base (G.protocolState s)))
... | nothing = case eq of λ ()
... | just f with U.progress f
...   | U.promisePublished hid mid = via-keys (IG.enqueueMuxStop mid) s eq
...   | (U.handshakePending helperPC) = case eq of λ ()
...   | U.returnedSuccess = case eq of λ ()
...   | U.handleAllocated _ _ = case eq of λ ()
retire-keys : ∀ w s {s′} → G.retireFor w s ≡ just s′ → Same s s′
retire-keys w s eq with G.retireAllowed (G.phase (G.frameAt w s))
... | false = case eq of λ ()
... | true with lookup w (U.frames (P.base (G.protocolState s)))
...   | nothing = case eq of λ ()
...   | just f with U.progress f
...     | U.promisePublished hid mid = via-keys (IG.retireCells mid) s eq
...     | (U.handshakePending helperPC) = case eq of λ ()
...     | U.returnedSuccess = case eq of λ ()
...     | U.handleAllocated _ _ = case eq of λ ()
select-stop-keys : ∀ w s {s′} → G.selectStop w s ≡ just s′ → Same s s′
select-stop-keys w s eq with G.phase (G.frameAt w s) | M.pcAt w (G.base s) | G.ownerContext w s
... | G.idle | M.waiting | just (f , mid) with P.noParent (G.poolAt w s) | P.noResults (G.poolAt w s)
...   | true | true with G.viaSource (IG.takeShutdownCommand mid) s in via
...     | nothing = case eq of λ ()
...     | just next = case just-injective eq of λ { refl → via-keys (IG.takeShutdownCommand mid) s via }
select-stop-keys w s eq | G.idle | M.waiting | just (f , mid) | true | false = case eq of λ ()
select-stop-keys w s eq | G.idle | M.waiting | just (f , mid) | false | _ = case eq of λ ()
select-stop-keys w s eq | G.idle | M.waiting | nothing = case eq of λ ()
select-stop-keys w s eq | G.idle | M.selected _ | _ = case eq of λ ()
select-stop-keys w s eq | G.idle | M.responderTracing _ | _ = case eq of λ ()
select-stop-keys w s eq | G.idle | M.initiatorTracing _ | _ = case eq of λ ()
select-stop-keys w s eq | G.idle | M.deadReady _ | _ = case eq of λ ()
select-stop-keys w s eq | G.idle | M.deadTracing _ | _ = case eq of λ ()
select-stop-keys w s eq | G.idle | M.finished _ | _ = case eq of λ ()
select-stop-keys w s eq | G.shutdownSelected | _ | _ = case eq of λ ()
select-stop-keys w s eq | G.stoppingTraced | _ | _ = case eq of λ ()
select-stop-keys w s eq | G.stoppingWritten | _ | _ = case eq of λ ()
select-stop-keys w s eq | G.groupClosing | _ | _ = case eq of λ ()
select-stop-keys w s eq | G.draining | _ | _ = case eq of λ ()
select-stop-keys w s eq | G.drainReady | _ | _ = case eq of λ ()
select-stop-keys w s eq | G.stoppedTrace | _ | _ = case eq of λ ()
select-stop-keys w s eq | G.stoppedTracing | _ | _ = case eq of λ ()
select-stop-keys w s eq | G.monitorReturnedNormal | _ | _ = case eq of λ ()
select-stop-keys w s eq | G.ownerAborting _ | _ | _ = case eq of λ ()
select-stop-keys w s eq | G.wholeClosing _ | _ | _ = case eq of λ ()
select-stop-keys w s eq | G.wholeClosed _ | _ | _ = case eq of λ ()
select-stop-keys w s eq | G.scopeDone _ | _ | _ = case eq of λ ()
select-stop-keys w s eq | G.asyncFailureWritten _ | _ | _ = case eq of λ ()
select-stop-keys w s eq | G.asyncDeadTracing _ | _ | _ = case eq of λ ()
drain-keys : ∀ w s {s′} → G.observeDrain w s ≡ just s′ → Same s s′
drain-keys w s eq with G.ownerContext w s
... | nothing = case eq of λ ()
... | just (f , mid) with P.muxAt mid (G.protocolState s)
...   | nothing = case eq of λ ()
...   | just m with Mux.Egress.drainReady (Mux.egress m)
...     | false = case eq of λ ()
...     | true = from-keys w G.draining G.drainReady s eq
capture-keys : ∀ w order s {s′} → G.captureMini w order s ≡ just s′ → Same s s′
capture-keys w order s eq with G.phase (G.frameAt w s) | Pool.sameSnapshot order (G.registeredMini w s) | P.noParent (G.poolAt w s)
... | G.stoppingWritten | true | true = case just-injective eq of λ { refl → same-refl _ }
capture-keys w order s eq | G.idle | _ | _ = case eq of λ ()
capture-keys w order s eq | G.shutdownSelected | _ | _ = case eq of λ ()
capture-keys w order s eq | G.stoppingTraced | _ | _ = case eq of λ ()
capture-keys w order s eq | G.stoppingWritten | true | false = case eq of λ ()
capture-keys w order s eq | G.stoppingWritten | false | _ = case eq of λ ()
capture-keys w order s eq | G.groupClosing | _ | _ = case eq of λ ()
capture-keys w order s eq | G.draining | _ | _ = case eq of λ ()
capture-keys w order s eq | G.drainReady | _ | _ = case eq of λ ()
capture-keys w order s eq | G.stoppedTrace | _ | _ = case eq of λ ()
capture-keys w order s eq | G.stoppedTracing | _ | _ = case eq of λ ()
capture-keys w order s eq | G.monitorReturnedNormal | _ | _ = case eq of λ ()
capture-keys w order s eq | G.ownerAborting _ | _ | _ = case eq of λ ()
capture-keys w order s eq | G.wholeClosing _ | _ | _ = case eq of λ ()
capture-keys w order s eq | G.wholeClosed _ | _ | _ = case eq of λ ()
capture-keys w order s eq | G.scopeDone _ | _ | _ = case eq of λ ()
capture-keys w order s eq | G.asyncFailureWritten _ | _ | _ = case eq of λ ()
capture-keys w order s eq | G.asyncDeadTracing _ | _ | _ = case eq of λ ()
request-group-keys : ∀ w s {s′} → G.requestGroup w s ≡ just s′ → Same s s′
request-group-keys w s eq with G.phase (G.frameAt w s) | G.cancelPC (G.frameAt w s) | G.remaining (G.frameAt w s)
... | G.groupClosing | G.ready | j ∷ rest = case just-injective eq of λ { refl → same-refl _ }
request-group-keys w s eq | G.idle | _ | _ = case eq of λ ()
request-group-keys w s eq | G.shutdownSelected | _ | _ = case eq of λ ()
request-group-keys w s eq | G.stoppingTraced | _ | _ = case eq of λ ()
request-group-keys w s eq | G.stoppingWritten | _ | _ = case eq of λ ()
request-group-keys w s eq | G.groupClosing | G.ready | [] = case eq of λ ()
request-group-keys w s eq | G.groupClosing | G.requested _ | _ = case eq of λ ()
request-group-keys w s eq | G.groupClosing | G.delivered _ | _ = case eq of λ ()
request-group-keys w s eq | G.draining | _ | _ = case eq of λ ()
request-group-keys w s eq | G.drainReady | _ | _ = case eq of λ ()
request-group-keys w s eq | G.stoppedTrace | _ | _ = case eq of λ ()
request-group-keys w s eq | G.stoppedTracing | _ | _ = case eq of λ ()
request-group-keys w s eq | G.monitorReturnedNormal | _ | _ = case eq of λ ()
request-group-keys w s eq | G.ownerAborting _ | _ | _ = case eq of λ ()
request-group-keys w s eq | G.wholeClosing _ | _ | _ = case eq of λ ()
request-group-keys w s eq | G.wholeClosed _ | _ | _ = case eq of λ ()
request-group-keys w s eq | G.scopeDone _ | _ | _ = case eq of λ ()
request-group-keys w s eq | G.asyncFailureWritten _ | _ | _ = case eq of λ ()
request-group-keys w s eq | G.asyncDeadTracing _ | _ | _ = case eq of λ ()
deliver-mini-keys : ∀ w s {s′} → G.deliverMini w s ≡ just s′ → Same s s′
deliver-mini-keys w s eq with G.phase (G.frameAt w s) | G.cancelPC (G.frameAt w s) | G.remaining (G.frameAt w s)
... | G.groupClosing | G.requested j | current ∷ rest with j ≟ current | G.miniMember w j s | G.childEligible j s
...   | yes _ | true | true with G.viaPool w (Pool.interruptJob j) s in pooled
...     | nothing = case eq of λ ()
...     | just next = case just-injective eq of λ { refl → pool-keys w (Pool.interruptJob j) s pooled }
deliver-mini-keys w s eq | G.groupClosing | G.requested j | current ∷ rest | yes _ | true | false = case eq of λ ()
deliver-mini-keys w s eq | G.groupClosing | G.requested j | current ∷ rest | yes _ | false | _ = case eq of λ ()
deliver-mini-keys w s eq | G.groupClosing | G.requested j | current ∷ rest | no _ | _ | _ = case eq of λ ()
deliver-mini-keys w s eq | G.idle | _ | _ = case eq of λ ()
deliver-mini-keys w s eq | G.shutdownSelected | _ | _ = case eq of λ ()
deliver-mini-keys w s eq | G.stoppingTraced | _ | _ = case eq of λ ()
deliver-mini-keys w s eq | G.stoppingWritten | _ | _ = case eq of λ ()
deliver-mini-keys w s eq | G.groupClosing | G.ready | _ = case eq of λ ()
deliver-mini-keys w s eq | G.groupClosing | G.requested _ | [] = case eq of λ ()
deliver-mini-keys w s eq | G.groupClosing | G.delivered _ | _ = case eq of λ ()
deliver-mini-keys w s eq | G.draining | _ | _ = case eq of λ ()
deliver-mini-keys w s eq | G.drainReady | _ | _ = case eq of λ ()
deliver-mini-keys w s eq | G.stoppedTrace | _ | _ = case eq of λ ()
deliver-mini-keys w s eq | G.stoppedTracing | _ | _ = case eq of λ ()
deliver-mini-keys w s eq | G.monitorReturnedNormal | _ | _ = case eq of λ ()
deliver-mini-keys w s eq | G.ownerAborting _ | _ | _ = case eq of λ ()
deliver-mini-keys w s eq | G.wholeClosing _ | _ | _ = case eq of λ ()
deliver-mini-keys w s eq | G.wholeClosed _ | _ | _ = case eq of λ ()
deliver-mini-keys w s eq | G.scopeDone _ | _ | _ = case eq of λ ()
deliver-mini-keys w s eq | G.asyncFailureWritten _ | _ | _ = case eq of λ ()
deliver-mini-keys w s eq | G.asyncDeadTracing _ | _ | _ = case eq of λ ()
join-head-keys : ∀ w current s {s′} → G.joinMiniHead w current s ≡ just s′ → Same s s′
join-head-keys w current s eq with G.remaining (G.frameAt w s) | lookup current (Pool.handles (G.poolAt w s))
... | head ∷ rest | just (Pool.resultAvailable exit) with current ≟ head
...   | yes _ = case just-injective eq of λ { refl → same-refl _ }
...   | no _ = case eq of λ ()
join-head-keys w current s eq | [] | _ = case eq of λ ()
join-head-keys w current s eq | _ ∷ _ | nothing = case eq of λ ()
join-head-keys w current s eq | _ ∷ _ | just Pool.bodyRunning = case eq of λ ()
join-head-keys w current s eq | _ ∷ _ | just Pool.bodyUnwinding = case eq of λ ()
join-head-keys w current s eq | _ ∷ _ | just (Pool.bodyReturned _) = case eq of λ ()
join-head-keys w current s eq | _ ∷ _ | just (Pool.deregisterPending _) = case eq of λ ()
join-head-keys w current s eq | _ ∷ _ | just (Pool.deregistered _) = case eq of λ ()
join-mini-keys : ∀ w s {s′} → G.joinMini w s ≡ just s′ → Same s s′
join-mini-keys w s eq with G.phase (G.frameAt w s) | G.cancelPC (G.frameAt w s)
... | G.groupClosing | G.requested j = join-head-keys w j s eq
... | G.groupClosing | G.delivered j = join-head-keys w j s eq
join-mini-keys w s eq | G.idle | _ = case eq of λ ()
join-mini-keys w s eq | G.shutdownSelected | _ = case eq of λ ()
join-mini-keys w s eq | G.stoppingTraced | _ = case eq of λ ()
join-mini-keys w s eq | G.stoppingWritten | _ = case eq of λ ()
join-mini-keys w s eq | G.groupClosing | G.ready = case eq of λ ()
join-mini-keys w s eq | G.draining | _ = case eq of λ ()
join-mini-keys w s eq | G.drainReady | _ = case eq of λ ()
join-mini-keys w s eq | G.stoppedTrace | _ = case eq of λ ()
join-mini-keys w s eq | G.stoppedTracing | _ = case eq of λ ()
join-mini-keys w s eq | G.monitorReturnedNormal | _ = case eq of λ ()
join-mini-keys w s eq | G.ownerAborting _ | _ = case eq of λ ()
join-mini-keys w s eq | G.wholeClosing _ | _ = case eq of λ ()
join-mini-keys w s eq | G.wholeClosed _ | _ = case eq of λ ()
join-mini-keys w s eq | G.scopeDone _ | _ = case eq of λ ()
join-mini-keys w s eq | G.asyncFailureWritten _ | _ = case eq of λ ()
join-mini-keys w s eq | G.asyncDeadTracing _ | _ = case eq of λ ()
finish-mini-keys : ∀ w s {s′} → G.finishMini w s ≡ just s′ → Same s s′
finish-mini-keys w s eq with G.phase (G.frameAt w s) | G.cancelPC (G.frameAt w s) | G.remaining (G.frameAt w s)
... | G.groupClosing | G.ready | [] = case just-injective eq of λ { refl → same-refl _ }
finish-mini-keys w s eq | G.idle | _ | _ = case eq of λ ()
finish-mini-keys w s eq | G.shutdownSelected | _ | _ = case eq of λ ()
finish-mini-keys w s eq | G.stoppingTraced | _ | _ = case eq of λ ()
finish-mini-keys w s eq | G.stoppingWritten | _ | _ = case eq of λ ()
finish-mini-keys w s eq | G.groupClosing | G.ready | _ ∷ _ = case eq of λ ()
finish-mini-keys w s eq | G.groupClosing | G.requested _ | _ = case eq of λ ()
finish-mini-keys w s eq | G.groupClosing | G.delivered _ | _ = case eq of λ ()
finish-mini-keys w s eq | G.draining | _ | _ = case eq of λ ()
finish-mini-keys w s eq | G.drainReady | _ | _ = case eq of λ ()
finish-mini-keys w s eq | G.stoppedTrace | _ | _ = case eq of λ ()
finish-mini-keys w s eq | G.stoppedTracing | _ | _ = case eq of λ ()
finish-mini-keys w s eq | G.monitorReturnedNormal | _ | _ = case eq of λ ()
finish-mini-keys w s eq | G.ownerAborting _ | _ | _ = case eq of λ ()
finish-mini-keys w s eq | G.wholeClosing _ | _ | _ = case eq of λ ()
finish-mini-keys w s eq | G.wholeClosed _ | _ | _ = case eq of λ ()
finish-mini-keys w s eq | G.scopeDone _ | _ | _ = case eq of λ ()
finish-mini-keys w s eq | G.asyncFailureWritten _ | _ | _ = case eq of λ ()
finish-mini-keys w s eq | G.asyncDeadTracing _ | _ | _ = case eq of λ ()
discard-keys : ∀ j job s {s′} → G.discardClean j job s ≡ just s′ → Same s s′
discard-keys j job s eq with Types.direction job
... | Mux.initiatorJob = case just-injective eq of λ { refl → same-refl _ }
... | Mux.responderJob with P.locate j (P.pendingAt (Types.owner job) (G.protocolState s)) | P.muxAt (Types.mux job) (G.protocolState s)
...   | just (index , kept) | just m with IG.takePending index (Mux.finishedJobs m)
...     | just ((n , result) , rest) with does (n Nat.≟ Types.protocolNumber job) ∧ P.sameOutcome clean result
...       | true with G.viaSource (IG.discardJobOccurrence (Types.mux job) index) s in via
...         | nothing = case eq of λ ()
...         | just next = case just-injective eq of λ { refl → via-keys (IG.discardJobOccurrence (Types.mux job) index) s via }
discard-keys j job s eq | Mux.responderJob | just (index , kept) | just m | just ((n , result) , rest) | false = case eq of λ ()
discard-keys j job s eq | Mux.responderJob | just (index , kept) | just m | nothing = case eq of λ ()
discard-keys j job s eq | Mux.responderJob | just _ | nothing = case eq of λ ()
discard-keys j job s eq | Mux.responderJob | nothing | _ = case eq of λ ()
prepare-keys : ∀ j w f s {s′} → G.prepareUnwind j w f s ≡ just s′ → Same s s′
prepare-keys j w f s eq with lookup j (P.jobs (G.protocolState s))
... | nothing with G.isInfra j f
...   | true = case just-injective eq of λ { refl → same-refl _ }
...   | false = case eq of λ ()
prepare-keys j w f s eq | just job with does (w ≟ Types.owner job) | Types.phase job
...   | true | Types.executing = case just-injective eq of λ { refl → same-refl _ }
...   | true | Types.waitingEgress = case just-injective eq of λ { refl → same-refl _ }
...   | true | Types.resultCaptured clean = discard-keys j job s eq
prepare-keys j w f s eq | just job | true | Types.resultCaptured (errored _) = case eq of λ ()
prepare-keys j w f s eq | just job | false | _ = case eq of λ ()
unwind-keys : ∀ j s {s′} → G.unwindChild j s ≡ just s′ → Same s s′
unwind-keys j s eq with G.ownerOf j s
... | nothing = case eq of λ ()
... | just (w , f) with lookup j (Pool.handles (G.poolAt w s))
...   | just Pool.bodyUnwinding with G.prepareUnwind j w f s in prepared
...     | nothing = case eq of λ ()
...     | just next with Pool.step (Pool.bodyUnwound j) (G.poolAt w next)
...       | nothing = case eq of λ ()
...       | just p = case just-injective eq of λ { refl → prepare-keys j w f s prepared }
unwind-keys j s eq | just (w , f) | nothing = case eq of λ ()
unwind-keys j s eq | just (w , f) | just Pool.bodyRunning = case eq of λ ()
unwind-keys j s eq | just (w , f) | just (Pool.bodyReturned _) = case eq of λ ()
unwind-keys j s eq | just (w , f) | just (Pool.deregisterPending _) = case eq of λ ()
unwind-keys j s eq | just (w , f) | just (Pool.deregistered _) = case eq of λ ()
unwind-keys j s eq | just (w , f) | just (Pool.resultAvailable _) = case eq of λ ()
replace-keys : ∀ j err s {s′} → G.replaceUnwind j err s ≡ just s′ → Same s s′
replace-keys j err s eq with lookup j (P.jobs (G.protocolState s))
... | nothing = case eq of λ ()
... | just job with G.replacementEligible (Types.phase job) | G.ownerOf j s
...   | true | just (w , f) with does (w ≟ Types.owner job) | Pool.step (Pool.resumeAfterUnwindError j) (G.poolAt w s)
...     | true | just p with P.step (P.protocolException j err) (G.protocolState (G.setPool w f p s)) in stepped
...       | nothing = case eq of λ ()
...       | just next = case just-injective eq of λ { refl →
  ProtocolKeys.step-keysP (P.protocolException j err) (G.protocolState (G.setPool w f p s)) stepped }
replace-keys j err s eq | just job | true | just (w , f) | true | nothing = case eq of λ ()
replace-keys j err s eq | just job | true | just (w , f) | false | _ = case eq of λ ()
replace-keys j err s eq | just job | true | nothing = case eq of λ ()
replace-keys j err s eq | just job | false | _ = case eq of λ ()
abort-keys : ∀ w err s {s′} → G.abortMonitor w err s ≡ just s′ → Same s s′
abort-keys w err s eq with G.abortStage w s | G.ownerContext w s | P.noParent (G.poolAt w s)
... | true | just (f , mid) | true with P.muxAt mid (G.protocolState s)
...   | just m with Mux.callback m
...     | Mux.returned = case just-injective eq of λ { refl → same-refl _ }
abort-keys w err s eq | true | just (f , mid) | true | just m | Mux.readActive _ = case eq of λ ()
abort-keys w err s eq | true | just (f , mid) | true | just m | Mux.commitTrace _ _ = case eq of λ ()
abort-keys w err s eq | true | just (f , mid) | true | just m | Mux.afterStart _ = case eq of λ ()
abort-keys w err s eq | true | just (f , mid) | true | just m | Mux.forkPending _ = case eq of λ ()
abort-keys w err s eq | true | just (f , mid) | true | just m | Mux.afterFailure = case eq of λ ()
abort-keys w err s eq | true | just (f , mid) | true | just m | Mux.tracerFailed _ = case eq of λ ()
abort-keys w err s eq | true | just (f , mid) | true | nothing = case eq of λ ()
abort-keys w err s eq | true | nothing | _ = case eq of λ ()
abort-keys w err s eq | true | just _ | false = case eq of λ ()
abort-keys w err s eq | false | _ | _ = case eq of λ ()
begin-whole-keys : ∀ w order s {s′} → G.beginWhole w order s ≡ just s′ → Same s s′
begin-whole-keys w order s eq with G.wholeOutcome w s
... | nothing = case eq of λ ()
... | just outcome with G.viaPool w (Pool.beginClose order) s in pooled
...   | nothing = case eq of λ ()
...   | just next = case just-injective eq of λ { refl → pool-keys w (Pool.beginClose order) s pooled }
whole-action-keys : ∀ w act s {s′} → G.wholeAction w act s ≡ just s′ → Same s s′
whole-action-keys w act s eq with G.phase (G.frameAt w s)
... | G.wholeClosing outcome = pool-keys w act s eq
whole-action-keys w act s eq | G.idle = case eq of λ ()
whole-action-keys w act s eq | G.shutdownSelected = case eq of λ ()
whole-action-keys w act s eq | G.stoppingTraced = case eq of λ ()
whole-action-keys w act s eq | G.stoppingWritten = case eq of λ ()
whole-action-keys w act s eq | G.groupClosing = case eq of λ ()
whole-action-keys w act s eq | G.draining = case eq of λ ()
whole-action-keys w act s eq | G.drainReady = case eq of λ ()
whole-action-keys w act s eq | G.stoppedTrace = case eq of λ ()
whole-action-keys w act s eq | G.stoppedTracing = case eq of λ ()
whole-action-keys w act s eq | G.monitorReturnedNormal = case eq of λ ()
whole-action-keys w act s eq | G.ownerAborting _ = case eq of λ ()
whole-action-keys w act s eq | G.wholeClosed _ = case eq of λ ()
whole-action-keys w act s eq | G.scopeDone _ = case eq of λ ()
whole-action-keys w act s eq | G.asyncFailureWritten _ = case eq of λ ()
whole-action-keys w act s eq | G.asyncDeadTracing _ = case eq of λ ()
deliver-whole-keys : ∀ w s {s′} → G.deliverWholeChild w s ≡ just s′ → Same s s′
deliver-whole-keys w s eq with G.phase (G.frameAt w s) | G.ownerContext w s | Pool.phase (G.poolAt w s)
... | G.wholeClosing outcome | just (f , mid) | Pool.cancelPending j with G.wholeDeliverable w j f s
...   | true = pool-keys w Pool.deliverCancel s eq
...   | false = case eq of λ ()
deliver-whole-keys w s eq | G.idle | _ | _ = case eq of λ ()
deliver-whole-keys w s eq | G.shutdownSelected | _ | _ = case eq of λ ()
deliver-whole-keys w s eq | G.stoppingTraced | _ | _ = case eq of λ ()
deliver-whole-keys w s eq | G.stoppingWritten | _ | _ = case eq of λ ()
deliver-whole-keys w s eq | G.groupClosing | _ | _ = case eq of λ ()
deliver-whole-keys w s eq | G.draining | _ | _ = case eq of λ ()
deliver-whole-keys w s eq | G.drainReady | _ | _ = case eq of λ ()
deliver-whole-keys w s eq | G.stoppedTrace | _ | _ = case eq of λ ()
deliver-whole-keys w s eq | G.stoppedTracing | _ | _ = case eq of λ ()
deliver-whole-keys w s eq | G.monitorReturnedNormal | _ | _ = case eq of λ ()
deliver-whole-keys w s eq | G.ownerAborting _ | _ | _ = case eq of λ ()
deliver-whole-keys w s eq | G.wholeClosing _ | nothing | _ = case eq of λ ()
deliver-whole-keys w s eq | G.wholeClosing _ | just _ | Pool.openPool = case eq of λ ()
deliver-whole-keys w s eq | G.wholeClosing _ | just _ | Pool.closing = case eq of λ ()
deliver-whole-keys w s eq | G.wholeClosing _ | just _ | Pool.closedPool = case eq of λ ()
deliver-whole-keys w s eq | G.wholeClosing _ | just _ | Pool.joinPending _ = case eq of λ ()
deliver-whole-keys w s eq | G.wholeClosed _ | _ | _ = case eq of λ ()
deliver-whole-keys w s eq | G.scopeDone _ | _ | _ = case eq of λ ()
deliver-whole-keys w s eq | G.asyncFailureWritten _ | _ | _ = case eq of λ ()
deliver-whole-keys w s eq | G.asyncDeadTracing _ | _ | _ = case eq of λ ()
finish-whole-keys : ∀ w s {s′} → G.finishWhole w s ≡ just s′ → Same s s′
finish-whole-keys w s eq with G.phase (G.frameAt w s)
... | G.wholeClosing outcome with G.viaPool w Pool.finishClose s in pooled
...   | nothing = case eq of λ ()
...   | just next = case just-injective eq of λ { refl → pool-keys w Pool.finishClose s pooled }
finish-whole-keys w s eq | G.idle = case eq of λ ()
finish-whole-keys w s eq | G.shutdownSelected = case eq of λ ()
finish-whole-keys w s eq | G.stoppingTraced = case eq of λ ()
finish-whole-keys w s eq | G.stoppingWritten = case eq of λ ()
finish-whole-keys w s eq | G.groupClosing = case eq of λ ()
finish-whole-keys w s eq | G.draining = case eq of λ ()
finish-whole-keys w s eq | G.drainReady = case eq of λ ()
finish-whole-keys w s eq | G.stoppedTrace = case eq of λ ()
finish-whole-keys w s eq | G.stoppedTracing = case eq of λ ()
finish-whole-keys w s eq | G.monitorReturnedNormal = case eq of λ ()
finish-whole-keys w s eq | G.ownerAborting _ = case eq of λ ()
finish-whole-keys w s eq | G.wholeClosed _ = case eq of λ ()
finish-whole-keys w s eq | G.scopeDone _ = case eq of λ ()
finish-whole-keys w s eq | G.asyncFailureWritten _ = case eq of λ ()
finish-whole-keys w s eq | G.asyncDeadTracing _ = case eq of λ ()
finish-stopped-keys : ∀ w s {s′} → G.finishStopped w s ≡ just s′ → Same s s′
finish-stopped-keys w s eq with G.sameStage G.stoppedTracing (G.phase (G.frameAt w s)) | G.ownerContext w s
... | true | just (f , mid) with P.muxAt mid (G.protocolState s)
...   | just m with Mux.status m | Mux.callback m
...     | Mux.stopped | Mux.returned = case just-injective eq of λ { refl → same-refl _ }
finish-stopped-keys w s eq | true | just (f , mid) | just m | Mux.ready | _ = case eq of λ ()
finish-stopped-keys w s eq | true | just (f , mid) | just m | Mux.stopping | _ = case eq of λ ()
finish-stopped-keys w s eq | true | just (f , mid) | just m | Mux.stopped | Mux.readActive _ = case eq of λ ()
finish-stopped-keys w s eq | true | just (f , mid) | just m | Mux.stopped | Mux.commitTrace _ _ = case eq of λ ()
finish-stopped-keys w s eq | true | just (f , mid) | just m | Mux.stopped | Mux.afterStart _ = case eq of λ ()
finish-stopped-keys w s eq | true | just (f , mid) | just m | Mux.stopped | Mux.forkPending _ = case eq of λ ()
finish-stopped-keys w s eq | true | just (f , mid) | just m | Mux.stopped | Mux.afterFailure = case eq of λ ()
finish-stopped-keys w s eq | true | just (f , mid) | just m | Mux.stopped | Mux.tracerFailed _ = case eq of λ ()
finish-stopped-keys w s eq | true | just (f , mid) | just m | Mux.failed _ | _ = case eq of λ ()
finish-stopped-keys w s eq | true | just (f , mid) | nothing = case eq of λ ()
finish-stopped-keys w s eq | true | nothing = case eq of λ ()
finish-stopped-keys w s eq | false | _ = case eq of λ ()
async-failure-keys : ∀ w s {s′} → G.asyncFailure w s ≡ just s′ → Same s s′
async-failure-keys w s eq with G.phase (G.frameAt w s) | Pool.phase (G.poolAt w s) | G.ownerContext w s
... | G.wholeClosed (G.asyncExit err) | Pool.closedPool | just (f , mid) with G.viaSource (IG.recordAsyncMuxFailure mid err) s in via
...   | nothing = case eq of λ ()
...   | just next = case just-injective eq of λ { refl → via-keys (IG.recordAsyncMuxFailure mid err) s via }
async-failure-keys w s eq | G.idle | _ | _ = case eq of λ ()
async-failure-keys w s eq | G.shutdownSelected | _ | _ = case eq of λ ()
async-failure-keys w s eq | G.stoppingTraced | _ | _ = case eq of λ ()
async-failure-keys w s eq | G.stoppingWritten | _ | _ = case eq of λ ()
async-failure-keys w s eq | G.groupClosing | _ | _ = case eq of λ ()
async-failure-keys w s eq | G.draining | _ | _ = case eq of λ ()
async-failure-keys w s eq | G.drainReady | _ | _ = case eq of λ ()
async-failure-keys w s eq | G.stoppedTrace | _ | _ = case eq of λ ()
async-failure-keys w s eq | G.stoppedTracing | _ | _ = case eq of λ ()
async-failure-keys w s eq | G.monitorReturnedNormal | _ | _ = case eq of λ ()
async-failure-keys w s eq | G.ownerAborting _ | _ | _ = case eq of λ ()
async-failure-keys w s eq | G.wholeClosing _ | _ | _ = case eq of λ ()
async-failure-keys w s eq | G.wholeClosed G.normalExit | _ | _ = case eq of λ ()
async-failure-keys w s eq | G.wholeClosed (G.failedExit _) | _ | _ = case eq of λ ()
async-failure-keys w s eq | G.wholeClosed (G.asyncExit _) | Pool.openPool | _ = case eq of λ ()
async-failure-keys w s eq | G.wholeClosed (G.asyncExit _) | Pool.closing | _ = case eq of λ ()
async-failure-keys w s eq | G.wholeClosed (G.asyncExit _) | Pool.closedPool | nothing = case eq of λ ()
async-failure-keys w s eq | G.wholeClosed (G.asyncExit _) | Pool.cancelPending _ | _ = case eq of λ ()
async-failure-keys w s eq | G.wholeClosed (G.asyncExit _) | Pool.joinPending _ | _ = case eq of λ ()
async-failure-keys w s eq | G.scopeDone _ | _ | _ = case eq of λ ()
async-failure-keys w s eq | G.asyncFailureWritten _ | _ | _ = case eq of λ ()
async-failure-keys w s eq | G.asyncDeadTracing _ | _ | _ = case eq of λ ()
async-dead-keys : ∀ w s {s′} → G.asyncDead w s ≡ just s′ → Same s s′
async-dead-keys w s eq with G.phase (G.frameAt w s) | G.ownerContext w s
... | G.asyncFailureWritten err | just (f , mid) with G.viaSource (IG.traceMuxDead mid) s in via
...   | nothing = case eq of λ ()
...   | just next = case just-injective eq of λ { refl → via-keys (IG.traceMuxDead mid) s via }
async-dead-keys w s eq | G.idle | _ = case eq of λ ()
async-dead-keys w s eq | G.shutdownSelected | _ = case eq of λ ()
async-dead-keys w s eq | G.stoppingTraced | _ = case eq of λ ()
async-dead-keys w s eq | G.stoppingWritten | _ = case eq of λ ()
async-dead-keys w s eq | G.groupClosing | _ = case eq of λ ()
async-dead-keys w s eq | G.draining | _ = case eq of λ ()
async-dead-keys w s eq | G.drainReady | _ = case eq of λ ()
async-dead-keys w s eq | G.stoppedTrace | _ = case eq of λ ()
async-dead-keys w s eq | G.stoppedTracing | _ = case eq of λ ()
async-dead-keys w s eq | G.monitorReturnedNormal | _ = case eq of λ ()
async-dead-keys w s eq | G.ownerAborting _ | _ = case eq of λ ()
async-dead-keys w s eq | G.wholeClosing _ | _ = case eq of λ ()
async-dead-keys w s eq | G.wholeClosed _ | _ = case eq of λ ()
async-dead-keys w s eq | G.scopeDone _ | _ = case eq of λ ()
async-dead-keys w s eq | G.asyncFailureWritten _ | nothing = case eq of λ ()
async-dead-keys w s eq | G.asyncDeadTracing _ | _ = case eq of λ ()
async-trace-keys : ∀ sample w s {s′} → G.asyncTrace sample w s ≡ just s′ → Same s s′
async-trace-keys sample w s eq with G.phase (G.frameAt w s) | G.ownerContext w s
... | G.asyncDeadTracing err | just (f , mid) with sample
...   | true = via-keys (IG.sampleTracer mid) s eq
...   | false = via-keys (IG.commitTracer mid) s eq
async-trace-keys sample w s eq | G.idle | _ = case eq of λ ()
async-trace-keys sample w s eq | G.shutdownSelected | _ = case eq of λ ()
async-trace-keys sample w s eq | G.stoppingTraced | _ = case eq of λ ()
async-trace-keys sample w s eq | G.stoppingWritten | _ = case eq of λ ()
async-trace-keys sample w s eq | G.groupClosing | _ = case eq of λ ()
async-trace-keys sample w s eq | G.draining | _ = case eq of λ ()
async-trace-keys sample w s eq | G.drainReady | _ = case eq of λ ()
async-trace-keys sample w s eq | G.stoppedTrace | _ = case eq of λ ()
async-trace-keys sample w s eq | G.stoppedTracing | _ = case eq of λ ()
async-trace-keys sample w s eq | G.monitorReturnedNormal | _ = case eq of λ ()
async-trace-keys sample w s eq | G.ownerAborting _ | _ = case eq of λ ()
async-trace-keys sample w s eq | G.wholeClosing _ | _ = case eq of λ ()
async-trace-keys sample w s eq | G.wholeClosed _ | _ = case eq of λ ()
async-trace-keys sample w s eq | G.scopeDone _ | _ = case eq of λ ()
async-trace-keys sample w s eq | G.asyncFailureWritten _ | _ = case eq of λ ()
async-trace-keys sample w s eq | G.asyncDeadTracing _ | nothing = case eq of λ ()
finish-async-keys : ∀ w s {s′} → G.finishAsync w s ≡ just s′ → Same s s′
finish-async-keys w s eq with G.phase (G.frameAt w s) | G.ownerContext w s | Pool.phase (G.poolAt w s)
... | G.asyncDeadTracing err | just (f , mid) | Pool.closedPool with P.muxAt mid (G.protocolState s)
...   | just m with Mux.callback m | M.finishMatches (M.failed err) (Mux.status m)
...     | Mux.returned | true = case just-injective eq of λ { refl → same-refl _ }
finish-async-keys w s eq | G.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | Mux.readActive _ | _ = case eq of λ ()
finish-async-keys w s eq | G.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | Mux.commitTrace _ _ | _ = case eq of λ ()
finish-async-keys w s eq | G.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | Mux.afterStart _ | _ = case eq of λ ()
finish-async-keys w s eq | G.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | Mux.forkPending _ | _ = case eq of λ ()
finish-async-keys w s eq | G.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | Mux.afterFailure | _ = case eq of λ ()
finish-async-keys w s eq | G.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | Mux.tracerFailed _ | _ = case eq of λ ()
finish-async-keys w s eq | G.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | Mux.returned | false = case eq of λ ()
finish-async-keys w s eq | G.asyncDeadTracing err | just (f , mid) | Pool.closedPool | nothing = case eq of λ ()
finish-async-keys w s eq | G.idle | _ | _ = case eq of λ ()
finish-async-keys w s eq | G.shutdownSelected | _ | _ = case eq of λ ()
finish-async-keys w s eq | G.stoppingTraced | _ | _ = case eq of λ ()
finish-async-keys w s eq | G.stoppingWritten | _ | _ = case eq of λ ()
finish-async-keys w s eq | G.groupClosing | _ | _ = case eq of λ ()
finish-async-keys w s eq | G.draining | _ | _ = case eq of λ ()
finish-async-keys w s eq | G.drainReady | _ | _ = case eq of λ ()
finish-async-keys w s eq | G.stoppedTrace | _ | _ = case eq of λ ()
finish-async-keys w s eq | G.stoppedTracing | _ | _ = case eq of λ ()
finish-async-keys w s eq | G.monitorReturnedNormal | _ | _ = case eq of λ ()
finish-async-keys w s eq | G.ownerAborting _ | _ | _ = case eq of λ ()
finish-async-keys w s eq | G.wholeClosing _ | _ | _ = case eq of λ ()
finish-async-keys w s eq | G.wholeClosed _ | _ | _ = case eq of λ ()
finish-async-keys w s eq | G.scopeDone _ | _ | _ = case eq of λ ()
finish-async-keys w s eq | G.asyncFailureWritten _ | _ | _ = case eq of λ ()
finish-async-keys w s eq | G.asyncDeadTracing _ | nothing | _ = case eq of λ ()
finish-async-keys w s eq | G.asyncDeadTracing _ | just _ | Pool.openPool = case eq of λ ()
finish-async-keys w s eq | G.asyncDeadTracing _ | just _ | Pool.closing = case eq of λ ()
finish-async-keys w s eq | G.asyncDeadTracing _ | just _ | Pool.cancelPending _ = case eq of λ ()
finish-async-keys w s eq | G.asyncDeadTracing _ | just _ | Pool.joinPending _ = case eq of λ ()
finish-ordinary-keys : ∀ w s {s′} → G.finishOrdinary w s ≡ just s′ → Same s s′
finish-ordinary-keys w s eq with G.phase (G.frameAt w s) | Pool.phase (G.poolAt w s)
... | G.wholeClosed G.normalExit | Pool.closedPool = case just-injective eq of λ { refl → same-refl _ }
... | G.wholeClosed (G.failedExit err) | Pool.closedPool = case just-injective eq of λ { refl → same-refl _ }
finish-ordinary-keys w s eq | G.idle | _ = case eq of λ ()
finish-ordinary-keys w s eq | G.shutdownSelected | _ = case eq of λ ()
finish-ordinary-keys w s eq | G.stoppingTraced | _ = case eq of λ ()
finish-ordinary-keys w s eq | G.stoppingWritten | _ = case eq of λ ()
finish-ordinary-keys w s eq | G.groupClosing | _ = case eq of λ ()
finish-ordinary-keys w s eq | G.draining | _ = case eq of λ ()
finish-ordinary-keys w s eq | G.drainReady | _ = case eq of λ ()
finish-ordinary-keys w s eq | G.stoppedTrace | _ = case eq of λ ()
finish-ordinary-keys w s eq | G.stoppedTracing | _ = case eq of λ ()
finish-ordinary-keys w s eq | G.monitorReturnedNormal | _ = case eq of λ ()
finish-ordinary-keys w s eq | G.ownerAborting _ | _ = case eq of λ ()
finish-ordinary-keys w s eq | G.wholeClosing _ | _ = case eq of λ ()
finish-ordinary-keys w s eq | G.wholeClosed G.normalExit | Pool.openPool = case eq of λ ()
finish-ordinary-keys w s eq | G.wholeClosed G.normalExit | Pool.closing = case eq of λ ()
finish-ordinary-keys w s eq | G.wholeClosed G.normalExit | Pool.cancelPending _ = case eq of λ ()
finish-ordinary-keys w s eq | G.wholeClosed G.normalExit | Pool.joinPending _ = case eq of λ ()
finish-ordinary-keys w s eq | G.wholeClosed (G.failedExit _) | Pool.openPool = case eq of λ ()
finish-ordinary-keys w s eq | G.wholeClosed (G.failedExit _) | Pool.closing = case eq of λ ()
finish-ordinary-keys w s eq | G.wholeClosed (G.failedExit _) | Pool.cancelPending _ = case eq of λ ()
finish-ordinary-keys w s eq | G.wholeClosed (G.failedExit _) | Pool.joinPending _ = case eq of λ ()
finish-ordinary-keys w s eq | G.wholeClosed (G.asyncExit _) | _ = case eq of λ ()
finish-ordinary-keys w s eq | G.scopeDone _ | _ = case eq of λ ()
finish-ordinary-keys w s eq | G.asyncFailureWritten _ | _ = case eq of λ ()
finish-ordinary-keys w s eq | G.asyncDeadTracing _ | _ = case eq of λ ()

step-keysG : ∀ a s {s′} → G.step a s ≡ just s′ → Effect (rootG a) (G.source s) (G.source s′)
step-keysG (G.run a) s eq = inherit-keys a s eq
step-keysG (G.requestShutdown w) s eq = request-stop-keys w s eq
step-keysG (G.retireCounters w) s eq = retire-keys w s eq
step-keysG (G.selectShutdown w) s eq = select-stop-keys w s eq
step-keysG (G.observeStoppingTrace w) s eq = from-keys w G.shutdownSelected G.stoppingTraced s eq
step-keysG (G.writeStopping w) s eq = source-phase-keys w G.stoppingTraced G.stoppingWritten IG.recordMuxStopping s eq
step-keysG (G.captureGroup w order) s eq = capture-keys w order s eq
step-keysG (G.requestGroupCancel w) s eq = request-group-keys w s eq
step-keysG (G.deliverGroup w) s eq = deliver-mini-keys w s eq
step-keysG (G.joinGroup w) s eq = join-mini-keys w s eq
step-keysG (G.finishGroup w) s eq = finish-mini-keys w s eq
step-keysG (G.drainEmpty w) s eq = drain-keys w s eq
step-keysG (G.timeout2Elapsed w) s eq = from-keys w G.draining G.drainReady s eq
step-keysG (G.writeStopped w) s eq = source-phase-keys w G.drainReady G.stoppedTrace IG.completeMuxStopping s eq
step-keysG (G.observeTraceStopped w) s eq = source-phase-keys w G.stoppedTrace G.stoppedTracing IG.traceGracefulMuxStopped s eq
step-keysG (G.sampleStoppedTracer w) s eq = source-phase-keys w G.stoppedTracing G.stoppedTracing IG.sampleTracer s eq
step-keysG (G.commitStoppedTracer w) s eq = source-phase-keys w G.stoppedTracing G.stoppedTracing IG.commitTracer s eq
step-keysG (G.finishStoppedTrace w) s eq = finish-stopped-keys w s eq
step-keysG (G.finishChildUnwind j) s eq = unwind-keys j s eq
step-keysG (G.unwindReplacedBySync j err) s eq = replace-keys j err s eq
step-keysG (G.abortOwner w err) s eq = abort-keys w err s eq
step-keysG (G.beginWholeClose w order) s eq = begin-whole-keys w order s eq
step-keysG (G.requestWholeCancel w) s eq = whole-action-keys w Pool.requestCancel s eq
step-keysG (G.deliverWhole w) s eq = deliver-whole-keys w s eq
step-keysG (G.joinWhole w) s eq = whole-action-keys w Pool.join s eq
step-keysG (G.finishWholeClose w) s eq = finish-whole-keys w s eq
step-keysG (G.finishNormalScope w) s eq = finish-ordinary-keys w s eq
step-keysG (G.writeAsyncFailure w) s eq = async-failure-keys w s eq
step-keysG (G.beginAsyncDead w) s eq = async-dead-keys w s eq
step-keysG (G.sampleAsyncTracer w) s eq = async-trace-keys true w s eq
step-keysG (G.commitAsyncTracer w) s eq = async-trace-keys false w s eq
step-keysG (G.finishAsyncDead w) s eq = finish-async-keys w s eq
