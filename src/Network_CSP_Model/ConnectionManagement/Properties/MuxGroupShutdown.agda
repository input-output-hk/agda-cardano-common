{-# OPTIONS --guardedness #-}

-- Source and physical-pool histories for MiniProtocol group cancellation and
-- whole-pool unwind. A completed scope is not a parent Async result or buffer IO.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.MuxGroupShutdown (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no; does)
open import Class.DecEq using (_≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import ConnectionManagement.Domain hiding (job; worker)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)
import ConnectionManagement.MuxGroupShutdown as Group
module W = Group isBearerClosed
open W using (remaining; joined; cancelPC)
import ConnectionManagement.Properties.MuxResultMonitor as MonitorFacts
module Base = MonitorFacts isBearerClosed
import ConnectionManagement.Properties.MuxProtocolJobs as ProtocolFacts
import ConnectionManagement.Rules.MuxJobTypes as Types
import Data.Nat
import ConnectionManagement.IGTypes
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as Machine
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Properties.JobPoolCloseKernel as CloseFacts
module Pool = W.Pool
module Close = CloseFacts Types.TypedResult true
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply

record Paths (before after : W.State) : Set where
  constructor paths
  field machine : ProtocolFacts.OTrace (W.source before) (W.source after)
        pools : ∀ selected → ProtocolFacts.PTrace (W.poolAt selected before) (W.poolAt selected after)
open Paths public
from-base : ∀ before after → Base.Paths (W.base before) (W.base after) → Paths before after
from-base before after path = paths (Base.machine path) (Base.pools path)
idle : ∀ s → Paths s s
idle s = from-base s s (Base.idle (W.base s))
compose : ∀ {p q r} → Paths p q → Paths q r → Paths p r
compose (paths (as , op) first) (paths (bs , oq) second) = paths
  (as ++ bs , O.append op oq) (λ selected → let left = first selected; right = second selected in
    proj₁ left ++ proj₁ right , ProtocolFacts.append-pools (proj₂ left) (proj₂ right))
module Monitor = W.M
module P = W.P
module U = W.U

frame-paths : ∀ w f s → Paths s (W.setFrame w f s)
frame-paths w f s = from-base s _ (Base.idle (W.base s))
phase-paths : ∀ w pc s → Paths s (W.setPhase w pc s)
phase-paths w pc s = frame-paths w _ s
phase-after : ∀ w pc {before after} → Paths before after → Paths before (W.setPhase w pc after)
phase-after w pc {after = after} path = compose path (phase-paths w pc after)
frame-after : ∀ w f {before after} → Paths before after → Paths before (W.setFrame w f after)
frame-after w f {after = after} path = compose path (frame-paths w f after)
from-protocol : ∀ before after → ProtocolFacts.Paths (W.protocolState before) (W.protocolState after) → Paths before after
from-protocol before after path = from-base before after (Base.from-base (W.base before) (W.base after) path)
protocol-projects : ∀ s p → ProtocolFacts.Paths (W.protocolState s) p → Paths s (W.setProtocols p s)
protocol-projects s p path = from-protocol s _ path
source-step : ∀ action s {c} → O.advance (O.inbound (Machine.igStep action)) (W.source s) ≡ just c → Paths s (W.setSource c s)
source-step action s eq = from-base s _ (Base.source-step action (W.base s) eq)
via-source-projects : ∀ action s {s′} → W.viaSource action s ≡ just s′ → Paths s s′
via-source-projects action s eq with O.advance (O.inbound (Machine.igStep action)) (W.source s) in advanced
... | nothing = case eq of λ ()
... | just c = case just-injective eq of λ { refl → source-step action s advanced }
pool-step : ∀ w f action s {p} → Pool.step action (W.poolAt w s) ≡ just p → Paths s (W.setPool w f p s)
pool-step w f action s eq = from-protocol s _ (ProtocolFacts.pool-step w f action (W.protocolState s) eq)
via-pool-projects : ∀ w action s {s′} → W.viaPool w action s ≡ just s′ → Paths s s′
via-pool-projects w action s eq with W.ownerContext w s
... | nothing = case eq of λ ()
... | just (f , mid) with Pool.step action (W.poolAt w s) in advanced
...   | nothing = case eq of λ ()
...   | just p = case just-injective eq of λ { refl → pool-step w f action s advanced }
inherit-projects : ∀ action s {s′} → W.inherit action s ≡ just s′ → Paths s s′
inherit-projects action s eq with W.delegateAllowed action s
... | false = case eq of λ ()
... | true with Monitor.step action (W.base s) in advanced
...   | nothing = case eq of λ ()
...   | just next = case just-injective eq of λ { refl → from-base s _ (Base.step-projects action (W.base s) advanced) }
from-phase-projects : ∀ w before after s {s′} → W.fromPhase w before after s ≡ just s′ → Paths s s′
from-phase-projects w before after s eq with W.sameStage before (W.phase (W.frameAt w s))
... | false = case eq of λ ()
... | true = case just-injective eq of λ { refl → phase-paths w after s }
source-phase-projects : ∀ w before after action s {s′} → W.sourcePhase w before after action s ≡ just s′ → Paths s s′
source-phase-projects w before after action s eq with W.sameStage before (W.phase (W.frameAt w s)) | W.ownerContext w s
... | true | just (f , mid) with W.viaSource (action mid) s in advanced
...   | nothing = case eq of λ ()
...   | just next = case just-injective eq of λ { refl → phase-after w after (via-source-projects (action mid) s advanced) }
source-phase-projects w before after action s eq | false | _ = case eq of λ ()
source-phase-projects w before after action s eq | true | nothing = case eq of λ ()
request-projects : ∀ w s {s′} → W.requestStop w s ≡ just s′ → Paths s s′
request-projects w s eq with lookup w (U.frames (P.base (W.protocolState s)))
... | nothing = case eq of λ ()
... | just f with U.progress f
...   | U.promisePublished hid mid = via-source-projects (IG.enqueueMuxStop mid) s eq
...   | U.returnedSuccess = case eq of λ ()
...   | U.handleAllocated hid mid = case eq of λ ()
select-projects : ∀ w s {s′} → W.selectStop w s ≡ just s′ → Paths s s′
select-projects w s eq with W.phase (W.frameAt w s) | Monitor.pcAt w (W.base s) | W.ownerContext w s
... | W.idle | Monitor.waiting | just (f , mid) with P.noParent (W.poolAt w s) | P.noResults (W.poolAt w s)
...   | true | true with W.viaSource (IG.takeShutdownCommand mid) s in advanced
...     | nothing = case eq of λ ()
...     | just next = case just-injective eq of λ { refl → phase-after w W.shutdownSelected (via-source-projects (IG.takeShutdownCommand mid) s advanced) }
select-projects w s eq | W.idle | Monitor.waiting | just (f , mid) | false | _ = case eq of λ ()
select-projects w s eq | W.idle | Monitor.waiting | just (f , mid) | true | false = case eq of λ ()
select-projects w s eq | W.idle | Monitor.waiting | nothing = case eq of λ ()
select-projects w s eq | W.idle | Monitor.selected item | _ = case eq of λ ()
select-projects w s eq | W.idle | Monitor.responderTracing result | _ = case eq of λ ()
select-projects w s eq | W.idle | Monitor.initiatorTracing result | _ = case eq of λ ()
select-projects w s eq | W.idle | Monitor.deadReady outcome | _ = case eq of λ ()
select-projects w s eq | W.idle | Monitor.deadTracing outcome | _ = case eq of λ ()
select-projects w s eq | W.idle | Monitor.finished outcome | _ = case eq of λ ()
select-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
select-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
select-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
select-projects w s eq | W.groupClosing | _ | _ = case eq of λ ()
select-projects w s eq | W.draining | _ | _ = case eq of λ ()
select-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
select-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
select-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
select-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
select-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
select-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
select-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
select-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
select-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
select-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
capture-projects : ∀ w order s {s′} → W.captureMini w order s ≡ just s′ → Paths s s′
capture-projects w order s eq with W.phase (W.frameAt w s) | Pool.sameSnapshot order (W.registeredMini w s) | P.noParent (W.poolAt w s)
... | W.stoppingWritten | true | true = case just-injective eq of λ { refl → frame-paths w _ s }
... | W.stoppingWritten | false | _ = case eq of λ ()
... | W.stoppingWritten | true | false = case eq of λ ()
capture-projects w order s eq | W.idle | _ | _ = case eq of λ ()
capture-projects w order s eq | W.shutdownSelected | _ | _ = case eq of λ ()
capture-projects w order s eq | W.stoppingTraced | _ | _ = case eq of λ ()
capture-projects w order s eq | W.groupClosing | _ | _ = case eq of λ ()
capture-projects w order s eq | W.draining | _ | _ = case eq of λ ()
capture-projects w order s eq | W.drainReady | _ | _ = case eq of λ ()
capture-projects w order s eq | W.stoppedTrace | _ | _ = case eq of λ ()
capture-projects w order s eq | W.stoppedTracing | _ | _ = case eq of λ ()
capture-projects w order s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
capture-projects w order s eq | W.ownerAborting err | _ | _ = case eq of λ ()
capture-projects w order s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
capture-projects w order s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
capture-projects w order s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
capture-projects w order s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
capture-projects w order s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
request-group-projects : ∀ w s {s′} → W.requestGroup w s ≡ just s′ → Paths s s′
request-group-projects w s eq with W.phase (W.frameAt w s) | W.cancelPC (W.frameAt w s) | W.remaining (W.frameAt w s)
... | W.groupClosing | W.ready | j ∷ rest = case just-injective eq of λ { refl → frame-paths w _ s }
... | W.groupClosing | W.ready | [] = case eq of λ ()
... | W.groupClosing | W.requested j | _ = case eq of λ ()
... | W.groupClosing | W.delivered j | _ = case eq of λ ()
request-group-projects w s eq | W.idle | _ | _ = case eq of λ ()
request-group-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
request-group-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
request-group-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
request-group-projects w s eq | W.draining | _ | _ = case eq of λ ()
request-group-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
request-group-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
request-group-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
request-group-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
request-group-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
request-group-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
request-group-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
request-group-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
request-group-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
request-group-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
deliver-group-projects : ∀ w s {s′} → W.deliverMini w s ≡ just s′ → Paths s s′
deliver-group-projects w s eq with W.phase (W.frameAt w s) | W.cancelPC (W.frameAt w s) | W.remaining (W.frameAt w s)
... | W.groupClosing | W.requested j | current ∷ rest with j ≟ current | W.miniMember w j s | W.childEligible j s
...   | yes same | true | true with W.viaPool w (Pool.interruptJob j) s in advanced
...     | nothing = case eq of λ ()
...     | just next = case just-injective eq of λ { refl → frame-after w _ (via-pool-projects w (Pool.interruptJob j) s advanced) }
deliver-group-projects w s eq | W.groupClosing | W.requested j | current ∷ rest | no apart | _ | _ = case eq of λ ()
deliver-group-projects w s eq | W.groupClosing | W.requested j | current ∷ rest | yes same | false | _ = case eq of λ ()
deliver-group-projects w s eq | W.groupClosing | W.requested j | current ∷ rest | yes same | true | false = case eq of λ ()
deliver-group-projects w s eq | W.groupClosing | W.requested j | [] = case eq of λ ()
deliver-group-projects w s eq | W.groupClosing | W.ready | _ = case eq of λ ()
deliver-group-projects w s eq | W.groupClosing | W.delivered j | _ = case eq of λ ()
deliver-group-projects w s eq | W.idle | _ | _ = case eq of λ ()
deliver-group-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
deliver-group-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
deliver-group-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
deliver-group-projects w s eq | W.draining | _ | _ = case eq of λ ()
deliver-group-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
deliver-group-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
deliver-group-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
deliver-group-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
deliver-group-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
deliver-group-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
deliver-group-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
deliver-group-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
deliver-group-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
deliver-group-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
join-head-projects : ∀ w current s {s′} → W.joinMiniHead w current s ≡ just s′ → Paths s s′
join-head-projects w current s eq with W.remaining (W.frameAt w s) | lookup current (Pool.handles (W.poolAt w s))
... | head ∷ rest | just (Pool.resultAvailable exit) with current ≟ head
...   | yes same = case just-injective eq of λ { refl → frame-paths w _ s }
...   | no apart = case eq of λ ()
join-head-projects w current s eq | [] | _ = case eq of λ ()
join-head-projects w current s eq | _ ∷ _ | nothing = case eq of λ ()
join-head-projects w current s eq | _ ∷ _ | just Pool.bodyRunning = case eq of λ ()
join-head-projects w current s eq | _ ∷ _ | just (Pool.bodyReturned result) = case eq of λ ()
join-head-projects w current s eq | _ ∷ _ | just Pool.bodyUnwinding = case eq of λ ()
join-head-projects w current s eq | _ ∷ _ | just (Pool.deregisterPending exit) = case eq of λ ()
join-head-projects w current s eq | _ ∷ _ | just (Pool.deregistered exit) = case eq of λ ()
join-group-projects : ∀ w s {s′} → W.joinMini w s ≡ just s′ → Paths s s′
join-group-projects w s eq with W.phase (W.frameAt w s) | W.cancelPC (W.frameAt w s)
... | W.groupClosing | W.requested j = join-head-projects w j s eq
... | W.groupClosing | W.delivered j = join-head-projects w j s eq
... | W.groupClosing | W.ready = case eq of λ ()
join-group-projects w s eq | W.idle | _ = case eq of λ ()
join-group-projects w s eq | W.shutdownSelected | _ = case eq of λ ()
join-group-projects w s eq | W.stoppingTraced | _ = case eq of λ ()
join-group-projects w s eq | W.stoppingWritten | _ = case eq of λ ()
join-group-projects w s eq | W.draining | _ = case eq of λ ()
join-group-projects w s eq | W.drainReady | _ = case eq of λ ()
join-group-projects w s eq | W.stoppedTrace | _ = case eq of λ ()
join-group-projects w s eq | W.stoppedTracing | _ = case eq of λ ()
join-group-projects w s eq | W.monitorReturnedNormal | _ = case eq of λ ()
join-group-projects w s eq | W.ownerAborting err | _ = case eq of λ ()
join-group-projects w s eq | W.wholeClosing outcome | _ = case eq of λ ()
join-group-projects w s eq | W.wholeClosed outcome | _ = case eq of λ ()
join-group-projects w s eq | W.asyncFailureWritten err | _ = case eq of λ ()
join-group-projects w s eq | W.asyncDeadTracing err | _ = case eq of λ ()
join-group-projects w s eq | W.scopeDone outcome | _ = case eq of λ ()
finish-group-projects : ∀ w s {s′} → W.finishMini w s ≡ just s′ → Paths s s′
finish-group-projects w s eq with W.phase (W.frameAt w s) | W.cancelPC (W.frameAt w s) | W.remaining (W.frameAt w s)
... | W.groupClosing | W.ready | [] = case just-injective eq of λ { refl → phase-paths w W.draining s }
... | W.groupClosing | W.ready | _ ∷ _ = case eq of λ ()
... | W.groupClosing | W.requested j | _ = case eq of λ ()
... | W.groupClosing | W.delivered j | _ = case eq of λ ()
finish-group-projects w s eq | W.idle | _ | _ = case eq of λ ()
finish-group-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
finish-group-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
finish-group-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
finish-group-projects w s eq | W.draining | _ | _ = case eq of λ ()
finish-group-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
finish-group-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
finish-group-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
finish-group-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
finish-group-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
finish-group-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
finish-group-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
finish-group-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
finish-group-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
finish-group-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
discard-projects : ∀ j job s {s′} → W.discardClean j job s ≡ just s′ → Paths s s′
discard-projects j job s eq with Types.direction job
... | Mux.initiatorJob = case just-injective eq of λ { refl → idle s }
... | Mux.responderJob with P.locate j (P.pendingAt (Types.owner job) (W.protocolState s)) | P.muxAt (Types.mux job) (W.protocolState s)
...   | just (index , kept) | just m with IG.takePending index (Mux.finishedJobs m)
...     | just ((n , result) , rest) with does (n Data.Nat.≟ Types.protocolNumber job) ∧ P.sameOutcome ConnectionManagement.IGTypes.clean result
...       | true with W.viaSource (IG.discardJobOccurrence (Types.mux job) index) s in advanced
...         | nothing = case eq of λ ()
...         | just next = case just-injective eq of λ { refl → compose
  (via-source-projects (IG.discardJobOccurrence (Types.mux job) index) s advanced)
  (protocol-projects next _ (ProtocolFacts.metadata (W.protocolState next) _ _)) }
discard-projects j job s eq | Mux.responderJob | just (index , kept) | just m | just ((n , result) , rest) | false = case eq of λ ()
discard-projects j job s eq | Mux.responderJob | just (index , kept) | just m | nothing = case eq of λ ()
discard-projects j job s eq | Mux.responderJob | nothing | _ = case eq of λ ()
discard-projects j job s eq | Mux.responderJob | just pair | nothing = case eq of λ ()
prepare-projects : ∀ j w f s {s′} → W.prepareUnwind j w f s ≡ just s′ → Paths s s′
prepare-projects j w f s eq with lookup j (P.jobs (W.protocolState s))
... | nothing with W.isInfra j f
...   | true = case just-injective eq of λ { refl → idle s }
...   | false = case eq of λ ()
prepare-projects j w f s eq | just job with does (w ≟ Types.owner job) | Types.phase job
... | true | Types.executing = case just-injective eq of λ { refl → idle s }
... | true | Types.waitingEgress = case just-injective eq of λ { refl → idle s }
... | true | Types.resultCaptured ConnectionManagement.IGTypes.clean = discard-projects j job s eq
... | true | Types.resultCaptured (ConnectionManagement.IGTypes.errored err) = case eq of λ ()
... | false | _ = case eq of λ ()
unwind-projects : ∀ j s {s′} → W.unwindChild j s ≡ just s′ → Paths s s′
unwind-projects j s eq with W.ownerOf j s
... | nothing = case eq of λ ()
... | just (w , f) with lookup j (Pool.handles (W.poolAt w s))
...   | just Pool.bodyUnwinding with W.prepareUnwind j w f s in prepared
...     | nothing = case eq of λ ()
...     | just next with Pool.step (Pool.bodyUnwound j) (W.poolAt w next) in advanced
...       | nothing = case eq of λ ()
...       | just p = case just-injective eq of λ { refl → compose (prepare-projects j w f s prepared) (pool-step w f (Pool.bodyUnwound j) next advanced) }
unwind-projects j s eq | just (w , f) | nothing = case eq of λ ()
unwind-projects j s eq | just (w , f) | just Pool.bodyRunning = case eq of λ ()
unwind-projects j s eq | just (w , f) | just (Pool.bodyReturned result) = case eq of λ ()
unwind-projects j s eq | just (w , f) | just (Pool.deregisterPending exit) = case eq of λ ()
unwind-projects j s eq | just (w , f) | just (Pool.deregistered exit) = case eq of λ ()
unwind-projects j s eq | just (w , f) | just (Pool.resultAvailable exit) = case eq of λ ()
replacement-projects : ∀ j err s {s′} → W.replaceUnwind j err s ≡ just s′ → Paths s s′
replacement-projects j err s eq with lookup j (P.jobs (W.protocolState s))
... | nothing = case eq of λ ()
... | just job with W.replacementEligible (Types.phase job) | W.ownerOf j s
...   | true | just (w , f) with does (w ≟ Types.owner job) | Pool.step (Pool.resumeAfterUnwindError j) (W.poolAt w s) in advanced
...     | true | just p with P.step (P.protocolException j err) (W.protocolState (W.setPool w f p s)) in captured
...       | nothing = case eq of λ ()
...       | just next = case just-injective eq of λ { refl → compose
  (pool-step w f (Pool.resumeAfterUnwindError j) s advanced)
  (protocol-projects (W.setPool w f p s) next (ProtocolFacts.step-projects (P.protocolException j err) _ captured)) }
replacement-projects j err s eq | just job | true | just (w , f) | false | _ = case eq of λ ()
replacement-projects j err s eq | just job | true | just (w , f) | true | nothing = case eq of λ ()
replacement-projects j err s eq | just job | false | _ = case eq of λ ()
replacement-projects j err s eq | just job | true | nothing = case eq of λ ()
abort-projects : ∀ w err s {s′} → W.abortMonitor w err s ≡ just s′ → Paths s s′
abort-projects w err s eq with W.abortStage w s | W.ownerContext w s | P.noParent (W.poolAt w s)
... | true | just (f , mid) | true with P.muxAt mid (W.protocolState s)
...   | just m with Mux.callback m
...     | Mux.returned = case just-injective eq of λ { refl → phase-paths w (W.ownerAborting err) s }
abort-projects w err s eq | true | just (f , mid) | true | just m | Mux.readActive tr = case eq of λ ()
abort-projects w err s eq | true | just (f , mid) | true | just m | Mux.commitTrace active tr = case eq of λ ()
abort-projects w err s eq | true | just (f , mid) | true | just m | Mux.afterStart n = case eq of λ ()
abort-projects w err s eq | true | just (f , mid) | true | just m | Mux.forkPending n = case eq of λ ()
abort-projects w err s eq | true | just (f , mid) | true | just m | Mux.afterFailure = case eq of λ ()
abort-projects w err s eq | true | just (f , mid) | true | just m | Mux.tracerFailed n = case eq of λ ()
abort-projects w err s eq | true | just (f , mid) | true | nothing = case eq of λ ()
abort-projects w err s eq | false | _ | _ = case eq of λ ()
abort-projects w err s eq | true | nothing | _ = case eq of λ ()
abort-projects w err s eq | true | just pair | false = case eq of λ ()
begin-whole-projects : ∀ w order s {s′} → W.beginWhole w order s ≡ just s′ → Paths s s′
begin-whole-projects w order s eq with W.wholeOutcome w s
... | nothing = case eq of λ ()
... | just outcome with W.viaPool w (Pool.beginClose order) s in advanced
...   | nothing = case eq of λ ()
...   | just next = case just-injective eq of λ { refl → phase-after w (W.wholeClosing outcome) (via-pool-projects w (Pool.beginClose order) s advanced) }
whole-action-projects : ∀ w action s {s′} → W.wholeAction w action s ≡ just s′ → Paths s s′
whole-action-projects w action s eq with W.phase (W.frameAt w s)
... | W.wholeClosing outcome = via-pool-projects w action s eq
whole-action-projects w action s eq | W.idle = case eq of λ ()
whole-action-projects w action s eq | W.shutdownSelected = case eq of λ ()
whole-action-projects w action s eq | W.stoppingTraced = case eq of λ ()
whole-action-projects w action s eq | W.stoppingWritten = case eq of λ ()
whole-action-projects w action s eq | W.groupClosing = case eq of λ ()
whole-action-projects w action s eq | W.draining = case eq of λ ()
whole-action-projects w action s eq | W.drainReady = case eq of λ ()
whole-action-projects w action s eq | W.stoppedTrace = case eq of λ ()
whole-action-projects w action s eq | W.stoppedTracing = case eq of λ ()
whole-action-projects w action s eq | W.monitorReturnedNormal = case eq of λ ()
whole-action-projects w action s eq | W.ownerAborting err = case eq of λ ()
whole-action-projects w action s eq | W.wholeClosed outcome = case eq of λ ()
whole-action-projects w action s eq | W.asyncFailureWritten err = case eq of λ ()
whole-action-projects w action s eq | W.asyncDeadTracing err = case eq of λ ()
whole-action-projects w action s eq | W.scopeDone outcome = case eq of λ ()
whole-delivery-projects : ∀ w s {s′} → W.deliverWholeChild w s ≡ just s′ → Paths s s′
whole-delivery-projects w s eq with W.phase (W.frameAt w s) | W.ownerContext w s | Pool.phase (W.poolAt w s)
... | W.wholeClosing outcome | just (f , mid) | Pool.cancelPending j with W.wholeDeliverable w j f s
...   | true = via-pool-projects w Pool.deliverCancel s eq
...   | false = case eq of λ ()
whole-delivery-projects w s eq | W.wholeClosing outcome | nothing | _ = case eq of λ ()
whole-delivery-projects w s eq | W.idle | _ | _ = case eq of λ ()
whole-delivery-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
whole-delivery-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
whole-delivery-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
whole-delivery-projects w s eq | W.groupClosing | _ | _ = case eq of λ ()
whole-delivery-projects w s eq | W.draining | _ | _ = case eq of λ ()
whole-delivery-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
whole-delivery-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
whole-delivery-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
whole-delivery-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
whole-delivery-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
whole-delivery-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
whole-delivery-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
whole-delivery-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
whole-delivery-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
whole-delivery-projects w s eq | W.wholeClosing outcome | just (f , mid) | Pool.openPool = case eq of λ ()
whole-delivery-projects w s eq | W.wholeClosing outcome | just (f , mid) | Pool.closing = case eq of λ ()
whole-delivery-projects w s eq | W.wholeClosing outcome | just (f , mid) | Pool.closedPool = case eq of λ ()
whole-delivery-projects w s eq | W.wholeClosing outcome | just (f , mid) | Pool.joinPending j = case eq of λ ()
finish-whole-projects : ∀ w s {s′} → W.finishWhole w s ≡ just s′ → Paths s s′
finish-whole-projects w s eq with W.phase (W.frameAt w s)
... | W.wholeClosing outcome with W.viaPool w Pool.finishClose s in advanced
...   | nothing = case eq of λ ()
...   | just next = case just-injective eq of λ { refl → phase-after w (W.wholeClosed outcome) (via-pool-projects w Pool.finishClose s advanced) }
finish-whole-projects w s eq | W.idle = case eq of λ ()
finish-whole-projects w s eq | W.shutdownSelected = case eq of λ ()
finish-whole-projects w s eq | W.stoppingTraced = case eq of λ ()
finish-whole-projects w s eq | W.stoppingWritten = case eq of λ ()
finish-whole-projects w s eq | W.groupClosing = case eq of λ ()
finish-whole-projects w s eq | W.draining = case eq of λ ()
finish-whole-projects w s eq | W.drainReady = case eq of λ ()
finish-whole-projects w s eq | W.stoppedTrace = case eq of λ ()
finish-whole-projects w s eq | W.stoppedTracing = case eq of λ ()
finish-whole-projects w s eq | W.monitorReturnedNormal = case eq of λ ()
finish-whole-projects w s eq | W.ownerAborting err = case eq of λ ()
finish-whole-projects w s eq | W.wholeClosed outcome = case eq of λ ()
finish-whole-projects w s eq | W.asyncFailureWritten err = case eq of λ ()
finish-whole-projects w s eq | W.asyncDeadTracing err = case eq of λ ()
finish-whole-projects w s eq | W.scopeDone outcome = case eq of λ ()
async-failure-projects : ∀ w s {s′} → W.asyncFailure w s ≡ just s′ → Paths s s′
async-failure-projects w s eq with W.phase (W.frameAt w s) | Pool.phase (W.poolAt w s) | W.ownerContext w s
... | W.wholeClosed (W.asyncExit err) | Pool.closedPool | just (f , mid) with W.viaSource (IG.recordAsyncMuxFailure mid err) s in advanced
...   | nothing = case eq of λ ()
...   | just next = case just-injective eq of λ { refl → phase-after w (W.asyncFailureWritten err) (via-source-projects (IG.recordAsyncMuxFailure mid err) s advanced) }
async-failure-projects w s eq | W.wholeClosed W.normalExit | _ | _ = case eq of λ ()
async-failure-projects w s eq | W.wholeClosed (W.failedExit err) | _ | _ = case eq of λ ()
async-failure-projects w s eq | W.wholeClosed (W.asyncExit err) | Pool.closedPool | nothing = case eq of λ ()
async-failure-projects w s eq | W.idle | _ | _ = case eq of λ ()
async-failure-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
async-failure-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
async-failure-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
async-failure-projects w s eq | W.groupClosing | _ | _ = case eq of λ ()
async-failure-projects w s eq | W.draining | _ | _ = case eq of λ ()
async-failure-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
async-failure-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
async-failure-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
async-failure-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
async-failure-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
async-failure-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
async-failure-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
async-failure-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
async-failure-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
async-failure-projects w s eq | W.wholeClosed (W.asyncExit err) | Pool.openPool | _ = case eq of λ ()
async-failure-projects w s eq | W.wholeClosed (W.asyncExit err) | Pool.closing | _ = case eq of λ ()
async-failure-projects w s eq | W.wholeClosed (W.asyncExit err) | Pool.cancelPending j | _ = case eq of λ ()
async-failure-projects w s eq | W.wholeClosed (W.asyncExit err) | Pool.joinPending j | _ = case eq of λ ()
async-dead-projects : ∀ w s {s′} → W.asyncDead w s ≡ just s′ → Paths s s′
async-dead-projects w s eq with W.phase (W.frameAt w s) | W.ownerContext w s
... | W.asyncFailureWritten err | just (f , mid) with W.viaSource (IG.traceMuxDead mid) s in advanced
...   | nothing = case eq of λ ()
...   | just next = case just-injective eq of λ { refl → phase-after w (W.asyncDeadTracing err) (via-source-projects (IG.traceMuxDead mid) s advanced) }
async-dead-projects w s eq | W.asyncFailureWritten err | nothing = case eq of λ ()
async-dead-projects w s eq | W.idle | _ = case eq of λ ()
async-dead-projects w s eq | W.shutdownSelected | _ = case eq of λ ()
async-dead-projects w s eq | W.stoppingTraced | _ = case eq of λ ()
async-dead-projects w s eq | W.stoppingWritten | _ = case eq of λ ()
async-dead-projects w s eq | W.groupClosing | _ = case eq of λ ()
async-dead-projects w s eq | W.draining | _ = case eq of λ ()
async-dead-projects w s eq | W.drainReady | _ = case eq of λ ()
async-dead-projects w s eq | W.stoppedTrace | _ = case eq of λ ()
async-dead-projects w s eq | W.stoppedTracing | _ = case eq of λ ()
async-dead-projects w s eq | W.monitorReturnedNormal | _ = case eq of λ ()
async-dead-projects w s eq | W.ownerAborting err | _ = case eq of λ ()
async-dead-projects w s eq | W.wholeClosing outcome | _ = case eq of λ ()
async-dead-projects w s eq | W.wholeClosed outcome | _ = case eq of λ ()
async-dead-projects w s eq | W.asyncDeadTracing err | _ = case eq of λ ()
async-dead-projects w s eq | W.scopeDone outcome | _ = case eq of λ ()
async-trace-projects : ∀ sample w s {s′} → W.asyncTrace sample w s ≡ just s′ → Paths s s′
async-trace-projects sample w s eq with W.phase (W.frameAt w s) | W.ownerContext w s
... | W.asyncDeadTracing err | just (f , mid) with sample
...   | true = via-source-projects (IG.sampleTracer mid) s eq
...   | false = via-source-projects (IG.commitTracer mid) s eq
async-trace-projects sample w s eq | W.asyncDeadTracing err | nothing = case eq of λ ()
async-trace-projects sample w s eq | W.idle | _ = case eq of λ ()
async-trace-projects sample w s eq | W.shutdownSelected | _ = case eq of λ ()
async-trace-projects sample w s eq | W.stoppingTraced | _ = case eq of λ ()
async-trace-projects sample w s eq | W.stoppingWritten | _ = case eq of λ ()
async-trace-projects sample w s eq | W.groupClosing | _ = case eq of λ ()
async-trace-projects sample w s eq | W.draining | _ = case eq of λ ()
async-trace-projects sample w s eq | W.drainReady | _ = case eq of λ ()
async-trace-projects sample w s eq | W.stoppedTrace | _ = case eq of λ ()
async-trace-projects sample w s eq | W.stoppedTracing | _ = case eq of λ ()
async-trace-projects sample w s eq | W.monitorReturnedNormal | _ = case eq of λ ()
async-trace-projects sample w s eq | W.ownerAborting err | _ = case eq of λ ()
async-trace-projects sample w s eq | W.wholeClosing outcome | _ = case eq of λ ()
async-trace-projects sample w s eq | W.wholeClosed outcome | _ = case eq of λ ()
async-trace-projects sample w s eq | W.asyncFailureWritten err | _ = case eq of λ ()
async-trace-projects sample w s eq | W.scopeDone outcome | _ = case eq of λ ()
finish-async-projects : ∀ w s {s′} → W.finishAsync w s ≡ just s′ → Paths s s′
finish-async-projects w s eq with W.phase (W.frameAt w s) | W.ownerContext w s | Pool.phase (W.poolAt w s)
... | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool with P.muxAt mid (W.protocolState s)
...   | just m with Mux.callback m | Monitor.finishMatches (Monitor.failed err) (Mux.status m)
...     | Mux.returned | true = case just-injective eq of λ { refl → phase-paths w (W.scopeDone (W.asyncExit err)) s }
...     | Mux.returned | false = case eq of λ ()
finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | Mux.readActive tr | _ = case eq of λ ()
finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | Mux.commitTrace active tr | _ = case eq of λ ()
finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | Mux.afterStart n | _ = case eq of λ ()
finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | Mux.forkPending n | _ = case eq of λ ()
finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | Mux.afterFailure | _ = case eq of λ ()
finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | Mux.tracerFailed n | _ = case eq of λ ()
finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | nothing = case eq of λ ()
finish-async-projects w s eq | W.asyncDeadTracing err | nothing | _ = case eq of λ ()
finish-async-projects w s eq | W.idle | _ | _ = case eq of λ ()
finish-async-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
finish-async-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
finish-async-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
finish-async-projects w s eq | W.groupClosing | _ | _ = case eq of λ ()
finish-async-projects w s eq | W.draining | _ | _ = case eq of λ ()
finish-async-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
finish-async-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
finish-async-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
finish-async-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
finish-async-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
finish-async-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
finish-async-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
finish-async-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
finish-async-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.openPool = case eq of λ ()
finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closing = case eq of λ ()
finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.cancelPending j = case eq of λ ()
finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.joinPending j = case eq of λ ()
finish-ordinary-projects : ∀ w s {s′} → W.finishOrdinary w s ≡ just s′ → Paths s s′
finish-ordinary-projects w s eq with W.phase (W.frameAt w s) | Pool.phase (W.poolAt w s)
... | W.wholeClosed W.normalExit | Pool.closedPool = case just-injective eq of λ { refl → phase-paths w (W.scopeDone W.normalExit) s }
... | W.wholeClosed (W.failedExit err) | Pool.closedPool = case just-injective eq of λ { refl → phase-paths w (W.scopeDone (W.failedExit err)) s }
... | W.wholeClosed (W.asyncExit err) | _ = case eq of λ ()
finish-ordinary-projects w s eq | W.idle | _ = case eq of λ ()
finish-ordinary-projects w s eq | W.shutdownSelected | _ = case eq of λ ()
finish-ordinary-projects w s eq | W.stoppingTraced | _ = case eq of λ ()
finish-ordinary-projects w s eq | W.stoppingWritten | _ = case eq of λ ()
finish-ordinary-projects w s eq | W.groupClosing | _ = case eq of λ ()
finish-ordinary-projects w s eq | W.draining | _ = case eq of λ ()
finish-ordinary-projects w s eq | W.drainReady | _ = case eq of λ ()
finish-ordinary-projects w s eq | W.stoppedTrace | _ = case eq of λ ()
finish-ordinary-projects w s eq | W.stoppedTracing | _ = case eq of λ ()
finish-ordinary-projects w s eq | W.monitorReturnedNormal | _ = case eq of λ ()
finish-ordinary-projects w s eq | W.ownerAborting err | _ = case eq of λ ()
finish-ordinary-projects w s eq | W.wholeClosing outcome | _ = case eq of λ ()
finish-ordinary-projects w s eq | W.asyncFailureWritten err | _ = case eq of λ ()
finish-ordinary-projects w s eq | W.asyncDeadTracing err | _ = case eq of λ ()
finish-ordinary-projects w s eq | W.scopeDone outcome | _ = case eq of λ ()
finish-ordinary-projects w s eq | W.wholeClosed W.normalExit | Pool.openPool = case eq of λ ()
finish-ordinary-projects w s eq | W.wholeClosed W.normalExit | Pool.closing = case eq of λ ()
finish-ordinary-projects w s eq | W.wholeClosed W.normalExit | Pool.cancelPending j = case eq of λ ()
finish-ordinary-projects w s eq | W.wholeClosed W.normalExit | Pool.joinPending j = case eq of λ ()
finish-ordinary-projects w s eq | W.wholeClosed (W.failedExit err) | Pool.openPool = case eq of λ ()
finish-ordinary-projects w s eq | W.wholeClosed (W.failedExit err) | Pool.closing = case eq of λ ()
finish-ordinary-projects w s eq | W.wholeClosed (W.failedExit err) | Pool.cancelPending j = case eq of λ ()
finish-ordinary-projects w s eq | W.wholeClosed (W.failedExit err) | Pool.joinPending j = case eq of λ ()
-- Every successful graceful return has the actual owner/mux lookup and a
-- returned callback at Stopped. It cannot be inferred merely from a status
-- write, a completed group snapshot, or a pool that happens to be empty.
record StoppedReturn (w : WorkerId) (s s′ : W.State) : Set where
  constructor stoppedReturn
  field ownerFrame : U.Frame
        capturedMux : MuxId
        muxValue : Mux.Mux
        phase-matches : W.sameStage W.stoppedTracing (W.phase (W.frameAt w s)) ≡ true
        owner-found : W.ownerContext w s ≡ just (ownerFrame , capturedMux)
        mux-found : P.muxAt capturedMux (W.protocolState s) ≡ just muxValue
        stopped-status : Mux.status muxValue ≡ Mux.stopped
        callback-returned : Mux.callback muxValue ≡ Mux.returned
        next-state : s′ ≡ W.setPhase w W.monitorReturnedNormal s
finish-stopped-observation : ∀ w s {s′} → W.finishStopped w s ≡ just s′ → StoppedReturn w s s′
finish-stopped-observation w s eq with W.sameStage W.stoppedTracing (W.phase (W.frameAt w s)) in phase | W.ownerContext w s in owner
... | true | just (f , mid) with P.muxAt mid (W.protocolState s) in found
...   | just m with Mux.status m in status | Mux.callback m in callback
...     | Mux.stopped | Mux.returned = stoppedReturn f mid m phase owner found status callback (sym (just-injective eq))
...     | Mux.stopped | Mux.readActive tr = case eq of λ ()
...     | Mux.stopped | Mux.commitTrace flag tr = case eq of λ ()
...     | Mux.stopped | Mux.afterStart n = case eq of λ ()
...     | Mux.stopped | Mux.forkPending n = case eq of λ ()
...     | Mux.stopped | Mux.afterFailure = case eq of λ ()
...     | Mux.stopped | Mux.tracerFailed n = case eq of λ ()
...     | Mux.ready | _ = case eq of λ ()
...     | Mux.stopping | _ = case eq of λ ()
...     | Mux.failed err | _ = case eq of λ ()
finish-stopped-observation w s eq | true | just (f , mid) | nothing = case eq of λ ()
finish-stopped-observation w s eq | false | _ = case eq of λ ()
finish-stopped-observation w s eq | true | nothing = case eq of λ ()
finish-stopped-projects : ∀ w s {s′} → W.finishStopped w s ≡ just s′ → Paths s s′
finish-stopped-projects w s eq = subst (Paths s)
  (sym (StoppedReturn.next-state (finish-stopped-observation w s eq))) (phase-paths w W.monitorReturnedNormal s)

step-projects : ∀ action s {s′} → W.step action s ≡ just s′ → Paths s s′
step-projects (W.run action) s eq = inherit-projects action s eq
step-projects (W.requestShutdown w) s eq = request-projects w s eq
step-projects (W.selectShutdown w) s eq = select-projects w s eq
step-projects (W.observeStoppingTrace w) s eq = from-phase-projects w W.shutdownSelected W.stoppingTraced s eq
step-projects (W.writeStopping w) s eq = source-phase-projects w W.stoppingTraced W.stoppingWritten IG.recordMuxStopping s eq
step-projects (W.captureGroup w order) s eq = capture-projects w order s eq
step-projects (W.requestGroupCancel w) s eq = request-group-projects w s eq
step-projects (W.deliverGroup w) s eq = deliver-group-projects w s eq
step-projects (W.joinGroup w) s eq = join-group-projects w s eq
step-projects (W.finishGroup w) s eq = finish-group-projects w s eq
step-projects (W.drainEmpty w) s eq = from-phase-projects w W.draining W.drainReady s eq
step-projects (W.timeout2Elapsed w) s eq = from-phase-projects w W.draining W.drainReady s eq
step-projects (W.writeStopped w) s eq = source-phase-projects w W.drainReady W.stoppedTrace IG.completeMuxStopping s eq
step-projects (W.observeTraceStopped w) s eq = source-phase-projects w W.stoppedTrace W.stoppedTracing IG.traceGracefulMuxStopped s eq
step-projects (W.sampleStoppedTracer w) s eq = source-phase-projects w W.stoppedTracing W.stoppedTracing IG.sampleTracer s eq
step-projects (W.commitStoppedTracer w) s eq = source-phase-projects w W.stoppedTracing W.stoppedTracing IG.commitTracer s eq
step-projects (W.finishStoppedTrace w) s eq = finish-stopped-projects w s eq
step-projects (W.finishChildUnwind j) s eq = unwind-projects j s eq
step-projects (W.unwindReplacedBySync j err) s eq = replacement-projects j err s eq
step-projects (W.abortOwner w err) s eq = abort-projects w err s eq
step-projects (W.beginWholeClose w order) s eq = begin-whole-projects w order s eq
step-projects (W.requestWholeCancel w) s eq = whole-action-projects w Pool.requestCancel s eq
step-projects (W.deliverWhole w) s eq = whole-delivery-projects w s eq
step-projects (W.joinWhole w) s eq = whole-action-projects w Pool.join s eq
step-projects (W.finishWholeClose w) s eq = finish-whole-projects w s eq
step-projects (W.finishNormalScope w) s eq = finish-ordinary-projects w s eq
step-projects (W.writeAsyncFailure w) s eq = async-failure-projects w s eq
step-projects (W.beginAsyncDead w) s eq = async-dead-projects w s eq
step-projects (W.sampleAsyncTracer w) s eq = async-trace-projects true w s eq
step-projects (W.commitAsyncTracer w) s eq = async-trace-projects false w s eq
step-projects (W.finishAsyncDead w) s eq = finish-async-projects w s eq
exec-projects : ∀ {s actions s′} → W.Executes s actions s′ → Paths s s′
exec-projects {s = s} W.done = idle s
exec-projects (W.next {s = s} {a = action} eq path) = compose (step-projects action s eq) (exec-projects path)
initial-base : ∀ c {s} → W.initial c ≡ just s → Monitor.initial c ≡ just (W.base s)
initial-base c eq with Monitor.initial c
... | nothing = case eq of λ ()
... | just s = case just-injective eq of λ { refl → refl }
initial-source : ∀ c {s} → W.initial c ≡ just s → W.source s ≡ c
initial-source c initialized = Base.initial-source c (initial-base c initialized)
initial-pool : ∀ c {s} → W.initial c ≡ just s → ∀ selected → W.poolAt selected s ≡ Pool.initial
initial-pool c initialized selected = Base.initial-pool c (initial-base c initialized) selected
pool-from-initial : ∀ {c start actions s} → W.initial c ≡ just start → W.Executes start actions s →
  ∀ selected → ProtocolFacts.PTrace Pool.initial (W.poolAt selected s)
pool-from-initial {c} initialized path selected = ProtocolFacts.trace-left (sym (initial-pool c initialized selected)) (pools (exec-projects path) selected)
captures-preserves : ∀ {s actions s′} → Capture.Captures (W.source s) → W.Executes s actions s′ → Capture.Captures (W.source s′)
captures-preserves valid path = Capture.exec-preserves valid (proj₂ (machine (exec-projects path)))
supply-preserves : ∀ {s actions s′} → Supply.Valid (W.source s) → W.Executes s actions s′ → Supply.Valid (W.source s′)
supply-preserves valid path = Supply.exec-preserves valid (proj₂ (machine (exec-projects path)))
from-initial-captures : ∀ {c start actions s} → W.initial (O.initial c) ≡ just start → W.Executes start actions s → Capture.Captures (W.source s)
from-initial-captures {c} initialized path = captures-preserves
  (subst Capture.Captures (sym (initial-source (O.initial c) initialized)) (Capture.initial-valid c)) path
from-initial-supply : ∀ {c start actions s} → W.initial (O.initial c) ≡ just start → SupplyBounds (Machine.world c) → W.Executes start actions s → Supply.Valid (W.source s)
from-initial-supply {c} initialized bounded path = supply-preserves
  (subst Supply.Valid (sym (initial-source (O.initial c) initialized)) (Capture.initial-valid c , bounded)) path

-- This certificate is about the immutable WHOLE-pool snapshot. A historical
-- handle already removed before beginClose is deliberately outside its scope.
whole-closed-from-initial : ∀ {c start actions s} → W.initial c ≡ just start → W.Executes start actions s →
  ∀ selected → Pool.phase (W.poolAt selected s) ≡ Pool.closedPool →
  ∀ j → j ∈ Pool.snapshot (W.poolAt selected s) → Close.Terminal (W.poolAt selected s) j
whole-closed-from-initial initialized path selected closed = Close.from-initial
  (proj₂ (pool-from-initial initialized path selected)) closed

-- The group read captures exactly the current MiniProtocol-tagged registration
-- subset. Its permutation guard preserves multiplicity/uniqueness semantics of
-- the model's registry traversal and excludes infrastructure/history by filter.
record GroupCapture (w : WorkerId) (order : List JobId) (before after : W.State) : Set where
  constructor groupCapture
  field current-registration : List JobId
        registration-read : current-registration ≡ Pool.registered (W.poolAt w before)
        selected-subset : W.registeredMini w before ≡ W.miniEntries w current-registration before
        exact-order : Pool.sameSnapshot order (W.registeredMini w before) ≡ true
        parent-settled : P.noParent (W.poolAt w before) ≡ true
        stopping-before : W.phase (W.frameAt w before) ≡ W.stoppingWritten
        after-shape : after ≡ W.setFrame w (W.frame W.groupClosing order order [] W.ready) before
        pools-unchanged : ∀ selected → W.poolAt selected after ≡ W.poolAt selected before
open GroupCapture public
capture-observation : ∀ w order s {s′} → W.step (W.captureGroup w order) s ≡ just s′ → GroupCapture w order s s′
capture-observation w order s eq with W.phase (W.frameAt w s) in pc | Pool.sameSnapshot order (W.registeredMini w s) in exact | P.noParent (W.poolAt w s) in settled
... | W.stoppingWritten | true | true = case just-injective eq of λ { refl → groupCapture _ refl refl exact settled pc refl (λ _ → refl) }
... | W.stoppingWritten | false | _ = case eq of λ ()
... | W.stoppingWritten | true | false = case eq of λ ()
capture-observation w order s eq | W.idle | _ | _ = case eq of λ ()
capture-observation w order s eq | W.shutdownSelected | _ | _ = case eq of λ ()
capture-observation w order s eq | W.stoppingTraced | _ | _ = case eq of λ ()
capture-observation w order s eq | W.groupClosing | _ | _ = case eq of λ ()
capture-observation w order s eq | W.draining | _ | _ = case eq of λ ()
capture-observation w order s eq | W.drainReady | _ | _ = case eq of λ ()
capture-observation w order s eq | W.stoppedTrace | _ | _ = case eq of λ ()
capture-observation w order s eq | W.stoppedTracing | _ | _ = case eq of λ ()
capture-observation w order s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
capture-observation w order s eq | W.ownerAborting err | _ | _ = case eq of λ ()
capture-observation w order s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
capture-observation w order s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
capture-observation w order s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
capture-observation w order s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
capture-observation w order s eq | W.scopeDone outcome | _ | _ = case eq of λ ()

-- Joining observes the captured physical handle's Async result. Registry
-- absence or a queued protocol result alone cannot discharge this observation.
record GroupJoin (w : WorkerId) (current : JobId) (before after : W.State) : Set where
  constructor groupJoin
  field head : JobId
        tail : List JobId
        exit : Pool.Exit
        original-cursor : W.remaining (W.frameAt w before) ≡ head ∷ tail
        selected-head : current ≡ head
        result-observed : lookup current (Pool.handles (W.poolAt w before)) ≡ just (Pool.resultAvailable exit)
        after-shape : after ≡ W.setFrame w (record (W.frameAt w before)
          { remaining = tail; joined = W.joined (W.frameAt w before) ++ (head ∷ []); cancelPC = W.ready }) before
        source-unchanged : W.source after ≡ W.source before
        pools-unchanged : ∀ selected → W.poolAt selected after ≡ W.poolAt selected before
open GroupJoin public
join-head-observation : ∀ w current s {s′} → W.joinMiniHead w current s ≡ just s′ → GroupJoin w current s s′
join-head-observation w current s eq with W.remaining (W.frameAt w s) in cursor | lookup current (Pool.handles (W.poolAt w s)) in found
... | head ∷ rest | just (Pool.resultAvailable exit) with current ≟ head
...   | yes same = case just-injective eq of λ { refl → groupJoin head rest exit cursor same found refl refl (λ _ → refl) }
...   | no apart = case eq of λ ()
join-head-observation w current s eq | [] | _ = case eq of λ ()
join-head-observation w current s eq | _ ∷ _ | nothing = case eq of λ ()
join-head-observation w current s eq | _ ∷ _ | just Pool.bodyRunning = case eq of λ ()
join-head-observation w current s eq | _ ∷ _ | just (Pool.bodyReturned result) = case eq of λ ()
join-head-observation w current s eq | _ ∷ _ | just Pool.bodyUnwinding = case eq of λ ()
join-head-observation w current s eq | _ ∷ _ | just (Pool.deregisterPending exit) = case eq of λ ()
join-head-observation w current s eq | _ ∷ _ | just (Pool.deregistered exit) = case eq of λ ()

-- Local unwind keeps the actual intermediate source/pending-state computation
-- and the distinct physical body-unwound transition. It does not certify an
-- absent buffer finalizer or manufacture a JobPool completion on cancellation.
record ChildUnwind (j : JobId) (before after : W.State) : Set where
  constructor childUnwind
  field owner : WorkerId
        ownerFrame : U.Frame
        prepared : W.State
        poolAfter : Pool.State
        physical-owner : W.ownerOf j before ≡ just (owner , ownerFrame)
        interrupted-body : lookup j (Pool.handles (W.poolAt owner before)) ≡ just Pool.bodyUnwinding
        source-preparation : W.prepareUnwind j owner ownerFrame before ≡ just prepared
        actual-unwind : Pool.step (Pool.bodyUnwound j) (W.poolAt owner prepared) ≡ just poolAfter
        after-shape : after ≡ W.setPool owner ownerFrame poolAfter prepared
open ChildUnwind public
unwind-observation : ∀ j s {s′} → W.step (W.finishChildUnwind j) s ≡ just s′ → ChildUnwind j s s′
unwind-observation j s eq with W.ownerOf j s in owned
... | nothing = case eq of λ ()
... | just (w , f) with lookup j (Pool.handles (W.poolAt w s)) in interrupted
...   | just Pool.bodyUnwinding with W.prepareUnwind j w f s in prepared
...     | nothing = case eq of λ ()
...     | just next with Pool.step (Pool.bodyUnwound j) (W.poolAt w next) in advanced
...       | nothing = case eq of λ ()
...       | just p = case just-injective eq of λ { refl → childUnwind w f next p owned interrupted prepared advanced refl }
unwind-observation j s eq | just (w , f) | nothing = case eq of λ ()
unwind-observation j s eq | just (w , f) | just Pool.bodyRunning = case eq of λ ()
unwind-observation j s eq | just (w , f) | just (Pool.bodyReturned result) = case eq of λ ()
unwind-observation j s eq | just (w , f) | just (Pool.deregisterPending exit) = case eq of λ ()
unwind-observation j s eq | just (w , f) | just (Pool.deregistered exit) = case eq of λ ()
unwind-observation j s eq | just (w , f) | just (Pool.resultAvailable exit) = case eq of λ ()

record PoolTransition (w : WorkerId) (action : Pool.Action) (before after : W.State) : Set where
  constructor poolTransition
  field ownerFrame : U.Frame
        capturedMux : MuxId
        poolAfter : Pool.State
        owner-context : W.ownerContext w before ≡ just (ownerFrame , capturedMux)
        actual-pool-step : Pool.step action (W.poolAt w before) ≡ just poolAfter
        after-shape : after ≡ W.setPool w ownerFrame poolAfter before
open PoolTransition public
via-pool-observation : ∀ w action s {s′} → W.viaPool w action s ≡ just s′ → PoolTransition w action s s′
via-pool-observation w action s eq with W.ownerContext w s in context
... | nothing = case eq of λ ()
... | just (f , mid) with Pool.step action (W.poolAt w s) in advanced
...   | nothing = case eq of λ ()
...   | just p = case just-injective eq of λ { refl → poolTransition f mid p context advanced refl }

record GroupDelivery (w : WorkerId) (before after : W.State) : Set where
  constructor groupDelivery
  field selectedJob current : JobId
        tail : List JobId
        intermediate : W.State
        group-stage : W.phase (W.frameAt w before) ≡ W.groupClosing
        request-captured : W.cancelPC (W.frameAt w before) ≡ W.requested selectedJob
        original-cursor : W.remaining (W.frameAt w before) ≡ current ∷ tail
        selected-head : selectedJob ≡ current
        registered-mini-owner : W.miniMember w selectedJob before ≡ true
        body-interruptible : W.childEligible selectedJob before ≡ true
        actual-interrupt : PoolTransition w (Pool.interruptJob selectedJob) before intermediate
        after-shape : after ≡ W.setFrame w (record (W.frameAt w intermediate) { cancelPC = W.delivered selectedJob }) intermediate
open GroupDelivery public
delivery-observation : ∀ w s {s′} → W.step (W.deliverGroup w) s ≡ just s′ → GroupDelivery w s s′
delivery-observation w s eq with W.phase (W.frameAt w s) in stage | W.cancelPC (W.frameAt w s) in requested | W.remaining (W.frameAt w s) in cursor
... | W.groupClosing | W.requested j | current ∷ rest with j ≟ current | W.miniMember w j s in member | W.childEligible j s in eligible
...   | yes same | true | true with W.viaPool w (Pool.interruptJob j) s in advanced
...     | nothing = case eq of λ ()
...     | just next = case just-injective eq of λ { refl → groupDelivery j current rest next stage requested cursor same member eligible
  (via-pool-observation w (Pool.interruptJob j) s advanced) refl }
delivery-observation w s eq | W.groupClosing | W.requested j | current ∷ rest | no apart | _ | _ = case eq of λ ()
delivery-observation w s eq | W.groupClosing | W.requested j | current ∷ rest | yes same | false | _ = case eq of λ ()
delivery-observation w s eq | W.groupClosing | W.requested j | current ∷ rest | yes same | true | false = case eq of λ ()
delivery-observation w s eq | W.groupClosing | W.requested j | [] = case eq of λ ()
delivery-observation w s eq | W.groupClosing | W.ready | _ = case eq of λ ()
delivery-observation w s eq | W.groupClosing | W.delivered j | _ = case eq of λ ()
delivery-observation w s eq | W.idle | _ | _ = case eq of λ ()
delivery-observation w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
delivery-observation w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
delivery-observation w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
delivery-observation w s eq | W.draining | _ | _ = case eq of λ ()
delivery-observation w s eq | W.drainReady | _ | _ = case eq of λ ()
delivery-observation w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
delivery-observation w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
delivery-observation w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
delivery-observation w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
delivery-observation w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
delivery-observation w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
delivery-observation w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
delivery-observation w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
delivery-observation w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()

join-observation : ∀ w s {s′} → W.step (W.joinGroup w) s ≡ just s′ → Σ JobId (λ j → GroupJoin w j s s′)
join-observation w s eq with W.phase (W.frameAt w s) | W.cancelPC (W.frameAt w s)
... | W.groupClosing | W.requested j = j , join-head-observation w j s eq
... | W.groupClosing | W.delivered j = j , join-head-observation w j s eq
... | W.groupClosing | W.ready = case eq of λ ()
join-observation w s eq | W.idle | _ = case eq of λ ()
join-observation w s eq | W.shutdownSelected | _ = case eq of λ ()
join-observation w s eq | W.stoppingTraced | _ = case eq of λ ()
join-observation w s eq | W.stoppingWritten | _ = case eq of λ ()
join-observation w s eq | W.draining | _ = case eq of λ ()
join-observation w s eq | W.drainReady | _ = case eq of λ ()
join-observation w s eq | W.stoppedTrace | _ = case eq of λ ()
join-observation w s eq | W.stoppedTracing | _ = case eq of λ ()
join-observation w s eq | W.monitorReturnedNormal | _ = case eq of λ ()
join-observation w s eq | W.ownerAborting err | _ = case eq of λ ()
join-observation w s eq | W.wholeClosing outcome | _ = case eq of λ ()
join-observation w s eq | W.wholeClosed outcome | _ = case eq of λ ()
join-observation w s eq | W.asyncFailureWritten err | _ = case eq of λ ()
join-observation w s eq | W.asyncDeadTracing err | _ = case eq of λ ()
join-observation w s eq | W.scopeDone outcome | _ = case eq of λ ()

record OwnerAbort (w : WorkerId) (err : ErrorId) (before after : W.State) : Set where
  constructor ownerAbort
  field ownerFrame : U.Frame
        capturedMux : MuxId
        sourceMux : Mux.Mux
        interruptible-stage : W.abortStage w before ≡ true
        owner-context : W.ownerContext w before ≡ just (ownerFrame , capturedMux)
        parent-settled : P.noParent (W.poolAt w before) ≡ true
        mux-found : P.muxAt capturedMux (W.protocolState before) ≡ just sourceMux
        callback-returned : Mux.callback sourceMux ≡ Mux.returned
        after-shape : after ≡ W.setPhase w (W.ownerAborting err) before
        source-unchanged : W.source after ≡ W.source before
        pools-unchanged : ∀ selected → W.poolAt selected after ≡ W.poolAt selected before
open OwnerAbort public
abort-observation : ∀ w err s {s′} → W.step (W.abortOwner w err) s ≡ just s′ → OwnerAbort w err s s′
abort-observation w err s eq with W.abortStage w s in stage | W.ownerContext w s in context | P.noParent (W.poolAt w s) in settled
... | true | just (f , mid) | true with P.muxAt mid (W.protocolState s) in found
...   | just m with Mux.callback m in returned
...     | Mux.returned = case just-injective eq of λ { refl → ownerAbort f mid m stage context settled found returned refl refl (λ _ → refl) }
abort-observation w err s eq | true | just (f , mid) | true | just m | Mux.readActive tr = case eq of λ ()
abort-observation w err s eq | true | just (f , mid) | true | just m | Mux.commitTrace active tr = case eq of λ ()
abort-observation w err s eq | true | just (f , mid) | true | just m | Mux.afterStart n = case eq of λ ()
abort-observation w err s eq | true | just (f , mid) | true | just m | Mux.forkPending n = case eq of λ ()
abort-observation w err s eq | true | just (f , mid) | true | just m | Mux.afterFailure = case eq of λ ()
abort-observation w err s eq | true | just (f , mid) | true | just m | Mux.tracerFailed n = case eq of λ ()
abort-observation w err s eq | true | just (f , mid) | true | nothing = case eq of λ ()
abort-observation w err s eq | false | _ | _ = case eq of λ ()
abort-observation w err s eq | true | nothing | _ = case eq of λ ()
abort-observation w err s eq | true | just pair | false = case eq of λ ()

record WholeCapture (w : WorkerId) (order : List JobId) (before after : W.State) : Set where
  constructor wholeCapture
  field outcome : W.Outcome
        intermediate : W.State
        monitor-outcome : W.wholeOutcome w before ≡ just outcome
        actual-close : PoolTransition w (Pool.beginClose order) before intermediate
        after-shape : after ≡ W.setPhase w (W.wholeClosing outcome) intermediate
open WholeCapture public
whole-capture-observation : ∀ w order s {s′} → W.step (W.beginWholeClose w order) s ≡ just s′ → WholeCapture w order s s′
whole-capture-observation w order s eq with W.wholeOutcome w s in outcome
... | nothing = case eq of λ ()
... | just result with W.viaPool w (Pool.beginClose order) s in advanced
...   | nothing = case eq of λ ()
...   | just next = case just-injective eq of λ { refl → wholeCapture result next outcome (via-pool-observation w (Pool.beginClose order) s advanced) refl }

record WholeFinish (w : WorkerId) (before after : W.State) : Set where
  constructor wholeFinish
  field outcome : W.Outcome
        intermediate : W.State
        closing-before : W.phase (W.frameAt w before) ≡ W.wholeClosing outcome
        actual-finish : PoolTransition w Pool.finishClose before intermediate
        after-shape : after ≡ W.setPhase w (W.wholeClosed outcome) intermediate
open WholeFinish public
whole-finish-observation : ∀ w s {s′} → W.step (W.finishWholeClose w) s ≡ just s′ → WholeFinish w s s′
whole-finish-observation w s eq with W.phase (W.frameAt w s) in stage
... | W.wholeClosing result with W.viaPool w Pool.finishClose s in advanced
...   | nothing = case eq of λ ()
...   | just next = case just-injective eq of λ { refl → wholeFinish result next stage (via-pool-observation w Pool.finishClose s advanced) refl }
whole-finish-observation w s eq | W.idle = case eq of λ ()
whole-finish-observation w s eq | W.shutdownSelected = case eq of λ ()
whole-finish-observation w s eq | W.stoppingTraced = case eq of λ ()
whole-finish-observation w s eq | W.stoppingWritten = case eq of λ ()
whole-finish-observation w s eq | W.groupClosing = case eq of λ ()
whole-finish-observation w s eq | W.draining = case eq of λ ()
whole-finish-observation w s eq | W.drainReady = case eq of λ ()
whole-finish-observation w s eq | W.stoppedTrace = case eq of λ ()
whole-finish-observation w s eq | W.stoppedTracing = case eq of λ ()
whole-finish-observation w s eq | W.monitorReturnedNormal = case eq of λ ()
whole-finish-observation w s eq | W.ownerAborting err = case eq of λ ()
whole-finish-observation w s eq | W.wholeClosed outcome = case eq of λ ()
whole-finish-observation w s eq | W.asyncFailureWritten err = case eq of λ ()
whole-finish-observation w s eq | W.asyncDeadTracing err = case eq of λ ()
whole-finish-observation w s eq | W.scopeDone outcome = case eq of λ ()
