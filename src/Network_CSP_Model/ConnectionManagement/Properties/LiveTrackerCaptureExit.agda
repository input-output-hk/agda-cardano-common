{-# OPTIONS --guardedness #-}

-- Exact descriptor agreement for every stored mux, exit and startup-fault row.
-- All covers traversal rows too, including rows shadowed by duplicate keys.
module ConnectionManagement.Properties.LiveTrackerCaptureExit where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (WorkerId; ErrorId)
open import ConnectionManagement.Store using (Store; lookup; put)
open import ConnectionManagement.Properties.Entries using (lookup-put)
open import ConnectionManagement.Properties.Stores using (lookup-put-other; lookup-head)
import ConnectionManagement.Rules.MuxEgress as EgressLayout
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.Properties.HandlerBirthEffects as Birth
import ConnectionManagement.MuxHandlerSupervision as MuxModel
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.OutboundRelease as OutboundRelease

import ConnectionManagement.MuxProtocolJobs as ProtocolModel
import ConnectionManagement.MuxHandlerExit as ExitModel
import ConnectionManagement.MuxGroupShutdown as GroupModel
import ConnectionManagement.Rules.MuxRuntime as WireMux
import ConnectionManagement.MuxStartupUnwind as UnwindModel
open import ConnectionManagement.Properties.LiveTrackerCapture public
open import ConnectionManagement.Properties.LiveTrackerCaptureLayers public
import ConnectionManagement.Properties.HandlerAuxBacking as Presence

import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.HandlerLifecycle as Life
module Exit (isBearerClosed : ErrorId → Bool) where
 private module W = ExitModel isBearerClosed using (Action; Frame; Plan; State; acknowledgeFinished; acknowledgeReleaseFinished; deliverReleaseMux; deliverReleaseTimeWait; releaseTarget; timeWaitTarget; releaseDelivery; releaseTimeWaitDelivery; base; beginExit; bodyExited; bufferScope; choose; choosePolicy; classifying; cleanup; cleanupComplete; cleanupException; cleanupFault; control; coordinator; currentCapture; delegateAllowed; deliverShutdownMux; deliverShutdownTimeWait; edit; effectiveResult; enact; enterFinalizer; errorTracing; exits; finalizing; finishCleanup; inherited; initial; local; machine; muxDelivery; nodeDelivery; nodeRethrow; noteCleanup; observeBufferException; observeBufferReturn; observeErrorTrace; observeNodeDelivery; peerRethrow; phase; physical; poolAt; publishAsyncResult; resultAvailable; resultReady; rethrow; run; sameCleanup; sameStart; countersClear; setShutdown; setSource; shared; shutdown; shutdownStep; source; step; timeWaitDelivery)
 private module G = GroupModel isBearerClosed using (abortOwner; asyncDeadTracing; asyncExit; asyncFailureWritten; drainReady; draining; failedExit; frameAt; groupClosing; idle; initial; monitorReturnedNormal; normalExit; ownerAborting; phase; protocolState; scopeDone; setPool; shutdownSelected; step; stoppedTrace; stoppedTracing; stoppingTraced; stoppingWritten; wholeClosed; wholeClosing)
 private module P = ProtocolModel using (hasWanton; enterProtocolBody; appendProtocolPayload; egressMuxer; module Pool; module U; base)
 private module U = P.U using (captured; frames)
 private module Pool = P.Pool using (cancelPending; closedPool; closing; joinPending; openPool; phase)
 private module Lower = Group isBearerClosed using (Valid; initialized-valid; step-preserves; direct-shutdown-same)
 view : W.State → Birth.Registry
 view = Birth.ExitLayer.view isBearerClosed
 Valid : W.State → Set
 Valid s = Lower.Valid (W.base s) × Covers (W.exits s) (view s)
 lower-valid : ∀ {s} → Valid s → Lower.Valid (W.base s)
 lower-valid = proj₁
 exits-present : ∀ {s} → Valid s → Covers (W.exits s) (view s)
 exits-present = proj₂
 frames-present : ∀ {s} → Valid s → Covers (U.frames (P.base (G.protocolState (W.base s)))) (view s)
 frames-present valid = proj₁ valid
 source-valid : ∀ c s → Valid s → Valid (W.setSource c s)
 source-valid c s valid = valid
 shutdown-valid : ∀ coordinator s → Valid s → Valid (W.setShutdown coordinator s)
 shutdown-valid coordinator s valid = valid
 local-valid : ∀ fs s → Covers fs (view s) → Valid s → Valid (record s { exits = fs })
 local-valid fs s cover valid = proj₁ valid , cover
 setPool-valid : ∀ w f p s → Ref w (P.U.captured f) (view s) → Valid s → Valid (record s { base = G.setPool w f p (W.base s) })
 setPool-valid w f p s present valid = Protocol.pool-valid w f p (G.protocolState (W.base s)) present (proj₁ valid) , proj₂ valid
 edit-covers : ∀ w f pc s → lookup w (W.exits s) ≡ just f → Valid s → Covers (W.edit w f pc s) (view s)
 edit-covers w f pc s found valid = covers-put w _ (W.exits s) (view s) (covers-at (proj₂ valid) w f found) (proj₂ valid)
 note-covers : ∀ w action s → Valid s → Covers (W.noteCleanup w action s) (view s)
 note-covers w action s valid with lookup w (W.exits s) in found | W.cleanupFault action
 ... | just f | just fault = covers-put w _ (W.exits s) (view s) (covers-at (proj₂ valid) w f found) (proj₂ valid)
 ... | nothing | _ = proj₂ valid
 ... | just f | nothing = proj₂ valid
 control-preserves : ∀ a s {t} → W.control a s ≡ just t → Valid s → Valid t
 control-preserves a s eq valid with Close.step (S.cm (W.shared s)) (λ w → W.resultReady w s) a (W.shutdown s)
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → shutdown-valid next s valid }
 data PlanSafe : W.Plan → W.State → Set where
  safe-local : ∀ {fs s} → Covers fs (view s) → PlanSafe (W.local fs) s
  safe-machine : ∀ {a fs s} → Covers fs (view s) → PlanSafe (W.machine a fs) s
  safe-inherited : ∀ {a s} → PlanSafe (W.inherited a) s
  safe-coordinator : ∀ {a s} → PlanSafe (W.coordinator a) s
  safe-muxDelivery : ∀ {w err s} → PlanSafe (W.muxDelivery w err) s
  safe-timeWaitDelivery : ∀ {w err s} → PlanSafe (W.timeWaitDelivery w err) s
  safe-releaseDelivery : ∀ {caller worker err s} → PlanSafe (W.releaseDelivery caller worker err) s
  safe-releaseTimeWaitDelivery : ∀ {caller worker err s} → PlanSafe (W.releaseTimeWaitDelivery caller worker err) s
 enact-preserves : ∀ p s {t} → W.enact p s ≡ just t → Valid s → PlanSafe p s → Valid t
 enact-preserves (W.local fs) s eq valid (safe-local cover) = case just-injective eq of λ { refl → local-valid fs s cover valid }
 enact-preserves (W.machine a fs) s eq valid (safe-machine cover) with O.advance a (W.source s)
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → local-valid fs (W.setSource c s) cover valid }
 enact-preserves (W.inherited a) s eq valid safe-inherited with G.step a (W.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just g = case just-injective eq of λ { refl → Lower.step-preserves a (W.base s) actual (proj₁ valid) ,
   covers-retained {rows = W.exits s} {before = view s} {after = Birth.GroupLayer.view isBearerClosed g}
     (change-retains (Birth.GroupLayer.change isBearerClosed a (W.base s) actual)) (proj₂ valid) }
 enact-preserves (W.coordinator a) s eq valid safe-coordinator = control-preserves a s eq valid
 enact-preserves (W.muxDelivery w err) s eq valid safe-muxDelivery with G.step (G.abortOwner w err) (W.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just g = control-preserves Close.acknowledgeDelivery (record s { base = g }) eq
   (Lower.step-preserves (G.abortOwner w err) (W.base s) actual (proj₁ valid) ,
    covers-retained {rows = W.exits s} {before = view s} {after = Birth.GroupLayer.view isBearerClosed g}
     (change-retains (Birth.GroupLayer.change isBearerClosed (G.abortOwner w err) (W.base s) actual)) (proj₂ valid))
 enact-preserves (W.timeWaitDelivery w err) s eq valid safe-timeWaitDelivery with O.advance
   (O.inbound (Machine.cleanupStep w (Cleanup.interruptTimeWait err))) (W.source s)
 ... | nothing = case eq of λ ()
 ... | just c = control-preserves Close.acknowledgeDelivery
   (record (W.setSource c s) { exits = W.noteCleanup w (Cleanup.interruptTimeWait err) s }) eq
   (proj₁ valid , note-covers w (Cleanup.interruptTimeWait err) s valid)
 enact-preserves (W.releaseDelivery caller worker err) s eq valid safe-releaseDelivery with G.step (G.abortOwner worker err) (W.base s) in aborted
 ... | nothing = case eq of λ ()
 ... | just g with O.advance (O.release caller (OutboundRelease.cancellationDelivered worker)) (W.source (record s { base = g })) in acknowledged
 ...   | nothing = case eq of λ ()
 ...   | just c = case just-injective eq of λ { refl → source-valid c (record s { base = g })
   (Lower.step-preserves (G.abortOwner worker err) (W.base s) aborted (proj₁ valid) ,
    covers-retained {rows = W.exits s} {before = view s} {after = Birth.GroupLayer.view isBearerClosed g}
      (change-retains (Birth.GroupLayer.change isBearerClosed (G.abortOwner worker err) (W.base s) aborted)) (proj₂ valid)) }
 enact-preserves (W.releaseTimeWaitDelivery caller worker err) s eq valid safe-releaseTimeWaitDelivery with O.advance
   (O.inbound (Machine.cleanupStep worker (Cleanup.interruptTimeWait err))) (W.source s)
 ... | nothing = case eq of λ ()
 ... | just c with O.advance (O.release caller (OutboundRelease.cancellationDelivered worker)) c
 ...   | nothing = case eq of λ ()
 ...   | just c′ = case just-injective eq of λ { refl → source-valid c′
   (record (W.setSource c s) { exits = W.noteCleanup worker (Cleanup.interruptTimeWait err) s })
   (proj₁ valid , note-covers worker (Cleanup.interruptTimeWait err) s valid) }
 choose-safe : ∀ a s {p} → W.choose a s ≡ just p → Valid s → PlanSafe p s
 choose-safe (W.run a) s eq valid with W.delegateAllowed a
 ... | true = case just-injective eq of λ { refl → safe-inherited }
 ... | false = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid with lookup w (W.exits s) | lookup w (U.frames (P.base (G.protocolState (W.base s)))) in found |
   G.phase (G.frameAt w (W.base s)) | Pool.phase (W.poolAt w s)
 ... | nothing | just f | G.scopeDone outcome | Pool.closedPool with lookup w (S.handlers (W.shared s))
 ...   | just h with W.sameStart (U.captured f) h ∧ W.countersClear f s
 ...     | true = case just-injective eq of λ { refl → safe-local (covers-put w _ (W.exits s) (view s) (covers-at (frames-present {s = s} valid) w f found) (proj₂ valid)) }
 ...     | false = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.scopeDone outcome | Pool.closedPool | nothing = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | just old | _ | _ | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | nothing | _ | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.idle | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.shutdownSelected | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.stoppingTraced | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.stoppingWritten | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.groupClosing | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.draining | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.drainReady | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.stoppedTrace | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.stoppedTracing | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.monitorReturnedNormal | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.ownerAborting err | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.wholeClosing outcome | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.wholeClosed outcome | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.asyncFailureWritten err | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.asyncDeadTracing err | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.scopeDone outcome | Pool.openPool = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.scopeDone outcome | Pool.closing = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.scopeDone outcome | Pool.cancelPending j = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.scopeDone outcome | Pool.joinPending j = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid with lookup w (W.exits s) in found
 ... | just f with W.phase f
 ...   | W.bufferScope outcome = case just-injective eq of λ { refl → safe-local (edit-covers w f _ s found valid) }
 choose-safe (W.observeBufferReturn w) s eq valid | just f | W.classifying otherError = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid | just f | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid | just f | W.peerRethrow otherError = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid | just f | W.nodeDelivery otherError = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid | just f | W.nodeRethrow otherError = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid | just f | W.bodyExited otherResult = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid | just f | W.finalizing otherResult = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid | just f | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid | just f | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid | nothing = case eq of λ ()
 choose-safe (W.observeBufferException w G.normalExit) s eq valid = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid with lookup w (W.exits s) in found
 ... | just f with W.phase f
 ...   | W.bufferScope outcome = case just-injective eq of λ { refl → safe-local (edit-covers w f _ s found valid) }
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | just f | W.classifying otherError = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | just f | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | just f | W.peerRethrow otherError = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | just f | W.nodeDelivery otherError = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | just f | W.nodeRethrow otherError = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | just f | W.bodyExited otherResult = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | just f | W.finalizing otherResult = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | just f | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | just f | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | nothing = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid with lookup w (W.exits s) in found
 ... | just f with W.phase f
 ...   | W.bufferScope outcome = case just-injective eq of λ { refl → safe-local (edit-covers w f _ s found valid) }
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | just f | W.classifying otherError = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | just f | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | just f | W.peerRethrow otherError = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | just f | W.nodeDelivery otherError = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | just f | W.nodeRethrow otherError = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | just f | W.bodyExited otherResult = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | just f | W.finalizing otherResult = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | just f | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | just f | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | nothing = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid with lookup w (W.exits s) in found
 ... | just f with W.phase f
 ...   | W.classifying err = case just-injective eq of λ { refl → safe-local (edit-covers w f _ s found valid) }
 choose-safe (W.choosePolicy w policy) s eq valid | just f | W.bufferScope otherOutcome = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid | just f | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid | just f | W.peerRethrow otherError = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid | just f | W.nodeDelivery otherError = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid | just f | W.nodeRethrow otherError = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid | just f | W.bodyExited otherResult = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid | just f | W.finalizing otherResult = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid | just f | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid | just f | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid | nothing = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid with lookup w (W.exits s) in found
 ... | just f with W.phase f
 ...   | W.errorTracing err Life.shutdownPeer = case just-injective eq of λ { refl → safe-local (edit-covers w f _ s found valid) }
 ...   | W.errorTracing err Life.shutdownNode = case just-injective eq of λ { refl → safe-local (edit-covers w f _ s found valid) }
 choose-safe (W.observeErrorTrace w) s eq valid | just f | W.bufferScope otherOutcome = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid | just f | W.classifying otherError = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid | just f | W.peerRethrow otherError = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid | just f | W.nodeDelivery otherError = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid | just f | W.nodeRethrow otherError = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid | just f | W.bodyExited otherResult = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid | just f | W.finalizing otherResult = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid | just f | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid | just f | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid | nothing = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid with lookup w (W.exits s) in found
 ... | just f with W.phase f
 ...   | W.nodeDelivery err = case just-injective eq of λ { refl → safe-local (edit-covers w f _ s found valid) }
 choose-safe (W.observeNodeDelivery w) s eq valid | just f | W.bufferScope otherOutcome = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid | just f | W.classifying otherError = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid | just f | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid | just f | W.peerRethrow otherError = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid | just f | W.nodeRethrow otherError = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid | just f | W.bodyExited otherResult = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid | just f | W.finalizing otherResult = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid | just f | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid | just f | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid | nothing = case eq of λ ()
 choose-safe (W.rethrow w) s eq valid with lookup w (W.exits s) in found
 ... | just f with W.phase f
 ...   | W.peerRethrow err = case just-injective eq of λ { refl → safe-local (edit-covers w f _ s found valid) }
 ...   | W.nodeRethrow err = case just-injective eq of λ { refl → safe-local (edit-covers w f _ s found valid) }
 choose-safe (W.rethrow w) s eq valid | just f | W.bufferScope otherOutcome = case eq of λ ()
 choose-safe (W.rethrow w) s eq valid | just f | W.classifying otherError = case eq of λ ()
 choose-safe (W.rethrow w) s eq valid | just f | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-safe (W.rethrow w) s eq valid | just f | W.nodeDelivery otherError = case eq of λ ()
 choose-safe (W.rethrow w) s eq valid | just f | W.bodyExited otherResult = case eq of λ ()
 choose-safe (W.rethrow w) s eq valid | just f | W.finalizing otherResult = case eq of λ ()
 choose-safe (W.rethrow w) s eq valid | just f | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-safe (W.rethrow w) s eq valid | just f | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-safe (W.rethrow w) s eq valid | nothing = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid with lookup w (W.exits s) in found
 ... | just f with W.phase f | W.currentCapture w f s
 ...   | W.bodyExited result | true = case just-injective eq of λ { refl → safe-machine (edit-covers w f _ s found valid) }
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.bufferScope otherOutcome | _ = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.classifying otherError | _ = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.errorTracing otherError otherPolicy | _ = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.peerRethrow otherError | _ = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.nodeDelivery otherError | _ = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.nodeRethrow otherError | _ = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.finalizing otherResult | _ = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.cleanupComplete otherResult otherCleanup | _ = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.resultAvailable otherResult otherCleanup | _ = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.bodyExited otherResult | false = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | nothing = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid with lookup w (W.exits s)
 ... | just f with W.phase f | W.currentCapture w f s
 ...   | W.finalizing result | true = case just-injective eq of λ { refl → safe-machine (note-covers w action s valid) }
 choose-safe (W.cleanup w action) s eq valid | just f | W.bufferScope otherOutcome | _ = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | just f | W.classifying otherError | _ = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | just f | W.errorTracing otherError otherPolicy | _ = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | just f | W.peerRethrow otherError | _ = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | just f | W.nodeDelivery otherError | _ = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | just f | W.nodeRethrow otherError | _ = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | just f | W.bodyExited otherResult | _ = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | just f | W.cleanupComplete otherResult otherCleanup | _ = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | just f | W.resultAvailable otherResult otherCleanup | _ = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | just f | W.finalizing otherResult | false = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | nothing = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid with lookup w (W.exits s) in found | lookup w (S.cleanups (W.shared s))
 ... | just f | just (S.cleanupDone outcome) with W.phase f
 ...   | W.finalizing result with W.effectiveResult result outcome (W.cleanupException f)
 ...     | just effective = case just-injective eq of λ { refl → safe-local (edit-covers w f _ s found valid) }
 ...     | nothing = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupDone outcome) | W.bufferScope otherOutcome = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupDone outcome) | W.classifying otherError = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupDone outcome) | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupDone outcome) | W.peerRethrow otherError = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupDone outcome) | W.nodeDelivery otherError = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupDone outcome) | W.nodeRethrow otherError = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupDone outcome) | W.bodyExited otherResult = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupDone outcome) | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupDone outcome) | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | nothing | _ = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | nothing = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupAcquire) = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupSelect savedLease) = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupClose savedLease map tail) = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupPublish savedLease map tail) = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupRestore savedLease error) = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupWaiting captured) = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupFinalize captured outcome) = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupCount outcome) = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid with lookup w (W.exits s) in found | lookup w (S.cleanups (W.shared s))
 ... | just f | just (S.cleanupDone outcome) with W.phase f
 ...   | W.cleanupComplete result observed with W.sameCleanup observed outcome
 ...     | true = case just-injective eq of λ { refl → safe-local (edit-covers w f _ s found valid) }
 ...     | false = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupDone outcome) | W.bufferScope otherOutcome = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupDone outcome) | W.classifying otherError = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupDone outcome) | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupDone outcome) | W.peerRethrow otherError = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupDone outcome) | W.nodeDelivery otherError = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupDone outcome) | W.nodeRethrow otherError = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupDone outcome) | W.bodyExited otherResult = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupDone outcome) | W.finalizing otherResult = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupDone outcome) | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | nothing | _ = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | nothing = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupAcquire) = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupSelect savedLease) = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupClose savedLease map tail) = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupPublish savedLease map tail) = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupRestore savedLease error) = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupWaiting captured) = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupFinalize captured outcome) = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupCount outcome) = case eq of λ ()
 choose-safe (W.shutdownStep Close.acknowledgeDelivery) s eq valid = case eq of λ ()
 choose-safe (W.shutdownStep Close.captureSnapshot) s eq valid = case just-injective eq of λ { refl → safe-coordinator }
 choose-safe (W.shutdownStep Close.readEntry) s eq valid = case just-injective eq of λ { refl → safe-coordinator }
 choose-safe (W.shutdownStep Close.requestCancellation) s eq valid = case just-injective eq of λ { refl → safe-coordinator }
 choose-safe (W.shutdownStep Close.finishTraversal) s eq valid = case just-injective eq of λ { refl → safe-coordinator }
 choose-safe (W.shutdownStep Close.finishClose) s eq valid = case just-injective eq of λ { refl → safe-coordinator }
 choose-safe (W.deliverShutdownMux err) s eq valid with Close.phase (W.shutdown s)
 ... | Close.awaitDelivery e w = case just-injective eq of λ { refl → safe-muxDelivery }
 choose-safe (W.deliverShutdownMux err) s eq valid | Close.initial = case eq of λ ()
 choose-safe (W.deliverShutdownMux err) s eq valid | Close.reading = case eq of λ ()
 choose-safe (W.deliverShutdownMux err) s eq valid | Close.sendReady e w = case eq of λ ()
 choose-safe (W.deliverShutdownMux err) s eq valid | Close.awaitResults = case eq of λ ()
 choose-safe (W.deliverShutdownMux err) s eq valid | Close.closed = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid with Close.phase (W.shutdown s)
 ... | Close.awaitDelivery e w with lookup w (W.exits s) | lookup w (S.cleanups (W.shared s))
 ...   | just f | just (S.cleanupWaiting h) with W.phase f | W.currentCapture w f s
 ...     | W.finalizing result | true = case just-injective eq of λ { refl → safe-timeWaitDelivery }
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.bufferScope otherOutcome | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.classifying otherError | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.errorTracing otherError otherPolicy | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.peerRethrow otherError | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.nodeDelivery otherError | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.nodeRethrow otherError | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.bodyExited otherResult | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.cleanupComplete otherResult otherCleanup | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.resultAvailable otherResult otherCleanup | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.finalizing result | false = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | nothing | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | nothing = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupAcquire) = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupSelect savedLease) = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupClose savedLease map tail) = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupPublish savedLease map tail) = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupRestore savedLease error) = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupFinalize captured outcome) = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupCount outcome) = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupDone outcome) = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.initial = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.reading = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.sendReady e w = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitResults = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.closed = case eq of λ ()
 choose-safe W.acknowledgeFinished s eq valid with Close.phase (W.shutdown s)
 ... | Close.awaitDelivery e w with W.resultReady w s
 ...   | true = case just-injective eq of λ { refl → safe-coordinator }
 ...   | false = case eq of λ ()
 choose-safe W.acknowledgeFinished s eq valid | Close.initial = case eq of λ ()
 choose-safe W.acknowledgeFinished s eq valid | Close.reading = case eq of λ ()
 choose-safe W.acknowledgeFinished s eq valid | Close.sendReady e w = case eq of λ ()
 choose-safe W.acknowledgeFinished s eq valid | Close.awaitResults = case eq of λ ()
 choose-safe W.acknowledgeFinished s eq valid | Close.closed = case eq of λ ()

 choose-safe (W.deliverReleaseMux caller err) s eq valid with W.releaseTarget caller s
 ... | nothing = case eq of λ ()
 ... | just worker = case just-injective eq of λ { refl → safe-releaseDelivery }
 choose-safe (W.deliverReleaseTimeWait caller err) s eq valid with W.timeWaitTarget caller s
 ... | nothing = case eq of λ ()
 ... | just worker = case just-injective eq of λ { refl → safe-releaseTimeWaitDelivery }
 choose-safe (W.acknowledgeReleaseFinished caller) s eq valid with W.releaseTarget caller s
 ... | nothing = case eq of λ ()
 ... | just worker with W.resultReady worker s
 ...   | false = case eq of λ ()
 ...   | true = case just-injective eq of λ { refl → safe-machine (proj₂ valid) }

 step-preserves : ∀ a s {t} → W.step a s ≡ just t → Valid s → Valid t
 step-preserves a s eq valid with W.choose a s in chosen
 ... | nothing = case eq of λ ()
 ... | just p = enact-preserves p s eq valid (choose-safe a s chosen valid)
 initialized-valid : ∀ c {s} → W.initial c ≡ just s → Valid s
 initialized-valid c eq with G.initial c in initialized
 ... | nothing = case eq of λ ()
 ... | just g = case just-injective eq of λ { refl → Lower.initialized-valid c initialized , covers-empty {W.Frame} (Birth.GroupLayer.view isBearerClosed g) }
 resultReady-present : ∀ {s w} → Valid s → W.resultReady w s ≡ true → Present w (view s)
 resultReady-present {s} {w} valid ready with lookup w (W.exits s) in found
 ... | just f = ExitModel.captured f , covers-at (proj₂ valid) w f found
 ... | nothing with lookup w (U.frames (P.base (G.protocolState (W.base s))))
 ...   | just f = case ready of λ ()
 ...   | nothing with lookup w (B.threads (W.physical s)) in thread
 ...     | just physical = H.captured physical , physical-present w (W.physical s) physical thread
 ...     | nothing = case ready of λ ()
 open Presence.Exit isBearerClosed public using (IsPlain; PlainPlan; choose-plain; plain-shutdown-same)

import ConnectionManagement.MuxExitCancellation as CancellationModel
module Cancellation (isBearerClosed : ErrorId → Bool) where
 private module X = CancellationModel isBearerClosed using (State; deliver; deliverShutdown; observeCancellation; observeErrorTraceException; run; shutdownDelivery; step; target; traceThrew)
 private module W = ExitModel isBearerClosed using (bodyExited; bufferScope; classifying; cleanupComplete; edit; errorTracing; exits; finalizing; nodeDelivery; nodeRethrow; peerRethrow; phase; resultAvailable; shutdown; syncException)
 private module Lower = Exit isBearerClosed using (Valid; control-preserves; edit-covers; local-valid; step-preserves)
 Valid : X.State → Set
 Valid = Lower.Valid
 deliver-preserves : ∀ window w err s {t} → X.deliver window w err s ≡ just t → Valid s → Valid t
 deliver-preserves window w err s eq valid with lookup w (W.exits s) in found
 ... | nothing = case eq of λ ()
 ... | just f with X.target window err (W.phase f)
 ...   | nothing = case eq of λ ()
 ...   | just pc = case just-injective eq of λ { refl → Lower.local-valid (W.edit w f pc s) s (Lower.edit-covers w f pc s found valid) valid }
 trace-preserves : ∀ w err s {t} → X.traceThrew w err s ≡ just t → Valid s → Valid t
 trace-preserves w err s eq valid with lookup w (W.exits s) in found
 ... | nothing = case eq of λ ()
 ... | just f with W.phase f
 ...   | W.errorTracing original policy = case just-injective eq of λ { refl → Lower.local-valid (W.edit w f (W.bodyExited (W.syncException err)) s) s (Lower.edit-covers w f (W.bodyExited (W.syncException err)) s found valid) valid }
 ...   | W.bufferScope outcome = case eq of λ ()
 ...   | W.classifying original = case eq of λ ()
 ...   | W.peerRethrow original = case eq of λ ()
 ...   | W.nodeDelivery original = case eq of λ ()
 ...   | W.nodeRethrow original = case eq of λ ()
 ...   | W.bodyExited result = case eq of λ ()
 ...   | W.finalizing result = case eq of λ ()
 ...   | W.cleanupComplete result outcome = case eq of λ ()
 ...   | W.resultAvailable result outcome = case eq of λ ()
 shutdown-preserves : ∀ window err s {t} → X.shutdownDelivery window err s ≡ just t → Valid s → Valid t
 shutdown-preserves window err s eq valid with Close.phase (W.shutdown s)
 ... | Close.awaitDelivery e w with X.deliver window w err s in delivered
 ...   | nothing = case eq of λ ()
 ...   | just next = Lower.control-preserves Close.acknowledgeDelivery next eq (deliver-preserves window w err s delivered valid)
 shutdown-preserves window err s eq valid | Close.initial = case eq of λ ()
 shutdown-preserves window err s eq valid | Close.reading = case eq of λ ()
 shutdown-preserves window err s eq valid | Close.sendReady e w = case eq of λ ()
 shutdown-preserves window err s eq valid | Close.awaitResults = case eq of λ ()
 shutdown-preserves window err s eq valid | Close.closed = case eq of λ ()
 step-preserves : ∀ a s {t} → X.step a s ≡ just t → Valid s → Valid t
 step-preserves (X.run a) = Lower.step-preserves a
 step-preserves (X.observeCancellation window w err) = deliver-preserves window w err
 step-preserves (X.deliverShutdown window err) = shutdown-preserves window err
 step-preserves (X.observeErrorTraceException w err) = trace-preserves w err

import ConnectionManagement.Properties.MuxStartupUnwind as UnwindProperties
module Unwind (isBearerClosed : ErrorId → Bool) where
 private module R = UnwindModel isBearerClosed using (Action; Fault; Plan; State; acknowledge; allowed; async; asyncDead; asyncStatus; awaitingClose; base; beginClose; beginDead; cancellationPlan; choose; closing; commitDead; continueSync; deadThrowPoint; deliverCancel; deliverShutdown; deliveryControl; deliveryRoute; enact; faults; finishClose; finishDead; handedOff; handoff; inherited; initial; join; local; machine; mux; observeCancellation; observeDeadTraceException; observeFailure; outcome; owner; phase; pool; poolAt; poolClosed; protocols; readyBody; readyBuffer; requestCancel; run; sameClose; sampleDead; setPhase; setPool; setSource; siteControl; siteRoute; source; start; step; sync; transfer; withPool; writeAsyncFailure)
 private module W = ExitModel isBearerClosed using (base; control; exits; setShutdown; shutdown)
 private module X = CancellationModel isBearerClosed using (initial; step)
 private module G = GroupModel isBearerClosed using (module M; protocolState; wholeDeliverable)
 private module P = ProtocolModel using (hasWanton; enterProtocolBody; appendProtocolPayload; egressMuxer; module Pool; module U; base; muxAt)
 private module U = P.U using (captured; frames)
 private module Pool = P.Pool using (beginClose; cancelPending; closedPool; closing; finishClose; join; joinPending; openPool; phase; requestCancel; step)
 private module M = G.M using (failed; finishMatches)
 private module F = UnwindProperties isBearerClosed using (Selection; selection-observation)
 private module Lower = Exit isBearerClosed using (Valid; control-preserves; exits-present; frames-present; initialized-valid; local-valid; setPool-valid; shutdown-valid)
 private module Cancel = Cancellation isBearerClosed using (step-preserves)
 view : R.State → Birth.Registry
 view = Birth.UnwindLayer.view isBearerClosed
 Valid : R.State → Set
 Valid s = Lower.Valid (R.base s) × Covers (R.faults s) (view s)
 lower-valid : ∀ {s} → Valid s → Lower.Valid (R.base s)
 lower-valid = proj₁
 frames-present : ∀ {s} → Valid s → Covers (U.frames (P.base (G.protocolState (W.base (R.base s))))) (view s)
 frames-present {s} valid = Lower.frames-present {s = R.base s} (proj₁ valid)
 exits-present : ∀ {s} → Valid s → Covers (W.exits (R.base s)) (view s)
 exits-present {s} valid = Lower.exits-present {s = R.base s} (proj₁ valid)
 faults-present : ∀ {s} → Valid s → Covers (R.faults s) (view s)
 faults-present = proj₂
 source-valid : ∀ c s → Valid s → Valid (R.setSource c s)
 source-valid c s valid = valid
 shutdown-valid : ∀ coordinator s → Valid s → Valid (record s { base = W.setShutdown coordinator (R.base s) })
 shutdown-valid coordinator s valid = Lower.shutdown-valid coordinator (R.base s) (proj₁ valid) , proj₂ valid
 local-valid : ∀ fs s → Covers fs (view s) → Valid s → Valid (record s { faults = fs })
 local-valid fs s cover valid = proj₁ valid , cover
 setPool-valid : ∀ w f p s → Ref w (P.U.captured f) (view s) → Valid s → Valid (R.setPool w f p s)
 setPool-valid w f p s present valid = Lower.setPool-valid w f p (R.base s) present (proj₁ valid) , proj₂ valid
 phase-covers : ∀ w f pc s → lookup w (R.faults s) ≡ just f → Valid s → Covers (R.setPhase w f pc s) (view s)
 phase-covers w f pc s found valid = covers-put w _ (R.faults s) (view s) (covers-at (proj₂ valid) w f found) (proj₂ valid)
 data PlanSafe : R.Plan → R.State → Set where
  safe-local : ∀ {fs s} → Covers fs (view s) → PlanSafe (R.local fs) s
  safe-machine : ∀ {a fs s} → Covers fs (view s) → PlanSafe (R.machine a fs) s
  safe-pool : ∀ {w u a fs s} → Ref w (P.U.captured u) (view s) → Covers fs (view s) → PlanSafe (R.pool w u a fs) s
  safe-transfer : ∀ {w f fs s} → Ref w (ExitModel.captured f) (view s) → Covers fs (view s) → PlanSafe (R.transfer w f fs) s
  safe-inherited : ∀ {a s} → PlanSafe (R.inherited a) s
  safe-acknowledge : ∀ {p s} → PlanSafe p s → PlanSafe (R.acknowledge p) s
 enact-preserves : ∀ p s {t} → R.enact p s ≡ just t → Valid s → PlanSafe p s → Valid t
 enact-preserves (R.local fs) s eq valid (safe-local cover) = case just-injective eq of λ { refl → local-valid fs s cover valid }
 enact-preserves (R.machine a fs) s eq valid (safe-machine cover) with O.advance a (R.source s)
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → local-valid fs (R.setSource c s) cover valid }
 enact-preserves (R.pool w u a fs) s eq valid (safe-pool present cover) with Pool.step a (R.poolAt w s)
 ... | nothing = case eq of λ ()
 ... | just p = case just-injective eq of λ { refl → local-valid fs (R.setPool w u p s) cover (setPool-valid w u p s present valid) }
 enact-preserves (R.transfer w f fs) s eq valid (safe-transfer present cover) = case just-injective eq of λ { refl →
   Lower.local-valid (put w f (W.exits (R.base s))) (R.base s)
     (covers-put w f (W.exits (R.base s)) (view s) present (exits-present {s = s} valid)) (proj₁ valid) , cover }
 enact-preserves (R.inherited a) s eq valid safe-inherited with X.step a (R.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just x = case just-injective eq of λ { refl → Cancel.step-preserves a (R.base s) actual (proj₁ valid) ,
   covers-retained {rows = R.faults s} {before = view s} {after = Birth.CancellationLayer.view isBearerClosed x}
     (change-retains (Birth.CancellationLayer.change isBearerClosed a (R.base s) actual)) (proj₂ valid) }
 enact-preserves (R.acknowledge p) s eq valid (safe-acknowledge safe) with R.enact p s in actual
 ... | nothing = case eq of λ ()
 ... | just next with W.control Close.acknowledgeDelivery (R.base next) in acknowledged
 ...   | nothing = case eq of λ ()
 ...   | just w = case just-injective eq of λ { refl → Lower.control-preserves Close.acknowledgeDelivery (R.base next) acknowledged (proj₁ following) ,
   subst (Covers (R.faults next))
     (sym (Birth.ExitLayer.CIPaths.retention (Birth.ExitLayer.ci-control-projects isBearerClosed Close.acknowledgeDelivery (R.base next) acknowledged)))
     (proj₂ following) }
   where following = enact-preserves p s actual valid safe
 start-safe : ∀ w result route s {p} → R.start w result route s ≡ just p → Valid s → PlanSafe p s
 start-safe w result route s chosen valid with F.selection-observation w result route s chosen
 ... | selected rewrite F.Selection.plan-shape selected = safe-local
   (covers-put w _ (R.faults s) (view s) (covers-at (frames-present {s = s} valid) w _ (F.Selection.owner-found selected)) (proj₂ valid))
 IsDirect : R.Action → Set
 IsDirect (R.run a) = ⊥
 IsDirect (R.deliverShutdown site err) = ⊥
 IsDirect _ = ⊤
 NonAck : R.Plan → Set
 NonAck (R.acknowledge p) = ⊥
 NonAck _ = ⊤
 ChosenSafe : R.Action → R.Plan → R.State → Set
 ChosenSafe a p s = PlanSafe p s × (IsDirect a → NonAck p)
 start-nonack : ∀ w result route s {p} → R.start w result route s ≡ just p → NonAck p
 start-nonack w result route s chosen with F.selection-observation w result route s chosen
 ... | selected rewrite F.Selection.plan-shape selected = tt
 cancellation-safe : ∀ w site err s {p} → R.cancellationPlan w site err s ≡ just p → Valid s → PlanSafe p s × NonAck p
 cancellation-safe w site err s eq valid with R.deliveryControl w site s
 ... | false = case eq of λ ()
 ... | true = start-safe w (R.async err) (λ f m → R.deliveryRoute site f m) s eq valid ,
   start-nonack w (R.async err) (λ f m → R.deliveryRoute site f m) s eq
 pool-safe : ∀ w before action after s {p} → R.withPool w before action after s ≡ just p → Valid s → PlanSafe p s × NonAck p
 pool-safe w before action after s eq valid with lookup w (R.faults s) in found | R.owner w s in owner
 ... | just f | just u with R.sameClose before (R.phase f)
 ...   | true = case just-injective eq of λ { refl → safe-pool (covers-at (frames-present {s = s} valid) w u owner) (phase-covers w f after s found valid) , tt }
 ...   | false = case eq of λ ()
 pool-safe w before action after s eq valid | nothing | nothing = case eq of λ ()
 pool-safe w before action after s eq valid | nothing | just u = case eq of λ ()
 pool-safe w before action after s eq valid | just f | nothing = case eq of λ ()
 chosen-safe : ∀ a s {p} → R.choose a s ≡ just p → Valid s → ChosenSafe a p s
 chosen-safe (R.run a) s eq valid with R.allowed a s
 ... | true = case just-injective eq of λ { refl → safe-inherited , λ () }
 ... | false = case eq of λ ()
 chosen-safe (R.observeFailure w site err) s eq valid with R.siteControl w site s
 ... | true = start-safe w (R.sync err) (λ f m → R.siteRoute w site f m s) s eq valid ,
   (λ _ → start-nonack w (R.sync err) (λ f m → R.siteRoute w site f m s) s eq)
 ... | false = case eq of λ ()
 chosen-safe (R.observeCancellation w site err) s eq valid with cancellation-safe w site err s eq valid
 ... | safe , plain = safe , (λ _ → plain)
 chosen-safe (R.deliverShutdown site err) s eq valid with Close.phase (W.shutdown (R.base s))
 ... | Close.awaitDelivery e w with R.cancellationPlan w site err s in cancelled
 ...   | just p = case just-injective eq of λ { refl → safe-acknowledge (proj₁ (cancellation-safe w site err s cancelled valid)) , λ () }
 ...   | nothing = case eq of λ ()
 chosen-safe (R.deliverShutdown site err) s eq valid | Close.initial = case eq of λ ()
 chosen-safe (R.deliverShutdown site err) s eq valid | Close.reading = case eq of λ ()
 chosen-safe (R.deliverShutdown site err) s eq valid | Close.sendReady e w = case eq of λ ()
 chosen-safe (R.deliverShutdown site err) s eq valid | Close.awaitResults = case eq of λ ()
 chosen-safe (R.deliverShutdown site err) s eq valid | Close.closed = case eq of λ ()
 chosen-safe (R.beginClose w order) s eq valid with pool-safe w R.awaitingClose (Pool.beginClose order) R.closing s eq valid
 ... | safe , plain = safe , (λ _ → plain)
 chosen-safe (R.requestCancel w) s eq valid with pool-safe w R.closing Pool.requestCancel R.closing s eq valid
 ... | safe , plain = safe , (λ _ → plain)
 chosen-safe (R.join w) s eq valid with pool-safe w R.closing Pool.join R.closing s eq valid
 ... | safe , plain = safe , (λ _ → plain)
 chosen-safe (R.finishClose w) s eq valid with pool-safe w R.closing Pool.finishClose R.poolClosed s eq valid
 ... | safe , plain = safe , (λ _ → plain)
 chosen-safe (R.deliverCancel w) s eq valid with lookup w (R.faults s) | R.owner w s in owner | Pool.phase (R.poolAt w s)
 ... | just f | just u | Pool.cancelPending j with R.phase f | G.wholeDeliverable w j u (W.base (R.base s))
 ...   | R.closing | true = case just-injective eq of λ { refl → safe-pool (covers-at (frames-present {s = s} valid) w u owner) (proj₂ valid) , λ _ → tt }
 ...   | R.readyBody | _ = case eq of λ ()
 ...   | R.readyBuffer | _ = case eq of λ ()
 ...   | R.awaitingClose | _ = case eq of λ ()
 ...   | R.poolClosed | _ = case eq of λ ()
 ...   | R.asyncStatus | _ = case eq of λ ()
 ...   | R.asyncDead | _ = case eq of λ ()
 ...   | R.handedOff | _ = case eq of λ ()
 ...   | R.closing | false = case eq of λ ()
 chosen-safe (R.deliverCancel w) s eq valid | nothing | _ | _ = case eq of λ ()
 chosen-safe (R.deliverCancel w) s eq valid | just f | nothing | _ = case eq of λ ()
 chosen-safe (R.deliverCancel w) s eq valid | just f | just u | Pool.openPool = case eq of λ ()
 chosen-safe (R.deliverCancel w) s eq valid | just f | just u | Pool.closing = case eq of λ ()
 chosen-safe (R.deliverCancel w) s eq valid | just f | just u | Pool.joinPending j = case eq of λ ()
 chosen-safe (R.deliverCancel w) s eq valid | just f | just u | Pool.closedPool = case eq of λ ()

 chosen-safe (R.continueSync w) s eq valid with lookup w (R.faults s) in found | Pool.phase (R.poolAt w s)
 ... | just f | Pool.closedPool with R.phase f | R.outcome f
 ...   | R.poolClosed | R.sync err = case just-injective eq of λ { refl → safe-local (phase-covers w f R.readyBuffer s found valid) , λ _ → tt }
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.poolClosed | R.async err = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.readyBody | _ = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.readyBuffer | _ = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.awaitingClose | _ = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.closing | _ = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.asyncStatus | _ = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.asyncDead | _ = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.handedOff | _ = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.openPool = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closing = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.cancelPending j = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.joinPending j = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | nothing | _ = case eq of λ ()

 chosen-safe (R.writeAsyncFailure w) s eq valid with lookup w (R.faults s) in found | Pool.phase (R.poolAt w s)
 ... | just f | Pool.closedPool with R.phase f | R.outcome f
 ...   | R.poolClosed | R.async err = case just-injective eq of λ { refl → safe-machine (phase-covers w f R.asyncStatus s found valid) , λ _ → tt }
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.poolClosed | R.sync err = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.readyBody | _ = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.readyBuffer | _ = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.awaitingClose | _ = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.closing | _ = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.asyncStatus | _ = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.asyncDead | _ = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.handedOff | _ = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.openPool = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closing = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.cancelPending j = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.joinPending j = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | nothing | _ = case eq of λ ()

 chosen-safe (R.beginDead w) s eq valid with lookup w (R.faults s) in found
 ... | just f with R.phase f
 ...   | R.asyncStatus = case just-injective eq of λ { refl → safe-machine (phase-covers w f R.asyncDead s found valid) , λ _ → tt }
 chosen-safe (R.beginDead w) s eq valid | just f | R.readyBody = case eq of λ ()
 chosen-safe (R.beginDead w) s eq valid | just f | R.readyBuffer = case eq of λ ()
 chosen-safe (R.beginDead w) s eq valid | just f | R.awaitingClose = case eq of λ ()
 chosen-safe (R.beginDead w) s eq valid | just f | R.closing = case eq of λ ()
 chosen-safe (R.beginDead w) s eq valid | just f | R.poolClosed = case eq of λ ()
 chosen-safe (R.beginDead w) s eq valid | just f | R.asyncDead = case eq of λ ()
 chosen-safe (R.beginDead w) s eq valid | just f | R.handedOff = case eq of λ ()
 chosen-safe (R.beginDead w) s eq valid | nothing = case eq of λ ()

 chosen-safe (R.sampleDead w) s eq valid with lookup w (R.faults s) in found
 ... | just f with R.phase f
 ...   | R.asyncDead = case just-injective eq of λ { refl → safe-machine (proj₂ valid) , λ _ → tt }
 chosen-safe (R.sampleDead w) s eq valid | just f | R.readyBody = case eq of λ ()
 chosen-safe (R.sampleDead w) s eq valid | just f | R.readyBuffer = case eq of λ ()
 chosen-safe (R.sampleDead w) s eq valid | just f | R.awaitingClose = case eq of λ ()
 chosen-safe (R.sampleDead w) s eq valid | just f | R.closing = case eq of λ ()
 chosen-safe (R.sampleDead w) s eq valid | just f | R.poolClosed = case eq of λ ()
 chosen-safe (R.sampleDead w) s eq valid | just f | R.asyncStatus = case eq of λ ()
 chosen-safe (R.sampleDead w) s eq valid | just f | R.handedOff = case eq of λ ()
 chosen-safe (R.sampleDead w) s eq valid | nothing = case eq of λ ()

 chosen-safe (R.commitDead w) s eq valid with lookup w (R.faults s) in found
 ... | just f with R.phase f
 ...   | R.asyncDead = case just-injective eq of λ { refl → safe-machine (proj₂ valid) , λ _ → tt }
 chosen-safe (R.commitDead w) s eq valid | just f | R.readyBody = case eq of λ ()
 chosen-safe (R.commitDead w) s eq valid | just f | R.readyBuffer = case eq of λ ()
 chosen-safe (R.commitDead w) s eq valid | just f | R.awaitingClose = case eq of λ ()
 chosen-safe (R.commitDead w) s eq valid | just f | R.closing = case eq of λ ()
 chosen-safe (R.commitDead w) s eq valid | just f | R.poolClosed = case eq of λ ()
 chosen-safe (R.commitDead w) s eq valid | just f | R.asyncStatus = case eq of λ ()
 chosen-safe (R.commitDead w) s eq valid | just f | R.handedOff = case eq of λ ()
 chosen-safe (R.commitDead w) s eq valid | nothing = case eq of λ ()

 chosen-safe (R.finishDead w) s eq valid with lookup w (R.faults s) in found
 ... | just f with R.phase f | R.outcome f | P.muxAt (R.mux f) (R.protocols s)
 ...   | R.asyncDead | R.async err | just m with WireMux.callback m | M.finishMatches (M.failed err) (WireMux.status m)
 ...     | WireMux.returned | true = case just-injective eq of λ { refl → safe-local (phase-covers w f R.readyBuffer s found valid) , λ _ → tt }
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | just m | WireMux.returned | false = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | just m | WireMux.readActive tr | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | just m | WireMux.commitTrace active tr | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | just m | WireMux.afterStart n | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | just m | WireMux.forkPending n | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | just m | WireMux.afterFailure | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | just m | WireMux.tracerFailed n | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | nothing = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.sync err | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.readyBody | _ | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.readyBuffer | _ | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.awaitingClose | _ | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.closing | _ | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.poolClosed | _ | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncStatus | _ | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.handedOff | _ | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | nothing = case eq of λ ()

 chosen-safe (R.observeDeadTraceException w err) s eq valid with lookup w (R.faults s) in found
 ... | just f with R.phase f | P.muxAt (R.mux f) (R.protocols s)
 ...   | R.asyncDead | just m with R.deadThrowPoint m
 ...     | true = case just-injective eq of λ { refl → safe-local (covers-put w _ (R.faults s) (view s) (covers-at (proj₂ valid) w f found) (proj₂ valid)) , λ _ → tt }
 ...     | false = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.asyncDead | nothing = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.readyBody | _ = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.readyBuffer | _ = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.awaitingClose | _ = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.closing | _ = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.poolClosed | _ = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.asyncStatus | _ = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.handedOff | _ = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | nothing = case eq of λ ()

 chosen-safe (R.handoff w) s eq valid with lookup w (R.faults s) in found | lookup w (W.exits (R.base s))
 ... | just f | nothing with R.phase f | R.outcome f
 ...   | R.readyBuffer | result = case just-injective eq of λ { refl → safe-transfer (covers-at (proj₂ valid) w f found) (phase-covers w f R.handedOff s found valid) , λ _ → tt }
 ...   | R.readyBody | R.sync err = case just-injective eq of λ { refl → safe-transfer (covers-at (proj₂ valid) w f found) (phase-covers w f R.handedOff s found valid) , λ _ → tt }
 ...   | R.readyBody | R.async err = case just-injective eq of λ { refl → safe-transfer (covers-at (proj₂ valid) w f found) (phase-covers w f R.handedOff s found valid) , λ _ → tt }
 chosen-safe (R.handoff w) s eq valid | just f | nothing | R.awaitingClose | _ = case eq of λ ()
 chosen-safe (R.handoff w) s eq valid | just f | nothing | R.closing | _ = case eq of λ ()
 chosen-safe (R.handoff w) s eq valid | just f | nothing | R.poolClosed | _ = case eq of λ ()
 chosen-safe (R.handoff w) s eq valid | just f | nothing | R.asyncStatus | _ = case eq of λ ()
 chosen-safe (R.handoff w) s eq valid | just f | nothing | R.asyncDead | _ = case eq of λ ()
 chosen-safe (R.handoff w) s eq valid | just f | nothing | R.handedOff | _ = case eq of λ ()
 chosen-safe (R.handoff w) s eq valid | just f | just exit = case eq of λ ()
 chosen-safe (R.handoff w) s eq valid | nothing | _ = case eq of λ ()
 choose-safe : ∀ a s {p} → R.choose a s ≡ just p → Valid s → PlanSafe p s
 choose-safe a s chosen valid = proj₁ (chosen-safe a s chosen valid)
 chosen-nonack : ∀ a s {p} → R.choose a s ≡ just p → Valid s → IsDirect a → NonAck p
 chosen-nonack a s chosen valid = proj₂ (chosen-safe a s chosen valid)
 step-preserves : ∀ a s {t} → R.step a s ≡ just t → Valid s → Valid t
 step-preserves a s eq valid with R.choose a s in chosen
 ... | nothing = case eq of λ ()
 ... | just p = enact-preserves p s eq valid (choose-safe a s chosen valid)
 initialized-valid : ∀ c {s} → R.initial c ≡ just s → Valid s
 initialized-valid c eq with X.initial c in initialized
 ... | nothing = case eq of λ ()
 ... | just x = case just-injective eq of λ { refl → Lower.initialized-valid c initialized , covers-empty {R.Fault} (Birth.ExitLayer.view isBearerClosed x) }
