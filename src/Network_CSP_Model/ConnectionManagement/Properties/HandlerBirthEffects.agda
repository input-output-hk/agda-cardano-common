{-# OPTIONS --guardedness #-}

-- Capture-map effects of real physical-handler steps. Phases may change;
-- captured descriptors are introduced only by the guarded fork operations.
module ConnectionManagement.Properties.HandlerBirthEffects where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (WorkerId; ErrorId)
open import ConnectionManagement.Store using (Store; lookup; put)
open import ConnectionManagement.Properties.Entries using (lookup-put)
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxEgress as EgressLayout
import ConnectionManagement.State as S
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundRelease as OutboundRelease
import ConnectionManagement.Rules.InboundRelease as Release
import ConnectionManagement.Rules.RemoteState as Remote
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.CMShutdown as Close

Registry : Set
Registry = Store WorkerId S.HandlerStart
captures : Store WorkerId H.Thread → Registry
captures = map (λ { (w , t) → w , H.captured t })
raw : H.State → Registry
raw s = captures (H.threads s)
physical : B.State → Registry
physical s = captures (B.threads s)

-- Store projection preserves lookup and replacement, including shadowed rows.
lookup-captures : ∀ w ts → lookup w (captures ts) ≡ Data.Maybe.map H.captured (lookup w ts)
lookup-captures w [] = refl
lookup-captures w ((q , t) ∷ ts) with w ≟ q
... | yes _ = refl
... | no _ = lookup-captures w ts
captures-put : ∀ w t ts → captures (put w t ts) ≡ put w (H.captured t) (captures ts)
captures-put w t [] = refl
captures-put w t ((q , old) ∷ ts) with w ≟ q
... | yes _ = refl
... | no _ = cong ((q , H.captured old) ∷_) (captures-put w t ts)
put-found : ∀ (w : WorkerId) (h : S.HandlerStart) (rs : Registry) → lookup w rs ≡ just h → put w h rs ≡ rs
put-found w h [] ()
put-found w h ((q , old) ∷ rs) eq with w ≟ q
... | yes refl with just-injective eq
...   | refl = refl
put-found w h ((q , old) ∷ rs) eq | no _ = cong ((q , old) ∷_) (put-found w h rs eq)
phase-map : ∀ w t phase s → lookup w (H.threads s) ≡ just t → raw (H.setPhase w t phase s) ≡ raw s
phase-map w t phase s found = trans (captures-put w (record t { phase = phase }) (H.threads s))
  (put-found w (H.captured t) (raw s) (trans (lookup-captures w (H.threads s)) (cong (Data.Maybe.map H.captured) found)))

-- A witness marks each real birth; the transitive form supports coupled steps.
data Change (Witness : Set) : Registry → Registry → Set where
 stable : ∀ {before after} → after ≡ before → Change Witness before after
 added : ∀ {before after} w h → lookup w before ≡ nothing → after ≡ put w h before → Witness → Change Witness before after
 followed : ∀ {before middle after} → Change Witness before middle → Change Witness middle after → Change Witness before after
map-change : ∀ {P Q before after} → (P → Q) → Change P before after → Change Q before after
map-change f (stable eq) = stable eq
map-change f (added w h absent same witness) = added w h absent same (f witness)
map-change f (followed first rest) = followed (map-change f first) (map-change f rest)

data AdmissionBirth : H.Action → Set where
 admission-birth : ∀ w → AdmissionBirth (H.run (M.admissionStep w Server.fork))

-- Ordinary source writes leave the physical registry intact.
dispatch-change : ∀ {P} action s {s′} → H.dispatch action s ≡ just s′ → Change P (raw s) (raw s′)
dispatch-change action s eq with M.advance action (H.source s)
... | nothing = case eq of λ ()
... | just c = case just-injective eq of λ { refl → stable refl }
dispatch-phase-change : ∀ {P} action w t phase s {s′} → lookup w (H.threads s) ≡ just t →
 H.dispatchPhase action w t phase s ≡ just s′ → Change P (raw s) (raw s′)
dispatch-phase-change action w t phase s found eq with M.advance action (H.source s)
... | nothing = case eq of λ ()
... | just c = case just-injective eq of λ { refl → stable (phase-map w t phase s found) }
acknowledge-change : ∀ {P} s {s′} → H.acknowledge s ≡ just s′ → Change P (raw s) (raw s′)
acknowledge-change s eq with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.acknowledgeDelivery (H.shutdown s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → stable refl }

fork-change : ∀ w s {s′} → H.forkAdmission w s ≡ just s′ → Change (AdmissionBirth (H.run (M.admissionStep w Server.fork))) (raw s) (raw s′)
fork-change w s eq with lookup w (S.admissions (M.world (H.source s)))
... | nothing = case eq of λ ()
... | just a with lookup (S.child (S.request a)) (H.threads s) in missing
...   | just old = case eq of λ ()
...   | nothing with M.advance (M.admissionStep w Server.fork) (H.source s)
...     | nothing = case eq of λ ()
...     | just c with lookup (S.child (S.request a)) (S.handlers (M.world c))
...       | nothing = case eq of λ ()
...       | just handler = case just-injective eq of λ { refl → added (S.child (S.request a)) handler
  (trans (lookup-captures (S.child (S.request a)) (H.threads s)) (cong (Data.Maybe.map H.captured) missing))
  (captures-put (S.child (S.request a)) (H.handlerThread handler H.maskedSetup) (H.threads s)) (admission-birth w) }

handshake-change : ∀ {P} w error s {s′} → H.deliverHandshake w error s ≡ just s′ → Change P (raw s) (raw s′)
handshake-change w error s eq with lookup w (H.threads s) in found
... | nothing = case eq of λ ()
... | just t with H.phase t
handshake-change w error s eq | just t | H.maskedSetup = case eq of λ ()
handshake-change w error s eq | just t | H.handshaking = case just-injective eq of λ { refl → stable (phase-map w t (H.caughtCancellation error) s found) }
handshake-change w error s eq | just t | (H.caughtCancellation err) = case eq of λ ()
handshake-change w error s eq | just t | (H.cancellationPublished err) = case eq of λ ()
handshake-change w error s eq | just t | (H.bodyExited err) = case eq of λ ()
handshake-change w error s eq | just t | (H.finalizing err) = case eq of λ ()
handshake-change w error s eq | just t | (H.cleanupComplete err outcome) = case eq of λ ()
handshake-change w error s eq | just t | (H.resultAvailable err outcome) = case eq of λ ()

setup-change : ∀ {P} w error s {s′} → H.deliverBlockedSetup w error s ≡ just s′ → Change P (raw s) (raw s′)
setup-change w error s eq with lookup w (H.threads s) in found
... | nothing = case eq of λ ()
... | just t with H.phase t
setup-change w error s eq | just t | H.maskedSetup = case just-injective eq of λ { refl → stable (phase-map w t (H.bodyExited error) s found) }
setup-change w error s eq | just t | H.handshaking = case eq of λ ()
setup-change w error s eq | just t | (H.caughtCancellation err) = case eq of λ ()
setup-change w error s eq | just t | (H.cancellationPublished err) = case eq of λ ()
setup-change w error s eq | just t | (H.bodyExited err) = case eq of λ ()
setup-change w error s eq | just t | (H.finalizing err) = case eq of λ ()
setup-change w error s eq | just t | (H.cleanupComplete err outcome) = case eq of λ ()
setup-change w error s eq | just t | (H.resultAvailable err outcome) = case eq of λ ()

shutdown-delivery-change : ∀ {P} blocked err s {s′} → H.deliverShutdown blocked err s ≡ just s′ → Change P (raw s) (raw s′)
shutdown-delivery-change blocked err s eq with Close.phase (H.shutdown s)
... | Close.awaitDelivery e w with blocked
...   | false with H.deliverHandshake w err s in delivered
...     | nothing = case eq of λ ()
...     | just next = followed (handshake-change w err s delivered) (acknowledge-change next eq)
shutdown-delivery-change blocked err s eq | Close.awaitDelivery e w | true with H.deliverBlockedSetup w err s in delivered
... | nothing = case eq of λ ()
... | just next = followed (setup-change w err s delivered) (acknowledge-change next eq)
shutdown-delivery-change blocked err s eq | Close.initial = case eq of λ ()
shutdown-delivery-change blocked err s eq | Close.reading = case eq of λ ()
shutdown-delivery-change blocked err s eq | (Close.sendReady e w) = case eq of λ ()
shutdown-delivery-change blocked err s eq | Close.awaitResults = case eq of λ ()
shutdown-delivery-change blocked err s eq | Close.closed = case eq of λ ()

timewait-change : ∀ {P} err s {s′} → H.deliverTimeWait err s ≡ just s′ → Change P (raw s) (raw s′)
timewait-change err s eq with Close.phase (H.shutdown s)
... | Close.awaitDelivery e w with lookup w (H.threads s) in found | lookup w (S.cleanups (M.world (H.source s)))
...   | just t | just (S.cleanupWaiting captured) with H.phase t
...     | H.finalizing original with H.dispatch (M.cleanupStep w (Cleanup.interruptTimeWait err)) s in advanced
...       | nothing = case eq of λ ()
...       | just next = followed (dispatch-change (M.cleanupStep w (Cleanup.interruptTimeWait err)) s advanced) (acknowledge-change next eq)
timewait-change err s eq | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | H.maskedSetup = case eq of λ ()
timewait-change err s eq | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | H.handshaking = case eq of λ ()
timewait-change err s eq | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | (H.caughtCancellation priorError) = case eq of λ ()
timewait-change err s eq | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | (H.cancellationPublished priorError) = case eq of λ ()
timewait-change err s eq | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | (H.bodyExited priorError) = case eq of λ ()
timewait-change err s eq | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | (H.cleanupComplete priorError outcome) = case eq of λ ()
timewait-change err s eq | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | (H.resultAvailable priorError outcome) = case eq of λ ()
timewait-change err s eq | Close.awaitDelivery e w | just t | just S.cleanupAcquire = case eq of λ ()
timewait-change err s eq | Close.awaitDelivery e w | just t | just (S.cleanupSelect capturedLease) = case eq of λ ()
timewait-change err s eq | Close.awaitDelivery e w | just t | just (S.cleanupClose capturedLease map tail) = case eq of λ ()
timewait-change err s eq | Close.awaitDelivery e w | just t | just (S.cleanupPublish capturedLease map tail) = case eq of λ ()
timewait-change err s eq | Close.awaitDelivery e w | just t | just (S.cleanupRestore capturedLease closeError) = case eq of λ ()
timewait-change err s eq | Close.awaitDelivery e w | just t | just (S.cleanupFinalize captured outcome) = case eq of λ ()
timewait-change err s eq | Close.awaitDelivery e w | just t | just (S.cleanupCount outcome) = case eq of λ ()
timewait-change err s eq | Close.awaitDelivery e w | just t | just (S.cleanupDone outcome) = case eq of λ ()
timewait-change err s eq | Close.awaitDelivery e w | nothing | cleanup = case eq of λ ()
timewait-change err s eq | Close.awaitDelivery e w | just t | nothing = case eq of λ ()
timewait-change err s eq | Close.initial = case eq of λ ()
timewait-change err s eq | Close.reading = case eq of λ ()
timewait-change err s eq | (Close.sendReady e w) = case eq of λ ()
timewait-change err s eq | Close.awaitResults = case eq of λ ()
timewait-change err s eq | Close.closed = case eq of λ ()


shutdown-captureSnapshot : ∀ {P} s {s′} → H.step (H.shutdownStep Close.captureSnapshot) s ≡ just s′ → Change P (raw s) (raw s′)
shutdown-captureSnapshot s eq with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.captureSnapshot (H.shutdown s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → stable refl }
shutdown-readEntry : ∀ {P} s {s′} → H.step (H.shutdownStep Close.readEntry) s ≡ just s′ → Change P (raw s) (raw s′)
shutdown-readEntry s eq with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.readEntry (H.shutdown s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → stable refl }
shutdown-requestCancellation : ∀ {P} s {s′} → H.step (H.shutdownStep Close.requestCancellation) s ≡ just s′ → Change P (raw s) (raw s′)
shutdown-requestCancellation s eq with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.requestCancellation (H.shutdown s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → stable refl }
shutdown-finishTraversal : ∀ {P} s {s′} → H.step (H.shutdownStep Close.finishTraversal) s ≡ just s′ → Change P (raw s) (raw s′)
shutdown-finishTraversal s eq with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.finishTraversal (H.shutdown s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → stable refl }
shutdown-finishClose : ∀ {P} s {s′} → H.step (H.shutdownStep Close.finishClose) s ≡ just s′ → Change P (raw s) (raw s′)
shutdown-finishClose s eq with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.finishClose (H.shutdown s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → stable refl }
step-change : ∀ action s {s′} → H.step action s ≡ just s′ → Change (AdmissionBirth action) (raw s) (raw s′)
step-change (H.run (M.admissionStep w Server.fork)) s eq = fork-change w s eq
step-change (H.run (M.admissionStep w Server.take)) s eq = dispatch-change (M.admissionStep w Server.take) s eq
step-change (H.run (M.admissionStep w Server.countLimit)) s eq = dispatch-change (M.admissionStep w Server.countLimit) s eq
step-change (H.run (M.admissionStep w Server.allocatePromise)) s eq = dispatch-change (M.admissionStep w Server.allocatePromise) s eq
step-change (H.run (M.admissionStep w Server.chooseEntry)) s eq = dispatch-change (M.admissionStep w Server.chooseEntry) s eq
step-change (H.run (M.admissionStep w Server.putMapBack)) s eq = dispatch-change (M.admissionStep w Server.putMapBack) s eq
step-change (H.run (M.admissionStep w Server.readCounters)) s eq = dispatch-change (M.admissionStep w Server.readCounters) s eq
step-change (H.run (M.admissionStep w Server.restore)) s eq = dispatch-change (M.admissionStep w Server.restore) s eq
step-change (H.run (M.admissionStep w Server.close)) s eq = dispatch-change (M.admissionStep w Server.close) s eq
step-change (H.run (M.admissionStep w Server.failFork)) s eq = dispatch-change (M.admissionStep w Server.failFork) s eq
step-change (H.run (M.handshakeStep w a)) s eq = dispatch-change (M.handshakeStep w a) s eq
step-change (H.run (M.handlerPublication w result outcome)) s eq = case eq of λ ()
step-change (H.run (M.handlerExit w)) s eq = case eq of λ ()
step-change (H.run (M.handlerStep w a)) s eq = case eq of λ ()
step-change (H.run (M.cleanupStep w a)) s eq = case eq of λ ()
step-change (H.run (M.igStep a)) s eq = dispatch-change (M.igStep a) s eq
step-change (H.run (M.remoteStep a)) s eq with H.rawAllowed (M.remoteStep a)
... | false = case eq of λ ()
... | true = dispatch-change (M.remoteStep a) s eq
step-change (H.run (M.releaseStep a)) s eq with H.rawAllowed (M.releaseStep a)
... | false = case eq of λ ()
... | true = dispatch-change (M.releaseStep a) s eq
step-change (H.enterHandshake w) s eq with lookup w (H.threads s) in found
... | nothing = case eq of λ ()
... | just t with H.phase t
step-change (H.enterHandshake w) s eq | just t | H.maskedSetup = case just-injective eq of λ { refl → stable (phase-map w t H.handshaking s found) }
step-change (H.enterHandshake w) s eq | just t | H.handshaking = case eq of λ ()
step-change (H.enterHandshake w) s eq | just t | (H.caughtCancellation err) = case eq of λ ()
step-change (H.enterHandshake w) s eq | just t | (H.cancellationPublished err) = case eq of λ ()
step-change (H.enterHandshake w) s eq | just t | (H.bodyExited err) = case eq of λ ()
step-change (H.enterHandshake w) s eq | just t | (H.finalizing err) = case eq of λ ()
step-change (H.enterHandshake w) s eq | just t | (H.cleanupComplete err outcome) = case eq of λ ()
step-change (H.enterHandshake w) s eq | just t | (H.resultAvailable err outcome) = case eq of λ ()
step-change (H.deliverHandshakeCancellation w err) s eq = handshake-change w err s eq
step-change (H.deliverBlockedSetupCancellation w err) s eq = setup-change w err s eq
step-change (H.publishCaught w) s eq with lookup w (H.threads s) in found
... | nothing = case eq of λ ()
... | just t with H.phase t
step-change (H.publishCaught w) s eq | just t | H.maskedSetup = case eq of λ ()
step-change (H.publishCaught w) s eq | just t | H.handshaking = case eq of λ ()
step-change (H.publishCaught w) s eq | just t | (H.caughtCancellation err) = dispatch-phase-change (M.handlerPublication w (S.handlerError S.protocolViolation err) M.resultWritten) w t (H.cancellationPublished err) s found eq
step-change (H.publishCaught w) s eq | just t | (H.cancellationPublished err) = case eq of λ ()
step-change (H.publishCaught w) s eq | just t | (H.bodyExited err) = case eq of λ ()
step-change (H.publishCaught w) s eq | just t | (H.finalizing err) = case eq of λ ()
step-change (H.publishCaught w) s eq | just t | (H.cleanupComplete err outcome) = case eq of λ ()
step-change (H.publishCaught w) s eq | just t | (H.resultAvailable err outcome) = case eq of λ ()
step-change (H.rethrowCaught w) s eq with lookup w (H.threads s) in found
... | nothing = case eq of λ ()
... | just t with H.phase t
step-change (H.rethrowCaught w) s eq | just t | H.maskedSetup = case eq of λ ()
step-change (H.rethrowCaught w) s eq | just t | H.handshaking = case eq of λ ()
step-change (H.rethrowCaught w) s eq | just t | (H.caughtCancellation err) = case eq of λ ()
step-change (H.rethrowCaught w) s eq | just t | (H.cancellationPublished err) = case just-injective eq of λ { refl → stable (phase-map w t (H.bodyExited err) s found) }
step-change (H.rethrowCaught w) s eq | just t | (H.bodyExited err) = case eq of λ ()
step-change (H.rethrowCaught w) s eq | just t | (H.finalizing err) = case eq of λ ()
step-change (H.rethrowCaught w) s eq | just t | (H.cleanupComplete err outcome) = case eq of λ ()
step-change (H.rethrowCaught w) s eq | just t | (H.resultAvailable err outcome) = case eq of λ ()
step-change (H.enterFinalizer w) s eq with lookup w (H.threads s) in found
... | nothing = case eq of λ ()
... | just t with H.phase t
step-change (H.enterFinalizer w) s eq | just t | H.maskedSetup = case eq of λ ()
step-change (H.enterFinalizer w) s eq | just t | H.handshaking = case eq of λ ()
step-change (H.enterFinalizer w) s eq | just t | (H.caughtCancellation err) = case eq of λ ()
step-change (H.enterFinalizer w) s eq | just t | (H.cancellationPublished err) = case eq of λ ()
step-change (H.enterFinalizer w) s eq | just t | (H.bodyExited err) = dispatch-phase-change (M.handlerExit w) w t (H.finalizing err) s found eq
step-change (H.enterFinalizer w) s eq | just t | (H.finalizing err) = case eq of λ ()
step-change (H.enterFinalizer w) s eq | just t | (H.cleanupComplete err outcome) = case eq of λ ()
step-change (H.enterFinalizer w) s eq | just t | (H.resultAvailable err outcome) = case eq of λ ()
step-change (H.cleanup w action) s eq with lookup w (H.threads s) in found
... | nothing = case eq of λ ()
... | just t with H.phase t
step-change (H.cleanup w action) s eq | just t | H.maskedSetup = case eq of λ ()
step-change (H.cleanup w action) s eq | just t | H.handshaking = case eq of λ ()
step-change (H.cleanup w action) s eq | just t | (H.caughtCancellation err) = case eq of λ ()
step-change (H.cleanup w action) s eq | just t | (H.cancellationPublished err) = case eq of λ ()
step-change (H.cleanup w action) s eq | just t | (H.bodyExited err) = case eq of λ ()
step-change (H.cleanup w action) s eq | just t | (H.finalizing err) = dispatch-change (M.cleanupStep w action) s eq
step-change (H.cleanup w action) s eq | just t | (H.cleanupComplete err outcome) = case eq of λ ()
step-change (H.cleanup w action) s eq | just t | (H.resultAvailable err outcome) = case eq of λ ()
step-change (H.finishCleanup w) s eq with lookup w (H.threads s) in found | lookup w (S.cleanups (M.world (H.source s)))
... | just t | just (S.cleanupDone outcome) with H.phase t
step-change (H.finishCleanup w) s eq | just t | just (S.cleanupDone outcome) | H.maskedSetup = case eq of λ ()
step-change (H.finishCleanup w) s eq | just t | just (S.cleanupDone outcome) | H.handshaking = case eq of λ ()
step-change (H.finishCleanup w) s eq | just t | just (S.cleanupDone outcome) | (H.caughtCancellation err) = case eq of λ ()
step-change (H.finishCleanup w) s eq | just t | just (S.cleanupDone outcome) | (H.cancellationPublished err) = case eq of λ ()
step-change (H.finishCleanup w) s eq | just t | just (S.cleanupDone outcome) | (H.bodyExited err) = case eq of λ ()
step-change (H.finishCleanup w) s eq | just t | just (S.cleanupDone outcome) | (H.finalizing err) = case just-injective eq of λ { refl → stable (phase-map w t (H.cleanupComplete err outcome) s found) }
step-change (H.finishCleanup w) s eq | just t | just (S.cleanupDone outcome) | (H.cleanupComplete err priorOutcome) = case eq of λ ()
step-change (H.finishCleanup w) s eq | just t | just (S.cleanupDone outcome) | (H.resultAvailable err priorOutcome) = case eq of λ ()
step-change (H.finishCleanup w) s eq | nothing | cleanup = case eq of λ ()
step-change (H.finishCleanup w) s eq | just t | nothing = case eq of λ ()
step-change (H.finishCleanup w) s eq | just t | just S.cleanupAcquire = case eq of λ ()
step-change (H.finishCleanup w) s eq | just t | just (S.cleanupSelect capturedLease) = case eq of λ ()
step-change (H.finishCleanup w) s eq | just t | just (S.cleanupClose capturedLease map tail) = case eq of λ ()
step-change (H.finishCleanup w) s eq | just t | just (S.cleanupPublish capturedLease map tail) = case eq of λ ()
step-change (H.finishCleanup w) s eq | just t | just (S.cleanupRestore capturedLease closeError) = case eq of λ ()
step-change (H.finishCleanup w) s eq | just t | just (S.cleanupWaiting captured) = case eq of λ ()
step-change (H.finishCleanup w) s eq | just t | just (S.cleanupFinalize captured outcome) = case eq of λ ()
step-change (H.finishCleanup w) s eq | just t | just (S.cleanupCount outcome) = case eq of λ ()
step-change (H.publishAsyncResult w) s eq with lookup w (H.threads s) in found | lookup w (S.cleanups (M.world (H.source s)))
... | just t | just (S.cleanupDone outcome) with H.phase t
step-change (H.publishAsyncResult w) s eq | just t | just (S.cleanupDone outcome) | H.maskedSetup = case eq of λ ()
step-change (H.publishAsyncResult w) s eq | just t | just (S.cleanupDone outcome) | H.handshaking = case eq of λ ()
step-change (H.publishAsyncResult w) s eq | just t | just (S.cleanupDone outcome) | (H.caughtCancellation err) = case eq of λ ()
step-change (H.publishAsyncResult w) s eq | just t | just (S.cleanupDone outcome) | (H.cancellationPublished err) = case eq of λ ()
step-change (H.publishAsyncResult w) s eq | just t | just (S.cleanupDone outcome) | (H.bodyExited err) = case eq of λ ()
step-change (H.publishAsyncResult w) s eq | just t | just (S.cleanupDone outcome) | (H.finalizing err) = case eq of λ ()
step-change (H.publishAsyncResult w) s eq | just t | just (S.cleanupDone outcome) | (H.cleanupComplete err observed) = case just-injective eq of λ { refl → stable (phase-map w t (H.resultAvailable err outcome) s found) }
step-change (H.publishAsyncResult w) s eq | just t | just (S.cleanupDone outcome) | (H.resultAvailable err priorOutcome) = case eq of λ ()
step-change (H.publishAsyncResult w) s eq | nothing | cleanup = case eq of λ ()
step-change (H.publishAsyncResult w) s eq | just t | nothing = case eq of λ ()
step-change (H.publishAsyncResult w) s eq | just t | just S.cleanupAcquire = case eq of λ ()
step-change (H.publishAsyncResult w) s eq | just t | just (S.cleanupSelect capturedLease) = case eq of λ ()
step-change (H.publishAsyncResult w) s eq | just t | just (S.cleanupClose capturedLease map tail) = case eq of λ ()
step-change (H.publishAsyncResult w) s eq | just t | just (S.cleanupPublish capturedLease map tail) = case eq of λ ()
step-change (H.publishAsyncResult w) s eq | just t | just (S.cleanupRestore capturedLease closeError) = case eq of λ ()
step-change (H.publishAsyncResult w) s eq | just t | just (S.cleanupWaiting captured) = case eq of λ ()
step-change (H.publishAsyncResult w) s eq | just t | just (S.cleanupFinalize captured outcome) = case eq of λ ()
step-change (H.publishAsyncResult w) s eq | just t | just (S.cleanupCount outcome) = case eq of λ ()
step-change (H.shutdownStep Close.acknowledgeDelivery) s ()
step-change (H.shutdownStep Close.captureSnapshot) s eq = shutdown-captureSnapshot s eq
step-change (H.shutdownStep Close.readEntry) s eq = shutdown-readEntry s eq
step-change (H.shutdownStep Close.requestCancellation) s eq = shutdown-requestCancellation s eq
step-change (H.shutdownStep Close.finishTraversal) s eq = shutdown-finishTraversal s eq
step-change (H.shutdownStep Close.finishClose) s eq = shutdown-finishClose s eq
step-change (H.deliverShutdownHandshake err) s eq = shutdown-delivery-change false err s eq
step-change (H.deliverShutdownBlockedSetup err) s eq = shutdown-delivery-change true err s eq
step-change (H.deliverShutdownTimeWait err) s eq = timewait-change err s eq
step-change H.acknowledgeFinished s eq with Close.phase (H.shutdown s)
... | Close.awaitDelivery e w with H.resultReady w s
...   | false = case eq of λ ()
...   | true = acknowledge-change s eq
step-change H.acknowledgeFinished s eq | Close.initial = case eq of λ ()
step-change H.acknowledgeFinished s eq | Close.reading = case eq of λ ()
step-change H.acknowledgeFinished s eq | (Close.sendReady e w) = case eq of λ ()
step-change H.acknowledgeFinished s eq | Close.awaitResults = case eq of λ ()
step-change H.acknowledgeFinished s eq | Close.closed = case eq of λ ()


-- The shared outbound wrapper introduces exactly these two physical routes.
data PhysicalBirth : B.Action → Set where
 inbound-physical : ∀ w → PhysicalBirth (B.handler (H.run (M.admissionStep w Server.fork)))
 outbound-physical : ∀ w → PhysicalBirth (B.outbound (O.acquire w A.forkOK))
handler-birth : ∀ {a} → AdmissionBirth a → PhysicalBirth (B.handler a)
handler-birth (admission-birth w) = inbound-physical w
fresh-threads : ∀ w s → B.freshChild w s ≡ true → lookup w (B.threads s) ≡ nothing
fresh-threads w s eq with lookup w (B.threads s)
... | just _ = case eq of λ ()
... | nothing = refl
outbound-fork-change : ∀ w s {s′} → B.forkOutbound w s ≡ just s′ →
 Change (PhysicalBirth (B.outbound (O.acquire w A.forkOK))) (physical s) (physical s′)
outbound-fork-change w s eq with lookup w (O.acquiring (B.source s))
... | nothing = case eq of λ ()
... | just f with B.freshChild (A.child (A.req f)) s in fresh
...   | false = case eq of λ ()
...   | true with O.advance (O.acquire w A.forkOK) (B.source s)
...     | nothing = case eq of λ ()
...     | just c with lookup (A.child (A.req f)) (S.handlers (M.world (O.core c)))
...       | nothing = case eq of λ ()
...       | just captured = case just-injective eq of λ { refl → added (A.child (A.req f)) captured
  (trans (lookup-captures (A.child (A.req f)) (B.threads s))
    (cong (Data.Maybe.map H.captured) (fresh-threads (A.child (A.req f)) s fresh)))
  (captures-put (A.child (A.req f)) (H.handlerThread captured H.maskedSetup) (B.threads s)) (outbound-physical w) }

fork-caller-reflect : ∀ action caller → B.forkCaller action ≡ just caller → action ≡ O.acquire caller A.forkOK
fork-caller-reflect (O.acquire caller A.forkOK) other eq = cong (λ w → O.acquire w A.forkOK) (just-injective eq)
fork-caller-reflect (O.acquire caller (A.select choice)) other ()
fork-caller-reflect (O.acquire caller (A.readCounters)) other ()
fork-caller-reflect (O.acquire caller (A.newPromise)) other ()
fork-caller-reflect (O.acquire caller (A.openOK)) other ()
fork-caller-reflect (O.acquire caller (A.configureOK)) other ()
fork-caller-reflect (O.acquire caller (A.bindOK)) other ()
fork-caller-reflect (O.acquire caller (A.connectOK)) other ()
fork-caller-reflect (O.acquire caller (A.gotLocal address)) other ()
fork-caller-reflect (O.acquire caller (A.updateLocalAddress)) other ()
fork-caller-reflect (O.acquire caller (A.commitConnected)) other ()
fork-caller-reflect (O.acquire caller (A.readResult)) other ()
fork-caller-reflect (O.acquire caller (A.commitHandshake)) other ()
fork-caller-reflect (O.acquire caller (A.returnResult)) other ()
fork-caller-reflect (O.acquire caller (A.failIO err)) other ()
fork-caller-reflect (O.acquire caller (A.closeFailed err)) other ()
fork-caller-reflect (O.acquire caller (A.closeOK)) other ()
fork-caller-reflect (O.acquire caller (A.removeReservation)) other ()
fork-caller-reflect (O.acquire caller (A.waitNegotiated)) other ()
fork-caller-reflect (O.inbound action) other ()
fork-caller-reflect (O.beginAcquire caller req) other ()
fork-caller-reflect (O.beginRelease caller key) other ()
fork-caller-reflect (O.release caller action) other ()

-- Nonfork outbound calls write the CM source, preserving physical threads.
physical-step-change : ∀ a s {t} → B.step a s ≡ just t → Change (PhysicalBirth a) (physical s) (physical t)
physical-step-change (B.handler a) s eq with B.handlerAllowed a s
... | false = case eq of λ ()
... | true with H.step a (B.view s) in actual
...   | nothing = case eq of λ ()
...   | just h = case just-injective eq of λ { refl → map-change handler-birth (step-change a (B.view s) actual) }
physical-step-change (B.outbound a) s eq with B.forkCaller a in recognized
... | just w = map-change
  (λ _ → subst (λ action → PhysicalBirth (B.outbound action)) (sym (fork-caller-reflect a w recognized)) (outbound-physical w))
  (outbound-fork-change w s eq)
... | nothing with B.outboundAllowed a s
...   | false = case eq of λ ()
...   | true with O.advance a (B.source s)
...     | nothing = case eq of λ ()
...     | just c = case just-injective eq of λ { refl → stable refl }

-- Birth effects never retarget an already captured descriptor.
retains : ∀ {P before after} → Change P before after → ∀ w h → lookup w before ≡ just h → lookup w after ≡ just h
retains (stable eq) w h found = trans (cong (lookup w) eq) found
retains (added {before = before} q captured absent same witness) w h found with w ≟ q
... | yes refl = case trans (sym absent) found of λ ()
... | no different = trans (cong (lookup w) same) (trans (lookup-put-other q w captured before different) found)
retains (followed first rest) w h found = retains rest w h (retains first w h found)
first-added : ∀ {P before after} → Change P before after → ∀ w h → lookup w before ≡ nothing → lookup w after ≡ just h → P
first-added (stable eq) w h absent found = case trans (sym absent) (trans (sym (cong (lookup w) eq)) found) of λ ()
first-added (added {before = before} q captured missing same witness) w h absent found with w ≟ q
... | yes _ = witness
... | no different = case trans (sym absent)
  (trans (sym (lookup-put-other q w captured before different)) (trans (sym (cong (lookup w) same)) found)) of λ ()
first-added (followed {middle = middle} first rest) w h absent found with lookup w middle in between
... | nothing = first-added rest w h between found
... | just earlier = first-added first w earlier absent between

-- This search works over any finite enabled execution with guarded birth effects.
-- It returns the actual step/prefix decomposition, without a supplied birth.
module Search (State Event : Set) (advance : Event → State → Maybe State)
 (registry : State → Registry) (Birth : State → Event → State → Set)
 (effects : ∀ a s {t} → advance a s ≡ just t → Change (Birth s a t) (registry s) (registry t)) where
 data Runs : State → List Event → State → Set where
  done : ∀ {s} → Runs s [] s
  next : ∀ {s t u a as} → advance a s ≡ just t → Runs t as u → Runs s (a ∷ as) u
 retained : ∀ {s as t} → Runs s as t → ∀ w h → lookup w (registry s) ≡ just h → lookup w (registry t) ≡ just h
 retained done w h found = found
 retained (next {s = s} {a = a} actual rest) w h found = retained rest w h (retains (effects a s actual) w h found)
 record Located (start current : State) (events : List Event) (worker : WorkerId) (captured : S.HandlerStart) : Set where
  field
   before after : State
   action : Event
   prefix suffix : List Event
   decomposition : events ≡ prefix ++ (action ∷ suffix)
   prefix-run : Runs start prefix before
   actual : advance action before ≡ just after
   selected : Birth before action after
   absent-before : lookup worker (registry before) ≡ nothing
   at-birth : lookup worker (registry after) ≡ just captured
   suffix-run : Runs after suffix current
   retained-descriptor : lookup worker (registry current) ≡ just captured
 prepend : ∀ {s t u a events w h} → advance a s ≡ just t → Located t u events w h → Located s u (a ∷ events) w h
 prepend {a = a} actual history = record
  { before = Located.before history; after = Located.after history; action = Located.action history
  ; prefix = a ∷ Located.prefix history; suffix = Located.suffix history
  ; decomposition = cong (a ∷_) (Located.decomposition history)
  ; prefix-run = next actual (Located.prefix-run history); actual = Located.actual history; selected = Located.selected history
  ; absent-before = Located.absent-before history; at-birth = Located.at-birth history
  ; suffix-run = Located.suffix-run history; retained-descriptor = Located.retained-descriptor history }
 locate : ∀ {s events t} → Runs s events t → ∀ w h →
   lookup w (registry s) ≡ nothing → lookup w (registry t) ≡ just h → Located s t events w h
 locate done w h absent found = case trans (sym absent) found of λ ()
 locate (next {s = s} {t = t} {a = a} {as = as} actual rest) w h absent found with lookup w (registry t) in between
 ... | nothing = prepend actual (locate rest w h between found)
 ... | just earlier = subst (λ descriptor → Located s _ (a ∷ as) w descriptor)
   (just-injective (trans (sym (retained rest w earlier between)) found)) record
   { before = s; after = t; action = a; prefix = []; suffix = as; decomposition = refl
   ; prefix-run = done; actual = actual; selected = first-added (effects a s actual) w earlier absent between
   ; absent-before = absent; at-birth = between; suffix-run = rest
   ; retained-descriptor = retained rest w earlier between }

-- The physical wrapper's successful initializer starts with an empty registry.
raw-initial-empty : ∀ c {s} → H.initial c ≡ just s → raw s ≡ []
raw-initial-empty c actual with S.handlers (M.world c) | S.cleanups (M.world c) | M.handlerLifecycles c | M.publicationFaults c
... | [] | [] | [] | [] = case just-injective actual of λ { refl → refl }
... | _ ∷ _ | _ | _ | _ = case actual of λ ()
... | [] | _ ∷ _ | _ | _ = case actual of λ ()
... | [] | [] | _ ∷ _ | _ = case actual of λ ()
... | [] | [] | [] | _ ∷ _ = case actual of λ ()
initial-empty : ∀ c {s} → B.initial c ≡ just s → physical s ≡ []
initial-empty c actual with H.initial (O.core c) in initialized
... | nothing = case actual of λ ()
... | just h = case just-injective actual of λ { refl → raw-initial-empty (O.core c) initialized }
module PhysicalSearch = Search B.State B.Action B.step physical (λ _ a _ → PhysicalBirth a) physical-step-change
physical-execution : ∀ {s as t} → B.Executes s as t → PhysicalSearch.Runs s as t
physical-execution B.done = PhysicalSearch.done
physical-execution (B.next actual rest) = PhysicalSearch.next actual (physical-execution rest)
physical-initialized-birth : ∀ {c start as current w thread} → B.initial c ≡ just start → B.Executes start as current →
 lookup w (B.threads current) ≡ just thread → PhysicalSearch.Located start current as w (H.captured thread)
physical-initialized-birth {c} {start} {current = current} {w} {thread} initialized path found = PhysicalSearch.locate (physical-execution path) w (H.captured thread)
 (trans (cong (lookup w) (initial-empty c initialized)) refl)
 (trans (lookup-captures w (B.threads current)) (cong (Data.Maybe.map H.captured) found))

-- With no admissible birth witness, the effect is capture-map equality.
no-witness-same : ∀ {P before after} → (P → ⊥) → Change P before after → after ≡ before
no-witness-same impossible (stable same) = same
no-witness-same impossible (added w h absent same witness) = ⊥-elim (impossible witness)
no-witness-same impossible (followed first rest) = trans (no-witness-same impossible rest) (no-witness-same impossible first)

import ConnectionManagement.MuxHandlerSupervision as MuxModel
import ConnectionManagement.Properties.MuxHandlerSupervision as MuxProperties
import ConnectionManagement.Rules.MuxJobTypes as Types
open import Data.Bool using (_∧_)
module MuxLayer where
 private module U = MuxModel Types.TypedResult
 private module Startup = U.Startup
 private module Old = MuxProperties Types.TypedResult
 view : U.State → Registry
 view s = physical (U.base s)
 data Selected : U.Action → Set where
  inherited-birth : ∀ {a} → PhysicalBirth a → Selected (U.run a)
 birth-base : ∀ birth s → U.base (U.noteBirth birth s) ≡ U.base s
 birth-base nothing s = refl
 birth-base (just _) s = refl
 inherited-change : ∀ a s {t} → U.inherit a s ≡ just t → Change (Selected (U.run a)) (view s) (view t)
 inherited-change a s eq with U.baseAllowed a s ∧ U.birthFresh (U.birth a (U.base s)) (U.origins s)
 ... | false = case eq of λ ()
 ... | true with B.step a (U.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just b = case just-injective eq of λ { refl → subst (Change (Selected (U.run a)) (view s))
   (sym (cong physical (birth-base (U.birth a (U.base s)) (record s { base = b }))))
   (map-change inherited-birth (physical-step-change a (U.base s) actual)) }
 negotiate-same : ∀ w ps flow s {s′} → U.negotiateReturned w ps flow s ≡ just s′ → view s′ ≡ view s
 negotiate-same w ps flow s eq with lookup w (B.threads (U.base s)) |
   lookup w (U.origins s) | lookup w (U.frames s) in absent
 ... | just t | just origin | nothing with H.phase t
 ...   | H.handshaking = case just-injective eq of λ { refl → refl }
 negotiate-same w ps flow s eq | just t | just origin | nothing | H.maskedSetup = case eq of λ ()
 negotiate-same w ps flow s eq | just t | just origin | nothing | H.caughtCancellation err = case eq of λ ()
 negotiate-same w ps flow s eq | just t | just origin | nothing | H.cancellationPublished err = case eq of λ ()
 negotiate-same w ps flow s eq | just t | just origin | nothing | H.bodyExited err = case eq of λ ()
 negotiate-same w ps flow s eq | just t | just origin | nothing | H.finalizing err = case eq of λ ()
 negotiate-same w ps flow s eq | just t | just origin | nothing | H.cleanupComplete err outcome = case eq of λ ()
 negotiate-same w ps flow s eq | just t | just origin | nothing | H.resultAvailable err outcome = case eq of λ ()
 negotiate-same w ps flow s eq | nothing | origin | previous = case eq of λ ()
 negotiate-same w ps flow s eq | just t | nothing | previous = case eq of λ ()
 negotiate-same w ps flow s eq | just t | just origin | just previous = case eq of λ ()

 allocate-same : ∀ w hid mid s {s′} → U.allocate w hid mid s ≡ just s′ → view s′ ≡ view s
 allocate-same w hid mid s eq with lookup w (U.frames s) in found
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f
 ...   | U.returnedSuccess with O.advance (O.inbound (M.igStep (U.allocationAction f hid mid))) (U.source s) in advanced
 ...     | nothing = case eq of λ ()
 ...     | just c = case just-injective eq of λ { refl → refl }
 allocate-same w hid mid s eq | just f | U.handleAllocated oldHandle oldMux = case eq of λ ()
 allocate-same w hid mid s eq | just f | U.promisePublished oldHandle oldMux = case eq of λ ()

 -- Configured egress installation writes only the actual allocated mux.
 configure-same : ∀ w plan limit bound keys s {s′} → U.configure w plan limit bound keys s ≡ just s′ → view s′ ≡ view s
 configure-same w EgressLayout.plainLayout limit bound keys s eq = case eq of λ ()
 configure-same w (EgressLayout.scheduledLayout slice) limit bound keys s eq with lookup w (U.frames s)
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f
 ...   | U.handleAllocated hid mid with O.advance (O.inbound (M.igStep (IG.configureEgress mid (EgressLayout.scheduledLayout slice) limit bound keys))) (U.source s) in advanced
 ...     | nothing = case eq of λ ()
 ...     | just c = case just-injective eq of λ { refl → refl }
 configure-same w (EgressLayout.scheduledLayout slice) limit bound keys s eq | just f | U.returnedSuccess = case eq of λ ()
 configure-same w (EgressLayout.scheduledLayout slice) limit bound keys s eq | just f | U.promisePublished h m = case eq of λ ()

 publish-same : ∀ w s {s′} → U.publish w s ≡ just s′ → view s′ ≡ view s
 publish-same w s eq with lookup w (U.frames s) in found
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f
 ...   | U.handleAllocated hid mid with O.advance
   (O.inbound (M.handlerPublication w (S.negotiated hid (U.flow f)) M.resultWritten)) (U.source s) in advanced |
   Startup.step Startup.observePublication (U.startup f) in progressed
 ...     | just c | just next = case just-injective eq of λ { refl → refl }
 publish-same w s eq | just f | U.handleAllocated hid mid | nothing | startupResult = case eq of λ ()
 publish-same w s eq | just f | U.handleAllocated hid mid | just c | nothing = case eq of λ ()
 publish-same w s eq | just f | U.returnedSuccess = case eq of λ ()
 publish-same w s eq | just f | U.promisePublished hid mid = case eq of λ ()

 change : ∀ a s {t} → U.step a s ≡ just t → Change (Selected a) (view s) (view t)
 change (U.run a) s eq = inherited-change a s eq
 change (U.negotiate w ps flow) s eq = stable (negotiate-same w ps flow s eq)
 change (U.allocateHandle w hid mid) s eq = stable (allocate-same w hid mid s eq)
 change (U.configureMux w plan limit bound keys) s eq = stable (configure-same w plan limit bound keys s eq)
 change (U.publishSuccess w) s eq = stable (publish-same w s eq)
 change (U.startupStep w a) s eq = stable (cong captures (Old.startup-parent-registry w a s eq))

import ConnectionManagement.MuxProtocolJobs as ProtocolModel
import ConnectionManagement.Properties.MuxProtocolJobs as ProtocolProperties
import ConnectionManagement.Rules.MuxRuntime as Mux
module ProtocolLayer where
 private module P = ProtocolModel
 private module U = P.U
 private module Startup = P.Startup
 private module Pool = P.Pool
 private module Old = ProtocolProperties
 view : P.State → Registry
 view s = physical (U.base (P.base s))
 data Selected : P.Action → Set where
  inherited-birth : ∀ {a} → MuxLayer.Selected a → Selected (P.run a)
 inherited-change : ∀ a s {t} → P.inherit a s ≡ just t → Change (Selected (P.run a)) (view s) (view t)
 inherited-change a s eq with P.inheritedAllowed a
 ... | false = case eq of λ ()
 ... | true with U.step a (P.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just u = case just-injective eq of λ { refl → map-change inherited-birth (MuxLayer.change a (P.base s) actual) }
 fork-same : ∀ w j gen s {t} → Old.Fork w j gen s t → view t ≡ view s
 fork-same w j gen s observation rewrite Old.Fork.after-shape observation = refl
 pending-view : ∀ job j s → view (P.appendPending job j s) ≡ view s
 pending-view job j s with Types.direction job
 ... | Mux.initiatorJob = refl
 ... | Mux.responderJob = refl
 removed-view : ∀ job kept s → view (P.removePublished job kept s) ≡ view s
 removed-view job kept s with Types.direction job
 ... | Mux.initiatorJob = refl
 ... | Mux.responderJob = refl
 commit-same : ∀ j s {t} → Old.CompletionCommit j s t → view t ≡ view s
 commit-same j s observation rewrite Old.CompletionCommit.after-shape observation =
  pending-view (Old.CompletionCommit.capturedJob observation) j _
 returned-body-same : ∀ j s {t} → Old.BodyReturn j s t → view t ≡ view s
 returned-body-same j s observation rewrite Old.BodyReturn.after-shape observation = refl
 published-same : ∀ j s {t} → Old.Publication j s t → view t ≡ view s
 published-same j s observation rewrite Old.Publication.after-shape observation =
  removed-view (Old.Publication.capturedJob observation) (Old.Publication.remainingPending observation) _
 returned-same : ∀ j s {t} → P.returned j s ≡ just t → view t ≡ view s
 returned-same j s eq with lookup j (P.jobs s) in found
 ... | nothing = case eq of λ ()
 ... | just job with Types.phase job
 ...   | Types.executing with P.hasWanton j job s
 ...     | false = case eq of λ ()
 ...     | true = case just-injective eq of λ { refl →
   refl }
 returned-same j s eq | just job | Types.waitingEgress = case eq of λ ()
 returned-same j s eq | just job | Types.resultCaptured result = case eq of λ ()
 registered-same : ∀ j s {t} → P.register j s ≡ just t → view t ≡ view s
 registered-same j s eq with lookup j (P.jobs s)
 ... | nothing = case eq of λ ()
 ... | just job with lookup (Types.owner job) (U.frames (P.base s)) | Pool.parentFork (P.poolAt (Types.owner job) s)
 ...   | just f | just current with j ≟ current
 ...     | no _ = case eq of λ ()
 ...     | yes _ with Pool.step Pool.register (P.poolAt (Types.owner job) s)
 ...       | nothing = case eq of λ ()
 ...       | just p = case just-injective eq of λ { refl → refl }
 registered-same j s eq | just job | nothing | _ = case eq of λ ()
 registered-same j s eq | just job | just f | nothing = case eq of λ ()

 via-protocol-same : ∀ j action s {t} → P.viaProtocol j action s ≡ just t → view t ≡ view s
 via-protocol-same j action s eq with lookup j (P.jobs s)
 ... | nothing = case eq of λ ()
 ... | just job with lookup (Types.owner job) (U.frames (P.base s)) | Pool.step action (P.poolAt (Types.owner job) s)
 ...   | just f | just p = case just-injective eq of λ { refl → refl }
 ...   | nothing | _ = case eq of λ ()
 ...   | just f | nothing = case eq of λ ()
 via-infra-same : ∀ w role action s {t} → P.viaInfra w role action s ≡ just t → view t ≡ view s
 via-infra-same w role action s eq with lookup w (U.frames (P.base s))
 ... | nothing = case eq of λ ()
 ... | just f with P.infraId role (Startup.phase (U.startup f))
 ...   | nothing = case eq of λ ()
 ...   | just j with Pool.step (action j) (P.poolAt w s)
 ...     | nothing = case eq of λ ()
 ...     | just p = case just-injective eq of λ { refl → refl }

 control-same : ∀ w action s {s′} → P.monitorControl w action s ≡ just s′ → view s′ ≡ view s
 control-same w action s eq with lookup w (U.frames (P.base s))
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f | P.monitoring f | P.noParent (P.poolAt w s)
 ...   | U.promisePublished hid mid | true | true with P.muxAt mid s
 ...     | nothing = case eq of λ ()
 ...     | just m with P.controlReady action m (P.poolAt w s)
 ...       | false = case eq of λ ()
 ...       | true with O.advance (O.inbound (M.igStep (P.sourceControl action mid))) (P.source s) in advanced
 ...         | nothing = case eq of λ ()
 ...         | just c = case just-injective eq of λ { refl → refl }
 control-same w action s eq | just f | U.returnedSuccess | _ | _ = case eq of λ ()
 control-same w action s eq | just f | U.handleAllocated hid mid | _ | _ = case eq of λ ()
 control-same w action s eq | just f | U.promisePublished hid mid | false | _ = case eq of λ ()
 control-same w action s eq | just f | U.promisePublished hid mid | true | false = case eq of λ ()

 -- Source egress updates retain the original physical birth registry.
 egress-same : ∀ s {t} → Old.EgressChange s t → view t ≡ view s
 egress-same s observation rewrite Old.EgressChange.after-shape observation = refl
 change : ∀ a s {t} → P.step a s ≡ just t → Change (Selected a) (view s) (view t)
 change (P.run a) s eq = inherited-change a s eq
 change (P.forkResponder w j gen) s eq = stable (fork-same w j gen s (Old.responder-fork-observation w j gen s eq))
 change (P.forkInitiator w j gen n) s eq = stable (fork-same w j gen s (Old.initiator-fork-observation w j gen n s eq))
 change (P.registerProtocol j) s eq = stable (registered-same j s eq)
 change (P.enterProtocolBody j) s eq = stable (egress-same s (Old.enter-observation j s eq))
 change (P.appendProtocolPayload j bytes) s eq = stable (egress-same s (Old.send-observation j bytes s eq))
 change (P.egressMuxer w action) s eq = stable (egress-same s (Old.muxer-egress-observation w action s eq))
 change (P.protocolReturned j) s eq = stable (returned-same j s eq)
 change (P.commitClean j) s eq = stable (commit-same j s (Old.clean-observation j s eq))
 change (P.protocolException j err) s eq = stable (commit-same j s (Old.exception-observation j err s eq))
 change (P.returnProtocol j) s eq = stable (returned-body-same j s (Old.return-observation j s eq))
 change (P.publishProtocol j) s eq = stable (published-same j s (Old.publication-observation j s eq))
 change (P.deregisterProtocol j) s eq = stable (via-protocol-same j (Pool.deregister j) s eq)
 change (P.asyncProtocolResult j) s eq = stable (via-protocol-same j (Pool.publishAsyncResult j) s eq)
 change (P.infrastructureReturn w role err) s eq = stable (via-infra-same w role (λ j → Pool.bodyReturnedWith j (Types.infraResult role err)) s eq)
 change (P.publishInfra w role) s eq = stable (via-infra-same w role Pool.publishCompletion s eq)
 change (P.deregisterInfra w role) s eq = stable (via-infra-same w role Pool.deregister s eq)
 change (P.asyncInfraResult w role) s eq = stable (via-infra-same w role Pool.publishAsyncResult s eq)
 change (P.control w a) s eq = stable (control-same w a s eq)

import ConnectionManagement.MuxResultMonitor as MonitorModel
open import ConnectionManagement.IGTypes using (clean; errored)
import Data.Nat as Nat
open import Relation.Nullary using (does)
module MonitorLayer (isBearerClosed : ErrorId → Bool) where
 private module W = MonitorModel isBearerClosed
 private module P = ProtocolModel
 private module U = P.U
 private module Pool = P.Pool
 view : W.State → Registry
 view s = ProtocolLayer.view (W.base s)
 data Selected : W.Action → Set where
  inherited-birth : ∀ {a} → ProtocolLayer.Selected a → Selected (W.run a)
 record CIPaths (before after : W.State) : Set where
  constructor ci-path
  field retention : view after ≡ view before
 ci-from-base : ∀ before after → ProtocolLayer.view (W.base after) ≡ ProtocolLayer.view (W.base before) → CIPaths before after
 ci-from-base before after path = ci-path path
 ci-idle : ∀ s → CIPaths s s
 ci-idle s = ci-path refl
 ci-pc-paths : ∀ w pc s → CIPaths s (W.setPC w pc s)
 ci-pc-paths w pc s = ci-path refl
 ci-compose : ∀ {p q r} → CIPaths p q → CIPaths q r → CIPaths p r
 ci-compose (ci-path first) (ci-path second) = ci-path (trans second first)
 ci-source-step : ∀ action s {c} → O.advance (O.inbound (M.igStep action)) (W.source s) ≡ just c → CIPaths s (W.setSource c s)
 ci-source-step action s eq = ci-path refl
 inherited-change : ∀ a s {t} → W.inherit a s ≡ just t → Change (Selected (W.run a)) (view s) (view t)
 inherited-change a s eq with W.delegateAllowed a s
 ... | false = case eq of λ ()
 ... | true with P.step a (W.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just p = case just-injective eq of λ { refl → map-change inherited-birth (ProtocolLayer.change a (W.base s) actual) }
 ci-via-projects : ∀ action s {s′} → W.viaSource action s ≡ just s′ → CIPaths s s′
 ci-via-projects action s eq with O.advance (O.inbound (M.igStep action)) (W.source s) in advanced
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → ci-source-step action s advanced }
 ci-select-projects : ∀ w s {s′} → W.selectHead w s ≡ just s′ → CIPaths s s′
 ci-select-projects w s eq with W.pcAt w s | W.ownerContext w s
 ... | W.waiting | just (f , mid) with W.muxAt mid s | P.noParent (W.poolAt w s) | Pool.completions (W.poolAt w s)
 ...   | just m | true | item ∷ rest with Mux.status m | Mux.callback m
 ...     | Mux.ready | Mux.returned with Pool.step Pool.consumeCompletion (W.poolAt w s) in advanced
 ...       | nothing = case eq of λ ()
 ...       | just next = case just-injective eq of λ { refl → ci-from-base s _ (refl) }
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.stopping | _ = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.stopped | _ = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.failed err | _ = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.ready | Mux.readActive tr = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.ready | Mux.commitTrace active tr = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.ready | Mux.afterStart n = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.ready | Mux.forkPending n = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.ready | Mux.afterFailure = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.ready | Mux.tracerFailed n = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | nothing | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just _ | false | _ = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just _ | true | [] = case eq of λ ()
 ci-select-projects w s eq | W.waiting | nothing = case eq of λ ()
 ci-select-projects w s eq | W.selected item | _ = case eq of λ ()
 ci-select-projects w s eq | W.responderTracing result | _ = case eq of λ ()
 ci-select-projects w s eq | W.initiatorTracing result | _ = case eq of λ ()
 ci-select-projects w s eq | W.deadReady outcome | _ = case eq of λ ()
 ci-select-projects w s eq | W.deadTracing outcome | _ = case eq of λ ()
 ci-select-projects w s eq | W.finished outcome | _ = case eq of λ ()

 ci-pc-after : ∀ w pc {before after} → CIPaths before after → CIPaths before (W.setPC w pc after)
 ci-pc-after w pc {after = after} path = ci-compose path (ci-pc-paths w pc after)
 ci-protocol-source-projects : ∀ w mid dir n outcome s {s′} → W.protocolSource w mid dir n outcome s ≡ just s′ → CIPaths s s′
 ci-protocol-source-projects w mid Mux.responderJob n outcome s eq with W.muxAt mid s
 ... | nothing = case eq of λ ()
 ... | just m with W.legacyMatches n outcome (Mux.completions m)
 ...   | false = case eq of λ ()
 ...   | true with W.viaSource (IG.monitorCompletion mid) s in advanced
 ...     | nothing = case eq of λ ()
 ...     | just next = case just-injective eq of λ { refl → ci-pc-after w (W.responderTracing outcome) (ci-via-projects (IG.monitorCompletion mid) s advanced) }
 ci-protocol-source-projects w mid Mux.initiatorJob n clean s eq = case just-injective eq of λ { refl → ci-pc-paths w (W.initiatorTracing clean) s }
 ci-protocol-source-projects w mid Mux.initiatorJob n (errored err) s eq with W.viaSource (IG.recordMuxFailure mid err) s in advanced
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → ci-pc-after w (W.initiatorTracing (errored err)) (ci-via-projects (IG.recordMuxFailure mid err) s advanced) }
 ci-handle-protocol-projects : ∀ w dir n gen outcome s {s′} → W.handleProtocol w dir n gen outcome s ≡ just s′ → CIPaths s s′
 ci-handle-protocol-projects w dir n gen outcome s eq with W.ownerContext w s | W.findCaptured w dir n gen outcome (P.jobs (W.base s))
 ... | just (f , mid) | just (j , job) with does (Types.mux job ≟ mid) | W.muxAt mid s
 ...   | true | just m with Mux.status m | Mux.callback m
 ...     | Mux.ready | Mux.returned = ci-protocol-source-projects w mid dir n outcome s eq
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.stopping | _ = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.stopped | _ = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.failed err | _ = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.ready | Mux.readActive tr = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.ready | Mux.commitTrace active tr = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.ready | Mux.afterStart k = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.ready | Mux.forkPending k = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.ready | Mux.afterFailure = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.ready | Mux.tracerFailed k = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | false | _ = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | nothing = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | nothing | _ = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just _ | nothing = case eq of λ ()
 ci-record-finish-projects : ∀ w outcome s {s′} → W.recordFinish w outcome s ≡ just s′ → CIPaths s s′
 ci-record-finish-projects w outcome s eq with W.ownerContext w s
 ... | nothing = case eq of λ ()
 ... | just (f , mid) with W.viaSource (W.statusAction outcome mid) s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-pc-after w (W.deadReady outcome) (ci-via-projects (W.statusAction outcome mid) s advanced) }
 ci-handle-projects : ∀ w s {s′} → W.handleHead w s ≡ just s′ → CIPaths s s′
 ci-handle-projects w s eq with W.pcAt w s
 ... | W.selected (Types.protocolCompletion dir n gen outcome) = ci-handle-protocol-projects w dir n gen outcome s eq
 ... | W.selected (Types.infraMuxer err) = ci-record-finish-projects w (W.failed err) s eq
 ... | W.selected (Types.infraDemuxer err) = ci-record-finish-projects w (W.demuxFinish w err s) s eq
 ... | W.waiting = case eq of λ ()
 ... | W.responderTracing _ = case eq of λ ()
 ... | W.initiatorTracing _ = case eq of λ ()
 ... | W.deadReady _ = case eq of λ ()
 ... | W.deadTracing _ = case eq of λ ()
 ... | W.finished _ = case eq of λ ()
 ci-trace-projects : ∀ sample w s {s′} → W.traceSource sample w s ≡ just s′ → CIPaths s s′
 ci-trace-projects sample w s eq with W.tracing (W.pcAt w s) | W.ownerContext w s
 ... | true | just (f , mid) with sample
 ...   | true = ci-via-projects (IG.sampleTracer mid) s eq
 ...   | false = ci-via-projects (IG.commitTracer mid) s eq
 ci-trace-projects sample w s eq | false | _ = case eq of λ ()
 ci-trace-projects sample w s eq | true | nothing = case eq of λ ()
 ci-finish-protocol-projects : ∀ w s {s′} → W.finishProtocol w s ≡ just s′ → CIPaths s s′
 ci-finish-protocol-projects w s eq with W.pcAt w s | W.ownerContext w s
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) with W.muxAt mid s
 ... | just m with Mux.callback m
 ...   | Mux.returned = case just-injective eq of λ { refl → ci-pc-paths w (W.waiting) s }
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | Mux.readActive tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | Mux.commitTrace active tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | Mux.afterStart n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | Mux.forkPending n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | Mux.afterFailure = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | Mux.tracerFailed n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) with W.muxAt mid s
 ... | just m with Mux.callback m
 ...   | Mux.afterFailure = case just-injective eq of λ { refl → ci-pc-paths w (W.deadReady (W.failed err)) s }
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | Mux.readActive tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | Mux.commitTrace active tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | Mux.afterStart n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | Mux.forkPending n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | Mux.tracerFailed n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | Mux.returned = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) with W.muxAt mid s
 ... | just m with Mux.callback m
 ...   | Mux.returned = case just-injective eq of λ { refl → ci-pc-paths w (W.waiting) s }
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | Mux.readActive tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | Mux.commitTrace active tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | Mux.afterStart n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | Mux.forkPending n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | Mux.afterFailure = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | Mux.tracerFailed n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) with W.muxAt mid s
 ... | just m with Mux.callback m
 ...   | Mux.returned = case just-injective eq of λ { refl → ci-pc-paths w (W.deadReady (W.failed err)) s }
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | Mux.readActive tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | Mux.commitTrace active tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | Mux.afterStart n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | Mux.forkPending n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | Mux.afterFailure = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | Mux.tracerFailed n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing result | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.waiting | _ = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.selected item | _ = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.deadReady outcome | _ = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.deadTracing outcome | _ = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.finished outcome | _ = case eq of λ ()

 ci-start-dead-projects : ∀ w s {s′} → W.startDead w s ≡ just s′ → CIPaths s s′
 ci-start-dead-projects w s eq with W.pcAt w s | W.ownerContext w s
 ... | W.deadReady outcome | just (f , mid) with W.muxAt mid s
 ...   | just m with W.finishMatches outcome (Mux.status m) | W.deadAction outcome (Mux.callback m) mid
 ...     | true | just action with W.viaSource action s in advanced
 ...       | nothing = case eq of λ ()
 ...       | just next = case just-injective eq of λ { refl → ci-pc-after w (W.deadTracing outcome) (ci-via-projects action s advanced) }
 ci-start-dead-projects w s eq | W.deadReady outcome | just (f , mid) | just m | false | _ = case eq of λ ()
 ci-start-dead-projects w s eq | W.deadReady outcome | just (f , mid) | just m | true | nothing = case eq of λ ()
 ci-start-dead-projects w s eq | W.deadReady outcome | just (f , mid) | nothing = case eq of λ ()
 ci-start-dead-projects w s eq | W.deadReady outcome | nothing = case eq of λ ()
 ci-start-dead-projects w s eq | W.waiting | _ = case eq of λ ()
 ci-start-dead-projects w s eq | W.selected item | _ = case eq of λ ()
 ci-start-dead-projects w s eq | W.responderTracing result | _ = case eq of λ ()
 ci-start-dead-projects w s eq | W.initiatorTracing result | _ = case eq of λ ()
 ci-start-dead-projects w s eq | W.deadTracing outcome | _ = case eq of λ ()
 ci-start-dead-projects w s eq | W.finished outcome | _ = case eq of λ ()
 ci-finish-dead-projects : ∀ w s {s′} → W.finishMux w s ≡ just s′ → CIPaths s s′
 ci-finish-dead-projects w s eq with W.pcAt w s | W.ownerContext w s
 ... | W.deadTracing outcome | just (f , mid) with W.muxAt mid s
 ...   | just m with Mux.callback m | W.finishMatches outcome (Mux.status m)
 ...     | Mux.returned | true = case just-injective eq of λ { refl → ci-pc-paths w (W.finished outcome) s }
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | Mux.readActive tr | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | Mux.commitTrace active tr | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | Mux.afterStart n | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | Mux.forkPending n | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | Mux.afterFailure | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | Mux.tracerFailed n | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | Mux.returned | false = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | nothing = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | nothing = case eq of λ ()
 ci-finish-dead-projects w s eq | W.waiting | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.selected item | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.responderTracing result | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.initiatorTracing result | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadReady outcome | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.finished outcome | _ = case eq of λ ()

 change : ∀ action s {s′} → W.step action s ≡ just s′ → Change (Selected action) (view s) (view s′)
 change (W.run action) s eq = inherited-change action s eq
 change (W.consume w) s eq = stable (CIPaths.retention (ci-select-projects w s eq))
 change (W.handleSelected w) s eq = stable (CIPaths.retention (ci-handle-projects w s eq))
 change (W.sampleTracer w) s eq = stable (CIPaths.retention (ci-trace-projects true w s eq))
 change (W.commitTracer w) s eq = stable (CIPaths.retention (ci-trace-projects false w s eq))
 change (W.finishProtocolTrace w) s eq = stable (CIPaths.retention (ci-finish-protocol-projects w s eq))
 change (W.beginDead w) s eq = stable (CIPaths.retention (ci-start-dead-projects w s eq))
 change (W.finishDead w) s eq = stable (CIPaths.retention (ci-finish-dead-projects w s eq))
 no-growth : ∀ a s {t} → W.step a s ≡ just t → (Selected a → ⊥) → CIPaths s t
 no-growth a s actual impossible = ci-path (no-witness-same impossible (change a s actual))

import ConnectionManagement.MuxGroupShutdown as GroupModel
import ConnectionManagement.Properties.MuxGroupShutdown as GroupProperties
module GroupLayer (isBearerClosed : ErrorId → Bool) where
 private module W = GroupModel isBearerClosed
 private module Old = GroupProperties isBearerClosed
 private module Monitor = W.M
 private module P = W.P
 private module U = W.U
 private module Pool = W.Pool
 private module CIBase = MonitorLayer isBearerClosed
 open W using (remaining; joined; cancelPC)
 view : W.State → Registry
 view s = CIBase.view (W.base s)
 data Selected : W.Action → Set where
  inherited-birth : ∀ {a} → CIBase.Selected a → Selected (W.run a)
 record CIPaths (before after : W.State) : Set where
  constructor ci-path
  field retention : view after ≡ view before
 ci-from-base : ∀ before after → CIBase.CIPaths (W.base before) (W.base after) → CIPaths before after
 ci-from-base before after path = ci-path (CIBase.CIPaths.retention path)
 ci-idle : ∀ s → CIPaths s s
 ci-idle s = ci-path refl
 ci-compose : ∀ {p q r} → CIPaths p q → CIPaths q r → CIPaths p r
 ci-compose (ci-path first) (ci-path second) = ci-path (trans second first)
 ci-frame-paths : ∀ w f s → CIPaths s (W.setFrame w f s)
 ci-frame-paths w f s = ci-path refl
 ci-phase-paths : ∀ w pc s → CIPaths s (W.setPhase w pc s)
 ci-phase-paths w pc s = ci-frame-paths w _ s
 ci-phase-after : ∀ w pc {before after} → CIPaths before after → CIPaths before (W.setPhase w pc after)
 ci-phase-after w pc {after = after} path = ci-compose path (ci-phase-paths w pc after)
 ci-frame-after : ∀ w f {before after} → CIPaths before after → CIPaths before (W.setFrame w f after)
 ci-frame-after w f {after = after} path = ci-compose path (ci-frame-paths w f after)
 ci-from-protocol : ∀ before after → ProtocolLayer.view (W.protocolState after) ≡ ProtocolLayer.view (W.protocolState before) → CIPaths before after
 ci-from-protocol before after path = ci-path path
 ci-protocol-projects : ∀ s p → ProtocolLayer.view p ≡ ProtocolLayer.view (W.protocolState s) → CIPaths s (W.setProtocols p s)
 ci-protocol-projects s p path = ci-path path
 ci-source-step : ∀ action s {c} → O.advance (O.inbound (M.igStep action)) (W.source s) ≡ just c → CIPaths s (W.setSource c s)
 ci-source-step action s eq = ci-path refl
 inherited-change : ∀ a s {t} → W.inherit a s ≡ just t → Change (Selected (W.run a)) (view s) (view t)
 inherited-change a s eq with W.delegateAllowed a s
 ... | false = case eq of λ ()
 ... | true with Monitor.step a (W.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just m = case just-injective eq of λ { refl → map-change inherited-birth (CIBase.change a (W.base s) actual) }
 ci-via-source-projects : ∀ action s {s′} → W.viaSource action s ≡ just s′ → CIPaths s s′
 ci-via-source-projects action s eq with O.advance (O.inbound (M.igStep action)) (W.source s) in advanced
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → ci-source-step action s advanced }
 ci-pool-step : ∀ w f action s {p} → Pool.step action (W.poolAt w s) ≡ just p → CIPaths s (W.setPool w f p s)
 ci-pool-step w f action s eq = ci-path (refl)
 ci-via-pool-projects : ∀ w action s {s′} → W.viaPool w action s ≡ just s′ → CIPaths s s′
 ci-via-pool-projects w action s eq with W.ownerContext w s
 ... | nothing = case eq of λ ()
 ... | just (f , mid) with Pool.step action (W.poolAt w s) in advanced
 ...   | nothing = case eq of λ ()
 ...   | just p = case just-injective eq of λ { refl → ci-pool-step w f action s advanced }
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
 ci-select-projects : ∀ w s {s′} → W.selectStop w s ≡ just s′ → CIPaths s s′
 ci-select-projects w s eq with W.phase (W.frameAt w s) | Monitor.pcAt w (W.base s) | W.ownerContext w s
 ... | W.idle | Monitor.waiting | just (f , mid) with P.noParent (W.poolAt w s) | P.noResults (W.poolAt w s)
 ...   | true | true with W.viaSource (IG.takeShutdownCommand mid) s in advanced
 ...     | nothing = case eq of λ ()
 ...     | just next = case just-injective eq of λ { refl → ci-phase-after w W.shutdownSelected (ci-via-source-projects (IG.takeShutdownCommand mid) s advanced) }
 ci-select-projects w s eq | W.idle | Monitor.waiting | just (f , mid) | false | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | Monitor.waiting | just (f , mid) | true | false = case eq of λ ()
 ci-select-projects w s eq | W.idle | Monitor.waiting | nothing = case eq of λ ()
 ci-select-projects w s eq | W.idle | Monitor.selected item | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | Monitor.responderTracing result | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | Monitor.initiatorTracing result | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | Monitor.deadReady outcome | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | Monitor.deadTracing outcome | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | Monitor.finished outcome | _ = case eq of λ ()
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
 ...     | just next = case just-injective eq of λ { refl → ci-frame-after w _ (ci-via-pool-projects w (Pool.interruptJob j) s advanced) }
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
 ci-discard-projects : ∀ j job s {s′} → W.discardClean j job s ≡ just s′ → CIPaths s s′
 ci-discard-projects j job s eq with Types.direction job
 ... | Mux.initiatorJob = case just-injective eq of λ { refl → ci-idle s }
 ... | Mux.responderJob with P.locate j (P.pendingAt (Types.owner job) (W.protocolState s)) | P.muxAt (Types.mux job) (W.protocolState s)
 ...   | just (index , kept) | just m with IG.takePending index (Mux.finishedJobs m)
 ...     | just ((n , result) , rest) with does (n Nat.≟ Types.protocolNumber job) ∧ P.sameOutcome ConnectionManagement.IGTypes.clean result
 ...       | true with W.viaSource (IG.discardJobOccurrence (Types.mux job) index) s in advanced
 ...         | nothing = case eq of λ ()
 ...         | just next = case just-injective eq of λ { refl → ci-compose
   (ci-via-source-projects (IG.discardJobOccurrence (Types.mux job) index) s advanced)
   (ci-protocol-projects next _ (refl)) }
 ci-discard-projects j job s eq | Mux.responderJob | just (index , kept) | just m | just ((n , result) , rest) | false = case eq of λ ()
 ci-discard-projects j job s eq | Mux.responderJob | just (index , kept) | just m | nothing = case eq of λ ()
 ci-discard-projects j job s eq | Mux.responderJob | nothing | _ = case eq of λ ()
 ci-discard-projects j job s eq | Mux.responderJob | just pair | nothing = case eq of λ ()
 ci-prepare-projects : ∀ j w f s {s′} → W.prepareUnwind j w f s ≡ just s′ → CIPaths s s′
 ci-prepare-projects j w f s eq with lookup j (P.jobs (W.protocolState s))
 ... | nothing with W.isInfra j f
 ...   | true = case just-injective eq of λ { refl → ci-idle s }
 ...   | false = case eq of λ ()
 ci-prepare-projects j w f s eq | just job with does (w ≟ Types.owner job) | Types.phase job
 ... | true | Types.executing = case just-injective eq of λ { refl → ci-idle s }
 ... | true | Types.waitingEgress = case just-injective eq of λ { refl → ci-idle s }
 ... | true | Types.resultCaptured ConnectionManagement.IGTypes.clean = ci-discard-projects j job s eq
 ... | true | Types.resultCaptured (ConnectionManagement.IGTypes.errored err) = case eq of λ ()
 ... | false | _ = case eq of λ ()
 ci-unwind-projects : ∀ j s {s′} → W.unwindChild j s ≡ just s′ → CIPaths s s′
 ci-unwind-projects j s eq with W.ownerOf j s
 ... | nothing = case eq of λ ()
 ... | just (w , f) with lookup j (Pool.handles (W.poolAt w s))
 ...   | just Pool.bodyUnwinding with W.prepareUnwind j w f s in prepared
 ...     | nothing = case eq of λ ()
 ...     | just next with Pool.step (Pool.bodyUnwound j) (W.poolAt w next) in advanced
 ...       | nothing = case eq of λ ()
 ...       | just p = case just-injective eq of λ { refl → ci-compose (ci-prepare-projects j w f s prepared) (ci-pool-step w f (Pool.bodyUnwound j) next advanced) }
 ci-unwind-projects j s eq | just (w , f) | nothing = case eq of λ ()
 ci-unwind-projects j s eq | just (w , f) | just Pool.bodyRunning = case eq of λ ()
 ci-unwind-projects j s eq | just (w , f) | just (Pool.bodyReturned result) = case eq of λ ()
 ci-unwind-projects j s eq | just (w , f) | just (Pool.deregisterPending exit) = case eq of λ ()
 ci-unwind-projects j s eq | just (w , f) | just (Pool.deregistered exit) = case eq of λ ()
 ci-unwind-projects j s eq | just (w , f) | just (Pool.resultAvailable exit) = case eq of λ ()
 ci-replacement-projects : ∀ j err s {s′} → W.replaceUnwind j err s ≡ just s′ → CIPaths s s′
 ci-replacement-projects j err s eq with lookup j (P.jobs (W.protocolState s))
 ... | nothing = case eq of λ ()
 ... | just job with W.replacementEligible (Types.phase job) | W.ownerOf j s
 ...   | true | just (w , f) with does (w ≟ Types.owner job) | Pool.step (Pool.resumeAfterUnwindError j) (W.poolAt w s) in advanced
 ...     | true | just p with P.step (P.protocolException j err) (W.protocolState (W.setPool w f p s)) in captured
 ...       | nothing = case eq of λ ()
 ...       | just next = case just-injective eq of λ { refl → ci-compose
   (ci-pool-step w f (Pool.resumeAfterUnwindError j) s advanced)
   (ci-protocol-projects (W.setPool w f p s) next (no-witness-same (λ ()) (ProtocolLayer.change (P.protocolException j err) (W.protocolState (W.setPool w f p s)) captured))) }
 ci-replacement-projects j err s eq | just job | true | just (w , f) | false | _ = case eq of λ ()
 ci-replacement-projects j err s eq | just job | true | just (w , f) | true | nothing = case eq of λ ()
 ci-replacement-projects j err s eq | just job | false | _ = case eq of λ ()
 ci-replacement-projects j err s eq | just job | true | nothing = case eq of λ ()
 ci-abort-projects : ∀ w err s {s′} → W.abortMonitor w err s ≡ just s′ → CIPaths s s′
 ci-abort-projects w err s eq with W.abortStage w s | W.ownerContext w s | P.noParent (W.poolAt w s)
 ... | true | just (f , mid) | true with P.muxAt mid (W.protocolState s)
 ...   | just m with Mux.callback m
 ...     | Mux.returned = case just-injective eq of λ { refl → ci-phase-paths w (W.ownerAborting err) s }
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | Mux.readActive tr = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | Mux.commitTrace active tr = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | Mux.afterStart n = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | Mux.forkPending n = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | Mux.afterFailure = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | Mux.tracerFailed n = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | nothing = case eq of λ ()
 ci-abort-projects w err s eq | false | _ | _ = case eq of λ ()
 ci-abort-projects w err s eq | true | nothing | _ = case eq of λ ()
 ci-abort-projects w err s eq | true | just pair | false = case eq of λ ()
 ci-begin-whole-projects : ∀ w order s {s′} → W.beginWhole w order s ≡ just s′ → CIPaths s s′
 ci-begin-whole-projects w order s eq with W.wholeOutcome w s
 ... | nothing = case eq of λ ()
 ... | just outcome with W.viaPool w (Pool.beginClose order) s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-phase-after w (W.wholeClosing outcome) (ci-via-pool-projects w (Pool.beginClose order) s advanced) }
 ci-whole-action-projects : ∀ w action s {s′} → W.wholeAction w action s ≡ just s′ → CIPaths s s′
 ci-whole-action-projects w action s eq with W.phase (W.frameAt w s)
 ... | W.wholeClosing outcome = ci-via-pool-projects w action s eq
 ci-whole-action-projects w action s eq | W.idle = case eq of λ ()
 ci-whole-action-projects w action s eq | W.shutdownSelected = case eq of λ ()
 ci-whole-action-projects w action s eq | W.stoppingTraced = case eq of λ ()
 ci-whole-action-projects w action s eq | W.stoppingWritten = case eq of λ ()
 ci-whole-action-projects w action s eq | W.groupClosing = case eq of λ ()
 ci-whole-action-projects w action s eq | W.draining = case eq of λ ()
 ci-whole-action-projects w action s eq | W.drainReady = case eq of λ ()
 ci-whole-action-projects w action s eq | W.stoppedTrace = case eq of λ ()
 ci-whole-action-projects w action s eq | W.stoppedTracing = case eq of λ ()
 ci-whole-action-projects w action s eq | W.monitorReturnedNormal = case eq of λ ()
 ci-whole-action-projects w action s eq | W.ownerAborting err = case eq of λ ()
 ci-whole-action-projects w action s eq | W.wholeClosed outcome = case eq of λ ()
 ci-whole-action-projects w action s eq | W.asyncFailureWritten err = case eq of λ ()
 ci-whole-action-projects w action s eq | W.asyncDeadTracing err = case eq of λ ()
 ci-whole-action-projects w action s eq | W.scopeDone outcome = case eq of λ ()
 ci-whole-delivery-projects : ∀ w s {s′} → W.deliverWholeChild w s ≡ just s′ → CIPaths s s′
 ci-whole-delivery-projects w s eq with W.phase (W.frameAt w s) | W.ownerContext w s | Pool.phase (W.poolAt w s)
 ... | W.wholeClosing outcome | just (f , mid) | Pool.cancelPending j with W.wholeDeliverable w j f s
 ...   | true = ci-via-pool-projects w Pool.deliverCancel s eq
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
 ...   | just next = case just-injective eq of λ { refl → ci-phase-after w (W.wholeClosed outcome) (ci-via-pool-projects w Pool.finishClose s advanced) }
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
 ...   | just m with Mux.callback m | Monitor.finishMatches (Monitor.failed err) (Mux.status m)
 ...     | Mux.returned | true = case just-injective eq of λ { refl → ci-phase-paths w (W.scopeDone (W.asyncExit err)) s }
 ...     | Mux.returned | false = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | Mux.readActive tr | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | Mux.commitTrace active tr | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | Mux.afterStart n | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | Mux.forkPending n | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | Mux.afterFailure | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | Mux.tracerFailed n | _ = case eq of λ ()
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
 ci-finish-stopped-projects w s eq = subst (CIPaths s)
   (sym (Old.StoppedReturn.next-state (Old.finish-stopped-observation w s eq))) (ci-phase-paths w W.monitorReturnedNormal s)

 change : ∀ action s {s′} → W.step action s ≡ just s′ → Change (Selected action) (view s) (view s′)
 change (W.run action) s eq = inherited-change action s eq
 change (W.requestShutdown w) s eq = stable (CIPaths.retention (ci-request-projects w s eq))
 change (W.selectShutdown w) s eq = stable (CIPaths.retention (ci-select-projects w s eq))
 change (W.observeStoppingTrace w) s eq = stable (CIPaths.retention (ci-from-phase-projects w W.shutdownSelected W.stoppingTraced s eq))
 change (W.writeStopping w) s eq = stable (CIPaths.retention (ci-source-phase-projects w W.stoppingTraced W.stoppingWritten IG.recordMuxStopping s eq))
 change (W.captureGroup w order) s eq = stable (CIPaths.retention (ci-capture-projects w order s eq))
 change (W.requestGroupCancel w) s eq = stable (CIPaths.retention (ci-request-group-projects w s eq))
 change (W.deliverGroup w) s eq = stable (CIPaths.retention (ci-deliver-group-projects w s eq))
 change (W.joinGroup w) s eq = stable (CIPaths.retention (ci-join-group-projects w s eq))
 change (W.finishGroup w) s eq = stable (CIPaths.retention (ci-finish-group-projects w s eq))
 change (W.drainEmpty w) s eq = stable (CIPaths.retention (ci-from-phase-projects w W.draining W.drainReady s (Old.drain-phase w s eq)))
 change (W.timeout2Elapsed w) s eq = stable (CIPaths.retention (ci-from-phase-projects w W.draining W.drainReady s eq))
 change (W.writeStopped w) s eq = stable (CIPaths.retention (ci-source-phase-projects w W.drainReady W.stoppedTrace IG.completeMuxStopping s eq))
 change (W.observeTraceStopped w) s eq = stable (CIPaths.retention (ci-source-phase-projects w W.stoppedTrace W.stoppedTracing IG.traceGracefulMuxStopped s eq))
 change (W.sampleStoppedTracer w) s eq = stable (CIPaths.retention (ci-source-phase-projects w W.stoppedTracing W.stoppedTracing IG.sampleTracer s eq))
 change (W.commitStoppedTracer w) s eq = stable (CIPaths.retention (ci-source-phase-projects w W.stoppedTracing W.stoppedTracing IG.commitTracer s eq))
 change (W.finishStoppedTrace w) s eq = stable (CIPaths.retention (ci-finish-stopped-projects w s eq))
 change (W.finishChildUnwind j) s eq = stable (CIPaths.retention (ci-unwind-projects j s eq))
 change (W.unwindReplacedBySync j err) s eq = stable (CIPaths.retention (ci-replacement-projects j err s eq))
 change (W.abortOwner w err) s eq = stable (CIPaths.retention (ci-abort-projects w err s eq))
 change (W.beginWholeClose w order) s eq = stable (CIPaths.retention (ci-begin-whole-projects w order s eq))
 change (W.requestWholeCancel w) s eq = stable (CIPaths.retention (ci-whole-action-projects w Pool.requestCancel s eq))
 change (W.deliverWhole w) s eq = stable (CIPaths.retention (ci-whole-delivery-projects w s eq))
 change (W.joinWhole w) s eq = stable (CIPaths.retention (ci-whole-action-projects w Pool.join s eq))
 change (W.finishWholeClose w) s eq = stable (CIPaths.retention (ci-finish-whole-projects w s eq))
 change (W.finishNormalScope w) s eq = stable (CIPaths.retention (ci-finish-ordinary-projects w s eq))
 change (W.writeAsyncFailure w) s eq = stable (CIPaths.retention (ci-async-failure-projects w s eq))
 change (W.beginAsyncDead w) s eq = stable (CIPaths.retention (ci-async-dead-projects w s eq))
 change (W.sampleAsyncTracer w) s eq = stable (CIPaths.retention (ci-async-trace-projects true w s eq))
 change (W.commitAsyncTracer w) s eq = stable (CIPaths.retention (ci-async-trace-projects false w s eq))
 change (W.finishAsyncDead w) s eq = stable (CIPaths.retention (ci-finish-async-projects w s eq))
 no-growth : ∀ a s {t} → W.step a s ≡ just t → (Selected a → ⊥) → CIPaths s t
 no-growth a s actual impossible = ci-path (no-witness-same impossible (change a s actual))

import ConnectionManagement.MuxHandlerExit as ExitModel
module ExitLayer (isBearerClosed : ErrorId → Bool) where
 private module W = ExitModel isBearerClosed
 private module G = W.G
 private module Lower = GroupLayer isBearerClosed
 view : W.State → Registry
 view s = Lower.view (W.base s)
 data PlanSelected : W.Plan → W.State → Set where
  inherited-plan : ∀ {a s} → Lower.Selected a → PlanSelected (W.inherited a) s
 data Selected (a : W.Action) (s : W.State) : Set where
  chosen-birth : ∀ {plan} → W.choose a s ≡ just plan → PlanSelected plan s → Selected a s
 -- Selection of an inherited action reflects its actual inherited plan.
 run-selected : ∀ a s → Selected (W.run a) s → Lower.Selected a
 run-selected a s (chosen-birth chosen selected) with W.delegateAllowed a
 ... | false = case chosen of λ ()
 ... | true with just-injective chosen
 ...   | refl with selected
 ...     | inherited-plan witness = witness
 control-change : ∀ {P} a s {t} → W.control a s ≡ just t → Change P (view s) (view t)
 control-change a s eq with Close.step (S.cm (W.shared s)) (λ w → W.resultReady w s) a (W.shutdown s)
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → stable refl }
 enact-change : ∀ plan s {t} → W.enact plan s ≡ just t → Change (PlanSelected plan s) (view s) (view t)
 enact-change (W.local fs) s eq = case just-injective eq of λ { refl → stable refl }
 enact-change (W.machine a fs) s eq with O.advance a (W.source s)
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → stable refl }
 enact-change (W.inherited a) s eq with G.step a (W.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just g = case just-injective eq of λ { refl → map-change inherited-plan (Lower.change a (W.base s) actual) }
 enact-change (W.coordinator a) s eq = control-change a s eq
 enact-change (W.muxDelivery w err) s eq with G.step (G.abortOwner w err) (W.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just g = followed
   (stable (Lower.CIPaths.retention (Lower.no-growth (G.abortOwner w err) (W.base s) actual (λ ()))))
   (control-change Close.acknowledgeDelivery (record s { base = g }) eq)
 enact-change (W.timeWaitDelivery w err) s eq with O.advance (O.inbound (M.cleanupStep w (Cleanup.interruptTimeWait err))) (W.source s)
 ... | nothing = case eq of λ ()
 ... | just c = followed (stable refl)
   (control-change Close.acknowledgeDelivery (record (W.setSource c s) { exits = W.noteCleanup w (Cleanup.interruptTimeWait err) s }) eq)
 enact-change (W.releaseDelivery caller worker err) s eq with G.step (G.abortOwner worker err) (W.base s) in aborted
 ... | nothing = case eq of λ ()
 ... | just g with O.advance (O.release caller (OutboundRelease.cancellationDelivered worker)) (G.source g) in acknowledged
 ...   | nothing = case eq of λ ()
 ...   | just c = case just-injective eq of λ { refl → stable
   (Lower.CIPaths.retention (Lower.no-growth (G.abortOwner worker err) (W.base s) aborted (λ ()))) }
 change : ∀ a s {t} → W.step a s ≡ just t → Change (Selected a s) (view s) (view t)
 change a s eq with W.choose a s in chosen
 ... | nothing = case eq of λ ()
 ... | just plan = map-change (chosen-birth chosen) (enact-change plan s eq)

 record CIPaths (before after : W.State) : Set where
  constructor ci-path
  field retention : view after ≡ view before
 ci-idle : ∀ s → CIPaths s s
 ci-idle s = ci-path refl
 ci-compose : ∀ {s t u} → CIPaths s t → CIPaths t u → CIPaths s u
 ci-compose (ci-path first) (ci-path rest) = ci-path (trans rest first)
 ci-metadata : ∀ s fs → CIPaths s (record s { exits = fs })
 ci-metadata s fs = ci-path refl
 ci-control-projects : ∀ a s {t} → W.control a s ≡ just t → CIPaths s t
 ci-control-projects a s actual = ci-path (no-witness-same (λ ()) (control-change {P = ⊥} a s actual))

import ConnectionManagement.MuxExitCancellation as CancellationModel
module CancellationLayer (isBearerClosed : ErrorId → Bool) where
 private module X = CancellationModel isBearerClosed
 private module W = ExitModel isBearerClosed
 private module CIBase = ExitLayer isBearerClosed
 view : X.State → Registry
 view = CIBase.view
 CIPaths : X.State → X.State → Set
 CIPaths = CIBase.CIPaths
 data Selected : X.Action → X.State → Set where
  inherited-birth : ∀ {a s} → CIBase.Selected a s → Selected (X.run a) s
 ci-delivery-projects : ∀ window w err s {s′} → X.deliver window w err s ≡ just s′ → CIPaths s s′
 ci-delivery-projects window w err s eq with lookup w (W.exits s)
 ... | nothing = case eq of λ ()
 ... | just f with X.target window err (W.phase f)
 ...   | nothing = case eq of λ ()
 ...   | just pc = case just-injective eq of λ { refl → CIBase.ci-metadata s (W.edit w f pc s) }
 ci-trace-projects : ∀ w err s {s′} → X.traceThrew w err s ≡ just s′ → CIPaths s s′
 ci-trace-projects w err s eq with lookup w (W.exits s)
 ... | nothing = case eq of λ ()
 ... | just f with W.phase f
 ...   | W.errorTracing _ _ = case just-injective eq of λ { refl → CIBase.ci-metadata s (W.edit w f (W.bodyExited (W.syncException err)) s) }
 ...   | W.bufferScope _ = case eq of λ ()
 ...   | W.classifying _ = case eq of λ ()
 ...   | W.peerRethrow _ = case eq of λ ()
 ...   | W.nodeDelivery _ = case eq of λ ()
 ...   | W.nodeRethrow _ = case eq of λ ()
 ...   | W.bodyExited _ = case eq of λ ()
 ...   | W.finalizing _ = case eq of λ ()
 ...   | W.cleanupComplete _ _ = case eq of λ ()
 ...   | W.resultAvailable _ _ = case eq of λ ()
 ci-shutdown-projects : ∀ window err s {s′} → X.shutdownDelivery window err s ≡ just s′ → CIPaths s s′
 ci-shutdown-projects window err s eq with Close.phase (W.shutdown s)
 ... | Close.awaitDelivery e w with X.deliver window w err s in delivered
 ...   | nothing = case eq of λ ()
 ...   | just next = CIBase.ci-compose (ci-delivery-projects window w err s delivered) (CIBase.ci-control-projects Close.acknowledgeDelivery next eq)
 ci-shutdown-projects window err s eq | Close.initial = case eq of λ ()
 ci-shutdown-projects window err s eq | Close.reading = case eq of λ ()
 ci-shutdown-projects window err s eq | Close.sendReady _ _ = case eq of λ ()
 ci-shutdown-projects window err s eq | Close.awaitResults = case eq of λ ()
 ci-shutdown-projects window err s eq | Close.closed = case eq of λ ()
 change : ∀ a s {t} → X.step a s ≡ just t → Change (Selected a s) (view s) (view t)
 change (X.run a) s actual = map-change inherited-birth (CIBase.change a s actual)
 change (X.observeCancellation window w err) s actual = stable (CIBase.CIPaths.retention (ci-delivery-projects window w err s actual))
 change (X.deliverShutdown window err) s actual = stable (CIBase.CIPaths.retention (ci-shutdown-projects window err s actual))
 change (X.observeErrorTraceException w err) s actual = stable (CIBase.CIPaths.retention (ci-trace-projects w err s actual))

import ConnectionManagement.MuxStartupUnwind as UnwindModel
import ConnectionManagement.Properties.MuxStartupUnwind as UnwindProperties
module UnwindLayer (isBearerClosed : ErrorId → Bool) where
 private module R = UnwindModel isBearerClosed
 private module X = CancellationModel isBearerClosed
 private module W = ExitModel isBearerClosed
 private module Pool = W.Pool
 private module Lower = CancellationLayer isBearerClosed
 private module Exit = ExitLayer isBearerClosed
 private module Old = UnwindProperties isBearerClosed
 view : R.State → Registry
 view s = Lower.view (R.base s)
 data PlanSelected : R.Plan → R.State → Set where
  inherited-plan : ∀ {a s} → Lower.Selected a (R.base s) → PlanSelected (R.inherited a) s
  acknowledged-plan : ∀ {p s} → PlanSelected p s → PlanSelected (R.acknowledge p) s
 data Selected (a : R.Action) (s : R.State) : Set where
  chosen-birth : ∀ {p} → R.choose a s ≡ just p → PlanSelected p s → Selected a s
 -- This inversion needs the selector, not normalization of a composed step.
 run-selected : ∀ a s → Selected (R.run a) s → Lower.Selected a (R.base s)
 run-selected a s (chosen-birth chosen selected) with R.allowed a s
 ... | false = case chosen of λ ()
 ... | true with just-injective chosen
 ...   | refl with selected
 ...     | inherited-plan witness = witness
 enact-change : ∀ p s {t} → R.enact p s ≡ just t → Change (PlanSelected p s) (view s) (view t)
 enact-change (R.local fs) s eq = case just-injective eq of λ { refl → stable refl }
 enact-change (R.machine a fs) s eq with O.advance a (R.source s)
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → stable refl }
 enact-change (R.pool w u a fs) s eq with Pool.step a (R.poolAt w s)
 ... | nothing = case eq of λ ()
 ... | just pool = case just-injective eq of λ { refl → stable refl }
 enact-change (R.inherited a) s eq with X.step a (R.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just x = case just-injective eq of λ { refl → map-change inherited-plan (Lower.change a (R.base s) actual) }
 enact-change (R.transfer w frame fs) s eq = case just-injective eq of λ { refl → stable refl }
 enact-change (R.acknowledge p) s eq with R.enact p s in delivered
 ... | nothing = case eq of λ ()
 ... | just next with W.control Close.acknowledgeDelivery (R.base next) in acknowledged
 ...   | nothing = case eq of λ ()
 ...   | just w = case just-injective eq of λ { refl → followed
   (map-change acknowledged-plan (enact-change p s delivered))
   (stable (Exit.CIPaths.retention (Exit.ci-control-projects Close.acknowledgeDelivery (R.base next) acknowledged))) }
 change : ∀ a s {t} → R.step a s ≡ just t → Change (Selected a s) (view s) (view t)
 change a s eq with R.choose a s in chosen
 ... | nothing = case eq of λ ()
 ... | just plan = map-change (chosen-birth chosen) (enact-change plan s eq)
 record CIPaths (before after : R.State) : Set where
  constructor ci-path
  field retention : view after ≡ view before
 ci-idle : ∀ s → CIPaths s s
 ci-idle s = ci-path refl
 ci-compose : ∀ {s t u} → CIPaths s t → CIPaths t u → CIPaths s u
 ci-compose (ci-path first) (ci-path rest) = ci-path (trans rest first)
 ci-enact-no-growth : ∀ p s {t} → R.enact p s ≡ just t → (PlanSelected p s → ⊥) → CIPaths s t
 ci-enact-no-growth p s actual impossible = ci-path (no-witness-same impossible (enact-change p s actual))

 -- The callback adapter invokes known monitor operations through this route.
 private module G = W.G
 private module Monitor = G.M
 private module Mon = MonitorLayer isBearerClosed
 run-lower : ∀ a s {t} → R.step (R.run a) s ≡ just t → X.step a (R.base s) ≡ just (R.base t)
 run-lower a s actual with R.allowed a s
 ... | false = case actual of λ ()
 ... | true with X.step a (R.base s)
 ...   | nothing = case actual of λ ()
 ...   | just x = case just-injective actual of λ { refl → refl }
 exit-run-lower : ∀ a s {t} → W.step (W.run a) s ≡ just t → G.step a (W.base s) ≡ just (W.base t)
 exit-run-lower a s eq with W.delegateAllowed a
 ... | false = case eq of λ ()
 ... | true with G.step a (W.base s)
 ...   | nothing = case eq of λ ()
 ...   | just g = case just-injective eq of λ { refl → refl }
 group-run-lower : ∀ a s {t} → G.step (G.run a) s ≡ just t → Monitor.step a (G.base s) ≡ just (G.base t)
 group-run-lower a s eq with G.delegateAllowed a s
 ... | false = case eq of λ ()
 ... | true with Monitor.step a (G.base s)
 ...   | nothing = case eq of λ ()
 ...   | just m = case just-injective eq of λ { refl → refl }
 monitor-source-same : ∀ a s {t} → R.step (R.run (X.run (W.run (G.run a)))) s ≡ just t → (Mon.Selected a → ⊥) → view t ≡ view s
 monitor-source-same a s actual impossible = Mon.CIPaths.retention (Mon.no-growth a (G.base (W.base (R.base s)))
   (group-run-lower a (W.base (R.base s)) (exit-run-lower (G.run a) (R.base s) (run-lower (X.run (W.run (G.run a))) s actual))) impossible)


import ConnectionManagement.MuxDeltaQ as DeltaQModel
import ConnectionManagement.Properties.MuxDeltaQ as DeltaQProperties
module DeltaQLayer (isBearerClosed : ErrorId → Bool) where
 private module D = DeltaQModel isBearerClosed using (Action; State; allowed; applyFault; base; begin; beginDeltaQ; beginInitiator; beginInitiatorTrace; captured; complete; deliverInitiatorShutdown; deliverShutdown; delivery; entryPhase; faultPlan; finishAction; inherit; initiatorFaultPlan; initiatorReady; invoked; muxInvoked; muxReturned; observeException; observeInitiatorException; observeInitiatorReturn; observeReturn; payload; phase; ready; returnInitiator; returned; run; step; throw; throwInitiator; throwing; tickets; wrapMonitor)
 private module R = UnwindModel isBearerClosed using (async; base; enact; poolBody; step)
 private module W = ExitModel isBearerClosed using (shutdown)
 private module Monitor = MonitorModel isBearerClosed using (finishDead; finishProtocolTrace)
 private module Lower = UnwindLayer isBearerClosed using (CIPaths; PlanSelected; Selected; acknowledged-plan; change; ci-enact-no-growth; monitor-source-same; view)
 private module Old = DeltaQProperties isBearerClosed using (fault-selection)
 private module OldR = UnwindProperties isBearerClosed using (Selection; selection-observation)
 view : D.State → Registry
 view s = Lower.view (D.base s)
 data Selected : D.Action → D.State → Set where
  inherited-birth : ∀ {a s} → Lower.Selected a (D.base s) → Selected (D.run a) s
 record CIPaths (before after : D.State) : Set where
  constructor ci-path
  field retention : view after ≡ view before
 ci-idle : ∀ s → CIPaths s s
 ci-idle s = ci-path refl
 ci-compose : ∀ {s t u} → CIPaths s t → CIPaths t u → CIPaths s u
 ci-compose (ci-path first) (ci-path rest) = ci-path (trans rest first)
 finish-same : ∀ w value s {t} → R.step (D.finishAction w value) s ≡ just t → Lower.view t ≡ Lower.view s
 finish-same w (Types.protocolCompletion dir n gen clean) s actual = Lower.monitor-source-same (Monitor.finishProtocolTrace w) s actual (λ ())
 finish-same w (Types.protocolCompletion dir n gen (errored err)) s actual = Lower.monitor-source-same (Monitor.finishDead w) s actual (λ ())
 finish-same w (Types.infraMuxer err) s actual = Lower.monitor-source-same (Monitor.finishDead w) s actual (λ ())
 finish-same w (Types.infraDemuxer err) s actual = Lower.monitor-source-same (Monitor.finishDead w) s actual (λ ())
 delivery-no-birth : ∀ ack p s → (Lower.PlanSelected p s → ⊥) → Lower.PlanSelected (D.delivery ack p) s → ⊥
 delivery-no-birth false p s impossible witness = impossible witness
 delivery-no-birth true p s impossible (Lower.acknowledged-plan witness) = impossible witness
 selection-no-birth : ∀ {w result route s p} → OldR.Selection w result route s p → Lower.PlanSelected p s → ⊥
 selection-no-birth selected rewrite OldR.Selection.plan-shape selected = λ ()
 initiator-selection : ∀ w result s {plan} → D.initiatorFaultPlan w result s ≡ just plan →
   OldR.Selection w result (λ _ _ → just R.poolBody) (D.base s) plan
 initiator-selection w result s eq with lookup w (D.tickets s)
 ... | nothing = case eq of λ ()
 ... | just t with D.phase t | D.initiatorReady w t s
 ...   | D.muxInvoked | true = OldR.selection-observation w result (λ _ _ → just R.poolBody) (D.base s) eq
 ...   | D.muxInvoked | false = case eq of λ ()
 ...   | D.captured | _ = case eq of λ ()
 ...   | D.invoked | _ = case eq of λ ()
 ...   | D.muxReturned | _ = case eq of λ ()
 ...   | D.returned | _ = case eq of λ ()
 ...   | D.throwing | _ = case eq of λ ()
 ci-begin-projects : ∀ w s {s′} → D.begin w s ≡ just s′ → CIPaths s s′
 ci-begin-projects w s eq with lookup w (D.tickets s)
 ... | nothing = case eq of λ ()
 ... | just t with D.entryPhase t ∧ D.ready w t s
 ...   | true = case just-injective eq of λ { refl → ci-path refl }
 ...   | false = case eq of λ ()
 ci-complete-projects : ∀ w s {s′} → D.complete w s ≡ just s′ → CIPaths s s′
 ci-complete-projects w s eq with lookup w (D.tickets s)
 ... | nothing = case eq of λ ()
 ... | just t with D.phase t | D.ready w t s
 ...   | D.invoked | true with R.step (D.finishAction w (D.payload t)) (D.base s) in advanced
 ...     | nothing = case eq of λ ()
 ...     | just r = case just-injective eq of λ { refl → ci-path (finish-same w (D.payload t) (D.base s) advanced) }
 ci-complete-projects w s eq | just t | D.captured | _ = case eq of λ ()
 ci-complete-projects w s eq | just t | D.muxInvoked | _ = case eq of λ ()
 ci-complete-projects w s eq | just t | D.muxReturned | _ = case eq of λ ()
 ci-complete-projects w s eq | just t | D.returned | _ = case eq of λ ()
 ci-complete-projects w s eq | just t | D.throwing | _ = case eq of λ ()
 ci-complete-projects w s eq | just t | D.invoked | false = case eq of λ ()
 ci-apply-fault-projects : ∀ w plan ack s {s′} → (Lower.PlanSelected plan (D.base s) → ⊥) → D.applyFault w plan ack s ≡ just s′ → CIPaths s s′
 ci-apply-fault-projects w plan ack s impossible eq with lookup w (D.tickets s)
 ... | nothing = case eq of λ ()
 ... | just t with R.enact (D.delivery ack plan) (D.base s) in advanced
 ...   | nothing = case eq of λ ()
 ...   | just r = case just-injective eq of λ { refl → ci-path (Lower.CIPaths.retention (Lower.ci-enact-no-growth (D.delivery ack plan) (D.base s) advanced (delivery-no-birth ack plan (D.base s) impossible))) }
 ci-throw-projects : ∀ w result ack s {s′} → D.throw w result ack s ≡ just s′ → CIPaths s s′
 ci-throw-projects w result ack s eq with D.faultPlan w result s in planned
 ... | nothing = case eq of λ ()
 ... | just plan = ci-apply-fault-projects w plan ack s (selection-no-birth (Old.fault-selection w result s planned)) eq
 ci-begin-initiator-projects : ∀ w s {s′} → D.beginInitiator w s ≡ just s′ → CIPaths s s′
 ci-begin-initiator-projects w s eq with lookup w (D.tickets s)
 ... | nothing = case eq of λ ()
 ... | just t with D.phase t | D.initiatorReady w t s
 ...   | D.captured | true = case just-injective eq of λ { refl → ci-path refl }
 ...   | D.captured | false = case eq of λ ()
 ...   | D.muxInvoked | _ = case eq of λ ()
 ...   | D.muxReturned | _ = case eq of λ ()
 ...   | D.invoked | _ = case eq of λ ()
 ...   | D.returned | _ = case eq of λ ()
 ...   | D.throwing | _ = case eq of λ ()
 ci-return-initiator-projects : ∀ w s {s′} → D.returnInitiator w s ≡ just s′ → CIPaths s s′
 ci-return-initiator-projects w s eq with lookup w (D.tickets s)
 ... | nothing = case eq of λ ()
 ... | just t with D.phase t | D.initiatorReady w t s
 ...   | D.muxInvoked | true with D.payload t
 ...     | Types.protocolCompletion Mux.initiatorJob n gen clean = case just-injective eq of λ { refl → ci-path refl }
 ...     | Types.protocolCompletion Mux.initiatorJob n gen (errored err) with R.step (D.wrapMonitor (Monitor.finishProtocolTrace w)) (D.base s) in advanced
 ...       | nothing = case eq of λ ()
 ...       | just r = case just-injective eq of λ { refl → ci-path (Lower.monitor-source-same (Monitor.finishProtocolTrace w) (D.base s) advanced (λ ())) }
 ci-return-initiator-projects w s eq | just t | D.muxInvoked | true | Types.protocolCompletion Mux.responderJob n gen outcome = case eq of λ ()
 ci-return-initiator-projects w s eq | just t | D.muxInvoked | true | Types.infraMuxer err = case eq of λ ()
 ci-return-initiator-projects w s eq | just t | D.muxInvoked | true | Types.infraDemuxer err = case eq of λ ()
 ci-return-initiator-projects w s eq | just t | D.muxInvoked | false = case eq of λ ()
 ci-return-initiator-projects w s eq | just t | D.captured | _ = case eq of λ ()
 ci-return-initiator-projects w s eq | just t | D.muxReturned | _ = case eq of λ ()
 ci-return-initiator-projects w s eq | just t | D.invoked | _ = case eq of λ ()
 ci-return-initiator-projects w s eq | just t | D.returned | _ = case eq of λ ()
 ci-return-initiator-projects w s eq | just t | D.throwing | _ = case eq of λ ()
 ci-throw-initiator-projects : ∀ w result ack s {s′} → D.throwInitiator w result ack s ≡ just s′ → CIPaths s s′
 ci-throw-initiator-projects w result ack s eq with D.initiatorFaultPlan w result s in planned
 ... | nothing = case eq of λ ()
 ... | just plan = ci-apply-fault-projects w plan ack s (selection-no-birth (initiator-selection w result s planned)) eq
 inherited-change : ∀ a s {t} → D.inherit a s ≡ just t → Change (Selected (D.run a) s) (view s) (view t)
 inherited-change a s eq with D.allowed a s
 ... | false = case eq of λ ()
 ... | true with R.step a (D.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just r = case just-injective eq of λ { refl → map-change inherited-birth (Lower.change a (D.base s) actual) }
 change : ∀ action s {s′} → D.step action s ≡ just s′ → Change (Selected action s) (view s) (view s′)
 change (D.run action) s eq = inherited-change action s eq
 change (D.beginDeltaQ w) s eq = stable (CIPaths.retention (ci-begin-projects w s eq))
 change (D.observeReturn w) s eq = stable (CIPaths.retention (ci-complete-projects w s eq))
 change (D.observeException w err) s eq = stable (CIPaths.retention (ci-throw-projects w err false s eq))
 change (D.beginInitiatorTrace w) s eq = stable (CIPaths.retention (ci-begin-initiator-projects w s eq))
 change (D.observeInitiatorReturn w) s eq = stable (CIPaths.retention (ci-return-initiator-projects w s eq))
 change (D.observeInitiatorException w err) s eq = stable (CIPaths.retention (ci-throw-initiator-projects w err false s eq))
 change (D.deliverShutdown err) s eq with Close.phase (W.shutdown (R.base (D.base s)))
 ... | Close.awaitDelivery e w = stable (CIPaths.retention (ci-throw-projects w (R.async err) true s eq))
 ... | Close.initial = case eq of λ ()
 ... | Close.reading = case eq of λ ()
 ... | Close.sendReady e w = case eq of λ ()
 ... | Close.awaitResults = case eq of λ ()
 ... | Close.closed = case eq of λ ()
 change (D.deliverInitiatorShutdown err) s eq with Close.phase (W.shutdown (R.base (D.base s)))
 ... | Close.awaitDelivery e w = stable (CIPaths.retention (ci-throw-initiator-projects w (R.async err) true s eq))
 ... | Close.initial = case eq of λ ()
 ... | Close.reading = case eq of λ ()
 ... | Close.sendReady e w = case eq of λ ()
 ... | Close.awaitResults = case eq of λ ()
 ... | Close.closed = case eq of λ ()

import ConnectionManagement.Properties.MuxCatchUnwind as CatchRoutes
import ConnectionManagement.MuxCatchUnwind as CatchModel
module CatchLayer (isBearerClosed : ErrorId → Bool) where
 private module C = CatchModel isBearerClosed using (Action; State; action; allowed; apply; base; cancellation; deliverShutdown; observe; observeCancellation; observeException; run; select; step; synchronous)
 private module D = DeltaQModel isBearerClosed using (base; delivery; step)
 private module R = UnwindModel isBearerClosed using (State; base; enact)
 private module W = ExitModel isBearerClosed using (shutdown)


 private module Lower = DeltaQLayer isBearerClosed using (Selected; change; delivery-no-birth; view)
 private module Raw = UnwindLayer isBearerClosed using (CIPaths; PlanSelected; ci-enact-no-growth)
 sourceState : C.State → R.State
 sourceState s = D.base (C.base s)
 view : C.State → Registry
 view s = Lower.view (C.base s)
 data Selected : C.Action → C.State → Set where
  inherited-birth : ∀ {a s} → Lower.Selected a (C.base s) → Selected (C.run a) s
 record CIPaths (before after : C.State) : Set where
  constructor ci-path
  field retention : view after ≡ view before
 select-no-birth : ∀ w reason s {p} → C.select w reason s ≡ just p → Raw.PlanSelected (C.action p) (sourceState s) → ⊥
 select-no-birth w reason s eq with CatchRoutes.select-is-local isBearerClosed w reason s eq
 ... | fs , shape rewrite shape = λ ()
 apply-same : ∀ w p ack s {t} → (Raw.PlanSelected (C.action p) (sourceState s) → ⊥) → C.apply w p ack s ≡ just t → CIPaths s t
 apply-same w p ack s impossible eq with R.enact (D.delivery ack (C.action p)) (sourceState s) in actual
 ... | nothing = case eq of λ ()
 ... | just r = case just-injective eq of λ { refl → ci-path (Raw.CIPaths.retention (Raw.ci-enact-no-growth
   (D.delivery ack (C.action p)) (sourceState s) actual (Lower.delivery-no-birth ack (C.action p) (sourceState s) impossible))) }
 observe-same : ∀ w reason ack s {t} → C.observe w reason ack s ≡ just t → CIPaths s t
 observe-same w reason ack s eq with C.select w reason s in selected
 ... | nothing = case eq of λ ()
 ... | just p = apply-same w p ack s (select-no-birth w reason s selected) eq
 change : ∀ a s {t} → C.step a s ≡ just t → Change (Selected a s) (view s) (view t)
 change (C.run a) s eq with C.allowed a
 ... | false = case eq of λ ()
 ... | true with D.step a (C.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just d = case just-injective eq of λ { refl → map-change inherited-birth (Lower.change a (C.base s) actual) }
 change (C.observeException w err) s eq = stable (CIPaths.retention (observe-same w (C.synchronous err) false s eq))
 change (C.observeCancellation w site err) s eq = stable (CIPaths.retention (observe-same w (C.cancellation site err) false s eq))
 change (C.deliverShutdown site err) s eq with Close.phase (W.shutdown (R.base (sourceState s)))
 ... | Close.awaitDelivery e w = stable (CIPaths.retention (observe-same w (C.cancellation site err) true s eq))
 ... | Close.initial = case eq of λ ()
 ... | Close.reading = case eq of λ ()
 ... | Close.sendReady e w = case eq of λ ()
 ... | Close.awaitResults = case eq of λ ()
 ... | Close.closed = case eq of λ ()

import ConnectionManagement.MuxPublicationUnwind as PublicationModel
module PublicationLayer (isBearerClosed : ErrorId → Bool) where
 private module N = PublicationModel isBearerClosed using (Action; State; action; allowed; apply; base; deliverShutdown; deliveryReady; failures; observe; observeFailure; poolAt; raw; run; select; siteReady; source; step)
 private module C = CatchModel isBearerClosed using (step)
 private module D = DeltaQModel isBearerClosed using (delivery)
 private module R = UnwindModel isBearerClosed using (async; base; enact; faults; owner)
 private module W = ExitModel isBearerClosed using (exits; sameStart; shutdown)
 private module U = MuxModel Types.TypedResult using (captured; progress; startup)
 private module Startup = ProtocolModel.Startup using (awaitPublication; bearerReady; bufferReady; demuxerForked; demuxerRegistered; egressReady; matureTraced; monitoring; muxerForked; muxerRegistered; phase; poolReady; published; runEntered; startingTraced)
 private module Pool = ProtocolModel.Pool using (handles)
 private module Lower = CatchLayer isBearerClosed using (Selected; change; view)
 private module Raw = UnwindLayer isBearerClosed using (CIPaths; PlanSelected; ci-enact-no-growth)
 private module Delivery = DeltaQLayer isBearerClosed using (delivery-no-birth)
 view : N.State → Registry
 view s = Lower.view (N.base s)
 data Selected : N.Action → N.State → Set where
  inherited-birth : ∀ {a s} → Lower.Selected a (N.base s) → Selected (N.run a) s
 record CIPaths (before after : N.State) : Set where
  constructor ci-path
  field retention : view after ≡ view before
 select-no-birth : ∀ w site result s {p} → N.select w site result s ≡ just p → Raw.PlanSelected (N.action p) (N.raw s) → ⊥
 select-no-birth w site result s eq with lookup w (N.failures s) | R.owner w (N.raw s) | lookup w (W.exits (R.base (N.raw s))) | lookup w (R.faults (N.raw s))
 ... | just oldFault | _ | _ | _ = case eq of λ ()
 ... | nothing | nothing | _ | _ = case eq of λ ()
 ... | nothing | just f | just e | _ = case eq of λ ()
 ... | nothing | just f | nothing | just oldFault = case eq of λ ()
 ... | nothing | just f | nothing | nothing with N.siteReady site (U.progress f) | N.deliveryReady site result | Startup.phase (U.startup f) | Pool.handles (N.poolAt w s)
 ...   | true | true | Startup.awaitPublication | [] with lookup w (S.handlers (M.world (O.core (N.source s)))) |
    lookup (S.handlerPromise (U.captured f)) (S.handshakeResults (M.world (O.core (N.source s))))
 ...     | just actual | nothing with W.sameStart (U.captured f) actual
 ...       | true = case just-injective eq of λ { refl → λ () }
 ...       | false = case eq of λ ()
 select-no-birth w site result s eq | nothing | just f | nothing | nothing | true | true | Startup.awaitPublication | [] | nothing | _ = case eq of λ ()
 select-no-birth w site result s eq | nothing | just f | nothing | nothing | true | true | Startup.awaitPublication | [] | just actual | just value = case eq of λ ()
 select-no-birth w site result s eq | nothing | just f | nothing | nothing | false | _ | _ | _ = case eq of λ ()
 select-no-birth w site result s eq | nothing | just f | nothing | nothing | true | false | _ | _ = case eq of λ ()
 select-no-birth w site result s eq | nothing | just f | nothing | nothing | true | true | Startup.awaitPublication | h ∷ rest = case eq of λ ()
 select-no-birth w site result s eq | nothing | just f | nothing | nothing | true | true | Startup.published | _ = case eq of λ ()
 select-no-birth w site result s eq | nothing | just f | nothing | nothing | true | true | Startup.bufferReady | _ = case eq of λ ()
 select-no-birth w site result s eq | nothing | just f | nothing | nothing | true | true | Startup.bearerReady | _ = case eq of λ ()
 select-no-birth w site result s eq | nothing | just f | nothing | nothing | true | true | Startup.runEntered | _ = case eq of λ ()
 select-no-birth w site result s eq | nothing | just f | nothing | nothing | true | true | Startup.startingTraced | _ = case eq of λ ()
 select-no-birth w site result s eq | nothing | just f | nothing | nothing | true | true | Startup.egressReady | _ = case eq of λ ()
 select-no-birth w site result s eq | nothing | just f | nothing | nothing | true | true | Startup.poolReady | _ = case eq of λ ()
 select-no-birth w site result s eq | nothing | just f | nothing | nothing | true | true | (Startup.muxerForked j) | _ = case eq of λ ()
 select-no-birth w site result s eq | nothing | just f | nothing | nothing | true | true | (Startup.muxerRegistered j) | _ = case eq of λ ()
 select-no-birth w site result s eq | nothing | just f | nothing | nothing | true | true | (Startup.demuxerForked j k) | _ = case eq of λ ()
 select-no-birth w site result s eq | nothing | just f | nothing | nothing | true | true | (Startup.demuxerRegistered j k) | _ = case eq of λ ()
 select-no-birth w site result s eq | nothing | just f | nothing | nothing | true | true | (Startup.matureTraced j k) | _ = case eq of λ ()
 select-no-birth w site result s eq | nothing | just f | nothing | nothing | true | true | (Startup.monitoring j k) | _ = case eq of λ ()
 apply-same : ∀ w p ack s {t} → (Raw.PlanSelected (N.action p) (N.raw s) → ⊥) → N.apply w p ack s ≡ just t → CIPaths s t
 apply-same w p ack s impossible eq with R.enact (D.delivery ack (N.action p)) (N.raw s) in actual
 ... | nothing = case eq of λ ()
 ... | just r = case just-injective eq of λ { refl → ci-path (Raw.CIPaths.retention (Raw.ci-enact-no-growth
   (D.delivery ack (N.action p)) (N.raw s) actual (Delivery.delivery-no-birth ack (N.action p) (N.raw s) impossible))) }
 observe-same : ∀ w site result ack s {t} → N.observe w site result ack s ≡ just t → CIPaths s t
 observe-same w site result ack s eq with N.select w site result s in selected
 ... | nothing = case eq of λ ()
 ... | just p = apply-same w p ack s (select-no-birth w site result s selected) eq
 change : ∀ a s {t} → N.step a s ≡ just t → Change (Selected a s) (view s) (view t)
 change (N.run a) s eq with N.allowed a s
 ... | false = case eq of λ ()
 ... | true with C.step a (N.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just c = case just-injective eq of λ { refl → map-change inherited-birth (Lower.change a (N.base s) actual) }
 change (N.observeFailure w site result) s eq = stable (CIPaths.retention (observe-same w site result false s eq))
 change (N.deliverShutdown site err) s eq with Close.phase (W.shutdown (R.base (N.raw s)))
 ... | Close.awaitDelivery e w = stable (CIPaths.retention (observe-same w site (R.async err) true s eq))
 ... | Close.initial = case eq of λ ()
 ... | Close.reading = case eq of λ ()
 ... | Close.sendReady e w = case eq of λ ()
 ... | Close.awaitResults = case eq of λ ()
 ... | Close.closed = case eq of λ ()

import ConnectionManagement.ServerAdmission as AdmissionModel
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Properties.MuxPublicationUnwind as PublicationRoutes
-- These observations expose just the inherited child call, avoiding the shared
-- resource/supply proof closure. Guards remain the actual model guards.
module InheritedRoutes (isBearerClosed : ErrorId → Bool) where



 private module Monitor = MonitorModel isBearerClosed using (base; delegateAllowed; run; step)
 private module P = ProtocolModel using (hasWanton; enterProtocolBody; appendProtocolPayload; egressMuxer; base; inheritedAllowed; run; step)
 private module U = MuxModel Types.TypedResult using (base; baseAllowed; birth; birthFresh; origins; run; step)
 group-inherited = (UnwindLayer.group-run-lower isBearerClosed)
 monitor-inherited : ∀ a s {t} → Monitor.step (Monitor.run a) s ≡ just t → P.step a (Monitor.base s) ≡ just (Monitor.base t)
 monitor-inherited a s eq with Monitor.delegateAllowed a s
 ... | false = case eq of λ ()
 ... | true with P.step a (Monitor.base s)
 ...   | nothing = case eq of λ ()
 ...   | just p = case just-injective eq of λ { refl → refl }
 jobs-inherited : ∀ a s {t} → P.step (P.run a) s ≡ just t → U.step a (P.base s) ≡ just (P.base t)
 jobs-inherited a s eq with P.inheritedAllowed a
 ... | false = case eq of λ ()
 ... | true with U.step a (P.base s)
 ...   | nothing = case eq of λ ()
 ...   | just u = case just-injective eq of λ { refl → refl }
 mux-inherited : ∀ a s {t} → U.step (U.run a) s ≡ just t → B.step a (U.base s) ≡ just (U.base t)
 mux-inherited a s eq with U.baseAllowed a s ∧ U.birthFresh (U.birth a (U.base s)) (U.origins s)
 ... | false = case eq of λ ()
 ... | true with B.step a (U.base s)
 ...   | nothing = case eq of λ ()
 ...   | just b = case just-injective eq of λ { refl → cong just (sym (MuxLayer.birth-base (U.birth a (U.base s)) (record s { base = b }))) }
module ServerLayer (isBearerClosed : ErrorId → Bool) where
 private module SA = AdmissionModel isBearerClosed using (Action; State; acceptedFork; accepting; allowed; base; bodyExited; calling; chooseScope; closeDisconnected; closeException; closePrefix; closePrefixWorker; closeWorker; enactClose; enactPrefixClose; enactScope; forkAccepted; fresh; inherit; listenerOpen; nextException; nextNormal; observeException; observeReturn; pc; physicalAction; prefixCloseFailed; prefixException; prefixMatches; prefixReturned; publishWorkerResult; resultAvailable; run; runMachine; sameLimit; scope; scopeAdvance; shared; stage; step; workerClose; workerException; workerPrefixException; workerPrefixReturned; workerResult; workerReturned; workers)
 private module N = PublicationModel isBearerClosed using (raw; step)
 private module W = ExitModel isBearerClosed using (run)
 private module G = GroupModel isBearerClosed using (Action; run)
 private module Monitor = MonitorModel isBearerClosed using (run)
 private module P = ProtocolModel using (hasWanton; enterProtocolBody; appendProtocolPayload; egressMuxer; run)
 private module U = MuxModel Types.TypedResult using (run)
 view : SA.State → Registry
 view s = (PublicationLayer.view isBearerClosed) (SA.base s)
 private module R = UnwindModel isBearerClosed using (base)
 private module X = CancellationModel isBearerClosed using (run)
 -- A source close has no selected physical fork. Reflection uses only the
 -- actual selectors; all enabled-step preservation comes from (PublicationLayer.change isBearerClosed).
 close-group-action : WorkerId → G.Action
 close-group-action w = G.run (Monitor.run (P.run (U.run (B.handler (H.run (Machine.admissionStep w Admission.close))))))
 close-group-impossible : ∀ w → (GroupLayer.Selected isBearerClosed) (close-group-action w) → ⊥
 close-group-impossible w (GroupLayer.inherited-birth (MonitorLayer.inherited-birth
   (ProtocolLayer.inherited-birth (MuxLayer.inherited-birth ()))))
 close-no-birth : ∀ w n → (PublicationLayer.Selected isBearerClosed) (SA.runMachine (Machine.admissionStep w Admission.close)) n → ⊥
 close-no-birth w n (PublicationLayer.inherited-birth (CatchLayer.inherited-birth (DeltaQLayer.inherited-birth selected))) with
   (UnwindLayer.run-selected isBearerClosed) (X.run (W.run (close-group-action w))) (N.raw n) selected
 ... | CancellationLayer.inherited-birth chosen = close-group-impossible w
   ((ExitLayer.run-selected isBearerClosed) (close-group-action w) (R.base (N.raw n)) chosen)
 close-same : ∀ w n {t} → N.step (SA.runMachine (Machine.admissionStep w Admission.close)) n ≡ just t → (PublicationLayer.view isBearerClosed) t ≡ (PublicationLayer.view isBearerClosed) n
 close-same w n {t} actual = no-witness-same (close-no-birth w n)
   ((PublicationLayer.change isBearerClosed) (SA.runMachine (Machine.admissionStep w Admission.close)) n {t = t} actual)

 data Selected : SA.Action → SA.State → Set where
  inherited-birth : ∀ {a s} → (PublicationLayer.Selected isBearerClosed) a (SA.base s) → Selected (SA.run a) s
  scoped-birth : ∀ {a s p command} → SA.chooseScope a s ≡ just p → SA.physicalAction p ≡ just command →
    (PublicationLayer.Selected isBearerClosed) command (SA.base s) → Selected (SA.scope a) s
 inherit-change : ∀ a s {t} → SA.inherit a s ≡ just t → Change (Selected (SA.run a) s) (view s) (view t)
 inherit-change a s eq with SA.allowed a s
 ... | false = case eq of λ ()
 ... | true with N.step a (SA.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just n = case just-injective eq of λ { refl → map-change inherited-birth ((PublicationLayer.change isBearerClosed) a (SA.base s) actual) }
 enact-scope-change : ∀ a p s {t} → SA.chooseScope a s ≡ just p → SA.enactScope p s ≡ just t → Change (Selected (SA.scope a) s) (view s) (view t)
 enact-scope-change a p s chosen eq with SA.physicalAction p in selected
 ... | nothing = case just-injective eq of λ { refl → stable refl }
 ... | just command with N.step command (SA.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just n = case just-injective eq of λ { refl → map-change (scoped-birth chosen selected) ((PublicationLayer.change isBearerClosed) command (SA.base s) actual) }
 scope-change : ∀ a s {t} → SA.scopeAdvance a s ≡ just t → Change (Selected (SA.scope a) s) (view s) (view t)
 scope-change a s eq with SA.chooseScope a s in chosen
 ... | nothing = case eq of λ ()
 ... | just p = enact-scope-change a p s chosen eq
 -- Fixed-map preservation for the Server's own admission-worker bookkeeping.
 private module From (captured : Registry) where
  Valid : SA.State → Set
  Valid s = view s ≡ captured
  -- Successful birth writes an admission and socket; physical metadata is separate.
  fork-preserves : ∀ w req s {t} → SA.forkAccepted w req s ≡ just t → Valid s → Valid t
  fork-preserves w req s eq valid with SA.accepting (SA.stage s) | SA.listenerOpen s |
    SA.sameLimit req (SA.workers s) | SA.fresh w s | SA.fresh (Shared.child req) s |
    w ≟ Shared.child req | lookup (Shared.socketRef req) (Shared.sockets (SA.shared s))
  ... | true | true | true | true | true | no _ | nothing =
    case just-injective eq of λ { refl → valid }
  ... | false | _ | _ | _ | _ | _ | _ = case eq of λ ()
  ... | true | false | _ | _ | _ | _ | _ = case eq of λ ()
  ... | true | true | false | _ | _ | _ | _ = case eq of λ ()
  ... | true | true | true | false | _ | _ | _ = case eq of λ ()
  ... | true | true | true | true | false | _ | _ = case eq of λ ()
  ... | true | true | true | true | true | yes _ | _ = case eq of λ ()
  ... | true | true | true | true | true | no _ | just _ = case eq of λ ()

  -- Return, exception and result observations change only raw-worker metadata.
  return-preserves : ∀ w s {t} → SA.observeReturn w s ≡ just t → Valid s → Valid t
  return-preserves w s eq valid with lookup w (SA.workers s) | lookup w (Shared.admissions (SA.shared s))
  ... | just worker | just a with SA.pc worker | Shared.pc a
  ...   | SA.calling | Shared.completedHandshake (Shared.connected _) = case just-injective eq of λ { refl → valid }
  ...   | SA.calling | Shared.completedHandshake (Shared.disconnected _) = case just-injective eq of λ { refl → valid }
  ...   | SA.calling | Shared.acquireMap = case eq of λ ()
  ...   | SA.calling | Shared.count _ = case eq of λ ()
  ...   | SA.calling | Shared.prepare _ = case eq of λ ()
  ...   | SA.calling | Shared.selectEntry _ _ = case eq of λ ()
  ...   | SA.calling | Shared.forkHandler _ _ _ = case eq of λ ()
  ...   | SA.calling | Shared.publish _ _ _ = case eq of λ ()
  ...   | SA.calling | Shared.reject _ _ = case eq of λ ()
  ...   | SA.calling | Shared.closeSocket _ = case eq of λ ()
  ...   | SA.calling | Shared.finished _ = case eq of λ ()
  ...   | SA.calling | Shared.countPublished _ _ = case eq of λ ()
  ...   | SA.calling | Shared.awaitHandshake _ _ = case eq of λ ()
  ...   | SA.calling | Shared.commitHandshake _ _ = case eq of λ ()
  ...   | SA.calling | Shared.countHandshake _ = case eq of λ ()
  ...   | SA.calling | Shared.notifyInbound _ = case eq of λ ()
  ...   | SA.calling | Shared.returnHandshake _ = case eq of λ ()
  ...   | SA.calling | Shared.impossibleHandshake = case eq of λ ()
  ...   | SA.closeDisconnected | _ = case eq of λ ()
  ...   | SA.closeException _ | _ = case eq of λ ()
  ...   | SA.closePrefix _ _ | _ = case eq of λ ()
  ...   | SA.bodyExited _ | _ = case eq of λ ()
  ...   | SA.resultAvailable _ | _ = case eq of λ ()
  return-preserves w s eq valid | nothing | _ = case eq of λ ()
  return-preserves w s eq valid | just _ | nothing = case eq of λ ()
  prefix-return-preserves : ∀ w s {t} → SA.prefixReturned w s ≡ just t → Valid s → Valid t
  prefix-return-preserves w s eq valid with lookup w (SA.workers s) | lookup w (Shared.admissions (SA.shared s))
  ... | just worker | just a with SA.pc worker | Shared.pc a
  ...   | SA.calling | Shared.closeSocket Shared.hardLimitReached = case just-injective eq of λ { refl → valid }
  ...   | SA.calling | Shared.acquireMap = case eq of λ ()
  ...   | SA.calling | Shared.count _ = case eq of λ ()
  ...   | SA.calling | Shared.prepare _ = case eq of λ ()
  ...   | SA.calling | Shared.selectEntry _ _ = case eq of λ ()
  ...   | SA.calling | Shared.forkHandler _ _ _ = case eq of λ ()
  ...   | SA.calling | Shared.publish _ _ _ = case eq of λ ()
  ...   | SA.calling | Shared.reject _ _ = case eq of λ ()
  ...   | SA.calling | Shared.finished _ = case eq of λ ()
  ...   | SA.calling | Shared.countPublished _ _ = case eq of λ ()
  ...   | SA.calling | Shared.awaitHandshake _ _ = case eq of λ ()
  ...   | SA.calling | Shared.commitHandshake _ _ = case eq of λ ()
  ...   | SA.calling | Shared.countHandshake _ = case eq of λ ()
  ...   | SA.calling | Shared.notifyInbound _ = case eq of λ ()
  ...   | SA.calling | Shared.returnHandshake _ = case eq of λ ()
  ...   | SA.calling | Shared.completedHandshake _ = case eq of λ ()
  ...   | SA.calling | Shared.impossibleHandshake = case eq of λ ()
  ...   | SA.calling | Shared.closeSocket Shared.forbidden = case eq of λ ()
  ...   | SA.calling | Shared.closeSocket Shared.forkFailed = case eq of λ ()
  ...   | SA.closeDisconnected | _ = case eq of λ ()
  ...   | SA.closeException _ | _ = case eq of λ ()
  ...   | SA.closePrefix _ _ | _ = case eq of λ ()
  ...   | SA.bodyExited _ | _ = case eq of λ ()
  ...   | SA.resultAvailable _ | _ = case eq of λ ()
  prefix-return-preserves w s eq valid | nothing | _ = case eq of λ ()
  prefix-return-preserves w s eq valid | just _ | nothing = case eq of λ ()
  prefix-exception-preserves : ∀ w err s {t} → SA.prefixException w err s ≡ just t → Valid s → Valid t
  prefix-exception-preserves w err s eq valid with lookup w (SA.workers s) | lookup w (Shared.admissions (SA.shared s))
  ... | just worker | just a with SA.pc worker | Shared.pc a
  ...   | SA.calling | Shared.closeSocket Shared.forbidden = case just-injective eq of λ { refl → valid }
  ...   | SA.calling | Shared.closeSocket Shared.forkFailed = case just-injective eq of λ { refl → valid }
  ...   | SA.calling | Shared.acquireMap = case eq of λ ()
  ...   | SA.calling | Shared.count _ = case eq of λ ()
  ...   | SA.calling | Shared.prepare _ = case eq of λ ()
  ...   | SA.calling | Shared.selectEntry _ _ = case eq of λ ()
  ...   | SA.calling | Shared.forkHandler _ _ _ = case eq of λ ()
  ...   | SA.calling | Shared.publish _ _ _ = case eq of λ ()
  ...   | SA.calling | Shared.reject _ _ = case eq of λ ()
  ...   | SA.calling | Shared.finished _ = case eq of λ ()
  ...   | SA.calling | Shared.countPublished _ _ = case eq of λ ()
  ...   | SA.calling | Shared.awaitHandshake _ _ = case eq of λ ()
  ...   | SA.calling | Shared.commitHandshake _ _ = case eq of λ ()
  ...   | SA.calling | Shared.countHandshake _ = case eq of λ ()
  ...   | SA.calling | Shared.notifyInbound _ = case eq of λ ()
  ...   | SA.calling | Shared.returnHandshake _ = case eq of λ ()
  ...   | SA.calling | Shared.completedHandshake _ = case eq of λ ()
  ...   | SA.calling | Shared.impossibleHandshake = case eq of λ ()
  ...   | SA.calling | Shared.closeSocket Shared.hardLimitReached = case eq of λ ()
  ...   | SA.closeDisconnected | _ = case eq of λ ()
  ...   | SA.closeException _ | _ = case eq of λ ()
  ...   | SA.closePrefix _ _ | _ = case eq of λ ()
  ...   | SA.bodyExited _ | _ = case eq of λ ()
  ...   | SA.resultAvailable _ | _ = case eq of λ ()
  prefix-exception-preserves w err s eq valid | nothing | _ = case eq of λ ()
  prefix-exception-preserves w err s eq valid | just _ | nothing = case eq of λ ()
  exception-preserves : ∀ w err s {t} → SA.observeException w err s ≡ just t → Valid s → Valid t
  exception-preserves w err s eq valid with lookup w (SA.workers s) | lookup w (Shared.admissions (SA.shared s))
  ... | just worker | just a with SA.pc worker | Shared.pc a
  ...   | SA.calling | Shared.awaitHandshake _ _ = case just-injective eq of λ { refl → valid }
  ...   | SA.calling | Shared.acquireMap = case eq of λ ()
  ...   | SA.calling | Shared.count _ = case eq of λ ()
  ...   | SA.calling | Shared.prepare _ = case eq of λ ()
  ...   | SA.calling | Shared.selectEntry _ _ = case eq of λ ()
  ...   | SA.calling | Shared.forkHandler _ _ _ = case eq of λ ()
  ...   | SA.calling | Shared.publish _ _ _ = case eq of λ ()
  ...   | SA.calling | Shared.reject _ _ = case eq of λ ()
  ...   | SA.calling | Shared.closeSocket _ = case eq of λ ()
  ...   | SA.calling | Shared.finished _ = case eq of λ ()
  ...   | SA.calling | Shared.countPublished _ _ = case eq of λ ()
  ...   | SA.calling | Shared.commitHandshake _ _ = case eq of λ ()
  ...   | SA.calling | Shared.countHandshake _ = case eq of λ ()
  ...   | SA.calling | Shared.notifyInbound _ = case eq of λ ()
  ...   | SA.calling | Shared.returnHandshake _ = case eq of λ ()
  ...   | SA.calling | Shared.completedHandshake _ = case eq of λ ()
  ...   | SA.calling | Shared.impossibleHandshake = case eq of λ ()
  ...   | SA.closeDisconnected | _ = case eq of λ ()
  ...   | SA.closeException _ | _ = case eq of λ ()
  ...   | SA.closePrefix _ _ | _ = case eq of λ ()
  ...   | SA.bodyExited _ | _ = case eq of λ ()
  ...   | SA.resultAvailable _ | _ = case eq of λ ()
  exception-preserves w err s eq valid | nothing | _ = case eq of λ ()
  exception-preserves w err s eq valid | just _ | nothing = case eq of λ ()
  result-preserves : ∀ w s {t} → SA.publishWorkerResult w s ≡ just t → Valid s → Valid t
  result-preserves w s eq valid with lookup w (SA.workers s)
  ... | nothing = case eq of λ ()
  ... | just worker with SA.pc worker
  ...   | SA.bodyExited r = case just-injective eq of λ { refl → valid }
  ...   | SA.calling = case eq of λ ()
  ...   | SA.closeDisconnected = case eq of λ ()
  ...   | SA.closeException _ = case eq of λ ()
  ...   | SA.closePrefix _ _ = case eq of λ ()
  ...   | SA.resultAvailable _ = case eq of λ ()

  -- Both successful/uncertain socket observations preserve the capture map.
  enact-close-preserves : ∀ w worker outcome next s → Valid s →
    Valid (SA.enactClose w worker outcome next s)
  enact-close-preserves w worker outcome next s valid =
    valid
  enact-prefix-preserves : ∀ w worker result outcome s {t} → SA.enactPrefixClose w worker result outcome s ≡ just t →
    Valid s → Valid t
  enact-prefix-preserves w worker result nothing s eq valid with N.step
    (SA.runMachine (Machine.admissionStep w Admission.close)) (SA.base s) in advanced
  ... | nothing = case eq of λ ()
  ... | just n = case just-injective eq of λ { refl → trans (close-same w (SA.base s) advanced) valid }
  enact-prefix-preserves w worker result (just err) s eq valid = case just-injective eq of λ
    { refl → enact-close-preserves w worker (just err) (SA.prefixCloseFailed result err) s valid }
  close-prefix-preserves : ∀ w worker failure result outcome s {t} →
    SA.closePrefixWorker w worker failure result outcome s ≡ just t → Valid s → Valid t
  close-prefix-preserves w worker failure result outcome s eq valid with SA.prefixMatches w failure s
  ... | false = case eq of λ ()
  ... | true = enact-prefix-preserves w worker result outcome s eq valid
  close-preserves : ∀ w outcome s {t} → SA.closeWorker w outcome s ≡ just t → Valid s → Valid t
  close-preserves w outcome s eq valid with lookup w (SA.workers s)
  ... | nothing = case eq of λ ()
  ... | just worker with SA.pc worker
  ...   | SA.closeDisconnected = case just-injective eq of λ
    { refl → enact-close-preserves w worker outcome (SA.nextNormal outcome) s valid }
  ...   | SA.closeException err = case just-injective eq of λ
    { refl → enact-close-preserves w worker outcome (SA.nextException err outcome) s valid }
  ...   | SA.closePrefix f r = close-prefix-preserves w worker f r outcome s eq valid
  ...   | SA.calling = case eq of λ ()
  ...   | SA.bodyExited _ = case eq of λ ()
  ...   | SA.resultAvailable _ = case eq of λ ()


 unchanged : ∀ a s {t} → SA.step a s ≡ just t → (view t ≡ view s) → Change (Selected a s) (view s) (view t)
 unchanged a s actual same = stable same
 change : ∀ a s {t} → SA.step a s ≡ just t → Change (Selected a s) (view s) (view t)
 change (SA.acceptedFork w req) s eq = stable (From.fork-preserves (view s) w req s eq refl)
 change (SA.run a) s eq = inherit-change a s eq
 change (SA.workerReturned w) s eq = stable (From.return-preserves (view s) w s eq refl)
 change (SA.workerPrefixReturned w) s eq = stable (From.prefix-return-preserves (view s) w s eq refl)
 change (SA.workerPrefixException w err) s eq = stable (From.prefix-exception-preserves (view s) w err s eq refl)
 change (SA.workerException w err) s eq = stable (From.exception-preserves (view s) w err s eq refl)
 change (SA.workerClose w outcome) s eq = stable (From.close-preserves (view s) w outcome s eq refl)
 change (SA.workerResult w) s eq = stable (From.result-preserves (view s) w s eq refl)
 change (SA.scope a) s eq = scope-change a s eq

import ConnectionManagement.ServerIGExit as IGExitModel
module IGExitLayer (isBearerClosed : ErrorId → Bool) where
 private module E = IGExitModel isBearerClosed using (Action; Plan; State; abandon; base; choose; delegate; enact; finish; local; step)
 private module SA = AdmissionModel isBearerClosed using (step)
 view : E.State → Registry
 view s = (ServerLayer.view isBearerClosed) (E.base s)
 data PlanSelected : E.Plan → E.State → Set where
  delegated-birth : ∀ {a e s} → (ServerLayer.Selected isBearerClosed) a (E.base s) → PlanSelected (E.delegate a e) s
 data Selected (a : E.Action) (s : E.State) : Set where
  chosen-birth : ∀ {p} → E.choose a s ≡ just p → PlanSelected p s → Selected a s
 enact-change : ∀ p s {t} → E.enact p s ≡ just t → Change (PlanSelected p s) (view s) (view t)
 enact-change (E.delegate a e) s eq with SA.step a (E.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just server = case just-injective eq of λ { refl → map-change delegated-birth ((ServerLayer.change isBearerClosed) a (E.base s) actual) }
 enact-change (E.local e) s eq = case just-injective eq of λ { refl → stable refl }
 enact-change (E.abandon r) s eq = case just-injective eq of λ { refl → stable refl }
 enact-change (E.finish e) s eq = case just-injective eq of λ { refl → stable refl }
 change : ∀ a s {t} → E.step a s ≡ just t → Change (Selected a s) (view s) (view t)
 change a s eq with E.choose a s in chosen
 ... | nothing = case eq of λ ()
 ... | just p = map-change (chosen-birth chosen) (enact-change p s eq)

import ConnectionManagement.ServerPeers as SharedModel
import ConnectionManagement.PeerSupervision as PeerModel
import ConnectionManagement.PeerContext as PeerContext
import ConnectionManagement.Rules.PeerActions as Peer
open import ConnectionManagement.Domain using (HandleId)
open import Data.Nat using (ℕ)
open import ConnectionManagement.IGTypes using (number)
module SharedLayer (isBearerClosed isIOManagerError : ErrorId → Bool) where
 private module K = SharedModel isBearerClosed isIOManagerError using (Action; State; coreAction; coreAllowed; coreStep; peerAllowed; peerOpen; peerStep; peers; server; serverAllowed; serverStep; step)
 private module E = IGExitModel isBearerClosed using (step)
 private module PS = PeerModel isIOManagerError using (step)
 view : K.State → Registry
 view s = (IGExitLayer.view isBearerClosed) (K.server s)
 data Selected : K.Action → K.State → Set where
  server-birth : ∀ {a s} → (IGExitLayer.Selected isBearerClosed) a (K.server s) → Selected (K.serverStep a) s
  core-birth : ∀ {a s} → (IGExitLayer.Selected isBearerClosed) (K.coreAction a) (K.server s) → Selected (K.coreStep a) s
 change : ∀ a s {t} → K.step a s ≡ just t → Change (Selected a s) (view s) (view t)
 change (K.serverStep a) s eq with K.serverAllowed a s
 ... | false = case eq of λ ()
 ... | true with E.step a (K.server s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just e = case just-injective eq of λ { refl → map-change server-birth ((IGExitLayer.change isBearerClosed) a (K.server s) actual) }
 change (K.coreStep a) s eq with K.coreAllowed a s
 ... | false = case eq of λ ()
 ... | true with E.step (K.coreAction a) (K.server s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just e = case just-injective eq of λ { refl → map-change core-birth ((IGExitLayer.change isBearerClosed) (K.coreAction a) (K.server s) actual) }
 change (K.peerStep a) s eq with K.peerOpen s ∧ K.peerAllowed a s
 ... | false = case eq of λ ()
 ... | true with PS.step a (K.peers s)
 ...   | nothing = case eq of λ ()
 ...   | just p = case just-injective eq of λ { refl → stable refl }

import ConnectionManagement.Properties.MuxResultMonitor as MonitorInit
import ConnectionManagement.Properties.MuxHandlerExit as ExitInit
import ConnectionManagement.Properties.MuxCatchUnwind as CatchInit
import ConnectionManagement.Properties.MuxPublicationUnwind as PublicationInit
