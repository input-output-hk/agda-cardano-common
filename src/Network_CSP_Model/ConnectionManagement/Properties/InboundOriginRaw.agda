{-# OPTIONS --guardedness #-}

-- Exact source admission effects through physical handler supervision. These
-- wrappers preserve source computations and add only registry/coordinator data.
module ConnectionManagement.Properties.InboundOriginRaw where

open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)
open import ConnectionManagement.Domain using (WorkerId; ErrorId; DecEq-Id)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.OutboundAcquire as Acquire
import ConnectionManagement.Rules.Cleanup as Cleanup
open import ConnectionManagement.Properties.InboundOriginEffect using (Effect; same; reframe; machine-effect; outbound-effect)

module Raw where
 dispatch-effect : ∀ a s {t} → H.dispatch a s ≡ just t → Effect (H.source s) (H.source t)
 dispatch-effect a s eq with Machine.advance a (H.source s) in actual
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → machine-effect a (H.source s) actual }
 dispatch-phase-effect : ∀ a w thread pc s {t} → lookup w (H.threads s) ≡ just thread →
   H.dispatchPhase a w thread pc s ≡ just t → Effect (H.source s) (H.source t)
 dispatch-phase-effect a w thread pc s found eq with Machine.advance a (H.source s) in actual
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → machine-effect a (H.source s) actual }
 fork-effect : ∀ w s {t} → H.forkAdmission w s ≡ just t → Effect (H.source s) (H.source t)
 fork-effect w s eq with lookup w (S.admissions (Machine.world (H.source s)))
 ... | nothing = case eq of λ ()
 ... | just a with lookup (S.child (S.request a)) (H.threads s)
 ...   | just old = case eq of λ ()
 ...   | nothing with Machine.advance (Machine.admissionStep w Server.fork) (H.source s) in actual
 ...     | nothing = case eq of λ ()
 ...     | just c with lookup (S.child (S.request a)) (S.handlers (Machine.world c))
 ...       | nothing = case eq of λ ()
 ...       | just child = case just-injective eq of λ { refl → machine-effect (Machine.admissionStep w Server.fork) (H.source s) actual }
 -- Acknowledgment only updates the coordinator, so transport the already
 -- observed atomic source effect rather than composing two source effects.
 acknowledge-effect : ∀ {before} s {t} → H.acknowledge s ≡ just t → Effect before (H.source s) → Effect before (H.source t)
 acknowledge-effect s eq observed with Close.step (S.cm (Machine.world (H.source s))) (λ w → H.resultReady w s)
   Close.acknowledgeDelivery (H.shutdown s)
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → observed }
 handshake-source : ∀ w err s {t} → H.deliverHandshake w err s ≡ just t → H.source t ≡ H.source s
 handshake-source w err s eq with lookup w (H.threads s)
 ... | nothing = case eq of λ ()
 ... | just thread with H.phase thread
 handshake-source w err s eq | just thread | H.maskedSetup = case eq of λ ()
 handshake-source w err s eq | just thread | H.handshaking = case just-injective eq of λ { refl → refl }
 handshake-source w err s eq | just thread | (H.caughtCancellation old) = case eq of λ ()
 handshake-source w err s eq | just thread | (H.cancellationPublished old) = case eq of λ ()
 handshake-source w err s eq | just thread | (H.bodyExited old) = case eq of λ ()
 handshake-source w err s eq | just thread | (H.finalizing old) = case eq of λ ()
 handshake-source w err s eq | just thread | (H.cleanupComplete old outcome) = case eq of λ ()
 handshake-source w err s eq | just thread | (H.resultAvailable old outcome) = case eq of λ ()
 setup-source : ∀ w err s {t} → H.deliverBlockedSetup w err s ≡ just t → H.source t ≡ H.source s
 setup-source w err s eq with lookup w (H.threads s)
 ... | nothing = case eq of λ ()
 ... | just thread with H.phase thread
 setup-source w err s eq | just thread | H.maskedSetup = case just-injective eq of λ { refl → refl }
 setup-source w err s eq | just thread | H.handshaking = case eq of λ ()
 setup-source w err s eq | just thread | (H.caughtCancellation old) = case eq of λ ()
 setup-source w err s eq | just thread | (H.cancellationPublished old) = case eq of λ ()
 setup-source w err s eq | just thread | (H.bodyExited old) = case eq of λ ()
 setup-source w err s eq | just thread | (H.finalizing old) = case eq of λ ()
 setup-source w err s eq | just thread | (H.cleanupComplete old outcome) = case eq of λ ()
 setup-source w err s eq | just thread | (H.resultAvailable old outcome) = case eq of λ ()
 handshake-effect : ∀ w err s {t} → H.deliverHandshake w err s ≡ just t → Effect (H.source s) (H.source t)
 handshake-effect w err s eq = reframe refl (handshake-source w err s eq) (same refl)
 setup-effect : ∀ w err s {t} → H.deliverBlockedSetup w err s ≡ just t → Effect (H.source s) (H.source t)
 setup-effect w err s eq = reframe refl (setup-source w err s eq) (same refl)
 shutdown-effect : ∀ blocked err s {t} → H.deliverShutdown blocked err s ≡ just t → Effect (H.source s) (H.source t)
 timewait-effect : ∀ err s {t} → H.deliverTimeWait err s ≡ just t → Effect (H.source s) (H.source t)
 effect : ∀ action s {t} → H.step action s ≡ just t → Effect (H.source s) (H.source t)
 effect (H.run (Machine.admissionStep w Server.fork)) s eq = fork-effect w s eq
 effect (H.run (Machine.admissionStep w Server.take)) s eq = dispatch-effect (Machine.admissionStep w Server.take) s eq
 effect (H.run (Machine.admissionStep w Server.countLimit)) s eq = dispatch-effect (Machine.admissionStep w Server.countLimit) s eq
 effect (H.run (Machine.admissionStep w Server.allocatePromise)) s eq = dispatch-effect (Machine.admissionStep w Server.allocatePromise) s eq
 effect (H.run (Machine.admissionStep w Server.chooseEntry)) s eq = dispatch-effect (Machine.admissionStep w Server.chooseEntry) s eq
 effect (H.run (Machine.admissionStep w Server.putMapBack)) s eq = dispatch-effect (Machine.admissionStep w Server.putMapBack) s eq
 effect (H.run (Machine.admissionStep w Server.readCounters)) s eq = dispatch-effect (Machine.admissionStep w Server.readCounters) s eq
 effect (H.run (Machine.admissionStep w Server.restoreBody)) s eq = dispatch-effect (Machine.admissionStep w Server.restoreBody) s eq
 effect (H.run (Machine.admissionStep w Server.restore)) s eq = dispatch-effect (Machine.admissionStep w Server.restore) s eq
 effect (H.run (Machine.admissionStep w Server.close)) s eq = dispatch-effect (Machine.admissionStep w Server.close) s eq
 effect (H.run (Machine.admissionStep w Server.failFork)) s eq = dispatch-effect (Machine.admissionStep w Server.failFork) s eq
 effect (H.run (Machine.handshakeStep w a)) s eq = dispatch-effect (Machine.handshakeStep w a) s eq
 effect (H.run (Machine.handlerPublication w result outcome)) s eq = case eq of λ ()
 effect (H.run (Machine.handlerExit w)) s eq = case eq of λ ()
 effect (H.run (Machine.handlerStep w a)) s eq = case eq of λ ()
 effect (H.run (Machine.cleanupStep w a)) s eq = case eq of λ ()
 effect (H.run (Machine.igStep a)) s eq = dispatch-effect (Machine.igStep a) s eq
 effect (H.run (Machine.remoteStep a)) s eq with H.rawAllowed (Machine.remoteStep a)
 ... | false = case eq of λ ()
 ... | true = dispatch-effect (Machine.remoteStep a) s eq
 effect (H.run (Machine.releaseStep a)) s eq with H.rawAllowed (Machine.releaseStep a)
 ... | false = case eq of λ ()
 ... | true = dispatch-effect (Machine.releaseStep a) s eq
 effect (H.enterHandshake w) s eq with lookup w (H.threads s) in found
 ... | nothing = case eq of λ ()
 ... | just t with H.phase t
 effect (H.enterHandshake w) s eq | just t | H.maskedSetup = case just-injective eq of λ { refl → same refl }
 effect (H.enterHandshake w) s eq | just t | H.handshaking = case eq of λ ()
 effect (H.enterHandshake w) s eq | just t | (H.caughtCancellation err) = case eq of λ ()
 effect (H.enterHandshake w) s eq | just t | (H.cancellationPublished err) = case eq of λ ()
 effect (H.enterHandshake w) s eq | just t | (H.bodyExited err) = case eq of λ ()
 effect (H.enterHandshake w) s eq | just t | (H.finalizing err) = case eq of λ ()
 effect (H.enterHandshake w) s eq | just t | (H.cleanupComplete err outcome) = case eq of λ ()
 effect (H.enterHandshake w) s eq | just t | (H.resultAvailable err outcome) = case eq of λ ()
 effect (H.deliverHandshakeCancellation w err) s eq = handshake-effect w err s eq
 effect (H.deliverBlockedSetupCancellation w err) s eq = setup-effect w err s eq
 effect (H.publishCaught w) s eq with lookup w (H.threads s) in found
 ... | nothing = case eq of λ ()
 ... | just t with H.phase t
 effect (H.publishCaught w) s eq | just t | H.maskedSetup = case eq of λ ()
 effect (H.publishCaught w) s eq | just t | H.handshaking = case eq of λ ()
 effect (H.publishCaught w) s eq | just t | (H.caughtCancellation err) = dispatch-phase-effect (Machine.handlerPublication w (S.handlerError S.protocolViolation err) Machine.resultWritten) w t (H.cancellationPublished err) s found eq
 effect (H.publishCaught w) s eq | just t | (H.cancellationPublished err) = case eq of λ ()
 effect (H.publishCaught w) s eq | just t | (H.bodyExited err) = case eq of λ ()
 effect (H.publishCaught w) s eq | just t | (H.finalizing err) = case eq of λ ()
 effect (H.publishCaught w) s eq | just t | (H.cleanupComplete err outcome) = case eq of λ ()
 effect (H.publishCaught w) s eq | just t | (H.resultAvailable err outcome) = case eq of λ ()
 effect (H.rethrowCaught w) s eq with lookup w (H.threads s) in found
 ... | nothing = case eq of λ ()
 ... | just t with H.phase t
 effect (H.rethrowCaught w) s eq | just t | H.maskedSetup = case eq of λ ()
 effect (H.rethrowCaught w) s eq | just t | H.handshaking = case eq of λ ()
 effect (H.rethrowCaught w) s eq | just t | (H.caughtCancellation err) = case eq of λ ()
 effect (H.rethrowCaught w) s eq | just t | (H.cancellationPublished err) = case just-injective eq of λ { refl → same refl }
 effect (H.rethrowCaught w) s eq | just t | (H.bodyExited err) = case eq of λ ()
 effect (H.rethrowCaught w) s eq | just t | (H.finalizing err) = case eq of λ ()
 effect (H.rethrowCaught w) s eq | just t | (H.cleanupComplete err outcome) = case eq of λ ()
 effect (H.rethrowCaught w) s eq | just t | (H.resultAvailable err outcome) = case eq of λ ()
 effect (H.enterFinalizer w) s eq with lookup w (H.threads s) in found
 ... | nothing = case eq of λ ()
 ... | just t with H.phase t
 effect (H.enterFinalizer w) s eq | just t | H.maskedSetup = case eq of λ ()
 effect (H.enterFinalizer w) s eq | just t | H.handshaking = case eq of λ ()
 effect (H.enterFinalizer w) s eq | just t | (H.caughtCancellation err) = case eq of λ ()
 effect (H.enterFinalizer w) s eq | just t | (H.cancellationPublished err) = case eq of λ ()
 effect (H.enterFinalizer w) s eq | just t | (H.bodyExited err) = dispatch-phase-effect (Machine.handlerExit w) w t (H.finalizing err) s found eq
 effect (H.enterFinalizer w) s eq | just t | (H.finalizing err) = case eq of λ ()
 effect (H.enterFinalizer w) s eq | just t | (H.cleanupComplete err outcome) = case eq of λ ()
 effect (H.enterFinalizer w) s eq | just t | (H.resultAvailable err outcome) = case eq of λ ()
 effect (H.cleanup w action) s eq with lookup w (H.threads s) in found
 ... | nothing = case eq of λ ()
 ... | just t with H.phase t
 effect (H.cleanup w action) s eq | just t | H.maskedSetup = case eq of λ ()
 effect (H.cleanup w action) s eq | just t | H.handshaking = case eq of λ ()
 effect (H.cleanup w action) s eq | just t | (H.caughtCancellation err) = case eq of λ ()
 effect (H.cleanup w action) s eq | just t | (H.cancellationPublished err) = case eq of λ ()
 effect (H.cleanup w action) s eq | just t | (H.bodyExited err) = case eq of λ ()
 effect (H.cleanup w action) s eq | just t | (H.finalizing err) = dispatch-effect (Machine.cleanupStep w action) s eq
 effect (H.cleanup w action) s eq | just t | (H.cleanupComplete err outcome) = case eq of λ ()
 effect (H.cleanup w action) s eq | just t | (H.resultAvailable err outcome) = case eq of λ ()
 effect (H.finishCleanup w) s eq with lookup w (H.threads s) in found | lookup w (S.cleanups (Machine.world (H.source s)))
 ... | just t | just (S.cleanupDone outcome) with H.phase t
 effect (H.finishCleanup w) s eq | just t | just (S.cleanupDone outcome) | H.maskedSetup = case eq of λ ()
 effect (H.finishCleanup w) s eq | just t | just (S.cleanupDone outcome) | H.handshaking = case eq of λ ()
 effect (H.finishCleanup w) s eq | just t | just (S.cleanupDone outcome) | (H.caughtCancellation err) = case eq of λ ()
 effect (H.finishCleanup w) s eq | just t | just (S.cleanupDone outcome) | (H.cancellationPublished err) = case eq of λ ()
 effect (H.finishCleanup w) s eq | just t | just (S.cleanupDone outcome) | (H.bodyExited err) = case eq of λ ()
 effect (H.finishCleanup w) s eq | just t | just (S.cleanupDone outcome) | (H.finalizing err) = case just-injective eq of λ { refl → same refl }
 effect (H.finishCleanup w) s eq | just t | just (S.cleanupDone outcome) | (H.cleanupComplete err priorOutcome) = case eq of λ ()
 effect (H.finishCleanup w) s eq | just t | just (S.cleanupDone outcome) | (H.resultAvailable err priorOutcome) = case eq of λ ()
 effect (H.finishCleanup w) s eq | nothing | cleanup = case eq of λ ()
 effect (H.finishCleanup w) s eq | just t | nothing = case eq of λ ()
 effect (H.finishCleanup w) s eq | just t | just S.cleanupAcquire = case eq of λ ()
 effect (H.finishCleanup w) s eq | just t | just (S.cleanupSelect capturedLease) = case eq of λ ()
 effect (H.finishCleanup w) s eq | just t | just (S.cleanupClose capturedLease map tail) = case eq of λ ()
 effect (H.finishCleanup w) s eq | just t | just (S.cleanupPublish capturedLease map tail) = case eq of λ ()
 effect (H.finishCleanup w) s eq | just t | just (S.cleanupRestore capturedLease closeError) = case eq of λ ()
 effect (H.finishCleanup w) s eq | just t | just (S.cleanupWaiting captured) = case eq of λ ()
 effect (H.finishCleanup w) s eq | just t | just (S.cleanupFinalize captured outcome) = case eq of λ ()
 effect (H.finishCleanup w) s eq | just t | just (S.cleanupCount outcome) = case eq of λ ()
 effect (H.publishAsyncResult w) s eq with lookup w (H.threads s) in found | lookup w (S.cleanups (Machine.world (H.source s)))
 ... | just t | just (S.cleanupDone outcome) with H.phase t
 effect (H.publishAsyncResult w) s eq | just t | just (S.cleanupDone outcome) | H.maskedSetup = case eq of λ ()
 effect (H.publishAsyncResult w) s eq | just t | just (S.cleanupDone outcome) | H.handshaking = case eq of λ ()
 effect (H.publishAsyncResult w) s eq | just t | just (S.cleanupDone outcome) | (H.caughtCancellation err) = case eq of λ ()
 effect (H.publishAsyncResult w) s eq | just t | just (S.cleanupDone outcome) | (H.cancellationPublished err) = case eq of λ ()
 effect (H.publishAsyncResult w) s eq | just t | just (S.cleanupDone outcome) | (H.bodyExited err) = case eq of λ ()
 effect (H.publishAsyncResult w) s eq | just t | just (S.cleanupDone outcome) | (H.finalizing err) = case eq of λ ()
 effect (H.publishAsyncResult w) s eq | just t | just (S.cleanupDone outcome) | (H.cleanupComplete err observed) = case just-injective eq of λ { refl → same refl }
 effect (H.publishAsyncResult w) s eq | just t | just (S.cleanupDone outcome) | (H.resultAvailable err priorOutcome) = case eq of λ ()
 effect (H.publishAsyncResult w) s eq | nothing | cleanup = case eq of λ ()
 effect (H.publishAsyncResult w) s eq | just t | nothing = case eq of λ ()
 effect (H.publishAsyncResult w) s eq | just t | just S.cleanupAcquire = case eq of λ ()
 effect (H.publishAsyncResult w) s eq | just t | just (S.cleanupSelect capturedLease) = case eq of λ ()
 effect (H.publishAsyncResult w) s eq | just t | just (S.cleanupClose capturedLease map tail) = case eq of λ ()
 effect (H.publishAsyncResult w) s eq | just t | just (S.cleanupPublish capturedLease map tail) = case eq of λ ()
 effect (H.publishAsyncResult w) s eq | just t | just (S.cleanupRestore capturedLease closeError) = case eq of λ ()
 effect (H.publishAsyncResult w) s eq | just t | just (S.cleanupWaiting captured) = case eq of λ ()
 effect (H.publishAsyncResult w) s eq | just t | just (S.cleanupFinalize captured outcome) = case eq of λ ()
 effect (H.publishAsyncResult w) s eq | just t | just (S.cleanupCount outcome) = case eq of λ ()
 effect (H.shutdownStep Close.captureSnapshot) s eq with Close.step (S.cm (Machine.world (H.source s))) (λ w → H.resultReady w s) Close.captureSnapshot (H.shutdown s) in stepped
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → same refl }
 effect (H.shutdownStep Close.readEntry) s eq with Close.step (S.cm (Machine.world (H.source s))) (λ w → H.resultReady w s) Close.readEntry (H.shutdown s) in stepped
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → same refl }
 effect (H.shutdownStep Close.requestCancellation) s eq with Close.step (S.cm (Machine.world (H.source s))) (λ w → H.resultReady w s) Close.requestCancellation (H.shutdown s) in stepped
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → same refl }
 effect (H.shutdownStep Close.finishTraversal) s eq with Close.step (S.cm (Machine.world (H.source s))) (λ w → H.resultReady w s) Close.finishTraversal (H.shutdown s) in stepped
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → same refl }
 effect (H.shutdownStep Close.finishClose) s eq with Close.step (S.cm (Machine.world (H.source s))) (λ w → H.resultReady w s) Close.finishClose (H.shutdown s) in stepped
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → same refl }
 effect (H.shutdownStep Close.acknowledgeDelivery) s ()
 effect (H.deliverShutdownHandshake err) s eq = shutdown-effect false err s eq
 effect (H.deliverShutdownBlockedSetup err) s eq = shutdown-effect true err s eq
 effect (H.deliverShutdownTimeWait err) s eq = timewait-effect err s eq
 effect H.acknowledgeFinished s eq with Close.phase (H.shutdown s) in awaited
 ... | Close.awaitDelivery e w with H.resultReady w s in ready
 ...   | true = acknowledge-effect s eq (same refl)
 ...   | false = case eq of λ ()
 effect H.acknowledgeFinished s eq | Close.initial = case eq of λ ()
 effect H.acknowledgeFinished s eq | Close.reading = case eq of λ ()
 effect H.acknowledgeFinished s eq | Close.sendReady e w = case eq of λ ()
 effect H.acknowledgeFinished s eq | Close.awaitResults = case eq of λ ()
 effect H.acknowledgeFinished s eq | Close.closed = case eq of λ ()
 shutdown-effect blocked err s eq with Close.phase (H.shutdown s) in awaited
 ... | Close.awaitDelivery e w with blocked
 ...   | false with H.deliverHandshake w err s in delivered
 ...     | nothing = case eq of λ ()
 ...     | just next = acknowledge-effect next eq (handshake-effect w err s delivered)
 shutdown-effect blocked err s eq | Close.awaitDelivery e w | true with H.deliverBlockedSetup w err s in delivered
 ...     | nothing = case eq of λ ()
 ...     | just next = acknowledge-effect next eq (setup-effect w err s delivered)
 shutdown-effect blocked err s eq | Close.initial = case eq of λ ()
 shutdown-effect blocked err s eq | Close.reading = case eq of λ ()
 shutdown-effect blocked err s eq | Close.sendReady e w = case eq of λ ()
 shutdown-effect blocked err s eq | Close.awaitResults = case eq of λ ()
 shutdown-effect blocked err s eq | Close.closed = case eq of λ ()
 timewait-effect err s eq with Close.phase (H.shutdown s) in awaited
 ... | Close.awaitDelivery e w with lookup w (H.threads s) in found | lookup w (S.cleanups (Machine.world (H.source s)))
 ...   | just t | just (S.cleanupWaiting captured) with H.phase t
 ...     | H.finalizing original with H.dispatch (Machine.cleanupStep w (Cleanup.interruptTimeWait err)) s in advanced
 ...       | nothing = case eq of λ ()
 ...       | just next = acknowledge-effect next eq (dispatch-effect (Machine.cleanupStep w (Cleanup.interruptTimeWait err)) s advanced)
 timewait-effect err s eq | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | H.maskedSetup = case eq of λ ()
 timewait-effect err s eq | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | H.handshaking = case eq of λ ()
 timewait-effect err s eq | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | (H.caughtCancellation priorError) = case eq of λ ()
 timewait-effect err s eq | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | (H.cancellationPublished priorError) = case eq of λ ()
 timewait-effect err s eq | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | (H.bodyExited priorError) = case eq of λ ()
 timewait-effect err s eq | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | (H.cleanupComplete priorError outcome) = case eq of λ ()
 timewait-effect err s eq | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | (H.resultAvailable priorError outcome) = case eq of λ ()
 timewait-effect err s eq | Close.awaitDelivery e w | just t | just S.cleanupAcquire = case eq of λ ()
 timewait-effect err s eq | Close.awaitDelivery e w | just t | just (S.cleanupSelect capturedLease) = case eq of λ ()
 timewait-effect err s eq | Close.awaitDelivery e w | just t | just (S.cleanupClose capturedLease map tail) = case eq of λ ()
 timewait-effect err s eq | Close.awaitDelivery e w | just t | just (S.cleanupPublish capturedLease map tail) = case eq of λ ()
 timewait-effect err s eq | Close.awaitDelivery e w | just t | just (S.cleanupRestore capturedLease closeError) = case eq of λ ()
 timewait-effect err s eq | Close.awaitDelivery e w | just t | just (S.cleanupFinalize captured outcome) = case eq of λ ()
 timewait-effect err s eq | Close.awaitDelivery e w | just t | just (S.cleanupCount outcome) = case eq of λ ()
 timewait-effect err s eq | Close.awaitDelivery e w | just t | just (S.cleanupDone outcome) = case eq of λ ()
 timewait-effect err s eq | Close.awaitDelivery e w | nothing | cleanup = case eq of λ ()
 timewait-effect err s eq | Close.awaitDelivery e w | just t | nothing = case eq of λ ()
 timewait-effect err s eq | Close.initial = case eq of λ ()
 timewait-effect err s eq | Close.reading = case eq of λ ()
 timewait-effect err s eq | (Close.sendReady e w) = case eq of λ ()
 timewait-effect err s eq | Close.awaitResults = case eq of λ ()
 timewait-effect err s eq | Close.closed = case eq of λ ()

module Physical where
 fork-effect : ∀ w s {t} → B.forkOutbound w s ≡ just t → Effect (O.core (B.source s)) (O.core (B.source t))
 fork-effect w s eq with lookup w (O.acquiring (B.source s))
 ... | nothing = case eq of λ ()
 ... | just f with B.freshChild (Acquire.child (Acquire.req f)) s
 ...   | false = case eq of λ ()
 ...   | true with O.advance (O.acquire w Acquire.forkOK) (B.source s) in actual
 ...     | nothing = case eq of λ ()
 ...     | just c with lookup (Acquire.child (Acquire.req f)) (S.handlers (Machine.world (O.core c)))
 ...       | nothing = case eq of λ ()
 ...       | just child = case just-injective eq of λ { refl → outbound-effect (O.acquire w Acquire.forkOK) (B.source s) actual }
 effect : ∀ a s {t} → B.step a s ≡ just t → Effect (O.core (B.source s)) (O.core (B.source t))
 effect (B.handler a) s eq with B.handlerAllowed a s
 ... | false = case eq of λ ()
 ... | true with H.step a (B.view s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just h = case just-injective eq of λ { refl → Raw.effect a (B.view s) actual }
 effect (B.outbound a) s eq with B.forkCaller a
 ... | just w = fork-effect w s eq
 ... | nothing with B.outboundAllowed a s
 ...   | false = case eq of λ ()
 ...   | true with O.advance a (B.source s) in actual
 ...     | nothing = case eq of λ ()
 ...     | just c = case just-injective eq of λ { refl → outbound-effect a (B.source s) actual }
