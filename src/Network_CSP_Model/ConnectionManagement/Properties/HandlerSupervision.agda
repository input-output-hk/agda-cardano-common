{-# OPTIONS --guardedness #-}

-- Actual dispatcher/coordinator projections of the bounded physical-handler
-- profile. Completion concerns its fixed snapshot and observed Async results,
-- not successful socket close or a census of every historical handler.
module ConnectionManagement.Properties.HandlerSupervision where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; sym; trans)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.Entries using (lookup-put)
import Data.List.Relation.Unary.All
import ConnectionManagement.State as S
import ConnectionManagement.Machine as M
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Properties.CMShutdown as CloseProof
import ConnectionManagement.Properties.SupplyInvariant as Supply
import ConnectionManagement.Properties.MapUniqueInvariant as Maps
import ConnectionManagement.Properties.OwnershipInvariant as Ownership
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)
import ConnectionManagement.Properties.StateMapUniqueness as MapPredicate
import ConnectionManagement.Properties.Ownership as OwnPredicate

-- Retain the concrete wrapper transition whose oracle was read by the wait.
record PhysicalWait (coordinator : Close.State) : Set where
  constructor physicalWait
  field
    before after : H.State
    actual-step : H.step (H.shutdownStep Close.finishClose) before ≡ just after
    same-coordinator : H.shutdown after ≡ coordinator
    primitive-wait : CloseProof.FinalWait coordinator
    physical-oracle : CloseProof.available primitive-wait ≡ (λ w → H.resultReady w before)
    actual-observation : CloseProof.Observed (λ w → H.resultReady w before) (H.shutdown after)
open PhysicalWait public
LastValid : Close.State → Set
LastValid c = Close.phase c ≡ Close.closed → PhysicalWait c

MTrace : M.Configuration → M.Configuration → Set
MTrace p q = Σ (List M.Action) (λ as → M.Executes p as q)
CTrace : Close.State → Close.State → Set
CTrace p q = Σ (List Close.Action) (λ as → Close.Executes p as q)
record Paths (before after : H.State) : Set where
  constructor paths
  field
    machine : MTrace (H.source before) (H.source after)
    coordinator : CTrace (H.shutdown before) (H.shutdown after)
    last-wait : LastValid (H.shutdown before) → LastValid (H.shutdown after)
open Paths public
idle : ∀ s → Paths s s
idle s = paths ([] , M.done) ([] , Close.done) (λ witness → witness)

append-close : ∀ {p as q bs r} → Close.Executes p as q → Close.Executes q bs r → Close.Executes p (as ++ bs) r
append-close Close.done tail = tail
append-close (Close.next eq path) tail = Close.next eq (append-close path tail)
compose : ∀ {p q r} → Paths p q → Paths q r → Paths p r
compose (paths (as , mp) (cs , cp) witness) (paths (bs , mq) (ds , cq) next) =
  paths (as ++ bs , M.exec-append mp mq) (cs ++ ds , append-close cp cq) (λ valid → next (witness valid))

-- An action other than the final wait never creates the closed cursor.
not-final-close : ∀ current available action before {after} →
  Close.step current available action before ≡ just after → action ≢ Close.finishClose →
  Close.phase after ≡ Close.closed → ⊥
not-final-close current available Close.finishClose before eq notFinal closed = notFinal refl
not-final-close current available Close.captureSnapshot (Close.shutdownState Close.initial snap rest workers) eq notFinal closed with S.mapCell current
... | S.taken owner = case eq of λ ()
... | S.full map = case just-injective eq of λ { refl → case closed of λ () }
not-final-close current available Close.readEntry (Close.shutdownState Close.reading snap [] workers) eq notFinal closed = case eq of λ ()
not-final-close current available Close.readEntry (Close.shutdownState Close.reading snap (e ∷ rest) workers) eq notFinal closed with lookup e (S.entries current)
... | nothing = case eq of λ ()
... | just state with Close.getConnThread state
...   | nothing = case just-injective eq of λ { refl → case closed of λ () }
...   | just w = case just-injective eq of λ { refl → case closed of λ () }
not-final-close current available Close.requestCancellation (Close.shutdownState (Close.sendReady e w) snap rest workers) eq notFinal closed =
  case just-injective eq of λ { refl → case closed of λ () }
not-final-close current available Close.acknowledgeDelivery (Close.shutdownState (Close.awaitDelivery e w) snap rest workers) eq notFinal closed =
  case just-injective eq of λ { refl → case closed of λ () }
not-final-close current available Close.finishTraversal (Close.shutdownState Close.reading snap [] workers) eq notFinal closed =
  case just-injective eq of λ { refl → case closed of λ () }
not-final-close current available Close.finishTraversal (Close.shutdownState Close.reading snap (e ∷ rest) workers) eq notFinal closed = case eq of λ ()
not-final-close current available Close.captureSnapshot (Close.shutdownState Close.reading snap rest workers) eq notFinal closed = case eq of λ ()
not-final-close current available Close.captureSnapshot (Close.shutdownState (Close.sendReady e w) snap rest workers) eq notFinal closed = case eq of λ ()
not-final-close current available Close.captureSnapshot (Close.shutdownState (Close.awaitDelivery e w) snap rest workers) eq notFinal closed = case eq of λ ()
not-final-close current available Close.captureSnapshot (Close.shutdownState Close.awaitResults snap rest workers) eq notFinal closed = case eq of λ ()
not-final-close current available Close.captureSnapshot (Close.shutdownState Close.closed snap rest workers) eq notFinal closed = case eq of λ ()
not-final-close current available Close.readEntry (Close.shutdownState Close.initial snap rest workers) eq notFinal closed = case eq of λ ()
not-final-close current available Close.readEntry (Close.shutdownState (Close.sendReady e w) snap rest workers) eq notFinal closed = case eq of λ ()
not-final-close current available Close.readEntry (Close.shutdownState (Close.awaitDelivery e w) snap rest workers) eq notFinal closed = case eq of λ ()
not-final-close current available Close.readEntry (Close.shutdownState Close.awaitResults snap rest workers) eq notFinal closed = case eq of λ ()
not-final-close current available Close.readEntry (Close.shutdownState Close.closed snap rest workers) eq notFinal closed = case eq of λ ()
not-final-close current available Close.requestCancellation (Close.shutdownState Close.initial snap rest workers) eq notFinal closed = case eq of λ ()
not-final-close current available Close.requestCancellation (Close.shutdownState Close.reading snap rest workers) eq notFinal closed = case eq of λ ()
not-final-close current available Close.requestCancellation (Close.shutdownState (Close.awaitDelivery e w) snap rest workers) eq notFinal closed = case eq of λ ()
not-final-close current available Close.requestCancellation (Close.shutdownState Close.awaitResults snap rest workers) eq notFinal closed = case eq of λ ()
not-final-close current available Close.requestCancellation (Close.shutdownState Close.closed snap rest workers) eq notFinal closed = case eq of λ ()
not-final-close current available Close.acknowledgeDelivery (Close.shutdownState Close.initial snap rest workers) eq notFinal closed = case eq of λ ()
not-final-close current available Close.acknowledgeDelivery (Close.shutdownState Close.reading snap rest workers) eq notFinal closed = case eq of λ ()
not-final-close current available Close.acknowledgeDelivery (Close.shutdownState (Close.sendReady e w) snap rest workers) eq notFinal closed = case eq of λ ()
not-final-close current available Close.acknowledgeDelivery (Close.shutdownState Close.awaitResults snap rest workers) eq notFinal closed = case eq of λ ()
not-final-close current available Close.acknowledgeDelivery (Close.shutdownState Close.closed snap rest workers) eq notFinal closed = case eq of λ ()
not-final-close current available Close.finishTraversal (Close.shutdownState Close.initial snap rest workers) eq notFinal closed = case eq of λ ()
not-final-close current available Close.finishTraversal (Close.shutdownState (Close.sendReady e w) snap rest workers) eq notFinal closed = case eq of λ ()
not-final-close current available Close.finishTraversal (Close.shutdownState (Close.awaitDelivery e w) snap rest workers) eq notFinal closed = case eq of λ ()
not-final-close current available Close.finishTraversal (Close.shutdownState Close.awaitResults snap rest workers) eq notFinal closed = case eq of λ ()
not-final-close current available Close.finishTraversal (Close.shutdownState Close.closed snap rest workers) eq notFinal closed = case eq of λ ()

-- Transparent dispatch helpers retain actual writes and erase only metadata.
dispatch-paths : ∀ action s {s′} → H.dispatch action s ≡ just s′ → Paths s s′
dispatch-paths action s eq with M.advance action (H.source s) in advanced
... | nothing = case eq of λ ()
... | just c = case just-injective eq of λ { refl → paths (action ∷ [] , M.next advanced M.done) ([] , Close.done) (λ witness → witness) }
dispatch-phase-paths : ∀ action w t phase s {s′} → H.dispatchPhase action w t phase s ≡ just s′ → Paths s s′
dispatch-phase-paths action w t phase s eq with M.advance action (H.source s) in advanced
... | nothing = case eq of λ ()
... | just c = case just-injective eq of λ { refl → paths (action ∷ [] , M.next advanced M.done) ([] , Close.done) (λ witness → witness) }
acknowledge-paths : ∀ s {s′} → H.acknowledge s ≡ just s′ → Paths s s′
acknowledge-paths s eq with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s)
  Close.acknowledgeDelivery (H.shutdown s) in advanced
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl →
  paths ([] , M.done) (Close.acknowledgeDelivery ∷ [] , Close.next {current = S.cm (M.world (H.source s))} {available = λ w → H.resultReady w s} advanced Close.done)
    (λ witness closed → ⊥-elim (not-final-close (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.acknowledgeDelivery (H.shutdown s) advanced (λ ()) closed)) }

fork-paths : ∀ w s {s′} → H.forkAdmission w s ≡ just s′ → Paths s s′
fork-paths w s eq with lookup w (S.admissions (M.world (H.source s)))
... | nothing = case eq of λ ()
... | just a with lookup (S.child (S.request a)) (H.threads s)
...   | just old = case eq of λ ()
...   | nothing with M.advance (M.admissionStep w Server.fork) (H.source s) in advanced
...     | nothing = case eq of λ ()
...     | just c with lookup (S.child (S.request a)) (S.handlers (M.world c))
...       | nothing = case eq of λ ()
...       | just handler = case just-injective eq of λ { refl →
  paths (M.admissionStep w Server.fork ∷ [] , M.next advanced M.done) ([] , Close.done) (λ witness → witness) }

handshake-delivery-paths : ∀ w error s {s′} → H.deliverHandshake w error s ≡ just s′ → Paths s s′
handshake-delivery-paths w error s eq with lookup w (H.threads s)
... | nothing = case eq of λ ()
... | just t with H.phase t
handshake-delivery-paths w error s eq | just t | H.maskedSetup = case eq of λ ()
handshake-delivery-paths w error s eq | just t | H.handshaking = case just-injective eq of λ { refl → paths ([] , M.done) ([] , Close.done) (λ witness → witness) }
handshake-delivery-paths w error s eq | just t | (H.caughtCancellation err) = case eq of λ ()
handshake-delivery-paths w error s eq | just t | (H.cancellationPublished err) = case eq of λ ()
handshake-delivery-paths w error s eq | just t | (H.bodyExited err) = case eq of λ ()
handshake-delivery-paths w error s eq | just t | (H.finalizing err) = case eq of λ ()
handshake-delivery-paths w error s eq | just t | (H.cleanupComplete err outcome) = case eq of λ ()
handshake-delivery-paths w error s eq | just t | (H.resultAvailable err outcome) = case eq of λ ()

setup-delivery-paths : ∀ w error s {s′} → H.deliverBlockedSetup w error s ≡ just s′ → Paths s s′
setup-delivery-paths w error s eq with lookup w (H.threads s)
... | nothing = case eq of λ ()
... | just t with H.phase t
setup-delivery-paths w error s eq | just t | H.maskedSetup = case just-injective eq of λ { refl → paths ([] , M.done) ([] , Close.done) (λ witness → witness) }
setup-delivery-paths w error s eq | just t | H.handshaking = case eq of λ ()
setup-delivery-paths w error s eq | just t | (H.caughtCancellation err) = case eq of λ ()
setup-delivery-paths w error s eq | just t | (H.cancellationPublished err) = case eq of λ ()
setup-delivery-paths w error s eq | just t | (H.bodyExited err) = case eq of λ ()
setup-delivery-paths w error s eq | just t | (H.finalizing err) = case eq of λ ()
setup-delivery-paths w error s eq | just t | (H.cleanupComplete err outcome) = case eq of λ ()
setup-delivery-paths w error s eq | just t | (H.resultAvailable err outcome) = case eq of λ ()

shutdown-delivery-paths : ∀ blocked err s {s′} → H.deliverShutdown blocked err s ≡ just s′ → Paths s s′
shutdown-delivery-paths blocked err s eq with Close.phase (H.shutdown s)
... | Close.awaitDelivery e w with blocked
...   | false with H.deliverHandshake w err s in delivered
...     | nothing = case eq of λ ()
...     | just next = compose (handshake-delivery-paths w err s delivered) (acknowledge-paths next eq)
shutdown-delivery-paths blocked err s eq | Close.awaitDelivery e w | true with H.deliverBlockedSetup w err s in delivered
... | nothing = case eq of λ ()
... | just next = compose (setup-delivery-paths w err s delivered) (acknowledge-paths next eq)
shutdown-delivery-paths blocked err s eq | Close.initial = case eq of λ ()
shutdown-delivery-paths blocked err s eq | Close.reading = case eq of λ ()
shutdown-delivery-paths blocked err s eq | (Close.sendReady e w) = case eq of λ ()
shutdown-delivery-paths blocked err s eq | Close.awaitResults = case eq of λ ()
shutdown-delivery-paths blocked err s eq | Close.closed = case eq of λ ()

timewait-delivery-paths : ∀ err s {s′} → H.deliverTimeWait err s ≡ just s′ → Paths s s′
timewait-delivery-paths err s eq with Close.phase (H.shutdown s)
... | Close.awaitDelivery e w with lookup w (H.threads s) | lookup w (S.cleanups (M.world (H.source s)))
...   | just t | just (S.cleanupWaiting captured) with H.phase t
...     | H.finalizing original with H.dispatch (M.cleanupStep w (Cleanup.interruptTimeWait err)) s in advanced
...       | nothing = case eq of λ ()
...       | just next = compose (dispatch-paths (M.cleanupStep w (Cleanup.interruptTimeWait err)) s advanced) (acknowledge-paths next eq)
timewait-delivery-paths err s eq | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | H.maskedSetup = case eq of λ ()
timewait-delivery-paths err s eq | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | H.handshaking = case eq of λ ()
timewait-delivery-paths err s eq | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | (H.caughtCancellation priorError) = case eq of λ ()
timewait-delivery-paths err s eq | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | (H.cancellationPublished priorError) = case eq of λ ()
timewait-delivery-paths err s eq | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | (H.bodyExited priorError) = case eq of λ ()
timewait-delivery-paths err s eq | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | (H.cleanupComplete priorError outcome) = case eq of λ ()
timewait-delivery-paths err s eq | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | (H.resultAvailable priorError outcome) = case eq of λ ()
timewait-delivery-paths err s eq | Close.awaitDelivery e w | just t | just S.cleanupAcquire = case eq of λ ()
timewait-delivery-paths err s eq | Close.awaitDelivery e w | just t | just (S.cleanupSelect capturedLease) = case eq of λ ()
timewait-delivery-paths err s eq | Close.awaitDelivery e w | just t | just (S.cleanupClose capturedLease map tail) = case eq of λ ()
timewait-delivery-paths err s eq | Close.awaitDelivery e w | just t | just (S.cleanupPublish capturedLease map tail) = case eq of λ ()
timewait-delivery-paths err s eq | Close.awaitDelivery e w | just t | just (S.cleanupRestore capturedLease closeError) = case eq of λ ()
timewait-delivery-paths err s eq | Close.awaitDelivery e w | just t | just (S.cleanupFinalize captured outcome) = case eq of λ ()
timewait-delivery-paths err s eq | Close.awaitDelivery e w | just t | just (S.cleanupCount outcome) = case eq of λ ()
timewait-delivery-paths err s eq | Close.awaitDelivery e w | just t | just (S.cleanupDone outcome) = case eq of λ ()
timewait-delivery-paths err s eq | Close.awaitDelivery e w | nothing | cleanup = case eq of λ ()
timewait-delivery-paths err s eq | Close.awaitDelivery e w | just t | nothing = case eq of λ ()
timewait-delivery-paths err s eq | Close.initial = case eq of λ ()
timewait-delivery-paths err s eq | Close.reading = case eq of λ ()
timewait-delivery-paths err s eq | (Close.sendReady e w) = case eq of λ ()
timewait-delivery-paths err s eq | Close.awaitResults = case eq of λ ()
timewait-delivery-paths err s eq | Close.closed = case eq of λ ()

-- The final wait uses the actual source map and the captured physical table.
-- The wrapper step, not merely a primitive oracle function, is retained.
shutdown-computation : ∀ s {next} → Close.step (S.cm (M.world (H.source s)))
  (λ w → H.resultReady w s) Close.finishClose (H.shutdown s) ≡ just next →
  H.step (H.shutdownStep Close.finishClose) s ≡ just (record s { shutdown = next })
shutdown-computation s eq rewrite eq = refl

finish-guards : ∀ current available before {after} →
  Close.step current available Close.finishClose before ≡ just after →
  Close.phase before ≡ Close.awaitResults ×
  Close.allAvailable available (Close.collected before) ≡ true × Close.collected after ≡ Close.collected before
finish-guards current available (Close.shutdownState Close.awaitResults snap rest workers) eq with Close.allAvailable available workers in ready
... | false = case eq of λ ()
... | true = case just-injective eq of λ { refl → refl , refl , refl }
finish-guards current available (Close.shutdownState Close.initial snap rest workers) eq = case eq of λ ()
finish-guards current available (Close.shutdownState Close.reading snap rest workers) eq = case eq of λ ()
finish-guards current available (Close.shutdownState (Close.sendReady e w) snap rest workers) eq = case eq of λ ()
finish-guards current available (Close.shutdownState (Close.awaitDelivery e w) snap rest workers) eq = case eq of λ ()
finish-guards current available (Close.shutdownState Close.closed snap rest workers) eq = case eq of λ ()

-- The oracle is a constructor field here, so its identity is retained directly;
-- no extensional equality or interpretation of an arbitrary oracle is needed.
make-wait : ∀ current available before {after} →
  Close.step current available Close.finishClose before ≡ just after → CloseProof.FinalWait after
make-wait current available before eq = CloseProof.finalWait before current available
  (proj₁ (finish-guards current available before eq)) eq
  (proj₂ (proj₂ (finish-guards current available before eq)))
  (subst (λ workers → Data.List.Relation.Unary.All.All (λ w → available w ≡ true) workers)
    (sym (proj₂ (proj₂ (finish-guards current available before eq))))
    (CloseProof.all-observed available (Close.collected before) (proj₁ (proj₂ (finish-guards current available before eq)))))

shutdown-paths : ∀ action s {s′} → H.step (H.shutdownStep action) s ≡ just s′ → Paths s s′
shutdown-paths Close.acknowledgeDelivery s eq = case eq of λ ()
shutdown-paths Close.captureSnapshot s eq with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.captureSnapshot (H.shutdown s) in advanced
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl →
  paths ([] , M.done) (Close.captureSnapshot ∷ [] , Close.next {current = S.cm (M.world (H.source s))} {available = λ w → H.resultReady w s} advanced Close.done)
    (λ witness closed → ⊥-elim (not-final-close (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.captureSnapshot (H.shutdown s) advanced (λ ()) closed)) }
shutdown-paths Close.readEntry s eq with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.readEntry (H.shutdown s) in advanced
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl →
  paths ([] , M.done) (Close.readEntry ∷ [] , Close.next {current = S.cm (M.world (H.source s))} {available = λ w → H.resultReady w s} advanced Close.done)
    (λ witness closed → ⊥-elim (not-final-close (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.readEntry (H.shutdown s) advanced (λ ()) closed)) }
shutdown-paths Close.requestCancellation s eq with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.requestCancellation (H.shutdown s) in advanced
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl →
  paths ([] , M.done) (Close.requestCancellation ∷ [] , Close.next {current = S.cm (M.world (H.source s))} {available = λ w → H.resultReady w s} advanced Close.done)
    (λ witness closed → ⊥-elim (not-final-close (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.requestCancellation (H.shutdown s) advanced (λ ()) closed)) }
shutdown-paths Close.finishTraversal s eq with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.finishTraversal (H.shutdown s) in advanced
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl →
  paths ([] , M.done) (Close.finishTraversal ∷ [] , Close.next {current = S.cm (M.world (H.source s))} {available = λ w → H.resultReady w s} advanced Close.done)
    (λ witness closed → ⊥-elim (not-final-close (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.finishTraversal (H.shutdown s) advanced (λ ()) closed)) }
shutdown-paths Close.finishClose s eq with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.finishClose (H.shutdown s) in advanced
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl →
  paths ([] , M.done) (Close.finishClose ∷ [] , Close.next {current = S.cm (M.world (H.source s))} {available = λ w → H.resultReady w s} advanced Close.done)
    (λ witness closed → physicalWait s (record s { shutdown = next })
      (shutdown-computation s advanced) refl
      (make-wait (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) (H.shutdown s) advanced)
      refl
      (CloseProof.observed-at-wait (make-wait (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) (H.shutdown s) advanced))) }

step-projects : ∀ action s {s′} → H.step action s ≡ just s′ → Paths s s′
step-projects (H.run (M.admissionStep w Server.fork)) s eq = fork-paths w s eq
step-projects (H.run (M.admissionStep w Server.take)) s eq = dispatch-paths (M.admissionStep w Server.take) s eq
step-projects (H.run (M.admissionStep w Server.countLimit)) s eq = dispatch-paths (M.admissionStep w Server.countLimit) s eq
step-projects (H.run (M.admissionStep w Server.allocatePromise)) s eq = dispatch-paths (M.admissionStep w Server.allocatePromise) s eq
step-projects (H.run (M.admissionStep w Server.chooseEntry)) s eq = dispatch-paths (M.admissionStep w Server.chooseEntry) s eq
step-projects (H.run (M.admissionStep w Server.putMapBack)) s eq = dispatch-paths (M.admissionStep w Server.putMapBack) s eq
step-projects (H.run (M.admissionStep w Server.readCounters)) s eq = dispatch-paths (M.admissionStep w Server.readCounters) s eq
step-projects (H.run (M.admissionStep w Server.restore)) s eq = dispatch-paths (M.admissionStep w Server.restore) s eq
step-projects (H.run (M.admissionStep w Server.close)) s eq = dispatch-paths (M.admissionStep w Server.close) s eq
step-projects (H.run (M.admissionStep w Server.failFork)) s eq = dispatch-paths (M.admissionStep w Server.failFork) s eq
step-projects (H.run (M.handshakeStep w a)) s eq = dispatch-paths (M.handshakeStep w a) s eq
step-projects (H.run (M.handlerPublication w result outcome)) s eq = case eq of λ ()
step-projects (H.run (M.handlerExit w)) s eq = case eq of λ ()
step-projects (H.run (M.handlerStep w a)) s eq = case eq of λ ()
step-projects (H.run (M.cleanupStep w a)) s eq = case eq of λ ()
step-projects (H.run (M.igStep a)) s eq = dispatch-paths (M.igStep a) s eq
step-projects (H.run (M.remoteStep a)) s eq with H.rawAllowed (M.remoteStep a)
... | false = case eq of λ ()
... | true = dispatch-paths (M.remoteStep a) s eq
step-projects (H.run (M.releaseStep a)) s eq with H.rawAllowed (M.releaseStep a)
... | false = case eq of λ ()
... | true = dispatch-paths (M.releaseStep a) s eq
step-projects (H.enterHandshake w) s eq with lookup w (H.threads s)
... | nothing = case eq of λ ()
... | just t with H.phase t
step-projects (H.enterHandshake w) s eq | just t | H.maskedSetup = case just-injective eq of λ { refl → paths ([] , M.done) ([] , Close.done) (λ witness → witness) }
step-projects (H.enterHandshake w) s eq | just t | H.handshaking = case eq of λ ()
step-projects (H.enterHandshake w) s eq | just t | (H.caughtCancellation err) = case eq of λ ()
step-projects (H.enterHandshake w) s eq | just t | (H.cancellationPublished err) = case eq of λ ()
step-projects (H.enterHandshake w) s eq | just t | (H.bodyExited err) = case eq of λ ()
step-projects (H.enterHandshake w) s eq | just t | (H.finalizing err) = case eq of λ ()
step-projects (H.enterHandshake w) s eq | just t | (H.cleanupComplete err outcome) = case eq of λ ()
step-projects (H.enterHandshake w) s eq | just t | (H.resultAvailable err outcome) = case eq of λ ()
step-projects (H.deliverHandshakeCancellation w err) s eq = handshake-delivery-paths w err s eq
step-projects (H.deliverBlockedSetupCancellation w err) s eq = setup-delivery-paths w err s eq
step-projects (H.publishCaught w) s eq with lookup w (H.threads s)
... | nothing = case eq of λ ()
... | just t with H.phase t
step-projects (H.publishCaught w) s eq | just t | H.maskedSetup = case eq of λ ()
step-projects (H.publishCaught w) s eq | just t | H.handshaking = case eq of λ ()
step-projects (H.publishCaught w) s eq | just t | (H.caughtCancellation err) = dispatch-phase-paths (M.handlerPublication w (S.handlerError S.protocolViolation err) M.resultWritten) w t (H.cancellationPublished err) s eq
step-projects (H.publishCaught w) s eq | just t | (H.cancellationPublished err) = case eq of λ ()
step-projects (H.publishCaught w) s eq | just t | (H.bodyExited err) = case eq of λ ()
step-projects (H.publishCaught w) s eq | just t | (H.finalizing err) = case eq of λ ()
step-projects (H.publishCaught w) s eq | just t | (H.cleanupComplete err outcome) = case eq of λ ()
step-projects (H.publishCaught w) s eq | just t | (H.resultAvailable err outcome) = case eq of λ ()
step-projects (H.rethrowCaught w) s eq with lookup w (H.threads s)
... | nothing = case eq of λ ()
... | just t with H.phase t
step-projects (H.rethrowCaught w) s eq | just t | H.maskedSetup = case eq of λ ()
step-projects (H.rethrowCaught w) s eq | just t | H.handshaking = case eq of λ ()
step-projects (H.rethrowCaught w) s eq | just t | (H.caughtCancellation err) = case eq of λ ()
step-projects (H.rethrowCaught w) s eq | just t | (H.cancellationPublished err) = case just-injective eq of λ { refl → paths ([] , M.done) ([] , Close.done) (λ witness → witness) }
step-projects (H.rethrowCaught w) s eq | just t | (H.bodyExited err) = case eq of λ ()
step-projects (H.rethrowCaught w) s eq | just t | (H.finalizing err) = case eq of λ ()
step-projects (H.rethrowCaught w) s eq | just t | (H.cleanupComplete err outcome) = case eq of λ ()
step-projects (H.rethrowCaught w) s eq | just t | (H.resultAvailable err outcome) = case eq of λ ()
step-projects (H.enterFinalizer w) s eq with lookup w (H.threads s)
... | nothing = case eq of λ ()
... | just t with H.phase t
step-projects (H.enterFinalizer w) s eq | just t | H.maskedSetup = case eq of λ ()
step-projects (H.enterFinalizer w) s eq | just t | H.handshaking = case eq of λ ()
step-projects (H.enterFinalizer w) s eq | just t | (H.caughtCancellation err) = case eq of λ ()
step-projects (H.enterFinalizer w) s eq | just t | (H.cancellationPublished err) = case eq of λ ()
step-projects (H.enterFinalizer w) s eq | just t | (H.bodyExited err) = dispatch-phase-paths (M.handlerExit w) w t (H.finalizing err) s eq
step-projects (H.enterFinalizer w) s eq | just t | (H.finalizing err) = case eq of λ ()
step-projects (H.enterFinalizer w) s eq | just t | (H.cleanupComplete err outcome) = case eq of λ ()
step-projects (H.enterFinalizer w) s eq | just t | (H.resultAvailable err outcome) = case eq of λ ()
step-projects (H.cleanup w action) s eq with lookup w (H.threads s)
... | nothing = case eq of λ ()
... | just t with H.phase t
step-projects (H.cleanup w action) s eq | just t | H.maskedSetup = case eq of λ ()
step-projects (H.cleanup w action) s eq | just t | H.handshaking = case eq of λ ()
step-projects (H.cleanup w action) s eq | just t | (H.caughtCancellation err) = case eq of λ ()
step-projects (H.cleanup w action) s eq | just t | (H.cancellationPublished err) = case eq of λ ()
step-projects (H.cleanup w action) s eq | just t | (H.bodyExited err) = case eq of λ ()
step-projects (H.cleanup w action) s eq | just t | (H.finalizing err) = dispatch-paths (M.cleanupStep w action) s eq
step-projects (H.cleanup w action) s eq | just t | (H.cleanupComplete err outcome) = case eq of λ ()
step-projects (H.cleanup w action) s eq | just t | (H.resultAvailable err outcome) = case eq of λ ()
step-projects (H.finishCleanup w) s eq with lookup w (H.threads s) | lookup w (S.cleanups (M.world (H.source s)))
... | just t | just (S.cleanupDone outcome) with H.phase t
step-projects (H.finishCleanup w) s eq | just t | just (S.cleanupDone outcome) | H.maskedSetup = case eq of λ ()
step-projects (H.finishCleanup w) s eq | just t | just (S.cleanupDone outcome) | H.handshaking = case eq of λ ()
step-projects (H.finishCleanup w) s eq | just t | just (S.cleanupDone outcome) | (H.caughtCancellation err) = case eq of λ ()
step-projects (H.finishCleanup w) s eq | just t | just (S.cleanupDone outcome) | (H.cancellationPublished err) = case eq of λ ()
step-projects (H.finishCleanup w) s eq | just t | just (S.cleanupDone outcome) | (H.bodyExited err) = case eq of λ ()
step-projects (H.finishCleanup w) s eq | just t | just (S.cleanupDone outcome) | (H.finalizing err) = case just-injective eq of λ { refl → paths ([] , M.done) ([] , Close.done) (λ witness → witness) }
step-projects (H.finishCleanup w) s eq | just t | just (S.cleanupDone outcome) | (H.cleanupComplete err priorOutcome) = case eq of λ ()
step-projects (H.finishCleanup w) s eq | just t | just (S.cleanupDone outcome) | (H.resultAvailable err priorOutcome) = case eq of λ ()
step-projects (H.finishCleanup w) s eq | nothing | cleanup = case eq of λ ()
step-projects (H.finishCleanup w) s eq | just t | nothing = case eq of λ ()
step-projects (H.finishCleanup w) s eq | just t | just S.cleanupAcquire = case eq of λ ()
step-projects (H.finishCleanup w) s eq | just t | just (S.cleanupSelect capturedLease) = case eq of λ ()
step-projects (H.finishCleanup w) s eq | just t | just (S.cleanupClose capturedLease map tail) = case eq of λ ()
step-projects (H.finishCleanup w) s eq | just t | just (S.cleanupPublish capturedLease map tail) = case eq of λ ()
step-projects (H.finishCleanup w) s eq | just t | just (S.cleanupRestore capturedLease closeError) = case eq of λ ()
step-projects (H.finishCleanup w) s eq | just t | just (S.cleanupWaiting captured) = case eq of λ ()
step-projects (H.finishCleanup w) s eq | just t | just (S.cleanupFinalize captured outcome) = case eq of λ ()
step-projects (H.finishCleanup w) s eq | just t | just (S.cleanupCount outcome) = case eq of λ ()
step-projects (H.publishAsyncResult w) s eq with lookup w (H.threads s) | lookup w (S.cleanups (M.world (H.source s)))
... | just t | just (S.cleanupDone outcome) with H.phase t
step-projects (H.publishAsyncResult w) s eq | just t | just (S.cleanupDone outcome) | H.maskedSetup = case eq of λ ()
step-projects (H.publishAsyncResult w) s eq | just t | just (S.cleanupDone outcome) | H.handshaking = case eq of λ ()
step-projects (H.publishAsyncResult w) s eq | just t | just (S.cleanupDone outcome) | (H.caughtCancellation err) = case eq of λ ()
step-projects (H.publishAsyncResult w) s eq | just t | just (S.cleanupDone outcome) | (H.cancellationPublished err) = case eq of λ ()
step-projects (H.publishAsyncResult w) s eq | just t | just (S.cleanupDone outcome) | (H.bodyExited err) = case eq of λ ()
step-projects (H.publishAsyncResult w) s eq | just t | just (S.cleanupDone outcome) | (H.finalizing err) = case eq of λ ()
step-projects (H.publishAsyncResult w) s eq | just t | just (S.cleanupDone outcome) | (H.cleanupComplete err observed) = case just-injective eq of λ { refl → paths ([] , M.done) ([] , Close.done) (λ witness → witness) }
step-projects (H.publishAsyncResult w) s eq | just t | just (S.cleanupDone outcome) | (H.resultAvailable err priorOutcome) = case eq of λ ()
step-projects (H.publishAsyncResult w) s eq | nothing | cleanup = case eq of λ ()
step-projects (H.publishAsyncResult w) s eq | just t | nothing = case eq of λ ()
step-projects (H.publishAsyncResult w) s eq | just t | just S.cleanupAcquire = case eq of λ ()
step-projects (H.publishAsyncResult w) s eq | just t | just (S.cleanupSelect capturedLease) = case eq of λ ()
step-projects (H.publishAsyncResult w) s eq | just t | just (S.cleanupClose capturedLease map tail) = case eq of λ ()
step-projects (H.publishAsyncResult w) s eq | just t | just (S.cleanupPublish capturedLease map tail) = case eq of λ ()
step-projects (H.publishAsyncResult w) s eq | just t | just (S.cleanupRestore capturedLease closeError) = case eq of λ ()
step-projects (H.publishAsyncResult w) s eq | just t | just (S.cleanupWaiting captured) = case eq of λ ()
step-projects (H.publishAsyncResult w) s eq | just t | just (S.cleanupFinalize captured outcome) = case eq of λ ()
step-projects (H.publishAsyncResult w) s eq | just t | just (S.cleanupCount outcome) = case eq of λ ()
step-projects (H.shutdownStep action) s eq = shutdown-paths action s eq
step-projects (H.deliverShutdownHandshake err) s eq = shutdown-delivery-paths false err s eq
step-projects (H.deliverShutdownBlockedSetup err) s eq = shutdown-delivery-paths true err s eq
step-projects (H.deliverShutdownTimeWait err) s eq = timewait-delivery-paths err s eq
step-projects H.acknowledgeFinished s eq with Close.phase (H.shutdown s)
... | Close.awaitDelivery e w with H.resultReady w s
...   | false = case eq of λ ()
...   | true = acknowledge-paths s eq
step-projects H.acknowledgeFinished s eq | Close.initial = case eq of λ ()
step-projects H.acknowledgeFinished s eq | Close.reading = case eq of λ ()
step-projects H.acknowledgeFinished s eq | (Close.sendReady e w) = case eq of λ ()
step-projects H.acknowledgeFinished s eq | Close.awaitResults = case eq of λ ()
step-projects H.acknowledgeFinished s eq | Close.closed = case eq of λ ()

exec-projects : ∀ {s actions s′} → H.Executes s actions s′ → Paths s s′
exec-projects {s = s} H.done = idle s
exec-projects (H.next {s = s} {a = a} eq path) = compose (step-projects a s eq) (exec-projects path)

initial-coordinator : ∀ c {s} → H.initial c ≡ just s → H.shutdown s ≡ Close.initialState
initial-coordinator c eq with S.handlers (M.world c) | S.cleanups (M.world c) | M.handlerLifecycles c | M.publicationFaults c
... | [] | [] | [] | [] = case just-injective eq of λ { refl → refl }
... | h ∷ hs | cleanups | lifecycles | faults = case eq of λ ()
... | [] | k ∷ ks | lifecycles | faults = case eq of λ ()
... | [] | [] | l ∷ ls | faults = case eq of λ ()
... | [] | [] | [] | f ∷ fs = case eq of λ ()
initial-last : ∀ c {s} → H.initial c ≡ just s → LastValid (H.shutdown s)
initial-last c eq rewrite initial-coordinator c eq = λ ()

-- The primitive certificate and wrapper checkpoint both come from the coupled
-- path. The available function is the physical table at the actual last wait.
closed-from-initial : ∀ {c start actions s} → H.initial c ≡ just start →
  H.Executes start actions s → Close.phase (H.shutdown s) ≡ Close.closed →
  Close.remaining (H.shutdown s) ≡ [] × PhysicalWait (H.shutdown s)
closed-from-initial {c} initialized path closed with exec-projects path
... | paths machine (as , coordinator) witnessed =
  proj₁ (CloseProof.closed-from-initial
    (subst (λ initial → Close.Executes initial as _) (initial-coordinator c initialized) coordinator) closed) ,
  witnessed (initial-last c initialized) closed

-- Reuse actual dispatcher executions for existing allocation/map/ownership laws.
supply-preserves : ∀ {s actions s′} → SupplyBounds (M.world (H.source s)) →
  H.Executes s actions s′ → SupplyBounds (M.world (H.source s′))
supply-preserves valid path = Supply.exec-preserves valid (proj₂ (machine (exec-projects path)))
maps-preserves : ∀ {s actions s′} → MapPredicate.Valid (M.world (H.source s)) →
  H.Executes s actions s′ → MapPredicate.Valid (M.world (H.source s′))
maps-preserves valid path = Maps.exec-preserves valid (proj₂ (machine (exec-projects path)))
ownership-preserves : ∀ {s actions s′} → OwnPredicate.Ownership (M.world (H.source s)) →
  H.Executes s actions s′ → OwnPredicate.Ownership (M.world (H.source s′))
ownership-preserves valid path = Ownership.exec-preserves valid (proj₂ (machine (exec-projects path)))

-- A local publication checkpoint retains the captured physical identity and
-- observes real cleanupDone at this transition. Exceptional cleanup outcomes
-- remain explicit; this is not a successful socket-close assertion.
record ResultPublication (w : WorkerId) (before after : H.State) : Set where
  constructor resultPublication
  field
    registered : H.Thread
    original : ErrorId
    earlierOutcome outcome : S.CleanupOutcome
    found-before : lookup w (H.threads before) ≡ just registered
    phase-before : H.phase registered ≡ H.cleanupComplete original earlierOutcome
    cleanup-done-before : lookup w (S.cleanups (M.world (H.source before))) ≡ just (S.cleanupDone outcome)
    found-after : lookup w (H.threads after) ≡
      just (record registered { phase = H.resultAvailable original outcome })
open ResultPublication public

publication-observation : ∀ w s {s′} → H.step (H.publishAsyncResult w) s ≡ just s′ → ResultPublication w s s′
publication-observation w s eq with lookup w (H.threads s) in threadFound | lookup w (S.cleanups (M.world (H.source s))) in cleanupFound
... | just t | just (S.cleanupDone outcome) with H.phase t in phase
...   | H.cleanupComplete err observed = case just-injective eq of λ { refl →
  resultPublication t err observed outcome threadFound phase cleanupFound
    (lookup-put w (record t { phase = H.resultAvailable err outcome }) (H.threads s)) }
publication-observation w s eq | just t | just (S.cleanupDone outcome) | H.maskedSetup = case eq of λ ()
publication-observation w s eq | just t | just (S.cleanupDone outcome) | H.handshaking = case eq of λ ()
publication-observation w s eq | just t | just (S.cleanupDone outcome) | (H.caughtCancellation err) = case eq of λ ()
publication-observation w s eq | just t | just (S.cleanupDone outcome) | (H.cancellationPublished err) = case eq of λ ()
publication-observation w s eq | just t | just (S.cleanupDone outcome) | (H.bodyExited err) = case eq of λ ()
publication-observation w s eq | just t | just (S.cleanupDone outcome) | (H.finalizing err) = case eq of λ ()
publication-observation w s eq | just t | just (S.cleanupDone outcome) | (H.resultAvailable err earlierOutcome) = case eq of λ ()
publication-observation w s eq | nothing | cleanup = case eq of λ ()
publication-observation w s eq | just t | nothing = case eq of λ ()
publication-observation w s eq | just t | just S.cleanupAcquire = case eq of λ ()
publication-observation w s eq | just t | just (S.cleanupSelect capturedLease) = case eq of λ ()
publication-observation w s eq | just t | just (S.cleanupClose capturedLease map tail) = case eq of λ ()
publication-observation w s eq | just t | just (S.cleanupPublish capturedLease map tail) = case eq of λ ()
publication-observation w s eq | just t | just (S.cleanupRestore capturedLease closeError) = case eq of λ ()
publication-observation w s eq | just t | just (S.cleanupWaiting captured) = case eq of λ ()
publication-observation w s eq | just t | just (S.cleanupFinalize captured earlierOutcome) = case eq of λ ()
publication-observation w s eq | just t | just (S.cleanupCount earlierOutcome) = case eq of λ ()
