{-# OPTIONS --guardedness #-}

-- Only actual acknowledged handlers enter CM's collected list. A connection
-- entry naming a worker is deliberately not used as a physical lookup.
module ConnectionManagement.Properties.CollectedHandlerBacking where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
import Data.Maybe as Maybe
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Function using (case_of_)
open import ConnectionManagement.Domain using (WorkerId; ErrorId)
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
import ConnectionManagement.Properties.HandlerBirthEffects as Effects
import ConnectionManagement.Properties.HandlerAuxBacking as Aux

-- Membership is preserved with multiplicity; the source list is not deduplicated.
At : Effects.Registry → List WorkerId → Set
At registry workers = ∀ {w} → w ∈ workers → Aux.Present w registry
Backed : Effects.Registry → Close.State → Set
Backed registry s = At registry (Close.collected s)

transport : ∀ {P before after workers} → Effects.Change P before after → At before workers → At after workers
transport changed valid member with valid member
... | captured , found = captured , Effects.retains changed _ captured found

present-transport : ∀ {P before after w} → Effects.Change P before after → Aux.Present w before → Aux.Present w after
present-transport changed (captured , found) = captured , Effects.retains changed _ captured found

thread-present : ∀ {w t ts} → lookup w ts ≡ just t → Aux.Present w (Effects.captures ts)
thread-present {w} {t} {ts} found = H.captured t , trans (Effects.lookup-captures w ts) (cong (Maybe.map H.captured) found)

-- The only list extension is a receipt for the exact awaited worker.
AwaitBacked : Effects.Registry → Close.State → Set
AwaitBacked registry s = ∀ {e w} → Close.phase s ≡ Close.awaitDelivery e w → Aux.Present w registry

recipient : ∀ {e e′ w w′} → Close.awaitDelivery e w ≡ Close.awaitDelivery e′ w′ → w ≡ w′
recipient refl = refl
await-backed : ∀ {registry pc e w} → pc ≡ Close.awaitDelivery e w → Aux.Present w registry →
  ∀ {e′ w′} → pc ≡ Close.awaitDelivery e′ w′ → Aux.Present w′ registry
await-backed {registry} awaited present actual = subst (λ w → Aux.Present w registry) (recipient (trans (sym awaited) actual)) present

append-backed : ∀ {registry} xs {w} → (∀ {q} → q ∈ xs → Aux.Present q registry) → Aux.Present w registry →
  ∀ {q} → q ∈ (xs ++ (w ∷ [])) → Aux.Present q registry
append-backed [] valid present (here refl) = present
append-backed [] valid present (there ())
append-backed (x ∷ xs) valid present (here refl) = valid (here refl)
append-backed {registry} (x ∷ xs) {w} valid present (there member) = append-backed {registry = registry} xs {w = w} (λ p → valid (there p)) present member

-- The primitive permits arbitrary oracles; only its acknowledgment needs a
-- physical-recipient premise. Concrete adapters discharge this from real guards.
close-preserves : ∀ registry current available action s {t} → Close.step current available action s ≡ just t →
  Backed registry s → (action ≡ Close.acknowledgeDelivery → AwaitBacked registry s) → Backed registry t
close-preserves registry current available Close.captureSnapshot (Close.shutdownState Close.initial snap rest workers) eq valid ack with S.mapCell current
... | S.taken owner = case eq of λ ()
... | S.full map = case just-injective eq of λ { refl → valid }
close-preserves registry current available Close.captureSnapshot (Close.shutdownState Close.reading snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.captureSnapshot (Close.shutdownState (Close.sendReady e w) snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.captureSnapshot (Close.shutdownState (Close.awaitDelivery e w) snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.captureSnapshot (Close.shutdownState Close.awaitResults snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.captureSnapshot (Close.shutdownState Close.closed snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.readEntry (Close.shutdownState Close.initial snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.readEntry (Close.shutdownState Close.reading snap [] workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.readEntry (Close.shutdownState Close.reading snap (e ∷ rest) workers) eq valid ack with lookup e (S.entries current)
... | nothing = case eq of λ ()
... | just state with Close.getConnThread state
...   | nothing = case just-injective eq of λ { refl → valid }
...   | just w = case just-injective eq of λ { refl → valid }
close-preserves registry current available Close.readEntry (Close.shutdownState (Close.sendReady e w) snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.readEntry (Close.shutdownState (Close.awaitDelivery e w) snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.readEntry (Close.shutdownState Close.awaitResults snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.readEntry (Close.shutdownState Close.closed snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.requestCancellation (Close.shutdownState Close.initial snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.requestCancellation (Close.shutdownState Close.reading snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.requestCancellation (Close.shutdownState (Close.sendReady e w) snap rest workers) eq valid ack = case just-injective eq of λ { refl → valid }
close-preserves registry current available Close.requestCancellation (Close.shutdownState (Close.awaitDelivery e w) snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.requestCancellation (Close.shutdownState Close.awaitResults snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.requestCancellation (Close.shutdownState Close.closed snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.acknowledgeDelivery (Close.shutdownState Close.initial snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.acknowledgeDelivery (Close.shutdownState Close.reading snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.acknowledgeDelivery (Close.shutdownState (Close.sendReady e w) snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.acknowledgeDelivery (Close.shutdownState (Close.awaitDelivery e w) snap rest workers) eq valid ack =
  case just-injective eq of λ { refl → append-backed {registry = registry} workers {w = w} valid (ack refl refl) }
close-preserves registry current available Close.acknowledgeDelivery (Close.shutdownState Close.awaitResults snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.acknowledgeDelivery (Close.shutdownState Close.closed snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.finishTraversal (Close.shutdownState Close.initial snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.finishTraversal (Close.shutdownState Close.reading snap [] workers) eq valid ack = case just-injective eq of λ { refl → valid }
close-preserves registry current available Close.finishTraversal (Close.shutdownState Close.reading snap (e ∷ rest) workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.finishTraversal (Close.shutdownState (Close.sendReady e w) snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.finishTraversal (Close.shutdownState (Close.awaitDelivery e w) snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.finishTraversal (Close.shutdownState Close.awaitResults snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.finishTraversal (Close.shutdownState Close.closed snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.finishClose (Close.shutdownState Close.initial snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.finishClose (Close.shutdownState Close.reading snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.finishClose (Close.shutdownState (Close.sendReady e w) snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.finishClose (Close.shutdownState (Close.awaitDelivery e w) snap rest workers) eq valid ack = case eq of λ ()
close-preserves registry current available Close.finishClose (Close.shutdownState Close.awaitResults snap rest workers) eq valid ack with Close.allAvailable available workers
... | false = case eq of λ ()
... | true = case just-injective eq of λ { refl → valid }
close-preserves registry current available Close.finishClose (Close.shutdownState Close.closed snap rest workers) eq valid ack = case eq of λ ()

-- Changing only the coordinator's cursor retains its exact list obligations.
same-collected : ∀ {registry before after} → after ≡ before → At registry before → At registry after
same-collected same valid {w} member = valid (subst (w ∈_) same member)

module Raw where
 Valid : H.State → Set
 Valid s = Backed (Effects.raw s) (H.shutdown s)
 source-valid : ∀ c s → Valid s → Valid (H.setSource c s)
 source-valid c s valid = valid
 phase-valid : ∀ w t pc s → lookup w (H.threads s) ≡ just t → Valid s → Valid (H.setPhase w t pc s)
 phase-valid w t pc s found valid = transport {P = ⊤} (Effects.stable (Effects.phase-map w t pc s found)) valid
 dispatch-valid : ∀ a s {t} → H.dispatch a s ≡ just t → Valid s → Valid t
 dispatch-valid a s actual valid with Machine.advance a (H.source s)
 ... | nothing = case actual of λ ()
 ... | just c = case just-injective actual of λ { refl → valid }
 dispatch-phase-valid : ∀ a w thread pc s {t} → lookup w (H.threads s) ≡ just thread →
   H.dispatchPhase a w thread pc s ≡ just t → Valid s → Valid t
 dispatch-phase-valid a w thread pc s found actual valid with Machine.advance a (H.source s)
 ... | nothing = case actual of λ ()
 ... | just c = case just-injective actual of λ { refl → phase-valid w thread pc (H.setSource c s) found valid }
 dispatch-shutdown : ∀ a s {t} → H.dispatch a s ≡ just t → H.shutdown t ≡ H.shutdown s
 dispatch-shutdown a s eq with Machine.advance a (H.source s)
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → refl }
 ready-present : ∀ w s → H.resultReady w s ≡ true → Aux.Present w (Effects.raw s)
 ready-present w s actual with lookup w (H.threads s) in found
 ... | nothing = case actual of λ ()
 ... | just thread = thread-present {w = w} {t = thread} {ts = H.threads s} found
 acknowledge-valid : ∀ s {t} → H.acknowledge s ≡ just t → AwaitBacked (Effects.raw s) (H.shutdown s) → Valid s → Valid t
 acknowledge-valid s actual backed valid with Close.step (S.cm (Machine.world (H.source s))) (λ w → H.resultReady w s)
   Close.acknowledgeDelivery (H.shutdown s) in stepped
 ... | nothing = case actual of λ ()
 ... | just next = case just-injective actual of λ { refl →
   close-preserves (Effects.raw s) (S.cm (Machine.world (H.source s))) (λ w → H.resultReady w s) Close.acknowledgeDelivery (H.shutdown s) stepped valid (λ _ → backed) }
 handshake-present : ∀ w err s {t} → H.deliverHandshake w err s ≡ just t → Aux.Present w (Effects.raw s)
 handshake-present w err s actual with lookup w (H.threads s) in found
 ... | nothing = case actual of λ ()
 ... | just thread = thread-present {w = w} {t = thread} {ts = H.threads s} found
 setup-present : ∀ w err s {t} → H.deliverBlockedSetup w err s ≡ just t → Aux.Present w (Effects.raw s)
 setup-present w err s actual with lookup w (H.threads s) in found
 ... | nothing = case actual of λ ()
 ... | just thread = thread-present {w = w} {t = thread} {ts = H.threads s} found
 -- Both deliveries change a phase without changing the shutdown cursor.
 handshake-valid : ∀ w err s {t} → H.deliverHandshake w err s ≡ just t → Valid s → Valid t
 setup-valid : ∀ w err s {t} → H.deliverBlockedSetup w err s ≡ just t → Valid s → Valid t

 handshake-valid w err s actual valid with lookup w (H.threads s) in found
 ... | nothing = case actual of λ ()
 ... | just thread with H.phase thread
 handshake-valid w err s actual valid | just thread | H.maskedSetup = case actual of λ ()
 handshake-valid w err s actual valid | just thread | H.handshaking = case just-injective actual of λ { refl → phase-valid w thread (H.caughtCancellation err) s found valid }
 handshake-valid w err s actual valid | just thread | (H.caughtCancellation old) = case actual of λ ()
 handshake-valid w err s actual valid | just thread | (H.cancellationPublished old) = case actual of λ ()
 handshake-valid w err s actual valid | just thread | (H.bodyExited old) = case actual of λ ()
 handshake-valid w err s actual valid | just thread | (H.finalizing old) = case actual of λ ()
 handshake-valid w err s actual valid | just thread | (H.cleanupComplete old outcome) = case actual of λ ()
 handshake-valid w err s actual valid | just thread | (H.resultAvailable old outcome) = case actual of λ ()
 setup-valid w err s actual valid with lookup w (H.threads s) in found
 ... | nothing = case actual of λ ()
 ... | just thread with H.phase thread
 setup-valid w err s actual valid | just thread | H.maskedSetup = case just-injective actual of λ { refl → phase-valid w thread (H.bodyExited err) s found valid }
 setup-valid w err s actual valid | just thread | H.handshaking = case actual of λ ()
 setup-valid w err s actual valid | just thread | (H.caughtCancellation old) = case actual of λ ()
 setup-valid w err s actual valid | just thread | (H.cancellationPublished old) = case actual of λ ()
 setup-valid w err s actual valid | just thread | (H.bodyExited old) = case actual of λ ()
 setup-valid w err s actual valid | just thread | (H.finalizing old) = case actual of λ ()
 setup-valid w err s actual valid | just thread | (H.cleanupComplete old outcome) = case actual of λ ()
 setup-valid w err s actual valid | just thread | (H.resultAvailable old outcome) = case actual of λ ()
 fork-valid : ∀ w s {t} → H.forkAdmission w s ≡ just t → Valid s → Valid t
 fork-valid w s eq valid with lookup w (S.admissions (Machine.world (H.source s)))
 ... | nothing = case eq of λ ()
 ... | just a with lookup (S.child (S.request a)) (H.threads s) in missing
 ...   | just old = case eq of λ ()
 ...   | nothing with Machine.advance (Machine.admissionStep w Server.fork) (H.source s)
 ...     | nothing = case eq of λ ()
 ...     | just c with lookup (S.child (S.request a)) (S.handlers (Machine.world c))
 ...       | nothing = case eq of λ ()
 ...       | just handler = case just-injective eq of λ { refl → transport {P = ⊤}
   (Effects.added {before = Effects.raw s} (S.child (S.request a)) handler
     (trans (Effects.lookup-captures (S.child (S.request a)) (H.threads s)) (cong (Maybe.map H.captured) missing))
     (Effects.captures-put (S.child (S.request a)) (H.handlerThread handler H.maskedSetup) (H.threads s)) tt) valid }
 shutdown-valid : ∀ blocked err s {t} → H.deliverShutdown blocked err s ≡ just t → Valid s → Valid t
 timewait-valid : ∀ err s {t} → H.deliverTimeWait err s ≡ just t → Valid s → Valid t
 step-preserves : ∀ action s {t} → H.step action s ≡ just t → Valid s → Valid t
 step-preserves (H.run (Machine.admissionStep w Server.fork)) s eq valid = fork-valid w s eq valid
 step-preserves (H.run (Machine.admissionStep w Server.take)) s eq valid = dispatch-valid (Machine.admissionStep w Server.take) s eq valid
 step-preserves (H.run (Machine.admissionStep w Server.countLimit)) s eq valid = dispatch-valid (Machine.admissionStep w Server.countLimit) s eq valid
 step-preserves (H.run (Machine.admissionStep w Server.allocatePromise)) s eq valid = dispatch-valid (Machine.admissionStep w Server.allocatePromise) s eq valid
 step-preserves (H.run (Machine.admissionStep w Server.chooseEntry)) s eq valid = dispatch-valid (Machine.admissionStep w Server.chooseEntry) s eq valid
 step-preserves (H.run (Machine.admissionStep w Server.putMapBack)) s eq valid = dispatch-valid (Machine.admissionStep w Server.putMapBack) s eq valid
 step-preserves (H.run (Machine.admissionStep w Server.readCounters)) s eq valid = dispatch-valid (Machine.admissionStep w Server.readCounters) s eq valid
 step-preserves (H.run (Machine.admissionStep w Server.restore)) s eq valid = dispatch-valid (Machine.admissionStep w Server.restore) s eq valid
 step-preserves (H.run (Machine.admissionStep w Server.close)) s eq valid = dispatch-valid (Machine.admissionStep w Server.close) s eq valid
 step-preserves (H.run (Machine.admissionStep w Server.failFork)) s eq valid = dispatch-valid (Machine.admissionStep w Server.failFork) s eq valid
 step-preserves (H.run (Machine.handshakeStep w a)) s eq valid = dispatch-valid (Machine.handshakeStep w a) s eq valid
 step-preserves (H.run (Machine.handlerPublication w result outcome)) s eq valid = case eq of λ ()
 step-preserves (H.run (Machine.handlerExit w)) s eq valid = case eq of λ ()
 step-preserves (H.run (Machine.handlerStep w a)) s eq valid = case eq of λ ()
 step-preserves (H.run (Machine.cleanupStep w a)) s eq valid = case eq of λ ()
 step-preserves (H.run (Machine.igStep a)) s eq valid = dispatch-valid (Machine.igStep a) s eq valid
 step-preserves (H.run (Machine.remoteStep a)) s eq valid with H.rawAllowed (Machine.remoteStep a)
 ... | false = case eq of λ ()
 ... | true = dispatch-valid (Machine.remoteStep a) s eq valid
 step-preserves (H.run (Machine.releaseStep a)) s eq valid with H.rawAllowed (Machine.releaseStep a)
 ... | false = case eq of λ ()
 ... | true = dispatch-valid (Machine.releaseStep a) s eq valid
 step-preserves (H.enterHandshake w) s eq valid with lookup w (H.threads s) in found
 ... | nothing = case eq of λ ()
 ... | just t with H.phase t
 step-preserves (H.enterHandshake w) s eq valid | just t | H.maskedSetup = case just-injective eq of λ { refl → phase-valid w t H.handshaking s found valid }
 step-preserves (H.enterHandshake w) s eq valid | just t | H.handshaking = case eq of λ ()
 step-preserves (H.enterHandshake w) s eq valid | just t | (H.caughtCancellation err) = case eq of λ ()
 step-preserves (H.enterHandshake w) s eq valid | just t | (H.cancellationPublished err) = case eq of λ ()
 step-preserves (H.enterHandshake w) s eq valid | just t | (H.bodyExited err) = case eq of λ ()
 step-preserves (H.enterHandshake w) s eq valid | just t | (H.finalizing err) = case eq of λ ()
 step-preserves (H.enterHandshake w) s eq valid | just t | (H.cleanupComplete err outcome) = case eq of λ ()
 step-preserves (H.enterHandshake w) s eq valid | just t | (H.resultAvailable err outcome) = case eq of λ ()
 step-preserves (H.deliverHandshakeCancellation w err) s eq valid = handshake-valid w err s eq valid
 step-preserves (H.deliverBlockedSetupCancellation w err) s eq valid = setup-valid w err s eq valid
 step-preserves (H.publishCaught w) s eq valid with lookup w (H.threads s) in found
 ... | nothing = case eq of λ ()
 ... | just t with H.phase t
 step-preserves (H.publishCaught w) s eq valid | just t | H.maskedSetup = case eq of λ ()
 step-preserves (H.publishCaught w) s eq valid | just t | H.handshaking = case eq of λ ()
 step-preserves (H.publishCaught w) s eq valid | just t | (H.caughtCancellation err) = dispatch-phase-valid (Machine.handlerPublication w (S.handlerError S.protocolViolation err) Machine.resultWritten) w t (H.cancellationPublished err) s found eq valid
 step-preserves (H.publishCaught w) s eq valid | just t | (H.cancellationPublished err) = case eq of λ ()
 step-preserves (H.publishCaught w) s eq valid | just t | (H.bodyExited err) = case eq of λ ()
 step-preserves (H.publishCaught w) s eq valid | just t | (H.finalizing err) = case eq of λ ()
 step-preserves (H.publishCaught w) s eq valid | just t | (H.cleanupComplete err outcome) = case eq of λ ()
 step-preserves (H.publishCaught w) s eq valid | just t | (H.resultAvailable err outcome) = case eq of λ ()
 step-preserves (H.rethrowCaught w) s eq valid with lookup w (H.threads s) in found
 ... | nothing = case eq of λ ()
 ... | just t with H.phase t
 step-preserves (H.rethrowCaught w) s eq valid | just t | H.maskedSetup = case eq of λ ()
 step-preserves (H.rethrowCaught w) s eq valid | just t | H.handshaking = case eq of λ ()
 step-preserves (H.rethrowCaught w) s eq valid | just t | (H.caughtCancellation err) = case eq of λ ()
 step-preserves (H.rethrowCaught w) s eq valid | just t | (H.cancellationPublished err) = case just-injective eq of λ { refl → phase-valid w t (H.bodyExited err) s found valid }
 step-preserves (H.rethrowCaught w) s eq valid | just t | (H.bodyExited err) = case eq of λ ()
 step-preserves (H.rethrowCaught w) s eq valid | just t | (H.finalizing err) = case eq of λ ()
 step-preserves (H.rethrowCaught w) s eq valid | just t | (H.cleanupComplete err outcome) = case eq of λ ()
 step-preserves (H.rethrowCaught w) s eq valid | just t | (H.resultAvailable err outcome) = case eq of λ ()
 step-preserves (H.enterFinalizer w) s eq valid with lookup w (H.threads s) in found
 ... | nothing = case eq of λ ()
 ... | just t with H.phase t
 step-preserves (H.enterFinalizer w) s eq valid | just t | H.maskedSetup = case eq of λ ()
 step-preserves (H.enterFinalizer w) s eq valid | just t | H.handshaking = case eq of λ ()
 step-preserves (H.enterFinalizer w) s eq valid | just t | (H.caughtCancellation err) = case eq of λ ()
 step-preserves (H.enterFinalizer w) s eq valid | just t | (H.cancellationPublished err) = case eq of λ ()
 step-preserves (H.enterFinalizer w) s eq valid | just t | (H.bodyExited err) = dispatch-phase-valid (Machine.handlerExit w) w t (H.finalizing err) s found eq valid
 step-preserves (H.enterFinalizer w) s eq valid | just t | (H.finalizing err) = case eq of λ ()
 step-preserves (H.enterFinalizer w) s eq valid | just t | (H.cleanupComplete err outcome) = case eq of λ ()
 step-preserves (H.enterFinalizer w) s eq valid | just t | (H.resultAvailable err outcome) = case eq of λ ()
 step-preserves (H.cleanup w action) s eq valid with lookup w (H.threads s) in found
 ... | nothing = case eq of λ ()
 ... | just t with H.phase t
 step-preserves (H.cleanup w action) s eq valid | just t | H.maskedSetup = case eq of λ ()
 step-preserves (H.cleanup w action) s eq valid | just t | H.handshaking = case eq of λ ()
 step-preserves (H.cleanup w action) s eq valid | just t | (H.caughtCancellation err) = case eq of λ ()
 step-preserves (H.cleanup w action) s eq valid | just t | (H.cancellationPublished err) = case eq of λ ()
 step-preserves (H.cleanup w action) s eq valid | just t | (H.bodyExited err) = case eq of λ ()
 step-preserves (H.cleanup w action) s eq valid | just t | (H.finalizing err) = dispatch-valid (Machine.cleanupStep w action) s eq valid
 step-preserves (H.cleanup w action) s eq valid | just t | (H.cleanupComplete err outcome) = case eq of λ ()
 step-preserves (H.cleanup w action) s eq valid | just t | (H.resultAvailable err outcome) = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq valid with lookup w (H.threads s) in found | lookup w (S.cleanups (Machine.world (H.source s)))
 ... | just t | just (S.cleanupDone outcome) with H.phase t
 step-preserves (H.finishCleanup w) s eq valid | just t | just (S.cleanupDone outcome) | H.maskedSetup = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq valid | just t | just (S.cleanupDone outcome) | H.handshaking = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq valid | just t | just (S.cleanupDone outcome) | (H.caughtCancellation err) = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq valid | just t | just (S.cleanupDone outcome) | (H.cancellationPublished err) = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq valid | just t | just (S.cleanupDone outcome) | (H.bodyExited err) = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq valid | just t | just (S.cleanupDone outcome) | (H.finalizing err) = case just-injective eq of λ { refl → phase-valid w t (H.cleanupComplete err outcome) s found valid }
 step-preserves (H.finishCleanup w) s eq valid | just t | just (S.cleanupDone outcome) | (H.cleanupComplete err priorOutcome) = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq valid | just t | just (S.cleanupDone outcome) | (H.resultAvailable err priorOutcome) = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq valid | nothing | cleanup = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq valid | just t | nothing = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq valid | just t | just S.cleanupAcquire = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq valid | just t | just (S.cleanupSelect capturedLease) = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq valid | just t | just (S.cleanupClose capturedLease map tail) = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq valid | just t | just (S.cleanupPublish capturedLease map tail) = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq valid | just t | just (S.cleanupRestore capturedLease closeError) = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq valid | just t | just (S.cleanupWaiting captured) = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq valid | just t | just (S.cleanupFinalize captured outcome) = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq valid | just t | just (S.cleanupCount outcome) = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq valid with lookup w (H.threads s) in found | lookup w (S.cleanups (Machine.world (H.source s)))
 ... | just t | just (S.cleanupDone outcome) with H.phase t
 step-preserves (H.publishAsyncResult w) s eq valid | just t | just (S.cleanupDone outcome) | H.maskedSetup = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq valid | just t | just (S.cleanupDone outcome) | H.handshaking = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq valid | just t | just (S.cleanupDone outcome) | (H.caughtCancellation err) = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq valid | just t | just (S.cleanupDone outcome) | (H.cancellationPublished err) = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq valid | just t | just (S.cleanupDone outcome) | (H.bodyExited err) = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq valid | just t | just (S.cleanupDone outcome) | (H.finalizing err) = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq valid | just t | just (S.cleanupDone outcome) | (H.cleanupComplete err observed) = case just-injective eq of λ { refl → phase-valid w t (H.resultAvailable err outcome) s found valid }
 step-preserves (H.publishAsyncResult w) s eq valid | just t | just (S.cleanupDone outcome) | (H.resultAvailable err priorOutcome) = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq valid | nothing | cleanup = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq valid | just t | nothing = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq valid | just t | just S.cleanupAcquire = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq valid | just t | just (S.cleanupSelect capturedLease) = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq valid | just t | just (S.cleanupClose capturedLease map tail) = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq valid | just t | just (S.cleanupPublish capturedLease map tail) = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq valid | just t | just (S.cleanupRestore capturedLease closeError) = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq valid | just t | just (S.cleanupWaiting captured) = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq valid | just t | just (S.cleanupFinalize captured outcome) = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq valid | just t | just (S.cleanupCount outcome) = case eq of λ ()
 step-preserves (H.shutdownStep Close.captureSnapshot) s eq valid with Close.step (S.cm (Machine.world (H.source s))) (λ w → H.resultReady w s) Close.captureSnapshot (H.shutdown s) in stepped
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → close-preserves (Effects.raw s) (S.cm (Machine.world (H.source s))) (λ w → H.resultReady w s) Close.captureSnapshot (H.shutdown s) stepped valid (λ ()) }
 step-preserves (H.shutdownStep Close.readEntry) s eq valid with Close.step (S.cm (Machine.world (H.source s))) (λ w → H.resultReady w s) Close.readEntry (H.shutdown s) in stepped
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → close-preserves (Effects.raw s) (S.cm (Machine.world (H.source s))) (λ w → H.resultReady w s) Close.readEntry (H.shutdown s) stepped valid (λ ()) }
 step-preserves (H.shutdownStep Close.requestCancellation) s eq valid with Close.step (S.cm (Machine.world (H.source s))) (λ w → H.resultReady w s) Close.requestCancellation (H.shutdown s) in stepped
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → close-preserves (Effects.raw s) (S.cm (Machine.world (H.source s))) (λ w → H.resultReady w s) Close.requestCancellation (H.shutdown s) stepped valid (λ ()) }
 step-preserves (H.shutdownStep Close.finishTraversal) s eq valid with Close.step (S.cm (Machine.world (H.source s))) (λ w → H.resultReady w s) Close.finishTraversal (H.shutdown s) in stepped
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → close-preserves (Effects.raw s) (S.cm (Machine.world (H.source s))) (λ w → H.resultReady w s) Close.finishTraversal (H.shutdown s) stepped valid (λ ()) }
 step-preserves (H.shutdownStep Close.finishClose) s eq valid with Close.step (S.cm (Machine.world (H.source s))) (λ w → H.resultReady w s) Close.finishClose (H.shutdown s) in stepped
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → close-preserves (Effects.raw s) (S.cm (Machine.world (H.source s))) (λ w → H.resultReady w s) Close.finishClose (H.shutdown s) stepped valid (λ ()) }
 step-preserves (H.shutdownStep Close.acknowledgeDelivery) s () valid
 step-preserves (H.deliverShutdownHandshake err) s eq valid = shutdown-valid false err s eq valid
 step-preserves (H.deliverShutdownBlockedSetup err) s eq valid = shutdown-valid true err s eq valid
 step-preserves (H.deliverShutdownTimeWait err) s eq valid = timewait-valid err s eq valid
 step-preserves H.acknowledgeFinished s eq valid with Close.phase (H.shutdown s) in awaited
 ... | Close.awaitDelivery e w with H.resultReady w s in ready
 ...   | true = acknowledge-valid s eq (await-backed {registry = Effects.raw s} awaited (ready-present w s ready)) valid
 ...   | false = case eq of λ ()
 step-preserves H.acknowledgeFinished s eq valid | Close.initial = case eq of λ ()
 step-preserves H.acknowledgeFinished s eq valid | Close.reading = case eq of λ ()
 step-preserves H.acknowledgeFinished s eq valid | Close.sendReady e w = case eq of λ ()
 step-preserves H.acknowledgeFinished s eq valid | Close.awaitResults = case eq of λ ()
 step-preserves H.acknowledgeFinished s eq valid | Close.closed = case eq of λ ()
 handshake-shutdown : ∀ w err s {t} → H.deliverHandshake w err s ≡ just t → H.shutdown t ≡ H.shutdown s
 handshake-shutdown w err s eq with lookup w (H.threads s)
 ... | nothing = case eq of λ ()
 ... | just thread with H.phase thread
 handshake-shutdown w err s eq | just thread | H.maskedSetup = case eq of λ ()
 handshake-shutdown w err s eq | just thread | H.handshaking = case just-injective eq of λ { refl → refl }
 handshake-shutdown w err s eq | just thread | (H.caughtCancellation old) = case eq of λ ()
 handshake-shutdown w err s eq | just thread | (H.cancellationPublished old) = case eq of λ ()
 handshake-shutdown w err s eq | just thread | (H.bodyExited old) = case eq of λ ()
 handshake-shutdown w err s eq | just thread | (H.finalizing old) = case eq of λ ()
 handshake-shutdown w err s eq | just thread | (H.cleanupComplete old outcome) = case eq of λ ()
 handshake-shutdown w err s eq | just thread | (H.resultAvailable old outcome) = case eq of λ ()
 setup-shutdown : ∀ w err s {t} → H.deliverBlockedSetup w err s ≡ just t → H.shutdown t ≡ H.shutdown s
 setup-shutdown w err s eq with lookup w (H.threads s)
 ... | nothing = case eq of λ ()
 ... | just thread with H.phase thread
 setup-shutdown w err s eq | just thread | H.maskedSetup = case just-injective eq of λ { refl → refl }
 setup-shutdown w err s eq | just thread | H.handshaking = case eq of λ ()
 setup-shutdown w err s eq | just thread | (H.caughtCancellation old) = case eq of λ ()
 setup-shutdown w err s eq | just thread | (H.cancellationPublished old) = case eq of λ ()
 setup-shutdown w err s eq | just thread | (H.bodyExited old) = case eq of λ ()
 setup-shutdown w err s eq | just thread | (H.finalizing old) = case eq of λ ()
 setup-shutdown w err s eq | just thread | (H.cleanupComplete old outcome) = case eq of λ ()
 setup-shutdown w err s eq | just thread | (H.resultAvailable old outcome) = case eq of λ ()
 shutdown-valid blocked err s eq valid with Close.phase (H.shutdown s) in awaited
 ... | Close.awaitDelivery e w with blocked
 ...   | false with H.deliverHandshake w err s in delivered
 ...     | nothing = case eq of λ ()
 ...     | just next = acknowledge-valid next eq
   (await-backed {registry = Effects.raw next} (trans (cong Close.phase (handshake-shutdown w err s delivered)) awaited)
     (present-transport (Effects.handshake-change {P = ⊤} w err s delivered) (handshake-present w err s delivered)))
   (handshake-valid w err s delivered valid)
 shutdown-valid blocked err s eq valid | Close.awaitDelivery e w | true with H.deliverBlockedSetup w err s in delivered
 ...     | nothing = case eq of λ ()
 ...     | just next = acknowledge-valid next eq
   (await-backed {registry = Effects.raw next} (trans (cong Close.phase (setup-shutdown w err s delivered)) awaited)
     (present-transport (Effects.setup-change {P = ⊤} w err s delivered) (setup-present w err s delivered)))
   (setup-valid w err s delivered valid)
 shutdown-valid blocked err s eq valid | Close.initial = case eq of λ ()
 shutdown-valid blocked err s eq valid | Close.reading = case eq of λ ()
 shutdown-valid blocked err s eq valid | Close.sendReady e w = case eq of λ ()
 shutdown-valid blocked err s eq valid | Close.awaitResults = case eq of λ ()
 shutdown-valid blocked err s eq valid | Close.closed = case eq of λ ()
 timewait-valid err s eq valid with Close.phase (H.shutdown s) in awaited
 ... | Close.awaitDelivery e w with lookup w (H.threads s) in found | lookup w (S.cleanups (Machine.world (H.source s)))
 ...   | just t | just (S.cleanupWaiting captured) with H.phase t
 ...     | H.finalizing original with H.dispatch (Machine.cleanupStep w (Cleanup.interruptTimeWait err)) s in advanced
 ...       | nothing = case eq of λ ()
 ...       | just next = acknowledge-valid next eq (await-backed {registry = Effects.raw next} (trans (cong Close.phase (dispatch-shutdown (Machine.cleanupStep w (Cleanup.interruptTimeWait err)) s advanced)) awaited) (present-transport (Effects.dispatch-change {P = ⊤} (Machine.cleanupStep w (Cleanup.interruptTimeWait err)) s advanced) (thread-present {w = w} {t = t} {ts = H.threads s} found))) (dispatch-valid (Machine.cleanupStep w (Cleanup.interruptTimeWait err)) s advanced valid)
 timewait-valid err s eq valid | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | H.maskedSetup = case eq of λ ()
 timewait-valid err s eq valid | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | H.handshaking = case eq of λ ()
 timewait-valid err s eq valid | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | (H.caughtCancellation priorError) = case eq of λ ()
 timewait-valid err s eq valid | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | (H.cancellationPublished priorError) = case eq of λ ()
 timewait-valid err s eq valid | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | (H.bodyExited priorError) = case eq of λ ()
 timewait-valid err s eq valid | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | (H.cleanupComplete priorError outcome) = case eq of λ ()
 timewait-valid err s eq valid | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | (H.resultAvailable priorError outcome) = case eq of λ ()
 timewait-valid err s eq valid | Close.awaitDelivery e w | just t | just S.cleanupAcquire = case eq of λ ()
 timewait-valid err s eq valid | Close.awaitDelivery e w | just t | just (S.cleanupSelect capturedLease) = case eq of λ ()
 timewait-valid err s eq valid | Close.awaitDelivery e w | just t | just (S.cleanupClose capturedLease map tail) = case eq of λ ()
 timewait-valid err s eq valid | Close.awaitDelivery e w | just t | just (S.cleanupPublish capturedLease map tail) = case eq of λ ()
 timewait-valid err s eq valid | Close.awaitDelivery e w | just t | just (S.cleanupRestore capturedLease closeError) = case eq of λ ()
 timewait-valid err s eq valid | Close.awaitDelivery e w | just t | just (S.cleanupFinalize captured outcome) = case eq of λ ()
 timewait-valid err s eq valid | Close.awaitDelivery e w | just t | just (S.cleanupCount outcome) = case eq of λ ()
 timewait-valid err s eq valid | Close.awaitDelivery e w | just t | just (S.cleanupDone outcome) = case eq of λ ()
 timewait-valid err s eq valid | Close.awaitDelivery e w | nothing | cleanup = case eq of λ ()
 timewait-valid err s eq valid | Close.awaitDelivery e w | just t | nothing = case eq of λ ()
 timewait-valid err s eq valid | Close.initial = case eq of λ ()
 timewait-valid err s eq valid | Close.reading = case eq of λ ()
 timewait-valid err s eq valid | (Close.sendReady e w) = case eq of λ ()
 timewait-valid err s eq valid | Close.awaitResults = case eq of λ ()
 timewait-valid err s eq valid | Close.closed = case eq of λ ()
 initialized-valid : ∀ c {s} → H.initial c ≡ just s → Valid s
 initialized-valid c eq with S.handlers (Machine.world c) | S.cleanups (Machine.world c) | Machine.handlerLifecycles c | Machine.publicationFaults c
 ... | [] | [] | [] | [] = case just-injective eq of λ { refl → λ () }
 ... | _ ∷ _ | _ | _ | _ = case eq of λ ()
 ... | [] | _ ∷ _ | _ | _ = case eq of λ ()
 ... | [] | [] | _ ∷ _ | _ = case eq of λ ()
 ... | [] | [] | [] | _ ∷ _ = case eq of λ ()

module Physical where
 Valid : B.State → Set
 Valid s = Backed (Effects.physical s) (B.shutdown s)
 source-valid : ∀ c s → Valid s → Valid (record s { source = c })
 source-valid c s valid = valid
 fork-valid : ∀ w s {t} → B.forkOutbound w s ≡ just t → Valid s → Valid t
 fork-valid w s eq valid with lookup w (O.acquiring (B.source s))
 ... | nothing = case eq of λ ()
 ... | just f with B.freshChild (Acquire.child (Acquire.req f)) s in fresh
 ...   | false = case eq of λ ()
 ...   | true with O.advance (O.acquire w Acquire.forkOK) (B.source s)
 ...     | nothing = case eq of λ ()
 ...     | just c with lookup (Acquire.child (Acquire.req f)) (S.handlers (Machine.world (O.core c)))
 ...       | nothing = case eq of λ ()
 ...       | just captured = case just-injective eq of λ { refl → transport {P = ⊤}
   (Effects.added {before = Effects.physical s} (Acquire.child (Acquire.req f)) captured
     (trans (Effects.lookup-captures (Acquire.child (Acquire.req f)) (B.threads s))
       (cong (Maybe.map H.captured) (Effects.fresh-threads (Acquire.child (Acquire.req f)) s fresh)))
     (Effects.captures-put (Acquire.child (Acquire.req f)) (H.handlerThread captured H.maskedSetup) (B.threads s)) tt) valid }
 step-preserves : ∀ a s {t} → B.step a s ≡ just t → Valid s → Valid t
 step-preserves (B.handler a) s eq valid with B.handlerAllowed a s
 ... | false = case eq of λ ()
 ... | true with H.step a (B.view s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just h = case just-injective eq of λ { refl → Raw.step-preserves a (B.view s) actual valid }
 step-preserves (B.outbound a) s eq valid with B.forkCaller a
 ... | just w = fork-valid w s eq valid
 ... | nothing with B.outboundAllowed a s
 ...   | false = case eq of λ ()
 ...   | true with O.advance a (B.source s)
 ...     | nothing = case eq of λ ()
 ...     | just c = case just-injective eq of λ { refl → valid }
 initialized-valid : ∀ c {s} → B.initial c ≡ just s → Valid s
 initialized-valid c eq with H.initial (O.core c) in actual
 ... | nothing = case eq of λ ()
 ... | just h = case just-injective eq of λ { refl → Raw.initialized-valid (O.core c) actual }

import ConnectionManagement.MuxHandlerSupervision as MuxModel
import ConnectionManagement.MuxProtocolJobs as ProtocolModel
import ConnectionManagement.MuxResultMonitor as MonitorModel
import ConnectionManagement.MuxGroupShutdown as GroupModel
import ConnectionManagement.MuxHandlerExit as ExitModel
import ConnectionManagement.MuxExitCancellation as CancellationModel
import ConnectionManagement.MuxStartupUnwind as UnwindModel
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.IGRegistration as IG
open import Data.Bool using (_∧_)

-- Startup, protocol and monitor metadata do not add CM collection entries.
module Mux where
 private module U = MuxModel Types.TypedResult using (State; allocateHandle; configure; configureMux; registerFor; registerCounters; beforePool; base; baseAllowed; birth; birthFresh; initial; negotiate; noteBirth; origins; publishSuccess; run; startupStep; step)
 view : U.State → Effects.Registry
 view = Effects.MuxLayer.view
 shutdown : U.State → Close.State
 shutdown s = B.shutdown (U.base s)
 Valid : U.State → Set
 Valid s = Backed (view s) (shutdown s)
 note-valid : ∀ origin s → Valid s → Valid (U.noteBirth origin s)
 note-valid nothing s valid = valid
 note-valid (just origin) s valid = valid
 step-preserves : ∀ a s {t} → U.step a s ≡ just t → Valid s → Valid t
 step-preserves (U.run a) s eq valid with U.baseAllowed a s ∧ U.birthFresh (U.birth a (U.base s)) (U.origins s)
 ... | false = case eq of λ ()
 ... | true with B.step a (U.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just b = case just-injective eq of λ { refl → note-valid (U.birth a (U.base s)) (record s { base = b }) (Physical.step-preserves a (U.base s) actual valid) }
 step-preserves (U.negotiate w ps flow) s eq valid = transport (Effects.MuxLayer.change (U.negotiate w ps flow) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Mux.direct-shutdown-same (U.negotiate w ps flow) s eq tt)) valid)
 step-preserves (U.allocateHandle w hid mid) s eq valid = transport (Effects.MuxLayer.change (U.allocateHandle w hid mid) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Mux.direct-shutdown-same (U.allocateHandle w hid mid) s eq tt)) valid)
 step-preserves (U.registerCounters w) s eq valid = transport (Effects.MuxLayer.change (U.registerCounters w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Mux.direct-shutdown-same (U.registerCounters w) s eq tt)) valid)
 step-preserves (U.configureMux w plan limit bound keys) s eq valid = transport (Effects.MuxLayer.change (U.configureMux w plan limit bound keys) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Mux.direct-shutdown-same (U.configureMux w plan limit bound keys) s eq tt)) valid)
 step-preserves (U.publishSuccess w) s eq valid = transport (Effects.MuxLayer.change (U.publishSuccess w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Mux.direct-shutdown-same (U.publishSuccess w) s eq tt)) valid)
 step-preserves (U.startupStep w action) s eq valid = transport (Effects.MuxLayer.change (U.startupStep w action) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Mux.direct-shutdown-same (U.startupStep w action) s eq tt)) valid)

 initialized-valid : ∀ c {s} → U.initial c ≡ just s → Valid s
 initialized-valid c eq with IG.handles (IG.execution (Machine.inboundGovernor (O.core c))) | IG.muxes (IG.execution (Machine.inboundGovernor (O.core c))) | B.initial c in actual
 ... | [] | [] | just b = case just-injective eq of λ { refl → Physical.initialized-valid c actual }
 ... | _ ∷ _ | _ | _ = case eq of λ ()
 ... | [] | _ ∷ _ | _ = case eq of λ ()
 ... | [] | [] | nothing = case eq of λ ()

module Protocol where
 private module P = ProtocolModel using (enterProtocolBody; appendProtocolPayload; egressMuxer; State; asyncInfraResult; asyncProtocolResult; base; commitClean; control; deregisterInfra; deregisterProtocol; forkInitiator; forkResponder; infrastructureReturn; inheritedAllowed; initial; protocolException; protocolReturned; publishInfra; publishProtocol; registerProtocol; returnProtocol; run; step; submitDbWrite; awaitDbWrite; dbWriteFailed; writerComplete; writerSeal)
 private module U = MuxModel Types.TypedResult using (base; initial; step)
 view : P.State → Effects.Registry
 view = Effects.ProtocolLayer.view
 shutdown : P.State → Close.State
 shutdown s = B.shutdown (U.base (P.base s))
 Valid : P.State → Set
 Valid s = Backed (view s) (shutdown s)
 step-preserves : ∀ a s {t} → P.step a s ≡ just t → Valid s → Valid t
 step-preserves (P.run a) s eq valid with P.inheritedAllowed a
 ... | false = case eq of λ ()
 ... | true with U.step a (P.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just u = case just-injective eq of λ { refl → Mux.step-preserves a (P.base s) actual valid }
 step-preserves (P.forkResponder w j gen) s eq valid = transport (Effects.ProtocolLayer.change (P.forkResponder w j gen) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Protocol.direct-shutdown-same (P.forkResponder w j gen) s eq tt)) valid)
 step-preserves (P.forkInitiator w j gen n) s eq valid = transport (Effects.ProtocolLayer.change (P.forkInitiator w j gen n) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Protocol.direct-shutdown-same (P.forkInitiator w j gen n) s eq tt)) valid)
 step-preserves (P.registerProtocol j) s eq valid = transport (Effects.ProtocolLayer.change (P.registerProtocol j) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Protocol.direct-shutdown-same (P.registerProtocol j) s eq tt)) valid)
 step-preserves (P.enterProtocolBody j) s eq valid = transport (Effects.ProtocolLayer.change (P.enterProtocolBody j) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Protocol.direct-shutdown-same (P.enterProtocolBody j) s eq tt)) valid)
 step-preserves (P.appendProtocolPayload j bytes) s eq valid = transport (Effects.ProtocolLayer.change (P.appendProtocolPayload j bytes) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Protocol.direct-shutdown-same (P.appendProtocolPayload j bytes) s eq tt)) valid)
 step-preserves (P.egressMuxer w action) s eq valid = transport (Effects.ProtocolLayer.change (P.egressMuxer w action) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Protocol.direct-shutdown-same (P.egressMuxer w action) s eq tt)) valid)
 step-preserves (P.protocolReturned j) s eq valid = transport (Effects.ProtocolLayer.change (P.protocolReturned j) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Protocol.direct-shutdown-same (P.protocolReturned j) s eq tt)) valid)
 step-preserves (P.commitClean j) s eq valid = transport (Effects.ProtocolLayer.change (P.commitClean j) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Protocol.direct-shutdown-same (P.commitClean j) s eq tt)) valid)
 step-preserves (P.protocolException j err) s eq valid = transport (Effects.ProtocolLayer.change (P.protocolException j err) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Protocol.direct-shutdown-same (P.protocolException j err) s eq tt)) valid)
 step-preserves (P.returnProtocol j) s eq valid = transport (Effects.ProtocolLayer.change (P.returnProtocol j) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Protocol.direct-shutdown-same (P.returnProtocol j) s eq tt)) valid)
 step-preserves (P.publishProtocol j) s eq valid = transport (Effects.ProtocolLayer.change (P.publishProtocol j) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Protocol.direct-shutdown-same (P.publishProtocol j) s eq tt)) valid)
 step-preserves (P.deregisterProtocol j) s eq valid = transport (Effects.ProtocolLayer.change (P.deregisterProtocol j) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Protocol.direct-shutdown-same (P.deregisterProtocol j) s eq tt)) valid)
 step-preserves (P.asyncProtocolResult j) s eq valid = transport (Effects.ProtocolLayer.change (P.asyncProtocolResult j) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Protocol.direct-shutdown-same (P.asyncProtocolResult j) s eq tt)) valid)
 step-preserves (P.infrastructureReturn w role err) s eq valid = transport (Effects.ProtocolLayer.change (P.infrastructureReturn w role err) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Protocol.direct-shutdown-same (P.infrastructureReturn w role err) s eq tt)) valid)
 step-preserves (P.publishInfra w role) s eq valid = transport (Effects.ProtocolLayer.change (P.publishInfra w role) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Protocol.direct-shutdown-same (P.publishInfra w role) s eq tt)) valid)
 step-preserves (P.deregisterInfra w role) s eq valid = transport (Effects.ProtocolLayer.change (P.deregisterInfra w role) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Protocol.direct-shutdown-same (P.deregisterInfra w role) s eq tt)) valid)
 step-preserves (P.asyncInfraResult w role) s eq valid = transport (Effects.ProtocolLayer.change (P.asyncInfraResult w role) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Protocol.direct-shutdown-same (P.asyncInfraResult w role) s eq tt)) valid)
 step-preserves (P.control w action) s eq valid = transport (Effects.ProtocolLayer.change (P.control w action) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Protocol.direct-shutdown-same (P.control w action) s eq tt)) valid)
 step-preserves (P.submitDbWrite j d) s eq valid = transport (Effects.ProtocolLayer.change (P.submitDbWrite j d) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Protocol.direct-shutdown-same (P.submitDbWrite j d) s eq tt)) valid)
 step-preserves (P.awaitDbWrite j) s eq valid = transport (Effects.ProtocolLayer.change (P.awaitDbWrite j) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Protocol.direct-shutdown-same (P.awaitDbWrite j) s eq tt)) valid)
 step-preserves (P.dbWriteFailed j) s eq valid = transport (Effects.ProtocolLayer.change (P.dbWriteFailed j) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Protocol.direct-shutdown-same (P.dbWriteFailed j) s eq tt)) valid)
 step-preserves (P.writerComplete d) s eq valid = transport (Effects.ProtocolLayer.change (P.writerComplete d) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Protocol.direct-shutdown-same (P.writerComplete d) s eq tt)) valid)
 step-preserves (P.writerSeal err) s eq valid = transport (Effects.ProtocolLayer.change (P.writerSeal err) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Protocol.direct-shutdown-same (P.writerSeal err) s eq tt)) valid)

 initialized-valid : ∀ c {s} → P.initial c ≡ just s → Valid s
 initialized-valid c eq with U.initial c in actual
 ... | nothing = case eq of λ ()
 ... | just lower = case just-injective eq of λ { refl → Mux.initialized-valid c actual }

module Monitor (isBearerClosed : ErrorId → Bool) where
 private module M = MonitorModel isBearerClosed using (State; base; beginDead; commitTracer; consume; delegateAllowed; finishDead; finishProtocolTrace; handleSelected; initial; run; sampleTracer; step)
 private module P = ProtocolModel using (enterProtocolBody; appendProtocolPayload; egressMuxer; initial; step)
 view : M.State → Effects.Registry
 view = Effects.MonitorLayer.view isBearerClosed
 shutdown : M.State → Close.State
 shutdown s = Protocol.shutdown (M.base s)
 Valid : M.State → Set
 Valid s = Backed (view s) (shutdown s)
 step-preserves : ∀ a s {t} → M.step a s ≡ just t → Valid s → Valid t
 step-preserves (M.run a) s eq valid with M.delegateAllowed a s
 ... | false = case eq of λ ()
 ... | true with P.step a (M.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just lower = case just-injective eq of λ { refl → Protocol.step-preserves a (M.base s) actual valid }
 step-preserves (M.consume w) s eq valid = transport (Effects.MonitorLayer.change isBearerClosed (M.consume w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Monitor.direct-shutdown-same isBearerClosed (M.consume w) s eq tt)) valid)
 step-preserves (M.handleSelected w) s eq valid = transport (Effects.MonitorLayer.change isBearerClosed (M.handleSelected w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Monitor.direct-shutdown-same isBearerClosed (M.handleSelected w) s eq tt)) valid)
 step-preserves (M.sampleTracer w) s eq valid = transport (Effects.MonitorLayer.change isBearerClosed (M.sampleTracer w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Monitor.direct-shutdown-same isBearerClosed (M.sampleTracer w) s eq tt)) valid)
 step-preserves (M.commitTracer w) s eq valid = transport (Effects.MonitorLayer.change isBearerClosed (M.commitTracer w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Monitor.direct-shutdown-same isBearerClosed (M.commitTracer w) s eq tt)) valid)
 step-preserves (M.finishProtocolTrace w) s eq valid = transport (Effects.MonitorLayer.change isBearerClosed (M.finishProtocolTrace w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Monitor.direct-shutdown-same isBearerClosed (M.finishProtocolTrace w) s eq tt)) valid)
 step-preserves (M.beginDead w) s eq valid = transport (Effects.MonitorLayer.change isBearerClosed (M.beginDead w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Monitor.direct-shutdown-same isBearerClosed (M.beginDead w) s eq tt)) valid)
 step-preserves (M.finishDead w) s eq valid = transport (Effects.MonitorLayer.change isBearerClosed (M.finishDead w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Monitor.direct-shutdown-same isBearerClosed (M.finishDead w) s eq tt)) valid)

 initialized-valid : ∀ c {s} → M.initial c ≡ just s → Valid s
 initialized-valid c eq with P.initial c in actual
 ... | nothing = case eq of λ ()
 ... | just lower = case just-injective eq of λ { refl → Protocol.initialized-valid c actual }

module Group (isBearerClosed : ErrorId → Bool) where
 private module G = GroupModel isBearerClosed using (State; abortOwner; base; beginAsyncDead; beginWholeClose; captureGroup; commitAsyncTracer; commitStoppedTracer; delegateAllowed; deliverGroup; deliverWhole; drainEmpty; finishAsyncDead; finishChildUnwind; finishGroup; finishNormalScope; finishStoppedTrace; finishWholeClose; initial; joinGroup; joinWhole; observeStoppingTrace; observeTraceStopped; requestGroupCancel; requestShutdown; retireCounters; requestWholeCancel; run; sampleAsyncTracer; sampleStoppedTracer; selectShutdown; step; timeout2Elapsed; unwindReplacedBySync; writeAsyncFailure; writeStopped; writeStopping)
 private module M = MonitorModel isBearerClosed using (initial; step)
 view : G.State → Effects.Registry
 view = Effects.GroupLayer.view isBearerClosed
 shutdown : G.State → Close.State
 shutdown s = Monitor.shutdown isBearerClosed (G.base s)
 Valid : G.State → Set
 Valid s = Backed (view s) (shutdown s)
 step-preserves : ∀ a s {t} → G.step a s ≡ just t → Valid s → Valid t
 step-preserves (G.run a) s eq valid with G.delegateAllowed a s
 ... | false = case eq of λ ()
 ... | true with M.step a (G.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just lower = case just-injective eq of λ { refl → Monitor.step-preserves isBearerClosed a (G.base s) actual valid }
 step-preserves (G.requestShutdown w) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.requestShutdown w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.requestShutdown w) s eq tt)) valid)
 step-preserves (G.retireCounters w) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.retireCounters w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.retireCounters w) s eq tt)) valid)
 step-preserves (G.selectShutdown w) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.selectShutdown w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.selectShutdown w) s eq tt)) valid)
 step-preserves (G.observeStoppingTrace w) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.observeStoppingTrace w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.observeStoppingTrace w) s eq tt)) valid)
 step-preserves (G.writeStopping w) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.writeStopping w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.writeStopping w) s eq tt)) valid)
 step-preserves (G.captureGroup w order) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.captureGroup w order) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.captureGroup w order) s eq tt)) valid)
 step-preserves (G.requestGroupCancel w) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.requestGroupCancel w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.requestGroupCancel w) s eq tt)) valid)
 step-preserves (G.deliverGroup w) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.deliverGroup w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.deliverGroup w) s eq tt)) valid)
 step-preserves (G.joinGroup w) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.joinGroup w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.joinGroup w) s eq tt)) valid)
 step-preserves (G.finishGroup w) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.finishGroup w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.finishGroup w) s eq tt)) valid)
 step-preserves (G.drainEmpty w) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.drainEmpty w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.drainEmpty w) s eq tt)) valid)
 step-preserves (G.timeout2Elapsed w) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.timeout2Elapsed w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.timeout2Elapsed w) s eq tt)) valid)
 step-preserves (G.writeStopped w) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.writeStopped w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.writeStopped w) s eq tt)) valid)
 step-preserves (G.observeTraceStopped w) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.observeTraceStopped w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.observeTraceStopped w) s eq tt)) valid)
 step-preserves (G.sampleStoppedTracer w) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.sampleStoppedTracer w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.sampleStoppedTracer w) s eq tt)) valid)
 step-preserves (G.commitStoppedTracer w) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.commitStoppedTracer w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.commitStoppedTracer w) s eq tt)) valid)
 step-preserves (G.finishStoppedTrace w) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.finishStoppedTrace w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.finishStoppedTrace w) s eq tt)) valid)
 step-preserves (G.finishChildUnwind j) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.finishChildUnwind j) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.finishChildUnwind j) s eq tt)) valid)
 step-preserves (G.unwindReplacedBySync j err) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.unwindReplacedBySync j err) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.unwindReplacedBySync j err) s eq tt)) valid)
 step-preserves (G.abortOwner w err) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.abortOwner w err) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.abortOwner w err) s eq tt)) valid)
 step-preserves (G.beginWholeClose w order) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.beginWholeClose w order) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.beginWholeClose w order) s eq tt)) valid)
 step-preserves (G.requestWholeCancel w) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.requestWholeCancel w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.requestWholeCancel w) s eq tt)) valid)
 step-preserves (G.deliverWhole w) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.deliverWhole w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.deliverWhole w) s eq tt)) valid)
 step-preserves (G.joinWhole w) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.joinWhole w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.joinWhole w) s eq tt)) valid)
 step-preserves (G.finishWholeClose w) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.finishWholeClose w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.finishWholeClose w) s eq tt)) valid)
 step-preserves (G.finishNormalScope w) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.finishNormalScope w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.finishNormalScope w) s eq tt)) valid)
 step-preserves (G.writeAsyncFailure w) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.writeAsyncFailure w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.writeAsyncFailure w) s eq tt)) valid)
 step-preserves (G.beginAsyncDead w) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.beginAsyncDead w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.beginAsyncDead w) s eq tt)) valid)
 step-preserves (G.sampleAsyncTracer w) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.sampleAsyncTracer w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.sampleAsyncTracer w) s eq tt)) valid)
 step-preserves (G.commitAsyncTracer w) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.commitAsyncTracer w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.commitAsyncTracer w) s eq tt)) valid)
 step-preserves (G.finishAsyncDead w) s eq valid = transport (Effects.GroupLayer.change isBearerClosed (G.finishAsyncDead w) s eq) (same-collected {registry = view s} (cong Close.collected (Aux.Group.direct-shutdown-same isBearerClosed (G.finishAsyncDead w) s eq tt)) valid)

 initialized-valid : ∀ c {s} → G.initial c ≡ just s → Valid s
 initialized-valid c eq with M.initial c in actual
 ... | nothing = case eq of λ ()
 ... | just lower = case just-injective eq of λ { refl → Monitor.initialized-valid isBearerClosed c actual }

-- Post-mux coordinator acknowledgment is available only through its guarded
-- physical delivery routes, or the exact physical-result observation.
module Exit (isBearerClosed : ErrorId → Bool) where
 private module W = ExitModel isBearerClosed using (State; acknowledgeFinished; acknowledgeReleaseFinished; deliverReleaseMux; base; beginExit; bodyExited; bufferScope; choosePolicy; classifying; cleanup; cleanupComplete; control; currentCapture; delegateAllowed; deliverShutdownMux; deliverShutdownTimeWait; enterFinalizer; errorTracing; exits; finalizing; finishCleanup; initial; nodeDelivery; nodeRethrow; noteCleanup; observeBufferException; observeBufferReturn; observeErrorTrace; observeNodeDelivery; peerRethrow; phase; publishAsyncResult; resultAvailable; resultReady; rethrow; run; setSource; shared; shutdown; shutdownStep; source; step)
 private module G = GroupModel isBearerClosed using (abortOwner; abortStage; base; initial; ownerContext; poolAt; step)
 private module MonitorModelAt = MonitorModel isBearerClosed using (base)
 private module U = MuxModel Types.TypedResult using (frames)
 private module P = ProtocolModel using (enterProtocolBody; appendProtocolPayload; egressMuxer; base; noParent)
 private module A = Aux.Exit isBearerClosed using (Valid; exits-present; lower-valid; plain-shutdown-same; resultReady-present)
 view : W.State → Effects.Registry
 view = Effects.ExitLayer.view isBearerClosed
 Valid : W.State → Set
 Valid s = Backed (view s) (W.shutdown s)
 source-valid : ∀ c s → Valid s → Valid (W.setSource c s)
 source-valid c s valid = valid
 control-preserves : ∀ a s {t} → W.control a s ≡ just t → Valid s →
   (a ≡ Close.acknowledgeDelivery → AwaitBacked (view s) (W.shutdown s)) → Valid t
 control-preserves a s eq valid safe with Close.step (S.cm (W.shared s)) (λ w → W.resultReady w s) a (W.shutdown s) in actual
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → close-preserves (view s) (S.cm (W.shared s)) (λ w → W.resultReady w s) a (W.shutdown s) actual valid safe }
 owner-present : ∀ w s {f mid} → G.ownerContext w s ≡ just (f , mid) → Aux.Group.Valid isBearerClosed s → Aux.Present w (Effects.GroupLayer.view isBearerClosed s)
 owner-present w s actual valid with lookup w (U.frames (P.base (MonitorModelAt.base (G.base s)))) in found
 ... | nothing = case actual of λ ()
 ... | just f = valid w f found
 abort-present : ∀ w err s {t} → G.step (G.abortOwner w err) s ≡ just t → Aux.Group.Valid isBearerClosed s → Aux.Present w (Effects.GroupLayer.view isBearerClosed s)
 abort-present w err s actual valid with G.abortStage w s | G.ownerContext w s in owned | P.noParent (G.poolAt w s)
 ... | true | just (f , mid) | true = owner-present w s owned valid
 ... | false | _ | _ = case actual of λ ()
 ... | true | nothing | _ = case actual of λ ()
 ... | true | just pair | false = case actual of λ ()
 step-preserves : ∀ a s {t} → W.step a s ≡ just t → A.Valid s → Valid s → Valid t
 step-preserves (W.run a) s eq aux valid with W.delegateAllowed a
 ... | false = case eq of λ ()
 ... | true with G.step a (W.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just g = case just-injective eq of λ { refl → Group.step-preserves isBearerClosed a (W.base s) actual valid }
 step-preserves (W.shutdownStep Close.captureSnapshot) s eq aux valid = control-preserves Close.captureSnapshot s eq valid (λ ())
 step-preserves (W.shutdownStep Close.readEntry) s eq aux valid = control-preserves Close.readEntry s eq valid (λ ())
 step-preserves (W.shutdownStep Close.requestCancellation) s eq aux valid = control-preserves Close.requestCancellation s eq valid (λ ())
 step-preserves (W.shutdownStep Close.finishTraversal) s eq aux valid = control-preserves Close.finishTraversal s eq valid (λ ())
 step-preserves (W.shutdownStep Close.finishClose) s eq aux valid = control-preserves Close.finishClose s eq valid (λ ())
 step-preserves (W.shutdownStep Close.acknowledgeDelivery) s () aux valid
 step-preserves (W.deliverShutdownMux err) s eq aux valid with Close.phase (W.shutdown s) in awaited
 ... | Close.awaitDelivery e w with G.step (G.abortOwner w err) (W.base s) in delivered
 ...   | nothing = case eq of λ ()
 ...   | just g = control-preserves Close.acknowledgeDelivery (record s { base = g }) eq
   (Group.step-preserves isBearerClosed (G.abortOwner w err) (W.base s) delivered valid)
   (λ _ → await-backed {registry = Effects.GroupLayer.view isBearerClosed g}
     (trans (cong Close.phase (Aux.Group.direct-shutdown-same isBearerClosed (G.abortOwner w err) (W.base s) delivered tt)) awaited)
     (present-transport (Effects.GroupLayer.change isBearerClosed (G.abortOwner w err) (W.base s) delivered)
       (abort-present w err (W.base s) delivered (A.lower-valid {s = s} aux))))
 step-preserves (W.deliverShutdownMux err) s eq aux valid | Close.initial = case eq of λ ()
 step-preserves (W.deliverShutdownMux err) s eq aux valid | Close.reading = case eq of λ ()
 step-preserves (W.deliverShutdownMux err) s eq aux valid | Close.sendReady e w = case eq of λ ()
 step-preserves (W.deliverShutdownMux err) s eq aux valid | Close.awaitResults = case eq of λ ()
 step-preserves (W.deliverShutdownMux err) s eq aux valid | Close.closed = case eq of λ ()
 step-preserves W.acknowledgeFinished s eq aux valid with Close.phase (W.shutdown s) in awaited
 ... | Close.awaitDelivery e w with W.resultReady w s in ready
 ...   | true = control-preserves Close.acknowledgeDelivery s eq valid (λ _ → await-backed {registry = view s} awaited (A.resultReady-present {s = s} {w = w} aux ready))
 ...   | false = case eq of λ ()
 step-preserves W.acknowledgeFinished s eq aux valid | Close.initial = case eq of λ ()
 step-preserves W.acknowledgeFinished s eq aux valid | Close.reading = case eq of λ ()
 step-preserves W.acknowledgeFinished s eq aux valid | Close.sendReady e w = case eq of λ ()
 step-preserves W.acknowledgeFinished s eq aux valid | Close.awaitResults = case eq of λ ()
 step-preserves W.acknowledgeFinished s eq aux valid | Close.closed = case eq of λ ()
 step-preserves (W.deliverReleaseMux caller err) s eq aux valid = transport (Effects.ExitLayer.change isBearerClosed (W.deliverReleaseMux caller err) s eq) (same-collected {registry = view s} (cong Close.collected (A.plain-shutdown-same (W.deliverReleaseMux caller err) s eq tt)) valid)
 step-preserves (W.acknowledgeReleaseFinished caller) s eq aux valid = transport (Effects.ExitLayer.change isBearerClosed (W.acknowledgeReleaseFinished caller) s eq) (same-collected {registry = view s} (cong Close.collected (A.plain-shutdown-same (W.acknowledgeReleaseFinished caller) s eq tt)) valid)
 step-preserves (W.beginExit w) s eq aux valid = transport (Effects.ExitLayer.change isBearerClosed (W.beginExit w) s eq) (same-collected {registry = view s} (cong Close.collected (A.plain-shutdown-same (W.beginExit w) s eq tt)) valid)
 step-preserves (W.observeBufferReturn w) s eq aux valid = transport (Effects.ExitLayer.change isBearerClosed (W.observeBufferReturn w) s eq) (same-collected {registry = view s} (cong Close.collected (A.plain-shutdown-same (W.observeBufferReturn w) s eq tt)) valid)
 step-preserves (W.observeBufferException w result) s eq aux valid = transport (Effects.ExitLayer.change isBearerClosed (W.observeBufferException w result) s eq) (same-collected {registry = view s} (cong Close.collected (A.plain-shutdown-same (W.observeBufferException w result) s eq tt)) valid)
 step-preserves (W.choosePolicy w policy) s eq aux valid = transport (Effects.ExitLayer.change isBearerClosed (W.choosePolicy w policy) s eq) (same-collected {registry = view s} (cong Close.collected (A.plain-shutdown-same (W.choosePolicy w policy) s eq tt)) valid)
 step-preserves (W.observeErrorTrace w) s eq aux valid = transport (Effects.ExitLayer.change isBearerClosed (W.observeErrorTrace w) s eq) (same-collected {registry = view s} (cong Close.collected (A.plain-shutdown-same (W.observeErrorTrace w) s eq tt)) valid)
 step-preserves (W.observeNodeDelivery w) s eq aux valid = transport (Effects.ExitLayer.change isBearerClosed (W.observeNodeDelivery w) s eq) (same-collected {registry = view s} (cong Close.collected (A.plain-shutdown-same (W.observeNodeDelivery w) s eq tt)) valid)
 step-preserves (W.rethrow w) s eq aux valid = transport (Effects.ExitLayer.change isBearerClosed (W.rethrow w) s eq) (same-collected {registry = view s} (cong Close.collected (A.plain-shutdown-same (W.rethrow w) s eq tt)) valid)
 step-preserves (W.enterFinalizer w) s eq aux valid = transport (Effects.ExitLayer.change isBearerClosed (W.enterFinalizer w) s eq) (same-collected {registry = view s} (cong Close.collected (A.plain-shutdown-same (W.enterFinalizer w) s eq tt)) valid)
 step-preserves (W.cleanup w action) s eq aux valid = transport (Effects.ExitLayer.change isBearerClosed (W.cleanup w action) s eq) (same-collected {registry = view s} (cong Close.collected (A.plain-shutdown-same (W.cleanup w action) s eq tt)) valid)
 step-preserves (W.finishCleanup w) s eq aux valid = transport (Effects.ExitLayer.change isBearerClosed (W.finishCleanup w) s eq) (same-collected {registry = view s} (cong Close.collected (A.plain-shutdown-same (W.finishCleanup w) s eq tt)) valid)
 step-preserves (W.publishAsyncResult w) s eq aux valid = transport (Effects.ExitLayer.change isBearerClosed (W.publishAsyncResult w) s eq) (same-collected {registry = view s} (cong Close.collected (A.plain-shutdown-same (W.publishAsyncResult w) s eq tt)) valid)
 step-preserves (W.deliverShutdownTimeWait err) s eq aux valid with Close.phase (W.shutdown s) in awaited
 ... | Close.awaitDelivery e w with lookup w (W.exits s) in found | lookup w (S.cleanups (W.shared s))
 ...   | just f | just (S.cleanupWaiting captured) with W.phase f | W.currentCapture w f s
 ...     | W.finalizing body | true with O.advance (O.inbound (Machine.cleanupStep w (Cleanup.interruptTimeWait err))) (W.source s) in advanced
 ...       | nothing = case eq of λ ()
 ...       | just c = control-preserves Close.acknowledgeDelivery
   (record (W.setSource c s) { exits = W.noteCleanup w (Cleanup.interruptTimeWait err) s }) eq valid
   (λ _ → await-backed {registry = view s} awaited (A.exits-present {s = s} aux w f found))
 step-preserves (W.deliverShutdownTimeWait err) s eq aux valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting captured) | W.bufferScope outcome | _ = case eq of λ ()
 step-preserves (W.deliverShutdownTimeWait err) s eq aux valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting captured) | W.classifying old | _ = case eq of λ ()
 step-preserves (W.deliverShutdownTimeWait err) s eq aux valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting captured) | W.errorTracing old policy | _ = case eq of λ ()
 step-preserves (W.deliverShutdownTimeWait err) s eq aux valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting captured) | W.peerRethrow old | _ = case eq of λ ()
 step-preserves (W.deliverShutdownTimeWait err) s eq aux valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting captured) | W.nodeDelivery old | _ = case eq of λ ()
 step-preserves (W.deliverShutdownTimeWait err) s eq aux valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting captured) | W.nodeRethrow old | _ = case eq of λ ()
 step-preserves (W.deliverShutdownTimeWait err) s eq aux valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting captured) | W.bodyExited body | _ = case eq of λ ()
 step-preserves (W.deliverShutdownTimeWait err) s eq aux valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting captured) | W.finalizing body | false = case eq of λ ()
 step-preserves (W.deliverShutdownTimeWait err) s eq aux valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting captured) | W.cleanupComplete body outcome | _ = case eq of λ ()
 step-preserves (W.deliverShutdownTimeWait err) s eq aux valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting captured) | W.resultAvailable body outcome | _ = case eq of λ ()
 step-preserves (W.deliverShutdownTimeWait err) s eq aux valid | Close.awaitDelivery e w | just f | just (S.cleanupAcquire) = case eq of λ ()
 step-preserves (W.deliverShutdownTimeWait err) s eq aux valid | Close.awaitDelivery e w | just f | just (S.cleanupSelect savedLease) = case eq of λ ()
 step-preserves (W.deliverShutdownTimeWait err) s eq aux valid | Close.awaitDelivery e w | just f | just (S.cleanupClose savedLease map tail) = case eq of λ ()
 step-preserves (W.deliverShutdownTimeWait err) s eq aux valid | Close.awaitDelivery e w | just f | just (S.cleanupPublish savedLease map tail) = case eq of λ ()
 step-preserves (W.deliverShutdownTimeWait err) s eq aux valid | Close.awaitDelivery e w | just f | just (S.cleanupRestore savedLease error) = case eq of λ ()
 step-preserves (W.deliverShutdownTimeWait err) s eq aux valid | Close.awaitDelivery e w | just f | just (S.cleanupFinalize captured outcome) = case eq of λ ()
 step-preserves (W.deliverShutdownTimeWait err) s eq aux valid | Close.awaitDelivery e w | just f | just (S.cleanupCount outcome) = case eq of λ ()
 step-preserves (W.deliverShutdownTimeWait err) s eq aux valid | Close.awaitDelivery e w | just f | just (S.cleanupDone outcome) = case eq of λ ()
 step-preserves (W.deliverShutdownTimeWait err) s eq aux valid | Close.awaitDelivery e w | nothing | _ = case eq of λ ()
 step-preserves (W.deliverShutdownTimeWait err) s eq aux valid | Close.awaitDelivery e w | just f | nothing = case eq of λ ()
 step-preserves (W.deliverShutdownTimeWait err) s eq aux valid | Close.initial = case eq of λ ()
 step-preserves (W.deliverShutdownTimeWait err) s eq aux valid | Close.reading = case eq of λ ()
 step-preserves (W.deliverShutdownTimeWait err) s eq aux valid | Close.sendReady e w = case eq of λ ()
 step-preserves (W.deliverShutdownTimeWait err) s eq aux valid | Close.awaitResults = case eq of λ ()
 step-preserves (W.deliverShutdownTimeWait err) s eq aux valid | Close.closed = case eq of λ ()

 initialized-valid : ∀ c {s} → W.initial c ≡ just s → Valid s
 initialized-valid c eq with G.initial c in actual
 ... | nothing = case eq of λ ()
 ... | just lower = case just-injective eq of λ { refl → Group.initialized-valid isBearerClosed c actual }

module Cancellation (isBearerClosed : ErrorId → Bool) where
 private module X = CancellationModel isBearerClosed using (State; deliver; deliverShutdown; initial; observeCancellation; observeErrorTraceException; run; step; target; traceThrew)
 private module W = ExitModel isBearerClosed using (bodyExited; bufferScope; classifying; cleanupComplete; edit; errorTracing; exits; finalizing; initial; nodeDelivery; nodeRethrow; peerRethrow; phase; resultAvailable; shutdown)
 private module A = Aux.Exit isBearerClosed using (Valid; exits-present)
 view : X.State → Effects.Registry
 view = Effects.CancellationLayer.view isBearerClosed
 Valid : X.State → Set
 Valid = Exit.Valid isBearerClosed
 delivered-valid : ∀ window w err s {t} → X.deliver window w err s ≡ just t → Valid s → Valid t
 delivered-valid window w err s eq valid with lookup w (W.exits s)
 ... | nothing = case eq of λ ()
 ... | just f with X.target window err (W.phase f)
 ...   | nothing = case eq of λ ()
 ...   | just pc = case just-injective eq of λ { refl → valid }
 trace-valid : ∀ w err s {t} → X.traceThrew w err s ≡ just t → Valid s → Valid t
 trace-valid w err s eq valid with lookup w (W.exits s)
 ... | nothing = case eq of λ ()
 ... | just f with W.phase f
 ...   | W.errorTracing original policy = case just-injective eq of λ { refl → valid }
 trace-valid w err s eq valid | just f | W.bufferScope outcome = case eq of λ ()
 trace-valid w err s eq valid | just f | W.classifying old = case eq of λ ()
 trace-valid w err s eq valid | just f | W.peerRethrow old = case eq of λ ()
 trace-valid w err s eq valid | just f | W.nodeDelivery old = case eq of λ ()
 trace-valid w err s eq valid | just f | W.nodeRethrow old = case eq of λ ()
 trace-valid w err s eq valid | just f | W.bodyExited body = case eq of λ ()
 trace-valid w err s eq valid | just f | W.finalizing body = case eq of λ ()
 trace-valid w err s eq valid | just f | W.cleanupComplete body outcome = case eq of λ ()
 trace-valid w err s eq valid | just f | W.resultAvailable body outcome = case eq of λ ()
 step-preserves : ∀ a s {t} → X.step a s ≡ just t → A.Valid s → Valid s → Valid t
 step-preserves (X.run a) s eq aux valid = Exit.step-preserves isBearerClosed a s eq aux valid
 step-preserves (X.observeCancellation window w err) s eq aux valid = delivered-valid window w err s eq valid
 step-preserves (X.observeErrorTraceException w err) s eq aux valid = trace-valid w err s eq valid
 step-preserves (X.deliverShutdown window err) s eq aux valid with Close.phase (W.shutdown s) in awaited
 ... | Close.awaitDelivery e w with lookup w (W.exits s) in found
 ...   | nothing = case eq of λ ()
 ...   | just f with X.target window err (W.phase f)
 ...     | nothing = case eq of λ ()
 ...     | just pc = Exit.control-preserves isBearerClosed Close.acknowledgeDelivery
   (record s { exits = W.edit w f pc s }) eq valid (λ _ → await-backed {registry = view s} awaited (A.exits-present {s = s} aux w f found))
 step-preserves (X.deliverShutdown window err) s eq aux valid | Close.initial = case eq of λ ()
 step-preserves (X.deliverShutdown window err) s eq aux valid | Close.reading = case eq of λ ()
 step-preserves (X.deliverShutdown window err) s eq aux valid | Close.sendReady e w = case eq of λ ()
 step-preserves (X.deliverShutdown window err) s eq aux valid | Close.awaitResults = case eq of λ ()
 step-preserves (X.deliverShutdown window err) s eq aux valid | Close.closed = case eq of λ ()

 initialized-valid : ∀ c {s} → X.initial c ≡ just s → Valid s
 initialized-valid c eq with W.initial c in actual
 ... | nothing = case eq of λ ()
 ... | just lower = case just-injective eq of λ { refl → Exit.initialized-valid isBearerClosed c actual }

-- Outer callback adapters may enact these exact plans. Plain plans preserve
-- the coordinator; an acknowledgment additionally carries its real recipient.
module Unwind (isBearerClosed : ErrorId → Bool) where
 private module R = UnwindModel isBearerClosed using (Plan; State; acknowledge; allowed; async; base; beginClose; beginDead; cancellationPlan; choose; commitDead; continueSync; deliverCancel; deliverShutdown; deliveryControl; deliveryRoute; enact; finishClose; finishDead; free; handoff; inherited; initial; join; local; machine; observeCancellation; observeDeadTraceException; observeFailure; owner; pool; poolAt; protocols; requestCancel; run; sampleDead; setSource; source; start; step; transfer; writeAsyncFailure)
 private module X = CancellationModel isBearerClosed using (initial; step)
 private module W = ExitModel isBearerClosed using (control; exits; shutdown)
 private module U = MuxModel Types.TypedResult using (handleAllocated; progress; promisePublished; returnedSuccess)
 private module P = ProtocolModel using (enterProtocolBody; appendProtocolPayload; egressMuxer; muxAt; noParent)
 private module A = Aux.Unwind isBearerClosed using (Valid; chosen-nonack; frames-present; lower-valid)
 private module Pool = ProtocolModel.Pool using (step)
 view : R.State → Effects.Registry
 view = Effects.UnwindLayer.view isBearerClosed
 shutdown : R.State → Close.State
 shutdown s = W.shutdown (R.base s)
 Valid : R.State → Set
 Valid s = Backed (view s) (shutdown s)
 source-valid : ∀ c s → Valid s → Valid (R.setSource c s)
 source-valid c s valid = valid
 data Plain : R.Plan → Set where
  plain-local : ∀ fs → Plain (R.local fs)
  plain-machine : ∀ action fs → Plain (R.machine action fs)
  plain-pool : ∀ w u action fs → Plain (R.pool w u action fs)
  plain-transfer : ∀ w frame fs → Plain (R.transfer w frame fs)
 data AckSafe : R.Plan → R.State → Set where
  plain-safe : ∀ {p s} → Plain p → AckSafe p s
  inherited-safe : ∀ {a s} → AckSafe (R.inherited a) s
  acknowledge-safe : ∀ {p s} → Plain p → AwaitBacked (view s) (shutdown s) → AckSafe (R.acknowledge p) s
 plain-view : ∀ {p} s {t} → Plain p → R.enact p s ≡ just t → view t ≡ view s
 plain-view s (plain-local fs) eq = case just-injective eq of λ { refl → refl }
 plain-view s (plain-machine action fs) eq with O.advance action (R.source s)
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → refl }
 plain-view s (plain-pool w u action fs) eq with Pool.step action (R.poolAt w s)
 ... | nothing = case eq of λ ()
 ... | just pool = case just-injective eq of λ { refl → refl }
 plain-view s (plain-transfer w frame fs) eq = case just-injective eq of λ { refl → refl }
 plain-shutdown : ∀ {p} s {t} → Plain p → R.enact p s ≡ just t → shutdown t ≡ shutdown s
 plain-shutdown s (plain-local fs) eq = case just-injective eq of λ { refl → refl }
 plain-shutdown s (plain-machine action fs) eq with O.advance action (R.source s)
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → refl }
 plain-shutdown s (plain-pool w u action fs) eq with Pool.step action (R.poolAt w s)
 ... | nothing = case eq of λ ()
 ... | just pool = case just-injective eq of λ { refl → refl }
 plain-shutdown s (plain-transfer w frame fs) eq = case just-injective eq of λ { refl → refl }
 plain-preserves : ∀ {p} s {t} → Plain p → R.enact p s ≡ just t → Valid s → Valid t
 plain-preserves s plain eq valid = transport {P = ⊤} (Effects.stable (plain-view s plain eq))
   (same-collected {registry = view s} (cong Close.collected (plain-shutdown s plain eq)) valid)
 enact-preserves : ∀ p s {t} → R.enact p s ≡ just t → A.Valid s → Valid s → AckSafe p s → Valid t
 enact-preserves p s eq aux valid (plain-safe plain) = plain-preserves s plain eq valid
 enact-preserves (R.inherited action) s eq aux valid inherited-safe with X.step action (R.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just x = case just-injective eq of λ { refl → Cancellation.step-preserves isBearerClosed action (R.base s) actual (A.lower-valid {s = s} aux) valid }
 enact-preserves (R.acknowledge p) s eq aux valid (acknowledge-safe plain backed) with R.enact p s in actual
 ... | nothing = case eq of λ ()
 ... | just next with W.control Close.acknowledgeDelivery (R.base next) in acknowledged
 ...   | nothing = case eq of λ ()
 ...   | just w = case just-injective eq of λ { refl → Exit.control-preserves isBearerClosed Close.acknowledgeDelivery (R.base next) acknowledged
   (plain-preserves s plain actual valid)
   (λ _ awaited → present-transport {P = ⊤} (Effects.stable (plain-view s plain actual))
     (backed (trans (sym (cong Close.phase (plain-shutdown s plain actual))) awaited))) }
 -- Successful setup-failure selection always returns one local plan; the
 -- selected owner already resolves to a physical handler before any receipt.
 start-plain : ∀ w result route s {p} → R.start w result route s ≡ just p → Plain p
 start-plain w result route s eq with R.free w s | R.owner w s | lookup w (W.exits (R.base s)) | P.noParent (R.poolAt w s)
 ... | true | just f | nothing | true with U.progress f
 ...   | U.promisePublished hid mid with P.muxAt mid (R.protocols s)
 ...     | just mux with route f mux
 ...       | just path = case just-injective eq of λ { refl → plain-local _ }
 ...       | nothing = case eq of λ ()
 start-plain w result route s eq | true | just f | nothing | true | U.promisePublished hid mid | nothing = case eq of λ ()
 start-plain w result route s eq | true | just f | nothing | true | U.returnedSuccess = case eq of λ ()
 start-plain w result route s eq | true | just f | nothing | true | U.handleAllocated hid mid = case eq of λ ()
 start-plain w result route s eq | false | _ | _ | _ = case eq of λ ()
 start-plain w result route s eq | true | nothing | _ | _ = case eq of λ ()
 start-plain w result route s eq | true | just f | just exit | _ = case eq of λ ()
 start-plain w result route s eq | true | just f | nothing | false = case eq of λ ()
 start-present : ∀ w result route s {p} → R.start w result route s ≡ just p → A.Valid s → Aux.Present w (view s)
 start-present w result route s eq aux with R.free w s | R.owner w s in owned | lookup w (W.exits (R.base s)) | P.noParent (R.poolAt w s)
 ... | true | just f | nothing | true = A.frames-present {s = s} aux w f owned
 ... | false | _ | _ | _ = case eq of λ ()
 ... | true | nothing | _ | _ = case eq of λ ()
 ... | true | just f | just exit | _ = case eq of λ ()
 ... | true | just f | nothing | false = case eq of λ ()
 cancellation-plain : ∀ w site err s {p} → R.cancellationPlan w site err s ≡ just p → Plain p
 cancellation-plain w site err s eq with R.deliveryControl w site s
 ... | false = case eq of λ ()
 ... | true = start-plain w (R.async err) (λ f mux → R.deliveryRoute site f mux) s eq
 cancellation-present : ∀ w site err s {p} → R.cancellationPlan w site err s ≡ just p → A.Valid s → Aux.Present w (view s)
 cancellation-present w site err s eq aux with R.deliveryControl w site s
 ... | false = case eq of λ ()
 ... | true = start-present w (R.async err) (λ f mux → R.deliveryRoute site f mux) s eq aux
 choose-safe : ∀ a s {p} → R.choose a s ≡ just p → A.Valid s → AckSafe p s
 choose-safe a s {R.local fs} eq aux = plain-safe (plain-local fs)
 choose-safe a s {R.machine action fs} eq aux = plain-safe (plain-machine action fs)
 choose-safe a s {R.pool w u action fs} eq aux = plain-safe (plain-pool w u action fs)
 choose-safe a s {R.transfer w frame fs} eq aux = plain-safe (plain-transfer w frame fs)
 choose-safe a s {R.inherited action} eq aux = inherited-safe
 choose-safe (R.run action) s {R.acknowledge p} eq aux with R.allowed action s
 ... | false = case eq of λ ()
 ... | true = case eq of λ ()
 choose-safe (R.deliverShutdown site err) s {R.acknowledge p} eq aux with Close.phase (shutdown s) in awaited
 ... | Close.awaitDelivery e w with R.cancellationPlan w site err s in selected
 ...   | nothing = case eq of λ ()
 ...   | just plain = case just-injective eq of λ { refl → acknowledge-safe
   (cancellation-plain w site err s selected)
   (await-backed {registry = view s} awaited (cancellation-present w site err s selected aux)) }
 choose-safe (R.deliverShutdown site err) s {R.acknowledge p} eq aux | Close.initial = case eq of λ ()
 choose-safe (R.deliverShutdown site err) s {R.acknowledge p} eq aux | Close.reading = case eq of λ ()
 choose-safe (R.deliverShutdown site err) s {R.acknowledge p} eq aux | Close.sendReady e w = case eq of λ ()
 choose-safe (R.deliverShutdown site err) s {R.acknowledge p} eq aux | Close.awaitResults = case eq of λ ()
 choose-safe (R.deliverShutdown site err) s {R.acknowledge p} eq aux | Close.closed = case eq of λ ()
 choose-safe (R.observeFailure w site err) s {R.acknowledge p} eq aux = case A.chosen-nonack (R.observeFailure w site err) s eq aux tt of λ ()
 choose-safe (R.observeCancellation w site err) s {R.acknowledge p} eq aux = case A.chosen-nonack (R.observeCancellation w site err) s eq aux tt of λ ()
 choose-safe (R.beginClose w order) s {R.acknowledge p} eq aux = case A.chosen-nonack (R.beginClose w order) s eq aux tt of λ ()
 choose-safe (R.requestCancel w) s {R.acknowledge p} eq aux = case A.chosen-nonack (R.requestCancel w) s eq aux tt of λ ()
 choose-safe (R.deliverCancel w) s {R.acknowledge p} eq aux = case A.chosen-nonack (R.deliverCancel w) s eq aux tt of λ ()
 choose-safe (R.join w) s {R.acknowledge p} eq aux = case A.chosen-nonack (R.join w) s eq aux tt of λ ()
 choose-safe (R.finishClose w) s {R.acknowledge p} eq aux = case A.chosen-nonack (R.finishClose w) s eq aux tt of λ ()
 choose-safe (R.continueSync w) s {R.acknowledge p} eq aux = case A.chosen-nonack (R.continueSync w) s eq aux tt of λ ()
 choose-safe (R.writeAsyncFailure w) s {R.acknowledge p} eq aux = case A.chosen-nonack (R.writeAsyncFailure w) s eq aux tt of λ ()
 choose-safe (R.beginDead w) s {R.acknowledge p} eq aux = case A.chosen-nonack (R.beginDead w) s eq aux tt of λ ()
 choose-safe (R.sampleDead w) s {R.acknowledge p} eq aux = case A.chosen-nonack (R.sampleDead w) s eq aux tt of λ ()
 choose-safe (R.commitDead w) s {R.acknowledge p} eq aux = case A.chosen-nonack (R.commitDead w) s eq aux tt of λ ()
 choose-safe (R.finishDead w) s {R.acknowledge p} eq aux = case A.chosen-nonack (R.finishDead w) s eq aux tt of λ ()
 choose-safe (R.handoff w) s {R.acknowledge p} eq aux = case A.chosen-nonack (R.handoff w) s eq aux tt of λ ()
 choose-safe (R.observeDeadTraceException w err) s {R.acknowledge p} eq aux = case A.chosen-nonack (R.observeDeadTraceException w err) s eq aux tt of λ ()
 step-preserves : ∀ a s {t} → R.step a s ≡ just t → A.Valid s → Valid s → Valid t
 step-preserves a s eq aux valid with R.choose a s in chosen
 ... | nothing = case eq of λ ()
 ... | just p = enact-preserves p s eq aux valid (choose-safe a s chosen aux)
 initialized-valid : ∀ c {s} → R.initial c ≡ just s → Valid s
 initialized-valid c eq with X.initial c in actual
 ... | nothing = case eq of λ ()
 ... | just x = case just-injective eq of λ { refl → Cancellation.initialized-valid isBearerClosed c actual }
