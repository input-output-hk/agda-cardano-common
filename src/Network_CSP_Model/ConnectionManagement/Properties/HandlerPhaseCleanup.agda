{-# OPTIONS --guardedness #-}

-- Phase/cleanup validity for physical handler threads (CM-I4c). Every tracked
-- thread's phase determines the shared cleanup record of its worker: none before
-- the finalizer, some record while finalizing, and the completed record with the
-- observed outcome once cleanup completion or the Async result is recorded. An
-- untracked worker has no cleanup record. Every initialized HandlerSupervision
-- and OutboundHandlerSupervision run preserves this. Relative restricts the
-- agreement to workers outside an excluded set and is used by MuxPhaseCleanup
-- for workers owned by mux and exit frames.
module ConnectionManagement.Properties.HandlerPhaseCleanup where

open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (WorkerId; DecEq-Id)
open import ConnectionManagement.Store using (Store; lookup; put)
open import ConnectionManagement.Properties.Entries using (lookup-put)
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
open import ConnectionManagement.Properties.CleanupWriters using (QuietMachine; QuietOutbound; machine-same; outbound-same; exit-effect; cleanup-effect; stepped)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.OutboundAcquire as A

-- The cleanup record a handler phase requires.
Expected : H.Phase → Maybe S.CleanupPC → Set
Expected H.maskedSetup c = c ≡ nothing
Expected H.handshaking c = c ≡ nothing
Expected (H.caughtCancellation _) c = c ≡ nothing
Expected (H.cancellationPublished _) c = c ≡ nothing
Expected (H.bodyExited _) c = c ≡ nothing
Expected (H.finalizing _) c = Σ S.CleanupPC (λ p → c ≡ just p)
Expected (H.cleanupComplete _ outcome) c = c ≡ just (S.cleanupDone outcome)
Expected (H.resultAvailable _ outcome) c = c ≡ just (S.cleanupDone outcome)

-- An untracked worker has no cleanup record.
Agrees : Maybe H.Thread → Maybe S.CleanupPC → Set
Agrees nothing c = c ≡ nothing
Agrees (just t) c = Expected (H.phase t) c

module Raw where
 cleanupsOf : H.State → Store WorkerId S.CleanupPC
 cleanupsOf s = S.cleanups (M.world (H.source s))
 record Valid (s : H.State) : Set where
  constructor valid
  field agrees : ∀ w → Agrees (lookup w (H.threads s)) (lookup w (cleanupsOf s))
 open Valid public

 at : ∀ {s w t} → Valid s → lookup w (H.threads s) ≡ just t → Expected (H.phase t) (lookup w (cleanupsOf s))
 at {s} {w} v found = subst (λ x → Agrees x (lookup w (cleanupsOf s))) found (agrees v w)
 in-phase : ∀ {s w t p} → Valid s → lookup w (H.threads s) ≡ just t → H.phase t ≡ p → Expected p (lookup w (cleanupsOf s))
 in-phase {s} {w} v found ph = subst (λ p → Expected p (lookup w (cleanupsOf s))) ph (at v found)
 absent : ∀ {s w} → Valid s → lookup w (H.threads s) ≡ nothing → lookup w (cleanupsOf s) ≡ nothing
 absent {s} {w} v missing = subst (λ x → Agrees x (lookup w (cleanupsOf s))) missing (agrees v w)

 -- Threads and cleanup records both unchanged.
 transport : ∀ {s t} → H.threads t ≡ H.threads s → cleanupsOf t ≡ cleanupsOf s → Valid s → Valid t
 transport {s} {t} th cl v = valid λ q → subst (λ x → Agrees (lookup q x) (lookup q (cleanupsOf t))) (sym th)
   (subst (λ x → Agrees (lookup q (H.threads s)) (lookup q x)) (sym cl) (agrees v q))
 -- One thread written, cleanup records unchanged.
 update : ∀ {s t} w th → H.threads t ≡ put w th (H.threads s) → cleanupsOf t ≡ cleanupsOf s →
   Expected (H.phase th) (lookup w (cleanupsOf s)) → Valid s → Valid t
 update {s} {t} w th threads cl ok v = valid pointwise
  where
  pointwise : ∀ q → Agrees (lookup q (H.threads t)) (lookup q (cleanupsOf t))
  pointwise q rewrite threads | cl with q ≟ w
  ... | yes refl rewrite lookup-put w th (H.threads s) = ok
  ... | no other rewrite lookup-put-other w q th (H.threads s) other = agrees v q
 -- One worker's cleanup record written, threads unchanged.
 write : ∀ {s t} w th c → lookup w (H.threads s) ≡ just th → H.threads t ≡ H.threads s →
   cleanupsOf t ≡ put w c (cleanupsOf s) → Expected (H.phase th) (just c) → Valid s → Valid t
 write {s} {t} w th c found threads cl ok v = valid pointwise
  where
  pointwise : ∀ q → Agrees (lookup q (H.threads t)) (lookup q (cleanupsOf t))
  pointwise q rewrite threads | cl with q ≟ w
  ... | yes refl rewrite lookup-put w c (cleanupsOf s) | found = ok
  ... | no other rewrite lookup-put-other w q c (cleanupsOf s) other = agrees v q
 -- One worker's thread and cleanup record written together.
 both : ∀ {s t} w th c → H.threads t ≡ put w th (H.threads s) →
   cleanupsOf t ≡ put w c (cleanupsOf s) → Expected (H.phase th) (just c) → Valid s → Valid t
 both {s} {t} w th c threads cl ok v = valid pointwise
  where
  pointwise : ∀ q → Agrees (lookup q (H.threads t)) (lookup q (cleanupsOf t))
  pointwise q rewrite threads | cl with q ≟ w
  ... | yes refl rewrite lookup-put w th (H.threads s) | lookup-put w c (cleanupsOf s) = ok
  ... | no other rewrite lookup-put-other w q th (H.threads s) other | lookup-put-other w q c (cleanupsOf s) other = agrees v q

 -- Quiet source operations leave threads and cleanup records unchanged.
 dispatch-same : ∀ a s {t} → H.dispatch a s ≡ just t → QuietMachine a →
   H.threads t ≡ H.threads s × cleanupsOf t ≡ cleanupsOf s
 dispatch-same a s eq q with M.advance a (H.source s) in actual
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → refl , machine-same a (H.source s) actual q }
 dispatch-valid : ∀ a s {t} → H.dispatch a s ≡ just t → QuietMachine a → Valid s → Valid t
 dispatch-valid a s eq q v = transport (proj₁ (dispatch-same a s eq q)) (proj₂ (dispatch-same a s eq q)) v
 dispatch-relabel : ∀ a w th p s {t} → H.dispatchPhase a w th p s ≡ just t → QuietMachine a →
   Expected p (lookup w (cleanupsOf s)) → Valid s → Valid t
 dispatch-relabel a w th p s eq q ok v with H.dispatch a s in actual
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl →
   update w (H.handlerThread (H.captured th) p) (cong (put w (H.handlerThread (H.captured th) p)) (proj₁ (dispatch-same a s actual q)))
     (proj₂ (dispatch-same a s actual q)) ok v }
 -- handlerExit creates the record of the thread entering its finalizer.
 exit-after : ∀ w th x s {next} → H.dispatch (M.handlerExit w) s ≡ just next → Valid s →
   Valid (H.setPhase w th (H.finalizing x) next)
 exit-after w th x s eq v with M.advance (M.handlerExit w) (H.source s) in actual
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl →
   both w (H.handlerThread (H.captured th) (H.finalizing x)) S.cleanupAcquire refl
     (proj₂ (exit-effect w (H.source s) actual)) (S.cleanupAcquire , refl) v }
 dispatch-exit : ∀ w th x s {t} → H.dispatchPhase (M.handlerExit w) w th (H.finalizing x) s ≡ just t → Valid s → Valid t
 dispatch-exit w th x s eq v with H.dispatch (M.handlerExit w) s in actual
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → exit-after w th x s actual v }
 -- A cleanup step of a finalizing thread rewrites only that thread's record.
 cleanup-valid : ∀ w action th x s {t} → lookup w (H.threads s) ≡ just th → H.phase th ≡ H.finalizing x →
   H.dispatch (M.cleanupStep w action) s ≡ just t → Valid s → Valid t
 cleanup-valid w action th x s found ph eq v with M.advance (M.cleanupStep w action) (H.source s) in actual
 ... | nothing = case eq of λ ()
 ... | just c with cleanup-effect w action (H.source s) actual
 ...   | stepped prior seen live (next , rw) = case just-injective eq of λ { refl →
   write w th next found refl rw (subst (λ p → Expected p (just next)) (sym ph) (next , refl)) v }
 acknowledge-valid : ∀ s {t} → H.acknowledge s ≡ just t → Valid s → Valid t
 acknowledge-valid s eq v with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.acknowledgeDelivery (H.shutdown s)
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → transport refl refl v }
 -- An admission fork adds an untracked child, which has no cleanup record.
 fork-valid : ∀ w s {t} → H.forkAdmission w s ≡ just t → Valid s → Valid t
 fork-valid w s eq v with lookup w (S.admissions (M.world (H.source s)))
 ... | nothing = case eq of λ ()
 ... | just a with lookup (S.child (S.request a)) (H.threads s) in missing
 ...   | just old = case eq of λ ()
 ...   | nothing with M.advance (M.admissionStep w Server.fork) (H.source s) in actual
 ...     | nothing = case eq of λ ()
 ...     | just c with lookup (S.child (S.request a)) (S.handlers (M.world c))
 ...       | nothing = case eq of λ ()
 ...       | just handler = case just-injective eq of λ { refl →
   update (S.child (S.request a)) (H.handlerThread handler H.maskedSetup) refl
     (machine-same (M.admissionStep w Server.fork) (H.source s) actual tt) (absent v missing) v }
 handshake-valid : ∀ w err s {t} → H.deliverHandshake w err s ≡ just t → Valid s → Valid t
 handshake-valid w err s eq v with lookup w (H.threads s) in found
 ... | nothing = case eq of λ ()
 ... | just th with H.phase th in ph
 handshake-valid w err s eq v | just th | H.maskedSetup = case eq of λ ()
 handshake-valid w err s eq v | just th | H.handshaking = case just-injective eq of λ { refl → update w (H.handlerThread (H.captured th) (H.caughtCancellation err)) refl refl (in-phase v found ph) v }
 handshake-valid w err s eq v | just th | (H.caughtCancellation x) = case eq of λ ()
 handshake-valid w err s eq v | just th | (H.cancellationPublished x) = case eq of λ ()
 handshake-valid w err s eq v | just th | (H.bodyExited x) = case eq of λ ()
 handshake-valid w err s eq v | just th | (H.finalizing x) = case eq of λ ()
 handshake-valid w err s eq v | just th | (H.cleanupComplete x o) = case eq of λ ()
 handshake-valid w err s eq v | just th | (H.resultAvailable x o) = case eq of λ ()
 setup-valid : ∀ w err s {t} → H.deliverBlockedSetup w err s ≡ just t → Valid s → Valid t
 setup-valid w err s eq v with lookup w (H.threads s) in found
 ... | nothing = case eq of λ ()
 ... | just th with H.phase th in ph
 setup-valid w err s eq v | just th | H.maskedSetup = case just-injective eq of λ { refl → update w (H.handlerThread (H.captured th) (H.bodyExited err)) refl refl (in-phase v found ph) v }
 setup-valid w err s eq v | just th | H.handshaking = case eq of λ ()
 setup-valid w err s eq v | just th | (H.caughtCancellation x) = case eq of λ ()
 setup-valid w err s eq v | just th | (H.cancellationPublished x) = case eq of λ ()
 setup-valid w err s eq v | just th | (H.bodyExited x) = case eq of λ ()
 setup-valid w err s eq v | just th | (H.finalizing x) = case eq of λ ()
 setup-valid w err s eq v | just th | (H.cleanupComplete x o) = case eq of λ ()
 setup-valid w err s eq v | just th | (H.resultAvailable x o) = case eq of λ ()
 shutdown-valid : ∀ blocked err s {t} → H.deliverShutdown blocked err s ≡ just t → Valid s → Valid t
 shutdown-valid blocked err s eq v with Close.phase (H.shutdown s)
 ... | Close.awaitDelivery e′ w with blocked
 ...   | false with H.deliverHandshake w err s in delivered
 ...     | nothing = case eq of λ ()
 ...     | just next = acknowledge-valid next eq (handshake-valid w err s delivered v)
 shutdown-valid blocked err s eq v | Close.awaitDelivery e′ w | true with H.deliverBlockedSetup w err s in delivered
 ...     | nothing = case eq of λ ()
 ...     | just next = acknowledge-valid next eq (setup-valid w err s delivered v)
 shutdown-valid blocked err s eq v | Close.initial = case eq of λ ()
 shutdown-valid blocked err s eq v | Close.reading = case eq of λ ()
 shutdown-valid blocked err s eq v | (Close.sendReady e′ w′) = case eq of λ ()
 shutdown-valid blocked err s eq v | Close.awaitResults = case eq of λ ()
 shutdown-valid blocked err s eq v | Close.closed = case eq of λ ()
 timewait-valid : ∀ err s {t} → H.deliverTimeWait err s ≡ just t → Valid s → Valid t
 timewait-valid err s eq v with Close.phase (H.shutdown s)
 ... | Close.awaitDelivery e′ w with lookup w (H.threads s) in found | lookup w (S.cleanups (M.world (H.source s)))
 ...   | just th | just (S.cleanupWaiting captured) with H.phase th in ph
 timewait-valid err s eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupWaiting captured) | H.maskedSetup = case eq of λ ()
 timewait-valid err s eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupWaiting captured) | H.handshaking = case eq of λ ()
 timewait-valid err s eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupWaiting captured) | (H.caughtCancellation x) = case eq of λ ()
 timewait-valid err s eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupWaiting captured) | (H.cancellationPublished x) = case eq of λ ()
 timewait-valid err s eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupWaiting captured) | (H.bodyExited x) = case eq of λ ()
 timewait-valid err s eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupWaiting captured) | (H.finalizing x) with H.dispatch (M.cleanupStep w (Cleanup.interruptTimeWait err)) s in advanced
 ...       | nothing = case eq of λ ()
 ...       | just next = acknowledge-valid next eq (cleanup-valid w (Cleanup.interruptTimeWait err) th x s found ph advanced v)
 timewait-valid err s eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupWaiting captured) | (H.cleanupComplete x o) = case eq of λ ()
 timewait-valid err s eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupWaiting captured) | (H.resultAvailable x o) = case eq of λ ()
 timewait-valid err s eq v | Close.awaitDelivery e′ w | just th | just S.cleanupAcquire = case eq of λ ()
 timewait-valid err s eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupSelect l) = case eq of λ ()
 timewait-valid err s eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupClose l m tl) = case eq of λ ()
 timewait-valid err s eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupPublish l m tl) = case eq of λ ()
 timewait-valid err s eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupRestore l y) = case eq of λ ()
 timewait-valid err s eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupFinalize h oc) = case eq of λ ()
 timewait-valid err s eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupCount oc) = case eq of λ ()
 timewait-valid err s eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupDone oc) = case eq of λ ()
 timewait-valid err s eq v | Close.awaitDelivery e′ w | nothing | cleanup = case eq of λ ()
 timewait-valid err s eq v | Close.awaitDelivery e′ w | just th | nothing = case eq of λ ()
 timewait-valid err s eq v | Close.initial = case eq of λ ()
 timewait-valid err s eq v | Close.reading = case eq of λ ()
 timewait-valid err s eq v | (Close.sendReady e′ w′) = case eq of λ ()
 timewait-valid err s eq v | Close.awaitResults = case eq of λ ()
 timewait-valid err s eq v | Close.closed = case eq of λ ()
 step-valid : ∀ action s {t} → H.step action s ≡ just t → Valid s → Valid t
 step-valid (H.run (M.admissionStep w Server.fork)) s eq v = fork-valid w s eq v
 step-valid (H.run (M.admissionStep w Server.take)) s eq v = dispatch-valid (M.admissionStep w Server.take) s eq tt v
 step-valid (H.run (M.admissionStep w Server.countLimit)) s eq v = dispatch-valid (M.admissionStep w Server.countLimit) s eq tt v
 step-valid (H.run (M.admissionStep w Server.allocatePromise)) s eq v = dispatch-valid (M.admissionStep w Server.allocatePromise) s eq tt v
 step-valid (H.run (M.admissionStep w Server.chooseEntry)) s eq v = dispatch-valid (M.admissionStep w Server.chooseEntry) s eq tt v
 step-valid (H.run (M.admissionStep w Server.putMapBack)) s eq v = dispatch-valid (M.admissionStep w Server.putMapBack) s eq tt v
 step-valid (H.run (M.admissionStep w Server.readCounters)) s eq v = dispatch-valid (M.admissionStep w Server.readCounters) s eq tt v
 step-valid (H.run (M.admissionStep w Server.restore)) s eq v = dispatch-valid (M.admissionStep w Server.restore) s eq tt v
 step-valid (H.run (M.admissionStep w Server.close)) s eq v = dispatch-valid (M.admissionStep w Server.close) s eq tt v
 step-valid (H.run (M.admissionStep w Server.failFork)) s eq v = dispatch-valid (M.admissionStep w Server.failFork) s eq tt v
 step-valid (H.run (M.handshakeStep w a)) s eq v = dispatch-valid (M.handshakeStep w a) s eq tt v
 step-valid (H.run (M.handlerPublication w result outcome)) s eq v = case eq of λ ()
 step-valid (H.run (M.handlerExit w)) s eq v = case eq of λ ()
 step-valid (H.run (M.handlerStep w a)) s eq v = case eq of λ ()
 step-valid (H.run (M.cleanupStep w a)) s eq v = case eq of λ ()
 step-valid (H.run (M.igStep a)) s eq v = dispatch-valid (M.igStep a) s eq tt v
 step-valid (H.run (M.remoteStep a)) s eq v with H.rawAllowed (M.remoteStep a)
 ... | false = case eq of λ ()
 ... | true = dispatch-valid (M.remoteStep a) s eq tt v
 step-valid (H.run (M.releaseStep a)) s eq v with H.rawAllowed (M.releaseStep a)
 ... | false = case eq of λ ()
 ... | true = dispatch-valid (M.releaseStep a) s eq tt v
 step-valid (H.enterHandshake w) s eq v with lookup w (H.threads s) in found
 ... | nothing = case eq of λ ()
 ... | just th with H.phase th in ph
 step-valid (H.enterHandshake w) s eq v | just th | H.maskedSetup = case just-injective eq of λ { refl → update w (H.handlerThread (H.captured th) H.handshaking) refl refl (in-phase v found ph) v }
 step-valid (H.enterHandshake w) s eq v | just th | H.handshaking = case eq of λ ()
 step-valid (H.enterHandshake w) s eq v | just th | (H.caughtCancellation x) = case eq of λ ()
 step-valid (H.enterHandshake w) s eq v | just th | (H.cancellationPublished x) = case eq of λ ()
 step-valid (H.enterHandshake w) s eq v | just th | (H.bodyExited x) = case eq of λ ()
 step-valid (H.enterHandshake w) s eq v | just th | (H.finalizing x) = case eq of λ ()
 step-valid (H.enterHandshake w) s eq v | just th | (H.cleanupComplete x o) = case eq of λ ()
 step-valid (H.enterHandshake w) s eq v | just th | (H.resultAvailable x o) = case eq of λ ()
 step-valid (H.deliverHandshakeCancellation w err) s eq v = handshake-valid w err s eq v
 step-valid (H.deliverBlockedSetupCancellation w err) s eq v = setup-valid w err s eq v
 step-valid (H.publishCaught w) s eq v with lookup w (H.threads s) in found
 ... | nothing = case eq of λ ()
 ... | just th with H.phase th in ph
 step-valid (H.publishCaught w) s eq v | just th | H.maskedSetup = case eq of λ ()
 step-valid (H.publishCaught w) s eq v | just th | H.handshaking = case eq of λ ()
 step-valid (H.publishCaught w) s eq v | just th | (H.caughtCancellation x) = dispatch-relabel (M.handlerPublication w (S.handlerError S.protocolViolation x) M.resultWritten) w th (H.cancellationPublished x) s eq tt (in-phase v found ph) v
 step-valid (H.publishCaught w) s eq v | just th | (H.cancellationPublished x) = case eq of λ ()
 step-valid (H.publishCaught w) s eq v | just th | (H.bodyExited x) = case eq of λ ()
 step-valid (H.publishCaught w) s eq v | just th | (H.finalizing x) = case eq of λ ()
 step-valid (H.publishCaught w) s eq v | just th | (H.cleanupComplete x o) = case eq of λ ()
 step-valid (H.publishCaught w) s eq v | just th | (H.resultAvailable x o) = case eq of λ ()
 step-valid (H.rethrowCaught w) s eq v with lookup w (H.threads s) in found
 ... | nothing = case eq of λ ()
 ... | just th with H.phase th in ph
 step-valid (H.rethrowCaught w) s eq v | just th | H.maskedSetup = case eq of λ ()
 step-valid (H.rethrowCaught w) s eq v | just th | H.handshaking = case eq of λ ()
 step-valid (H.rethrowCaught w) s eq v | just th | (H.caughtCancellation x) = case eq of λ ()
 step-valid (H.rethrowCaught w) s eq v | just th | (H.cancellationPublished x) = case just-injective eq of λ { refl → update w (H.handlerThread (H.captured th) (H.bodyExited x)) refl refl (in-phase v found ph) v }
 step-valid (H.rethrowCaught w) s eq v | just th | (H.bodyExited x) = case eq of λ ()
 step-valid (H.rethrowCaught w) s eq v | just th | (H.finalizing x) = case eq of λ ()
 step-valid (H.rethrowCaught w) s eq v | just th | (H.cleanupComplete x o) = case eq of λ ()
 step-valid (H.rethrowCaught w) s eq v | just th | (H.resultAvailable x o) = case eq of λ ()
 step-valid (H.enterFinalizer w) s eq v with lookup w (H.threads s) in found
 ... | nothing = case eq of λ ()
 ... | just th with H.phase th in ph
 step-valid (H.enterFinalizer w) s eq v | just th | H.maskedSetup = case eq of λ ()
 step-valid (H.enterFinalizer w) s eq v | just th | H.handshaking = case eq of λ ()
 step-valid (H.enterFinalizer w) s eq v | just th | (H.caughtCancellation x) = case eq of λ ()
 step-valid (H.enterFinalizer w) s eq v | just th | (H.cancellationPublished x) = case eq of λ ()
 step-valid (H.enterFinalizer w) s eq v | just th | (H.bodyExited x) = dispatch-exit w th x s eq v
 step-valid (H.enterFinalizer w) s eq v | just th | (H.finalizing x) = case eq of λ ()
 step-valid (H.enterFinalizer w) s eq v | just th | (H.cleanupComplete x o) = case eq of λ ()
 step-valid (H.enterFinalizer w) s eq v | just th | (H.resultAvailable x o) = case eq of λ ()
 step-valid (H.cleanup w action) s eq v with lookup w (H.threads s) in found
 ... | nothing = case eq of λ ()
 ... | just th with H.phase th in ph
 step-valid (H.cleanup w action) s eq v | just th | H.maskedSetup = case eq of λ ()
 step-valid (H.cleanup w action) s eq v | just th | H.handshaking = case eq of λ ()
 step-valid (H.cleanup w action) s eq v | just th | (H.caughtCancellation x) = case eq of λ ()
 step-valid (H.cleanup w action) s eq v | just th | (H.cancellationPublished x) = case eq of λ ()
 step-valid (H.cleanup w action) s eq v | just th | (H.bodyExited x) = case eq of λ ()
 step-valid (H.cleanup w action) s eq v | just th | (H.finalizing x) = cleanup-valid w action th x s found ph eq v
 step-valid (H.cleanup w action) s eq v | just th | (H.cleanupComplete x o) = case eq of λ ()
 step-valid (H.cleanup w action) s eq v | just th | (H.resultAvailable x o) = case eq of λ ()
 step-valid (H.finishCleanup w) s eq v with lookup w (H.threads s) | lookup w (S.cleanups (M.world (H.source s))) in cl
 ... | just th | just (S.cleanupDone done) with H.phase th
 step-valid (H.finishCleanup w) s eq v | just th | just (S.cleanupDone done) | H.maskedSetup = case eq of λ ()
 step-valid (H.finishCleanup w) s eq v | just th | just (S.cleanupDone done) | H.handshaking = case eq of λ ()
 step-valid (H.finishCleanup w) s eq v | just th | just (S.cleanupDone done) | (H.caughtCancellation x) = case eq of λ ()
 step-valid (H.finishCleanup w) s eq v | just th | just (S.cleanupDone done) | (H.cancellationPublished x) = case eq of λ ()
 step-valid (H.finishCleanup w) s eq v | just th | just (S.cleanupDone done) | (H.bodyExited x) = case eq of λ ()
 step-valid (H.finishCleanup w) s eq v | just th | just (S.cleanupDone done) | (H.finalizing x) = case just-injective eq of λ { refl → update w (H.handlerThread (H.captured th) (H.cleanupComplete x done)) refl refl cl v }
 step-valid (H.finishCleanup w) s eq v | just th | just (S.cleanupDone done) | (H.cleanupComplete x o) = case eq of λ ()
 step-valid (H.finishCleanup w) s eq v | just th | just (S.cleanupDone done) | (H.resultAvailable x o) = case eq of λ ()
 step-valid (H.finishCleanup w) s eq v | nothing | cleanup = case eq of λ ()
 step-valid (H.finishCleanup w) s eq v | just th | nothing = case eq of λ ()
 step-valid (H.finishCleanup w) s eq v | just th | just S.cleanupAcquire = case eq of λ ()
 step-valid (H.finishCleanup w) s eq v | just th | just (S.cleanupSelect l) = case eq of λ ()
 step-valid (H.finishCleanup w) s eq v | just th | just (S.cleanupClose l m tl) = case eq of λ ()
 step-valid (H.finishCleanup w) s eq v | just th | just (S.cleanupPublish l m tl) = case eq of λ ()
 step-valid (H.finishCleanup w) s eq v | just th | just (S.cleanupRestore l y) = case eq of λ ()
 step-valid (H.finishCleanup w) s eq v | just th | just (S.cleanupWaiting h) = case eq of λ ()
 step-valid (H.finishCleanup w) s eq v | just th | just (S.cleanupFinalize h oc) = case eq of λ ()
 step-valid (H.finishCleanup w) s eq v | just th | just (S.cleanupCount oc) = case eq of λ ()
 step-valid (H.publishAsyncResult w) s eq v with lookup w (H.threads s) | lookup w (S.cleanups (M.world (H.source s))) in cl
 ... | just th | just (S.cleanupDone done) with H.phase th
 step-valid (H.publishAsyncResult w) s eq v | just th | just (S.cleanupDone done) | H.maskedSetup = case eq of λ ()
 step-valid (H.publishAsyncResult w) s eq v | just th | just (S.cleanupDone done) | H.handshaking = case eq of λ ()
 step-valid (H.publishAsyncResult w) s eq v | just th | just (S.cleanupDone done) | (H.caughtCancellation x) = case eq of λ ()
 step-valid (H.publishAsyncResult w) s eq v | just th | just (S.cleanupDone done) | (H.cancellationPublished x) = case eq of λ ()
 step-valid (H.publishAsyncResult w) s eq v | just th | just (S.cleanupDone done) | (H.bodyExited x) = case eq of λ ()
 step-valid (H.publishAsyncResult w) s eq v | just th | just (S.cleanupDone done) | (H.finalizing x) = case eq of λ ()
 step-valid (H.publishAsyncResult w) s eq v | just th | just (S.cleanupDone done) | (H.cleanupComplete x o) = case just-injective eq of λ { refl → update w (H.handlerThread (H.captured th) (H.resultAvailable x done)) refl refl cl v }
 step-valid (H.publishAsyncResult w) s eq v | just th | just (S.cleanupDone done) | (H.resultAvailable x o) = case eq of λ ()
 step-valid (H.publishAsyncResult w) s eq v | nothing | cleanup = case eq of λ ()
 step-valid (H.publishAsyncResult w) s eq v | just th | nothing = case eq of λ ()
 step-valid (H.publishAsyncResult w) s eq v | just th | just S.cleanupAcquire = case eq of λ ()
 step-valid (H.publishAsyncResult w) s eq v | just th | just (S.cleanupSelect l) = case eq of λ ()
 step-valid (H.publishAsyncResult w) s eq v | just th | just (S.cleanupClose l m tl) = case eq of λ ()
 step-valid (H.publishAsyncResult w) s eq v | just th | just (S.cleanupPublish l m tl) = case eq of λ ()
 step-valid (H.publishAsyncResult w) s eq v | just th | just (S.cleanupRestore l y) = case eq of λ ()
 step-valid (H.publishAsyncResult w) s eq v | just th | just (S.cleanupWaiting h) = case eq of λ ()
 step-valid (H.publishAsyncResult w) s eq v | just th | just (S.cleanupFinalize h oc) = case eq of λ ()
 step-valid (H.publishAsyncResult w) s eq v | just th | just (S.cleanupCount oc) = case eq of λ ()
 step-valid (H.shutdownStep Close.captureSnapshot) s eq v with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.captureSnapshot (H.shutdown s)
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → transport refl refl v }
 step-valid (H.shutdownStep Close.readEntry) s eq v with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.readEntry (H.shutdown s)
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → transport refl refl v }
 step-valid (H.shutdownStep Close.requestCancellation) s eq v with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.requestCancellation (H.shutdown s)
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → transport refl refl v }
 step-valid (H.shutdownStep Close.finishTraversal) s eq v with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.finishTraversal (H.shutdown s)
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → transport refl refl v }
 step-valid (H.shutdownStep Close.finishClose) s eq v with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.finishClose (H.shutdown s)
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → transport refl refl v }
 step-valid (H.shutdownStep Close.acknowledgeDelivery) s () v
 step-valid (H.deliverShutdownHandshake err) s eq v = shutdown-valid false err s eq v
 step-valid (H.deliverShutdownBlockedSetup err) s eq v = shutdown-valid true err s eq v
 step-valid (H.deliverShutdownTimeWait err) s eq v = timewait-valid err s eq v
 step-valid H.acknowledgeFinished s eq v with Close.phase (H.shutdown s)
 ... | Close.awaitDelivery e′ w with H.resultReady w s
 ...   | true = acknowledge-valid s eq v
 ...   | false = case eq of λ ()
 step-valid H.acknowledgeFinished s eq v | Close.initial = case eq of λ ()
 step-valid H.acknowledgeFinished s eq v | Close.reading = case eq of λ ()
 step-valid H.acknowledgeFinished s eq v | (Close.sendReady e′ w′) = case eq of λ ()
 step-valid H.acknowledgeFinished s eq v | Close.awaitResults = case eq of λ ()
 step-valid H.acknowledgeFinished s eq v | Close.closed = case eq of λ ()
 exec-valid : ∀ {s as t} → H.Executes s as t → Valid s → Valid t
 exec-valid H.done v = v
 exec-valid {s} (H.next {a = a} eq rest) v = exec-valid rest (step-valid a s eq v)
 initialized-valid : ∀ c {s} → H.initial c ≡ just s → Valid s
 initialized-valid c eq with S.handlers (M.world c) | S.cleanups (M.world c) in empty | M.handlerLifecycles c | M.publicationFaults c
 ... | [] | [] | [] | [] = case just-injective eq of λ { refl → valid (λ w → cong (lookup w) empty) }
 ... | _ ∷ _ | _ | _ | _ = case eq of λ ()
 ... | [] | _ ∷ _ | _ | _ = case eq of λ ()
 ... | [] | [] | _ ∷ _ | _ = case eq of λ ()
 ... | [] | [] | [] | _ ∷ _ = case eq of λ ()
 -- Every initialized handler-supervision run keeps phases and cleanup records in agreement.
 from-initial : ∀ c {start as s} → H.initial c ≡ just start → H.Executes start as s → Valid s
 from-initial c actual path = exec-valid path (initialized-valid c actual)

-- The outbound physical layer forwards handler actions to Raw; its own forks
-- add untracked children and its other operations are quiet.
module Physical where
 Valid : B.State → Set
 Valid s = Raw.Valid (B.view s)
 allowed-quiet : ∀ a s → B.outboundAllowed a s ≡ true → QuietOutbound a
 allowed-quiet (O.inbound a) s ()
 allowed-quiet (O.beginAcquire w req) s allowed = tt
 allowed-quiet (O.acquire w a) s allowed = tt
 allowed-quiet (O.beginRelease w key) s allowed = tt
 allowed-quiet (O.release w a) s allowed = tt
 fresh-thread : ∀ child s → B.freshChild child s ≡ true → lookup child (B.threads s) ≡ nothing
 fresh-thread child s eq with lookup child (B.threads s) | lookup child (S.handlers (M.world (O.core (B.source s)))) |
   lookup child (S.admissions (M.world (O.core (B.source s)))) | lookup child (O.acquiring (B.source s)) | lookup child (O.releasing (B.source s))
 ... | nothing | nothing | nothing | nothing | nothing = refl
 ... | just _ | _ | _ | _ | _ = case eq of λ ()
 ... | nothing | just _ | _ | _ | _ = case eq of λ ()
 ... | nothing | nothing | just _ | _ | _ = case eq of λ ()
 ... | nothing | nothing | nothing | just _ | _ = case eq of λ ()
 ... | nothing | nothing | nothing | nothing | just _ = case eq of λ ()
 fork-valid : ∀ w s {t} → B.forkOutbound w s ≡ just t → Valid s → Valid t
 fork-valid w s eq v with lookup w (O.acquiring (B.source s))
 ... | nothing = case eq of λ ()
 ... | just f with B.freshChild (A.child (A.req f)) s in fresh
 ...   | false = case eq of λ ()
 ...   | true with O.advance (O.acquire w A.forkOK) (B.source s) in actual
 ...     | nothing = case eq of λ ()
 ...     | just c with lookup (A.child (A.req f)) (S.handlers (M.world (O.core c)))
 ...       | nothing = case eq of λ ()
 ...       | just captured = case just-injective eq of λ { refl →
   Raw.update (A.child (A.req f)) (H.handlerThread captured H.maskedSetup) refl
     (outbound-same (O.acquire w A.forkOK) (B.source s) actual tt)
     (Raw.absent v (fresh-thread (A.child (A.req f)) s fresh)) v }
 step-valid : ∀ a s {t} → B.step a s ≡ just t → Valid s → Valid t
 step-valid (B.handler a) s eq v with B.handlerAllowed a s
 ... | false = case eq of λ ()
 ... | true with H.step a (B.view s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just h = case just-injective eq of λ { refl → Raw.step-valid a (B.view s) actual v }
 step-valid (B.outbound a) s eq v with B.forkCaller a
 ... | just w = fork-valid w s eq v
 ... | nothing with B.outboundAllowed a s in allowed
 ...   | false = case eq of λ ()
 ...   | true with O.advance a (B.source s) in actual
 ...     | nothing = case eq of λ ()
 ...     | just c = case just-injective eq of λ { refl → Raw.transport refl (outbound-same a (B.source s) actual (allowed-quiet a s allowed)) v }
 exec-valid : ∀ {s as t} → B.Executes s as t → Valid s → Valid t
 exec-valid B.done v = v
 exec-valid {s} (B.next {a = a} eq rest) v = exec-valid rest (step-valid a s eq v)
 initialized-valid : ∀ c {s} → B.initial c ≡ just s → Valid s
 initialized-valid c eq with H.initial (O.core c) in actual
 ... | nothing = case eq of λ ()
 ... | just h = case just-injective eq of λ { refl → Raw.initialized-valid (O.core c) actual }
 -- Every initialized outbound-physical run keeps phases and cleanup records in agreement.
 from-initial : ∀ c {start as s} → B.initial c ≡ just start → B.Executes start as s → Valid s
 from-initial c actual path = exec-valid path (initialized-valid c actual)

-- Relative validity for the mux layers. Excluded workers (Z q ≡ true: those
-- owned by a mux frame) keep a thread, and steps whose per-worker target is
-- not excluded leave every excluded worker's thread and cleanup record intact.
-- Agreement is required only for workers that are not excluded.
module Relative (Z : WorkerId → Bool) where
 open Raw using (cleanupsOf)
 record On (s : H.State) : Set where
  constructor on
  field free : ∀ q → Z q ≡ false → Agrees (lookup q (H.threads s)) (lookup q (cleanupsOf s))
        kept : ∀ q → Z q ≡ true → Σ H.Thread (λ t → lookup q (H.threads s) ≡ just t)
 open On public
 Frozen : H.State → H.State → Set
 Frozen s t = ∀ q → Z q ≡ true →
   lookup q (H.threads t) ≡ lookup q (H.threads s) × lookup q (cleanupsOf t) ≡ lookup q (cleanupsOf s)
 Moves : H.State → H.State → Set
 Moves s t = On t × Frozen s t

 -- Per-worker operations and shutdown deliveries target a worker that is not excluded.
 TargetFree : H.State → Set
 TargetFree s = ∀ e w → Close.phase (H.shutdown s) ≡ Close.awaitDelivery e w → Z w ≡ false
 Guard : H.Action → H.State → Set
 Guard (H.run _) s = ⊤
 Guard (H.enterHandshake w) s = Z w ≡ false
 Guard (H.deliverHandshakeCancellation w _) s = Z w ≡ false
 Guard (H.deliverBlockedSetupCancellation w _) s = Z w ≡ false
 Guard (H.publishCaught w) s = Z w ≡ false
 Guard (H.rethrowCaught w) s = Z w ≡ false
 Guard (H.enterFinalizer w) s = Z w ≡ false
 Guard (H.cleanup w _) s = Z w ≡ false
 Guard (H.finishCleanup w) s = Z w ≡ false
 Guard (H.publishAsyncResult w) s = Z w ≡ false
 Guard (H.shutdownStep _) s = ⊤
 Guard (H.deliverShutdownHandshake _) s = TargetFree s
 Guard (H.deliverShutdownBlockedSetup _) s = TargetFree s
 Guard (H.deliverShutdownTimeWait _) s = TargetFree s
 Guard H.acknowledgeFinished s = ⊤

 apart : ∀ {q w} → Z q ≡ true → Z w ≡ false → q ≢ w
 apart zq zw refl = case trans (sym zq) zw of λ ()
 at : ∀ {s w t} → On s → Z w ≡ false → lookup w (H.threads s) ≡ just t → Expected (H.phase t) (lookup w (cleanupsOf s))
 at {s} {w} v zw found = subst (λ x → Agrees x (lookup w (cleanupsOf s))) found (free v w zw)
 in-phase : ∀ {s w t p} → On s → Z w ≡ false → lookup w (H.threads s) ≡ just t → H.phase t ≡ p → Expected p (lookup w (cleanupsOf s))
 in-phase {s} {w} v zw found ph = subst (λ p → Expected p (lookup w (cleanupsOf s))) ph (at v zw found)
 absent : ∀ {s w} → On s → Z w ≡ false → lookup w (H.threads s) ≡ nothing → lookup w (cleanupsOf s) ≡ nothing
 absent {s} {w} v zw missing = subst (λ x → Agrees x (lookup w (cleanupsOf s))) missing (free v w zw)
 -- A worker without a thread is not excluded.
 fresh-free : ∀ {s w} → On s → lookup w (H.threads s) ≡ nothing → Z w ≡ false
 fresh-free {s} {w} v missing with Z w in zw
 ... | false = refl
 ... | true with kept v w zw
 ...   | t , found = case trans (sym missing) found of λ ()

 transport : ∀ {s t} → H.threads t ≡ H.threads s → cleanupsOf t ≡ cleanupsOf s → On s → Moves s t
 transport {s} {t} th cl v = on free′ kept′ , λ q zq → cong (lookup q) th , cong (lookup q) cl
  where
  free′ : ∀ q → Z q ≡ false → Agrees (lookup q (H.threads t)) (lookup q (cleanupsOf t))
  free′ q zq rewrite th | cl = free v q zq
  kept′ : ∀ q → Z q ≡ true → Σ H.Thread (λ x → lookup q (H.threads t) ≡ just x)
  kept′ q zq rewrite th = kept v q zq
 update : ∀ {s t} w th → Z w ≡ false → H.threads t ≡ put w th (H.threads s) → cleanupsOf t ≡ cleanupsOf s →
   Expected (H.phase th) (lookup w (cleanupsOf s)) → On s → Moves s t
 update {s} {t} w th zw threads cl ok v = on free′ kept′ , frozen′
  where
  free′ : ∀ q → Z q ≡ false → Agrees (lookup q (H.threads t)) (lookup q (cleanupsOf t))
  free′ q zq rewrite threads | cl with q ≟ w
  ... | yes refl rewrite lookup-put w th (H.threads s) = ok
  ... | no other rewrite lookup-put-other w q th (H.threads s) other = free v q zq
  kept′ : ∀ q → Z q ≡ true → Σ H.Thread (λ x → lookup q (H.threads t) ≡ just x)
  kept′ q zq rewrite threads | lookup-put-other w q th (H.threads s) (apart zq zw) = kept v q zq
  frozen′ : Frozen s t
  frozen′ q zq rewrite threads | cl | lookup-put-other w q th (H.threads s) (apart zq zw) = refl , refl
 write : ∀ {s t} w th c → Z w ≡ false → lookup w (H.threads s) ≡ just th → H.threads t ≡ H.threads s →
   cleanupsOf t ≡ put w c (cleanupsOf s) → Expected (H.phase th) (just c) → On s → Moves s t
 write {s} {t} w th c zw found threads cl ok v = on free′ kept′ , frozen′
  where
  free′ : ∀ q → Z q ≡ false → Agrees (lookup q (H.threads t)) (lookup q (cleanupsOf t))
  free′ q zq rewrite threads | cl with q ≟ w
  ... | yes refl rewrite lookup-put w c (cleanupsOf s) | found = ok
  ... | no other rewrite lookup-put-other w q c (cleanupsOf s) other = free v q zq
  kept′ : ∀ q → Z q ≡ true → Σ H.Thread (λ x → lookup q (H.threads t) ≡ just x)
  kept′ q zq rewrite threads = kept v q zq
  frozen′ : Frozen s t
  frozen′ q zq rewrite threads | cl | lookup-put-other w q c (cleanupsOf s) (apart zq zw) = refl , refl
 both : ∀ {s t} w th c → Z w ≡ false → H.threads t ≡ put w th (H.threads s) →
   cleanupsOf t ≡ put w c (cleanupsOf s) → Expected (H.phase th) (just c) → On s → Moves s t
 both {s} {t} w th c zw threads cl ok v = on free′ kept′ , frozen′
  where
  free′ : ∀ q → Z q ≡ false → Agrees (lookup q (H.threads t)) (lookup q (cleanupsOf t))
  free′ q zq rewrite threads | cl with q ≟ w
  ... | yes refl rewrite lookup-put w th (H.threads s) | lookup-put w c (cleanupsOf s) = ok
  ... | no other rewrite lookup-put-other w q th (H.threads s) other | lookup-put-other w q c (cleanupsOf s) other = free v q zq
  kept′ : ∀ q → Z q ≡ true → Σ H.Thread (λ x → lookup q (H.threads t) ≡ just x)
  kept′ q zq rewrite threads | lookup-put-other w q th (H.threads s) (apart zq zw) = kept v q zq
  frozen′ : Frozen s t
  frozen′ q zq rewrite threads | cl | lookup-put-other w q th (H.threads s) (apart zq zw) | lookup-put-other w q c (cleanupsOf s) (apart zq zw) = refl , refl
 -- Writing an excluded worker's cleanup record leaves relative validity intact.
 excluded-write : ∀ {s t} w c → Z w ≡ true → H.threads t ≡ H.threads s →
   cleanupsOf t ≡ put w c (cleanupsOf s) → On s → On t
 excluded-write {s} {t} w c zw threads cl v = on free′ kept′
  where
  free′ : ∀ q → Z q ≡ false → Agrees (lookup q (H.threads t)) (lookup q (cleanupsOf t))
  free′ q zq rewrite threads | cl | lookup-put-other w q c (cleanupsOf s) (λ e → apart zw zq (sym e)) = free v q zq
  kept′ : ∀ q → Z q ≡ true → Σ H.Thread (λ x → lookup q (H.threads t) ≡ just x)
  kept′ q zq rewrite threads = kept v q zq
 -- Composition: a later step that keeps validity extends the frozen relation.
 chain : ∀ s m {t} → Moves s m → (On m → Moves m t) → Moves s t
 chain s m (vm , fm) next with next vm
 ... | vt , ft = vt , λ q zq → trans (proj₁ (ft q zq)) (proj₁ (fm q zq)) , trans (proj₂ (ft q zq)) (proj₂ (fm q zq))

 dispatch-moves : ∀ a s {t} → H.dispatch a s ≡ just t → QuietMachine a → On s → Moves s t
 dispatch-moves a s eq q v = transport (proj₁ (Raw.dispatch-same a s eq q)) (proj₂ (Raw.dispatch-same a s eq q)) v
 dispatch-relabel : ∀ a w th p s {t} → Z w ≡ false → H.dispatchPhase a w th p s ≡ just t → QuietMachine a →
   Expected p (lookup w (cleanupsOf s)) → On s → Moves s t
 dispatch-relabel a w th p s zw eq q ok v with H.dispatch a s in actual
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl →
   update w (H.handlerThread (H.captured th) p) zw (cong (put w (H.handlerThread (H.captured th) p)) (proj₁ (Raw.dispatch-same a s actual q)))
     (proj₂ (Raw.dispatch-same a s actual q)) ok v }
 exit-after : ∀ w th x s {next} → Z w ≡ false → H.dispatch (M.handlerExit w) s ≡ just next → On s →
   Moves s (H.setPhase w th (H.finalizing x) next)
 exit-after w th x s zw eq v with M.advance (M.handlerExit w) (H.source s) in actual
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl →
   both w (H.handlerThread (H.captured th) (H.finalizing x)) S.cleanupAcquire zw refl
     (proj₂ (exit-effect w (H.source s) actual)) (S.cleanupAcquire , refl) v }
 dispatch-exit : ∀ w th x s {t} → Z w ≡ false → H.dispatchPhase (M.handlerExit w) w th (H.finalizing x) s ≡ just t → On s → Moves s t
 dispatch-exit w th x s zw eq v with H.dispatch (M.handlerExit w) s in actual
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → exit-after w th x s zw actual v }
 cleanup-moves : ∀ w action th x s {t} → Z w ≡ false → lookup w (H.threads s) ≡ just th → H.phase th ≡ H.finalizing x →
   H.dispatch (M.cleanupStep w action) s ≡ just t → On s → Moves s t
 cleanup-moves w action th x s zw found ph eq v with M.advance (M.cleanupStep w action) (H.source s) in actual
 ... | nothing = case eq of λ ()
 ... | just c with cleanup-effect w action (H.source s) actual
 ...   | stepped prior seen live (next , rw) = case just-injective eq of λ { refl →
   write w th next zw found refl rw (subst (λ p → Expected p (just next)) (sym ph) (next , refl)) v }
 acknowledge-moves : ∀ s {t} → H.acknowledge s ≡ just t → On s → Moves s t
 acknowledge-moves s eq v with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.acknowledgeDelivery (H.shutdown s)
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → transport refl refl v }
 fork-moves : ∀ w s {t} → H.forkAdmission w s ≡ just t → On s → Moves s t
 fork-moves w s eq v with lookup w (S.admissions (M.world (H.source s)))
 ... | nothing = case eq of λ ()
 ... | just a with lookup (S.child (S.request a)) (H.threads s) in missing
 ...   | just old = case eq of λ ()
 ...   | nothing with M.advance (M.admissionStep w Server.fork) (H.source s) in actual
 ...     | nothing = case eq of λ ()
 ...     | just c with lookup (S.child (S.request a)) (S.handlers (M.world c))
 ...       | nothing = case eq of λ ()
 ...       | just handler = case just-injective eq of λ { refl →
   update (S.child (S.request a)) (H.handlerThread handler H.maskedSetup) (fresh-free v missing) refl
     (machine-same (M.admissionStep w Server.fork) (H.source s) actual tt) (absent v (fresh-free v missing) missing) v }
 handshake-moves : ∀ w err s {t} → Z w ≡ false → H.deliverHandshake w err s ≡ just t → On s → Moves s t
 handshake-moves w err s zw eq v with lookup w (H.threads s) in found
 ... | nothing = case eq of λ ()
 ... | just th with H.phase th in ph
 handshake-moves w err s zw eq v | just th | H.maskedSetup = case eq of λ ()
 handshake-moves w err s zw eq v | just th | H.handshaking = case just-injective eq of λ { refl → update w (H.handlerThread (H.captured th) (H.caughtCancellation err)) zw refl refl (in-phase v zw found ph) v }
 handshake-moves w err s zw eq v | just th | (H.caughtCancellation x) = case eq of λ ()
 handshake-moves w err s zw eq v | just th | (H.cancellationPublished x) = case eq of λ ()
 handshake-moves w err s zw eq v | just th | (H.bodyExited x) = case eq of λ ()
 handshake-moves w err s zw eq v | just th | (H.finalizing x) = case eq of λ ()
 handshake-moves w err s zw eq v | just th | (H.cleanupComplete x o) = case eq of λ ()
 handshake-moves w err s zw eq v | just th | (H.resultAvailable x o) = case eq of λ ()
 setup-moves : ∀ w err s {t} → Z w ≡ false → H.deliverBlockedSetup w err s ≡ just t → On s → Moves s t
 setup-moves w err s zw eq v with lookup w (H.threads s) in found
 ... | nothing = case eq of λ ()
 ... | just th with H.phase th in ph
 setup-moves w err s zw eq v | just th | H.maskedSetup = case just-injective eq of λ { refl → update w (H.handlerThread (H.captured th) (H.bodyExited err)) zw refl refl (in-phase v zw found ph) v }
 setup-moves w err s zw eq v | just th | H.handshaking = case eq of λ ()
 setup-moves w err s zw eq v | just th | (H.caughtCancellation x) = case eq of λ ()
 setup-moves w err s zw eq v | just th | (H.cancellationPublished x) = case eq of λ ()
 setup-moves w err s zw eq v | just th | (H.bodyExited x) = case eq of λ ()
 setup-moves w err s zw eq v | just th | (H.finalizing x) = case eq of λ ()
 setup-moves w err s zw eq v | just th | (H.cleanupComplete x o) = case eq of λ ()
 setup-moves w err s zw eq v | just th | (H.resultAvailable x o) = case eq of λ ()
 shutdown-moves : ∀ blocked err s {t} → TargetFree s → H.deliverShutdown blocked err s ≡ just t → On s → Moves s t
 shutdown-moves blocked err s g eq v with Close.phase (H.shutdown s) in cp
 ... | Close.awaitDelivery e′ w with blocked
 ...   | false with H.deliverHandshake w err s in delivered
 ...     | nothing = case eq of λ ()
 ...     | just next = chain s next (handshake-moves w err s (g e′ w refl) delivered v) (acknowledge-moves next eq)
 shutdown-moves blocked err s g eq v | Close.awaitDelivery e′ w | true with H.deliverBlockedSetup w err s in delivered
 ...     | nothing = case eq of λ ()
 ...     | just next = chain s next (setup-moves w err s (g e′ w refl) delivered v) (acknowledge-moves next eq)
 shutdown-moves blocked err s g eq v | Close.initial = case eq of λ ()
 shutdown-moves blocked err s g eq v | Close.reading = case eq of λ ()
 shutdown-moves blocked err s g eq v | (Close.sendReady e′ w′) = case eq of λ ()
 shutdown-moves blocked err s g eq v | Close.awaitResults = case eq of λ ()
 shutdown-moves blocked err s g eq v | Close.closed = case eq of λ ()
 timewait-moves : ∀ err s {t} → TargetFree s → H.deliverTimeWait err s ≡ just t → On s → Moves s t
 timewait-moves err s g eq v with Close.phase (H.shutdown s) in cp
 ... | Close.awaitDelivery e′ w with lookup w (H.threads s) in found | lookup w (S.cleanups (M.world (H.source s)))
 ...   | just th | just (S.cleanupWaiting captured) with H.phase th in ph
 timewait-moves err s g eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupWaiting captured) | H.maskedSetup = case eq of λ ()
 timewait-moves err s g eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupWaiting captured) | H.handshaking = case eq of λ ()
 timewait-moves err s g eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupWaiting captured) | (H.caughtCancellation x) = case eq of λ ()
 timewait-moves err s g eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupWaiting captured) | (H.cancellationPublished x) = case eq of λ ()
 timewait-moves err s g eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupWaiting captured) | (H.bodyExited x) = case eq of λ ()
 timewait-moves err s g eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupWaiting captured) | (H.finalizing x) with H.dispatch (M.cleanupStep w (Cleanup.interruptTimeWait err)) s in advanced
 ...       | nothing = case eq of λ ()
 ...       | just next = chain s next (cleanup-moves w (Cleanup.interruptTimeWait err) th x s (g e′ w refl) found ph advanced v) (acknowledge-moves next eq)
 timewait-moves err s g eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupWaiting captured) | (H.cleanupComplete x o) = case eq of λ ()
 timewait-moves err s g eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupWaiting captured) | (H.resultAvailable x o) = case eq of λ ()
 timewait-moves err s g eq v | Close.awaitDelivery e′ w | just th | just S.cleanupAcquire = case eq of λ ()
 timewait-moves err s g eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupSelect l) = case eq of λ ()
 timewait-moves err s g eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupClose l m tl) = case eq of λ ()
 timewait-moves err s g eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupPublish l m tl) = case eq of λ ()
 timewait-moves err s g eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupRestore l y) = case eq of λ ()
 timewait-moves err s g eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupFinalize h oc) = case eq of λ ()
 timewait-moves err s g eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupCount oc) = case eq of λ ()
 timewait-moves err s g eq v | Close.awaitDelivery e′ w | just th | just (S.cleanupDone oc) = case eq of λ ()
 timewait-moves err s g eq v | Close.awaitDelivery e′ w | nothing | cleanup = case eq of λ ()
 timewait-moves err s g eq v | Close.awaitDelivery e′ w | just th | nothing = case eq of λ ()
 timewait-moves err s g eq v | Close.initial = case eq of λ ()
 timewait-moves err s g eq v | Close.reading = case eq of λ ()
 timewait-moves err s g eq v | (Close.sendReady e′ w′) = case eq of λ ()
 timewait-moves err s g eq v | Close.awaitResults = case eq of λ ()
 timewait-moves err s g eq v | Close.closed = case eq of λ ()
 step-moves : ∀ action s {t} → Guard action s → H.step action s ≡ just t → On s → Moves s t
 step-moves (H.run (M.admissionStep w Server.fork)) s g eq v = fork-moves w s eq v
 step-moves (H.run (M.admissionStep w Server.take)) s g eq v = dispatch-moves (M.admissionStep w Server.take) s eq tt v
 step-moves (H.run (M.admissionStep w Server.countLimit)) s g eq v = dispatch-moves (M.admissionStep w Server.countLimit) s eq tt v
 step-moves (H.run (M.admissionStep w Server.allocatePromise)) s g eq v = dispatch-moves (M.admissionStep w Server.allocatePromise) s eq tt v
 step-moves (H.run (M.admissionStep w Server.chooseEntry)) s g eq v = dispatch-moves (M.admissionStep w Server.chooseEntry) s eq tt v
 step-moves (H.run (M.admissionStep w Server.putMapBack)) s g eq v = dispatch-moves (M.admissionStep w Server.putMapBack) s eq tt v
 step-moves (H.run (M.admissionStep w Server.readCounters)) s g eq v = dispatch-moves (M.admissionStep w Server.readCounters) s eq tt v
 step-moves (H.run (M.admissionStep w Server.restore)) s g eq v = dispatch-moves (M.admissionStep w Server.restore) s eq tt v
 step-moves (H.run (M.admissionStep w Server.close)) s g eq v = dispatch-moves (M.admissionStep w Server.close) s eq tt v
 step-moves (H.run (M.admissionStep w Server.failFork)) s g eq v = dispatch-moves (M.admissionStep w Server.failFork) s eq tt v
 step-moves (H.run (M.handshakeStep w a)) s g eq v = dispatch-moves (M.handshakeStep w a) s eq tt v
 step-moves (H.run (M.handlerPublication w result outcome)) s g eq v = case eq of λ ()
 step-moves (H.run (M.handlerExit w)) s g eq v = case eq of λ ()
 step-moves (H.run (M.handlerStep w a)) s g eq v = case eq of λ ()
 step-moves (H.run (M.cleanupStep w a)) s g eq v = case eq of λ ()
 step-moves (H.run (M.igStep a)) s g eq v = dispatch-moves (M.igStep a) s eq tt v
 step-moves (H.run (M.remoteStep a)) s g eq v with H.rawAllowed (M.remoteStep a)
 ... | false = case eq of λ ()
 ... | true = dispatch-moves (M.remoteStep a) s eq tt v
 step-moves (H.run (M.releaseStep a)) s g eq v with H.rawAllowed (M.releaseStep a)
 ... | false = case eq of λ ()
 ... | true = dispatch-moves (M.releaseStep a) s eq tt v
 step-moves (H.enterHandshake w) s zw eq v with lookup w (H.threads s) in found
 ... | nothing = case eq of λ ()
 ... | just th with H.phase th in ph
 step-moves (H.enterHandshake w) s zw eq v | just th | H.maskedSetup = case just-injective eq of λ { refl → update w (H.handlerThread (H.captured th) H.handshaking) zw refl refl (in-phase v zw found ph) v }
 step-moves (H.enterHandshake w) s zw eq v | just th | H.handshaking = case eq of λ ()
 step-moves (H.enterHandshake w) s zw eq v | just th | (H.caughtCancellation x) = case eq of λ ()
 step-moves (H.enterHandshake w) s zw eq v | just th | (H.cancellationPublished x) = case eq of λ ()
 step-moves (H.enterHandshake w) s zw eq v | just th | (H.bodyExited x) = case eq of λ ()
 step-moves (H.enterHandshake w) s zw eq v | just th | (H.finalizing x) = case eq of λ ()
 step-moves (H.enterHandshake w) s zw eq v | just th | (H.cleanupComplete x o) = case eq of λ ()
 step-moves (H.enterHandshake w) s zw eq v | just th | (H.resultAvailable x o) = case eq of λ ()
 step-moves (H.deliverHandshakeCancellation w err) s zw eq v = handshake-moves w err s zw eq v
 step-moves (H.deliverBlockedSetupCancellation w err) s zw eq v = setup-moves w err s zw eq v
 step-moves (H.publishCaught w) s zw eq v with lookup w (H.threads s) in found
 ... | nothing = case eq of λ ()
 ... | just th with H.phase th in ph
 step-moves (H.publishCaught w) s zw eq v | just th | H.maskedSetup = case eq of λ ()
 step-moves (H.publishCaught w) s zw eq v | just th | H.handshaking = case eq of λ ()
 step-moves (H.publishCaught w) s zw eq v | just th | (H.caughtCancellation x) = dispatch-relabel (M.handlerPublication w (S.handlerError S.protocolViolation x) M.resultWritten) w th (H.cancellationPublished x) s zw eq tt (in-phase v zw found ph) v
 step-moves (H.publishCaught w) s zw eq v | just th | (H.cancellationPublished x) = case eq of λ ()
 step-moves (H.publishCaught w) s zw eq v | just th | (H.bodyExited x) = case eq of λ ()
 step-moves (H.publishCaught w) s zw eq v | just th | (H.finalizing x) = case eq of λ ()
 step-moves (H.publishCaught w) s zw eq v | just th | (H.cleanupComplete x o) = case eq of λ ()
 step-moves (H.publishCaught w) s zw eq v | just th | (H.resultAvailable x o) = case eq of λ ()
 step-moves (H.rethrowCaught w) s zw eq v with lookup w (H.threads s) in found
 ... | nothing = case eq of λ ()
 ... | just th with H.phase th in ph
 step-moves (H.rethrowCaught w) s zw eq v | just th | H.maskedSetup = case eq of λ ()
 step-moves (H.rethrowCaught w) s zw eq v | just th | H.handshaking = case eq of λ ()
 step-moves (H.rethrowCaught w) s zw eq v | just th | (H.caughtCancellation x) = case eq of λ ()
 step-moves (H.rethrowCaught w) s zw eq v | just th | (H.cancellationPublished x) = case just-injective eq of λ { refl → update w (H.handlerThread (H.captured th) (H.bodyExited x)) zw refl refl (in-phase v zw found ph) v }
 step-moves (H.rethrowCaught w) s zw eq v | just th | (H.bodyExited x) = case eq of λ ()
 step-moves (H.rethrowCaught w) s zw eq v | just th | (H.finalizing x) = case eq of λ ()
 step-moves (H.rethrowCaught w) s zw eq v | just th | (H.cleanupComplete x o) = case eq of λ ()
 step-moves (H.rethrowCaught w) s zw eq v | just th | (H.resultAvailable x o) = case eq of λ ()
 step-moves (H.enterFinalizer w) s zw eq v with lookup w (H.threads s) in found
 ... | nothing = case eq of λ ()
 ... | just th with H.phase th in ph
 step-moves (H.enterFinalizer w) s zw eq v | just th | H.maskedSetup = case eq of λ ()
 step-moves (H.enterFinalizer w) s zw eq v | just th | H.handshaking = case eq of λ ()
 step-moves (H.enterFinalizer w) s zw eq v | just th | (H.caughtCancellation x) = case eq of λ ()
 step-moves (H.enterFinalizer w) s zw eq v | just th | (H.cancellationPublished x) = case eq of λ ()
 step-moves (H.enterFinalizer w) s zw eq v | just th | (H.bodyExited x) = dispatch-exit w th x s zw eq v
 step-moves (H.enterFinalizer w) s zw eq v | just th | (H.finalizing x) = case eq of λ ()
 step-moves (H.enterFinalizer w) s zw eq v | just th | (H.cleanupComplete x o) = case eq of λ ()
 step-moves (H.enterFinalizer w) s zw eq v | just th | (H.resultAvailable x o) = case eq of λ ()
 step-moves (H.cleanup w action) s zw eq v with lookup w (H.threads s) in found
 ... | nothing = case eq of λ ()
 ... | just th with H.phase th in ph
 step-moves (H.cleanup w action) s zw eq v | just th | H.maskedSetup = case eq of λ ()
 step-moves (H.cleanup w action) s zw eq v | just th | H.handshaking = case eq of λ ()
 step-moves (H.cleanup w action) s zw eq v | just th | (H.caughtCancellation x) = case eq of λ ()
 step-moves (H.cleanup w action) s zw eq v | just th | (H.cancellationPublished x) = case eq of λ ()
 step-moves (H.cleanup w action) s zw eq v | just th | (H.bodyExited x) = case eq of λ ()
 step-moves (H.cleanup w action) s zw eq v | just th | (H.finalizing x) = cleanup-moves w action th x s zw found ph eq v
 step-moves (H.cleanup w action) s zw eq v | just th | (H.cleanupComplete x o) = case eq of λ ()
 step-moves (H.cleanup w action) s zw eq v | just th | (H.resultAvailable x o) = case eq of λ ()
 step-moves (H.finishCleanup w) s zw eq v with lookup w (H.threads s) | lookup w (S.cleanups (M.world (H.source s))) in cl
 ... | just th | just (S.cleanupDone done) with H.phase th
 step-moves (H.finishCleanup w) s zw eq v | just th | just (S.cleanupDone done) | H.maskedSetup = case eq of λ ()
 step-moves (H.finishCleanup w) s zw eq v | just th | just (S.cleanupDone done) | H.handshaking = case eq of λ ()
 step-moves (H.finishCleanup w) s zw eq v | just th | just (S.cleanupDone done) | (H.caughtCancellation x) = case eq of λ ()
 step-moves (H.finishCleanup w) s zw eq v | just th | just (S.cleanupDone done) | (H.cancellationPublished x) = case eq of λ ()
 step-moves (H.finishCleanup w) s zw eq v | just th | just (S.cleanupDone done) | (H.bodyExited x) = case eq of λ ()
 step-moves (H.finishCleanup w) s zw eq v | just th | just (S.cleanupDone done) | (H.finalizing x) = case just-injective eq of λ { refl → update w (H.handlerThread (H.captured th) (H.cleanupComplete x done)) zw refl refl cl v }
 step-moves (H.finishCleanup w) s zw eq v | just th | just (S.cleanupDone done) | (H.cleanupComplete x o) = case eq of λ ()
 step-moves (H.finishCleanup w) s zw eq v | just th | just (S.cleanupDone done) | (H.resultAvailable x o) = case eq of λ ()
 step-moves (H.finishCleanup w) s zw eq v | nothing | cleanup = case eq of λ ()
 step-moves (H.finishCleanup w) s zw eq v | just th | nothing = case eq of λ ()
 step-moves (H.finishCleanup w) s zw eq v | just th | just S.cleanupAcquire = case eq of λ ()
 step-moves (H.finishCleanup w) s zw eq v | just th | just (S.cleanupSelect l) = case eq of λ ()
 step-moves (H.finishCleanup w) s zw eq v | just th | just (S.cleanupClose l m tl) = case eq of λ ()
 step-moves (H.finishCleanup w) s zw eq v | just th | just (S.cleanupPublish l m tl) = case eq of λ ()
 step-moves (H.finishCleanup w) s zw eq v | just th | just (S.cleanupRestore l y) = case eq of λ ()
 step-moves (H.finishCleanup w) s zw eq v | just th | just (S.cleanupWaiting h) = case eq of λ ()
 step-moves (H.finishCleanup w) s zw eq v | just th | just (S.cleanupFinalize h oc) = case eq of λ ()
 step-moves (H.finishCleanup w) s zw eq v | just th | just (S.cleanupCount oc) = case eq of λ ()
 step-moves (H.publishAsyncResult w) s zw eq v with lookup w (H.threads s) | lookup w (S.cleanups (M.world (H.source s))) in cl
 ... | just th | just (S.cleanupDone done) with H.phase th
 step-moves (H.publishAsyncResult w) s zw eq v | just th | just (S.cleanupDone done) | H.maskedSetup = case eq of λ ()
 step-moves (H.publishAsyncResult w) s zw eq v | just th | just (S.cleanupDone done) | H.handshaking = case eq of λ ()
 step-moves (H.publishAsyncResult w) s zw eq v | just th | just (S.cleanupDone done) | (H.caughtCancellation x) = case eq of λ ()
 step-moves (H.publishAsyncResult w) s zw eq v | just th | just (S.cleanupDone done) | (H.cancellationPublished x) = case eq of λ ()
 step-moves (H.publishAsyncResult w) s zw eq v | just th | just (S.cleanupDone done) | (H.bodyExited x) = case eq of λ ()
 step-moves (H.publishAsyncResult w) s zw eq v | just th | just (S.cleanupDone done) | (H.finalizing x) = case eq of λ ()
 step-moves (H.publishAsyncResult w) s zw eq v | just th | just (S.cleanupDone done) | (H.cleanupComplete x o) = case just-injective eq of λ { refl → update w (H.handlerThread (H.captured th) (H.resultAvailable x done)) zw refl refl cl v }
 step-moves (H.publishAsyncResult w) s zw eq v | just th | just (S.cleanupDone done) | (H.resultAvailable x o) = case eq of λ ()
 step-moves (H.publishAsyncResult w) s zw eq v | nothing | cleanup = case eq of λ ()
 step-moves (H.publishAsyncResult w) s zw eq v | just th | nothing = case eq of λ ()
 step-moves (H.publishAsyncResult w) s zw eq v | just th | just S.cleanupAcquire = case eq of λ ()
 step-moves (H.publishAsyncResult w) s zw eq v | just th | just (S.cleanupSelect l) = case eq of λ ()
 step-moves (H.publishAsyncResult w) s zw eq v | just th | just (S.cleanupClose l m tl) = case eq of λ ()
 step-moves (H.publishAsyncResult w) s zw eq v | just th | just (S.cleanupPublish l m tl) = case eq of λ ()
 step-moves (H.publishAsyncResult w) s zw eq v | just th | just (S.cleanupRestore l y) = case eq of λ ()
 step-moves (H.publishAsyncResult w) s zw eq v | just th | just (S.cleanupWaiting h) = case eq of λ ()
 step-moves (H.publishAsyncResult w) s zw eq v | just th | just (S.cleanupFinalize h oc) = case eq of λ ()
 step-moves (H.publishAsyncResult w) s zw eq v | just th | just (S.cleanupCount oc) = case eq of λ ()
 step-moves (H.shutdownStep Close.captureSnapshot) s g eq v with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.captureSnapshot (H.shutdown s)
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → transport refl refl v }
 step-moves (H.shutdownStep Close.readEntry) s g eq v with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.readEntry (H.shutdown s)
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → transport refl refl v }
 step-moves (H.shutdownStep Close.requestCancellation) s g eq v with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.requestCancellation (H.shutdown s)
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → transport refl refl v }
 step-moves (H.shutdownStep Close.finishTraversal) s g eq v with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.finishTraversal (H.shutdown s)
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → transport refl refl v }
 step-moves (H.shutdownStep Close.finishClose) s g eq v with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.finishClose (H.shutdown s)
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → transport refl refl v }
 step-moves (H.shutdownStep Close.acknowledgeDelivery) s g () v
 step-moves (H.deliverShutdownHandshake err) s g eq v = shutdown-moves false err s g eq v
 step-moves (H.deliverShutdownBlockedSetup err) s g eq v = shutdown-moves true err s g eq v
 step-moves (H.deliverShutdownTimeWait err) s g eq v = timewait-moves err s g eq v
 step-moves H.acknowledgeFinished s g eq v with Close.phase (H.shutdown s)
 ... | Close.awaitDelivery e′ w with H.resultReady w s
 ...   | true = acknowledge-moves s eq v
 ...   | false = case eq of λ ()
 step-moves H.acknowledgeFinished s g eq v | Close.initial = case eq of λ ()
 step-moves H.acknowledgeFinished s g eq v | Close.reading = case eq of λ ()
 step-moves H.acknowledgeFinished s g eq v | (Close.sendReady e′ w′) = case eq of λ ()
 step-moves H.acknowledgeFinished s g eq v | Close.awaitResults = case eq of λ ()
 step-moves H.acknowledgeFinished s g eq v | Close.closed = case eq of λ ()

 -- Outbound physical steps: handler steps keep their guard, forks add a child
 -- that is not excluded, and other outbound operations are quiet.
 module Outbound where
  Guarded : B.Action → B.State → Set
  Guarded (B.handler a) s = Guard a (B.view s)
  Guarded (B.outbound _) s = ⊤
  fork-moves′ : ∀ w s {t} → B.forkOutbound w s ≡ just t → On (B.view s) → Moves (B.view s) (B.view t)
  fork-moves′ w s eq v with lookup w (O.acquiring (B.source s))
  ... | nothing = case eq of λ ()
  ... | just f with B.freshChild (A.child (A.req f)) s in fresh
  ...   | false = case eq of λ ()
  ...   | true with O.advance (O.acquire w A.forkOK) (B.source s) in actual
  ...     | nothing = case eq of λ ()
  ...     | just c with lookup (A.child (A.req f)) (S.handlers (M.world (O.core c)))
  ...       | nothing = case eq of λ ()
  ...       | just captured = case just-injective eq of λ { refl →
    update (A.child (A.req f)) (H.handlerThread captured H.maskedSetup)
      (fresh-free v (Physical.fresh-thread (A.child (A.req f)) s fresh)) refl
      (outbound-same (O.acquire w A.forkOK) (B.source s) actual tt)
      (absent v (fresh-free v (Physical.fresh-thread (A.child (A.req f)) s fresh)) (Physical.fresh-thread (A.child (A.req f)) s fresh)) v }
  step-moves′ : ∀ a s {t} → Guarded a s → B.step a s ≡ just t → On (B.view s) → Moves (B.view s) (B.view t)
  step-moves′ (B.handler a) s g eq v with B.handlerAllowed a s
  ... | false = case eq of λ ()
  ... | true with H.step a (B.view s) in actual
  ...   | nothing = case eq of λ ()
  ...   | just h = case just-injective eq of λ { refl → step-moves a (B.view s) g actual v }
  step-moves′ (B.outbound a) s g eq v with B.forkCaller a
  ... | just w = fork-moves′ w s eq v
  ... | nothing with B.outboundAllowed a s in allowed
  ...   | false = case eq of λ ()
  ...   | true with O.advance a (B.source s) in actual
  ...     | nothing = case eq of λ ()
  ...     | just c = case just-injective eq of λ { refl → transport refl (outbound-same a (B.source s) actual (Physical.allowed-quiet a s allowed)) v }
