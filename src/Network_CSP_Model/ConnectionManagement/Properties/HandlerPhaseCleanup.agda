{-# OPTIONS --guardedness #-}

-- Phase/cleanup validity for physical handler threads (CM-I4c). Every tracked
-- thread's phase determines the shared cleanup record of its worker: none before
-- the finalizer, some record while finalizing, and the completed record with the
-- observed outcome once cleanup completion or the Async result is recorded. An
-- untracked worker has no cleanup record. Every initialized HandlerSupervision
-- and OutboundHandlerSupervision run preserves this. MuxHandlerExit exit frames
-- and the layers above are not covered here.
module ConnectionManagement.Properties.HandlerPhaseCleanup where

open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
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
