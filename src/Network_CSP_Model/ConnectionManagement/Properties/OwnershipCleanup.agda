{-# OPTIONS --guardedness #-}

-- Every cleanup action preserves exclusive map ownership, including finalization.
module ConnectionManagement.Properties.OwnershipCleanup where

open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.State
open import ConnectionManagement.Properties.Ownership
open import ConnectionManagement.Properties.OwnershipNeutral
open import ConnectionManagement.Properties.OwnershipSteps
open import ConnectionManagement.Properties.OwnershipMapDispatcher
import ConnectionManagement.Rules.Cleanup as Cleanup

-- Each decision retains the exact captured lease, even when it writes the heap.
select-preserves : ∀ w h l decision s → lookup w (cleanups s) ≡ just (cleanupSelect l) →
  Ownership s → Ownership (Cleanup.selectCleanup w h l decision s)
select-preserves w h l Cleanup.terminateAndPurge s found own = cleanup-neutral w (cleanupSelect l)
  (cleanupClose l (Cleanup.purgeCaptured (handlerKey h) (handlerEntry h) (savedMap l)) countImmediately)
  (record s { cm = record (cm s) { entries = put (handlerEntry h) (terminated nothing) (entries (cm s)) } }) found refl own
select-preserves w h l Cleanup.purgeOnly s found own = cleanup-neutral w (cleanupSelect l)
  (cleanupClose l (Cleanup.purgeCaptured (handlerKey h) (handlerEntry h) (savedMap l)) countImmediately) s found refl own
select-preserves w h l (Cleanup.waitBeforePurge st) s found own = cleanup-neutral w (cleanupSelect l)
  (cleanupClose l (savedMap l) (timeWait st)) s found refl own

cleanup-worker : ∀ action w h p s {s′} → lookup w (cleanups s) ≡ just p →
  Cleanup.stepWorker w h p action s ≡ just s′ → Ownership s → Ownership s′
cleanup-worker Cleanup.takeCleanupMap = take-cleanup-worker
cleanup-worker Cleanup.publishCleanupMap = publish-cleanup-worker
cleanup-worker Cleanup.restoreCleanupMap = restore-cleanup-worker
cleanup-worker Cleanup.closeHandlerSocket = close-worker
cleanup-worker (Cleanup.failSocketClose err) w h p s = fail-worker w h p err s
cleanup-worker Cleanup.selectCleanupEntry w h cleanupAcquire s found () own
cleanup-worker Cleanup.selectCleanupEntry w h (cleanupClose l m tail) s found () own
cleanup-worker Cleanup.selectCleanupEntry w h (cleanupPublish l m tail) s found () own
cleanup-worker Cleanup.selectCleanupEntry w h (cleanupRestore l err) s found () own
cleanup-worker Cleanup.selectCleanupEntry w h (cleanupWaiting st) s found () own
cleanup-worker Cleanup.selectCleanupEntry w h (cleanupFinalize st outcome) s found () own
cleanup-worker Cleanup.selectCleanupEntry w h (cleanupCount outcome) s found () own
cleanup-worker Cleanup.selectCleanupEntry w h (cleanupDone outcome) s found () own
cleanup-worker Cleanup.selectCleanupEntry w h (cleanupSelect l) s found eq own with mapCell (cm s) in cell
... | full _ = case eq of λ ()
... | taken owner with owner ≟ w
...   | no _ = case eq of λ ()
...   | yes _ with lookup (handlerEntry h) (entries (cm s))
...     | nothing = case eq of λ ()
...     | just st = subst Ownership (just-injective eq) (select-preserves w h l (Cleanup.decideCleanup st) s found
        (subst (λ cell → Owns cell (claims s)) (sym cell) own))
cleanup-worker Cleanup.timeWaitElapsed w h cleanupAcquire s found () own
cleanup-worker Cleanup.timeWaitElapsed w h (cleanupSelect l) s found () own
cleanup-worker Cleanup.timeWaitElapsed w h (cleanupClose l m tail) s found () own
cleanup-worker Cleanup.timeWaitElapsed w h (cleanupPublish l m tail) s found () own
cleanup-worker Cleanup.timeWaitElapsed w h (cleanupRestore l err) s found () own
cleanup-worker Cleanup.timeWaitElapsed w h (cleanupFinalize st outcome) s found () own
cleanup-worker Cleanup.timeWaitElapsed w h (cleanupCount outcome) s found () own
cleanup-worker Cleanup.timeWaitElapsed w h (cleanupDone outcome) s found () own
cleanup-worker Cleanup.timeWaitElapsed w h (cleanupWaiting st) s found eq own =
  subst Ownership (just-injective eq) (cleanup-neutral w (cleanupWaiting st) (cleanupFinalize st cleanupNormal) s found refl own)
cleanup-worker (Cleanup.interruptTimeWait error) w h cleanupAcquire s found () own
cleanup-worker (Cleanup.interruptTimeWait error) w h (cleanupSelect l) s found () own
cleanup-worker (Cleanup.interruptTimeWait error) w h (cleanupClose l m tail) s found () own
cleanup-worker (Cleanup.interruptTimeWait error) w h (cleanupPublish l m tail) s found () own
cleanup-worker (Cleanup.interruptTimeWait error) w h (cleanupRestore l err) s found () own
cleanup-worker (Cleanup.interruptTimeWait error) w h (cleanupFinalize st outcome) s found () own
cleanup-worker (Cleanup.interruptTimeWait error) w h (cleanupCount outcome) s found () own
cleanup-worker (Cleanup.interruptTimeWait error) w h (cleanupDone outcome) s found () own
cleanup-worker (Cleanup.interruptTimeWait error) w h (cleanupWaiting st) s found eq own =
  subst Ownership (just-injective eq) (cleanup-neutral w (cleanupWaiting st) (cleanupFinalize st (cleanupError error)) s found refl own)
cleanup-worker Cleanup.finishTimeWait w h cleanupAcquire s found () own
cleanup-worker Cleanup.finishTimeWait w h (cleanupSelect l) s found () own
cleanup-worker Cleanup.finishTimeWait w h (cleanupClose l m tail) s found () own
cleanup-worker Cleanup.finishTimeWait w h (cleanupPublish l m tail) s found () own
cleanup-worker Cleanup.finishTimeWait w h (cleanupRestore l err) s found () own
cleanup-worker Cleanup.finishTimeWait w h (cleanupWaiting st) s found () own
cleanup-worker Cleanup.finishTimeWait w h (cleanupCount outcome) s found () own
cleanup-worker Cleanup.finishTimeWait w h (cleanupDone outcome) s found () own
cleanup-worker Cleanup.finishTimeWait w h (cleanupFinalize st outcome) s found eq own with mapCell (cm s) in cell
... | taken _ = case eq of λ ()
... | full m with lookup (handlerEntry h) (entries (cm s))
...   | nothing = case eq of λ ()
...   | just _ = subst Ownership (just-injective eq) (cleanup-neutral w (cleanupFinalize st outcome) (cleanupCount outcome)
    (record s { cm = record (cm s)
      { mapCell = full (Cleanup.purgeCaptured (handlerKey h) (handlerEntry h) m)
      ; entries = Cleanup.finishEntry (handlerEntry h) st (entries (cm s)) } }) found refl own)
cleanup-worker Cleanup.readCleanupCounters w h cleanupAcquire s found () own
cleanup-worker Cleanup.readCleanupCounters w h (cleanupSelect l) s found () own
cleanup-worker Cleanup.readCleanupCounters w h (cleanupClose l m tail) s found () own
cleanup-worker Cleanup.readCleanupCounters w h (cleanupPublish l m tail) s found () own
cleanup-worker Cleanup.readCleanupCounters w h (cleanupRestore l err) s found () own
cleanup-worker Cleanup.readCleanupCounters w h (cleanupWaiting st) s found () own
cleanup-worker Cleanup.readCleanupCounters w h (cleanupFinalize st outcome) s found () own
cleanup-worker Cleanup.readCleanupCounters w h (cleanupDone outcome) s found () own
cleanup-worker Cleanup.readCleanupCounters w h (cleanupCount outcome) s found eq own with mapCell (cm s) in cell
... | taken _ = case eq of λ ()
... | full m with countIncoming (entries (cm s)) m
...   | nothing = case eq of λ ()
...   | just _ = subst Ownership (just-injective eq) (cleanup-neutral w (cleanupCount outcome) (cleanupDone outcome) s found refl
    (subst (λ cell → Owns cell (claims s)) (sym cell) own))
