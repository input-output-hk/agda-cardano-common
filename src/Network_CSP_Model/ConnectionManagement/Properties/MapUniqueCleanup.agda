{-# OPTIONS --guardedness #-}

-- Cleanup preserves uniqueness of original and prospective maps.
module ConnectionManagement.Properties.MapUniqueCleanup where

open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.State
open import ConnectionManagement.Properties.StateMapUniqueness
open import ConnectionManagement.Properties.MapUniqueness using (MapUnique)
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.CM as CM

-- Selection derives the prospective map from the captured original.
select-preserves : ∀ w h l decision s → MapUnique (savedMap l) → Valid s →
  Valid (Cleanup.selectCleanup w h l decision s)
select-preserves w h l Cleanup.terminateAndPurge s av v =
  cleanup-update w (cleanupClose l (Cleanup.purgeCaptured (handlerKey h) (handlerEntry h) (savedMap l)) countImmediately)
    (record s { cm = record (cm s) { entries = put (handlerEntry h) (terminated nothing) (entries (cm s)) } })
    (av , purge-unique (handlerKey h) (handlerEntry h) (savedMap l) av) v
select-preserves w h l Cleanup.purgeOnly s av v =
  cleanup-update w (cleanupClose l (Cleanup.purgeCaptured (handlerKey h) (handlerEntry h) (savedMap l)) countImmediately)
    s (av , purge-unique (handlerKey h) (handlerEntry h) (savedMap l) av) v
select-preserves w h l (Cleanup.waitBeforePurge st) s av v =
  cleanup-update w (cleanupClose l (savedMap l) (timeWait st)) s (av , av) v

-- Publication removes both captured maps from the continuation.
after-valid : ∀ tail → CleanupMaps (Cleanup.afterPublish tail)
after-valid countImmediately = tt
after-valid (timeWait _) = tt

-- The selected cleanup frame certificate is obtained from the runtime store.
cleanup-preserves : ∀ action w h p s {s′} → Cleanup.stepWorker w h p action s ≡ just s′ →
  CleanupMaps p → Valid s → Valid s′
cleanup-preserves Cleanup.takeCleanupMap w h cleanupAcquire s eq av v with CM.takeMap w (cm s) in takenEq
... | nothing = case eq of λ ()
... | just (l , c′) = subst Valid (just-injective eq) (cleanup-update w (cleanupSelect l) (record s { cm = c′ })
  (proj₂ (take-maps w s takenEq v)) (proj₁ (take-maps w s takenEq v) , proj₂ v))
cleanup-preserves Cleanup.takeCleanupMap w h (cleanupSelect l) s () av v
cleanup-preserves Cleanup.takeCleanupMap w h (cleanupClose l m tail) s () av v
cleanup-preserves Cleanup.takeCleanupMap w h (cleanupPublish l m tail) s () av v
cleanup-preserves Cleanup.takeCleanupMap w h (cleanupRestore l err) s () av v
cleanup-preserves Cleanup.takeCleanupMap w h (cleanupWaiting st) s () av v
cleanup-preserves Cleanup.takeCleanupMap w h (cleanupFinalize st outcome) s () av v
cleanup-preserves Cleanup.takeCleanupMap w h (cleanupCount outcome) s () av v
cleanup-preserves Cleanup.takeCleanupMap w h (cleanupDone outcome) s () av v
cleanup-preserves Cleanup.selectCleanupEntry w h (cleanupSelect l) s eq av v with mapCell (cm s) in cell
... | full _ = case eq of λ ()
... | taken owner with owner ≟ w
...   | no _ = case eq of λ ()
...   | yes _ with lookup (handlerEntry h) (entries (cm s))
...     | nothing = case eq of λ ()
...     | just st = subst Valid (just-injective eq) (select-preserves w h l (Cleanup.decideCleanup st) s av
  (restore-current s (taken owner) cell v))
cleanup-preserves Cleanup.selectCleanupEntry w h cleanupAcquire s () av v
cleanup-preserves Cleanup.selectCleanupEntry w h (cleanupClose l m tail) s () av v
cleanup-preserves Cleanup.selectCleanupEntry w h (cleanupPublish l m tail) s () av v
cleanup-preserves Cleanup.selectCleanupEntry w h (cleanupRestore l err) s () av v
cleanup-preserves Cleanup.selectCleanupEntry w h (cleanupWaiting st) s () av v
cleanup-preserves Cleanup.selectCleanupEntry w h (cleanupFinalize st outcome) s () av v
cleanup-preserves Cleanup.selectCleanupEntry w h (cleanupCount outcome) s () av v
cleanup-preserves Cleanup.selectCleanupEntry w h (cleanupDone outcome) s () av v
cleanup-preserves Cleanup.closeHandlerSocket w h (cleanupClose l m tail) s eq av v = subst Valid (just-injective eq) (cleanup-update w (cleanupPublish l m tail) (record s
  { sockets = put (handlerSocket h) closed (sockets s) }) av v)
cleanup-preserves Cleanup.closeHandlerSocket w h cleanupAcquire s () av v
cleanup-preserves Cleanup.closeHandlerSocket w h (cleanupSelect l) s () av v
cleanup-preserves Cleanup.closeHandlerSocket w h (cleanupPublish l m tail) s () av v
cleanup-preserves Cleanup.closeHandlerSocket w h (cleanupRestore l err) s () av v
cleanup-preserves Cleanup.closeHandlerSocket w h (cleanupWaiting st) s () av v
cleanup-preserves Cleanup.closeHandlerSocket w h (cleanupFinalize st outcome) s () av v
cleanup-preserves Cleanup.closeHandlerSocket w h (cleanupCount outcome) s () av v
cleanup-preserves Cleanup.closeHandlerSocket w h (cleanupDone outcome) s () av v
cleanup-preserves (Cleanup.failSocketClose error) w h (cleanupClose l m tail) s eq av v = subst Valid (just-injective eq) (cleanup-update w (cleanupRestore l error) (record s
  { sockets = put (handlerSocket h) (closeUncertain error) (sockets s) }) (proj₁ av) v)
cleanup-preserves (Cleanup.failSocketClose error) w h cleanupAcquire s () av v
cleanup-preserves (Cleanup.failSocketClose error) w h (cleanupSelect l) s () av v
cleanup-preserves (Cleanup.failSocketClose error) w h (cleanupPublish l m tail) s () av v
cleanup-preserves (Cleanup.failSocketClose error) w h (cleanupRestore l err) s () av v
cleanup-preserves (Cleanup.failSocketClose error) w h (cleanupWaiting st) s () av v
cleanup-preserves (Cleanup.failSocketClose error) w h (cleanupFinalize st outcome) s () av v
cleanup-preserves (Cleanup.failSocketClose error) w h (cleanupCount outcome) s () av v
cleanup-preserves (Cleanup.failSocketClose error) w h (cleanupDone outcome) s () av v
cleanup-preserves Cleanup.publishCleanupMap w h (cleanupPublish l m tail) s eq av v with CM.putMap l m (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst Valid (just-injective eq) (cleanup-update w (Cleanup.afterPublish tail) (record s { cm = c′ }) (after-valid tail)
  (put-maps l m s putEq (proj₂ av) v))
cleanup-preserves Cleanup.publishCleanupMap w h cleanupAcquire s () av v
cleanup-preserves Cleanup.publishCleanupMap w h (cleanupSelect l) s () av v
cleanup-preserves Cleanup.publishCleanupMap w h (cleanupClose l m tail) s () av v
cleanup-preserves Cleanup.publishCleanupMap w h (cleanupRestore l err) s () av v
cleanup-preserves Cleanup.publishCleanupMap w h (cleanupWaiting st) s () av v
cleanup-preserves Cleanup.publishCleanupMap w h (cleanupFinalize st outcome) s () av v
cleanup-preserves Cleanup.publishCleanupMap w h (cleanupCount outcome) s () av v
cleanup-preserves Cleanup.publishCleanupMap w h (cleanupDone outcome) s () av v
cleanup-preserves Cleanup.restoreCleanupMap w h (cleanupRestore l err) s eq av v with CM.restoreMap l (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst Valid (just-injective eq) (cleanup-update w (cleanupDone (cleanupError err)) (record s { cm = c′ }) tt
  (put-maps l (savedMap l) s putEq av v))
cleanup-preserves Cleanup.restoreCleanupMap w h cleanupAcquire s () av v
cleanup-preserves Cleanup.restoreCleanupMap w h (cleanupSelect l) s () av v
cleanup-preserves Cleanup.restoreCleanupMap w h (cleanupClose l m tail) s () av v
cleanup-preserves Cleanup.restoreCleanupMap w h (cleanupPublish l m tail) s () av v
cleanup-preserves Cleanup.restoreCleanupMap w h (cleanupWaiting st) s () av v
cleanup-preserves Cleanup.restoreCleanupMap w h (cleanupFinalize st outcome) s () av v
cleanup-preserves Cleanup.restoreCleanupMap w h (cleanupCount outcome) s () av v
cleanup-preserves Cleanup.restoreCleanupMap w h (cleanupDone outcome) s () av v
cleanup-preserves Cleanup.timeWaitElapsed w h (cleanupWaiting st) s eq av v = subst Valid (just-injective eq) (cleanup-update w (cleanupFinalize st cleanupNormal) s tt v)
cleanup-preserves Cleanup.timeWaitElapsed w h cleanupAcquire s () av v
cleanup-preserves Cleanup.timeWaitElapsed w h (cleanupSelect l) s () av v
cleanup-preserves Cleanup.timeWaitElapsed w h (cleanupClose l m tail) s () av v
cleanup-preserves Cleanup.timeWaitElapsed w h (cleanupPublish l m tail) s () av v
cleanup-preserves Cleanup.timeWaitElapsed w h (cleanupRestore l err) s () av v
cleanup-preserves Cleanup.timeWaitElapsed w h (cleanupFinalize st outcome) s () av v
cleanup-preserves Cleanup.timeWaitElapsed w h (cleanupCount outcome) s () av v
cleanup-preserves Cleanup.timeWaitElapsed w h (cleanupDone outcome) s () av v
cleanup-preserves (Cleanup.interruptTimeWait error) w h (cleanupWaiting st) s eq av v = subst Valid (just-injective eq) (cleanup-update w (cleanupFinalize st (cleanupError error)) s tt v)
cleanup-preserves (Cleanup.interruptTimeWait error) w h cleanupAcquire s () av v
cleanup-preserves (Cleanup.interruptTimeWait error) w h (cleanupSelect l) s () av v
cleanup-preserves (Cleanup.interruptTimeWait error) w h (cleanupClose l m tail) s () av v
cleanup-preserves (Cleanup.interruptTimeWait error) w h (cleanupPublish l m tail) s () av v
cleanup-preserves (Cleanup.interruptTimeWait error) w h (cleanupRestore l err) s () av v
cleanup-preserves (Cleanup.interruptTimeWait error) w h (cleanupFinalize st outcome) s () av v
cleanup-preserves (Cleanup.interruptTimeWait error) w h (cleanupCount outcome) s () av v
cleanup-preserves (Cleanup.interruptTimeWait error) w h (cleanupDone outcome) s () av v
cleanup-preserves Cleanup.finishTimeWait w h (cleanupFinalize st outcome) s eq av v with mapCell (cm s) in cell
... | taken _ = case eq of λ ()
... | full m with lookup (handlerEntry h) (entries (cm s))
...   | nothing = case eq of λ ()
...   | just _ = subst Valid (just-injective eq) (cleanup-update w (cleanupCount outcome) (record s { cm = record (cm s)
  { mapCell = full (Cleanup.purgeCaptured (handlerKey h) (handlerEntry h) m)
  ; entries = Cleanup.finishEntry (handlerEntry h) st (entries (cm s)) } }) tt
  (purge-unique (handlerKey h) (handlerEntry h) m (proj₁ v) , proj₂ v))
cleanup-preserves Cleanup.finishTimeWait w h cleanupAcquire s () av v
cleanup-preserves Cleanup.finishTimeWait w h (cleanupSelect l) s () av v
cleanup-preserves Cleanup.finishTimeWait w h (cleanupClose l m tail) s () av v
cleanup-preserves Cleanup.finishTimeWait w h (cleanupPublish l m tail) s () av v
cleanup-preserves Cleanup.finishTimeWait w h (cleanupRestore l err) s () av v
cleanup-preserves Cleanup.finishTimeWait w h (cleanupWaiting st) s () av v
cleanup-preserves Cleanup.finishTimeWait w h (cleanupCount outcome) s () av v
cleanup-preserves Cleanup.finishTimeWait w h (cleanupDone outcome) s () av v
cleanup-preserves Cleanup.readCleanupCounters w h (cleanupCount outcome) s eq av v with mapCell (cm s) in cell
... | taken _ = case eq of λ ()
... | full m with countIncoming (entries (cm s)) m
...   | nothing = case eq of λ ()
...   | just _ = subst Valid (just-injective eq) (cleanup-update w (cleanupDone outcome) s tt (restore-current s (full m) cell v))
cleanup-preserves Cleanup.readCleanupCounters w h cleanupAcquire s () av v
cleanup-preserves Cleanup.readCleanupCounters w h (cleanupSelect l) s () av v
cleanup-preserves Cleanup.readCleanupCounters w h (cleanupClose l m tail) s () av v
cleanup-preserves Cleanup.readCleanupCounters w h (cleanupPublish l m tail) s () av v
cleanup-preserves Cleanup.readCleanupCounters w h (cleanupRestore l err) s () av v
cleanup-preserves Cleanup.readCleanupCounters w h (cleanupWaiting st) s () av v
cleanup-preserves Cleanup.readCleanupCounters w h (cleanupFinalize st outcome) s () av v
cleanup-preserves Cleanup.readCleanupCounters w h (cleanupDone outcome) s () av v
