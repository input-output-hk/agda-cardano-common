{-# OPTIONS --guardedness #-}

-- Supply preservation includes cleanup entry writes and captured TIME_WAIT state.
module ConnectionManagement.Properties.SupplyCleanup where

open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.State
open import ConnectionManagement.Properties.Freshness using (BelowSupply)
open import ConnectionManagement.Properties.SupplyBounds
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.CM as CM

select-preserves : ∀ w h l decision s {old} → lookup (handlerEntry h) (entries (cm s)) ≡ just old →
  SupplyBounds s → SupplyBounds (Cleanup.selectCleanup w h l decision s)
select-preserves w h l Cleanup.terminateAndPurge s found (eb , pb) =
  overwrite-bound (nextEntry (cm s)) (handlerEntry h) (terminated nothing) (entries (cm s)) eb found , pb
select-preserves w h l Cleanup.purgeOnly s found bounded = bounded
select-preserves w h l (Cleanup.waitBeforePurge st) s found bounded = bounded

finish-bound : ∀ n e captured heap {old} → lookup e heap ≡ just old → BelowSupply n heap →
  BelowSupply n (Cleanup.finishEntry e captured heap)
finish-bound n e (terminated _) heap found bounded = bounded
finish-bound n e reservedOutbound heap found bounded = overwrite-bound n e (terminated nothing) heap bounded found
finish-bound n e (unnegotiated _ _ _) heap found bounded = overwrite-bound n e (terminated nothing) heap bounded found
finish-bound n e (outboundUni _ _ _) heap found bounded = overwrite-bound n e (terminated nothing) heap bounded found
finish-bound n e (outboundDup _ _ _ _) heap found bounded = overwrite-bound n e (terminated nothing) heap bounded found
finish-bound n e (outboundIdle _ _ _ _) heap found bounded = overwrite-bound n e (terminated nothing) heap bounded found
finish-bound n e (inboundIdle _ _ _ _) heap found bounded = overwrite-bound n e (terminated nothing) heap bounded found
finish-bound n e (inboundActive _ _ _ _) heap found bounded = overwrite-bound n e (terminated nothing) heap bounded found
finish-bound n e (duplexActive _ _ _) heap found bounded = overwrite-bound n e (terminated nothing) heap bounded found
finish-bound n e (terminating _ _ _) heap found bounded = overwrite-bound n e (terminated nothing) heap bounded found

cleanup-preserves : ∀ action w h p s {s′} → Cleanup.stepWorker w h p action s ≡ just s′ →
  SupplyBounds s → SupplyBounds s′
cleanup-preserves Cleanup.takeCleanupMap w h (cleanupSelect l) s () bounded
cleanup-preserves Cleanup.takeCleanupMap w h (cleanupClose l m tail) s () bounded
cleanup-preserves Cleanup.takeCleanupMap w h (cleanupPublish l m tail) s () bounded
cleanup-preserves Cleanup.takeCleanupMap w h (cleanupRestore l err) s () bounded
cleanup-preserves Cleanup.takeCleanupMap w h (cleanupWaiting st) s () bounded
cleanup-preserves Cleanup.takeCleanupMap w h (cleanupFinalize st outcome) s () bounded
cleanup-preserves Cleanup.takeCleanupMap w h (cleanupCount outcome) s () bounded
cleanup-preserves Cleanup.takeCleanupMap w h (cleanupDone outcome) s () bounded
cleanup-preserves Cleanup.takeCleanupMap w h cleanupAcquire s eq (eb , pb) with CM.takeMap w (cm s) in takenEq
... | nothing = case eq of λ ()
... | just (l , c′) = subst SupplyBounds (just-injective eq) (take-bound w (cm s) takenEq eb , pb)
cleanup-preserves Cleanup.selectCleanupEntry w h cleanupAcquire s () bounded
cleanup-preserves Cleanup.selectCleanupEntry w h (cleanupClose l m tail) s () bounded
cleanup-preserves Cleanup.selectCleanupEntry w h (cleanupPublish l m tail) s () bounded
cleanup-preserves Cleanup.selectCleanupEntry w h (cleanupRestore l err) s () bounded
cleanup-preserves Cleanup.selectCleanupEntry w h (cleanupWaiting st) s () bounded
cleanup-preserves Cleanup.selectCleanupEntry w h (cleanupFinalize st outcome) s () bounded
cleanup-preserves Cleanup.selectCleanupEntry w h (cleanupCount outcome) s () bounded
cleanup-preserves Cleanup.selectCleanupEntry w h (cleanupDone outcome) s () bounded
cleanup-preserves Cleanup.selectCleanupEntry w h (cleanupSelect l) s eq bounded with mapCell (cm s)
... | full _ = case eq of λ ()
... | taken owner with owner ≟ w
...   | no _ = case eq of λ ()
...   | yes _ with lookup (handlerEntry h) (entries (cm s)) in found
...     | nothing = case eq of λ ()
...     | just st = subst SupplyBounds (just-injective eq) (select-preserves w h l (Cleanup.decideCleanup st) s found bounded)
cleanup-preserves Cleanup.closeHandlerSocket w h cleanupAcquire s () bounded
cleanup-preserves Cleanup.closeHandlerSocket w h (cleanupSelect l) s () bounded
cleanup-preserves Cleanup.closeHandlerSocket w h (cleanupPublish l m tail) s () bounded
cleanup-preserves Cleanup.closeHandlerSocket w h (cleanupRestore l err) s () bounded
cleanup-preserves Cleanup.closeHandlerSocket w h (cleanupWaiting st) s () bounded
cleanup-preserves Cleanup.closeHandlerSocket w h (cleanupFinalize st outcome) s () bounded
cleanup-preserves Cleanup.closeHandlerSocket w h (cleanupCount outcome) s () bounded
cleanup-preserves Cleanup.closeHandlerSocket w h (cleanupDone outcome) s () bounded
cleanup-preserves Cleanup.closeHandlerSocket w h (cleanupClose l m tail) s eq bounded = subst SupplyBounds (just-injective eq) bounded
cleanup-preserves (Cleanup.failSocketClose error) w h cleanupAcquire s () bounded
cleanup-preserves (Cleanup.failSocketClose error) w h (cleanupSelect l) s () bounded
cleanup-preserves (Cleanup.failSocketClose error) w h (cleanupPublish l m tail) s () bounded
cleanup-preserves (Cleanup.failSocketClose error) w h (cleanupRestore l err) s () bounded
cleanup-preserves (Cleanup.failSocketClose error) w h (cleanupWaiting st) s () bounded
cleanup-preserves (Cleanup.failSocketClose error) w h (cleanupFinalize st outcome) s () bounded
cleanup-preserves (Cleanup.failSocketClose error) w h (cleanupCount outcome) s () bounded
cleanup-preserves (Cleanup.failSocketClose error) w h (cleanupDone outcome) s () bounded
cleanup-preserves (Cleanup.failSocketClose error) w h (cleanupClose l m tail) s eq bounded = subst SupplyBounds (just-injective eq) bounded
cleanup-preserves Cleanup.publishCleanupMap w h cleanupAcquire s () bounded
cleanup-preserves Cleanup.publishCleanupMap w h (cleanupSelect l) s () bounded
cleanup-preserves Cleanup.publishCleanupMap w h (cleanupClose l m tail) s () bounded
cleanup-preserves Cleanup.publishCleanupMap w h (cleanupRestore l err) s () bounded
cleanup-preserves Cleanup.publishCleanupMap w h (cleanupWaiting st) s () bounded
cleanup-preserves Cleanup.publishCleanupMap w h (cleanupFinalize st outcome) s () bounded
cleanup-preserves Cleanup.publishCleanupMap w h (cleanupCount outcome) s () bounded
cleanup-preserves Cleanup.publishCleanupMap w h (cleanupDone outcome) s () bounded
cleanup-preserves Cleanup.publishCleanupMap w h (cleanupPublish l m tail) s eq (eb , pb) with CM.putMap l m (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst SupplyBounds (just-injective eq) (put-bound l m (cm s) putEq eb , pb)
cleanup-preserves Cleanup.restoreCleanupMap w h cleanupAcquire s () bounded
cleanup-preserves Cleanup.restoreCleanupMap w h (cleanupSelect l) s () bounded
cleanup-preserves Cleanup.restoreCleanupMap w h (cleanupClose l m tail) s () bounded
cleanup-preserves Cleanup.restoreCleanupMap w h (cleanupPublish l m tail) s () bounded
cleanup-preserves Cleanup.restoreCleanupMap w h (cleanupWaiting st) s () bounded
cleanup-preserves Cleanup.restoreCleanupMap w h (cleanupFinalize st outcome) s () bounded
cleanup-preserves Cleanup.restoreCleanupMap w h (cleanupCount outcome) s () bounded
cleanup-preserves Cleanup.restoreCleanupMap w h (cleanupDone outcome) s () bounded
cleanup-preserves Cleanup.restoreCleanupMap w h (cleanupRestore l err) s eq (eb , pb) with CM.putMap l (savedMap l) (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst SupplyBounds (just-injective eq) (put-bound l (savedMap l) (cm s) putEq eb , pb)
cleanup-preserves Cleanup.timeWaitElapsed w h cleanupAcquire s () bounded
cleanup-preserves Cleanup.timeWaitElapsed w h (cleanupSelect l) s () bounded
cleanup-preserves Cleanup.timeWaitElapsed w h (cleanupClose l m tail) s () bounded
cleanup-preserves Cleanup.timeWaitElapsed w h (cleanupPublish l m tail) s () bounded
cleanup-preserves Cleanup.timeWaitElapsed w h (cleanupRestore l err) s () bounded
cleanup-preserves Cleanup.timeWaitElapsed w h (cleanupFinalize st outcome) s () bounded
cleanup-preserves Cleanup.timeWaitElapsed w h (cleanupCount outcome) s () bounded
cleanup-preserves Cleanup.timeWaitElapsed w h (cleanupDone outcome) s () bounded
cleanup-preserves Cleanup.timeWaitElapsed w h (cleanupWaiting st) s eq bounded = subst SupplyBounds (just-injective eq) bounded
cleanup-preserves (Cleanup.interruptTimeWait error) w h cleanupAcquire s () bounded
cleanup-preserves (Cleanup.interruptTimeWait error) w h (cleanupSelect l) s () bounded
cleanup-preserves (Cleanup.interruptTimeWait error) w h (cleanupClose l m tail) s () bounded
cleanup-preserves (Cleanup.interruptTimeWait error) w h (cleanupPublish l m tail) s () bounded
cleanup-preserves (Cleanup.interruptTimeWait error) w h (cleanupRestore l err) s () bounded
cleanup-preserves (Cleanup.interruptTimeWait error) w h (cleanupFinalize st outcome) s () bounded
cleanup-preserves (Cleanup.interruptTimeWait error) w h (cleanupCount outcome) s () bounded
cleanup-preserves (Cleanup.interruptTimeWait error) w h (cleanupDone outcome) s () bounded
cleanup-preserves (Cleanup.interruptTimeWait error) w h (cleanupWaiting st) s eq bounded = subst SupplyBounds (just-injective eq) bounded
cleanup-preserves Cleanup.finishTimeWait w h cleanupAcquire s () bounded
cleanup-preserves Cleanup.finishTimeWait w h (cleanupSelect l) s () bounded
cleanup-preserves Cleanup.finishTimeWait w h (cleanupClose l m tail) s () bounded
cleanup-preserves Cleanup.finishTimeWait w h (cleanupPublish l m tail) s () bounded
cleanup-preserves Cleanup.finishTimeWait w h (cleanupRestore l err) s () bounded
cleanup-preserves Cleanup.finishTimeWait w h (cleanupWaiting st) s () bounded
cleanup-preserves Cleanup.finishTimeWait w h (cleanupCount outcome) s () bounded
cleanup-preserves Cleanup.finishTimeWait w h (cleanupDone outcome) s () bounded
cleanup-preserves Cleanup.finishTimeWait w h (cleanupFinalize st outcome) s eq (eb , pb) with mapCell (cm s)
... | taken _ = case eq of λ ()
... | full m with lookup (handlerEntry h) (entries (cm s)) in found
...   | nothing = case eq of λ ()
...   | just _ = subst SupplyBounds (just-injective eq)
  (finish-bound (nextEntry (cm s)) (handlerEntry h) st (entries (cm s)) found eb , pb)
cleanup-preserves Cleanup.readCleanupCounters w h cleanupAcquire s () bounded
cleanup-preserves Cleanup.readCleanupCounters w h (cleanupSelect l) s () bounded
cleanup-preserves Cleanup.readCleanupCounters w h (cleanupClose l m tail) s () bounded
cleanup-preserves Cleanup.readCleanupCounters w h (cleanupPublish l m tail) s () bounded
cleanup-preserves Cleanup.readCleanupCounters w h (cleanupRestore l err) s () bounded
cleanup-preserves Cleanup.readCleanupCounters w h (cleanupWaiting st) s () bounded
cleanup-preserves Cleanup.readCleanupCounters w h (cleanupFinalize st outcome) s () bounded
cleanup-preserves Cleanup.readCleanupCounters w h (cleanupDone outcome) s () bounded
cleanup-preserves Cleanup.readCleanupCounters w h (cleanupCount outcome) s eq bounded with mapCell (cm s)
... | taken _ = case eq of λ ()
... | full m with countIncoming (entries (cm s)) m
...   | nothing = case eq of λ ()
...   | just _ = subst SupplyBounds (just-injective eq) bounded
