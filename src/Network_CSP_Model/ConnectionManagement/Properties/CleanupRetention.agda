{-# OPTIONS --guardedness #-}

-- Cleanup retains original references even when socket and entry values change.
module ConnectionManagement.Properties.CleanupRetention where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.State
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.Entries using (Present; put-preserves-present)
open import ConnectionManagement.Properties.HandlerReferences hiding (exec-preserves)
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.CM as CM

-- Preserve immutable stores exactly and mutable objects by identity.
record Retains (s s′ : State) : Set where
  constructor retains
  field
    handlersSame : handlers s′ ≡ handlers s
    resultsSame : handshakeResults s′ ≡ handshakeResults s
    entriesRetained : ∀ e → Present e (entries (cm s)) → Present e (entries (cm s′))
    socketsRetained : ∀ sock → Present sock (sockets s) → Present sock (sockets s′)
open Retains public

retains-chain : ∀ {w mid s s′ ig} → Retains s s′ → Chain w mid s ig → Chain w mid s′ ig
retains-chain eff ch = record
  { originalHandler = originalHandler ch; publishedHandle = publishedHandle ch
  ; negotiatedFlow = negotiatedFlow ch; handleValue = handleValue ch; muxValue = muxValue ch
  ; handlerFound = trans (cong (lookup _) (handlersSame eff)) (handlerFound ch)
  ; promiseFound = trans (cong (lookup _) (resultsSame eff)) (promiseFound ch)
  ; handleFound = handleFound ch; handleMux = handleMux ch; muxFound = muxFound ch
  ; keyMatches = keyMatches ch
  ; entryPresent = entriesRetained eff _ (entryPresent ch)
  ; socketPresent = socketsRetained eff _ (socketPresent ch) }

reframe : ∀ {s} c′ ss pcs →
  (∀ e → Present e (entries (cm s)) → Present e (entries c′)) →
  (∀ sock → Present sock (sockets s) → Present sock ss) →
  Retains s (record s { cm = c′; sockets = ss; cleanups = pcs })
reframe c′ ss pcs ep sp = retains refl refl ep sp

take-entries : ∀ w c {l c′} → CM.takeMap w c ≡ just (l , c′) → entries c′ ≡ entries c
take-entries w c eq with mapCell c
... | taken _ = case eq of λ ()
... | full m with just-injective eq
...   | refl = refl
put-entries : ∀ l m c {c′} → CM.putMap l m c ≡ just c′ → entries c′ ≡ entries c
put-entries l m c eq with mapCell c
... | full _ = case eq of λ ()
... | taken w with owner l ≟ w
...   | no _ = case eq of λ ()
...   | yes _ with just-injective eq
...     | refl = refl

select-retains : ∀ w h l decision s →
  Retains s (Cleanup.selectCleanup w h l decision s)
select-retains w h l Cleanup.terminateAndPurge s =
  reframe _ _ _ (λ e → put-preserves-present (handlerEntry h) e (terminated nothing) (entries (cm s))) (λ _ p → p)
select-retains w h l Cleanup.purgeOnly s = reframe _ _ _ (λ _ p → p) (λ _ p → p)
select-retains w h l (Cleanup.waitBeforePurge st) s = reframe _ _ _ (λ _ p → p) (λ _ p → p)

finish-present : ∀ e captured heap q → Present q heap → Present q (Cleanup.finishEntry e captured heap)
finish-present e (terminated _) heap q present = present
finish-present e reservedOutbound heap q present = put-preserves-present e q (terminated nothing) heap present
finish-present e (unnegotiated _ _ _) heap q present = put-preserves-present e q (terminated nothing) heap present
finish-present e (outboundUni _ _ _) heap q present = put-preserves-present e q (terminated nothing) heap present
finish-present e (outboundDup _ _ _ _) heap q present = put-preserves-present e q (terminated nothing) heap present
finish-present e (outboundIdle _ _ _ _) heap q present = put-preserves-present e q (terminated nothing) heap present
finish-present e (inboundIdle _ _ _ _) heap q present = put-preserves-present e q (terminated nothing) heap present
finish-present e (inboundActive _ _ _ _) heap q present = put-preserves-present e q (terminated nothing) heap present
finish-present e (duplexActive _ _ _) heap q present = put-preserves-present e q (terminated nothing) heap present
finish-present e (terminating _ _ _) heap q present = put-preserves-present e q (terminated nothing) heap present

worker-retains : ∀ action w h p s {s′} → Cleanup.stepWorker w h p action s ≡ just s′ →
  Retains s s′
worker-retains Cleanup.takeCleanupMap w h (cleanupSelect l) s ()
worker-retains Cleanup.takeCleanupMap w h (cleanupClose l m tail) s ()
worker-retains Cleanup.takeCleanupMap w h (cleanupPublish l m tail) s ()
worker-retains Cleanup.takeCleanupMap w h (cleanupRestore l err) s ()
worker-retains Cleanup.takeCleanupMap w h (cleanupWaiting st) s ()
worker-retains Cleanup.takeCleanupMap w h (cleanupFinalize st outcome) s ()
worker-retains Cleanup.takeCleanupMap w h (cleanupCount outcome) s ()
worker-retains Cleanup.takeCleanupMap w h (cleanupDone outcome) s ()
worker-retains Cleanup.takeCleanupMap w h cleanupAcquire s eq with CM.takeMap w (cm s) in takenEq
... | nothing = case eq of λ ()
... | just (l , c′) = subst (Retains s) (just-injective eq) (reframe _ _ _ (λ e p → subst (Present e) (sym (take-entries w (cm s) takenEq)) p) (λ _ p → p))
worker-retains Cleanup.selectCleanupEntry w h cleanupAcquire s ()
worker-retains Cleanup.selectCleanupEntry w h (cleanupClose l m tail) s ()
worker-retains Cleanup.selectCleanupEntry w h (cleanupPublish l m tail) s ()
worker-retains Cleanup.selectCleanupEntry w h (cleanupRestore l err) s ()
worker-retains Cleanup.selectCleanupEntry w h (cleanupWaiting st) s ()
worker-retains Cleanup.selectCleanupEntry w h (cleanupFinalize st outcome) s ()
worker-retains Cleanup.selectCleanupEntry w h (cleanupCount outcome) s ()
worker-retains Cleanup.selectCleanupEntry w h (cleanupDone outcome) s ()
worker-retains Cleanup.selectCleanupEntry w h (cleanupSelect l) s eq with mapCell (cm s)
... | full _ = case eq of λ ()
... | taken owner with owner ≟ w
...   | no _ = case eq of λ ()
...   | yes _ with lookup (handlerEntry h) (entries (cm s)) in found
...     | nothing = case eq of λ ()
...     | just st = subst (Retains s) (just-injective eq) (select-retains w h l (Cleanup.decideCleanup st) s)
worker-retains Cleanup.closeHandlerSocket w h cleanupAcquire s ()
worker-retains Cleanup.closeHandlerSocket w h (cleanupSelect l) s ()
worker-retains Cleanup.closeHandlerSocket w h (cleanupPublish l m tail) s ()
worker-retains Cleanup.closeHandlerSocket w h (cleanupRestore l err) s ()
worker-retains Cleanup.closeHandlerSocket w h (cleanupWaiting st) s ()
worker-retains Cleanup.closeHandlerSocket w h (cleanupFinalize st outcome) s ()
worker-retains Cleanup.closeHandlerSocket w h (cleanupCount outcome) s ()
worker-retains Cleanup.closeHandlerSocket w h (cleanupDone outcome) s ()
worker-retains Cleanup.closeHandlerSocket w h (cleanupClose l m tail) s eq = subst (Retains s) (just-injective eq) (reframe _ _ _ (λ _ p → p) (λ sock → put-preserves-present (handlerSocket h) sock closed (sockets s)))
worker-retains (Cleanup.failSocketClose error) w h cleanupAcquire s ()
worker-retains (Cleanup.failSocketClose error) w h (cleanupSelect l) s ()
worker-retains (Cleanup.failSocketClose error) w h (cleanupPublish l m tail) s ()
worker-retains (Cleanup.failSocketClose error) w h (cleanupRestore l err) s ()
worker-retains (Cleanup.failSocketClose error) w h (cleanupWaiting st) s ()
worker-retains (Cleanup.failSocketClose error) w h (cleanupFinalize st outcome) s ()
worker-retains (Cleanup.failSocketClose error) w h (cleanupCount outcome) s ()
worker-retains (Cleanup.failSocketClose error) w h (cleanupDone outcome) s ()
worker-retains (Cleanup.failSocketClose error) w h (cleanupClose l m tail) s eq = subst (Retains s) (just-injective eq) (reframe _ _ _ (λ _ p → p) (λ sock → put-preserves-present (handlerSocket h) sock (closeUncertain error) (sockets s)))
worker-retains Cleanup.publishCleanupMap w h cleanupAcquire s ()
worker-retains Cleanup.publishCleanupMap w h (cleanupSelect l) s ()
worker-retains Cleanup.publishCleanupMap w h (cleanupClose l m tail) s ()
worker-retains Cleanup.publishCleanupMap w h (cleanupRestore l err) s ()
worker-retains Cleanup.publishCleanupMap w h (cleanupWaiting st) s ()
worker-retains Cleanup.publishCleanupMap w h (cleanupFinalize st outcome) s ()
worker-retains Cleanup.publishCleanupMap w h (cleanupCount outcome) s ()
worker-retains Cleanup.publishCleanupMap w h (cleanupDone outcome) s ()
worker-retains Cleanup.publishCleanupMap w h (cleanupPublish l m tail) s eq with CM.putMap l m (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst (Retains s) (just-injective eq) (reframe _ _ _ (λ e p → subst (Present e) (sym (put-entries l m (cm s) putEq)) p) (λ _ p → p))
worker-retains Cleanup.restoreCleanupMap w h cleanupAcquire s ()
worker-retains Cleanup.restoreCleanupMap w h (cleanupSelect l) s ()
worker-retains Cleanup.restoreCleanupMap w h (cleanupClose l m tail) s ()
worker-retains Cleanup.restoreCleanupMap w h (cleanupPublish l m tail) s ()
worker-retains Cleanup.restoreCleanupMap w h (cleanupWaiting st) s ()
worker-retains Cleanup.restoreCleanupMap w h (cleanupFinalize st outcome) s ()
worker-retains Cleanup.restoreCleanupMap w h (cleanupCount outcome) s ()
worker-retains Cleanup.restoreCleanupMap w h (cleanupDone outcome) s ()
worker-retains Cleanup.restoreCleanupMap w h (cleanupRestore l err) s eq with CM.putMap l (savedMap l) (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst (Retains s) (just-injective eq) (reframe _ _ _ (λ e p → subst (Present e) (sym (put-entries l (savedMap l) (cm s) putEq)) p) (λ _ p → p))
worker-retains Cleanup.timeWaitElapsed w h cleanupAcquire s ()
worker-retains Cleanup.timeWaitElapsed w h (cleanupSelect l) s ()
worker-retains Cleanup.timeWaitElapsed w h (cleanupClose l m tail) s ()
worker-retains Cleanup.timeWaitElapsed w h (cleanupPublish l m tail) s ()
worker-retains Cleanup.timeWaitElapsed w h (cleanupRestore l err) s ()
worker-retains Cleanup.timeWaitElapsed w h (cleanupFinalize st outcome) s ()
worker-retains Cleanup.timeWaitElapsed w h (cleanupCount outcome) s ()
worker-retains Cleanup.timeWaitElapsed w h (cleanupDone outcome) s ()
worker-retains Cleanup.timeWaitElapsed w h (cleanupWaiting st) s eq = subst (Retains s) (just-injective eq) (reframe _ _ _ (λ _ p → p) (λ _ p → p))
worker-retains (Cleanup.interruptTimeWait error) w h cleanupAcquire s ()
worker-retains (Cleanup.interruptTimeWait error) w h (cleanupSelect l) s ()
worker-retains (Cleanup.interruptTimeWait error) w h (cleanupClose l m tail) s ()
worker-retains (Cleanup.interruptTimeWait error) w h (cleanupPublish l m tail) s ()
worker-retains (Cleanup.interruptTimeWait error) w h (cleanupRestore l err) s ()
worker-retains (Cleanup.interruptTimeWait error) w h (cleanupFinalize st outcome) s ()
worker-retains (Cleanup.interruptTimeWait error) w h (cleanupCount outcome) s ()
worker-retains (Cleanup.interruptTimeWait error) w h (cleanupDone outcome) s ()
worker-retains (Cleanup.interruptTimeWait error) w h (cleanupWaiting st) s eq = subst (Retains s) (just-injective eq) (reframe _ _ _ (λ _ p → p) (λ _ p → p))
worker-retains Cleanup.finishTimeWait w h cleanupAcquire s ()
worker-retains Cleanup.finishTimeWait w h (cleanupSelect l) s ()
worker-retains Cleanup.finishTimeWait w h (cleanupClose l m tail) s ()
worker-retains Cleanup.finishTimeWait w h (cleanupPublish l m tail) s ()
worker-retains Cleanup.finishTimeWait w h (cleanupRestore l err) s ()
worker-retains Cleanup.finishTimeWait w h (cleanupWaiting st) s ()
worker-retains Cleanup.finishTimeWait w h (cleanupCount outcome) s ()
worker-retains Cleanup.finishTimeWait w h (cleanupDone outcome) s ()
worker-retains Cleanup.finishTimeWait w h (cleanupFinalize st outcome) s eq with mapCell (cm s)
... | taken _ = case eq of λ ()
... | full m with lookup (handlerEntry h) (entries (cm s)) in found
...   | nothing = case eq of λ ()
...   | just _ = subst (Retains s) (just-injective eq)
  (reframe _ _ _ (finish-present (handlerEntry h) st (entries (cm s))) (λ _ p → p))
worker-retains Cleanup.readCleanupCounters w h cleanupAcquire s ()
worker-retains Cleanup.readCleanupCounters w h (cleanupSelect l) s ()
worker-retains Cleanup.readCleanupCounters w h (cleanupClose l m tail) s ()
worker-retains Cleanup.readCleanupCounters w h (cleanupPublish l m tail) s ()
worker-retains Cleanup.readCleanupCounters w h (cleanupRestore l err) s ()
worker-retains Cleanup.readCleanupCounters w h (cleanupWaiting st) s ()
worker-retains Cleanup.readCleanupCounters w h (cleanupFinalize st outcome) s ()
worker-retains Cleanup.readCleanupCounters w h (cleanupDone outcome) s ()
worker-retains Cleanup.readCleanupCounters w h (cleanupCount outcome) s eq with mapCell (cm s)
... | taken _ = case eq of λ ()
... | full m with countIncoming (entries (cm s)) m
...   | nothing = case eq of λ ()
...   | just _ = subst (Retains s) (just-injective eq) (reframe _ _ _ (λ _ p → p) (λ _ p → p))

-- Lift every cleanup worker rule through lookup and the actual dispatcher.
cleanup-retains : ∀ w a s {s′} → Cleanup.stepCleanup w a s ≡ just s′ → Retains s s′
cleanup-retains w a s eq with lookup w (handlers s) | lookup w (cleanups s)
... | nothing | _ = case eq of λ ()
... | just _ | nothing = case eq of λ ()
... | just h | just pc = worker-retains a w h pc s eq

step-retains : ∀ w a c {c′} → advance (cleanupStep w a) c ≡ just c′ → Retains (world c) (world c′)
step-retains w a c eq with Cleanup.stepCleanup w a (world c) in stepped
... | nothing = case eq of λ ()
... | just s′ with just-injective eq
...   | refl = cleanup-retains w a (world c) stepped
