{-# OPTIONS --guardedness #-}

-- Cleanup retains original references even when socket and entry values change.
module ConnectionManagement.Properties.HandlerCleanup where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.State
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.Entries using (Present; put-preserves-present)
open import ConnectionManagement.Properties.HandlerReferences hiding (exec-preserves)
open import ConnectionManagement.Properties.HandlerBoundaries using (publication-preserves; exit-preserves)
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.CM as CM

-- The three fields cleanup may update; presence, not the old resource value,
-- is the invariant. Handler and negotiated-result stores remain unchanged.
reframe : ∀ {q mid s ig} c′ ss pcs →
  (∀ e → Present e (entries (cm s)) → Present e (entries c′)) →
  (∀ sock → Present sock (sockets s) → Present sock ss) →
  Chain q mid s ig → Chain q mid (record s { cm = c′; sockets = ss; cleanups = pcs }) ig
reframe c′ ss pcs ep sp chain = record
  { originalHandler = originalHandler chain; publishedHandle = publishedHandle chain
  ; negotiatedFlow = negotiatedFlow chain; handleValue = handleValue chain; muxValue = muxValue chain
  ; handlerFound = handlerFound chain; promiseFound = promiseFound chain
  ; handleFound = handleFound chain; handleMux = handleMux chain; muxFound = muxFound chain
  ; keyMatches = keyMatches chain
  ; entryPresent = ep _ (entryPresent chain); socketPresent = sp _ (socketPresent chain) }

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

select-preserves : ∀ w h l decision s {q mid ig} →
  Chain q mid s ig → Chain q mid (Cleanup.selectCleanup w h l decision s) ig
select-preserves w h l Cleanup.terminateAndPurge s chain =
  reframe _ _ _ (λ e → put-preserves-present (handlerEntry h) e (terminated nothing) (entries (cm s))) (λ _ p → p) chain
select-preserves w h l Cleanup.purgeOnly s chain = reframe _ _ _ (λ _ p → p) (λ _ p → p) chain
select-preserves w h l (Cleanup.waitBeforePurge st) s chain = reframe _ _ _ (λ _ p → p) (λ _ p → p) chain

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

cleanup-preserves : ∀ {q mid ig} action w h p s {s′} → Cleanup.stepWorker w h p action s ≡ just s′ →
  Chain q mid s ig → Chain q mid s′ ig
cleanup-preserves {q} {mid} {ig} Cleanup.takeCleanupMap w h (cleanupSelect l) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.takeCleanupMap w h (cleanupClose l m tail) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.takeCleanupMap w h (cleanupPublish l m tail) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.takeCleanupMap w h (cleanupRestore l err) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.takeCleanupMap w h (cleanupWaiting st) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.takeCleanupMap w h (cleanupFinalize st outcome) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.takeCleanupMap w h (cleanupCount outcome) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.takeCleanupMap w h (cleanupDone outcome) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.takeCleanupMap w h cleanupAcquire s eq chain with CM.takeMap w (cm s) in takenEq
... | nothing = case eq of λ ()
... | just (l , c′) = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ _ _ (λ e p → subst (Present e) (sym (take-entries w (cm s) takenEq)) p) (λ _ p → p) chain)
cleanup-preserves {q} {mid} {ig} Cleanup.selectCleanupEntry w h cleanupAcquire s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.selectCleanupEntry w h (cleanupClose l m tail) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.selectCleanupEntry w h (cleanupPublish l m tail) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.selectCleanupEntry w h (cleanupRestore l err) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.selectCleanupEntry w h (cleanupWaiting st) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.selectCleanupEntry w h (cleanupFinalize st outcome) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.selectCleanupEntry w h (cleanupCount outcome) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.selectCleanupEntry w h (cleanupDone outcome) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.selectCleanupEntry w h (cleanupSelect l) s eq chain with mapCell (cm s)
... | full _ = case eq of λ ()
... | taken owner with owner ≟ w
...   | no _ = case eq of λ ()
...   | yes _ with lookup (handlerEntry h) (entries (cm s)) in found
...     | nothing = case eq of λ ()
...     | just st = subst (λ s → Chain q mid s ig) (just-injective eq) (select-preserves w h l (Cleanup.decideCleanup st) s chain)
cleanup-preserves {q} {mid} {ig} Cleanup.closeHandlerSocket w h cleanupAcquire s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.closeHandlerSocket w h (cleanupSelect l) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.closeHandlerSocket w h (cleanupPublish l m tail) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.closeHandlerSocket w h (cleanupRestore l err) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.closeHandlerSocket w h (cleanupWaiting st) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.closeHandlerSocket w h (cleanupFinalize st outcome) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.closeHandlerSocket w h (cleanupCount outcome) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.closeHandlerSocket w h (cleanupDone outcome) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.closeHandlerSocket w h (cleanupClose l m tail) s eq chain = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ _ _ (λ _ p → p) (λ sock → put-preserves-present (handlerSocket h) sock closed (sockets s)) chain)
cleanup-preserves {q} {mid} {ig} (Cleanup.failSocketClose error) w h cleanupAcquire s () chain
cleanup-preserves {q} {mid} {ig} (Cleanup.failSocketClose error) w h (cleanupSelect l) s () chain
cleanup-preserves {q} {mid} {ig} (Cleanup.failSocketClose error) w h (cleanupPublish l m tail) s () chain
cleanup-preserves {q} {mid} {ig} (Cleanup.failSocketClose error) w h (cleanupRestore l err) s () chain
cleanup-preserves {q} {mid} {ig} (Cleanup.failSocketClose error) w h (cleanupWaiting st) s () chain
cleanup-preserves {q} {mid} {ig} (Cleanup.failSocketClose error) w h (cleanupFinalize st outcome) s () chain
cleanup-preserves {q} {mid} {ig} (Cleanup.failSocketClose error) w h (cleanupCount outcome) s () chain
cleanup-preserves {q} {mid} {ig} (Cleanup.failSocketClose error) w h (cleanupDone outcome) s () chain
cleanup-preserves {q} {mid} {ig} (Cleanup.failSocketClose error) w h (cleanupClose l m tail) s eq chain = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ _ _ (λ _ p → p) (λ sock → put-preserves-present (handlerSocket h) sock (closeUncertain error) (sockets s)) chain)
cleanup-preserves {q} {mid} {ig} Cleanup.publishCleanupMap w h cleanupAcquire s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.publishCleanupMap w h (cleanupSelect l) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.publishCleanupMap w h (cleanupClose l m tail) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.publishCleanupMap w h (cleanupRestore l err) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.publishCleanupMap w h (cleanupWaiting st) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.publishCleanupMap w h (cleanupFinalize st outcome) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.publishCleanupMap w h (cleanupCount outcome) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.publishCleanupMap w h (cleanupDone outcome) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.publishCleanupMap w h (cleanupPublish l m tail) s eq chain with CM.putMap l m (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ _ _ (λ e p → subst (Present e) (sym (put-entries l m (cm s) putEq)) p) (λ _ p → p) chain)
cleanup-preserves {q} {mid} {ig} Cleanup.restoreCleanupMap w h cleanupAcquire s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.restoreCleanupMap w h (cleanupSelect l) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.restoreCleanupMap w h (cleanupClose l m tail) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.restoreCleanupMap w h (cleanupPublish l m tail) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.restoreCleanupMap w h (cleanupWaiting st) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.restoreCleanupMap w h (cleanupFinalize st outcome) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.restoreCleanupMap w h (cleanupCount outcome) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.restoreCleanupMap w h (cleanupDone outcome) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.restoreCleanupMap w h (cleanupRestore l err) s eq chain with CM.putMap l (savedMap l) (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ _ _ (λ e p → subst (Present e) (sym (put-entries l (savedMap l) (cm s) putEq)) p) (λ _ p → p) chain)
cleanup-preserves {q} {mid} {ig} Cleanup.timeWaitElapsed w h cleanupAcquire s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.timeWaitElapsed w h (cleanupSelect l) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.timeWaitElapsed w h (cleanupClose l m tail) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.timeWaitElapsed w h (cleanupPublish l m tail) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.timeWaitElapsed w h (cleanupRestore l err) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.timeWaitElapsed w h (cleanupFinalize st outcome) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.timeWaitElapsed w h (cleanupCount outcome) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.timeWaitElapsed w h (cleanupDone outcome) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.timeWaitElapsed w h (cleanupWaiting st) s eq chain = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ _ _ (λ _ p → p) (λ _ p → p) chain)
cleanup-preserves {q} {mid} {ig} (Cleanup.interruptTimeWait error) w h cleanupAcquire s () chain
cleanup-preserves {q} {mid} {ig} (Cleanup.interruptTimeWait error) w h (cleanupSelect l) s () chain
cleanup-preserves {q} {mid} {ig} (Cleanup.interruptTimeWait error) w h (cleanupClose l m tail) s () chain
cleanup-preserves {q} {mid} {ig} (Cleanup.interruptTimeWait error) w h (cleanupPublish l m tail) s () chain
cleanup-preserves {q} {mid} {ig} (Cleanup.interruptTimeWait error) w h (cleanupRestore l err) s () chain
cleanup-preserves {q} {mid} {ig} (Cleanup.interruptTimeWait error) w h (cleanupFinalize st outcome) s () chain
cleanup-preserves {q} {mid} {ig} (Cleanup.interruptTimeWait error) w h (cleanupCount outcome) s () chain
cleanup-preserves {q} {mid} {ig} (Cleanup.interruptTimeWait error) w h (cleanupDone outcome) s () chain
cleanup-preserves {q} {mid} {ig} (Cleanup.interruptTimeWait error) w h (cleanupWaiting st) s eq chain = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ _ _ (λ _ p → p) (λ _ p → p) chain)
cleanup-preserves {q} {mid} {ig} Cleanup.finishTimeWait w h cleanupAcquire s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.finishTimeWait w h (cleanupSelect l) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.finishTimeWait w h (cleanupClose l m tail) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.finishTimeWait w h (cleanupPublish l m tail) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.finishTimeWait w h (cleanupRestore l err) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.finishTimeWait w h (cleanupWaiting st) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.finishTimeWait w h (cleanupCount outcome) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.finishTimeWait w h (cleanupDone outcome) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.finishTimeWait w h (cleanupFinalize st outcome) s eq chain with mapCell (cm s)
... | taken _ = case eq of λ ()
... | full m with lookup (handlerEntry h) (entries (cm s)) in found
...   | nothing = case eq of λ ()
...   | just _ = subst (λ s → Chain q mid s ig) (just-injective eq)
  (reframe _ _ _ (finish-present (handlerEntry h) st (entries (cm s))) (λ _ p → p) chain)
cleanup-preserves {q} {mid} {ig} Cleanup.readCleanupCounters w h cleanupAcquire s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.readCleanupCounters w h (cleanupSelect l) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.readCleanupCounters w h (cleanupClose l m tail) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.readCleanupCounters w h (cleanupPublish l m tail) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.readCleanupCounters w h (cleanupRestore l err) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.readCleanupCounters w h (cleanupWaiting st) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.readCleanupCounters w h (cleanupFinalize st outcome) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.readCleanupCounters w h (cleanupDone outcome) s () chain
cleanup-preserves {q} {mid} {ig} Cleanup.readCleanupCounters w h (cleanupCount outcome) s eq chain with mapCell (cm s)
... | taken _ = case eq of λ ()
... | full m with countIncoming (entries (cm s)) m
...   | nothing = case eq of λ ()
...   | just _ = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ _ _ (λ _ p → p) (λ _ p → p) chain)

-- Lift from a selected cleanup worker to the actual dispatcher.
step-preserves : ∀ w a c {c′} → advance (cleanupStep w a) c ≡ just c′ →
  ∀ q → TrackedChain q c → TrackedChain q c′
step-preserves w a c eq q (f , found , chain) with Cleanup.stepCleanup w a (world c) in stepped
... | nothing = case eq of λ ()
... | just s with just-injective eq
...   | refl = f , found , worker-chain w a (world c) stepped chain
  where
  worker-chain : ∀ w a s {s′ q mid ig} → Cleanup.stepCleanup w a s ≡ just s′ →
    Chain q mid s ig → Chain q mid s′ ig
  worker-chain w a s eq chain with lookup w (handlers s) | lookup w (cleanups s)
  ... | nothing | _ = case eq of λ ()
  ... | just _ | nothing = case eq of λ ()
  ... | just h | just p = cleanup-preserves a w h p s eq chain

-- Includes all cleanup outcomes, with arbitrary actors at every step.
data CleanupActions : List Action → Set where
  empty : CleanupActions []
  lifecycle : ∀ {w a as} → CleanupActions as → CleanupActions (handlerStep w a ∷ as)
  publication : ∀ {w result outcome as} → CleanupActions as → CleanupActions (handlerPublication w result outcome ∷ as)
  exit : ∀ {w as} → CleanupActions as → CleanupActions (handlerExit w ∷ as)
  cleanup : ∀ {w a as} → CleanupActions as → CleanupActions (cleanupStep w a ∷ as)

exec-preserves : ∀ {c as c′} → CleanupActions as → Executes c as c′ →
  ∀ q → TrackedChain q c → TrackedChain q c′
exec-preserves empty done q chain = chain
exec-preserves (lifecycle {w} {a} only) (next {c = c} eq rest) q chain =
  exec-preserves only rest q (handler-step-preserves w a c eq q chain)
exec-preserves (publication {w} {result} {outcome} only) (next {c = c} eq rest) q chain =
  exec-preserves only rest q (publication-preserves w result outcome c eq q chain)
exec-preserves (exit {w} only) (next {c = c} eq rest) q chain =
  exec-preserves only rest q (exit-preserves w c eq q chain)
exec-preserves (cleanup {w} {a} only) (next {c = c} eq rest) q chain =
  exec-preserves only rest q (step-preserves w a c eq q chain)
