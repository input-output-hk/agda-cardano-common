{-# OPTIONS --guardedness #-}

-- Promise allocation is monotone: later source actions never remove a cell.
-- Each component follows its successful primitive result; no supply bounds or
-- ownership premise is needed. The case structure mirrors the supply proofs.
open import ConnectionManagement.Domain using
  (PromiseId; ident; inbound; outbound; DecEq-Id; DecEq-PeerAddr; DecEq-ConnectionKey; DecEq-LocalKey)
module ConnectionManagement.Properties.LivePromiseCore (observedPromise : PromiseId) where

open import ConnectionManagement.State using
  (State; promises; admissionWorker; acquireMap; count; prepare; selectEntry; forkHandler; publish;
   reject; hardLimitReached; forbidden; bodyFailed; forkFailed; closeSocket; finished; countPublished;
   awaitHandshake; commitHandshake; countHandshake; notifyInbound; returnHandshake;
   completedHandshake; impossibleHandshake; cm; savedMap; countIncoming; entries; hardLimit;
   nextPromise; handlers; admissions; key; child; mapCell; full; taken; insertConnection; owner;
   handlerEntry; handlerPromise; cleanups; cleanupAcquire; cleanupSelect; cleanupClose;
   cleanupPublish; cleanupRestore; cleanupWaiting; cleanupFinalize; cleanupCount; cleanupDone;
   handshakeResults; negotiated; query; handlerError; handshakeQuery; handshakeError; request;
   inboundInfo; sockets; unnegotiated; outboundUni; outboundDup; outboundIdle; inboundIdle;
   inboundActive; duplexActive; terminating; terminated; reservedOutbound; responderMode;
   noResponderMode; nextEntry; lookupConnection; connected; disconnected; newConnection; newConnectionInfo)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (there)

Allocated : State → Set
Allocated s = observedPromise ∈ promises s

-- Admission preserves each already allocated promise.
-- Admission allocation prepends a cell; every other admission action keeps it.
module AdmissionPart where
 open import Data.Nat using (suc; _≤?_)
 open import Data.List using (_∷_)
 open import Data.Maybe using (just; nothing)
 open import Data.Maybe.Properties using (just-injective)
 open import Data.Product using (_,_)
 open import Relation.Nullary using (yes; no)
 open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
 open import Function using (case_of_)
 open import ConnectionManagement.Store using (lookup)
 import ConnectionManagement.Rules.Server as Server
 import ConnectionManagement.Rules.CM as CM

 -- Follow every enabled admission-prefix action, including allocation.
 admission-preserves : ∀ action w a s {s′} →
   Server.stepWorker w a action s ≡ just s′ → Allocated s → Allocated s′
 admission-preserves Server.take w (admissionWorker r (count l)) s () allocated
 admission-preserves Server.take w (admissionWorker r (prepare l)) s () allocated
 admission-preserves Server.take w (admissionWorker r (selectEntry l p)) s () allocated
 admission-preserves Server.take w (admissionWorker r (forkHandler l p e)) s () allocated
 admission-preserves Server.take w (admissionWorker r (publish l p e)) s () allocated
 admission-preserves Server.take w (admissionWorker r (reject l hardLimitReached)) s () allocated
 admission-preserves Server.take w (admissionWorker r (reject l forbidden)) s () allocated
 admission-preserves Server.take w (admissionWorker r (reject l bodyFailed)) s () allocated
 admission-preserves Server.take w (admissionWorker r (reject l forkFailed)) s () allocated
 admission-preserves Server.take w (admissionWorker r (closeSocket reason)) s () allocated
 admission-preserves Server.take w (admissionWorker r (finished reason)) s () allocated
 admission-preserves Server.take w (admissionWorker r (countPublished p e)) s () allocated
 admission-preserves Server.take w (admissionWorker r (awaitHandshake p e)) s () allocated
 admission-preserves Server.take w (admissionWorker r (commitHandshake e result)) s () allocated
 admission-preserves Server.take w (admissionWorker r (countHandshake result)) s () allocated
 admission-preserves Server.take w (admissionWorker r (notifyInbound info)) s () allocated
 admission-preserves Server.take w (admissionWorker r (returnHandshake result)) s () allocated
 admission-preserves Server.take w (admissionWorker r (completedHandshake result)) s () allocated
 admission-preserves Server.take w (admissionWorker r impossibleHandshake) s () allocated
 admission-preserves Server.take w (admissionWorker r acquireMap) s eq allocated with CM.takeMap w (cm s) in takenEq
 ... | nothing = case eq of λ ()
 ... | just (l , c′) = subst Allocated (just-injective eq) allocated
 admission-preserves Server.countLimit w (admissionWorker r acquireMap) s () allocated
 admission-preserves Server.countLimit w (admissionWorker r (prepare l)) s () allocated
 admission-preserves Server.countLimit w (admissionWorker r (selectEntry l p)) s () allocated
 admission-preserves Server.countLimit w (admissionWorker r (forkHandler l p e)) s () allocated
 admission-preserves Server.countLimit w (admissionWorker r (publish l p e)) s () allocated
 admission-preserves Server.countLimit w (admissionWorker r (reject l hardLimitReached)) s () allocated
 admission-preserves Server.countLimit w (admissionWorker r (reject l forbidden)) s () allocated
 admission-preserves Server.countLimit w (admissionWorker r (reject l bodyFailed)) s () allocated
 admission-preserves Server.countLimit w (admissionWorker r (reject l forkFailed)) s () allocated
 admission-preserves Server.countLimit w (admissionWorker r (closeSocket reason)) s () allocated
 admission-preserves Server.countLimit w (admissionWorker r (finished reason)) s () allocated
 admission-preserves Server.countLimit w (admissionWorker r (countPublished p e)) s () allocated
 admission-preserves Server.countLimit w (admissionWorker r (awaitHandshake p e)) s () allocated
 admission-preserves Server.countLimit w (admissionWorker r (commitHandshake e result)) s () allocated
 admission-preserves Server.countLimit w (admissionWorker r (countHandshake result)) s () allocated
 admission-preserves Server.countLimit w (admissionWorker r (notifyInbound info)) s () allocated
 admission-preserves Server.countLimit w (admissionWorker r (returnHandshake result)) s () allocated
 admission-preserves Server.countLimit w (admissionWorker r (completedHandshake result)) s () allocated
 admission-preserves Server.countLimit w (admissionWorker r impossibleHandshake) s () allocated
 admission-preserves Server.countLimit w (admissionWorker r (count l)) s eq allocated with countIncoming (entries (cm s)) (savedMap l)
 ... | nothing = case eq of λ ()
 ... | just n with suc n ≤? hardLimit r
 ...   | yes _ = subst Allocated (just-injective eq) allocated
 ...   | no _ = subst Allocated (just-injective eq) allocated
 admission-preserves Server.allocatePromise w (admissionWorker r acquireMap) s () allocated
 admission-preserves Server.allocatePromise w (admissionWorker r (count l)) s () allocated
 admission-preserves Server.allocatePromise w (admissionWorker r (selectEntry l p)) s () allocated
 admission-preserves Server.allocatePromise w (admissionWorker r (forkHandler l p e)) s () allocated
 admission-preserves Server.allocatePromise w (admissionWorker r (publish l p e)) s () allocated
 admission-preserves Server.allocatePromise w (admissionWorker r (reject l hardLimitReached)) s () allocated
 admission-preserves Server.allocatePromise w (admissionWorker r (reject l forbidden)) s () allocated
 admission-preserves Server.allocatePromise w (admissionWorker r (reject l bodyFailed)) s () allocated
 admission-preserves Server.allocatePromise w (admissionWorker r (reject l forkFailed)) s () allocated
 admission-preserves Server.allocatePromise w (admissionWorker r (closeSocket reason)) s () allocated
 admission-preserves Server.allocatePromise w (admissionWorker r (finished reason)) s () allocated
 admission-preserves Server.allocatePromise w (admissionWorker r (countPublished p e)) s () allocated
 admission-preserves Server.allocatePromise w (admissionWorker r (awaitHandshake p e)) s () allocated
 admission-preserves Server.allocatePromise w (admissionWorker r (commitHandshake e result)) s () allocated
 admission-preserves Server.allocatePromise w (admissionWorker r (countHandshake result)) s () allocated
 admission-preserves Server.allocatePromise w (admissionWorker r (notifyInbound info)) s () allocated
 admission-preserves Server.allocatePromise w (admissionWorker r (returnHandshake result)) s () allocated
 admission-preserves Server.allocatePromise w (admissionWorker r (completedHandshake result)) s () allocated
 admission-preserves Server.allocatePromise w (admissionWorker r impossibleHandshake) s () allocated
 admission-preserves Server.allocatePromise w (admissionWorker r (prepare l)) s eq allocated = subst Allocated (just-injective eq)
   (there allocated)
 admission-preserves Server.chooseEntry w (admissionWorker r acquireMap) s () allocated
 admission-preserves Server.chooseEntry w (admissionWorker r (count l)) s () allocated
 admission-preserves Server.chooseEntry w (admissionWorker r (prepare l)) s () allocated
 admission-preserves Server.chooseEntry w (admissionWorker r (forkHandler l p e)) s () allocated
 admission-preserves Server.chooseEntry w (admissionWorker r (publish l p e)) s () allocated
 admission-preserves Server.chooseEntry w (admissionWorker r (reject l hardLimitReached)) s () allocated
 admission-preserves Server.chooseEntry w (admissionWorker r (reject l forbidden)) s () allocated
 admission-preserves Server.chooseEntry w (admissionWorker r (reject l bodyFailed)) s () allocated
 admission-preserves Server.chooseEntry w (admissionWorker r (reject l forkFailed)) s () allocated
 admission-preserves Server.chooseEntry w (admissionWorker r (closeSocket reason)) s () allocated
 admission-preserves Server.chooseEntry w (admissionWorker r (finished reason)) s () allocated
 admission-preserves Server.chooseEntry w (admissionWorker r (countPublished p e)) s () allocated
 admission-preserves Server.chooseEntry w (admissionWorker r (awaitHandshake p e)) s () allocated
 admission-preserves Server.chooseEntry w (admissionWorker r (commitHandshake e result)) s () allocated
 admission-preserves Server.chooseEntry w (admissionWorker r (countHandshake result)) s () allocated
 admission-preserves Server.chooseEntry w (admissionWorker r (notifyInbound info)) s () allocated
 admission-preserves Server.chooseEntry w (admissionWorker r (returnHandshake result)) s () allocated
 admission-preserves Server.chooseEntry w (admissionWorker r (completedHandshake result)) s () allocated
 admission-preserves Server.chooseEntry w (admissionWorker r impossibleHandshake) s () allocated
 admission-preserves Server.chooseEntry w (admissionWorker r (selectEntry l p)) s eq allocated with CM.selectInbound l r (cm s) in selected
 ... | nothing = case eq of λ ()
 ... | just CM.denied = subst Allocated (just-injective eq) allocated
 ... | just (CM.selected e c′) = subst Allocated (just-injective eq) allocated
 admission-preserves Server.fork w (admissionWorker r acquireMap) s () allocated
 admission-preserves Server.fork w (admissionWorker r (count l)) s () allocated
 admission-preserves Server.fork w (admissionWorker r (prepare l)) s () allocated
 admission-preserves Server.fork w (admissionWorker r (selectEntry l p)) s () allocated
 admission-preserves Server.fork w (admissionWorker r (publish l p e)) s () allocated
 admission-preserves Server.fork w (admissionWorker r (reject l hardLimitReached)) s () allocated
 admission-preserves Server.fork w (admissionWorker r (reject l forbidden)) s () allocated
 admission-preserves Server.fork w (admissionWorker r (reject l bodyFailed)) s () allocated
 admission-preserves Server.fork w (admissionWorker r (reject l forkFailed)) s () allocated
 admission-preserves Server.fork w (admissionWorker r (closeSocket reason)) s () allocated
 admission-preserves Server.fork w (admissionWorker r (finished reason)) s () allocated
 admission-preserves Server.fork w (admissionWorker r (countPublished p e)) s () allocated
 admission-preserves Server.fork w (admissionWorker r (awaitHandshake p e)) s () allocated
 admission-preserves Server.fork w (admissionWorker r (commitHandshake e result)) s () allocated
 admission-preserves Server.fork w (admissionWorker r (countHandshake result)) s () allocated
 admission-preserves Server.fork w (admissionWorker r (notifyInbound info)) s () allocated
 admission-preserves Server.fork w (admissionWorker r (returnHandshake result)) s () allocated
 admission-preserves Server.fork w (admissionWorker r (completedHandshake result)) s () allocated
 admission-preserves Server.fork w (admissionWorker r impossibleHandshake) s () allocated
 admission-preserves Server.fork w (admissionWorker r (forkHandler l p e)) s eq allocated with lookup (child r) (handlers s) | lookup (child r) (admissions s)
 ... | nothing | nothing = subst Allocated (just-injective eq) allocated
 ... | just _ | _ = case eq of λ ()
 ... | nothing | just _ = case eq of λ ()
 admission-preserves Server.failFork w (admissionWorker r acquireMap) s () allocated
 admission-preserves Server.failFork w (admissionWorker r (count l)) s () allocated
 admission-preserves Server.failFork w (admissionWorker r (prepare l)) s () allocated
 admission-preserves Server.failFork w (admissionWorker r (selectEntry l p)) s () allocated
 admission-preserves Server.failFork w (admissionWorker r (publish l p e)) s () allocated
 admission-preserves Server.failFork w (admissionWorker r (reject l hardLimitReached)) s () allocated
 admission-preserves Server.failFork w (admissionWorker r (reject l forbidden)) s () allocated
 admission-preserves Server.failFork w (admissionWorker r (reject l bodyFailed)) s () allocated
 admission-preserves Server.failFork w (admissionWorker r (reject l forkFailed)) s () allocated
 admission-preserves Server.failFork w (admissionWorker r (closeSocket reason)) s () allocated
 admission-preserves Server.failFork w (admissionWorker r (finished reason)) s () allocated
 admission-preserves Server.failFork w (admissionWorker r (countPublished p e)) s () allocated
 admission-preserves Server.failFork w (admissionWorker r (awaitHandshake p e)) s () allocated
 admission-preserves Server.failFork w (admissionWorker r (commitHandshake e result)) s () allocated
 admission-preserves Server.failFork w (admissionWorker r (countHandshake result)) s () allocated
 admission-preserves Server.failFork w (admissionWorker r (notifyInbound info)) s () allocated
 admission-preserves Server.failFork w (admissionWorker r (returnHandshake result)) s () allocated
 admission-preserves Server.failFork w (admissionWorker r (completedHandshake result)) s () allocated
 admission-preserves Server.failFork w (admissionWorker r impossibleHandshake) s () allocated
 admission-preserves Server.failFork w (admissionWorker r (forkHandler l p e)) s eq allocated = subst Allocated (just-injective eq) allocated
 admission-preserves Server.readCounters w (admissionWorker r acquireMap) s () allocated
 admission-preserves Server.readCounters w (admissionWorker r (count l)) s () allocated
 admission-preserves Server.readCounters w (admissionWorker r (prepare l)) s () allocated
 admission-preserves Server.readCounters w (admissionWorker r (selectEntry l p)) s () allocated
 admission-preserves Server.readCounters w (admissionWorker r (forkHandler l p e)) s () allocated
 admission-preserves Server.readCounters w (admissionWorker r (publish l p e)) s () allocated
 admission-preserves Server.readCounters w (admissionWorker r (reject l hardLimitReached)) s () allocated
 admission-preserves Server.readCounters w (admissionWorker r (reject l forbidden)) s () allocated
 admission-preserves Server.readCounters w (admissionWorker r (reject l bodyFailed)) s () allocated
 admission-preserves Server.readCounters w (admissionWorker r (reject l forkFailed)) s () allocated
 admission-preserves Server.readCounters w (admissionWorker r (closeSocket reason)) s () allocated
 admission-preserves Server.readCounters w (admissionWorker r (finished reason)) s () allocated
 admission-preserves Server.readCounters w (admissionWorker r (awaitHandshake p e)) s () allocated
 admission-preserves Server.readCounters w (admissionWorker r (commitHandshake e result)) s () allocated
 admission-preserves Server.readCounters w (admissionWorker r (countHandshake result)) s () allocated
 admission-preserves Server.readCounters w (admissionWorker r (notifyInbound info)) s () allocated
 admission-preserves Server.readCounters w (admissionWorker r (returnHandshake result)) s () allocated
 admission-preserves Server.readCounters w (admissionWorker r (completedHandshake result)) s () allocated
 admission-preserves Server.readCounters w (admissionWorker r impossibleHandshake) s () allocated
 admission-preserves Server.readCounters w (admissionWorker r (countPublished p e)) s eq allocated with mapCell (cm s)
 ... | taken _ = case eq of λ ()
 ... | full m with countIncoming (entries (cm s)) m
 ...   | nothing = case eq of λ ()
 ...   | just _ = subst Allocated (just-injective eq) allocated
 admission-preserves Server.close w (admissionWorker r acquireMap) s () allocated
 admission-preserves Server.close w (admissionWorker r (count l)) s () allocated
 admission-preserves Server.close w (admissionWorker r (prepare l)) s () allocated
 admission-preserves Server.close w (admissionWorker r (selectEntry l p)) s () allocated
 admission-preserves Server.close w (admissionWorker r (forkHandler l p e)) s () allocated
 admission-preserves Server.close w (admissionWorker r (publish l p e)) s () allocated
 admission-preserves Server.close w (admissionWorker r (reject l hardLimitReached)) s () allocated
 admission-preserves Server.close w (admissionWorker r (reject l forbidden)) s () allocated
 admission-preserves Server.close w (admissionWorker r (reject l bodyFailed)) s () allocated
 admission-preserves Server.close w (admissionWorker r (reject l forkFailed)) s () allocated
 admission-preserves Server.close w (admissionWorker r (finished reason)) s () allocated
 admission-preserves Server.close w (admissionWorker r (countPublished p e)) s () allocated
 admission-preserves Server.close w (admissionWorker r (awaitHandshake p e)) s () allocated
 admission-preserves Server.close w (admissionWorker r (commitHandshake e result)) s () allocated
 admission-preserves Server.close w (admissionWorker r (countHandshake result)) s () allocated
 admission-preserves Server.close w (admissionWorker r (notifyInbound info)) s () allocated
 admission-preserves Server.close w (admissionWorker r (returnHandshake result)) s () allocated
 admission-preserves Server.close w (admissionWorker r (completedHandshake result)) s () allocated
 admission-preserves Server.close w (admissionWorker r impossibleHandshake) s () allocated
 admission-preserves Server.close w (admissionWorker r (closeSocket reason)) s eq allocated = subst Allocated (just-injective eq) allocated
 admission-preserves Server.putMapBack w (admissionWorker r acquireMap) s () allocated
 admission-preserves Server.putMapBack w (admissionWorker r (count l)) s () allocated
 admission-preserves Server.putMapBack w (admissionWorker r (prepare l)) s () allocated
 admission-preserves Server.putMapBack w (admissionWorker r (selectEntry l p)) s () allocated
 admission-preserves Server.putMapBack w (admissionWorker r (forkHandler l p e)) s () allocated
 admission-preserves Server.putMapBack w (admissionWorker r (reject l forbidden)) s () allocated
 admission-preserves Server.putMapBack w (admissionWorker r (reject l bodyFailed)) s () allocated
 admission-preserves Server.putMapBack w (admissionWorker r (reject l forkFailed)) s () allocated
 admission-preserves Server.putMapBack w (admissionWorker r (closeSocket reason)) s () allocated
 admission-preserves Server.putMapBack w (admissionWorker r (finished reason)) s () allocated
 admission-preserves Server.putMapBack w (admissionWorker r (countPublished p e)) s () allocated
 admission-preserves Server.putMapBack w (admissionWorker r (awaitHandshake p e)) s () allocated
 admission-preserves Server.putMapBack w (admissionWorker r (commitHandshake e result)) s () allocated
 admission-preserves Server.putMapBack w (admissionWorker r (countHandshake result)) s () allocated
 admission-preserves Server.putMapBack w (admissionWorker r (notifyInbound info)) s () allocated
 admission-preserves Server.putMapBack w (admissionWorker r (returnHandshake result)) s () allocated
 admission-preserves Server.putMapBack w (admissionWorker r (completedHandshake result)) s () allocated
 admission-preserves Server.putMapBack w (admissionWorker r impossibleHandshake) s () allocated
 admission-preserves Server.putMapBack w (admissionWorker r (publish l p e)) s eq allocated with CM.putMap l (insertConnection (key r) e (savedMap l)) (cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = subst Allocated (just-injective eq) allocated
 admission-preserves Server.putMapBack w (admissionWorker r (reject l hardLimitReached)) s eq allocated with CM.putMap l (savedMap l) (cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = subst Allocated (just-injective eq) allocated
 admission-preserves Server.restore w (admissionWorker r acquireMap) s () allocated
 admission-preserves Server.restore w (admissionWorker r (count l)) s () allocated
 admission-preserves Server.restore w (admissionWorker r (prepare l)) s () allocated
 admission-preserves Server.restore w (admissionWorker r (selectEntry l p)) s () allocated
 admission-preserves Server.restore w (admissionWorker r (forkHandler l p e)) s () allocated
 admission-preserves Server.restore w (admissionWorker r (publish l p e)) s () allocated
 admission-preserves Server.restore w (admissionWorker r (reject l hardLimitReached)) s () allocated
 admission-preserves Server.restore w (admissionWorker r (closeSocket reason)) s () allocated
 admission-preserves Server.restore w (admissionWorker r (finished reason)) s () allocated
 admission-preserves Server.restore w (admissionWorker r (countPublished p e)) s () allocated
 admission-preserves Server.restore w (admissionWorker r (awaitHandshake p e)) s () allocated
 admission-preserves Server.restore w (admissionWorker r (commitHandshake e result)) s () allocated
 admission-preserves Server.restore w (admissionWorker r (countHandshake result)) s () allocated
 admission-preserves Server.restore w (admissionWorker r (notifyInbound info)) s () allocated
 admission-preserves Server.restore w (admissionWorker r (returnHandshake result)) s () allocated
 admission-preserves Server.restore w (admissionWorker r (completedHandshake result)) s () allocated
 admission-preserves Server.restore w (admissionWorker r impossibleHandshake) s () allocated
 admission-preserves Server.restore w (admissionWorker r (reject l forbidden)) s eq allocated with CM.putMap l (savedMap l) (cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = subst Allocated (just-injective eq) allocated
 admission-preserves Server.restore w (admissionWorker r (reject l bodyFailed)) s eq allocated with CM.putMap l (savedMap l) (cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = subst Allocated (just-injective eq) allocated
 admission-preserves Server.restore w (admissionWorker r (reject l forkFailed)) s eq allocated with CM.putMap l (savedMap l) (cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = subst Allocated (just-injective eq) allocated

 admission-preserves Server.restoreBody w (admissionWorker r (count l)) s eq allocated with CM.putMap l (savedMap l) (cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = subst Allocated (just-injective eq) allocated
 admission-preserves Server.restoreBody w (admissionWorker r (prepare l)) s eq allocated with CM.putMap l (savedMap l) (cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = subst Allocated (just-injective eq) allocated
 admission-preserves Server.restoreBody w (admissionWorker r (selectEntry l p)) s eq allocated with CM.putMap l (savedMap l) (cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = subst Allocated (just-injective eq) allocated
 admission-preserves Server.restoreBody w (admissionWorker r (forkHandler l p e)) s eq allocated with CM.putMap l (savedMap l) (cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = subst Allocated (just-injective eq) allocated
 admission-preserves Server.restoreBody w (admissionWorker r (publish l p e)) s eq allocated with CM.putMap l (savedMap l) (cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = subst Allocated (just-injective eq) allocated
 admission-preserves Server.restoreBody w (admissionWorker r acquireMap) s () allocated
 admission-preserves Server.restoreBody w (admissionWorker r (reject l hardLimitReached)) s () allocated
 admission-preserves Server.restoreBody w (admissionWorker r (closeSocket reason)) s () allocated
 admission-preserves Server.restoreBody w (admissionWorker r (finished reason)) s () allocated
 admission-preserves Server.restoreBody w (admissionWorker r (countPublished p e)) s () allocated
 admission-preserves Server.restoreBody w (admissionWorker r (awaitHandshake p e)) s () allocated
 admission-preserves Server.restoreBody w (admissionWorker r (commitHandshake e result)) s () allocated
 admission-preserves Server.restoreBody w (admissionWorker r (countHandshake result)) s () allocated
 admission-preserves Server.restoreBody w (admissionWorker r (notifyInbound info)) s () allocated
 admission-preserves Server.restoreBody w (admissionWorker r (returnHandshake result)) s () allocated
 admission-preserves Server.restoreBody w (admissionWorker r (completedHandshake result)) s () allocated
 admission-preserves Server.restoreBody w (admissionWorker r impossibleHandshake) s () allocated
 admission-preserves Server.restoreBody w (admissionWorker r (reject l forbidden)) s () allocated
 admission-preserves Server.restoreBody w (admissionWorker r (reject l bodyFailed)) s () allocated
 admission-preserves Server.restoreBody w (admissionWorker r (reject l forkFailed)) s () allocated
-- Cleanup can replace entries and close sockets, but keeps allocated cells.
module CleanupPart where
 open import Data.Maybe using (just; nothing)
 open import Data.Maybe.Properties using (just-injective)
 open import Data.Product using (_,_)
 open import Relation.Nullary using (yes; no)
 open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
 open import Function using (case_of_)
 open import Class.DecEq using (_≟_)
 open import ConnectionManagement.Store using (lookup)
 import ConnectionManagement.Rules.Cleanup as Cleanup
 import ConnectionManagement.Rules.CM as CM

 -- Cleanup selection edits the entry heap without touching promises.
 select-preserves : ∀ w h l decision s → Allocated s → Allocated (Cleanup.selectCleanup w h l decision s)
 select-preserves w h l Cleanup.terminateAndPurge s allocated = allocated
 select-preserves w h l Cleanup.purgeOnly s allocated = allocated
 select-preserves w h l (Cleanup.waitBeforePurge st) s allocated = allocated

 -- Follow every cleanup branch, including interruption and close failure.
 cleanup-preserves : ∀ action w h p s {s′} → Cleanup.stepWorker w h p action s ≡ just s′ →
   Allocated s → Allocated s′
 cleanup-preserves Cleanup.takeCleanupMap w h (cleanupSelect l) s () allocated
 cleanup-preserves Cleanup.takeCleanupMap w h (cleanupClose l m tail) s () allocated
 cleanup-preserves Cleanup.takeCleanupMap w h (cleanupPublish l m tail) s () allocated
 cleanup-preserves Cleanup.takeCleanupMap w h (cleanupRestore l err) s () allocated
 cleanup-preserves Cleanup.takeCleanupMap w h (cleanupWaiting st) s () allocated
 cleanup-preserves Cleanup.takeCleanupMap w h (cleanupFinalize st outcome) s () allocated
 cleanup-preserves Cleanup.takeCleanupMap w h (cleanupCount outcome) s () allocated
 cleanup-preserves Cleanup.takeCleanupMap w h (cleanupDone outcome) s () allocated
 cleanup-preserves Cleanup.takeCleanupMap w h cleanupAcquire s eq allocated with CM.takeMap w (cm s) in takenEq
 ... | nothing = case eq of λ ()
 ... | just (l , c′) = subst Allocated (just-injective eq) allocated
 cleanup-preserves Cleanup.selectCleanupEntry w h cleanupAcquire s () allocated
 cleanup-preserves Cleanup.selectCleanupEntry w h (cleanupClose l m tail) s () allocated
 cleanup-preserves Cleanup.selectCleanupEntry w h (cleanupPublish l m tail) s () allocated
 cleanup-preserves Cleanup.selectCleanupEntry w h (cleanupRestore l err) s () allocated
 cleanup-preserves Cleanup.selectCleanupEntry w h (cleanupWaiting st) s () allocated
 cleanup-preserves Cleanup.selectCleanupEntry w h (cleanupFinalize st outcome) s () allocated
 cleanup-preserves Cleanup.selectCleanupEntry w h (cleanupCount outcome) s () allocated
 cleanup-preserves Cleanup.selectCleanupEntry w h (cleanupDone outcome) s () allocated
 cleanup-preserves Cleanup.selectCleanupEntry w h (cleanupSelect l) s eq allocated with mapCell (cm s)
 ... | full _ = case eq of λ ()
 ... | taken owner with owner ≟ w
 ...   | no _ = case eq of λ ()
 ...   | yes _ with lookup (handlerEntry h) (entries (cm s)) in found
 ...     | nothing = case eq of λ ()
 ...     | just st = subst Allocated (just-injective eq) (select-preserves w h l (Cleanup.decideCleanup st) s allocated)
 cleanup-preserves Cleanup.closeHandlerSocket w h cleanupAcquire s () allocated
 cleanup-preserves Cleanup.closeHandlerSocket w h (cleanupSelect l) s () allocated
 cleanup-preserves Cleanup.closeHandlerSocket w h (cleanupPublish l m tail) s () allocated
 cleanup-preserves Cleanup.closeHandlerSocket w h (cleanupRestore l err) s () allocated
 cleanup-preserves Cleanup.closeHandlerSocket w h (cleanupWaiting st) s () allocated
 cleanup-preserves Cleanup.closeHandlerSocket w h (cleanupFinalize st outcome) s () allocated
 cleanup-preserves Cleanup.closeHandlerSocket w h (cleanupCount outcome) s () allocated
 cleanup-preserves Cleanup.closeHandlerSocket w h (cleanupDone outcome) s () allocated
 cleanup-preserves Cleanup.closeHandlerSocket w h (cleanupClose l m tail) s eq allocated = subst Allocated (just-injective eq) allocated
 cleanup-preserves (Cleanup.failSocketClose error) w h cleanupAcquire s () allocated
 cleanup-preserves (Cleanup.failSocketClose error) w h (cleanupSelect l) s () allocated
 cleanup-preserves (Cleanup.failSocketClose error) w h (cleanupPublish l m tail) s () allocated
 cleanup-preserves (Cleanup.failSocketClose error) w h (cleanupRestore l err) s () allocated
 cleanup-preserves (Cleanup.failSocketClose error) w h (cleanupWaiting st) s () allocated
 cleanup-preserves (Cleanup.failSocketClose error) w h (cleanupFinalize st outcome) s () allocated
 cleanup-preserves (Cleanup.failSocketClose error) w h (cleanupCount outcome) s () allocated
 cleanup-preserves (Cleanup.failSocketClose error) w h (cleanupDone outcome) s () allocated
 cleanup-preserves (Cleanup.failSocketClose error) w h (cleanupClose l m tail) s eq allocated = subst Allocated (just-injective eq) allocated
 cleanup-preserves Cleanup.publishCleanupMap w h cleanupAcquire s () allocated
 cleanup-preserves Cleanup.publishCleanupMap w h (cleanupSelect l) s () allocated
 cleanup-preserves Cleanup.publishCleanupMap w h (cleanupClose l m tail) s () allocated
 cleanup-preserves Cleanup.publishCleanupMap w h (cleanupRestore l err) s () allocated
 cleanup-preserves Cleanup.publishCleanupMap w h (cleanupWaiting st) s () allocated
 cleanup-preserves Cleanup.publishCleanupMap w h (cleanupFinalize st outcome) s () allocated
 cleanup-preserves Cleanup.publishCleanupMap w h (cleanupCount outcome) s () allocated
 cleanup-preserves Cleanup.publishCleanupMap w h (cleanupDone outcome) s () allocated
 cleanup-preserves Cleanup.publishCleanupMap w h (cleanupPublish l m tail) s eq allocated with CM.putMap l m (cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = subst Allocated (just-injective eq) allocated
 cleanup-preserves Cleanup.restoreCleanupMap w h cleanupAcquire s () allocated
 cleanup-preserves Cleanup.restoreCleanupMap w h (cleanupSelect l) s () allocated
 cleanup-preserves Cleanup.restoreCleanupMap w h (cleanupClose l m tail) s () allocated
 cleanup-preserves Cleanup.restoreCleanupMap w h (cleanupPublish l m tail) s () allocated
 cleanup-preserves Cleanup.restoreCleanupMap w h (cleanupWaiting st) s () allocated
 cleanup-preserves Cleanup.restoreCleanupMap w h (cleanupFinalize st outcome) s () allocated
 cleanup-preserves Cleanup.restoreCleanupMap w h (cleanupCount outcome) s () allocated
 cleanup-preserves Cleanup.restoreCleanupMap w h (cleanupDone outcome) s () allocated
 cleanup-preserves Cleanup.restoreCleanupMap w h (cleanupRestore l err) s eq allocated with CM.putMap l (savedMap l) (cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = subst Allocated (just-injective eq) allocated
 cleanup-preserves Cleanup.timeWaitElapsed w h cleanupAcquire s () allocated
 cleanup-preserves Cleanup.timeWaitElapsed w h (cleanupSelect l) s () allocated
 cleanup-preserves Cleanup.timeWaitElapsed w h (cleanupClose l m tail) s () allocated
 cleanup-preserves Cleanup.timeWaitElapsed w h (cleanupPublish l m tail) s () allocated
 cleanup-preserves Cleanup.timeWaitElapsed w h (cleanupRestore l err) s () allocated
 cleanup-preserves Cleanup.timeWaitElapsed w h (cleanupFinalize st outcome) s () allocated
 cleanup-preserves Cleanup.timeWaitElapsed w h (cleanupCount outcome) s () allocated
 cleanup-preserves Cleanup.timeWaitElapsed w h (cleanupDone outcome) s () allocated
 cleanup-preserves Cleanup.timeWaitElapsed w h (cleanupWaiting st) s eq allocated = subst Allocated (just-injective eq) allocated
 cleanup-preserves (Cleanup.interruptTimeWait error) w h cleanupAcquire s () allocated
 cleanup-preserves (Cleanup.interruptTimeWait error) w h (cleanupSelect l) s () allocated
 cleanup-preserves (Cleanup.interruptTimeWait error) w h (cleanupClose l m tail) s () allocated
 cleanup-preserves (Cleanup.interruptTimeWait error) w h (cleanupPublish l m tail) s () allocated
 cleanup-preserves (Cleanup.interruptTimeWait error) w h (cleanupRestore l err) s () allocated
 cleanup-preserves (Cleanup.interruptTimeWait error) w h (cleanupFinalize st outcome) s () allocated
 cleanup-preserves (Cleanup.interruptTimeWait error) w h (cleanupCount outcome) s () allocated
 cleanup-preserves (Cleanup.interruptTimeWait error) w h (cleanupDone outcome) s () allocated
 cleanup-preserves (Cleanup.interruptTimeWait error) w h (cleanupWaiting st) s eq allocated = subst Allocated (just-injective eq) allocated
 cleanup-preserves Cleanup.finishTimeWait w h cleanupAcquire s () allocated
 cleanup-preserves Cleanup.finishTimeWait w h (cleanupSelect l) s () allocated
 cleanup-preserves Cleanup.finishTimeWait w h (cleanupClose l m tail) s () allocated
 cleanup-preserves Cleanup.finishTimeWait w h (cleanupPublish l m tail) s () allocated
 cleanup-preserves Cleanup.finishTimeWait w h (cleanupRestore l err) s () allocated
 cleanup-preserves Cleanup.finishTimeWait w h (cleanupWaiting st) s () allocated
 cleanup-preserves Cleanup.finishTimeWait w h (cleanupCount outcome) s () allocated
 cleanup-preserves Cleanup.finishTimeWait w h (cleanupDone outcome) s () allocated
 cleanup-preserves Cleanup.finishTimeWait w h (cleanupFinalize st outcome) s eq allocated with mapCell (cm s)
 ... | taken _ = case eq of λ ()
 ... | full m with lookup (handlerEntry h) (entries (cm s)) in found
 ...   | nothing = case eq of λ ()
 ...   | just _ = subst Allocated (just-injective eq)
   allocated
 cleanup-preserves Cleanup.readCleanupCounters w h cleanupAcquire s () allocated
 cleanup-preserves Cleanup.readCleanupCounters w h (cleanupSelect l) s () allocated
 cleanup-preserves Cleanup.readCleanupCounters w h (cleanupClose l m tail) s () allocated
 cleanup-preserves Cleanup.readCleanupCounters w h (cleanupPublish l m tail) s () allocated
 cleanup-preserves Cleanup.readCleanupCounters w h (cleanupRestore l err) s () allocated
 cleanup-preserves Cleanup.readCleanupCounters w h (cleanupWaiting st) s () allocated
 cleanup-preserves Cleanup.readCleanupCounters w h (cleanupFinalize st outcome) s () allocated
 cleanup-preserves Cleanup.readCleanupCounters w h (cleanupDone outcome) s () allocated
 cleanup-preserves Cleanup.readCleanupCounters w h (cleanupCount outcome) s eq allocated with mapCell (cm s)
 ... | taken _ = case eq of λ ()
 ... | full m with countIncoming (entries (cm s)) m
 ...   | nothing = case eq of λ ()
 ...   | just _ = subst Allocated (just-injective eq) allocated

-- Consuming a handshake result does not consume its promise cell.
module Handshake where
 open import Data.Nat using (suc; _≤?_)
 open import Data.List using (length)
 open import Data.Maybe using (just; nothing)
 open import Data.Maybe.Properties using (just-injective)
 open import Data.Product using (_,_)
 open import Relation.Nullary using (yes; no)
 open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
 open import Function using (case_of_)
 open import Class.DecEq using (_≟_)
 open import ConnectionManagement.Store using (lookup)
 import ConnectionManagement.Rules.Handshake as H

 -- Successful negotiation updates keep the allocated promise list.
 success-preserves : ∀ w a e h f decision s {old} → lookup e (entries (cm s)) ≡ just old →
   Allocated s → Allocated (H.applySuccess w a e h f decision s)
 success-preserves w a e h f (H.update st provenance) s found allocated =
   allocated
 success-preserves w a e h f (H.retain provenance) s found allocated = allocated
 success-preserves w a e h f (H.disconnect reason) s found allocated = allocated
 success-preserves w a e h f H.impossible s found allocated = allocated

 -- Error/query termination changes entries and map bindings only.
 terminate-preserves : ∀ w a e reason s {s′} → H.terminateResult w a e reason s ≡ just s′ →
   Allocated s → Allocated s′
 terminate-preserves w a e reason s eq allocated
   with lookup e (entries (cm s)) in found | mapCell (cm s)
 ... | nothing | _ = case eq of λ ()
 ... | just _ | taken _ = case eq of λ ()
 ... | just _ | full m with lookupConnection (key (request a)) m
 ...   | nothing = subst Allocated (just-injective eq) allocated
 ...   | just current with e ≟ current
 ...     | no _ = subst Allocated (just-injective eq) allocated
 ...     | yes _ = subst Allocated (just-injective eq)
   allocated

 -- Every consumer step retains its non-consuming promise cell.
 handshake-preserves : ∀ action mode w a s {s′} → H.stepWorker mode w a action s ≡ just s′ →
   Allocated s → Allocated s′
 handshake-preserves H.readResult mode w (admissionWorker r acquireMap) s () allocated
 handshake-preserves H.readResult mode w (admissionWorker r (count l)) s () allocated
 handshake-preserves H.readResult mode w (admissionWorker r (prepare l)) s () allocated
 handshake-preserves H.readResult mode w (admissionWorker r (selectEntry l p)) s () allocated
 handshake-preserves H.readResult mode w (admissionWorker r (forkHandler l p e)) s () allocated
 handshake-preserves H.readResult mode w (admissionWorker r (publish l p e)) s () allocated
 handshake-preserves H.readResult mode w (admissionWorker r (reject l reason)) s () allocated
 handshake-preserves H.readResult mode w (admissionWorker r (closeSocket reason)) s () allocated
 handshake-preserves H.readResult mode w (admissionWorker r (finished reason)) s () allocated
 handshake-preserves H.readResult mode w (admissionWorker r (countPublished p e)) s () allocated
 handshake-preserves H.readResult mode w (admissionWorker r (commitHandshake e result)) s () allocated
 handshake-preserves H.readResult mode w (admissionWorker r (countHandshake result)) s () allocated
 handshake-preserves H.readResult mode w (admissionWorker r (notifyInbound info)) s () allocated
 handshake-preserves H.readResult mode w (admissionWorker r (returnHandshake result)) s () allocated
 handshake-preserves H.readResult mode w (admissionWorker r (completedHandshake result)) s () allocated
 handshake-preserves H.readResult mode w (admissionWorker r impossibleHandshake) s () allocated
 handshake-preserves H.readResult mode w a@(admissionWorker r (awaitHandshake p e)) s eq allocated with lookup p (handshakeResults s)
 ... | nothing = case eq of λ ()
 ... | just result = subst Allocated (just-injective eq) allocated
 handshake-preserves H.commitResult mode w (admissionWorker r acquireMap) s () allocated
 handshake-preserves H.commitResult mode w (admissionWorker r (count l)) s () allocated
 handshake-preserves H.commitResult mode w (admissionWorker r (prepare l)) s () allocated
 handshake-preserves H.commitResult mode w (admissionWorker r (selectEntry l p)) s () allocated
 handshake-preserves H.commitResult mode w (admissionWorker r (forkHandler l p e)) s () allocated
 handshake-preserves H.commitResult mode w (admissionWorker r (publish l p e)) s () allocated
 handshake-preserves H.commitResult mode w (admissionWorker r (reject l reason)) s () allocated
 handshake-preserves H.commitResult mode w (admissionWorker r (closeSocket reason)) s () allocated
 handshake-preserves H.commitResult mode w (admissionWorker r (finished reason)) s () allocated
 handshake-preserves H.commitResult mode w (admissionWorker r (countPublished p e)) s () allocated
 handshake-preserves H.commitResult mode w (admissionWorker r (awaitHandshake p e)) s () allocated
 handshake-preserves H.commitResult mode w (admissionWorker r (countHandshake result)) s () allocated
 handshake-preserves H.commitResult mode w (admissionWorker r (notifyInbound info)) s () allocated
 handshake-preserves H.commitResult mode w (admissionWorker r (returnHandshake result)) s () allocated
 handshake-preserves H.commitResult mode w (admissionWorker r (completedHandshake result)) s () allocated
 handshake-preserves H.commitResult mode w (admissionWorker r impossibleHandshake) s () allocated
 handshake-preserves H.commitResult mode w a@(admissionWorker r (commitHandshake e (negotiated h f))) s eq allocated
   with lookup e (entries (cm s)) in found
 ... | nothing = case eq of λ ()
 ... | just st = subst Allocated (just-injective eq) (success-preserves w a e h f (H.decideSuccess r h f st) s found allocated)
 handshake-preserves H.commitResult mode w a@(admissionWorker r (commitHandshake e query)) s eq allocated =
   terminate-preserves w a e handshakeQuery s eq allocated
 handshake-preserves H.commitResult mode w a@(admissionWorker r (commitHandshake e (handlerError cls err))) s eq allocated =
   terminate-preserves w a e (handshakeError cls err) s eq allocated
 handshake-preserves H.readResultCounters mode w (admissionWorker r acquireMap) s () allocated
 handshake-preserves H.readResultCounters mode w (admissionWorker r (count l)) s () allocated
 handshake-preserves H.readResultCounters mode w (admissionWorker r (prepare l)) s () allocated
 handshake-preserves H.readResultCounters mode w (admissionWorker r (selectEntry l p)) s () allocated
 handshake-preserves H.readResultCounters mode w (admissionWorker r (forkHandler l p e)) s () allocated
 handshake-preserves H.readResultCounters mode w (admissionWorker r (publish l p e)) s () allocated
 handshake-preserves H.readResultCounters mode w (admissionWorker r (reject l reason)) s () allocated
 handshake-preserves H.readResultCounters mode w (admissionWorker r (closeSocket reason)) s () allocated
 handshake-preserves H.readResultCounters mode w (admissionWorker r (finished reason)) s () allocated
 handshake-preserves H.readResultCounters mode w (admissionWorker r (countPublished p e)) s () allocated
 handshake-preserves H.readResultCounters mode w (admissionWorker r (awaitHandshake p e)) s () allocated
 handshake-preserves H.readResultCounters mode w (admissionWorker r (commitHandshake e result)) s () allocated
 handshake-preserves H.readResultCounters mode w (admissionWorker r (notifyInbound info)) s () allocated
 handshake-preserves H.readResultCounters mode w (admissionWorker r (returnHandshake result)) s () allocated
 handshake-preserves H.readResultCounters mode w (admissionWorker r (completedHandshake result)) s () allocated
 handshake-preserves H.readResultCounters mode w (admissionWorker r impossibleHandshake) s () allocated
 handshake-preserves H.readResultCounters mode w a@(admissionWorker r (countHandshake result)) s eq allocated with mapCell (cm s)
 ... | taken _ = case eq of λ ()
 ... | full m with countIncoming (entries (cm s)) m
 ...   | nothing = case eq of λ ()
 ...   | just _ with result | mode
 ...     | connected info | responderMode = subst Allocated (just-injective eq) allocated
 ...     | connected info | noResponderMode = subst Allocated (just-injective eq) allocated
 ...     | disconnected _ | _ = subst Allocated (just-injective eq) allocated
 handshake-preserves H.enqueueInbound mode w (admissionWorker r acquireMap) s () allocated
 handshake-preserves H.enqueueInbound mode w (admissionWorker r (count l)) s () allocated
 handshake-preserves H.enqueueInbound mode w (admissionWorker r (prepare l)) s () allocated
 handshake-preserves H.enqueueInbound mode w (admissionWorker r (selectEntry l p)) s () allocated
 handshake-preserves H.enqueueInbound mode w (admissionWorker r (forkHandler l p e)) s () allocated
 handshake-preserves H.enqueueInbound mode w (admissionWorker r (publish l p e)) s () allocated
 handshake-preserves H.enqueueInbound mode w (admissionWorker r (reject l reason)) s () allocated
 handshake-preserves H.enqueueInbound mode w (admissionWorker r (closeSocket reason)) s () allocated
 handshake-preserves H.enqueueInbound mode w (admissionWorker r (finished reason)) s () allocated
 handshake-preserves H.enqueueInbound mode w (admissionWorker r (countPublished p e)) s () allocated
 handshake-preserves H.enqueueInbound mode w (admissionWorker r (awaitHandshake p e)) s () allocated
 handshake-preserves H.enqueueInbound mode w (admissionWorker r (commitHandshake e result)) s () allocated
 handshake-preserves H.enqueueInbound mode w (admissionWorker r (countHandshake result)) s () allocated
 handshake-preserves H.enqueueInbound mode w (admissionWorker r (returnHandshake result)) s () allocated
 handshake-preserves H.enqueueInbound mode w (admissionWorker r (completedHandshake result)) s () allocated
 handshake-preserves H.enqueueInbound mode w (admissionWorker r impossibleHandshake) s () allocated
 handshake-preserves H.enqueueInbound mode w a@(admissionWorker r (notifyInbound info)) s eq allocated with suc (length (inboundInfo s)) ≤? 100
 ... | no _ = case eq of λ ()
 ... | yes _ = subst Allocated (just-injective eq) allocated
 handshake-preserves H.returnResult mode w (admissionWorker r acquireMap) s () allocated
 handshake-preserves H.returnResult mode w (admissionWorker r (count l)) s () allocated
 handshake-preserves H.returnResult mode w (admissionWorker r (prepare l)) s () allocated
 handshake-preserves H.returnResult mode w (admissionWorker r (selectEntry l p)) s () allocated
 handshake-preserves H.returnResult mode w (admissionWorker r (forkHandler l p e)) s () allocated
 handshake-preserves H.returnResult mode w (admissionWorker r (publish l p e)) s () allocated
 handshake-preserves H.returnResult mode w (admissionWorker r (reject l reason)) s () allocated
 handshake-preserves H.returnResult mode w (admissionWorker r (closeSocket reason)) s () allocated
 handshake-preserves H.returnResult mode w (admissionWorker r (finished reason)) s () allocated
 handshake-preserves H.returnResult mode w (admissionWorker r (countPublished p e)) s () allocated
 handshake-preserves H.returnResult mode w (admissionWorker r (awaitHandshake p e)) s () allocated
 handshake-preserves H.returnResult mode w (admissionWorker r (commitHandshake e result)) s () allocated
 handshake-preserves H.returnResult mode w (admissionWorker r (countHandshake result)) s () allocated
 handshake-preserves H.returnResult mode w (admissionWorker r (notifyInbound info)) s () allocated
 handshake-preserves H.returnResult mode w (admissionWorker r (completedHandshake result)) s () allocated
 handshake-preserves H.returnResult mode w (admissionWorker r impossibleHandshake) s () allocated
 handshake-preserves H.returnResult mode w a@(admissionWorker r (returnHandshake result)) s eq allocated = subst Allocated (just-injective eq) allocated

-- The complete inbound dispatcher composes these primitive effects.
module Inbound where
 open import Data.Product using (_,_; proj₁; proj₂)
 import ConnectionManagement.Rules.IGRegistration as IG
 import ConnectionManagement.Rules.InboundRelease as Release
 import ConnectionManagement.Rules.RemoteState as Remote
 import ConnectionManagement.Rules.Pruning as Prune
 import ConnectionManagement.Rules.HandlerLifecycle as Life
 open import Data.List using ([]; _∷_)
 open import Data.Bool using (true; false)
 open import Data.Bool.ListAction using (any)
 open import Data.Maybe using (just; nothing)
 open import Data.Maybe.Properties using (just-injective)
 open import Relation.Nullary using (does)
 open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
 open import Function using (case_of_)
 open import Class.DecEq using (_≟_)
 open import ConnectionManagement.Store using (lookup)
 open import ConnectionManagement.Machine using
   (advance; handlerStep; remoteStep; promotionHardLimit; pruningGeneration; remoteCall;
    inboundGovernor; world; handlerLifecycles; inboundRelease; responder; releaseStep; igStep;
    admissionStep; cleanupStep; handshakeStep; handlerExit; handlerPublication; publicationFaults;
    resultWritten; duplicateWrite; Executes; done; next; replay; replay-sound)
 open AdmissionPart
 open CleanupPart
 open Handshake
 import ConnectionManagement.Rules.Handshake as H
 import ConnectionManagement.Rules.Server as Server
 import ConnectionManagement.Rules.Cleanup as Cleanup

 -- Publishing a result writes its result store, not the cell list.
 publication-preserves : ∀ w result s {s′} → H.publishBoundary w result s ≡ just (H.published s′) →
   Allocated s → Allocated s′
 publication-preserves w result s eq allocated with lookup w (handlers s) | lookup w (cleanups s)
 ... | nothing | _ = case eq of λ ()
 ... | just _ | just _ = case eq of λ ()
 ... | just h | nothing with any (λ p → does (p ≟ handlerPromise h)) (promises s)
 ...   | false = case eq of λ ()
 ...   | true with lookup (handlerPromise h) (handshakeResults s)
 ...     | just _ = case eq of λ ()
 ...     | nothing with just-injective eq
 ...       | refl = allocated

 -- A primitive release edit changes only a CM entry.
 release-edit-preserves : ∀ edit s {s′} → Release.applyEdit edit s ≡ just s′ →
   Allocated s → Allocated s′
 release-edit-preserves nothing s eq allocated = subst Allocated (just-injective eq) allocated
 release-edit-preserves (just (e , st)) s eq allocated with lookup e (entries (cm s)) in found
 ... | nothing = case eq of λ ()
 ... | just old with just-injective eq
 ...   | refl = allocated

 -- Compose entry-only edits inside the atomic pruning operation.
 prune-edits-preserves : ∀ edits s {s′} → Prune.applyEdits edits s ≡ just s′ →
   Allocated s → Allocated s′
 prune-edits-preserves [] s eq allocated = subst Allocated (just-injective eq) allocated
 prune-edits-preserves (edit ∷ edits) s eq allocated
   with Release.applyEdit (just edit) s in changed
 ... | nothing = case eq of λ ()
 ... | just s₁ = prune-edits-preserves edits s₁ eq
   (release-edit-preserves (just edit) s changed allocated)

 -- Successful dispatcher steps preserve the same allocated promise.
 advance-preserves : ∀ action c {c′} → advance action c ≡ just c′ →
   Allocated (world c) → Allocated (world c′)
 advance-preserves (handlerStep w action) c eq allocated
   with Life.step w action (handlerLifecycles c) (inboundGovernor c) (world c)
 ... | nothing = case eq of λ ()
 ... | just (rt , ig) = subst (λ config → Allocated (world config)) (just-injective eq) allocated
 advance-preserves (remoteStep action) c eq allocated
   with Life.allowRemote action (handlerLifecycles c) (world c)
 ... | false = case eq of λ ()
 ... | true with Remote.step (promotionHardLimit c) (pruningGeneration c) action (remoteCall c) (inboundGovernor c) (world c)
 ... | nothing = case eq of λ ()
 ... | just p with Prune.applyEdits (Remote.edits p) (world c) in edited
 ...   | nothing = case eq of λ ()
 ...   | just s = subst (λ config → Allocated (world config)) (just-injective eq)
   (prune-edits-preserves (Remote.edits p) (world c) edited allocated)
 advance-preserves (releaseStep action) c eq allocated
   with Life.allowRelease action (handlerLifecycles c) (world c)
 ... | false = case eq of λ ()
 ... | true with Release.step action (inboundRelease c) (inboundGovernor c) (world c)
 ... | nothing = case eq of λ ()
 ... | just p with Release.applyEdit (Release.edit p) (world c) in edited
 ...   | nothing = case eq of λ ()
 ...   | just s = subst (λ config → Allocated (world config)) (just-injective eq)
   (release-edit-preserves (Release.edit p) (world c) edited allocated)
 advance-preserves (igStep action) c eq allocated
   with Life.allowIG action (handlerLifecycles c)
 ... | false = case eq of λ ()
 ... | true with IG.step (responder c) action (inboundGovernor c) (inboundInfo (world c))
 ... | nothing = case eq of λ ()
 ... | just (ig , queue) = subst (λ config → Allocated (world config)) (just-injective eq) allocated
 advance-preserves (admissionStep w action) c eq allocated with lookup w (admissions (world c))
 ... | nothing = case eq of λ ()
 ... | just a with Server.stepWorker w a action (world c) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just s′ = subst (λ config → Allocated (world config)) (just-injective eq)
   (admission-preserves action w a (world c) stepped allocated)
 advance-preserves (cleanupStep w action) c eq allocated
   with lookup w (handlers (world c)) | lookup w (cleanups (world c))
 ... | nothing | _ = case eq of λ ()
 ... | just _ | nothing = case eq of λ ()
 ... | just h | just p with Cleanup.stepWorker w h p action (world c) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just s′ = subst (λ config → Allocated (world config)) (just-injective eq)
   (cleanup-preserves action w h p (world c) stepped allocated)
 advance-preserves (handshakeStep w action) c eq allocated with lookup w (admissions (world c))
 ... | nothing = case eq of λ ()
 ... | just a with H.stepWorker (responder c) w a action (world c) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just s′ = subst (λ config → Allocated (world config)) (just-injective eq)
   (handshake-preserves action (responder c) w a (world c) stepped allocated)
 advance-preserves (handlerExit w) c eq allocated
   with Life.mayExit w (handlerLifecycles c)
 ... | false = case eq of λ ()
 ... | true with lookup w (handlers (world c)) | lookup w (cleanups (world c))
 ... | nothing | _ = case eq of λ ()
 ... | just _ | just _ = case eq of λ ()
 ... | just _ | nothing = subst (λ config → Allocated (world config)) (just-injective eq) allocated
 advance-preserves (handlerPublication w result outcome) c eq allocated
   with any (λ v → does (v ≟ w)) (publicationFaults c)
 ... | true = case eq of λ ()
 ... | false with H.publishBoundary w result (world c) in published | outcome
 ...   | nothing | _ = case eq of λ ()
 ...   | just (H.published s′) | resultWritten =
   subst (λ config → Allocated (world config)) (just-injective eq)
     (publication-preserves w result (world c) published allocated)
 ...   | just H.writerBlocked | duplicateWrite =
   subst (λ config → Allocated (world config)) (just-injective eq) allocated
 ...   | just (H.published _) | duplicateWrite = case eq of λ ()
 ...   | just H.writerBlocked | resultWritten = case eq of λ ()

 -- Induction over any finite source execution.
 exec-preserves : ∀ {c actions c′} → Allocated (world c) → Executes c actions c′ → Allocated (world c′)
 exec-preserves allocated done = allocated
 exec-preserves allocated (next {c = c} {a = action} eq rest) = exec-preserves (advance-preserves action c eq allocated) rest

 -- Successful replay supplies a genuine finite source execution.
 replay-preserves : ∀ actions c {c′} → Allocated (world c) → replay actions c ≡ just c′ → Allocated (world c′)
 replay-preserves actions c allocated eq = exec-preserves allocated (replay-sound actions c eq)

-- Outbound acquisition only extends the list at newPromise.
module Acquire where
 open import Data.Bool using (true; false)
 open import Data.Nat using (suc; _<_)
 open import Data.Maybe using (just; nothing)
 open import Data.Maybe.Properties using (just-injective)
 open import Data.Product using (_×_; _,_; proj₁; proj₂)
 open import Relation.Binary.PropositionalEquality using (_≡_; subst)
 open import Function using (case_of_)
 open import ConnectionManagement.Store using (lookup)
 import ConnectionManagement.Rules.OutboundAcquire as A
 import ConnectionManagement.Rules.OutboundCases as C
 import ConnectionManagement.Rules.InformationChannel as Queue

 -- Transport membership along equality of exact successful results.
 result-preserves : ∀ {pair pair′ : A.Frame × State} → just pair ≡ just pair′ →
   Allocated (proj₂ pair) → Allocated (proj₂ pair′)
 result-preserves eq = subst (λ pair → Allocated (proj₂ pair)) (just-injective eq)

 -- Each acquisition decision keeps existing allocated cells.
 choice-preserves : ∀ first e d f s {out} →
   Allocated s → A.applyChoice first e d f s ≡ just out → Allocated (proj₂ out)
 choice-preserves first e C.retry f s allocated ()
 choice-preserves first e (C.waitInbound k) f s allocated eq = result-preserves eq allocated
 choice-preserves true e (C.refuse err) f s allocated eq = result-preserves eq allocated
 choice-preserves false e (C.refuse err) f s allocated eq = result-preserves eq allocated
 choice-preserves first e (C.gone result) f s allocated eq = result-preserves eq allocated
 choice-preserves true e (C.reuse st result) f s allocated eq = result-preserves eq allocated
 choice-preserves false e (C.reuse st result) f s allocated eq = result-preserves eq allocated

 -- Existing and fresh entry selections preserve promise membership.
 known-preserves : ∀ chosen m f s {out} → Allocated s →
   A.selectKnown chosen m f s ≡ just out → Allocated (proj₂ out)
 known-preserves (just e) m f s allocated eq with lookup e (entries (cm s)) in found
 ... | nothing = case eq of λ ()
 ... | just st = choice-preserves true e (C.acquireCase st) f s
    allocated eq
 known-preserves nothing m f s allocated eq with A.provenance (A.req f)
 ... | inbound = result-preserves eq allocated
 ... | outbound with lookup (ident (nextEntry (cm s))) (entries (cm s))
 ...   | just _ = case eq of λ ()
 ...   | nothing = result-preserves eq
   allocated

 -- The guarded map selection delegates to the same entry decision.
 selection-preserves : ∀ chosen f s {out} → Allocated s →
   A.selectEntry chosen f s ≡ just out → Allocated (proj₂ out)
 selection-preserves chosen f s allocated eq with mapCell (cm s)
 ... | taken _ = case eq of λ ()
 ... | full m with A.validSelection (A.peer (A.req f)) chosen m
 ...   | false = case eq of λ ()
 ...   | true = known-preserves chosen m f s allocated eq

 -- Successful negotiation updates keep the allocated promise list.
 success-preserves : ∀ mode e k h flow f s {out} → Allocated s →
   A.commitSuccess mode e k h flow f s ≡ just out → Allocated (proj₂ out)
 success-preserves mode e k h flow f s allocated eq with lookup e (entries (cm s)) in found
 ... | nothing = case eq of λ ()
 ... | just st with C.successCase k (A.child (A.req f)) h flow st
 ...   | C.decision replacement notify (C.raised err) = result-preserves eq allocated
 ...   | C.decision replacement false (C.connected k′ flow′ h′) with replacement
 ...     | nothing = result-preserves eq allocated
 ...     | just replacement′ = result-preserves eq allocated
 success-preserves mode e k h flow f s allocated eq | just st | C.decision replacement false (C.disconnected k′ reason) with replacement
 ... | nothing = result-preserves eq allocated
 ... | just replacement′ = result-preserves eq allocated
 success-preserves noResponderMode e k h flow f s allocated eq | just st | C.decision replacement true result with result | replacement
 ... | C.connected _ _ _ | nothing = result-preserves eq allocated
 ... | C.connected _ _ _ | just replacement′ = result-preserves eq allocated
 ... | C.disconnected _ _ | nothing = result-preserves eq allocated
 ... | C.disconnected _ _ | just replacement′ = result-preserves eq allocated
 ... | C.raised _ | _ = result-preserves eq allocated
 success-preserves responderMode e k h flow f s allocated eq | just st | C.decision replacement true result
   with Queue.writeMessage (newConnection (newConnectionInfo outbound k flow h)) (inboundInfo s) in enqueued | result | replacement
 ... | nothing | C.connected _ _ _ | _ rewrite enqueued = case eq of λ ()
 ... | nothing | C.disconnected _ _ | _ rewrite enqueued = case eq of λ ()
 ... | just queue | C.connected _ _ _ | nothing rewrite enqueued = result-preserves eq allocated
 ... | just queue | C.connected _ _ _ | just replacement′ rewrite enqueued = result-preserves eq allocated
 ... | just queue | C.disconnected _ _ | nothing rewrite enqueued = result-preserves eq allocated
 ... | just queue | C.disconnected _ _ | just replacement′ rewrite enqueued = result-preserves eq allocated
 ... | _ | C.raised _ | _ = result-preserves eq allocated

 -- Acquisition error commits change entries and aliases only.
 error-preserves : ∀ e k reason f s {out} → Allocated s →
   A.commitError e k reason f s ≡ just out → Allocated (proj₂ out)
 error-preserves e k reason f s allocated eq with lookup e (entries (cm s)) in found | mapCell (cm s)
 ... | nothing | _ = case eq of λ ()
 ... | just _ | taken _ = case eq of λ ()
 ... | just st | full m = result-preserves eq
   allocated

 -- Every enabled primitive step retains the observed promise.
 step-preserves : ∀ caller mode action f s {out} → Allocated s →
   A.step caller mode action f s ≡ just out → Allocated (proj₂ out)
 step-preserves caller mode (A.select chosen) f s allocated eq with A.pc f
 ... | A.selecting = selection-preserves chosen f s allocated eq
 step-preserves caller mode (A.select chosen) f s allocated eq | (A.count p) = case eq of λ ()
 step-preserves caller mode (A.select chosen) f s allocated eq | (A.allocatePromise e) = case eq of λ ()
 step-preserves caller mode (A.select chosen) f s allocated eq | (A.openSocket e p) = case eq of λ ()
 step-preserves caller mode (A.select chosen) f s allocated eq | (A.configureSocket e p) = case eq of λ ()
 step-preserves caller mode (A.select chosen) f s allocated eq | (A.bindSocket e p) = case eq of λ ()
 step-preserves caller mode (A.select chosen) f s allocated eq | (A.connectSocket e p) = case eq of λ ()
 step-preserves caller mode (A.select chosen) f s allocated eq | (A.localAddress e p) = case eq of λ ()
 step-preserves caller mode (A.select chosen) f s allocated eq | (A.updateAddress e p k) = case eq of λ ()
 step-preserves caller mode (A.select chosen) f s allocated eq | (A.forkHandler e p k) = case eq of λ ()
 step-preserves caller mode (A.select chosen) f s allocated eq | (A.connectedCommit e p k) = case eq of λ ()
 step-preserves caller mode (A.select chosen) f s allocated eq | (A.awaitResult e p k) = case eq of λ ()
 step-preserves caller mode (A.select chosen) f s allocated eq | (A.commitResult e k result) = case eq of λ ()
 step-preserves caller mode (A.select chosen) f s allocated eq | (A.waitingInbound e k) = case eq of λ ()
 step-preserves caller mode (A.select chosen) f s allocated eq | (A.closeError e err′) = case eq of λ ()
 step-preserves caller mode (A.select chosen) f s allocated eq | (A.removeError e err′) = case eq of λ ()
 step-preserves caller mode (A.select chosen) f s allocated eq | (A.complete result) = case eq of λ ()
 step-preserves caller mode A.readCounters f s allocated eq with A.pc f | mapCell (cm s)
 ... | A.count next | full m with countIncoming (entries (cm s)) m
 ...   | nothing = case eq of λ ()
 ...   | just _ = result-preserves eq allocated
 step-preserves caller mode A.readCounters f s allocated eq | A.selecting | _ = case eq of λ ()
 step-preserves caller mode A.readCounters f s allocated eq | (A.allocatePromise e) | _ = case eq of λ ()
 step-preserves caller mode A.readCounters f s allocated eq | (A.openSocket e p) | _ = case eq of λ ()
 step-preserves caller mode A.readCounters f s allocated eq | (A.configureSocket e p) | _ = case eq of λ ()
 step-preserves caller mode A.readCounters f s allocated eq | (A.bindSocket e p) | _ = case eq of λ ()
 step-preserves caller mode A.readCounters f s allocated eq | (A.connectSocket e p) | _ = case eq of λ ()
 step-preserves caller mode A.readCounters f s allocated eq | (A.localAddress e p) | _ = case eq of λ ()
 step-preserves caller mode A.readCounters f s allocated eq | (A.updateAddress e p k) | _ = case eq of λ ()
 step-preserves caller mode A.readCounters f s allocated eq | (A.forkHandler e p k) | _ = case eq of λ ()
 step-preserves caller mode A.readCounters f s allocated eq | (A.connectedCommit e p k) | _ = case eq of λ ()
 step-preserves caller mode A.readCounters f s allocated eq | (A.awaitResult e p k) | _ = case eq of λ ()
 step-preserves caller mode A.readCounters f s allocated eq | (A.commitResult e k result) | _ = case eq of λ ()
 step-preserves caller mode A.readCounters f s allocated eq | (A.waitingInbound e k) | _ = case eq of λ ()
 step-preserves caller mode A.readCounters f s allocated eq | (A.closeError e err′) | _ = case eq of λ ()
 step-preserves caller mode A.readCounters f s allocated eq | (A.removeError e err′) | _ = case eq of λ ()
 step-preserves caller mode A.readCounters f s allocated eq | (A.complete result) | _ = case eq of λ ()
 step-preserves caller mode A.readCounters f s allocated eq | (A.count p) | taken w = case eq of λ ()
 step-preserves caller mode A.newPromise f s allocated eq with A.pc f
 ... | A.allocatePromise e with lookup (ident (nextPromise s)) (handshakeResults s)
 ...   | just _ = case eq of λ ()
 ...   | nothing = result-preserves eq
   (there allocated)
 step-preserves caller mode A.newPromise f s allocated eq | A.selecting = case eq of λ ()
 step-preserves caller mode A.newPromise f s allocated eq | (A.count p) = case eq of λ ()
 step-preserves caller mode A.newPromise f s allocated eq | (A.openSocket e p) = case eq of λ ()
 step-preserves caller mode A.newPromise f s allocated eq | (A.configureSocket e p) = case eq of λ ()
 step-preserves caller mode A.newPromise f s allocated eq | (A.bindSocket e p) = case eq of λ ()
 step-preserves caller mode A.newPromise f s allocated eq | (A.connectSocket e p) = case eq of λ ()
 step-preserves caller mode A.newPromise f s allocated eq | (A.localAddress e p) = case eq of λ ()
 step-preserves caller mode A.newPromise f s allocated eq | (A.updateAddress e p k) = case eq of λ ()
 step-preserves caller mode A.newPromise f s allocated eq | (A.forkHandler e p k) = case eq of λ ()
 step-preserves caller mode A.newPromise f s allocated eq | (A.connectedCommit e p k) = case eq of λ ()
 step-preserves caller mode A.newPromise f s allocated eq | (A.awaitResult e p k) = case eq of λ ()
 step-preserves caller mode A.newPromise f s allocated eq | (A.commitResult e k result) = case eq of λ ()
 step-preserves caller mode A.newPromise f s allocated eq | (A.waitingInbound e k) = case eq of λ ()
 step-preserves caller mode A.newPromise f s allocated eq | (A.closeError e err′) = case eq of λ ()
 step-preserves caller mode A.newPromise f s allocated eq | (A.removeError e err′) = case eq of λ ()
 step-preserves caller mode A.newPromise f s allocated eq | (A.complete result) = case eq of λ ()
 step-preserves caller mode A.openOK f s allocated eq with A.pc f | lookup (A.socketRef (A.req f)) (sockets s)
 ... | A.openSocket e p | nothing = result-preserves eq allocated
 step-preserves caller mode A.openOK f s allocated eq | A.selecting | _ = case eq of λ ()
 step-preserves caller mode A.openOK f s allocated eq | (A.count p) | _ = case eq of λ ()
 step-preserves caller mode A.openOK f s allocated eq | (A.allocatePromise e) | _ = case eq of λ ()
 step-preserves caller mode A.openOK f s allocated eq | (A.configureSocket e p) | _ = case eq of λ ()
 step-preserves caller mode A.openOK f s allocated eq | (A.bindSocket e p) | _ = case eq of λ ()
 step-preserves caller mode A.openOK f s allocated eq | (A.connectSocket e p) | _ = case eq of λ ()
 step-preserves caller mode A.openOK f s allocated eq | (A.localAddress e p) | _ = case eq of λ ()
 step-preserves caller mode A.openOK f s allocated eq | (A.updateAddress e p k) | _ = case eq of λ ()
 step-preserves caller mode A.openOK f s allocated eq | (A.forkHandler e p k) | _ = case eq of λ ()
 step-preserves caller mode A.openOK f s allocated eq | (A.connectedCommit e p k) | _ = case eq of λ ()
 step-preserves caller mode A.openOK f s allocated eq | (A.awaitResult e p k) | _ = case eq of λ ()
 step-preserves caller mode A.openOK f s allocated eq | (A.commitResult e k result) | _ = case eq of λ ()
 step-preserves caller mode A.openOK f s allocated eq | (A.waitingInbound e k) | _ = case eq of λ ()
 step-preserves caller mode A.openOK f s allocated eq | (A.closeError e err′) | _ = case eq of λ ()
 step-preserves caller mode A.openOK f s allocated eq | (A.removeError e err′) | _ = case eq of λ ()
 step-preserves caller mode A.openOK f s allocated eq | (A.complete result) | _ = case eq of λ ()
 step-preserves caller mode A.openOK f s allocated eq | (A.openSocket e p) | just sock = case eq of λ ()
 step-preserves caller mode A.configureOK f s allocated eq with A.pc f | A.bindLocal (A.req f)
 ... | A.configureSocket e p | nothing = result-preserves eq allocated
 ... | A.configureSocket e p | just _ = result-preserves eq allocated
 step-preserves caller mode A.configureOK f s allocated eq | A.selecting | _ = case eq of λ ()
 step-preserves caller mode A.configureOK f s allocated eq | (A.count p) | _ = case eq of λ ()
 step-preserves caller mode A.configureOK f s allocated eq | (A.allocatePromise e) | _ = case eq of λ ()
 step-preserves caller mode A.configureOK f s allocated eq | (A.openSocket e p) | _ = case eq of λ ()
 step-preserves caller mode A.configureOK f s allocated eq | (A.bindSocket e p) | _ = case eq of λ ()
 step-preserves caller mode A.configureOK f s allocated eq | (A.connectSocket e p) | _ = case eq of λ ()
 step-preserves caller mode A.configureOK f s allocated eq | (A.localAddress e p) | _ = case eq of λ ()
 step-preserves caller mode A.configureOK f s allocated eq | (A.updateAddress e p k) | _ = case eq of λ ()
 step-preserves caller mode A.configureOK f s allocated eq | (A.forkHandler e p k) | _ = case eq of λ ()
 step-preserves caller mode A.configureOK f s allocated eq | (A.connectedCommit e p k) | _ = case eq of λ ()
 step-preserves caller mode A.configureOK f s allocated eq | (A.awaitResult e p k) | _ = case eq of λ ()
 step-preserves caller mode A.configureOK f s allocated eq | (A.commitResult e k result) | _ = case eq of λ ()
 step-preserves caller mode A.configureOK f s allocated eq | (A.waitingInbound e k) | _ = case eq of λ ()
 step-preserves caller mode A.configureOK f s allocated eq | (A.closeError e err′) | _ = case eq of λ ()
 step-preserves caller mode A.configureOK f s allocated eq | (A.removeError e err′) | _ = case eq of λ ()
 step-preserves caller mode A.configureOK f s allocated eq | (A.complete result) | _ = case eq of λ ()
 step-preserves caller mode A.bindOK f s allocated eq with A.pc f
 ... | A.bindSocket e p = result-preserves eq allocated
 step-preserves caller mode A.bindOK f s allocated eq | A.selecting = case eq of λ ()
 step-preserves caller mode A.bindOK f s allocated eq | (A.count p) = case eq of λ ()
 step-preserves caller mode A.bindOK f s allocated eq | (A.allocatePromise e) = case eq of λ ()
 step-preserves caller mode A.bindOK f s allocated eq | (A.openSocket e p) = case eq of λ ()
 step-preserves caller mode A.bindOK f s allocated eq | (A.configureSocket e p) = case eq of λ ()
 step-preserves caller mode A.bindOK f s allocated eq | (A.connectSocket e p) = case eq of λ ()
 step-preserves caller mode A.bindOK f s allocated eq | (A.localAddress e p) = case eq of λ ()
 step-preserves caller mode A.bindOK f s allocated eq | (A.updateAddress e p k) = case eq of λ ()
 step-preserves caller mode A.bindOK f s allocated eq | (A.forkHandler e p k) = case eq of λ ()
 step-preserves caller mode A.bindOK f s allocated eq | (A.connectedCommit e p k) = case eq of λ ()
 step-preserves caller mode A.bindOK f s allocated eq | (A.awaitResult e p k) = case eq of λ ()
 step-preserves caller mode A.bindOK f s allocated eq | (A.commitResult e k result) = case eq of λ ()
 step-preserves caller mode A.bindOK f s allocated eq | (A.waitingInbound e k) = case eq of λ ()
 step-preserves caller mode A.bindOK f s allocated eq | (A.closeError e err′) = case eq of λ ()
 step-preserves caller mode A.bindOK f s allocated eq | (A.removeError e err′) = case eq of λ ()
 step-preserves caller mode A.bindOK f s allocated eq | (A.complete result) = case eq of λ ()
 step-preserves caller mode A.connectOK f s allocated eq with A.pc f
 ... | A.connectSocket e p = result-preserves eq allocated
 step-preserves caller mode A.connectOK f s allocated eq | A.selecting = case eq of λ ()
 step-preserves caller mode A.connectOK f s allocated eq | (A.count p) = case eq of λ ()
 step-preserves caller mode A.connectOK f s allocated eq | (A.allocatePromise e) = case eq of λ ()
 step-preserves caller mode A.connectOK f s allocated eq | (A.openSocket e p) = case eq of λ ()
 step-preserves caller mode A.connectOK f s allocated eq | (A.configureSocket e p) = case eq of λ ()
 step-preserves caller mode A.connectOK f s allocated eq | (A.bindSocket e p) = case eq of λ ()
 step-preserves caller mode A.connectOK f s allocated eq | (A.localAddress e p) = case eq of λ ()
 step-preserves caller mode A.connectOK f s allocated eq | (A.updateAddress e p k) = case eq of λ ()
 step-preserves caller mode A.connectOK f s allocated eq | (A.forkHandler e p k) = case eq of λ ()
 step-preserves caller mode A.connectOK f s allocated eq | (A.connectedCommit e p k) = case eq of λ ()
 step-preserves caller mode A.connectOK f s allocated eq | (A.awaitResult e p k) = case eq of λ ()
 step-preserves caller mode A.connectOK f s allocated eq | (A.commitResult e k result) = case eq of λ ()
 step-preserves caller mode A.connectOK f s allocated eq | (A.waitingInbound e k) = case eq of λ ()
 step-preserves caller mode A.connectOK f s allocated eq | (A.closeError e err′) = case eq of λ ()
 step-preserves caller mode A.connectOK f s allocated eq | (A.removeError e err′) = case eq of λ ()
 step-preserves caller mode A.connectOK f s allocated eq | (A.complete result) = case eq of λ ()
 step-preserves caller mode (A.gotLocal local) f s allocated eq with A.pc f
 ... | A.localAddress e p = result-preserves eq allocated
 step-preserves caller mode (A.gotLocal local) f s allocated eq | A.selecting = case eq of λ ()
 step-preserves caller mode (A.gotLocal local) f s allocated eq | (A.count p) = case eq of λ ()
 step-preserves caller mode (A.gotLocal local) f s allocated eq | (A.allocatePromise e) = case eq of λ ()
 step-preserves caller mode (A.gotLocal local) f s allocated eq | (A.openSocket e p) = case eq of λ ()
 step-preserves caller mode (A.gotLocal local) f s allocated eq | (A.configureSocket e p) = case eq of λ ()
 step-preserves caller mode (A.gotLocal local) f s allocated eq | (A.bindSocket e p) = case eq of λ ()
 step-preserves caller mode (A.gotLocal local) f s allocated eq | (A.connectSocket e p) = case eq of λ ()
 step-preserves caller mode (A.gotLocal local) f s allocated eq | (A.updateAddress e p k) = case eq of λ ()
 step-preserves caller mode (A.gotLocal local) f s allocated eq | (A.forkHandler e p k) = case eq of λ ()
 step-preserves caller mode (A.gotLocal local) f s allocated eq | (A.connectedCommit e p k) = case eq of λ ()
 step-preserves caller mode (A.gotLocal local) f s allocated eq | (A.awaitResult e p k) = case eq of λ ()
 step-preserves caller mode (A.gotLocal local) f s allocated eq | (A.commitResult e k result) = case eq of λ ()
 step-preserves caller mode (A.gotLocal local) f s allocated eq | (A.waitingInbound e k) = case eq of λ ()
 step-preserves caller mode (A.gotLocal local) f s allocated eq | (A.closeError e err′) = case eq of λ ()
 step-preserves caller mode (A.gotLocal local) f s allocated eq | (A.removeError e err′) = case eq of λ ()
 step-preserves caller mode (A.gotLocal local) f s allocated eq | (A.complete result) = case eq of λ ()
 step-preserves caller mode A.updateLocalAddress f s allocated eq with A.pc f | mapCell (cm s)
 ... | A.updateAddress e p k | full m with A.updateLocal k m
 ...   | true , m′ = result-preserves eq allocated
 ...   | false , m′ = result-preserves eq allocated
 step-preserves caller mode A.updateLocalAddress f s allocated eq | A.selecting | _ = case eq of λ ()
 step-preserves caller mode A.updateLocalAddress f s allocated eq | (A.count p) | _ = case eq of λ ()
 step-preserves caller mode A.updateLocalAddress f s allocated eq | (A.allocatePromise e) | _ = case eq of λ ()
 step-preserves caller mode A.updateLocalAddress f s allocated eq | (A.openSocket e p) | _ = case eq of λ ()
 step-preserves caller mode A.updateLocalAddress f s allocated eq | (A.configureSocket e p) | _ = case eq of λ ()
 step-preserves caller mode A.updateLocalAddress f s allocated eq | (A.bindSocket e p) | _ = case eq of λ ()
 step-preserves caller mode A.updateLocalAddress f s allocated eq | (A.connectSocket e p) | _ = case eq of λ ()
 step-preserves caller mode A.updateLocalAddress f s allocated eq | (A.localAddress e p) | _ = case eq of λ ()
 step-preserves caller mode A.updateLocalAddress f s allocated eq | (A.forkHandler e p k) | _ = case eq of λ ()
 step-preserves caller mode A.updateLocalAddress f s allocated eq | (A.connectedCommit e p k) | _ = case eq of λ ()
 step-preserves caller mode A.updateLocalAddress f s allocated eq | (A.awaitResult e p k) | _ = case eq of λ ()
 step-preserves caller mode A.updateLocalAddress f s allocated eq | (A.commitResult e k result) | _ = case eq of λ ()
 step-preserves caller mode A.updateLocalAddress f s allocated eq | (A.waitingInbound e k) | _ = case eq of λ ()
 step-preserves caller mode A.updateLocalAddress f s allocated eq | (A.closeError e err′) | _ = case eq of λ ()
 step-preserves caller mode A.updateLocalAddress f s allocated eq | (A.removeError e err′) | _ = case eq of λ ()
 step-preserves caller mode A.updateLocalAddress f s allocated eq | (A.complete result) | _ = case eq of λ ()
 step-preserves caller mode A.updateLocalAddress f s allocated eq | (A.updateAddress e p k) | taken w = case eq of λ ()
 step-preserves caller mode A.forkOK f s allocated eq with A.pc f | lookup (A.child (A.req f)) (handlers s)
 ... | A.forkHandler e p k | nothing = result-preserves eq allocated
 step-preserves caller mode A.forkOK f s allocated eq | A.selecting | _ = case eq of λ ()
 step-preserves caller mode A.forkOK f s allocated eq | (A.count p) | _ = case eq of λ ()
 step-preserves caller mode A.forkOK f s allocated eq | (A.allocatePromise e) | _ = case eq of λ ()
 step-preserves caller mode A.forkOK f s allocated eq | (A.openSocket e p) | _ = case eq of λ ()
 step-preserves caller mode A.forkOK f s allocated eq | (A.configureSocket e p) | _ = case eq of λ ()
 step-preserves caller mode A.forkOK f s allocated eq | (A.bindSocket e p) | _ = case eq of λ ()
 step-preserves caller mode A.forkOK f s allocated eq | (A.connectSocket e p) | _ = case eq of λ ()
 step-preserves caller mode A.forkOK f s allocated eq | (A.localAddress e p) | _ = case eq of λ ()
 step-preserves caller mode A.forkOK f s allocated eq | (A.updateAddress e p k) | _ = case eq of λ ()
 step-preserves caller mode A.forkOK f s allocated eq | (A.connectedCommit e p k) | _ = case eq of λ ()
 step-preserves caller mode A.forkOK f s allocated eq | (A.awaitResult e p k) | _ = case eq of λ ()
 step-preserves caller mode A.forkOK f s allocated eq | (A.commitResult e k result) | _ = case eq of λ ()
 step-preserves caller mode A.forkOK f s allocated eq | (A.waitingInbound e k) | _ = case eq of λ ()
 step-preserves caller mode A.forkOK f s allocated eq | (A.closeError e err′) | _ = case eq of λ ()
 step-preserves caller mode A.forkOK f s allocated eq | (A.removeError e err′) | _ = case eq of λ ()
 step-preserves caller mode A.forkOK f s allocated eq | (A.complete result) | _ = case eq of λ ()
 step-preserves caller mode A.forkOK f s allocated eq | (A.forkHandler e p k) | just h = case eq of λ ()
 step-preserves caller mode A.commitConnected f s allocated eq with A.pc f
 ... | A.connectedCommit e p k with lookup e (entries (cm s)) in found
 ...   | nothing = case eq of λ ()
 ...   | just reservedOutbound = result-preserves eq
   allocated
 ...   | just (unnegotiated inbound _ _) = result-preserves eq
   allocated
 ...   | just old@(unnegotiated outbound _ _) = result-preserves eq allocated
 ...   | just old@(outboundUni _ _ _) = result-preserves eq allocated
 ...   | just old@(outboundDup _ _ _ _) = result-preserves eq allocated
 ...   | just old@(outboundIdle _ _ _ _) = result-preserves eq allocated
 ...   | just old@(inboundIdle _ _ _ _) = result-preserves eq allocated
 ...   | just old@(inboundActive _ _ _ _) = result-preserves eq allocated
 ...   | just old@(duplexActive _ _ _) = result-preserves eq allocated
 ...   | just old@(terminating _ _ _) = result-preserves eq allocated
 ...   | just old@(terminated _) = result-preserves eq allocated
 step-preserves caller mode A.commitConnected f s allocated eq | A.selecting = case eq of λ ()
 step-preserves caller mode A.commitConnected f s allocated eq | (A.count p) = case eq of λ ()
 step-preserves caller mode A.commitConnected f s allocated eq | (A.allocatePromise e) = case eq of λ ()
 step-preserves caller mode A.commitConnected f s allocated eq | (A.openSocket e p) = case eq of λ ()
 step-preserves caller mode A.commitConnected f s allocated eq | (A.configureSocket e p) = case eq of λ ()
 step-preserves caller mode A.commitConnected f s allocated eq | (A.bindSocket e p) = case eq of λ ()
 step-preserves caller mode A.commitConnected f s allocated eq | (A.connectSocket e p) = case eq of λ ()
 step-preserves caller mode A.commitConnected f s allocated eq | (A.localAddress e p) = case eq of λ ()
 step-preserves caller mode A.commitConnected f s allocated eq | (A.updateAddress e p k) = case eq of λ ()
 step-preserves caller mode A.commitConnected f s allocated eq | (A.forkHandler e p k) = case eq of λ ()
 step-preserves caller mode A.commitConnected f s allocated eq | (A.awaitResult e p k) = case eq of λ ()
 step-preserves caller mode A.commitConnected f s allocated eq | (A.commitResult e k result) = case eq of λ ()
 step-preserves caller mode A.commitConnected f s allocated eq | (A.waitingInbound e k) = case eq of λ ()
 step-preserves caller mode A.commitConnected f s allocated eq | (A.closeError e err′) = case eq of λ ()
 step-preserves caller mode A.commitConnected f s allocated eq | (A.removeError e err′) = case eq of λ ()
 step-preserves caller mode A.commitConnected f s allocated eq | (A.complete result) = case eq of λ ()
 step-preserves caller mode A.readResult f s allocated eq with A.pc f
 ... | A.awaitResult e p k with lookup p (handshakeResults s)
 ...   | nothing = case eq of λ ()
 ...   | just result = result-preserves eq allocated
 step-preserves caller mode A.readResult f s allocated eq | A.selecting = case eq of λ ()
 step-preserves caller mode A.readResult f s allocated eq | (A.count p) = case eq of λ ()
 step-preserves caller mode A.readResult f s allocated eq | (A.allocatePromise e) = case eq of λ ()
 step-preserves caller mode A.readResult f s allocated eq | (A.openSocket e p) = case eq of λ ()
 step-preserves caller mode A.readResult f s allocated eq | (A.configureSocket e p) = case eq of λ ()
 step-preserves caller mode A.readResult f s allocated eq | (A.bindSocket e p) = case eq of λ ()
 step-preserves caller mode A.readResult f s allocated eq | (A.connectSocket e p) = case eq of λ ()
 step-preserves caller mode A.readResult f s allocated eq | (A.localAddress e p) = case eq of λ ()
 step-preserves caller mode A.readResult f s allocated eq | (A.updateAddress e p k) = case eq of λ ()
 step-preserves caller mode A.readResult f s allocated eq | (A.forkHandler e p k) = case eq of λ ()
 step-preserves caller mode A.readResult f s allocated eq | (A.connectedCommit e p k) = case eq of λ ()
 step-preserves caller mode A.readResult f s allocated eq | (A.commitResult e k result) = case eq of λ ()
 step-preserves caller mode A.readResult f s allocated eq | (A.waitingInbound e k) = case eq of λ ()
 step-preserves caller mode A.readResult f s allocated eq | (A.closeError e err′) = case eq of λ ()
 step-preserves caller mode A.readResult f s allocated eq | (A.removeError e err′) = case eq of λ ()
 step-preserves caller mode A.readResult f s allocated eq | (A.complete result) = case eq of λ ()
 step-preserves caller mode A.commitHandshake f s allocated eq with A.pc f
 ... | A.commitResult e k (negotiated h flow) = success-preserves mode e k h flow f s allocated eq
 ... | A.commitResult e k query = error-preserves e k handshakeQuery f s allocated eq
 ... | A.commitResult e k (handlerError cls err) = error-preserves e k (handshakeError cls err) f s allocated eq
 step-preserves caller mode A.commitHandshake f s allocated eq | A.selecting = case eq of λ ()
 step-preserves caller mode A.commitHandshake f s allocated eq | (A.count p) = case eq of λ ()
 step-preserves caller mode A.commitHandshake f s allocated eq | (A.allocatePromise e) = case eq of λ ()
 step-preserves caller mode A.commitHandshake f s allocated eq | (A.openSocket e p) = case eq of λ ()
 step-preserves caller mode A.commitHandshake f s allocated eq | (A.configureSocket e p) = case eq of λ ()
 step-preserves caller mode A.commitHandshake f s allocated eq | (A.bindSocket e p) = case eq of λ ()
 step-preserves caller mode A.commitHandshake f s allocated eq | (A.connectSocket e p) = case eq of λ ()
 step-preserves caller mode A.commitHandshake f s allocated eq | (A.localAddress e p) = case eq of λ ()
 step-preserves caller mode A.commitHandshake f s allocated eq | (A.updateAddress e p k) = case eq of λ ()
 step-preserves caller mode A.commitHandshake f s allocated eq | (A.forkHandler e p k) = case eq of λ ()
 step-preserves caller mode A.commitHandshake f s allocated eq | (A.connectedCommit e p k) = case eq of λ ()
 step-preserves caller mode A.commitHandshake f s allocated eq | (A.awaitResult e p k) = case eq of λ ()
 step-preserves caller mode A.commitHandshake f s allocated eq | (A.waitingInbound e k) = case eq of λ ()
 step-preserves caller mode A.commitHandshake f s allocated eq | (A.closeError e err′) = case eq of λ ()
 step-preserves caller mode A.commitHandshake f s allocated eq | (A.removeError e err′) = case eq of λ ()
 step-preserves caller mode A.commitHandshake f s allocated eq | (A.complete result) = case eq of λ ()
 step-preserves caller mode A.waitNegotiated f s allocated eq with A.pc f
 ... | A.waitingInbound e k with lookup e (entries (cm s)) in found
 ...   | nothing = case eq of λ ()
 ...   | just st = choice-preserves false e (C.waitCase k st) f s  allocated eq
 step-preserves caller mode A.waitNegotiated f s allocated eq | A.selecting = case eq of λ ()
 step-preserves caller mode A.waitNegotiated f s allocated eq | (A.count p) = case eq of λ ()
 step-preserves caller mode A.waitNegotiated f s allocated eq | (A.allocatePromise e) = case eq of λ ()
 step-preserves caller mode A.waitNegotiated f s allocated eq | (A.openSocket e p) = case eq of λ ()
 step-preserves caller mode A.waitNegotiated f s allocated eq | (A.configureSocket e p) = case eq of λ ()
 step-preserves caller mode A.waitNegotiated f s allocated eq | (A.bindSocket e p) = case eq of λ ()
 step-preserves caller mode A.waitNegotiated f s allocated eq | (A.connectSocket e p) = case eq of λ ()
 step-preserves caller mode A.waitNegotiated f s allocated eq | (A.localAddress e p) = case eq of λ ()
 step-preserves caller mode A.waitNegotiated f s allocated eq | (A.updateAddress e p k) = case eq of λ ()
 step-preserves caller mode A.waitNegotiated f s allocated eq | (A.forkHandler e p k) = case eq of λ ()
 step-preserves caller mode A.waitNegotiated f s allocated eq | (A.connectedCommit e p k) = case eq of λ ()
 step-preserves caller mode A.waitNegotiated f s allocated eq | (A.awaitResult e p k) = case eq of λ ()
 step-preserves caller mode A.waitNegotiated f s allocated eq | (A.commitResult e k result) = case eq of λ ()
 step-preserves caller mode A.waitNegotiated f s allocated eq | (A.closeError e err′) = case eq of λ ()
 step-preserves caller mode A.waitNegotiated f s allocated eq | (A.removeError e err′) = case eq of λ ()
 step-preserves caller mode A.waitNegotiated f s allocated eq | (A.complete result) = case eq of λ ()
 step-preserves caller mode (A.failIO err) f s allocated eq with A.pc f
 ... | A.openSocket e p = result-preserves eq allocated
 ... | A.configureSocket e p = result-preserves eq allocated
 ... | A.bindSocket e p = result-preserves eq allocated
 ... | A.connectSocket e p = result-preserves eq allocated
 ... | A.localAddress e p = result-preserves eq allocated
 ... | A.forkHandler e p k = result-preserves eq allocated
 step-preserves caller mode (A.failIO err) f s allocated eq | A.selecting = case eq of λ ()
 step-preserves caller mode (A.failIO err) f s allocated eq | (A.count p) = case eq of λ ()
 step-preserves caller mode (A.failIO err) f s allocated eq | (A.allocatePromise e) = case eq of λ ()
 step-preserves caller mode (A.failIO err) f s allocated eq | (A.updateAddress e p k) = case eq of λ ()
 step-preserves caller mode (A.failIO err) f s allocated eq | (A.connectedCommit e p k) = case eq of λ ()
 step-preserves caller mode (A.failIO err) f s allocated eq | (A.awaitResult e p k) = case eq of λ ()
 step-preserves caller mode (A.failIO err) f s allocated eq | (A.commitResult e k result) = case eq of λ ()
 step-preserves caller mode (A.failIO err) f s allocated eq | (A.waitingInbound e k) = case eq of λ ()
 step-preserves caller mode (A.failIO err) f s allocated eq | (A.closeError e err′) = case eq of λ ()
 step-preserves caller mode (A.failIO err) f s allocated eq | (A.removeError e err′) = case eq of λ ()
 step-preserves caller mode (A.failIO err) f s allocated eq | (A.complete result) = case eq of λ ()
 step-preserves caller mode A.closeOK f s allocated eq with A.pc f
 ... | A.closeError e err = result-preserves eq allocated
 step-preserves caller mode A.closeOK f s allocated eq | A.selecting = case eq of λ ()
 step-preserves caller mode A.closeOK f s allocated eq | (A.count p) = case eq of λ ()
 step-preserves caller mode A.closeOK f s allocated eq | (A.allocatePromise e) = case eq of λ ()
 step-preserves caller mode A.closeOK f s allocated eq | (A.openSocket e p) = case eq of λ ()
 step-preserves caller mode A.closeOK f s allocated eq | (A.configureSocket e p) = case eq of λ ()
 step-preserves caller mode A.closeOK f s allocated eq | (A.bindSocket e p) = case eq of λ ()
 step-preserves caller mode A.closeOK f s allocated eq | (A.connectSocket e p) = case eq of λ ()
 step-preserves caller mode A.closeOK f s allocated eq | (A.localAddress e p) = case eq of λ ()
 step-preserves caller mode A.closeOK f s allocated eq | (A.updateAddress e p k) = case eq of λ ()
 step-preserves caller mode A.closeOK f s allocated eq | (A.forkHandler e p k) = case eq of λ ()
 step-preserves caller mode A.closeOK f s allocated eq | (A.connectedCommit e p k) = case eq of λ ()
 step-preserves caller mode A.closeOK f s allocated eq | (A.awaitResult e p k) = case eq of λ ()
 step-preserves caller mode A.closeOK f s allocated eq | (A.commitResult e k result) = case eq of λ ()
 step-preserves caller mode A.closeOK f s allocated eq | (A.waitingInbound e k) = case eq of λ ()
 step-preserves caller mode A.closeOK f s allocated eq | (A.removeError e err′) = case eq of λ ()
 step-preserves caller mode A.closeOK f s allocated eq | (A.complete result) = case eq of λ ()
 step-preserves caller mode (A.closeFailed err) f s allocated eq with A.pc f
 ... | A.closeError e _ = result-preserves eq allocated
 step-preserves caller mode (A.closeFailed err) f s allocated eq | A.selecting = case eq of λ ()
 step-preserves caller mode (A.closeFailed err) f s allocated eq | (A.count p) = case eq of λ ()
 step-preserves caller mode (A.closeFailed err) f s allocated eq | (A.allocatePromise e) = case eq of λ ()
 step-preserves caller mode (A.closeFailed err) f s allocated eq | (A.openSocket e p) = case eq of λ ()
 step-preserves caller mode (A.closeFailed err) f s allocated eq | (A.configureSocket e p) = case eq of λ ()
 step-preserves caller mode (A.closeFailed err) f s allocated eq | (A.bindSocket e p) = case eq of λ ()
 step-preserves caller mode (A.closeFailed err) f s allocated eq | (A.connectSocket e p) = case eq of λ ()
 step-preserves caller mode (A.closeFailed err) f s allocated eq | (A.localAddress e p) = case eq of λ ()
 step-preserves caller mode (A.closeFailed err) f s allocated eq | (A.updateAddress e p k) = case eq of λ ()
 step-preserves caller mode (A.closeFailed err) f s allocated eq | (A.forkHandler e p k) = case eq of λ ()
 step-preserves caller mode (A.closeFailed err) f s allocated eq | (A.connectedCommit e p k) = case eq of λ ()
 step-preserves caller mode (A.closeFailed err) f s allocated eq | (A.awaitResult e p k) = case eq of λ ()
 step-preserves caller mode (A.closeFailed err) f s allocated eq | (A.commitResult e k result) = case eq of λ ()
 step-preserves caller mode (A.closeFailed err) f s allocated eq | (A.waitingInbound e k) = case eq of λ ()
 step-preserves caller mode (A.closeFailed err) f s allocated eq | (A.removeError e err′) = case eq of λ ()
 step-preserves caller mode (A.closeFailed err) f s allocated eq | (A.complete result) = case eq of λ ()
 step-preserves caller mode A.removeReservation f s allocated eq with A.pc f | mapCell (cm s)
 ... | A.removeError e err | full m = result-preserves eq allocated
 step-preserves caller mode A.removeReservation f s allocated eq | A.selecting | _ = case eq of λ ()
 step-preserves caller mode A.removeReservation f s allocated eq | (A.count p) | _ = case eq of λ ()
 step-preserves caller mode A.removeReservation f s allocated eq | (A.allocatePromise e) | _ = case eq of λ ()
 step-preserves caller mode A.removeReservation f s allocated eq | (A.openSocket e p) | _ = case eq of λ ()
 step-preserves caller mode A.removeReservation f s allocated eq | (A.configureSocket e p) | _ = case eq of λ ()
 step-preserves caller mode A.removeReservation f s allocated eq | (A.bindSocket e p) | _ = case eq of λ ()
 step-preserves caller mode A.removeReservation f s allocated eq | (A.connectSocket e p) | _ = case eq of λ ()
 step-preserves caller mode A.removeReservation f s allocated eq | (A.localAddress e p) | _ = case eq of λ ()
 step-preserves caller mode A.removeReservation f s allocated eq | (A.updateAddress e p k) | _ = case eq of λ ()
 step-preserves caller mode A.removeReservation f s allocated eq | (A.forkHandler e p k) | _ = case eq of λ ()
 step-preserves caller mode A.removeReservation f s allocated eq | (A.connectedCommit e p k) | _ = case eq of λ ()
 step-preserves caller mode A.removeReservation f s allocated eq | (A.awaitResult e p k) | _ = case eq of λ ()
 step-preserves caller mode A.removeReservation f s allocated eq | (A.commitResult e k result) | _ = case eq of λ ()
 step-preserves caller mode A.removeReservation f s allocated eq | (A.waitingInbound e k) | _ = case eq of λ ()
 step-preserves caller mode A.removeReservation f s allocated eq | (A.closeError e err′) | _ = case eq of λ ()
 step-preserves caller mode A.removeReservation f s allocated eq | (A.complete result) | _ = case eq of λ ()
 step-preserves caller mode A.removeReservation f s allocated eq | (A.removeError e err′) | taken w = case eq of λ ()
 step-preserves caller mode A.returnResult f s allocated ()

-- Release and pruning keep the promise list through all branch outcomes.
module ReleasePart where
 open import Data.Bool using (true; false)
 open import Data.Nat using (suc; _<_; _≤?_; _∸_)
 open import Data.List using ([]; _∷_; map)
 open import Data.Maybe using (just; nothing)
 open import Data.Maybe.Properties using (just-injective)
 open import Data.Product using (_×_; _,_; proj₁; proj₂)
 open import Relation.Nullary using (yes; no)
 open import Relation.Binary.PropositionalEquality using (_≡_; subst)
 open import Function using (case_of_)
 open import Class.DecEq using (_≟_)
 open import ConnectionManagement.Store using (lookup)
 import ConnectionManagement.Rules.OutboundRelease as R
 import ConnectionManagement.Rules.Pruning as P

 -- Transport membership along equality of exact successful results.
 result-preserves : ∀ {pair pair′ : R.Frame × State} → just pair ≡ just pair′ →
   Allocated (proj₂ pair) → Allocated (proj₂ pair′)
 result-preserves eq = subst (λ pair → Allocated (proj₂ pair)) (just-injective eq)

 -- Release branch replacement changes only the chosen entry.
 apply-preserves : ∀ e d f s → Allocated s →
   Allocated (proj₂ (R.apply e d f s))
 apply-preserves e d f s allocated with R.replacement d
 ... | nothing = allocated
 ... | just st = allocated

 -- Capacity pruning composes the checked entry-only edit effects.
 capacity-preserves : ∀ limit scores m e old d f s {out} →
   Allocated s →
   R.capacity limit scores m e old d f s ≡ just out → Allocated (proj₂ out)
 capacity-preserves limit scores m e old d f s allocated eq with R.needsCapacity d
 ... | false with scores
 ...   | nothing = result-preserves eq (apply-preserves e d f s allocated)
 ...   | just _ = case eq of λ ()
 capacity-preserves limit scores m e old d f s allocated eq | true with countIncoming (entries (cm s)) m
 ... | nothing = case eq of λ ()
 ... | just n with suc n ≤? limit
 ...   | yes _ with scores
 ...     | nothing = result-preserves eq (apply-preserves e d f s allocated)
 ...     | just _ = case eq of λ ()
 capacity-preserves limit scores m e old d f s allocated eq | true | just n | no _
   with scores | R.replacement d | P.candidates m (entries (cm s))
 ... | just draws | just st | just candidates with P.candidateFor (R.key f) e st
 ...   | nothing = case eq of λ ()
 ...   | just self with P.makePlan (suc n ∸ limit) self st candidates draws
 ...     | nothing = case eq of λ ()
 ...     | just selectedPlan with P.applyEdits (map (λ c → P.entryRef c , terminated nothing) (P.victims selectedPlan)) s in edited
 ...       | nothing = case eq of λ ()
 ...       | just s′ = result-preserves eq
   (Inbound.prune-edits-preserves
     (map (λ c → P.entryRef c , terminated nothing) (P.victims selectedPlan)) s edited allocated)
 capacity-preserves limit scores m e old d f s allocated eq | true | just n | no _ | nothing | _ | _ = case eq of λ ()
 capacity-preserves limit scores m e old d f s allocated eq | true | just n | no _ | just _ | nothing | _ = case eq of λ ()
 capacity-preserves limit scores m e old d f s allocated eq | true | just n | no _ | just _ | just _ | nothing = case eq of λ ()

 -- Release transaction selection delegates to its actual branch.
 transact-preserves : ∀ limit scores f s {out} → Allocated s →
   R.transact limit scores f s ≡ just out → Allocated (proj₂ out)
 transact-preserves limit scores f s allocated eq with mapCell (cm s)
 ... | taken _ = case eq of λ ()
 ... | full m with lookupConnection (R.key f) m
 ...   | nothing with scores
 ...     | nothing = result-preserves eq allocated
 ...     | just _ = case eq of λ ()
 transact-preserves limit scores f s allocated eq | full m | just e with lookup e (entries (cm s)) in found
 ... | nothing = case eq of λ ()
 ... | just st = capacity-preserves limit scores m e st (R.branch (R.key f) e st) f s
    allocated eq

 -- Every enabled primitive step retains the observed promise.
 step-preserves : ∀ limit action f s {out} → Allocated s →
   R.step limit action f s ≡ just out → Allocated (proj₂ out)
 step-preserves limit R.transactionStep f s allocated eq with R.pc f
 ... | R.transaction = transact-preserves limit nothing f s allocated eq
 step-preserves limit R.transactionStep f s allocated eq | (R.check flag p) = case eq of λ ()
 step-preserves limit R.transactionStep f s allocated eq | (R.count p) = case eq of λ ()
 step-preserves limit R.transactionStep f s allocated eq | (R.armTimer e v) = case eq of λ ()
 step-preserves limit R.transactionStep f s allocated eq | (R.waitIdle e v) = case eq of λ ()
 step-preserves limit R.transactionStep f s allocated eq | (R.timeoutWrite e v) = case eq of λ ()
 step-preserves limit R.transactionStep f s allocated eq | (R.cancel v p) = case eq of λ ()
 step-preserves limit R.transactionStep f s allocated eq | (R.delivering v p) = case eq of λ ()
 step-preserves limit R.transactionStep f s allocated eq | (R.prune victims result) = case eq of λ ()
 step-preserves limit R.transactionStep f s allocated eq | (R.complete result) = case eq of λ ()
 step-preserves limit (R.transactionPruning scores) f s allocated eq with R.pc f
 ... | R.transaction = transact-preserves limit (just scores) f s allocated eq
 step-preserves limit (R.transactionPruning scores) f s allocated eq | (R.check flag p) = case eq of λ ()
 step-preserves limit (R.transactionPruning scores) f s allocated eq | (R.count p) = case eq of λ ()
 step-preserves limit (R.transactionPruning scores) f s allocated eq | (R.armTimer e v) = case eq of λ ()
 step-preserves limit (R.transactionPruning scores) f s allocated eq | (R.waitIdle e v) = case eq of λ ()
 step-preserves limit (R.transactionPruning scores) f s allocated eq | (R.timeoutWrite e v) = case eq of λ ()
 step-preserves limit (R.transactionPruning scores) f s allocated eq | (R.cancel v p) = case eq of λ ()
 step-preserves limit (R.transactionPruning scores) f s allocated eq | (R.delivering v p) = case eq of λ ()
 step-preserves limit (R.transactionPruning scores) f s allocated eq | (R.prune victims result) = case eq of λ ()
 step-preserves limit (R.transactionPruning scores) f s allocated eq | (R.complete result) = case eq of λ ()
 step-preserves limit R.checkAssertion f s allocated eq with R.pc f
 ... | R.check true next = result-preserves eq allocated
 ... | R.check false next = result-preserves eq allocated
 step-preserves limit R.checkAssertion f s allocated eq | (R.transaction) = case eq of λ ()
 step-preserves limit R.checkAssertion f s allocated eq | (R.count p) = case eq of λ ()
 step-preserves limit R.checkAssertion f s allocated eq | (R.armTimer e v) = case eq of λ ()
 step-preserves limit R.checkAssertion f s allocated eq | (R.waitIdle e v) = case eq of λ ()
 step-preserves limit R.checkAssertion f s allocated eq | (R.timeoutWrite e v) = case eq of λ ()
 step-preserves limit R.checkAssertion f s allocated eq | (R.cancel v p) = case eq of λ ()
 step-preserves limit R.checkAssertion f s allocated eq | (R.delivering v p) = case eq of λ ()
 step-preserves limit R.checkAssertion f s allocated eq | (R.prune victims result) = case eq of λ ()
 step-preserves limit R.checkAssertion f s allocated eq | (R.complete result) = case eq of λ ()
 step-preserves limit R.readCounters f s allocated eq with R.pc f | mapCell (cm s)
 ... | R.count next | full m with countIncoming (entries (cm s)) m
 ...   | nothing = case eq of λ ()
 ...   | just _ = result-preserves eq allocated
 step-preserves limit R.readCounters f s allocated eq | (R.transaction) | _ = case eq of λ ()
 step-preserves limit R.readCounters f s allocated eq | (R.check flag p) | _ = case eq of λ ()
 step-preserves limit R.readCounters f s allocated eq | (R.armTimer e v) | _ = case eq of λ ()
 step-preserves limit R.readCounters f s allocated eq | (R.waitIdle e v) | _ = case eq of λ ()
 step-preserves limit R.readCounters f s allocated eq | (R.timeoutWrite e v) | _ = case eq of λ ()
 step-preserves limit R.readCounters f s allocated eq | (R.cancel v p) | _ = case eq of λ ()
 step-preserves limit R.readCounters f s allocated eq | (R.delivering v p) | _ = case eq of λ ()
 step-preserves limit R.readCounters f s allocated eq | (R.prune victims result) | _ = case eq of λ ()
 step-preserves limit R.readCounters f s allocated eq | (R.complete result) | _ = case eq of λ ()
 step-preserves limit R.readCounters f s allocated eq | (R.count p) | taken w = case eq of λ ()
 step-preserves limit R.registerTimer f s allocated eq with R.pc f
 ... | R.armTimer e w = result-preserves eq allocated
 step-preserves limit R.registerTimer f s allocated eq | (R.transaction) = case eq of λ ()
 step-preserves limit R.registerTimer f s allocated eq | (R.check flag p) = case eq of λ ()
 step-preserves limit R.registerTimer f s allocated eq | (R.count p) = case eq of λ ()
 step-preserves limit R.registerTimer f s allocated eq | (R.waitIdle e v) = case eq of λ ()
 step-preserves limit R.registerTimer f s allocated eq | (R.timeoutWrite e v) = case eq of λ ()
 step-preserves limit R.registerTimer f s allocated eq | (R.cancel v p) = case eq of λ ()
 step-preserves limit R.registerTimer f s allocated eq | (R.delivering v p) = case eq of λ ()
 step-preserves limit R.registerTimer f s allocated eq | (R.prune victims result) = case eq of λ ()
 step-preserves limit R.registerTimer f s allocated eq | (R.complete result) = case eq of λ ()
 step-preserves limit R.expireTimer f s allocated eq with R.pc f | R.timerReady f
 ... | R.waitIdle e w | false = result-preserves eq allocated
 step-preserves limit R.expireTimer f s allocated eq | (R.transaction) | _ = case eq of λ ()
 step-preserves limit R.expireTimer f s allocated eq | (R.check flag p) | _ = case eq of λ ()
 step-preserves limit R.expireTimer f s allocated eq | (R.count p) | _ = case eq of λ ()
 step-preserves limit R.expireTimer f s allocated eq | (R.armTimer e v) | _ = case eq of λ ()
 step-preserves limit R.expireTimer f s allocated eq | (R.timeoutWrite e v) | _ = case eq of λ ()
 step-preserves limit R.expireTimer f s allocated eq | (R.cancel v p) | _ = case eq of λ ()
 step-preserves limit R.expireTimer f s allocated eq | (R.delivering v p) | _ = case eq of λ ()
 step-preserves limit R.expireTimer f s allocated eq | (R.prune victims result) | _ = case eq of λ ()
 step-preserves limit R.expireTimer f s allocated eq | (R.complete result) | _ = case eq of λ ()
 step-preserves limit R.expireTimer f s allocated eq | (R.waitIdle e v) | true = case eq of λ ()
 step-preserves limit R.selectWakeup f s allocated eq with R.pc f
 ... | R.waitIdle e w with lookup e (entries (cm s)) in found
 ...   | nothing = case eq of λ ()
 ...   | just st with R.isIdle st | R.isTerminated st | R.timerReady f
 ...     | false | true | _ = result-preserves eq allocated
 ...     | false | false | _ = result-preserves eq allocated
 ...     | true | _ | true = result-preserves eq allocated
 ...     | true | _ | false = case eq of λ ()
 step-preserves limit R.selectWakeup f s allocated eq | (R.transaction) = case eq of λ ()
 step-preserves limit R.selectWakeup f s allocated eq | (R.check flag p) = case eq of λ ()
 step-preserves limit R.selectWakeup f s allocated eq | (R.count p) = case eq of λ ()
 step-preserves limit R.selectWakeup f s allocated eq | (R.armTimer e v) = case eq of λ ()
 step-preserves limit R.selectWakeup f s allocated eq | (R.timeoutWrite e v) = case eq of λ ()
 step-preserves limit R.selectWakeup f s allocated eq | (R.cancel v p) = case eq of λ ()
 step-preserves limit R.selectWakeup f s allocated eq | (R.delivering v p) = case eq of λ ()
 step-preserves limit R.selectWakeup f s allocated eq | (R.prune victims result) = case eq of λ ()
 step-preserves limit R.selectWakeup f s allocated eq | (R.complete result) = case eq of λ ()
 step-preserves limit R.commitTimeout f s allocated eq with R.pc f
 ... | R.timeoutWrite e w with lookup e (entries (cm s)) in found
 ...   | nothing = case eq of λ ()
 ...   | just _ = result-preserves eq
   allocated
 step-preserves limit R.commitTimeout f s allocated eq | (R.transaction) = case eq of λ ()
 step-preserves limit R.commitTimeout f s allocated eq | (R.check flag p) = case eq of λ ()
 step-preserves limit R.commitTimeout f s allocated eq | (R.count p) = case eq of λ ()
 step-preserves limit R.commitTimeout f s allocated eq | (R.armTimer e v) = case eq of λ ()
 step-preserves limit R.commitTimeout f s allocated eq | (R.waitIdle e v) = case eq of λ ()
 step-preserves limit R.commitTimeout f s allocated eq | (R.cancel v p) = case eq of λ ()
 step-preserves limit R.commitTimeout f s allocated eq | (R.delivering v p) = case eq of λ ()
 step-preserves limit R.commitTimeout f s allocated eq | (R.prune victims result) = case eq of λ ()
 step-preserves limit R.commitTimeout f s allocated eq | (R.complete result) = case eq of λ ()
 step-preserves limit R.requestCancellation f s allocated eq with R.pc f
 ... | R.cancel w next = result-preserves eq allocated
 ... | R.prune [] result = result-preserves eq allocated
 ... | R.prune (victim ∷ rest) result = result-preserves eq allocated
 step-preserves limit R.requestCancellation f s allocated eq | (R.transaction) = case eq of λ ()
 step-preserves limit R.requestCancellation f s allocated eq | (R.check flag p) = case eq of λ ()
 step-preserves limit R.requestCancellation f s allocated eq | (R.count p) = case eq of λ ()
 step-preserves limit R.requestCancellation f s allocated eq | (R.armTimer e v) = case eq of λ ()
 step-preserves limit R.requestCancellation f s allocated eq | (R.waitIdle e v) = case eq of λ ()
 step-preserves limit R.requestCancellation f s allocated eq | (R.timeoutWrite e v) = case eq of λ ()
 step-preserves limit R.requestCancellation f s allocated eq | (R.delivering v p) = case eq of λ ()
 step-preserves limit R.requestCancellation f s allocated eq | (R.complete result) = case eq of λ ()
 step-preserves limit (R.cancellationDelivered w) f s allocated eq with R.pc f
 ... | R.delivering v next with w ≟ v
 ...   | yes _ = result-preserves eq allocated
 ...   | no _ = case eq of λ ()
 step-preserves limit (R.cancellationDelivered w) f s allocated eq | (R.transaction) = case eq of λ ()
 step-preserves limit (R.cancellationDelivered w) f s allocated eq | (R.check flag p) = case eq of λ ()
 step-preserves limit (R.cancellationDelivered w) f s allocated eq | (R.count p) = case eq of λ ()
 step-preserves limit (R.cancellationDelivered w) f s allocated eq | (R.armTimer e v) = case eq of λ ()
 step-preserves limit (R.cancellationDelivered w) f s allocated eq | (R.waitIdle e v) = case eq of λ ()
 step-preserves limit (R.cancellationDelivered w) f s allocated eq | (R.timeoutWrite e v) = case eq of λ ()
 step-preserves limit (R.cancellationDelivered w) f s allocated eq | (R.cancel v p) = case eq of λ ()
 step-preserves limit (R.cancellationDelivered w) f s allocated eq | (R.prune victims result) = case eq of λ ()
 step-preserves limit (R.cancellationDelivered w) f s allocated eq | (R.complete result) = case eq of λ ()
 step-preserves limit R.returnResult f s allocated ()

-- The source-machine induction needs no capture or allocation-bound premise.
module Outbound where
 open import Data.Bool using (true; false)
 open import Data.Maybe using (just; nothing)
 open import Data.Maybe.Properties using (just-injective)
 open import Data.Product using (_×_; _,_; proj₁; proj₂)
 open import Relation.Binary.PropositionalEquality using (_≡_; subst)
 open import Function using (case_of_)
 import ConnectionManagement.State as S
 import ConnectionManagement.Machine as I
 open import ConnectionManagement.OutboundMachine using
   (Configuration; core; acquiring; releasing; advanceAcquire; advanceRelease; inbound;
    beginAcquire; acquire; beginRelease; release; canDeliver; advance; initial; Executes; done; next)
 open import ConnectionManagement.Store using (lookup)

 import ConnectionManagement.Rules.OutboundAcquire as A
 import ConnectionManagement.Rules.OutboundRelease as R

 -- Observe membership in the source machine shared world.
 Held : Configuration → Set
 Held c = Allocated (I.world (core c))

 -- Ignore pending callers when lifting this world-only predicate.
 RuntimeValid : A.Runtime → S.State → Set
 RuntimeValid rt s = Allocated s

 -- Use the same world-only predicate for the combined source dispatcher.
 Valid : Configuration → Set
 Valid c = RuntimeValid (acquiring c) (I.world (core c))

 -- The selected acquisition result retains promise membership.
 acquisition-preserves : ∀ w action c f {f′ s′} →
   lookup w (acquiring c) ≡ just f →
   A.step w (I.responder (core c)) action f (I.world (core c)) ≡ just (f′ , s′) →
   Held c → Allocated s′
 acquisition-preserves w action c f found stepped allocated =
   Acquire.step-preserves w (I.responder (core c)) action f (I.world (core c))
     allocated stepped

 -- Acquisition return changes caller bookkeeping; other actions use their primitive result.
 acquire-preserves : ∀ w action c {c′} → advanceAcquire w action c ≡ just c′ →
   Held c → Held c′
 acquire-preserves w A.returnResult c eq allocated with lookup w (acquiring c)
 ... | nothing = case eq of λ ()
 ... | just f with A.pc f
 ...   | A.complete result = subst Held (just-injective eq)
   allocated
 ...   | A.selecting = case eq of λ ()
 ...   | A.count p = case eq of λ ()
 ...   | A.allocatePromise e = case eq of λ ()
 ...   | A.openSocket e p = case eq of λ ()
 ...   | A.configureSocket e p = case eq of λ ()
 ...   | A.bindSocket e p = case eq of λ ()
 ...   | A.connectSocket e p = case eq of λ ()
 ...   | A.localAddress e p = case eq of λ ()
 ...   | A.updateAddress e p k = case eq of λ ()
 ...   | A.forkHandler e p k = case eq of λ ()
 ...   | A.connectedCommit e p k = case eq of λ ()
 ...   | A.awaitResult e p k = case eq of λ ()
 ...   | A.commitResult e k result = case eq of λ ()
 ...   | A.waitingInbound e k = case eq of λ ()
 ...   | A.closeError e err = case eq of λ ()
 ...   | A.removeError e err = case eq of λ ()
 acquire-preserves w (A.select chosen) c eq allocated with lookup w (acquiring c) in found
 ... | nothing = case eq of λ ()
 ... | just f with A.step w (I.responder (core c)) (A.select chosen) f (I.world (core c)) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , s′) = subst Held (just-injective eq)
   (acquisition-preserves w (A.select chosen) c f found stepped allocated)
 acquire-preserves w (A.readCounters) c eq allocated with lookup w (acquiring c) in found
 ... | nothing = case eq of λ ()
 ... | just f with A.step w (I.responder (core c)) (A.readCounters) f (I.world (core c)) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , s′) = subst Held (just-injective eq)
   (acquisition-preserves w (A.readCounters) c f found stepped allocated)
 acquire-preserves w (A.newPromise) c eq allocated with lookup w (acquiring c) in found
 ... | nothing = case eq of λ ()
 ... | just f with A.step w (I.responder (core c)) (A.newPromise) f (I.world (core c)) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , s′) = subst Held (just-injective eq)
   (acquisition-preserves w (A.newPromise) c f found stepped allocated)
 acquire-preserves w (A.openOK) c eq allocated with lookup w (acquiring c) in found
 ... | nothing = case eq of λ ()
 ... | just f with A.step w (I.responder (core c)) (A.openOK) f (I.world (core c)) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , s′) = subst Held (just-injective eq)
   (acquisition-preserves w (A.openOK) c f found stepped allocated)
 acquire-preserves w (A.configureOK) c eq allocated with lookup w (acquiring c) in found
 ... | nothing = case eq of λ ()
 ... | just f with A.step w (I.responder (core c)) (A.configureOK) f (I.world (core c)) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , s′) = subst Held (just-injective eq)
   (acquisition-preserves w (A.configureOK) c f found stepped allocated)
 acquire-preserves w (A.bindOK) c eq allocated with lookup w (acquiring c) in found
 ... | nothing = case eq of λ ()
 ... | just f with A.step w (I.responder (core c)) (A.bindOK) f (I.world (core c)) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , s′) = subst Held (just-injective eq)
   (acquisition-preserves w (A.bindOK) c f found stepped allocated)
 acquire-preserves w (A.connectOK) c eq allocated with lookup w (acquiring c) in found
 ... | nothing = case eq of λ ()
 ... | just f with A.step w (I.responder (core c)) (A.connectOK) f (I.world (core c)) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , s′) = subst Held (just-injective eq)
   (acquisition-preserves w (A.connectOK) c f found stepped allocated)
 acquire-preserves w (A.gotLocal local) c eq allocated with lookup w (acquiring c) in found
 ... | nothing = case eq of λ ()
 ... | just f with A.step w (I.responder (core c)) (A.gotLocal local) f (I.world (core c)) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , s′) = subst Held (just-injective eq)
   (acquisition-preserves w (A.gotLocal local) c f found stepped allocated)
 acquire-preserves w (A.updateLocalAddress) c eq allocated with lookup w (acquiring c) in found
 ... | nothing = case eq of λ ()
 ... | just f with A.step w (I.responder (core c)) (A.updateLocalAddress) f (I.world (core c)) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , s′) = subst Held (just-injective eq)
   (acquisition-preserves w (A.updateLocalAddress) c f found stepped allocated)
 acquire-preserves w (A.forkOK) c eq allocated with lookup w (acquiring c) in found
 ... | nothing = case eq of λ ()
 ... | just f with A.step w (I.responder (core c)) (A.forkOK) f (I.world (core c)) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , s′) = subst Held (just-injective eq)
   (acquisition-preserves w (A.forkOK) c f found stepped allocated)
 acquire-preserves w (A.commitConnected) c eq allocated with lookup w (acquiring c) in found
 ... | nothing = case eq of λ ()
 ... | just f with A.step w (I.responder (core c)) (A.commitConnected) f (I.world (core c)) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , s′) = subst Held (just-injective eq)
   (acquisition-preserves w (A.commitConnected) c f found stepped allocated)
 acquire-preserves w (A.readResult) c eq allocated with lookup w (acquiring c) in found
 ... | nothing = case eq of λ ()
 ... | just f with A.step w (I.responder (core c)) (A.readResult) f (I.world (core c)) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , s′) = subst Held (just-injective eq)
   (acquisition-preserves w (A.readResult) c f found stepped allocated)
 acquire-preserves w (A.commitHandshake) c eq allocated with lookup w (acquiring c) in found
 ... | nothing = case eq of λ ()
 ... | just f with A.step w (I.responder (core c)) (A.commitHandshake) f (I.world (core c)) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , s′) = subst Held (just-injective eq)
   (acquisition-preserves w (A.commitHandshake) c f found stepped allocated)
 acquire-preserves w (A.failIO err) c eq allocated with lookup w (acquiring c) in found
 ... | nothing = case eq of λ ()
 ... | just f with A.step w (I.responder (core c)) (A.failIO err) f (I.world (core c)) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , s′) = subst Held (just-injective eq)
   (acquisition-preserves w (A.failIO err) c f found stepped allocated)
 acquire-preserves w (A.closeFailed err) c eq allocated with lookup w (acquiring c) in found
 ... | nothing = case eq of λ ()
 ... | just f with A.step w (I.responder (core c)) (A.closeFailed err) f (I.world (core c)) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , s′) = subst Held (just-injective eq)
   (acquisition-preserves w (A.closeFailed err) c f found stepped allocated)
 acquire-preserves w (A.closeOK) c eq allocated with lookup w (acquiring c) in found
 ... | nothing = case eq of λ ()
 ... | just f with A.step w (I.responder (core c)) (A.closeOK) f (I.world (core c)) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , s′) = subst Held (just-injective eq)
   (acquisition-preserves w (A.closeOK) c f found stepped allocated)
 acquire-preserves w (A.removeReservation) c eq allocated with lookup w (acquiring c) in found
 ... | nothing = case eq of λ ()
 ... | just f with A.step w (I.responder (core c)) (A.removeReservation) f (I.world (core c)) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , s′) = subst Held (just-injective eq)
   (acquisition-preserves w (A.removeReservation) c f found stepped allocated)
 acquire-preserves w (A.waitNegotiated) c eq allocated with lookup w (acquiring c) in found
 ... | nothing = case eq of λ ()
 ... | just f with A.step w (I.responder (core c)) (A.waitNegotiated) f (I.world (core c)) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , s′) = subst Held (just-injective eq)
   (acquisition-preserves w (A.waitNegotiated) c f found stepped allocated)

 -- Release return changes caller bookkeeping; other actions use their primitive result.
 release-preserves : ∀ w action c {c′} → advanceRelease w action c ≡ just c′ →
   Held c → Held c′
 release-preserves w R.returnResult c eq allocated with lookup w (releasing c)
 ... | nothing = case eq of λ ()
 ... | just f with R.pc f
 ...   | R.complete result = subst Held (just-injective eq) allocated
 ...   | R.transaction = case eq of λ ()
 ...   | R.check flag p = case eq of λ ()
 ...   | R.count p = case eq of λ ()
 ...   | R.armTimer e v = case eq of λ ()
 ...   | R.waitIdle e v = case eq of λ ()
 ...   | R.timeoutWrite e v = case eq of λ ()
 ...   | R.cancel v p = case eq of λ ()
 ...   | R.delivering v p = case eq of λ ()
 ...   | R.prune victims result = case eq of λ ()
 release-preserves w (R.transactionStep) c eq allocated with lookup w (releasing c) | canDeliver (R.transactionStep) c
 ... | nothing | _ = case eq of λ ()
 ... | just f | false = case eq of λ ()
 ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.transactionStep) f (I.world (core c)) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , s′) = subst Held (just-injective eq)
   (ReleasePart.step-preserves (I.promotionHardLimit (core c)) (R.transactionStep) f (I.world (core c)) allocated stepped)
 release-preserves w (R.transactionPruning scores) c eq allocated with lookup w (releasing c) | canDeliver (R.transactionPruning scores) c
 ... | nothing | _ = case eq of λ ()
 ... | just f | false = case eq of λ ()
 ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.transactionPruning scores) f (I.world (core c)) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , s′) = subst Held (just-injective eq)
   (ReleasePart.step-preserves (I.promotionHardLimit (core c)) (R.transactionPruning scores) f (I.world (core c)) allocated stepped)
 release-preserves w (R.checkAssertion) c eq allocated with lookup w (releasing c) | canDeliver (R.checkAssertion) c
 ... | nothing | _ = case eq of λ ()
 ... | just f | false = case eq of λ ()
 ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.checkAssertion) f (I.world (core c)) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , s′) = subst Held (just-injective eq)
   (ReleasePart.step-preserves (I.promotionHardLimit (core c)) (R.checkAssertion) f (I.world (core c)) allocated stepped)
 release-preserves w (R.readCounters) c eq allocated with lookup w (releasing c) | canDeliver (R.readCounters) c
 ... | nothing | _ = case eq of λ ()
 ... | just f | false = case eq of λ ()
 ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.readCounters) f (I.world (core c)) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , s′) = subst Held (just-injective eq)
   (ReleasePart.step-preserves (I.promotionHardLimit (core c)) (R.readCounters) f (I.world (core c)) allocated stepped)
 release-preserves w (R.registerTimer) c eq allocated with lookup w (releasing c) | canDeliver (R.registerTimer) c
 ... | nothing | _ = case eq of λ ()
 ... | just f | false = case eq of λ ()
 ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.registerTimer) f (I.world (core c)) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , s′) = subst Held (just-injective eq)
   (ReleasePart.step-preserves (I.promotionHardLimit (core c)) (R.registerTimer) f (I.world (core c)) allocated stepped)
 release-preserves w (R.expireTimer) c eq allocated with lookup w (releasing c) | canDeliver (R.expireTimer) c
 ... | nothing | _ = case eq of λ ()
 ... | just f | false = case eq of λ ()
 ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.expireTimer) f (I.world (core c)) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , s′) = subst Held (just-injective eq)
   (ReleasePart.step-preserves (I.promotionHardLimit (core c)) (R.expireTimer) f (I.world (core c)) allocated stepped)
 release-preserves w (R.selectWakeup) c eq allocated with lookup w (releasing c) | canDeliver (R.selectWakeup) c
 ... | nothing | _ = case eq of λ ()
 ... | just f | false = case eq of λ ()
 ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.selectWakeup) f (I.world (core c)) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , s′) = subst Held (just-injective eq)
   (ReleasePart.step-preserves (I.promotionHardLimit (core c)) (R.selectWakeup) f (I.world (core c)) allocated stepped)
 release-preserves w (R.commitTimeout) c eq allocated with lookup w (releasing c) | canDeliver (R.commitTimeout) c
 ... | nothing | _ = case eq of λ ()
 ... | just f | false = case eq of λ ()
 ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.commitTimeout) f (I.world (core c)) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , s′) = subst Held (just-injective eq)
   (ReleasePart.step-preserves (I.promotionHardLimit (core c)) (R.commitTimeout) f (I.world (core c)) allocated stepped)
 release-preserves w (R.requestCancellation) c eq allocated with lookup w (releasing c) | canDeliver (R.requestCancellation) c
 ... | nothing | _ = case eq of λ ()
 ... | just f | false = case eq of λ ()
 ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.requestCancellation) f (I.world (core c)) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , s′) = subst Held (just-injective eq)
   (ReleasePart.step-preserves (I.promotionHardLimit (core c)) (R.requestCancellation) f (I.world (core c)) allocated stepped)
 release-preserves w (R.cancellationDelivered v) c eq allocated with lookup w (releasing c) | canDeliver (R.cancellationDelivered v) c
 ... | nothing | _ = case eq of λ ()
 ... | just f | false = case eq of λ ()
 ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.cancellationDelivered v) f (I.world (core c)) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just (f′ , s′) = subst Held (just-injective eq)
   (ReleasePart.step-preserves (I.promotionHardLimit (core c)) (R.cancellationDelivered v) f (I.world (core c)) allocated stepped)

 -- Cover every action of the combined inbound/outbound source machine.
 advance-held : ∀ a c {c′} → advance a c ≡ just c′ →
   Held c → Held c′
 advance-held (inbound a) c eq allocated with I.advance a (core c) in stepped
 ... | nothing = case eq of λ ()
 ... | just c′ = subst Held (just-injective eq)
   (Inbound.advance-preserves a (core c) stepped allocated)
 advance-held (beginAcquire w req) c eq allocated with lookup w (acquiring c) | lookup w (releasing c)
 ... | nothing | nothing = subst Held (just-injective eq) allocated
 ... | just _ | _ = case eq of λ ()
 ... | nothing | just _ = case eq of λ ()
 advance-held (acquire w a) c = acquire-preserves w a c
 advance-held (beginRelease w key) c eq allocated with lookup w (acquiring c) | lookup w (releasing c)
 ... | nothing | nothing = subst Held (just-injective eq) allocated
 ... | just _ | _ = case eq of λ ()
 ... | nothing | just _ = case eq of λ ()
 advance-held (release w a) c eq allocated = release-preserves w a c eq allocated

 -- Successful dispatcher steps preserve the same allocated promise.
 advance-preserves : ∀ a c {c′} → advance a c ≡ just c′ → Valid c → Valid c′
 advance-preserves a c eq allocated = advance-held a c eq allocated

 -- Induction over any finite source execution.
 exec-preserves : ∀ {c actions c′} → Valid c → Executes c actions c′ → Valid c′
 exec-preserves valid done = valid
 exec-preserves valid (next {c = c} {a = a} eq rest) =
   exec-preserves (advance-preserves a c eq valid) rest

 -- The empty caller initializer retains membership supplied by its core.
 from-initial : ∀ {c actions c′} → Allocated (I.world c) →
   Executes (initial c) actions c′ → Valid c′
 from-initial {c} allocated = exec-preserves allocated
