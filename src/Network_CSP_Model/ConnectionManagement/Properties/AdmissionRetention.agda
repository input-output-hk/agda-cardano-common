{-# OPTIONS --guardedness #-}

-- Existing chains survive admission; this does not establish a new chain.
module ConnectionManagement.Properties.AdmissionRetention where

open import Data.Nat using (suc; _≤?_)
open import Data.List using (_∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.Entries using (Present; put-preserves-present)
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
open import ConnectionManagement.Properties.StateRetention
open import ConnectionManagement.Properties.IGTableRetention using (fresh-lookup)
open import ConnectionManagement.Properties.HandlerCleanup using (take-entries; put-entries)
import ConnectionManagement.Rules.Server as S
import ConnectionManagement.Rules.CM as CM

fresh-present : ∀ r c {e c′} → CM.freshInbound r c ≡ just (CM.selected e c′) →
  ∀ q → Present q (entries c) → Present q (entries c′)
fresh-present r c eq q present with lookup (ident (nextEntry c)) (entries c)
... | just _ = case eq of λ ()
... | nothing with just-injective eq
...   | refl = put-preserves-present (ident (nextEntry c)) q (unnegotiated inbound (key r) (child r)) (entries c) present

existing-present : ∀ e st r c {e′ c′} → CM.existingInbound e st r c ≡ just (CM.selected e′ c′) →
  ∀ q → Present q (entries c) → Present q (entries c′)
existing-present e reservedOutbound r c eq q present with just-injective eq
... | refl = put-preserves-present e q (unnegotiated inbound (key r) (child r)) (entries c) present
existing-present e (unnegotiated p k w) r c eq q present with just-injective eq
... | refl = put-preserves-present e q (unnegotiated inbound (key r) (child r)) (entries c) present
existing-present e (outboundUni k w h) r c () q present
existing-present e (outboundDup k w h t) r c () q present
existing-present e (outboundIdle k w h f) r c () q present
existing-present e (inboundIdle k w h f) r c () q present
existing-present e (inboundActive k w h f) r c () q present
existing-present e (duplexActive k w h) r c () q present
existing-present e (terminating k w err) r c eq q present = fresh-present r c eq q present
existing-present e (terminated err) r c eq q present = fresh-present r c eq q present

selected-present : ∀ l r c {e c′} → CM.selectInbound l r c ≡ just (CM.selected e c′) →
  ∀ q → Present q (entries c) → Present q (entries c′)
selected-present l r c eq q present with mapCell c
... | full _ = case eq of λ ()
... | taken w with owner l ≟ w
...   | no _ = case eq of λ ()
...   | yes _ with lookupConnection (key r) (savedMap l)
...     | nothing = fresh-present r c eq q present
...     | just e with lookup e (entries c)
...       | nothing = case eq of λ ()
...       | just st = existing-present e st r c eq q present

worker-retains : ∀ act w a s {s′} → S.stepWorker w a act s ≡ just s′ →
  Retains s s′
worker-retains S.take w (admissionWorker r (count l)) s ()
worker-retains S.take w (admissionWorker r (prepare l)) s ()
worker-retains S.take w (admissionWorker r (selectEntry l p)) s ()
worker-retains S.take w (admissionWorker r (forkHandler l p e)) s ()
worker-retains S.take w (admissionWorker r (publish l p e)) s ()
worker-retains S.take w (admissionWorker r (reject l reason)) s ()
worker-retains S.take w (admissionWorker r (closeSocket reason)) s ()
worker-retains S.take w (admissionWorker r (finished reason)) s ()
worker-retains S.take w (admissionWorker r (countPublished p e)) s ()
worker-retains S.take w (admissionWorker r (awaitHandshake p e)) s ()
worker-retains S.take w (admissionWorker r (commitHandshake e result)) s ()
worker-retains S.take w (admissionWorker r (countHandshake result)) s ()
worker-retains S.take w (admissionWorker r (notifyInbound info)) s ()
worker-retains S.take w (admissionWorker r (returnHandshake result)) s ()
worker-retains S.take w (admissionWorker r (completedHandshake result)) s ()
worker-retains S.take w (admissionWorker r impossibleHandshake) s ()
worker-retains S.take w a@(admissionWorker r acquireMap) s eq with CM.takeMap w (cm s) in takenEq
... | nothing = case eq of λ ()
... | just (l , c′) = subst (Retains s) (just-injective eq) (reframe _ refl refl (λ e p → subst (Present e) (sym (take-entries w (cm s) takenEq)) p) (λ _ p → p))
worker-retains S.countLimit w (admissionWorker r acquireMap) s ()
worker-retains S.countLimit w (admissionWorker r (prepare l)) s ()
worker-retains S.countLimit w (admissionWorker r (selectEntry l p)) s ()
worker-retains S.countLimit w (admissionWorker r (forkHandler l p e)) s ()
worker-retains S.countLimit w (admissionWorker r (publish l p e)) s ()
worker-retains S.countLimit w (admissionWorker r (reject l reason)) s ()
worker-retains S.countLimit w (admissionWorker r (closeSocket reason)) s ()
worker-retains S.countLimit w (admissionWorker r (finished reason)) s ()
worker-retains S.countLimit w (admissionWorker r (countPublished p e)) s ()
worker-retains S.countLimit w (admissionWorker r (awaitHandshake p e)) s ()
worker-retains S.countLimit w (admissionWorker r (commitHandshake e result)) s ()
worker-retains S.countLimit w (admissionWorker r (countHandshake result)) s ()
worker-retains S.countLimit w (admissionWorker r (notifyInbound info)) s ()
worker-retains S.countLimit w (admissionWorker r (returnHandshake result)) s ()
worker-retains S.countLimit w (admissionWorker r (completedHandshake result)) s ()
worker-retains S.countLimit w (admissionWorker r impossibleHandshake) s ()
worker-retains S.countLimit w a@(admissionWorker r (count l)) s eq with countIncoming (entries (cm s)) (savedMap l)
... | nothing = case eq of λ ()
... | just n with suc n ≤? hardLimit r
...   | yes _ = subst (Retains s) (just-injective eq) (reframe _ refl refl (λ _ p → p) (λ _ p → p))
...   | no _ = subst (Retains s) (just-injective eq) (reframe _ refl refl (λ _ p → p) (λ _ p → p))
worker-retains S.allocatePromise w (admissionWorker r acquireMap) s ()
worker-retains S.allocatePromise w (admissionWorker r (count l)) s ()
worker-retains S.allocatePromise w (admissionWorker r (selectEntry l p)) s ()
worker-retains S.allocatePromise w (admissionWorker r (forkHandler l p e)) s ()
worker-retains S.allocatePromise w (admissionWorker r (publish l p e)) s ()
worker-retains S.allocatePromise w (admissionWorker r (reject l reason)) s ()
worker-retains S.allocatePromise w (admissionWorker r (closeSocket reason)) s ()
worker-retains S.allocatePromise w (admissionWorker r (finished reason)) s ()
worker-retains S.allocatePromise w (admissionWorker r (countPublished p e)) s ()
worker-retains S.allocatePromise w (admissionWorker r (awaitHandshake p e)) s ()
worker-retains S.allocatePromise w (admissionWorker r (commitHandshake e result)) s ()
worker-retains S.allocatePromise w (admissionWorker r (countHandshake result)) s ()
worker-retains S.allocatePromise w (admissionWorker r (notifyInbound info)) s ()
worker-retains S.allocatePromise w (admissionWorker r (returnHandshake result)) s ()
worker-retains S.allocatePromise w (admissionWorker r (completedHandshake result)) s ()
worker-retains S.allocatePromise w (admissionWorker r impossibleHandshake) s ()
worker-retains S.allocatePromise w a@(admissionWorker r (prepare l)) s eq = subst (Retains s) (just-injective eq) (reframe _ refl refl (λ _ p → p) (λ _ p → p))
worker-retains S.chooseEntry w (admissionWorker r acquireMap) s ()
worker-retains S.chooseEntry w (admissionWorker r (count l)) s ()
worker-retains S.chooseEntry w (admissionWorker r (prepare l)) s ()
worker-retains S.chooseEntry w (admissionWorker r (forkHandler l p e)) s ()
worker-retains S.chooseEntry w (admissionWorker r (publish l p e)) s ()
worker-retains S.chooseEntry w (admissionWorker r (reject l reason)) s ()
worker-retains S.chooseEntry w (admissionWorker r (closeSocket reason)) s ()
worker-retains S.chooseEntry w (admissionWorker r (finished reason)) s ()
worker-retains S.chooseEntry w (admissionWorker r (countPublished p e)) s ()
worker-retains S.chooseEntry w (admissionWorker r (awaitHandshake p e)) s ()
worker-retains S.chooseEntry w (admissionWorker r (commitHandshake e result)) s ()
worker-retains S.chooseEntry w (admissionWorker r (countHandshake result)) s ()
worker-retains S.chooseEntry w (admissionWorker r (notifyInbound info)) s ()
worker-retains S.chooseEntry w (admissionWorker r (returnHandshake result)) s ()
worker-retains S.chooseEntry w (admissionWorker r (completedHandshake result)) s ()
worker-retains S.chooseEntry w (admissionWorker r impossibleHandshake) s ()
worker-retains S.chooseEntry w a@(admissionWorker r (selectEntry l p)) s eq with CM.selectInbound l r (cm s) in selectedEq
... | nothing = case eq of λ ()
... | just CM.denied = subst (Retains s) (just-injective eq) (reframe _ refl refl (λ _ p → p) (λ _ p → p))
... | just (CM.selected e c′) = subst (Retains s) (just-injective eq) (reframe _ refl refl (selected-present l r (cm s) selectedEq) (λ _ p → p))
worker-retains S.fork w (admissionWorker r acquireMap) s ()
worker-retains S.fork w (admissionWorker r (count l)) s ()
worker-retains S.fork w (admissionWorker r (prepare l)) s ()
worker-retains S.fork w (admissionWorker r (selectEntry l p)) s ()
worker-retains S.fork w (admissionWorker r (publish l p e)) s ()
worker-retains S.fork w (admissionWorker r (reject l reason)) s ()
worker-retains S.fork w (admissionWorker r (closeSocket reason)) s ()
worker-retains S.fork w (admissionWorker r (finished reason)) s ()
worker-retains S.fork w (admissionWorker r (countPublished p e)) s ()
worker-retains S.fork w (admissionWorker r (awaitHandshake p e)) s ()
worker-retains S.fork w (admissionWorker r (commitHandshake e result)) s ()
worker-retains S.fork w (admissionWorker r (countHandshake result)) s ()
worker-retains S.fork w (admissionWorker r (notifyInbound info)) s ()
worker-retains S.fork w (admissionWorker r (returnHandshake result)) s ()
worker-retains S.fork w (admissionWorker r (completedHandshake result)) s ()
worker-retains S.fork w (admissionWorker r impossibleHandshake) s ()
worker-retains S.fork w a@(admissionWorker r (forkHandler l p e)) s eq with lookup (child r) (handlers s) in absent | lookup (child r) (admissions s)
... | just _ | _ = case eq of λ ()
... | nothing | just _ = case eq of λ ()
... | nothing | nothing = subst (Retains s) (just-injective eq) (record
  { handlersRetained = λ q h found → fresh-lookup (child r) q (handlerStart e (socketRef r) p (key r)) h (handlers s) absent found
  ; resultsRetained = λ _ _ found → found
  ; entriesRetained = λ _ present → present
  ; socketsRetained = λ sock → put-preserves-present (socketRef r) sock (handling (child r)) (sockets s) })
worker-retains S.failFork w (admissionWorker r acquireMap) s ()
worker-retains S.failFork w (admissionWorker r (count l)) s ()
worker-retains S.failFork w (admissionWorker r (prepare l)) s ()
worker-retains S.failFork w (admissionWorker r (selectEntry l p)) s ()
worker-retains S.failFork w (admissionWorker r (publish l p e)) s ()
worker-retains S.failFork w (admissionWorker r (reject l reason)) s ()
worker-retains S.failFork w (admissionWorker r (closeSocket reason)) s ()
worker-retains S.failFork w (admissionWorker r (finished reason)) s ()
worker-retains S.failFork w (admissionWorker r (countPublished p e)) s ()
worker-retains S.failFork w (admissionWorker r (awaitHandshake p e)) s ()
worker-retains S.failFork w (admissionWorker r (commitHandshake e result)) s ()
worker-retains S.failFork w (admissionWorker r (countHandshake result)) s ()
worker-retains S.failFork w (admissionWorker r (notifyInbound info)) s ()
worker-retains S.failFork w (admissionWorker r (returnHandshake result)) s ()
worker-retains S.failFork w (admissionWorker r (completedHandshake result)) s ()
worker-retains S.failFork w (admissionWorker r impossibleHandshake) s ()
worker-retains S.failFork w a@(admissionWorker r (forkHandler l p e)) s eq = subst (Retains s) (just-injective eq) (reframe _ refl refl (λ _ p → p) (λ _ p → p))
worker-retains S.readCounters w (admissionWorker r acquireMap) s ()
worker-retains S.readCounters w (admissionWorker r (count l)) s ()
worker-retains S.readCounters w (admissionWorker r (prepare l)) s ()
worker-retains S.readCounters w (admissionWorker r (selectEntry l p)) s ()
worker-retains S.readCounters w (admissionWorker r (forkHandler l p e)) s ()
worker-retains S.readCounters w (admissionWorker r (publish l p e)) s ()
worker-retains S.readCounters w (admissionWorker r (reject l reason)) s ()
worker-retains S.readCounters w (admissionWorker r (closeSocket reason)) s ()
worker-retains S.readCounters w (admissionWorker r (finished reason)) s ()
worker-retains S.readCounters w (admissionWorker r (awaitHandshake p e)) s ()
worker-retains S.readCounters w (admissionWorker r (commitHandshake e result)) s ()
worker-retains S.readCounters w (admissionWorker r (countHandshake result)) s ()
worker-retains S.readCounters w (admissionWorker r (notifyInbound info)) s ()
worker-retains S.readCounters w (admissionWorker r (returnHandshake result)) s ()
worker-retains S.readCounters w (admissionWorker r (completedHandshake result)) s ()
worker-retains S.readCounters w (admissionWorker r impossibleHandshake) s ()
worker-retains S.readCounters w a@(admissionWorker r (countPublished p e)) s eq with mapCell (cm s)
... | taken _ = case eq of λ ()
... | full m with countIncoming (entries (cm s)) m
...   | nothing = case eq of λ ()
...   | just _ = subst (Retains s) (just-injective eq) (reframe _ refl refl (λ _ p → p) (λ _ p → p))
worker-retains S.close w (admissionWorker r acquireMap) s ()
worker-retains S.close w (admissionWorker r (count l)) s ()
worker-retains S.close w (admissionWorker r (prepare l)) s ()
worker-retains S.close w (admissionWorker r (selectEntry l p)) s ()
worker-retains S.close w (admissionWorker r (forkHandler l p e)) s ()
worker-retains S.close w (admissionWorker r (publish l p e)) s ()
worker-retains S.close w (admissionWorker r (reject l reason)) s ()
worker-retains S.close w (admissionWorker r (finished reason)) s ()
worker-retains S.close w (admissionWorker r (countPublished p e)) s ()
worker-retains S.close w (admissionWorker r (awaitHandshake p e)) s ()
worker-retains S.close w (admissionWorker r (commitHandshake e result)) s ()
worker-retains S.close w (admissionWorker r (countHandshake result)) s ()
worker-retains S.close w (admissionWorker r (notifyInbound info)) s ()
worker-retains S.close w (admissionWorker r (returnHandshake result)) s ()
worker-retains S.close w (admissionWorker r (completedHandshake result)) s ()
worker-retains S.close w (admissionWorker r impossibleHandshake) s ()
worker-retains S.close w a@(admissionWorker r (closeSocket reason)) s eq = subst (Retains s) (just-injective eq) (reframe _ refl refl (λ _ p → p) (λ sock → put-preserves-present (socketRef r) sock closed (sockets s)))
worker-retains S.putMapBack w (admissionWorker r acquireMap) s ()
worker-retains S.putMapBack w (admissionWorker r (count l)) s ()
worker-retains S.putMapBack w (admissionWorker r (prepare l)) s ()
worker-retains S.putMapBack w (admissionWorker r (selectEntry l p)) s ()
worker-retains S.putMapBack w (admissionWorker r (forkHandler l p e)) s ()
worker-retains S.putMapBack w (admissionWorker r (closeSocket reason)) s ()
worker-retains S.putMapBack w (admissionWorker r (finished reason)) s ()
worker-retains S.putMapBack w (admissionWorker r (countPublished p e)) s ()
worker-retains S.putMapBack w (admissionWorker r (awaitHandshake p e)) s ()
worker-retains S.putMapBack w (admissionWorker r (commitHandshake e result)) s ()
worker-retains S.putMapBack w (admissionWorker r (countHandshake result)) s ()
worker-retains S.putMapBack w (admissionWorker r (notifyInbound info)) s ()
worker-retains S.putMapBack w (admissionWorker r (returnHandshake result)) s ()
worker-retains S.putMapBack w (admissionWorker r (completedHandshake result)) s ()
worker-retains S.putMapBack w (admissionWorker r impossibleHandshake) s ()
worker-retains S.putMapBack w (admissionWorker r (reject l forbidden)) s ()
worker-retains S.putMapBack w (admissionWorker r (reject l forkFailed)) s ()
worker-retains S.putMapBack w a@(admissionWorker r (publish l p e)) s eq with CM.putMap l (insertConnection (key r) e (savedMap l)) (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst (Retains s) (just-injective eq) (reframe _ refl refl (λ ref present → subst (Present ref) (sym (put-entries l (insertConnection (key r) e (savedMap l)) (cm s) putEq)) present) (λ _ p → p))
worker-retains S.putMapBack w a@(admissionWorker r (reject l hardLimitReached)) s eq with CM.restoreMap l (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst (Retains s) (just-injective eq) (reframe _ refl refl (λ ref present → subst (Present ref) (sym (put-entries l (savedMap l) (cm s) putEq)) present) (λ _ p → p))
worker-retains S.restore w (admissionWorker r acquireMap) s ()
worker-retains S.restore w (admissionWorker r (count l)) s ()
worker-retains S.restore w (admissionWorker r (prepare l)) s ()
worker-retains S.restore w (admissionWorker r (selectEntry l p)) s ()
worker-retains S.restore w (admissionWorker r (forkHandler l p e)) s ()
worker-retains S.restore w (admissionWorker r (publish l p e)) s ()
worker-retains S.restore w (admissionWorker r (closeSocket reason)) s ()
worker-retains S.restore w (admissionWorker r (finished reason)) s ()
worker-retains S.restore w (admissionWorker r (countPublished p e)) s ()
worker-retains S.restore w (admissionWorker r (awaitHandshake p e)) s ()
worker-retains S.restore w (admissionWorker r (commitHandshake e result)) s ()
worker-retains S.restore w (admissionWorker r (countHandshake result)) s ()
worker-retains S.restore w (admissionWorker r (notifyInbound info)) s ()
worker-retains S.restore w (admissionWorker r (returnHandshake result)) s ()
worker-retains S.restore w (admissionWorker r (completedHandshake result)) s ()
worker-retains S.restore w (admissionWorker r impossibleHandshake) s ()
worker-retains S.restore w (admissionWorker r (reject l hardLimitReached)) s ()
worker-retains S.restore w a@(admissionWorker r (reject l forbidden)) s eq with CM.restoreMap l (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst (Retains s) (just-injective eq) (reframe _ refl refl (λ ref present → subst (Present ref) (sym (put-entries l (savedMap l) (cm s) putEq)) present) (λ _ p → p))
worker-retains S.restore w a@(admissionWorker r (reject l forkFailed)) s eq with CM.restoreMap l (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst (Retains s) (just-injective eq) (reframe _ refl refl (λ ref present → subst (Present ref) (sym (put-entries l (savedMap l) (cm s) putEq)) present) (λ _ p → p))

-- Successful admission steps only replace the world; the IG is unchanged.
step-effects : ∀ w a c {c′} → advance (admissionStep w a) c ≡ just c′ →
  Retains (world c) (world c′) × inboundGovernor c′ ≡ inboundGovernor c
step-effects w a c eq with lookup w (admissions (world c))
... | nothing = case eq of λ ()
... | just a₀ with S.stepWorker w a₀ a (world c) in stepped
...   | nothing = case eq of λ ()
...   | just s′ with just-injective eq
...     | refl = worker-retains a w a₀ (world c) stepped , refl
