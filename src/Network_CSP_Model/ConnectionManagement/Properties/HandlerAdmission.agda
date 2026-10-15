{-# OPTIONS --guardedness #-}

-- Existing chains survive admission; this does not establish a new chain.
module ConnectionManagement.Properties.HandlerAdmission where

open import Data.Nat using (suc; _≤?_)
open import Data.List using (_∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
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
open import ConnectionManagement.Properties.HandlerReferences
open import ConnectionManagement.Properties.HandlerCleanup using (take-entries; put-entries)
import ConnectionManagement.Rules.Server as S
import ConnectionManagement.Rules.CM as CM

-- Transport unchanged immutable stores and retained mutable resource identities.
reframe : ∀ {q mid s ig} s′ → handlers s′ ≡ handlers s →
  handshakeResults s′ ≡ handshakeResults s →
  (∀ e → Present e (entries (cm s)) → Present e (entries (cm s′))) →
  (∀ sock → Present sock (sockets s) → Present sock (sockets s′)) →
  Chain q mid s ig → Chain q mid s′ ig
reframe s′ hs ps ep sp chain = record
  { originalHandler = originalHandler chain; publishedHandle = publishedHandle chain; negotiatedFlow = negotiatedFlow chain; handleValue = handleValue chain; muxValue = muxValue chain; handleFound = handleFound chain; handleMux = handleMux chain; muxFound = muxFound chain; keyMatches = keyMatches chain
  ; handlerFound = trans (cong (lookup _) hs) (handlerFound chain)
  ; promiseFound = trans (cong (lookup _) ps) (promiseFound chain)
  ; entryPresent = ep _ (entryPresent chain); socketPresent = sp _ (socketPresent chain) }

-- The absent child guard protects all already-published handler records.
fresh-handler-chain : ∀ w h {q mid s ig} → lookup w (handlers s) ≡ nothing →
  Chain q mid s ig → Chain q mid (record s { handlers = put w h (handlers s) }) ig
fresh-handler-chain w h {q} {s = s} absent chain with q ≟ w
... | yes same = case trans (sym absent) (subst (λ k → lookup k (handlers s) ≡ _) same (handlerFound chain)) of λ ()
... | no different = record
  { originalHandler = originalHandler chain; publishedHandle = publishedHandle chain; negotiatedFlow = negotiatedFlow chain; handleValue = handleValue chain; muxValue = muxValue chain; handleFound = handleFound chain; handleMux = handleMux chain; muxFound = muxFound chain; keyMatches = keyMatches chain
  ; promiseFound = promiseFound chain; entryPresent = entryPresent chain; socketPresent = socketPresent chain
  ; handlerFound = trans (lookup-put-other w q h (handlers s) different) (handlerFound chain) }

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

worker-chain : ∀ {q mid ig} act w a s {s′} → S.stepWorker w a act s ≡ just s′ →
  Chain q mid s ig → Chain q mid s′ ig
worker-chain {q} {mid} {ig} S.take w (admissionWorker r (count l)) s () chain
worker-chain {q} {mid} {ig} S.take w (admissionWorker r (prepare l)) s () chain
worker-chain {q} {mid} {ig} S.take w (admissionWorker r (selectEntry l p)) s () chain
worker-chain {q} {mid} {ig} S.take w (admissionWorker r (forkHandler l p e)) s () chain
worker-chain {q} {mid} {ig} S.take w (admissionWorker r (publish l p e)) s () chain
worker-chain {q} {mid} {ig} S.take w (admissionWorker r (reject l reason)) s () chain
worker-chain {q} {mid} {ig} S.take w (admissionWorker r (closeSocket reason)) s () chain
worker-chain {q} {mid} {ig} S.take w (admissionWorker r (finished reason)) s () chain
worker-chain {q} {mid} {ig} S.take w (admissionWorker r (countPublished p e)) s () chain
worker-chain {q} {mid} {ig} S.take w (admissionWorker r (awaitHandshake p e)) s () chain
worker-chain {q} {mid} {ig} S.take w (admissionWorker r (commitHandshake e result)) s () chain
worker-chain {q} {mid} {ig} S.take w (admissionWorker r (countHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.take w (admissionWorker r (notifyInbound info)) s () chain
worker-chain {q} {mid} {ig} S.take w (admissionWorker r (returnHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.take w (admissionWorker r (completedHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.take w (admissionWorker r impossibleHandshake) s () chain
worker-chain {q} {mid} {ig} S.take w a@(admissionWorker r acquireMap) s eq chain with CM.takeMap w (cm s) in takenEq
... | nothing = case eq of λ ()
... | just (l , c′) = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ refl refl (λ e p → subst (Present e) (sym (take-entries w (cm s) takenEq)) p) (λ _ p → p) chain)
worker-chain {q} {mid} {ig} S.countLimit w (admissionWorker r acquireMap) s () chain
worker-chain {q} {mid} {ig} S.countLimit w (admissionWorker r (prepare l)) s () chain
worker-chain {q} {mid} {ig} S.countLimit w (admissionWorker r (selectEntry l p)) s () chain
worker-chain {q} {mid} {ig} S.countLimit w (admissionWorker r (forkHandler l p e)) s () chain
worker-chain {q} {mid} {ig} S.countLimit w (admissionWorker r (publish l p e)) s () chain
worker-chain {q} {mid} {ig} S.countLimit w (admissionWorker r (reject l reason)) s () chain
worker-chain {q} {mid} {ig} S.countLimit w (admissionWorker r (closeSocket reason)) s () chain
worker-chain {q} {mid} {ig} S.countLimit w (admissionWorker r (finished reason)) s () chain
worker-chain {q} {mid} {ig} S.countLimit w (admissionWorker r (countPublished p e)) s () chain
worker-chain {q} {mid} {ig} S.countLimit w (admissionWorker r (awaitHandshake p e)) s () chain
worker-chain {q} {mid} {ig} S.countLimit w (admissionWorker r (commitHandshake e result)) s () chain
worker-chain {q} {mid} {ig} S.countLimit w (admissionWorker r (countHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.countLimit w (admissionWorker r (notifyInbound info)) s () chain
worker-chain {q} {mid} {ig} S.countLimit w (admissionWorker r (returnHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.countLimit w (admissionWorker r (completedHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.countLimit w (admissionWorker r impossibleHandshake) s () chain
worker-chain {q} {mid} {ig} S.countLimit w a@(admissionWorker r (count l)) s eq chain with countIncoming (entries (cm s)) (savedMap l)
... | nothing = case eq of λ ()
... | just n with suc n ≤? hardLimit r
...   | yes _ = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ refl refl (λ _ p → p) (λ _ p → p) chain)
...   | no _ = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ refl refl (λ _ p → p) (λ _ p → p) chain)
worker-chain {q} {mid} {ig} S.allocatePromise w (admissionWorker r acquireMap) s () chain
worker-chain {q} {mid} {ig} S.allocatePromise w (admissionWorker r (count l)) s () chain
worker-chain {q} {mid} {ig} S.allocatePromise w (admissionWorker r (selectEntry l p)) s () chain
worker-chain {q} {mid} {ig} S.allocatePromise w (admissionWorker r (forkHandler l p e)) s () chain
worker-chain {q} {mid} {ig} S.allocatePromise w (admissionWorker r (publish l p e)) s () chain
worker-chain {q} {mid} {ig} S.allocatePromise w (admissionWorker r (reject l reason)) s () chain
worker-chain {q} {mid} {ig} S.allocatePromise w (admissionWorker r (closeSocket reason)) s () chain
worker-chain {q} {mid} {ig} S.allocatePromise w (admissionWorker r (finished reason)) s () chain
worker-chain {q} {mid} {ig} S.allocatePromise w (admissionWorker r (countPublished p e)) s () chain
worker-chain {q} {mid} {ig} S.allocatePromise w (admissionWorker r (awaitHandshake p e)) s () chain
worker-chain {q} {mid} {ig} S.allocatePromise w (admissionWorker r (commitHandshake e result)) s () chain
worker-chain {q} {mid} {ig} S.allocatePromise w (admissionWorker r (countHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.allocatePromise w (admissionWorker r (notifyInbound info)) s () chain
worker-chain {q} {mid} {ig} S.allocatePromise w (admissionWorker r (returnHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.allocatePromise w (admissionWorker r (completedHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.allocatePromise w (admissionWorker r impossibleHandshake) s () chain
worker-chain {q} {mid} {ig} S.allocatePromise w a@(admissionWorker r (prepare l)) s eq chain = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ refl refl (λ _ p → p) (λ _ p → p) chain)
worker-chain {q} {mid} {ig} S.chooseEntry w (admissionWorker r acquireMap) s () chain
worker-chain {q} {mid} {ig} S.chooseEntry w (admissionWorker r (count l)) s () chain
worker-chain {q} {mid} {ig} S.chooseEntry w (admissionWorker r (prepare l)) s () chain
worker-chain {q} {mid} {ig} S.chooseEntry w (admissionWorker r (forkHandler l p e)) s () chain
worker-chain {q} {mid} {ig} S.chooseEntry w (admissionWorker r (publish l p e)) s () chain
worker-chain {q} {mid} {ig} S.chooseEntry w (admissionWorker r (reject l reason)) s () chain
worker-chain {q} {mid} {ig} S.chooseEntry w (admissionWorker r (closeSocket reason)) s () chain
worker-chain {q} {mid} {ig} S.chooseEntry w (admissionWorker r (finished reason)) s () chain
worker-chain {q} {mid} {ig} S.chooseEntry w (admissionWorker r (countPublished p e)) s () chain
worker-chain {q} {mid} {ig} S.chooseEntry w (admissionWorker r (awaitHandshake p e)) s () chain
worker-chain {q} {mid} {ig} S.chooseEntry w (admissionWorker r (commitHandshake e result)) s () chain
worker-chain {q} {mid} {ig} S.chooseEntry w (admissionWorker r (countHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.chooseEntry w (admissionWorker r (notifyInbound info)) s () chain
worker-chain {q} {mid} {ig} S.chooseEntry w (admissionWorker r (returnHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.chooseEntry w (admissionWorker r (completedHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.chooseEntry w (admissionWorker r impossibleHandshake) s () chain
worker-chain {q} {mid} {ig} S.chooseEntry w a@(admissionWorker r (selectEntry l p)) s eq chain with CM.selectInbound l r (cm s) in selectedEq
... | nothing = case eq of λ ()
... | just CM.denied = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ refl refl (λ _ p → p) (λ _ p → p) chain)
... | just (CM.selected e c′) = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ refl refl (selected-present l r (cm s) selectedEq) (λ _ p → p) chain)
worker-chain {q} {mid} {ig} S.fork w (admissionWorker r acquireMap) s () chain
worker-chain {q} {mid} {ig} S.fork w (admissionWorker r (count l)) s () chain
worker-chain {q} {mid} {ig} S.fork w (admissionWorker r (prepare l)) s () chain
worker-chain {q} {mid} {ig} S.fork w (admissionWorker r (selectEntry l p)) s () chain
worker-chain {q} {mid} {ig} S.fork w (admissionWorker r (publish l p e)) s () chain
worker-chain {q} {mid} {ig} S.fork w (admissionWorker r (reject l reason)) s () chain
worker-chain {q} {mid} {ig} S.fork w (admissionWorker r (closeSocket reason)) s () chain
worker-chain {q} {mid} {ig} S.fork w (admissionWorker r (finished reason)) s () chain
worker-chain {q} {mid} {ig} S.fork w (admissionWorker r (countPublished p e)) s () chain
worker-chain {q} {mid} {ig} S.fork w (admissionWorker r (awaitHandshake p e)) s () chain
worker-chain {q} {mid} {ig} S.fork w (admissionWorker r (commitHandshake e result)) s () chain
worker-chain {q} {mid} {ig} S.fork w (admissionWorker r (countHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.fork w (admissionWorker r (notifyInbound info)) s () chain
worker-chain {q} {mid} {ig} S.fork w (admissionWorker r (returnHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.fork w (admissionWorker r (completedHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.fork w (admissionWorker r impossibleHandshake) s () chain
worker-chain {q} {mid} {ig} S.fork w a@(admissionWorker r (forkHandler l p e)) s eq chain with lookup (child r) (handlers s) in absent | lookup (child r) (admissions s)
... | just _ | _ = case eq of λ ()
... | nothing | just _ = case eq of λ ()
... | nothing | nothing = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ refl refl (λ _ p → p) (λ sock → put-preserves-present (socketRef r) sock (handling (child r)) (sockets s)) (fresh-handler-chain (child r) (handlerStart e (socketRef r) p (key r)) absent chain))
worker-chain {q} {mid} {ig} S.failFork w (admissionWorker r acquireMap) s () chain
worker-chain {q} {mid} {ig} S.failFork w (admissionWorker r (count l)) s () chain
worker-chain {q} {mid} {ig} S.failFork w (admissionWorker r (prepare l)) s () chain
worker-chain {q} {mid} {ig} S.failFork w (admissionWorker r (selectEntry l p)) s () chain
worker-chain {q} {mid} {ig} S.failFork w (admissionWorker r (publish l p e)) s () chain
worker-chain {q} {mid} {ig} S.failFork w (admissionWorker r (reject l reason)) s () chain
worker-chain {q} {mid} {ig} S.failFork w (admissionWorker r (closeSocket reason)) s () chain
worker-chain {q} {mid} {ig} S.failFork w (admissionWorker r (finished reason)) s () chain
worker-chain {q} {mid} {ig} S.failFork w (admissionWorker r (countPublished p e)) s () chain
worker-chain {q} {mid} {ig} S.failFork w (admissionWorker r (awaitHandshake p e)) s () chain
worker-chain {q} {mid} {ig} S.failFork w (admissionWorker r (commitHandshake e result)) s () chain
worker-chain {q} {mid} {ig} S.failFork w (admissionWorker r (countHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.failFork w (admissionWorker r (notifyInbound info)) s () chain
worker-chain {q} {mid} {ig} S.failFork w (admissionWorker r (returnHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.failFork w (admissionWorker r (completedHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.failFork w (admissionWorker r impossibleHandshake) s () chain
worker-chain {q} {mid} {ig} S.failFork w a@(admissionWorker r (forkHandler l p e)) s eq chain = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ refl refl (λ _ p → p) (λ _ p → p) chain)
worker-chain {q} {mid} {ig} S.readCounters w (admissionWorker r acquireMap) s () chain
worker-chain {q} {mid} {ig} S.readCounters w (admissionWorker r (count l)) s () chain
worker-chain {q} {mid} {ig} S.readCounters w (admissionWorker r (prepare l)) s () chain
worker-chain {q} {mid} {ig} S.readCounters w (admissionWorker r (selectEntry l p)) s () chain
worker-chain {q} {mid} {ig} S.readCounters w (admissionWorker r (forkHandler l p e)) s () chain
worker-chain {q} {mid} {ig} S.readCounters w (admissionWorker r (publish l p e)) s () chain
worker-chain {q} {mid} {ig} S.readCounters w (admissionWorker r (reject l reason)) s () chain
worker-chain {q} {mid} {ig} S.readCounters w (admissionWorker r (closeSocket reason)) s () chain
worker-chain {q} {mid} {ig} S.readCounters w (admissionWorker r (finished reason)) s () chain
worker-chain {q} {mid} {ig} S.readCounters w (admissionWorker r (awaitHandshake p e)) s () chain
worker-chain {q} {mid} {ig} S.readCounters w (admissionWorker r (commitHandshake e result)) s () chain
worker-chain {q} {mid} {ig} S.readCounters w (admissionWorker r (countHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.readCounters w (admissionWorker r (notifyInbound info)) s () chain
worker-chain {q} {mid} {ig} S.readCounters w (admissionWorker r (returnHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.readCounters w (admissionWorker r (completedHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.readCounters w (admissionWorker r impossibleHandshake) s () chain
worker-chain {q} {mid} {ig} S.readCounters w a@(admissionWorker r (countPublished p e)) s eq chain with mapCell (cm s)
... | taken _ = case eq of λ ()
... | full m with countIncoming (entries (cm s)) m
...   | nothing = case eq of λ ()
...   | just _ = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ refl refl (λ _ p → p) (λ _ p → p) chain)
worker-chain {q} {mid} {ig} S.close w (admissionWorker r acquireMap) s () chain
worker-chain {q} {mid} {ig} S.close w (admissionWorker r (count l)) s () chain
worker-chain {q} {mid} {ig} S.close w (admissionWorker r (prepare l)) s () chain
worker-chain {q} {mid} {ig} S.close w (admissionWorker r (selectEntry l p)) s () chain
worker-chain {q} {mid} {ig} S.close w (admissionWorker r (forkHandler l p e)) s () chain
worker-chain {q} {mid} {ig} S.close w (admissionWorker r (publish l p e)) s () chain
worker-chain {q} {mid} {ig} S.close w (admissionWorker r (reject l reason)) s () chain
worker-chain {q} {mid} {ig} S.close w (admissionWorker r (finished reason)) s () chain
worker-chain {q} {mid} {ig} S.close w (admissionWorker r (countPublished p e)) s () chain
worker-chain {q} {mid} {ig} S.close w (admissionWorker r (awaitHandshake p e)) s () chain
worker-chain {q} {mid} {ig} S.close w (admissionWorker r (commitHandshake e result)) s () chain
worker-chain {q} {mid} {ig} S.close w (admissionWorker r (countHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.close w (admissionWorker r (notifyInbound info)) s () chain
worker-chain {q} {mid} {ig} S.close w (admissionWorker r (returnHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.close w (admissionWorker r (completedHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.close w (admissionWorker r impossibleHandshake) s () chain
worker-chain {q} {mid} {ig} S.close w a@(admissionWorker r (closeSocket reason)) s eq chain = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ refl refl (λ _ p → p) (λ sock → put-preserves-present (socketRef r) sock closed (sockets s)) chain)
worker-chain {q} {mid} {ig} S.putMapBack w (admissionWorker r acquireMap) s () chain
worker-chain {q} {mid} {ig} S.putMapBack w (admissionWorker r (count l)) s () chain
worker-chain {q} {mid} {ig} S.putMapBack w (admissionWorker r (prepare l)) s () chain
worker-chain {q} {mid} {ig} S.putMapBack w (admissionWorker r (selectEntry l p)) s () chain
worker-chain {q} {mid} {ig} S.putMapBack w (admissionWorker r (forkHandler l p e)) s () chain
worker-chain {q} {mid} {ig} S.putMapBack w (admissionWorker r (closeSocket reason)) s () chain
worker-chain {q} {mid} {ig} S.putMapBack w (admissionWorker r (finished reason)) s () chain
worker-chain {q} {mid} {ig} S.putMapBack w (admissionWorker r (countPublished p e)) s () chain
worker-chain {q} {mid} {ig} S.putMapBack w (admissionWorker r (awaitHandshake p e)) s () chain
worker-chain {q} {mid} {ig} S.putMapBack w (admissionWorker r (commitHandshake e result)) s () chain
worker-chain {q} {mid} {ig} S.putMapBack w (admissionWorker r (countHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.putMapBack w (admissionWorker r (notifyInbound info)) s () chain
worker-chain {q} {mid} {ig} S.putMapBack w (admissionWorker r (returnHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.putMapBack w (admissionWorker r (completedHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.putMapBack w (admissionWorker r impossibleHandshake) s () chain
worker-chain {q} {mid} {ig} S.putMapBack w (admissionWorker r (reject l forbidden)) s () chain
worker-chain {q} {mid} {ig} S.putMapBack w (admissionWorker r (reject l forkFailed)) s () chain
worker-chain {q} {mid} {ig} S.putMapBack w a@(admissionWorker r (publish l p e)) s eq chain with CM.putMap l (insertConnection (key r) e (savedMap l)) (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ refl refl (λ ref present → subst (Present ref) (sym (put-entries l (insertConnection (key r) e (savedMap l)) (cm s) putEq)) present) (λ _ p → p) chain)
worker-chain {q} {mid} {ig} S.putMapBack w a@(admissionWorker r (reject l hardLimitReached)) s eq chain with CM.restoreMap l (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ refl refl (λ ref present → subst (Present ref) (sym (put-entries l (savedMap l) (cm s) putEq)) present) (λ _ p → p) chain)
worker-chain {q} {mid} {ig} S.restore w (admissionWorker r acquireMap) s () chain
worker-chain {q} {mid} {ig} S.restore w (admissionWorker r (count l)) s () chain
worker-chain {q} {mid} {ig} S.restore w (admissionWorker r (prepare l)) s () chain
worker-chain {q} {mid} {ig} S.restore w (admissionWorker r (selectEntry l p)) s () chain
worker-chain {q} {mid} {ig} S.restore w (admissionWorker r (forkHandler l p e)) s () chain
worker-chain {q} {mid} {ig} S.restore w (admissionWorker r (publish l p e)) s () chain
worker-chain {q} {mid} {ig} S.restore w (admissionWorker r (closeSocket reason)) s () chain
worker-chain {q} {mid} {ig} S.restore w (admissionWorker r (finished reason)) s () chain
worker-chain {q} {mid} {ig} S.restore w (admissionWorker r (countPublished p e)) s () chain
worker-chain {q} {mid} {ig} S.restore w (admissionWorker r (awaitHandshake p e)) s () chain
worker-chain {q} {mid} {ig} S.restore w (admissionWorker r (commitHandshake e result)) s () chain
worker-chain {q} {mid} {ig} S.restore w (admissionWorker r (countHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.restore w (admissionWorker r (notifyInbound info)) s () chain
worker-chain {q} {mid} {ig} S.restore w (admissionWorker r (returnHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.restore w (admissionWorker r (completedHandshake result)) s () chain
worker-chain {q} {mid} {ig} S.restore w (admissionWorker r impossibleHandshake) s () chain
worker-chain {q} {mid} {ig} S.restore w (admissionWorker r (reject l hardLimitReached)) s () chain
worker-chain {q} {mid} {ig} S.restore w a@(admissionWorker r (reject l forbidden)) s eq chain with CM.restoreMap l (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ refl refl (λ ref present → subst (Present ref) (sym (put-entries l (savedMap l) (cm s) putEq)) present) (λ _ p → p) chain)
worker-chain {q} {mid} {ig} S.restore w a@(admissionWorker r (reject l forkFailed)) s eq chain with CM.restoreMap l (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ refl refl (λ ref present → subst (Present ref) (sym (put-entries l (savedMap l) (cm s) putEq)) present) (λ _ p → p) chain)

-- The dispatcher changes the world only; lifecycle frames and IG stay intact.
step-preserves : ∀ w a c {c′} → advance (admissionStep w a) c ≡ just c′ →
  ∀ q → TrackedChain q c → TrackedChain q c′
step-preserves w a c eq q (f , found , chain) with lookup w (admissions (world c))
... | nothing = case eq of λ ()
... | just a₀ with S.stepWorker w a₀ a (world c) in stepped
...   | nothing = case eq of λ ()
...   | just s′ with just-injective eq
...     | refl = f , found , worker-chain a w a₀ (world c) stepped chain
