{-# OPTIONS --guardedness #-}

-- Handshake consumers retain original references even when removing map entries.
module ConnectionManagement.Properties.HandlerHandshake where

open import Data.Nat using (suc; _≤?_)
open import Data.List using ([]; _∷_; _++_; length)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.Entries using (put-preserves-present)
open import ConnectionManagement.Properties.HandlerReferences
open import ConnectionManagement.Properties.HandlerAdmission using (reframe)
import ConnectionManagement.Rules.Handshake as H

success-chain : ∀ w a e h f decision s {q mid ig} → Chain q mid s ig →
  Chain q mid (H.applySuccess w a e h f decision s) ig
success-chain w a e h f (H.update st provenance) s chain =
  reframe _ refl refl (λ ref → put-preserves-present e ref st (entries (cm s))) (λ _ p → p) chain
success-chain w a e h f (H.retain provenance) s chain = reframe _ refl refl (λ _ p → p) (λ _ p → p) chain
success-chain w a e h f (H.disconnect reason) s chain = reframe _ refl refl (λ _ p → p) (λ _ p → p) chain
success-chain w a e h f H.impossible s chain = reframe _ refl refl (λ _ p → p) (λ _ p → p) chain

terminate-chain : ∀ {q mid ig} w a e reason s {s′} → H.terminateResult w a e reason s ≡ just s′ →
  Chain q mid s ig → Chain q mid s′ ig
terminate-chain {q} {mid} {ig} w a e reason s eq chain with lookup e (entries (cm s)) | mapCell (cm s)
... | nothing | _ = case eq of λ ()
... | just _ | taken _ = case eq of λ ()
... | just _ | full m with lookupConnection (key (request a)) m
...   | nothing = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ refl refl (λ _ p → p) (λ _ p → p) chain)
...   | just current with e ≟ current
...     | no _ = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ refl refl (λ _ p → p) (λ _ p → p) chain)
...     | yes _ = subst (λ s → Chain q mid s ig) (just-injective eq)
  (reframe _ refl refl (λ ref → put-preserves-present e ref (H.errorState (request a) reason) (entries (cm s))) (λ _ p → p) chain)

worker-chain : ∀ {q mid ig} act mode w a s {s′} → H.stepWorker mode w a act s ≡ just s′ →
  Chain q mid s ig → Chain q mid s′ ig
worker-chain {q} {mid} {ig} H.readResult mode w (admissionWorker r acquireMap) s () chain
worker-chain {q} {mid} {ig} H.readResult mode w (admissionWorker r (count l)) s () chain
worker-chain {q} {mid} {ig} H.readResult mode w (admissionWorker r (prepare l)) s () chain
worker-chain {q} {mid} {ig} H.readResult mode w (admissionWorker r (selectEntry l p)) s () chain
worker-chain {q} {mid} {ig} H.readResult mode w (admissionWorker r (forkHandler l p e)) s () chain
worker-chain {q} {mid} {ig} H.readResult mode w (admissionWorker r (publish l p e)) s () chain
worker-chain {q} {mid} {ig} H.readResult mode w (admissionWorker r (reject l reason)) s () chain
worker-chain {q} {mid} {ig} H.readResult mode w (admissionWorker r (closeSocket reason)) s () chain
worker-chain {q} {mid} {ig} H.readResult mode w (admissionWorker r (finished reason)) s () chain
worker-chain {q} {mid} {ig} H.readResult mode w (admissionWorker r (countPublished p e)) s () chain
worker-chain {q} {mid} {ig} H.readResult mode w (admissionWorker r (commitHandshake e result)) s () chain
worker-chain {q} {mid} {ig} H.readResult mode w (admissionWorker r (countHandshake result)) s () chain
worker-chain {q} {mid} {ig} H.readResult mode w (admissionWorker r (notifyInbound info)) s () chain
worker-chain {q} {mid} {ig} H.readResult mode w (admissionWorker r (returnHandshake result)) s () chain
worker-chain {q} {mid} {ig} H.readResult mode w (admissionWorker r (completedHandshake result)) s () chain
worker-chain {q} {mid} {ig} H.readResult mode w (admissionWorker r impossibleHandshake) s () chain
worker-chain {q} {mid} {ig} H.readResult mode w a@(admissionWorker r (awaitHandshake p e)) s eq chain with lookup p (handshakeResults s)
... | nothing = case eq of λ ()
... | just result = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ refl refl (λ _ p → p) (λ _ p → p) chain)
worker-chain {q} {mid} {ig} H.commitResult mode w (admissionWorker r acquireMap) s () chain
worker-chain {q} {mid} {ig} H.commitResult mode w (admissionWorker r (count l)) s () chain
worker-chain {q} {mid} {ig} H.commitResult mode w (admissionWorker r (prepare l)) s () chain
worker-chain {q} {mid} {ig} H.commitResult mode w (admissionWorker r (selectEntry l p)) s () chain
worker-chain {q} {mid} {ig} H.commitResult mode w (admissionWorker r (forkHandler l p e)) s () chain
worker-chain {q} {mid} {ig} H.commitResult mode w (admissionWorker r (publish l p e)) s () chain
worker-chain {q} {mid} {ig} H.commitResult mode w (admissionWorker r (reject l reason)) s () chain
worker-chain {q} {mid} {ig} H.commitResult mode w (admissionWorker r (closeSocket reason)) s () chain
worker-chain {q} {mid} {ig} H.commitResult mode w (admissionWorker r (finished reason)) s () chain
worker-chain {q} {mid} {ig} H.commitResult mode w (admissionWorker r (countPublished p e)) s () chain
worker-chain {q} {mid} {ig} H.commitResult mode w (admissionWorker r (awaitHandshake p e)) s () chain
worker-chain {q} {mid} {ig} H.commitResult mode w (admissionWorker r (countHandshake result)) s () chain
worker-chain {q} {mid} {ig} H.commitResult mode w (admissionWorker r (notifyInbound info)) s () chain
worker-chain {q} {mid} {ig} H.commitResult mode w (admissionWorker r (returnHandshake result)) s () chain
worker-chain {q} {mid} {ig} H.commitResult mode w (admissionWorker r (completedHandshake result)) s () chain
worker-chain {q} {mid} {ig} H.commitResult mode w (admissionWorker r impossibleHandshake) s () chain
worker-chain {q} {mid} {ig} H.commitResult mode w a@(admissionWorker r (commitHandshake e (negotiated h f))) s eq chain with lookup e (entries (cm s))
... | nothing = case eq of λ ()
... | just st = subst (λ s → Chain q mid s ig) (just-injective eq) (success-chain w a e h f (H.decideSuccess r h f st) s chain)
worker-chain {q} {mid} {ig} H.commitResult mode w a@(admissionWorker r (commitHandshake e query)) s eq chain = terminate-chain w a e handshakeQuery s eq chain
worker-chain {q} {mid} {ig} H.commitResult mode w a@(admissionWorker r (commitHandshake e (handlerError cls err))) s eq chain = terminate-chain w a e (handshakeError cls err) s eq chain
worker-chain {q} {mid} {ig} H.readResultCounters mode w (admissionWorker r acquireMap) s () chain
worker-chain {q} {mid} {ig} H.readResultCounters mode w (admissionWorker r (count l)) s () chain
worker-chain {q} {mid} {ig} H.readResultCounters mode w (admissionWorker r (prepare l)) s () chain
worker-chain {q} {mid} {ig} H.readResultCounters mode w (admissionWorker r (selectEntry l p)) s () chain
worker-chain {q} {mid} {ig} H.readResultCounters mode w (admissionWorker r (forkHandler l p e)) s () chain
worker-chain {q} {mid} {ig} H.readResultCounters mode w (admissionWorker r (publish l p e)) s () chain
worker-chain {q} {mid} {ig} H.readResultCounters mode w (admissionWorker r (reject l reason)) s () chain
worker-chain {q} {mid} {ig} H.readResultCounters mode w (admissionWorker r (closeSocket reason)) s () chain
worker-chain {q} {mid} {ig} H.readResultCounters mode w (admissionWorker r (finished reason)) s () chain
worker-chain {q} {mid} {ig} H.readResultCounters mode w (admissionWorker r (countPublished p e)) s () chain
worker-chain {q} {mid} {ig} H.readResultCounters mode w (admissionWorker r (awaitHandshake p e)) s () chain
worker-chain {q} {mid} {ig} H.readResultCounters mode w (admissionWorker r (commitHandshake e result)) s () chain
worker-chain {q} {mid} {ig} H.readResultCounters mode w (admissionWorker r (notifyInbound info)) s () chain
worker-chain {q} {mid} {ig} H.readResultCounters mode w (admissionWorker r (returnHandshake result)) s () chain
worker-chain {q} {mid} {ig} H.readResultCounters mode w (admissionWorker r (completedHandshake result)) s () chain
worker-chain {q} {mid} {ig} H.readResultCounters mode w (admissionWorker r impossibleHandshake) s () chain
worker-chain {q} {mid} {ig} H.readResultCounters mode w a@(admissionWorker r (countHandshake result)) s eq chain with mapCell (cm s)
... | taken _ = case eq of λ ()
... | full m with countIncoming (entries (cm s)) m
...   | nothing = case eq of λ ()
...   | just _ with result | mode
...     | connected info | responderMode = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ refl refl (λ _ p → p) (λ _ p → p) chain)
...     | connected info | noResponderMode = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ refl refl (λ _ p → p) (λ _ p → p) chain)
...     | disconnected reason | _ = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ refl refl (λ _ p → p) (λ _ p → p) chain)
worker-chain {q} {mid} {ig} H.enqueueInbound mode w (admissionWorker r acquireMap) s () chain
worker-chain {q} {mid} {ig} H.enqueueInbound mode w (admissionWorker r (count l)) s () chain
worker-chain {q} {mid} {ig} H.enqueueInbound mode w (admissionWorker r (prepare l)) s () chain
worker-chain {q} {mid} {ig} H.enqueueInbound mode w (admissionWorker r (selectEntry l p)) s () chain
worker-chain {q} {mid} {ig} H.enqueueInbound mode w (admissionWorker r (forkHandler l p e)) s () chain
worker-chain {q} {mid} {ig} H.enqueueInbound mode w (admissionWorker r (publish l p e)) s () chain
worker-chain {q} {mid} {ig} H.enqueueInbound mode w (admissionWorker r (reject l reason)) s () chain
worker-chain {q} {mid} {ig} H.enqueueInbound mode w (admissionWorker r (closeSocket reason)) s () chain
worker-chain {q} {mid} {ig} H.enqueueInbound mode w (admissionWorker r (finished reason)) s () chain
worker-chain {q} {mid} {ig} H.enqueueInbound mode w (admissionWorker r (countPublished p e)) s () chain
worker-chain {q} {mid} {ig} H.enqueueInbound mode w (admissionWorker r (awaitHandshake p e)) s () chain
worker-chain {q} {mid} {ig} H.enqueueInbound mode w (admissionWorker r (commitHandshake e result)) s () chain
worker-chain {q} {mid} {ig} H.enqueueInbound mode w (admissionWorker r (countHandshake result)) s () chain
worker-chain {q} {mid} {ig} H.enqueueInbound mode w (admissionWorker r (returnHandshake result)) s () chain
worker-chain {q} {mid} {ig} H.enqueueInbound mode w (admissionWorker r (completedHandshake result)) s () chain
worker-chain {q} {mid} {ig} H.enqueueInbound mode w (admissionWorker r impossibleHandshake) s () chain
worker-chain {q} {mid} {ig} H.enqueueInbound mode w a@(admissionWorker r (notifyInbound info)) s eq chain with suc (length (inboundInfo s)) ≤? 100
... | no _ = case eq of λ ()
... | yes _ = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ refl refl (λ _ p → p) (λ _ p → p) chain)
worker-chain {q} {mid} {ig} H.returnResult mode w (admissionWorker r acquireMap) s () chain
worker-chain {q} {mid} {ig} H.returnResult mode w (admissionWorker r (count l)) s () chain
worker-chain {q} {mid} {ig} H.returnResult mode w (admissionWorker r (prepare l)) s () chain
worker-chain {q} {mid} {ig} H.returnResult mode w (admissionWorker r (selectEntry l p)) s () chain
worker-chain {q} {mid} {ig} H.returnResult mode w (admissionWorker r (forkHandler l p e)) s () chain
worker-chain {q} {mid} {ig} H.returnResult mode w (admissionWorker r (publish l p e)) s () chain
worker-chain {q} {mid} {ig} H.returnResult mode w (admissionWorker r (reject l reason)) s () chain
worker-chain {q} {mid} {ig} H.returnResult mode w (admissionWorker r (closeSocket reason)) s () chain
worker-chain {q} {mid} {ig} H.returnResult mode w (admissionWorker r (finished reason)) s () chain
worker-chain {q} {mid} {ig} H.returnResult mode w (admissionWorker r (countPublished p e)) s () chain
worker-chain {q} {mid} {ig} H.returnResult mode w (admissionWorker r (awaitHandshake p e)) s () chain
worker-chain {q} {mid} {ig} H.returnResult mode w (admissionWorker r (commitHandshake e result)) s () chain
worker-chain {q} {mid} {ig} H.returnResult mode w (admissionWorker r (countHandshake result)) s () chain
worker-chain {q} {mid} {ig} H.returnResult mode w (admissionWorker r (notifyInbound info)) s () chain
worker-chain {q} {mid} {ig} H.returnResult mode w (admissionWorker r (completedHandshake result)) s () chain
worker-chain {q} {mid} {ig} H.returnResult mode w (admissionWorker r impossibleHandshake) s () chain
worker-chain {q} {mid} {ig} H.returnResult mode w a@(admissionWorker r (returnHandshake result)) s eq chain = subst (λ s → Chain q mid s ig) (just-injective eq) (reframe _ refl refl (λ _ p → p) (λ _ p → p) chain)

-- Consumer steps leave lifecycle frames and the IG execution engine untouched.
step-preserves : ∀ w a c {c′} → advance (handshakeStep w a) c ≡ just c′ →
  ∀ q → TrackedChain q c → TrackedChain q c′
step-preserves w a c eq q (f , found , chain) with lookup w (admissions (world c))
... | nothing = case eq of λ ()
... | just a₀ with H.stepWorker (responder c) w a₀ a (world c) in stepped
...   | nothing = case eq of λ ()
...   | just s′ with just-injective eq
...     | refl = f , found , worker-chain a (responder c) w a₀ (world c) stepped chain
