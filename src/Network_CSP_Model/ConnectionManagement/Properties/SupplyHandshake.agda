{-# OPTIONS --guardedness #-}

-- Handshake results may overwrite an existing entry but never allocate an ID.
module ConnectionManagement.Properties.SupplyHandshake where

open import Data.Nat using (suc; _≤?_)
open import Data.List using (length)
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
open import ConnectionManagement.Properties.SupplyBounds
import ConnectionManagement.Rules.Handshake as H

success-preserves : ∀ w a e h f decision s {old} → lookup e (entries (cm s)) ≡ just old →
  SupplyBounds s → SupplyBounds (H.applySuccess w a e h f decision s)
success-preserves w a e h f (H.update st provenance) s found (eb , pb) =
  overwrite-bound (nextEntry (cm s)) e st (entries (cm s)) eb found , pb
success-preserves w a e h f (H.retain provenance) s found bounded = bounded
success-preserves w a e h f (H.disconnect reason) s found bounded = bounded
success-preserves w a e h f H.impossible s found bounded = bounded

terminate-preserves : ∀ w a e reason s {s′} → H.terminateResult w a e reason s ≡ just s′ →
  SupplyBounds s → SupplyBounds s′
terminate-preserves w a e reason s eq (eb , pb)
  with lookup e (entries (cm s)) in found | mapCell (cm s)
... | nothing | _ = case eq of λ ()
... | just _ | taken _ = case eq of λ ()
... | just _ | full m with lookupConnection (key (request a)) m
...   | nothing = subst SupplyBounds (just-injective eq) (eb , pb)
...   | just current with e ≟ current
...     | no _ = subst SupplyBounds (just-injective eq) (eb , pb)
...     | yes _ = subst SupplyBounds (just-injective eq)
  (overwrite-bound (nextEntry (cm s)) e (H.errorState (request a) reason) (entries (cm s)) eb found , pb)

handshake-preserves : ∀ action mode w a s {s′} → H.stepWorker mode w a action s ≡ just s′ →
  SupplyBounds s → SupplyBounds s′
handshake-preserves H.readResult mode w (admissionWorker r acquireMap) s () bounded
handshake-preserves H.readResult mode w (admissionWorker r (count l)) s () bounded
handshake-preserves H.readResult mode w (admissionWorker r (prepare l)) s () bounded
handshake-preserves H.readResult mode w (admissionWorker r (selectEntry l p)) s () bounded
handshake-preserves H.readResult mode w (admissionWorker r (forkHandler l p e)) s () bounded
handshake-preserves H.readResult mode w (admissionWorker r (publish l p e)) s () bounded
handshake-preserves H.readResult mode w (admissionWorker r (reject l reason)) s () bounded
handshake-preserves H.readResult mode w (admissionWorker r (closeSocket reason)) s () bounded
handshake-preserves H.readResult mode w (admissionWorker r (finished reason)) s () bounded
handshake-preserves H.readResult mode w (admissionWorker r (countPublished p e)) s () bounded
handshake-preserves H.readResult mode w (admissionWorker r (commitHandshake e result)) s () bounded
handshake-preserves H.readResult mode w (admissionWorker r (countHandshake result)) s () bounded
handshake-preserves H.readResult mode w (admissionWorker r (notifyInbound info)) s () bounded
handshake-preserves H.readResult mode w (admissionWorker r (returnHandshake result)) s () bounded
handshake-preserves H.readResult mode w (admissionWorker r (completedHandshake result)) s () bounded
handshake-preserves H.readResult mode w (admissionWorker r impossibleHandshake) s () bounded
handshake-preserves H.readResult mode w a@(admissionWorker r (awaitHandshake p e)) s eq bounded with lookup p (handshakeResults s)
... | nothing = case eq of λ ()
... | just result = subst SupplyBounds (just-injective eq) bounded
handshake-preserves H.commitResult mode w (admissionWorker r acquireMap) s () bounded
handshake-preserves H.commitResult mode w (admissionWorker r (count l)) s () bounded
handshake-preserves H.commitResult mode w (admissionWorker r (prepare l)) s () bounded
handshake-preserves H.commitResult mode w (admissionWorker r (selectEntry l p)) s () bounded
handshake-preserves H.commitResult mode w (admissionWorker r (forkHandler l p e)) s () bounded
handshake-preserves H.commitResult mode w (admissionWorker r (publish l p e)) s () bounded
handshake-preserves H.commitResult mode w (admissionWorker r (reject l reason)) s () bounded
handshake-preserves H.commitResult mode w (admissionWorker r (closeSocket reason)) s () bounded
handshake-preserves H.commitResult mode w (admissionWorker r (finished reason)) s () bounded
handshake-preserves H.commitResult mode w (admissionWorker r (countPublished p e)) s () bounded
handshake-preserves H.commitResult mode w (admissionWorker r (awaitHandshake p e)) s () bounded
handshake-preserves H.commitResult mode w (admissionWorker r (countHandshake result)) s () bounded
handshake-preserves H.commitResult mode w (admissionWorker r (notifyInbound info)) s () bounded
handshake-preserves H.commitResult mode w (admissionWorker r (returnHandshake result)) s () bounded
handshake-preserves H.commitResult mode w (admissionWorker r (completedHandshake result)) s () bounded
handshake-preserves H.commitResult mode w (admissionWorker r impossibleHandshake) s () bounded
handshake-preserves H.commitResult mode w a@(admissionWorker r (commitHandshake e (negotiated h f))) s eq bounded
  with lookup e (entries (cm s)) in found
... | nothing = case eq of λ ()
... | just st = subst SupplyBounds (just-injective eq) (success-preserves w a e h f (H.decideSuccess r h f st) s found bounded)
handshake-preserves H.commitResult mode w a@(admissionWorker r (commitHandshake e query)) s eq bounded =
  terminate-preserves w a e handshakeQuery s eq bounded
handshake-preserves H.commitResult mode w a@(admissionWorker r (commitHandshake e (handlerError cls err))) s eq bounded =
  terminate-preserves w a e (handshakeError cls err) s eq bounded
handshake-preserves H.readResultCounters mode w (admissionWorker r acquireMap) s () bounded
handshake-preserves H.readResultCounters mode w (admissionWorker r (count l)) s () bounded
handshake-preserves H.readResultCounters mode w (admissionWorker r (prepare l)) s () bounded
handshake-preserves H.readResultCounters mode w (admissionWorker r (selectEntry l p)) s () bounded
handshake-preserves H.readResultCounters mode w (admissionWorker r (forkHandler l p e)) s () bounded
handshake-preserves H.readResultCounters mode w (admissionWorker r (publish l p e)) s () bounded
handshake-preserves H.readResultCounters mode w (admissionWorker r (reject l reason)) s () bounded
handshake-preserves H.readResultCounters mode w (admissionWorker r (closeSocket reason)) s () bounded
handshake-preserves H.readResultCounters mode w (admissionWorker r (finished reason)) s () bounded
handshake-preserves H.readResultCounters mode w (admissionWorker r (countPublished p e)) s () bounded
handshake-preserves H.readResultCounters mode w (admissionWorker r (awaitHandshake p e)) s () bounded
handshake-preserves H.readResultCounters mode w (admissionWorker r (commitHandshake e result)) s () bounded
handshake-preserves H.readResultCounters mode w (admissionWorker r (notifyInbound info)) s () bounded
handshake-preserves H.readResultCounters mode w (admissionWorker r (returnHandshake result)) s () bounded
handshake-preserves H.readResultCounters mode w (admissionWorker r (completedHandshake result)) s () bounded
handshake-preserves H.readResultCounters mode w (admissionWorker r impossibleHandshake) s () bounded
handshake-preserves H.readResultCounters mode w a@(admissionWorker r (countHandshake result)) s eq bounded with mapCell (cm s)
... | taken _ = case eq of λ ()
... | full m with countIncoming (entries (cm s)) m
...   | nothing = case eq of λ ()
...   | just _ with result | mode
...     | connected info | responderMode = subst SupplyBounds (just-injective eq) bounded
...     | connected info | noResponderMode = subst SupplyBounds (just-injective eq) bounded
...     | disconnected _ | _ = subst SupplyBounds (just-injective eq) bounded
handshake-preserves H.enqueueInbound mode w (admissionWorker r acquireMap) s () bounded
handshake-preserves H.enqueueInbound mode w (admissionWorker r (count l)) s () bounded
handshake-preserves H.enqueueInbound mode w (admissionWorker r (prepare l)) s () bounded
handshake-preserves H.enqueueInbound mode w (admissionWorker r (selectEntry l p)) s () bounded
handshake-preserves H.enqueueInbound mode w (admissionWorker r (forkHandler l p e)) s () bounded
handshake-preserves H.enqueueInbound mode w (admissionWorker r (publish l p e)) s () bounded
handshake-preserves H.enqueueInbound mode w (admissionWorker r (reject l reason)) s () bounded
handshake-preserves H.enqueueInbound mode w (admissionWorker r (closeSocket reason)) s () bounded
handshake-preserves H.enqueueInbound mode w (admissionWorker r (finished reason)) s () bounded
handshake-preserves H.enqueueInbound mode w (admissionWorker r (countPublished p e)) s () bounded
handshake-preserves H.enqueueInbound mode w (admissionWorker r (awaitHandshake p e)) s () bounded
handshake-preserves H.enqueueInbound mode w (admissionWorker r (commitHandshake e result)) s () bounded
handshake-preserves H.enqueueInbound mode w (admissionWorker r (countHandshake result)) s () bounded
handshake-preserves H.enqueueInbound mode w (admissionWorker r (returnHandshake result)) s () bounded
handshake-preserves H.enqueueInbound mode w (admissionWorker r (completedHandshake result)) s () bounded
handshake-preserves H.enqueueInbound mode w (admissionWorker r impossibleHandshake) s () bounded
handshake-preserves H.enqueueInbound mode w a@(admissionWorker r (notifyInbound info)) s eq bounded with suc (length (inboundInfo s)) ≤? 100
... | no _ = case eq of λ ()
... | yes _ = subst SupplyBounds (just-injective eq) bounded
handshake-preserves H.returnResult mode w (admissionWorker r acquireMap) s () bounded
handshake-preserves H.returnResult mode w (admissionWorker r (count l)) s () bounded
handshake-preserves H.returnResult mode w (admissionWorker r (prepare l)) s () bounded
handshake-preserves H.returnResult mode w (admissionWorker r (selectEntry l p)) s () bounded
handshake-preserves H.returnResult mode w (admissionWorker r (forkHandler l p e)) s () bounded
handshake-preserves H.returnResult mode w (admissionWorker r (publish l p e)) s () bounded
handshake-preserves H.returnResult mode w (admissionWorker r (reject l reason)) s () bounded
handshake-preserves H.returnResult mode w (admissionWorker r (closeSocket reason)) s () bounded
handshake-preserves H.returnResult mode w (admissionWorker r (finished reason)) s () bounded
handshake-preserves H.returnResult mode w (admissionWorker r (countPublished p e)) s () bounded
handshake-preserves H.returnResult mode w (admissionWorker r (awaitHandshake p e)) s () bounded
handshake-preserves H.returnResult mode w (admissionWorker r (commitHandshake e result)) s () bounded
handshake-preserves H.returnResult mode w (admissionWorker r (countHandshake result)) s () bounded
handshake-preserves H.returnResult mode w (admissionWorker r (notifyInbound info)) s () bounded
handshake-preserves H.returnResult mode w (admissionWorker r (completedHandshake result)) s () bounded
handshake-preserves H.returnResult mode w (admissionWorker r impossibleHandshake) s () bounded
handshake-preserves H.returnResult mode w a@(admissionWorker r (returnHandshake result)) s eq bounded = subst SupplyBounds (just-injective eq) bounded
