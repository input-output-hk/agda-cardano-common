{-# OPTIONS --guardedness #-}

-- Handshake consumption retains no admission lease. Full-map error transactions
-- may change bindings but cannot create or remove a map owner.
module ConnectionManagement.Properties.OwnershipHandshake where

open import Data.Nat using (suc; _≤?_)
open import Data.List using ([]; _∷_; _++_; length)
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
import ConnectionManagement.Rules.Handshake as H

success-preserves : ∀ w a e h f decision s → lookup w (admissions s) ≡ just a →
  admissionLease (pc a) ≡ nothing → Ownership s → Ownership (H.applySuccess w a e h f decision s)
success-preserves w a e h f (H.update st provenance) s found none own =
  admission-neutral w a (countHandshake (connected (newConnectionInfo provenance (key (request a)) f h)))
    (record s { cm = record (cm s) { entries = put e st (entries (cm s)) } }) found (sym none) own
success-preserves w a e h f (H.retain provenance) s found none own =
  admission-neutral w a (countHandshake (connected (newConnectionInfo provenance (key (request a)) f h))) s found (sym none) own
success-preserves w a e h f (H.disconnect reason) s found none own =
  admission-neutral w a (countHandshake (disconnected reason)) s found (sym none) own
success-preserves w a e h f H.impossible s found none own = admission-neutral w a impossibleHandshake s found (sym none) own

terminate-preserves : ∀ w a e reason s {s′} → lookup w (admissions s) ≡ just a →
  admissionLease (pc a) ≡ nothing → H.terminateResult w a e reason s ≡ just s′ → Ownership s → Ownership s′
terminate-preserves w a e reason s found none eq own
  with lookup e (entries (cm s)) | mapCell (cm s) in cell
... | nothing | _ = case eq of λ ()
... | just _ | taken _ = case eq of λ ()
... | just _ | full m with lookupConnection (key (request a)) m
...   | nothing = subst Ownership (just-injective eq)
  (admission-neutral w a (countHandshake (disconnected reason)) s found (sym none)
    (subst (λ cell → Owns cell (claims s)) (sym cell) own))
...   | just current with e ≟ current
...     | no _ = subst Ownership (just-injective eq)
  (admission-neutral w a (countHandshake (disconnected reason)) s found (sym none)
    (subst (λ cell → Owns cell (claims s)) (sym cell) own))
...     | yes _ = subst Ownership (just-injective eq)
  (admission-neutral w a (countHandshake (disconnected reason))
    (record s { cm = record (cm s)
      { mapCell = full (deleteConnection (key (request a)) m)
      ; entries = put e (H.errorState (request a) reason) (entries (cm s)) } }) found (sym none) own)

handshake-worker : ∀ action mode w a s {s′} → lookup w (admissions s) ≡ just a →
  H.stepWorker mode w a action s ≡ just s′ → Ownership s → Ownership s′
handshake-worker H.readResult mode w (admissionWorker r acquireMap) s found () own
handshake-worker H.readResult mode w (admissionWorker r (count l)) s found () own
handshake-worker H.readResult mode w (admissionWorker r (prepare l)) s found () own
handshake-worker H.readResult mode w (admissionWorker r (selectEntry l p)) s found () own
handshake-worker H.readResult mode w (admissionWorker r (forkHandler l p e)) s found () own
handshake-worker H.readResult mode w (admissionWorker r (publish l p e)) s found () own
handshake-worker H.readResult mode w (admissionWorker r (reject l reason)) s found () own
handshake-worker H.readResult mode w (admissionWorker r (closeSocket reason)) s found () own
handshake-worker H.readResult mode w (admissionWorker r (finished reason)) s found () own
handshake-worker H.readResult mode w (admissionWorker r (countPublished p e)) s found () own
handshake-worker H.readResult mode w (admissionWorker r (commitHandshake e result)) s found () own
handshake-worker H.readResult mode w (admissionWorker r (countHandshake result)) s found () own
handshake-worker H.readResult mode w (admissionWorker r (notifyInbound info)) s found () own
handshake-worker H.readResult mode w (admissionWorker r (returnHandshake result)) s found () own
handshake-worker H.readResult mode w (admissionWorker r (completedHandshake result)) s found () own
handshake-worker H.readResult mode w (admissionWorker r impossibleHandshake) s found () own
handshake-worker H.readResult mode w a@(admissionWorker r (awaitHandshake p e)) s found eq own
  with lookup p (handshakeResults s)
... | nothing = case eq of λ ()
... | just result = subst Ownership (just-injective eq) (admission-neutral w a (commitHandshake e result) s found refl own)
handshake-worker H.commitResult mode w (admissionWorker r acquireMap) s found () own
handshake-worker H.commitResult mode w (admissionWorker r (count l)) s found () own
handshake-worker H.commitResult mode w (admissionWorker r (prepare l)) s found () own
handshake-worker H.commitResult mode w (admissionWorker r (selectEntry l p)) s found () own
handshake-worker H.commitResult mode w (admissionWorker r (forkHandler l p e)) s found () own
handshake-worker H.commitResult mode w (admissionWorker r (publish l p e)) s found () own
handshake-worker H.commitResult mode w (admissionWorker r (reject l reason)) s found () own
handshake-worker H.commitResult mode w (admissionWorker r (closeSocket reason)) s found () own
handshake-worker H.commitResult mode w (admissionWorker r (finished reason)) s found () own
handshake-worker H.commitResult mode w (admissionWorker r (countPublished p e)) s found () own
handshake-worker H.commitResult mode w (admissionWorker r (awaitHandshake p e)) s found () own
handshake-worker H.commitResult mode w (admissionWorker r (countHandshake result)) s found () own
handshake-worker H.commitResult mode w (admissionWorker r (notifyInbound info)) s found () own
handshake-worker H.commitResult mode w (admissionWorker r (returnHandshake result)) s found () own
handshake-worker H.commitResult mode w (admissionWorker r (completedHandshake result)) s found () own
handshake-worker H.commitResult mode w (admissionWorker r impossibleHandshake) s found () own
handshake-worker H.commitResult mode w a@(admissionWorker r (commitHandshake e (negotiated h f))) s found eq own
  with lookup e (entries (cm s))
... | nothing = case eq of λ ()
... | just st = subst Ownership (just-injective eq) (success-preserves w a e h f (H.decideSuccess r h f st) s found refl own)
handshake-worker H.commitResult mode w a@(admissionWorker r (commitHandshake e query)) s found eq own =
  terminate-preserves w a e handshakeQuery s found refl eq own
handshake-worker H.commitResult mode w a@(admissionWorker r (commitHandshake e (handlerError cls err))) s found eq own =
  terminate-preserves w a e (handshakeError cls err) s found refl eq own
handshake-worker H.readResultCounters mode w (admissionWorker r acquireMap) s found () own
handshake-worker H.readResultCounters mode w (admissionWorker r (count l)) s found () own
handshake-worker H.readResultCounters mode w (admissionWorker r (prepare l)) s found () own
handshake-worker H.readResultCounters mode w (admissionWorker r (selectEntry l p)) s found () own
handshake-worker H.readResultCounters mode w (admissionWorker r (forkHandler l p e)) s found () own
handshake-worker H.readResultCounters mode w (admissionWorker r (publish l p e)) s found () own
handshake-worker H.readResultCounters mode w (admissionWorker r (reject l reason)) s found () own
handshake-worker H.readResultCounters mode w (admissionWorker r (closeSocket reason)) s found () own
handshake-worker H.readResultCounters mode w (admissionWorker r (finished reason)) s found () own
handshake-worker H.readResultCounters mode w (admissionWorker r (countPublished p e)) s found () own
handshake-worker H.readResultCounters mode w (admissionWorker r (awaitHandshake p e)) s found () own
handshake-worker H.readResultCounters mode w (admissionWorker r (commitHandshake e result)) s found () own
handshake-worker H.readResultCounters mode w (admissionWorker r (notifyInbound info)) s found () own
handshake-worker H.readResultCounters mode w (admissionWorker r (returnHandshake result)) s found () own
handshake-worker H.readResultCounters mode w (admissionWorker r (completedHandshake result)) s found () own
handshake-worker H.readResultCounters mode w (admissionWorker r impossibleHandshake) s found () own
handshake-worker H.readResultCounters mode w a@(admissionWorker r (countHandshake result)) s found eq own
  with mapCell (cm s) in cell
... | taken _ = case eq of λ ()
... | full m with countIncoming (entries (cm s)) m
...   | nothing = case eq of λ ()
...   | just _ with result | mode
...     | connected info | responderMode = subst Ownership (just-injective eq)
  (admission-neutral w (admissionWorker r (countHandshake (connected info))) (notifyInbound info) s found refl (subst (λ cell → Owns cell (claims s)) (sym cell) own))
...     | connected info | noResponderMode = subst Ownership (just-injective eq)
  (admission-neutral w (admissionWorker r (countHandshake (connected info))) (returnHandshake (connected info)) s found refl (subst (λ cell → Owns cell (claims s)) (sym cell) own))
...     | disconnected reason | _ = subst Ownership (just-injective eq)
  (admission-neutral w (admissionWorker r (countHandshake (disconnected reason))) (returnHandshake (disconnected reason)) s found refl (subst (λ cell → Owns cell (claims s)) (sym cell) own))
handshake-worker H.enqueueInbound mode w (admissionWorker r acquireMap) s found () own
handshake-worker H.enqueueInbound mode w (admissionWorker r (count l)) s found () own
handshake-worker H.enqueueInbound mode w (admissionWorker r (prepare l)) s found () own
handshake-worker H.enqueueInbound mode w (admissionWorker r (selectEntry l p)) s found () own
handshake-worker H.enqueueInbound mode w (admissionWorker r (forkHandler l p e)) s found () own
handshake-worker H.enqueueInbound mode w (admissionWorker r (publish l p e)) s found () own
handshake-worker H.enqueueInbound mode w (admissionWorker r (reject l reason)) s found () own
handshake-worker H.enqueueInbound mode w (admissionWorker r (closeSocket reason)) s found () own
handshake-worker H.enqueueInbound mode w (admissionWorker r (finished reason)) s found () own
handshake-worker H.enqueueInbound mode w (admissionWorker r (countPublished p e)) s found () own
handshake-worker H.enqueueInbound mode w (admissionWorker r (awaitHandshake p e)) s found () own
handshake-worker H.enqueueInbound mode w (admissionWorker r (commitHandshake e result)) s found () own
handshake-worker H.enqueueInbound mode w (admissionWorker r (countHandshake result)) s found () own
handshake-worker H.enqueueInbound mode w (admissionWorker r (returnHandshake result)) s found () own
handshake-worker H.enqueueInbound mode w (admissionWorker r (completedHandshake result)) s found () own
handshake-worker H.enqueueInbound mode w (admissionWorker r impossibleHandshake) s found () own
handshake-worker H.enqueueInbound mode w a@(admissionWorker r (notifyInbound info)) s found eq own
  with suc (length (inboundInfo s)) ≤? 100
... | no _ = case eq of λ ()
... | yes _ = subst Ownership (just-injective eq) (admission-neutral w a (returnHandshake (connected info))
  (record s { inboundInfo = inboundInfo s ++ (info ∷ []) }) found refl own)
handshake-worker H.returnResult mode w (admissionWorker r acquireMap) s found () own
handshake-worker H.returnResult mode w (admissionWorker r (count l)) s found () own
handshake-worker H.returnResult mode w (admissionWorker r (prepare l)) s found () own
handshake-worker H.returnResult mode w (admissionWorker r (selectEntry l p)) s found () own
handshake-worker H.returnResult mode w (admissionWorker r (forkHandler l p e)) s found () own
handshake-worker H.returnResult mode w (admissionWorker r (publish l p e)) s found () own
handshake-worker H.returnResult mode w (admissionWorker r (reject l reason)) s found () own
handshake-worker H.returnResult mode w (admissionWorker r (closeSocket reason)) s found () own
handshake-worker H.returnResult mode w (admissionWorker r (finished reason)) s found () own
handshake-worker H.returnResult mode w (admissionWorker r (countPublished p e)) s found () own
handshake-worker H.returnResult mode w (admissionWorker r (awaitHandshake p e)) s found () own
handshake-worker H.returnResult mode w (admissionWorker r (commitHandshake e result)) s found () own
handshake-worker H.returnResult mode w (admissionWorker r (countHandshake result)) s found () own
handshake-worker H.returnResult mode w (admissionWorker r (notifyInbound info)) s found () own
handshake-worker H.returnResult mode w (admissionWorker r (completedHandshake result)) s found () own
handshake-worker H.returnResult mode w (admissionWorker r impossibleHandshake) s found () own
handshake-worker H.returnResult mode w a@(admissionWorker r (returnHandshake result)) s found eq own =
  subst Ownership (just-injective eq) (admission-neutral w a (completedHandshake result) s found refl own)
