{-# OPTIONS --guardedness #-}

-- Ownership preservation for every admission action, including entry selection.
module ConnectionManagement.Properties.OwnershipAdmission where

open import Data.Nat using (suc; _≤?_)
open import Data.List using (_∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Function using (case_of_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.State
open import ConnectionManagement.Properties.Ownership
open import ConnectionManagement.Properties.OwnershipNeutral
open import ConnectionManagement.Properties.OwnershipMapDispatcher
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.CM as CM

admission-worker : ∀ action w a s {s′} → lookup w (admissions s) ≡ just a →
  Server.stepWorker w a action s ≡ just s′ → Ownership s → Ownership s′
admission-worker Server.take = take-admission-worker
admission-worker Server.putMapBack = publish-admission-worker
admission-worker Server.restore = restore-admission-worker
admission-worker Server.countLimit w (admissionWorker r acquireMap) s found () own
admission-worker Server.countLimit w (admissionWorker r (prepare l)) s found () own
admission-worker Server.countLimit w (admissionWorker r (selectEntry l p)) s found () own
admission-worker Server.countLimit w (admissionWorker r (forkHandler l p e)) s found () own
admission-worker Server.countLimit w (admissionWorker r (publish l p e)) s found () own
admission-worker Server.countLimit w (admissionWorker r (reject l reason)) s found () own
admission-worker Server.countLimit w (admissionWorker r (closeSocket reason)) s found () own
admission-worker Server.countLimit w (admissionWorker r (finished reason)) s found () own
admission-worker Server.countLimit w (admissionWorker r (countPublished p e)) s found () own
admission-worker Server.countLimit w (admissionWorker r (awaitHandshake p e)) s found () own
admission-worker Server.countLimit w (admissionWorker r (commitHandshake e result)) s found () own
admission-worker Server.countLimit w (admissionWorker r (countHandshake result)) s found () own
admission-worker Server.countLimit w (admissionWorker r (notifyInbound info)) s found () own
admission-worker Server.countLimit w (admissionWorker r (returnHandshake result)) s found () own
admission-worker Server.countLimit w (admissionWorker r (completedHandshake result)) s found () own
admission-worker Server.countLimit w (admissionWorker r impossibleHandshake) s found () own
admission-worker Server.countLimit w a@(admissionWorker r (count l)) s found eq own
  with countIncoming (entries (cm s)) (savedMap l)
... | nothing = case eq of λ ()
... | just n with suc n ≤? hardLimit r
...   | yes _ = subst Ownership (just-injective eq) (admission-neutral w a (prepare l) s found refl own)
...   | no _ = subst Ownership (just-injective eq) (admission-neutral w a (reject l hardLimitReached) s found refl own)
admission-worker Server.allocatePromise w (admissionWorker r acquireMap) s found () own
admission-worker Server.allocatePromise w (admissionWorker r (count l)) s found () own
admission-worker Server.allocatePromise w (admissionWorker r (selectEntry l p)) s found () own
admission-worker Server.allocatePromise w (admissionWorker r (forkHandler l p e)) s found () own
admission-worker Server.allocatePromise w (admissionWorker r (publish l p e)) s found () own
admission-worker Server.allocatePromise w (admissionWorker r (reject l reason)) s found () own
admission-worker Server.allocatePromise w (admissionWorker r (closeSocket reason)) s found () own
admission-worker Server.allocatePromise w (admissionWorker r (finished reason)) s found () own
admission-worker Server.allocatePromise w (admissionWorker r (countPublished p e)) s found () own
admission-worker Server.allocatePromise w (admissionWorker r (awaitHandshake p e)) s found () own
admission-worker Server.allocatePromise w (admissionWorker r (commitHandshake e result)) s found () own
admission-worker Server.allocatePromise w (admissionWorker r (countHandshake result)) s found () own
admission-worker Server.allocatePromise w (admissionWorker r (notifyInbound info)) s found () own
admission-worker Server.allocatePromise w (admissionWorker r (returnHandshake result)) s found () own
admission-worker Server.allocatePromise w (admissionWorker r (completedHandshake result)) s found () own
admission-worker Server.allocatePromise w (admissionWorker r impossibleHandshake) s found () own
admission-worker Server.allocatePromise w a@(admissionWorker r (prepare l)) s found eq own =
  subst Ownership (just-injective eq) (admission-neutral w a (selectEntry l (ident (nextPromise s)))
    (record s { promises = ident (nextPromise s) ∷ promises s ; nextPromise = suc (nextPromise s) }) found refl own)
admission-worker Server.chooseEntry w (admissionWorker r acquireMap) s found () own
admission-worker Server.chooseEntry w (admissionWorker r (count l)) s found () own
admission-worker Server.chooseEntry w (admissionWorker r (prepare l)) s found () own
admission-worker Server.chooseEntry w (admissionWorker r (forkHandler l p e)) s found () own
admission-worker Server.chooseEntry w (admissionWorker r (publish l p e)) s found () own
admission-worker Server.chooseEntry w (admissionWorker r (reject l reason)) s found () own
admission-worker Server.chooseEntry w (admissionWorker r (closeSocket reason)) s found () own
admission-worker Server.chooseEntry w (admissionWorker r (finished reason)) s found () own
admission-worker Server.chooseEntry w (admissionWorker r (countPublished p e)) s found () own
admission-worker Server.chooseEntry w (admissionWorker r (awaitHandshake p e)) s found () own
admission-worker Server.chooseEntry w (admissionWorker r (commitHandshake e result)) s found () own
admission-worker Server.chooseEntry w (admissionWorker r (countHandshake result)) s found () own
admission-worker Server.chooseEntry w (admissionWorker r (notifyInbound info)) s found () own
admission-worker Server.chooseEntry w (admissionWorker r (returnHandshake result)) s found () own
admission-worker Server.chooseEntry w (admissionWorker r (completedHandshake result)) s found () own
admission-worker Server.chooseEntry w (admissionWorker r impossibleHandshake) s found () own
admission-worker Server.chooseEntry w a@(admissionWorker r (selectEntry l p)) s found eq own
  with CM.selectInbound l r (cm s) in selected
... | nothing = case eq of λ ()
... | just CM.denied = subst Ownership (just-injective eq) (admission-neutral w a (reject l forbidden) s found refl own)
... | just (CM.selected e c′) = subst Ownership (just-injective eq)
  (admission-neutral w a (forkHandler l p e) (record s { cm = c′ }) found refl
    (replace-cm s c′ (selected-cell l r (cm s) selected) own))
admission-worker Server.fork w (admissionWorker r acquireMap) s found () own
admission-worker Server.fork w (admissionWorker r (count l)) s found () own
admission-worker Server.fork w (admissionWorker r (prepare l)) s found () own
admission-worker Server.fork w (admissionWorker r (selectEntry l p)) s found () own
admission-worker Server.fork w (admissionWorker r (publish l p e)) s found () own
admission-worker Server.fork w (admissionWorker r (reject l reason)) s found () own
admission-worker Server.fork w (admissionWorker r (closeSocket reason)) s found () own
admission-worker Server.fork w (admissionWorker r (finished reason)) s found () own
admission-worker Server.fork w (admissionWorker r (countPublished p e)) s found () own
admission-worker Server.fork w (admissionWorker r (awaitHandshake p e)) s found () own
admission-worker Server.fork w (admissionWorker r (commitHandshake e result)) s found () own
admission-worker Server.fork w (admissionWorker r (countHandshake result)) s found () own
admission-worker Server.fork w (admissionWorker r (notifyInbound info)) s found () own
admission-worker Server.fork w (admissionWorker r (returnHandshake result)) s found () own
admission-worker Server.fork w (admissionWorker r (completedHandshake result)) s found () own
admission-worker Server.fork w (admissionWorker r impossibleHandshake) s found () own
admission-worker Server.fork w a@(admissionWorker r (forkHandler l p e)) s found eq own
  with lookup (child r) (handlers s) | lookup (child r) (admissions s)
... | nothing | nothing = subst Ownership (just-injective eq)
  (admission-neutral w a (publish l p e)
    (record s { handlers = put (child r) (handlerStart e (socketRef r) p (key r)) (handlers s)
              ; sockets = put (socketRef r) (handling (child r)) (sockets s) }) found refl own)
... | just _ | _ = case eq of λ ()
... | nothing | just _ = case eq of λ ()
admission-worker Server.failFork w (admissionWorker r acquireMap) s found () own
admission-worker Server.failFork w (admissionWorker r (count l)) s found () own
admission-worker Server.failFork w (admissionWorker r (prepare l)) s found () own
admission-worker Server.failFork w (admissionWorker r (selectEntry l p)) s found () own
admission-worker Server.failFork w (admissionWorker r (publish l p e)) s found () own
admission-worker Server.failFork w (admissionWorker r (reject l reason)) s found () own
admission-worker Server.failFork w (admissionWorker r (closeSocket reason)) s found () own
admission-worker Server.failFork w (admissionWorker r (finished reason)) s found () own
admission-worker Server.failFork w (admissionWorker r (countPublished p e)) s found () own
admission-worker Server.failFork w (admissionWorker r (awaitHandshake p e)) s found () own
admission-worker Server.failFork w (admissionWorker r (commitHandshake e result)) s found () own
admission-worker Server.failFork w (admissionWorker r (countHandshake result)) s found () own
admission-worker Server.failFork w (admissionWorker r (notifyInbound info)) s found () own
admission-worker Server.failFork w (admissionWorker r (returnHandshake result)) s found () own
admission-worker Server.failFork w (admissionWorker r (completedHandshake result)) s found () own
admission-worker Server.failFork w (admissionWorker r impossibleHandshake) s found () own
admission-worker Server.failFork w a@(admissionWorker r (forkHandler l p e)) s found eq own =
  subst Ownership (just-injective eq) (admission-neutral w a (reject l forkFailed) s found refl own)
admission-worker Server.readCounters w (admissionWorker r acquireMap) s found () own
admission-worker Server.readCounters w (admissionWorker r (count l)) s found () own
admission-worker Server.readCounters w (admissionWorker r (prepare l)) s found () own
admission-worker Server.readCounters w (admissionWorker r (selectEntry l p)) s found () own
admission-worker Server.readCounters w (admissionWorker r (forkHandler l p e)) s found () own
admission-worker Server.readCounters w (admissionWorker r (publish l p e)) s found () own
admission-worker Server.readCounters w (admissionWorker r (reject l reason)) s found () own
admission-worker Server.readCounters w (admissionWorker r (closeSocket reason)) s found () own
admission-worker Server.readCounters w (admissionWorker r (finished reason)) s found () own
admission-worker Server.readCounters w (admissionWorker r (awaitHandshake p e)) s found () own
admission-worker Server.readCounters w (admissionWorker r (commitHandshake e result)) s found () own
admission-worker Server.readCounters w (admissionWorker r (countHandshake result)) s found () own
admission-worker Server.readCounters w (admissionWorker r (notifyInbound info)) s found () own
admission-worker Server.readCounters w (admissionWorker r (returnHandshake result)) s found () own
admission-worker Server.readCounters w (admissionWorker r (completedHandshake result)) s found () own
admission-worker Server.readCounters w (admissionWorker r impossibleHandshake) s found () own
admission-worker Server.readCounters w a@(admissionWorker r (countPublished p e)) s found eq own
  with mapCell (cm s) in cell
... | taken _ = case eq of λ ()
... | full m with countIncoming (entries (cm s)) m
...   | nothing = case eq of λ ()
...   | just _ = subst Ownership (just-injective eq) (admission-neutral w a (awaitHandshake p e) s found refl
    (subst (λ cell → Owns cell (claims s)) (sym cell) own))
admission-worker Server.close w (admissionWorker r acquireMap) s found () own
admission-worker Server.close w (admissionWorker r (count l)) s found () own
admission-worker Server.close w (admissionWorker r (prepare l)) s found () own
admission-worker Server.close w (admissionWorker r (selectEntry l p)) s found () own
admission-worker Server.close w (admissionWorker r (forkHandler l p e)) s found () own
admission-worker Server.close w (admissionWorker r (publish l p e)) s found () own
admission-worker Server.close w (admissionWorker r (reject l reason)) s found () own
admission-worker Server.close w (admissionWorker r (finished reason)) s found () own
admission-worker Server.close w (admissionWorker r (countPublished p e)) s found () own
admission-worker Server.close w (admissionWorker r (awaitHandshake p e)) s found () own
admission-worker Server.close w (admissionWorker r (commitHandshake e result)) s found () own
admission-worker Server.close w (admissionWorker r (countHandshake result)) s found () own
admission-worker Server.close w (admissionWorker r (notifyInbound info)) s found () own
admission-worker Server.close w (admissionWorker r (returnHandshake result)) s found () own
admission-worker Server.close w (admissionWorker r (completedHandshake result)) s found () own
admission-worker Server.close w (admissionWorker r impossibleHandshake) s found () own
admission-worker Server.close w a@(admissionWorker r (closeSocket reason)) s found eq own =
  subst Ownership (just-injective eq) (admission-neutral w a (finished reason)
    (record s { sockets = put (socketRef r) closed (sockets s) }) found refl own)
