{-# OPTIONS --guardedness #-}

-- Supply-bound preservation by every admission-prefix action.
module ConnectionManagement.Properties.SupplyAdmission where

open import Data.Nat using (suc; _≤?_)
open import Data.List using (_∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Function using (case_of_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.State
open import ConnectionManagement.Properties.SupplyBounds
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.CM as CM

admission-preserves : ∀ action w a s {s′} →
  Server.stepWorker w a action s ≡ just s′ → SupplyBounds s → SupplyBounds s′
admission-preserves Server.take w (admissionWorker r (count l)) s () bounded
admission-preserves Server.take w (admissionWorker r (prepare l)) s () bounded
admission-preserves Server.take w (admissionWorker r (selectEntry l p)) s () bounded
admission-preserves Server.take w (admissionWorker r (forkHandler l p e)) s () bounded
admission-preserves Server.take w (admissionWorker r (publish l p e)) s () bounded
admission-preserves Server.take w (admissionWorker r (reject l hardLimitReached)) s () bounded
admission-preserves Server.take w (admissionWorker r (reject l forbidden)) s () bounded
admission-preserves Server.take w (admissionWorker r (reject l forkFailed)) s () bounded
admission-preserves Server.take w (admissionWorker r (closeSocket reason)) s () bounded
admission-preserves Server.take w (admissionWorker r (finished reason)) s () bounded
admission-preserves Server.take w (admissionWorker r (countPublished p e)) s () bounded
admission-preserves Server.take w (admissionWorker r (awaitHandshake p e)) s () bounded
admission-preserves Server.take w (admissionWorker r (commitHandshake e result)) s () bounded
admission-preserves Server.take w (admissionWorker r (countHandshake result)) s () bounded
admission-preserves Server.take w (admissionWorker r (notifyInbound info)) s () bounded
admission-preserves Server.take w (admissionWorker r (returnHandshake result)) s () bounded
admission-preserves Server.take w (admissionWorker r (completedHandshake result)) s () bounded
admission-preserves Server.take w (admissionWorker r impossibleHandshake) s () bounded
admission-preserves Server.take w (admissionWorker r acquireMap) s eq (eb , pb) with CM.takeMap w (cm s) in takenEq
... | nothing = case eq of λ ()
... | just (l , c′) = subst SupplyBounds (just-injective eq) (take-bound w (cm s) takenEq eb , pb)
admission-preserves Server.countLimit w (admissionWorker r acquireMap) s () bounded
admission-preserves Server.countLimit w (admissionWorker r (prepare l)) s () bounded
admission-preserves Server.countLimit w (admissionWorker r (selectEntry l p)) s () bounded
admission-preserves Server.countLimit w (admissionWorker r (forkHandler l p e)) s () bounded
admission-preserves Server.countLimit w (admissionWorker r (publish l p e)) s () bounded
admission-preserves Server.countLimit w (admissionWorker r (reject l hardLimitReached)) s () bounded
admission-preserves Server.countLimit w (admissionWorker r (reject l forbidden)) s () bounded
admission-preserves Server.countLimit w (admissionWorker r (reject l forkFailed)) s () bounded
admission-preserves Server.countLimit w (admissionWorker r (closeSocket reason)) s () bounded
admission-preserves Server.countLimit w (admissionWorker r (finished reason)) s () bounded
admission-preserves Server.countLimit w (admissionWorker r (countPublished p e)) s () bounded
admission-preserves Server.countLimit w (admissionWorker r (awaitHandshake p e)) s () bounded
admission-preserves Server.countLimit w (admissionWorker r (commitHandshake e result)) s () bounded
admission-preserves Server.countLimit w (admissionWorker r (countHandshake result)) s () bounded
admission-preserves Server.countLimit w (admissionWorker r (notifyInbound info)) s () bounded
admission-preserves Server.countLimit w (admissionWorker r (returnHandshake result)) s () bounded
admission-preserves Server.countLimit w (admissionWorker r (completedHandshake result)) s () bounded
admission-preserves Server.countLimit w (admissionWorker r impossibleHandshake) s () bounded
admission-preserves Server.countLimit w (admissionWorker r (count l)) s eq bounded with countIncoming (entries (cm s)) (savedMap l)
... | nothing = case eq of λ ()
... | just n with suc n ≤? hardLimit r
...   | yes _ = subst SupplyBounds (just-injective eq) bounded
...   | no _ = subst SupplyBounds (just-injective eq) bounded
admission-preserves Server.allocatePromise w (admissionWorker r acquireMap) s () bounded
admission-preserves Server.allocatePromise w (admissionWorker r (count l)) s () bounded
admission-preserves Server.allocatePromise w (admissionWorker r (selectEntry l p)) s () bounded
admission-preserves Server.allocatePromise w (admissionWorker r (forkHandler l p e)) s () bounded
admission-preserves Server.allocatePromise w (admissionWorker r (publish l p e)) s () bounded
admission-preserves Server.allocatePromise w (admissionWorker r (reject l hardLimitReached)) s () bounded
admission-preserves Server.allocatePromise w (admissionWorker r (reject l forbidden)) s () bounded
admission-preserves Server.allocatePromise w (admissionWorker r (reject l forkFailed)) s () bounded
admission-preserves Server.allocatePromise w (admissionWorker r (closeSocket reason)) s () bounded
admission-preserves Server.allocatePromise w (admissionWorker r (finished reason)) s () bounded
admission-preserves Server.allocatePromise w (admissionWorker r (countPublished p e)) s () bounded
admission-preserves Server.allocatePromise w (admissionWorker r (awaitHandshake p e)) s () bounded
admission-preserves Server.allocatePromise w (admissionWorker r (commitHandshake e result)) s () bounded
admission-preserves Server.allocatePromise w (admissionWorker r (countHandshake result)) s () bounded
admission-preserves Server.allocatePromise w (admissionWorker r (notifyInbound info)) s () bounded
admission-preserves Server.allocatePromise w (admissionWorker r (returnHandshake result)) s () bounded
admission-preserves Server.allocatePromise w (admissionWorker r (completedHandshake result)) s () bounded
admission-preserves Server.allocatePromise w (admissionWorker r impossibleHandshake) s () bounded
admission-preserves Server.allocatePromise w (admissionWorker r (prepare l)) s eq (eb , pb) = subst SupplyBounds (just-injective eq)
  (eb , promise-step (nextPromise s) (promises s) pb)
admission-preserves Server.chooseEntry w (admissionWorker r acquireMap) s () bounded
admission-preserves Server.chooseEntry w (admissionWorker r (count l)) s () bounded
admission-preserves Server.chooseEntry w (admissionWorker r (prepare l)) s () bounded
admission-preserves Server.chooseEntry w (admissionWorker r (forkHandler l p e)) s () bounded
admission-preserves Server.chooseEntry w (admissionWorker r (publish l p e)) s () bounded
admission-preserves Server.chooseEntry w (admissionWorker r (reject l hardLimitReached)) s () bounded
admission-preserves Server.chooseEntry w (admissionWorker r (reject l forbidden)) s () bounded
admission-preserves Server.chooseEntry w (admissionWorker r (reject l forkFailed)) s () bounded
admission-preserves Server.chooseEntry w (admissionWorker r (closeSocket reason)) s () bounded
admission-preserves Server.chooseEntry w (admissionWorker r (finished reason)) s () bounded
admission-preserves Server.chooseEntry w (admissionWorker r (countPublished p e)) s () bounded
admission-preserves Server.chooseEntry w (admissionWorker r (awaitHandshake p e)) s () bounded
admission-preserves Server.chooseEntry w (admissionWorker r (commitHandshake e result)) s () bounded
admission-preserves Server.chooseEntry w (admissionWorker r (countHandshake result)) s () bounded
admission-preserves Server.chooseEntry w (admissionWorker r (notifyInbound info)) s () bounded
admission-preserves Server.chooseEntry w (admissionWorker r (returnHandshake result)) s () bounded
admission-preserves Server.chooseEntry w (admissionWorker r (completedHandshake result)) s () bounded
admission-preserves Server.chooseEntry w (admissionWorker r impossibleHandshake) s () bounded
admission-preserves Server.chooseEntry w (admissionWorker r (selectEntry l p)) s eq (eb , pb) with CM.selectInbound l r (cm s) in selected
... | nothing = case eq of λ ()
... | just CM.denied = subst SupplyBounds (just-injective eq) (eb , pb)
... | just (CM.selected e c′) = subst SupplyBounds (just-injective eq) (selected-bound l r (cm s) selected eb , pb)
admission-preserves Server.fork w (admissionWorker r acquireMap) s () bounded
admission-preserves Server.fork w (admissionWorker r (count l)) s () bounded
admission-preserves Server.fork w (admissionWorker r (prepare l)) s () bounded
admission-preserves Server.fork w (admissionWorker r (selectEntry l p)) s () bounded
admission-preserves Server.fork w (admissionWorker r (publish l p e)) s () bounded
admission-preserves Server.fork w (admissionWorker r (reject l hardLimitReached)) s () bounded
admission-preserves Server.fork w (admissionWorker r (reject l forbidden)) s () bounded
admission-preserves Server.fork w (admissionWorker r (reject l forkFailed)) s () bounded
admission-preserves Server.fork w (admissionWorker r (closeSocket reason)) s () bounded
admission-preserves Server.fork w (admissionWorker r (finished reason)) s () bounded
admission-preserves Server.fork w (admissionWorker r (countPublished p e)) s () bounded
admission-preserves Server.fork w (admissionWorker r (awaitHandshake p e)) s () bounded
admission-preserves Server.fork w (admissionWorker r (commitHandshake e result)) s () bounded
admission-preserves Server.fork w (admissionWorker r (countHandshake result)) s () bounded
admission-preserves Server.fork w (admissionWorker r (notifyInbound info)) s () bounded
admission-preserves Server.fork w (admissionWorker r (returnHandshake result)) s () bounded
admission-preserves Server.fork w (admissionWorker r (completedHandshake result)) s () bounded
admission-preserves Server.fork w (admissionWorker r impossibleHandshake) s () bounded
admission-preserves Server.fork w (admissionWorker r (forkHandler l p e)) s eq bounded with lookup (child r) (handlers s) | lookup (child r) (admissions s)
... | nothing | nothing = subst SupplyBounds (just-injective eq) bounded
... | just _ | _ = case eq of λ ()
... | nothing | just _ = case eq of λ ()
admission-preserves Server.failFork w (admissionWorker r acquireMap) s () bounded
admission-preserves Server.failFork w (admissionWorker r (count l)) s () bounded
admission-preserves Server.failFork w (admissionWorker r (prepare l)) s () bounded
admission-preserves Server.failFork w (admissionWorker r (selectEntry l p)) s () bounded
admission-preserves Server.failFork w (admissionWorker r (publish l p e)) s () bounded
admission-preserves Server.failFork w (admissionWorker r (reject l hardLimitReached)) s () bounded
admission-preserves Server.failFork w (admissionWorker r (reject l forbidden)) s () bounded
admission-preserves Server.failFork w (admissionWorker r (reject l forkFailed)) s () bounded
admission-preserves Server.failFork w (admissionWorker r (closeSocket reason)) s () bounded
admission-preserves Server.failFork w (admissionWorker r (finished reason)) s () bounded
admission-preserves Server.failFork w (admissionWorker r (countPublished p e)) s () bounded
admission-preserves Server.failFork w (admissionWorker r (awaitHandshake p e)) s () bounded
admission-preserves Server.failFork w (admissionWorker r (commitHandshake e result)) s () bounded
admission-preserves Server.failFork w (admissionWorker r (countHandshake result)) s () bounded
admission-preserves Server.failFork w (admissionWorker r (notifyInbound info)) s () bounded
admission-preserves Server.failFork w (admissionWorker r (returnHandshake result)) s () bounded
admission-preserves Server.failFork w (admissionWorker r (completedHandshake result)) s () bounded
admission-preserves Server.failFork w (admissionWorker r impossibleHandshake) s () bounded
admission-preserves Server.failFork w (admissionWorker r (forkHandler l p e)) s eq bounded = subst SupplyBounds (just-injective eq) bounded
admission-preserves Server.readCounters w (admissionWorker r acquireMap) s () bounded
admission-preserves Server.readCounters w (admissionWorker r (count l)) s () bounded
admission-preserves Server.readCounters w (admissionWorker r (prepare l)) s () bounded
admission-preserves Server.readCounters w (admissionWorker r (selectEntry l p)) s () bounded
admission-preserves Server.readCounters w (admissionWorker r (forkHandler l p e)) s () bounded
admission-preserves Server.readCounters w (admissionWorker r (publish l p e)) s () bounded
admission-preserves Server.readCounters w (admissionWorker r (reject l hardLimitReached)) s () bounded
admission-preserves Server.readCounters w (admissionWorker r (reject l forbidden)) s () bounded
admission-preserves Server.readCounters w (admissionWorker r (reject l forkFailed)) s () bounded
admission-preserves Server.readCounters w (admissionWorker r (closeSocket reason)) s () bounded
admission-preserves Server.readCounters w (admissionWorker r (finished reason)) s () bounded
admission-preserves Server.readCounters w (admissionWorker r (awaitHandshake p e)) s () bounded
admission-preserves Server.readCounters w (admissionWorker r (commitHandshake e result)) s () bounded
admission-preserves Server.readCounters w (admissionWorker r (countHandshake result)) s () bounded
admission-preserves Server.readCounters w (admissionWorker r (notifyInbound info)) s () bounded
admission-preserves Server.readCounters w (admissionWorker r (returnHandshake result)) s () bounded
admission-preserves Server.readCounters w (admissionWorker r (completedHandshake result)) s () bounded
admission-preserves Server.readCounters w (admissionWorker r impossibleHandshake) s () bounded
admission-preserves Server.readCounters w (admissionWorker r (countPublished p e)) s eq bounded with mapCell (cm s)
... | taken _ = case eq of λ ()
... | full m with countIncoming (entries (cm s)) m
...   | nothing = case eq of λ ()
...   | just _ = subst SupplyBounds (just-injective eq) bounded
admission-preserves Server.close w (admissionWorker r acquireMap) s () bounded
admission-preserves Server.close w (admissionWorker r (count l)) s () bounded
admission-preserves Server.close w (admissionWorker r (prepare l)) s () bounded
admission-preserves Server.close w (admissionWorker r (selectEntry l p)) s () bounded
admission-preserves Server.close w (admissionWorker r (forkHandler l p e)) s () bounded
admission-preserves Server.close w (admissionWorker r (publish l p e)) s () bounded
admission-preserves Server.close w (admissionWorker r (reject l hardLimitReached)) s () bounded
admission-preserves Server.close w (admissionWorker r (reject l forbidden)) s () bounded
admission-preserves Server.close w (admissionWorker r (reject l forkFailed)) s () bounded
admission-preserves Server.close w (admissionWorker r (finished reason)) s () bounded
admission-preserves Server.close w (admissionWorker r (countPublished p e)) s () bounded
admission-preserves Server.close w (admissionWorker r (awaitHandshake p e)) s () bounded
admission-preserves Server.close w (admissionWorker r (commitHandshake e result)) s () bounded
admission-preserves Server.close w (admissionWorker r (countHandshake result)) s () bounded
admission-preserves Server.close w (admissionWorker r (notifyInbound info)) s () bounded
admission-preserves Server.close w (admissionWorker r (returnHandshake result)) s () bounded
admission-preserves Server.close w (admissionWorker r (completedHandshake result)) s () bounded
admission-preserves Server.close w (admissionWorker r impossibleHandshake) s () bounded
admission-preserves Server.close w (admissionWorker r (closeSocket reason)) s eq bounded = subst SupplyBounds (just-injective eq) bounded
admission-preserves Server.putMapBack w (admissionWorker r acquireMap) s () bounded
admission-preserves Server.putMapBack w (admissionWorker r (count l)) s () bounded
admission-preserves Server.putMapBack w (admissionWorker r (prepare l)) s () bounded
admission-preserves Server.putMapBack w (admissionWorker r (selectEntry l p)) s () bounded
admission-preserves Server.putMapBack w (admissionWorker r (forkHandler l p e)) s () bounded
admission-preserves Server.putMapBack w (admissionWorker r (reject l forbidden)) s () bounded
admission-preserves Server.putMapBack w (admissionWorker r (reject l forkFailed)) s () bounded
admission-preserves Server.putMapBack w (admissionWorker r (closeSocket reason)) s () bounded
admission-preserves Server.putMapBack w (admissionWorker r (finished reason)) s () bounded
admission-preserves Server.putMapBack w (admissionWorker r (countPublished p e)) s () bounded
admission-preserves Server.putMapBack w (admissionWorker r (awaitHandshake p e)) s () bounded
admission-preserves Server.putMapBack w (admissionWorker r (commitHandshake e result)) s () bounded
admission-preserves Server.putMapBack w (admissionWorker r (countHandshake result)) s () bounded
admission-preserves Server.putMapBack w (admissionWorker r (notifyInbound info)) s () bounded
admission-preserves Server.putMapBack w (admissionWorker r (returnHandshake result)) s () bounded
admission-preserves Server.putMapBack w (admissionWorker r (completedHandshake result)) s () bounded
admission-preserves Server.putMapBack w (admissionWorker r impossibleHandshake) s () bounded
admission-preserves Server.putMapBack w (admissionWorker r (publish l p e)) s eq (eb , pb) with CM.putMap l (insertConnection (key r) e (savedMap l)) (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst SupplyBounds (just-injective eq) (put-bound l (insertConnection (key r) e (savedMap l)) (cm s) putEq eb , pb)
admission-preserves Server.putMapBack w (admissionWorker r (reject l hardLimitReached)) s eq (eb , pb) with CM.putMap l (savedMap l) (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst SupplyBounds (just-injective eq) (put-bound l (savedMap l) (cm s) putEq eb , pb)
admission-preserves Server.restore w (admissionWorker r acquireMap) s () bounded
admission-preserves Server.restore w (admissionWorker r (count l)) s () bounded
admission-preserves Server.restore w (admissionWorker r (prepare l)) s () bounded
admission-preserves Server.restore w (admissionWorker r (selectEntry l p)) s () bounded
admission-preserves Server.restore w (admissionWorker r (forkHandler l p e)) s () bounded
admission-preserves Server.restore w (admissionWorker r (publish l p e)) s () bounded
admission-preserves Server.restore w (admissionWorker r (reject l hardLimitReached)) s () bounded
admission-preserves Server.restore w (admissionWorker r (closeSocket reason)) s () bounded
admission-preserves Server.restore w (admissionWorker r (finished reason)) s () bounded
admission-preserves Server.restore w (admissionWorker r (countPublished p e)) s () bounded
admission-preserves Server.restore w (admissionWorker r (awaitHandshake p e)) s () bounded
admission-preserves Server.restore w (admissionWorker r (commitHandshake e result)) s () bounded
admission-preserves Server.restore w (admissionWorker r (countHandshake result)) s () bounded
admission-preserves Server.restore w (admissionWorker r (notifyInbound info)) s () bounded
admission-preserves Server.restore w (admissionWorker r (returnHandshake result)) s () bounded
admission-preserves Server.restore w (admissionWorker r (completedHandshake result)) s () bounded
admission-preserves Server.restore w (admissionWorker r impossibleHandshake) s () bounded
admission-preserves Server.restore w (admissionWorker r (reject l forbidden)) s eq (eb , pb) with CM.putMap l (savedMap l) (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst SupplyBounds (just-injective eq) (put-bound l (savedMap l) (cm s) putEq eb , pb)
admission-preserves Server.restore w (admissionWorker r (reject l forkFailed)) s eq (eb , pb) with CM.putMap l (savedMap l) (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst SupplyBounds (just-injective eq) (put-bound l (savedMap l) (cm s) putEq eb , pb)
