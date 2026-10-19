{-# OPTIONS --guardedness #-}

-- Admission preserves references and the allocation needed for map publication.
module ConnectionManagement.Properties.MapReferencesAdmission where

open import Data.Nat using (suc; _≤?_)
open import Data.List using (_∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Function using (case_of_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.State
open import ConnectionManagement.Properties.StateMapReferences
open import ConnectionManagement.Properties.MapReferenceLaws using (insert-references; map-retained)
import ConnectionManagement.Properties.AdmissionRetention as Retention
import ConnectionManagement.Properties.AdmissionAllocation as Allocation
open import ConnectionManagement.Properties.OwnershipNeutral using (selected-cell)
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.CM as CM

-- The selected worker certificate includes its pending publication identity.
admission-preserves : ∀ action w a s {s′} →
  Server.stepWorker w a action s ≡ just s′ → AdmissionValid (entries (cm s)) a → Valid s → Valid s′
admission-preserves Server.take w a@(admissionWorker r acquireMap) s eq av v with CM.takeMap w (cm s) in takenEq
... | nothing = case eq of λ ()
... | just (l , c′) = subst Valid (just-injective eq) (admission-update w a (count l) (record s { cm = c′ })
  (proj₂ (take-maps w s takenEq v)) (proj₁ (take-maps w s takenEq v)))
admission-preserves Server.take w (admissionWorker r (count l)) s () av v
admission-preserves Server.take w (admissionWorker r (prepare l)) s () av v
admission-preserves Server.take w (admissionWorker r (selectEntry l p)) s () av v
admission-preserves Server.take w (admissionWorker r (forkHandler l p e)) s () av v
admission-preserves Server.take w (admissionWorker r (publish l p e)) s () av v
admission-preserves Server.take w (admissionWorker r (reject l hardLimitReached)) s () av v
admission-preserves Server.take w (admissionWorker r (reject l forbidden)) s () av v
admission-preserves Server.take w (admissionWorker r (reject l forkFailed)) s () av v
admission-preserves Server.take w (admissionWorker r (closeSocket reason)) s () av v
admission-preserves Server.take w (admissionWorker r (finished reason)) s () av v
admission-preserves Server.take w (admissionWorker r (countPublished p e)) s () av v
admission-preserves Server.take w (admissionWorker r (awaitHandshake p e)) s () av v
admission-preserves Server.take w (admissionWorker r (commitHandshake e result)) s () av v
admission-preserves Server.take w (admissionWorker r (countHandshake result)) s () av v
admission-preserves Server.take w (admissionWorker r (notifyInbound info)) s () av v
admission-preserves Server.take w (admissionWorker r (returnHandshake result)) s () av v
admission-preserves Server.take w (admissionWorker r (completedHandshake result)) s () av v
admission-preserves Server.take w (admissionWorker r impossibleHandshake) s () av v
admission-preserves Server.countLimit w a@(admissionWorker r (count l)) s eq av v with countIncoming (entries (cm s)) (savedMap l)
... | nothing = case eq of λ ()
... | just n with suc n ≤? hardLimit r
...   | yes _ = subst Valid (just-injective eq) (admission-update w a (prepare l) s av v)
...   | no _ = subst Valid (just-injective eq) (admission-update w a (reject l hardLimitReached) s av v)
admission-preserves Server.countLimit w (admissionWorker r acquireMap) s () av v
admission-preserves Server.countLimit w (admissionWorker r (prepare l)) s () av v
admission-preserves Server.countLimit w (admissionWorker r (selectEntry l p)) s () av v
admission-preserves Server.countLimit w (admissionWorker r (forkHandler l p e)) s () av v
admission-preserves Server.countLimit w (admissionWorker r (publish l p e)) s () av v
admission-preserves Server.countLimit w (admissionWorker r (reject l hardLimitReached)) s () av v
admission-preserves Server.countLimit w (admissionWorker r (reject l forbidden)) s () av v
admission-preserves Server.countLimit w (admissionWorker r (reject l forkFailed)) s () av v
admission-preserves Server.countLimit w (admissionWorker r (closeSocket reason)) s () av v
admission-preserves Server.countLimit w (admissionWorker r (finished reason)) s () av v
admission-preserves Server.countLimit w (admissionWorker r (countPublished p e)) s () av v
admission-preserves Server.countLimit w (admissionWorker r (awaitHandshake p e)) s () av v
admission-preserves Server.countLimit w (admissionWorker r (commitHandshake e result)) s () av v
admission-preserves Server.countLimit w (admissionWorker r (countHandshake result)) s () av v
admission-preserves Server.countLimit w (admissionWorker r (notifyInbound info)) s () av v
admission-preserves Server.countLimit w (admissionWorker r (returnHandshake result)) s () av v
admission-preserves Server.countLimit w (admissionWorker r (completedHandshake result)) s () av v
admission-preserves Server.countLimit w (admissionWorker r impossibleHandshake) s () av v
admission-preserves Server.allocatePromise w a@(admissionWorker r (prepare l)) s eq av v = subst Valid (just-injective eq) (admission-update w a (selectEntry l (ident (nextPromise s)))
  (record s { promises = ident (nextPromise s) ∷ promises s; nextPromise = suc (nextPromise s) }) av v)
admission-preserves Server.allocatePromise w (admissionWorker r acquireMap) s () av v
admission-preserves Server.allocatePromise w (admissionWorker r (count l)) s () av v
admission-preserves Server.allocatePromise w (admissionWorker r (selectEntry l p)) s () av v
admission-preserves Server.allocatePromise w (admissionWorker r (forkHandler l p e)) s () av v
admission-preserves Server.allocatePromise w (admissionWorker r (publish l p e)) s () av v
admission-preserves Server.allocatePromise w (admissionWorker r (reject l hardLimitReached)) s () av v
admission-preserves Server.allocatePromise w (admissionWorker r (reject l forbidden)) s () av v
admission-preserves Server.allocatePromise w (admissionWorker r (reject l forkFailed)) s () av v
admission-preserves Server.allocatePromise w (admissionWorker r (closeSocket reason)) s () av v
admission-preserves Server.allocatePromise w (admissionWorker r (finished reason)) s () av v
admission-preserves Server.allocatePromise w (admissionWorker r (countPublished p e)) s () av v
admission-preserves Server.allocatePromise w (admissionWorker r (awaitHandshake p e)) s () av v
admission-preserves Server.allocatePromise w (admissionWorker r (commitHandshake e result)) s () av v
admission-preserves Server.allocatePromise w (admissionWorker r (countHandshake result)) s () av v
admission-preserves Server.allocatePromise w (admissionWorker r (notifyInbound info)) s () av v
admission-preserves Server.allocatePromise w (admissionWorker r (returnHandshake result)) s () av v
admission-preserves Server.allocatePromise w (admissionWorker r (completedHandshake result)) s () av v
admission-preserves Server.allocatePromise w (admissionWorker r impossibleHandshake) s () av v
admission-preserves Server.chooseEntry w a@(admissionWorker r (selectEntry l p)) s eq av v with CM.selectInbound l r (cm s) in selected
... | nothing = case eq of λ ()
... | just CM.denied = subst Valid (just-injective eq) (admission-update w a (reject l forbidden) s av v)
... | just (CM.selected e c′) = subst Valid (just-injective eq) (admission-update w a (forkHandler l p e) (record s { cm = c′ })
  (map-retained (entries (cm s)) (entries c′) (savedMap l)
    (Retention.selected-present l r (cm s) selected) av , Allocation.selected-allocated l r (cm s) selected)
  (replace-cm s c′ (selected-cell l r (cm s) selected)
    (Retention.selected-present l r (cm s) selected) v))
admission-preserves Server.chooseEntry w (admissionWorker r acquireMap) s () av v
admission-preserves Server.chooseEntry w (admissionWorker r (count l)) s () av v
admission-preserves Server.chooseEntry w (admissionWorker r (prepare l)) s () av v
admission-preserves Server.chooseEntry w (admissionWorker r (forkHandler l p e)) s () av v
admission-preserves Server.chooseEntry w (admissionWorker r (publish l p e)) s () av v
admission-preserves Server.chooseEntry w (admissionWorker r (reject l hardLimitReached)) s () av v
admission-preserves Server.chooseEntry w (admissionWorker r (reject l forbidden)) s () av v
admission-preserves Server.chooseEntry w (admissionWorker r (reject l forkFailed)) s () av v
admission-preserves Server.chooseEntry w (admissionWorker r (closeSocket reason)) s () av v
admission-preserves Server.chooseEntry w (admissionWorker r (finished reason)) s () av v
admission-preserves Server.chooseEntry w (admissionWorker r (countPublished p e)) s () av v
admission-preserves Server.chooseEntry w (admissionWorker r (awaitHandshake p e)) s () av v
admission-preserves Server.chooseEntry w (admissionWorker r (commitHandshake e result)) s () av v
admission-preserves Server.chooseEntry w (admissionWorker r (countHandshake result)) s () av v
admission-preserves Server.chooseEntry w (admissionWorker r (notifyInbound info)) s () av v
admission-preserves Server.chooseEntry w (admissionWorker r (returnHandshake result)) s () av v
admission-preserves Server.chooseEntry w (admissionWorker r (completedHandshake result)) s () av v
admission-preserves Server.chooseEntry w (admissionWorker r impossibleHandshake) s () av v
admission-preserves Server.fork w a@(admissionWorker r (forkHandler l p e)) s eq av v with lookup (child r) (handlers s) | lookup (child r) (admissions s)
... | nothing | nothing = subst Valid (just-injective eq) (admission-update w a (publish l p e) (record s
  { handlers = ConnectionManagement.Store.put (child r) (handlerStart e (socketRef r) p (key r)) (handlers s)
  ; sockets = ConnectionManagement.Store.put (socketRef r) (handling (child r)) (sockets s) }) av v)
... | just _ | _ = case eq of λ ()
... | nothing | just _ = case eq of λ ()
admission-preserves Server.fork w (admissionWorker r acquireMap) s () av v
admission-preserves Server.fork w (admissionWorker r (count l)) s () av v
admission-preserves Server.fork w (admissionWorker r (prepare l)) s () av v
admission-preserves Server.fork w (admissionWorker r (selectEntry l p)) s () av v
admission-preserves Server.fork w (admissionWorker r (publish l p e)) s () av v
admission-preserves Server.fork w (admissionWorker r (reject l hardLimitReached)) s () av v
admission-preserves Server.fork w (admissionWorker r (reject l forbidden)) s () av v
admission-preserves Server.fork w (admissionWorker r (reject l forkFailed)) s () av v
admission-preserves Server.fork w (admissionWorker r (closeSocket reason)) s () av v
admission-preserves Server.fork w (admissionWorker r (finished reason)) s () av v
admission-preserves Server.fork w (admissionWorker r (countPublished p e)) s () av v
admission-preserves Server.fork w (admissionWorker r (awaitHandshake p e)) s () av v
admission-preserves Server.fork w (admissionWorker r (commitHandshake e result)) s () av v
admission-preserves Server.fork w (admissionWorker r (countHandshake result)) s () av v
admission-preserves Server.fork w (admissionWorker r (notifyInbound info)) s () av v
admission-preserves Server.fork w (admissionWorker r (returnHandshake result)) s () av v
admission-preserves Server.fork w (admissionWorker r (completedHandshake result)) s () av v
admission-preserves Server.fork w (admissionWorker r impossibleHandshake) s () av v
admission-preserves Server.failFork w a@(admissionWorker r (forkHandler l p e)) s eq av v = subst Valid (just-injective eq) (admission-update w a (reject l forkFailed) s (proj₁ av) v)
admission-preserves Server.failFork w (admissionWorker r acquireMap) s () av v
admission-preserves Server.failFork w (admissionWorker r (count l)) s () av v
admission-preserves Server.failFork w (admissionWorker r (prepare l)) s () av v
admission-preserves Server.failFork w (admissionWorker r (selectEntry l p)) s () av v
admission-preserves Server.failFork w (admissionWorker r (publish l p e)) s () av v
admission-preserves Server.failFork w (admissionWorker r (reject l hardLimitReached)) s () av v
admission-preserves Server.failFork w (admissionWorker r (reject l forbidden)) s () av v
admission-preserves Server.failFork w (admissionWorker r (reject l forkFailed)) s () av v
admission-preserves Server.failFork w (admissionWorker r (closeSocket reason)) s () av v
admission-preserves Server.failFork w (admissionWorker r (finished reason)) s () av v
admission-preserves Server.failFork w (admissionWorker r (countPublished p e)) s () av v
admission-preserves Server.failFork w (admissionWorker r (awaitHandshake p e)) s () av v
admission-preserves Server.failFork w (admissionWorker r (commitHandshake e result)) s () av v
admission-preserves Server.failFork w (admissionWorker r (countHandshake result)) s () av v
admission-preserves Server.failFork w (admissionWorker r (notifyInbound info)) s () av v
admission-preserves Server.failFork w (admissionWorker r (returnHandshake result)) s () av v
admission-preserves Server.failFork w (admissionWorker r (completedHandshake result)) s () av v
admission-preserves Server.failFork w (admissionWorker r impossibleHandshake) s () av v
admission-preserves Server.readCounters w a@(admissionWorker r (countPublished p e)) s eq av v with mapCell (cm s) in cell
... | taken _ = case eq of λ ()
... | full m with countIncoming (entries (cm s)) m
...   | nothing = case eq of λ ()
...   | just _ = subst Valid (just-injective eq) (admission-update w a (awaitHandshake p e) s tt (restore-current s (full m) cell v))
admission-preserves Server.readCounters w (admissionWorker r acquireMap) s () av v
admission-preserves Server.readCounters w (admissionWorker r (count l)) s () av v
admission-preserves Server.readCounters w (admissionWorker r (prepare l)) s () av v
admission-preserves Server.readCounters w (admissionWorker r (selectEntry l p)) s () av v
admission-preserves Server.readCounters w (admissionWorker r (forkHandler l p e)) s () av v
admission-preserves Server.readCounters w (admissionWorker r (publish l p e)) s () av v
admission-preserves Server.readCounters w (admissionWorker r (reject l hardLimitReached)) s () av v
admission-preserves Server.readCounters w (admissionWorker r (reject l forbidden)) s () av v
admission-preserves Server.readCounters w (admissionWorker r (reject l forkFailed)) s () av v
admission-preserves Server.readCounters w (admissionWorker r (closeSocket reason)) s () av v
admission-preserves Server.readCounters w (admissionWorker r (finished reason)) s () av v
admission-preserves Server.readCounters w (admissionWorker r (awaitHandshake p e)) s () av v
admission-preserves Server.readCounters w (admissionWorker r (commitHandshake e result)) s () av v
admission-preserves Server.readCounters w (admissionWorker r (countHandshake result)) s () av v
admission-preserves Server.readCounters w (admissionWorker r (notifyInbound info)) s () av v
admission-preserves Server.readCounters w (admissionWorker r (returnHandshake result)) s () av v
admission-preserves Server.readCounters w (admissionWorker r (completedHandshake result)) s () av v
admission-preserves Server.readCounters w (admissionWorker r impossibleHandshake) s () av v
admission-preserves Server.close w a@(admissionWorker r (closeSocket reason)) s eq av v = subst Valid (just-injective eq) (admission-update w a (finished reason) (record s
  { sockets = ConnectionManagement.Store.put (socketRef r) closed (sockets s) }) tt v)
admission-preserves Server.close w (admissionWorker r acquireMap) s () av v
admission-preserves Server.close w (admissionWorker r (count l)) s () av v
admission-preserves Server.close w (admissionWorker r (prepare l)) s () av v
admission-preserves Server.close w (admissionWorker r (selectEntry l p)) s () av v
admission-preserves Server.close w (admissionWorker r (forkHandler l p e)) s () av v
admission-preserves Server.close w (admissionWorker r (publish l p e)) s () av v
admission-preserves Server.close w (admissionWorker r (reject l hardLimitReached)) s () av v
admission-preserves Server.close w (admissionWorker r (reject l forbidden)) s () av v
admission-preserves Server.close w (admissionWorker r (reject l forkFailed)) s () av v
admission-preserves Server.close w (admissionWorker r (finished reason)) s () av v
admission-preserves Server.close w (admissionWorker r (countPublished p e)) s () av v
admission-preserves Server.close w (admissionWorker r (awaitHandshake p e)) s () av v
admission-preserves Server.close w (admissionWorker r (commitHandshake e result)) s () av v
admission-preserves Server.close w (admissionWorker r (countHandshake result)) s () av v
admission-preserves Server.close w (admissionWorker r (notifyInbound info)) s () av v
admission-preserves Server.close w (admissionWorker r (returnHandshake result)) s () av v
admission-preserves Server.close w (admissionWorker r (completedHandshake result)) s () av v
admission-preserves Server.close w (admissionWorker r impossibleHandshake) s () av v
admission-preserves Server.putMapBack w a@(admissionWorker r (publish l p e)) s eq av v with CM.putMap l (insertConnection (key r) e (savedMap l)) (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst Valid (just-injective eq) (admission-update w a (countPublished p e) (record s { cm = c′ }) tt
  (put-maps l (insertConnection (key r) e (savedMap l)) s putEq
    (insert-references (entries (cm s)) (remote (key r)) (knownLocal (local (key r))) e (savedMap l) (proj₂ av) (proj₁ av)) v))
admission-preserves Server.putMapBack w a@(admissionWorker r (reject l hardLimitReached)) s eq av v with CM.restoreMap l (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst Valid (just-injective eq) (admission-update w a (closeSocket hardLimitReached) (record s { cm = c′ }) tt
  (put-maps l (savedMap l) s putEq av v))
admission-preserves Server.putMapBack w (admissionWorker r acquireMap) s () av v
admission-preserves Server.putMapBack w (admissionWorker r (count l)) s () av v
admission-preserves Server.putMapBack w (admissionWorker r (prepare l)) s () av v
admission-preserves Server.putMapBack w (admissionWorker r (selectEntry l p)) s () av v
admission-preserves Server.putMapBack w (admissionWorker r (forkHandler l p e)) s () av v
admission-preserves Server.putMapBack w (admissionWorker r (reject l forbidden)) s () av v
admission-preserves Server.putMapBack w (admissionWorker r (reject l forkFailed)) s () av v
admission-preserves Server.putMapBack w (admissionWorker r (closeSocket reason)) s () av v
admission-preserves Server.putMapBack w (admissionWorker r (finished reason)) s () av v
admission-preserves Server.putMapBack w (admissionWorker r (countPublished p e)) s () av v
admission-preserves Server.putMapBack w (admissionWorker r (awaitHandshake p e)) s () av v
admission-preserves Server.putMapBack w (admissionWorker r (commitHandshake e result)) s () av v
admission-preserves Server.putMapBack w (admissionWorker r (countHandshake result)) s () av v
admission-preserves Server.putMapBack w (admissionWorker r (notifyInbound info)) s () av v
admission-preserves Server.putMapBack w (admissionWorker r (returnHandshake result)) s () av v
admission-preserves Server.putMapBack w (admissionWorker r (completedHandshake result)) s () av v
admission-preserves Server.putMapBack w (admissionWorker r impossibleHandshake) s () av v
admission-preserves Server.restore w a@(admissionWorker r (reject l forbidden)) s eq av v with CM.restoreMap l (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst Valid (just-injective eq) (admission-update w a (closeSocket forbidden) (record s { cm = c′ }) tt
  (put-maps l (savedMap l) s putEq av v))
admission-preserves Server.restore w a@(admissionWorker r (reject l forkFailed)) s eq av v with CM.restoreMap l (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst Valid (just-injective eq) (admission-update w a (closeSocket forkFailed) (record s { cm = c′ }) tt
  (put-maps l (savedMap l) s putEq av v))
admission-preserves Server.restore w (admissionWorker r acquireMap) s () av v
admission-preserves Server.restore w (admissionWorker r (count l)) s () av v
admission-preserves Server.restore w (admissionWorker r (prepare l)) s () av v
admission-preserves Server.restore w (admissionWorker r (selectEntry l p)) s () av v
admission-preserves Server.restore w (admissionWorker r (forkHandler l p e)) s () av v
admission-preserves Server.restore w (admissionWorker r (publish l p e)) s () av v
admission-preserves Server.restore w (admissionWorker r (reject l hardLimitReached)) s () av v
admission-preserves Server.restore w (admissionWorker r (closeSocket reason)) s () av v
admission-preserves Server.restore w (admissionWorker r (finished reason)) s () av v
admission-preserves Server.restore w (admissionWorker r (countPublished p e)) s () av v
admission-preserves Server.restore w (admissionWorker r (awaitHandshake p e)) s () av v
admission-preserves Server.restore w (admissionWorker r (commitHandshake e result)) s () av v
admission-preserves Server.restore w (admissionWorker r (countHandshake result)) s () av v
admission-preserves Server.restore w (admissionWorker r (notifyInbound info)) s () av v
admission-preserves Server.restore w (admissionWorker r (returnHandshake result)) s () av v
admission-preserves Server.restore w (admissionWorker r (completedHandshake result)) s () av v
admission-preserves Server.restore w (admissionWorker r impossibleHandshake) s () av v
