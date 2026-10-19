{-# OPTIONS --guardedness #-}

-- Inbound handshake updates preserve all current and captured maps.
module ConnectionManagement.Properties.MapUniqueHandshake where

open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.StateMapUniqueness
open import ConnectionManagement.Properties.MapUniqueness using (delete-connection-unique)
import ConnectionManagement.Rules.Handshake as H
import ConnectionManagement.Rules.InformationChannel as Info

-- Successful-result commits publish lease-free continuations.
success-preserves : ∀ w a e h f decision s → Valid s → Valid (H.applySuccess w a e h f decision s)
success-preserves w a e h f (H.update st provenance) s v =
  admission-update w a (countHandshake (connected (newConnectionInfo provenance (key (request a)) f h)))
    (record s { cm = record (cm s) { entries = put e st (entries (cm s)) } }) tt v
success-preserves w a e h f (H.retain provenance) s v =
  admission-update w a (countHandshake (connected (newConnectionInfo provenance (key (request a)) f h))) s tt v
success-preserves w a e h f (H.disconnect reason) s v =
  admission-update w a (countHandshake (disconnected reason)) s tt v
success-preserves w a e h f H.impossible s v = admission-update w a impossibleHandshake s tt v

-- Identity-sensitive deletion preserves the unique full map.
terminate-preserves : ∀ w a e reason s {s′} → H.terminateResult w a e reason s ≡ just s′ →
  Valid s → Valid s′
terminate-preserves w a e reason s eq v with lookup e (entries (cm s)) | mapCell (cm s) in cell
... | nothing | _ = case eq of λ ()
... | just _ | taken _ = case eq of λ ()
... | just _ | full m with lookupConnection (key (request a)) m
...   | nothing = subst Valid (just-injective eq)
  (admission-update w a (countHandshake (disconnected reason)) s tt (restore-current s (full m) cell v))
...   | just current with e ≟ current
...     | no _ = subst Valid (just-injective eq)
  (admission-update w a (countHandshake (disconnected reason)) s tt (restore-current s (full m) cell v))
...     | yes _ = subst Valid (just-injective eq)
  (admission-update w a (countHandshake (disconnected reason)) (record s { cm = record (cm s)
    { mapCell = full (deleteConnection (key (request a)) m)
    ; entries = put e (H.errorState (request a) reason) (entries (cm s)) } }) tt
    (delete-connection-unique (key (request a)) m (proj₁ v) , proj₂ v))

-- Handshake continuations do not introduce saved or prospective maps.
handshake-preserves : ∀ action mode w a s {s′} → H.stepWorker mode w a action s ≡ just s′ →
  Valid s → Valid s′
handshake-preserves H.readResult mode w a@(admissionWorker r (awaitHandshake p e)) s eq v with lookup p (handshakeResults s)
... | nothing = case eq of λ ()
... | just result = subst Valid (just-injective eq) (admission-update w a (commitHandshake e result) s tt v)
handshake-preserves H.readResult mode w (admissionWorker r acquireMap) s () v
handshake-preserves H.readResult mode w (admissionWorker r (count l)) s () v
handshake-preserves H.readResult mode w (admissionWorker r (prepare l)) s () v
handshake-preserves H.readResult mode w (admissionWorker r (selectEntry l p)) s () v
handshake-preserves H.readResult mode w (admissionWorker r (forkHandler l p e)) s () v
handshake-preserves H.readResult mode w (admissionWorker r (publish l p e)) s () v
handshake-preserves H.readResult mode w (admissionWorker r (reject l reason)) s () v
handshake-preserves H.readResult mode w (admissionWorker r (closeSocket reason)) s () v
handshake-preserves H.readResult mode w (admissionWorker r (finished reason)) s () v
handshake-preserves H.readResult mode w (admissionWorker r (countPublished p e)) s () v
handshake-preserves H.readResult mode w (admissionWorker r (commitHandshake e result)) s () v
handshake-preserves H.readResult mode w (admissionWorker r (countHandshake result)) s () v
handshake-preserves H.readResult mode w (admissionWorker r (notifyInbound info)) s () v
handshake-preserves H.readResult mode w (admissionWorker r (returnHandshake result)) s () v
handshake-preserves H.readResult mode w (admissionWorker r (completedHandshake result)) s () v
handshake-preserves H.readResult mode w (admissionWorker r impossibleHandshake) s () v
handshake-preserves H.commitResult mode w a@(admissionWorker r (commitHandshake e (negotiated h f))) s eq v with lookup e (entries (cm s))
... | nothing = case eq of λ ()
... | just st = subst Valid (just-injective eq) (success-preserves w a e h f (H.decideSuccess r h f st) s v)
handshake-preserves H.commitResult mode w a@(admissionWorker r (commitHandshake e query)) s eq v = terminate-preserves w a e handshakeQuery s eq v
handshake-preserves H.commitResult mode w a@(admissionWorker r (commitHandshake e (handlerError cls err))) s eq v = terminate-preserves w a e (handshakeError cls err) s eq v
handshake-preserves H.commitResult mode w (admissionWorker r acquireMap) s () v
handshake-preserves H.commitResult mode w (admissionWorker r (count l)) s () v
handshake-preserves H.commitResult mode w (admissionWorker r (prepare l)) s () v
handshake-preserves H.commitResult mode w (admissionWorker r (selectEntry l p)) s () v
handshake-preserves H.commitResult mode w (admissionWorker r (forkHandler l p e)) s () v
handshake-preserves H.commitResult mode w (admissionWorker r (publish l p e)) s () v
handshake-preserves H.commitResult mode w (admissionWorker r (reject l reason)) s () v
handshake-preserves H.commitResult mode w (admissionWorker r (closeSocket reason)) s () v
handshake-preserves H.commitResult mode w (admissionWorker r (finished reason)) s () v
handshake-preserves H.commitResult mode w (admissionWorker r (countPublished p e)) s () v
handshake-preserves H.commitResult mode w (admissionWorker r (awaitHandshake p e)) s () v
handshake-preserves H.commitResult mode w (admissionWorker r (countHandshake result)) s () v
handshake-preserves H.commitResult mode w (admissionWorker r (notifyInbound info)) s () v
handshake-preserves H.commitResult mode w (admissionWorker r (returnHandshake result)) s () v
handshake-preserves H.commitResult mode w (admissionWorker r (completedHandshake result)) s () v
handshake-preserves H.commitResult mode w (admissionWorker r impossibleHandshake) s () v
handshake-preserves H.readResultCounters mode w a@(admissionWorker r (countHandshake result)) s eq v with mapCell (cm s) in cell
... | taken _ = case eq of λ ()
... | full m with countIncoming (entries (cm s)) m
...   | nothing = case eq of λ ()
...   | just _ with result | mode
...     | connected info | responderMode = subst Valid (just-injective eq) (admission-update w a (notifyInbound info) s tt (restore-current s (full m) cell v))
...     | connected info | noResponderMode = subst Valid (just-injective eq) (admission-update w a (returnHandshake (connected info)) s tt (restore-current s (full m) cell v))
...     | disconnected reason | _ = subst Valid (just-injective eq) (admission-update w a (returnHandshake (disconnected reason)) s tt (restore-current s (full m) cell v))
handshake-preserves H.readResultCounters mode w (admissionWorker r acquireMap) s () v
handshake-preserves H.readResultCounters mode w (admissionWorker r (count l)) s () v
handshake-preserves H.readResultCounters mode w (admissionWorker r (prepare l)) s () v
handshake-preserves H.readResultCounters mode w (admissionWorker r (selectEntry l p)) s () v
handshake-preserves H.readResultCounters mode w (admissionWorker r (forkHandler l p e)) s () v
handshake-preserves H.readResultCounters mode w (admissionWorker r (publish l p e)) s () v
handshake-preserves H.readResultCounters mode w (admissionWorker r (reject l reason)) s () v
handshake-preserves H.readResultCounters mode w (admissionWorker r (closeSocket reason)) s () v
handshake-preserves H.readResultCounters mode w (admissionWorker r (finished reason)) s () v
handshake-preserves H.readResultCounters mode w (admissionWorker r (countPublished p e)) s () v
handshake-preserves H.readResultCounters mode w (admissionWorker r (awaitHandshake p e)) s () v
handshake-preserves H.readResultCounters mode w (admissionWorker r (commitHandshake e result)) s () v
handshake-preserves H.readResultCounters mode w (admissionWorker r (notifyInbound info)) s () v
handshake-preserves H.readResultCounters mode w (admissionWorker r (returnHandshake result)) s () v
handshake-preserves H.readResultCounters mode w (admissionWorker r (completedHandshake result)) s () v
handshake-preserves H.readResultCounters mode w (admissionWorker r impossibleHandshake) s () v
handshake-preserves H.enqueueInbound mode w a@(admissionWorker r (notifyInbound info)) s eq v with Info.writeMessage (newConnection info) (inboundInfo s)
... | nothing = case eq of λ ()
... | just queue = subst Valid (just-injective eq) (admission-update w a (returnHandshake (connected info)) (record s { inboundInfo = queue }) tt v)
handshake-preserves H.enqueueInbound mode w (admissionWorker r acquireMap) s () v
handshake-preserves H.enqueueInbound mode w (admissionWorker r (count l)) s () v
handshake-preserves H.enqueueInbound mode w (admissionWorker r (prepare l)) s () v
handshake-preserves H.enqueueInbound mode w (admissionWorker r (selectEntry l p)) s () v
handshake-preserves H.enqueueInbound mode w (admissionWorker r (forkHandler l p e)) s () v
handshake-preserves H.enqueueInbound mode w (admissionWorker r (publish l p e)) s () v
handshake-preserves H.enqueueInbound mode w (admissionWorker r (reject l reason)) s () v
handshake-preserves H.enqueueInbound mode w (admissionWorker r (closeSocket reason)) s () v
handshake-preserves H.enqueueInbound mode w (admissionWorker r (finished reason)) s () v
handshake-preserves H.enqueueInbound mode w (admissionWorker r (countPublished p e)) s () v
handshake-preserves H.enqueueInbound mode w (admissionWorker r (awaitHandshake p e)) s () v
handshake-preserves H.enqueueInbound mode w (admissionWorker r (commitHandshake e result)) s () v
handshake-preserves H.enqueueInbound mode w (admissionWorker r (countHandshake result)) s () v
handshake-preserves H.enqueueInbound mode w (admissionWorker r (returnHandshake result)) s () v
handshake-preserves H.enqueueInbound mode w (admissionWorker r (completedHandshake result)) s () v
handshake-preserves H.enqueueInbound mode w (admissionWorker r impossibleHandshake) s () v
handshake-preserves H.returnResult mode w a@(admissionWorker r (returnHandshake result)) s eq v = subst Valid (just-injective eq) (admission-update w a (completedHandshake result) s tt v)
handshake-preserves H.returnResult mode w (admissionWorker r acquireMap) s () v
handshake-preserves H.returnResult mode w (admissionWorker r (count l)) s () v
handshake-preserves H.returnResult mode w (admissionWorker r (prepare l)) s () v
handshake-preserves H.returnResult mode w (admissionWorker r (selectEntry l p)) s () v
handshake-preserves H.returnResult mode w (admissionWorker r (forkHandler l p e)) s () v
handshake-preserves H.returnResult mode w (admissionWorker r (publish l p e)) s () v
handshake-preserves H.returnResult mode w (admissionWorker r (reject l reason)) s () v
handshake-preserves H.returnResult mode w (admissionWorker r (closeSocket reason)) s () v
handshake-preserves H.returnResult mode w (admissionWorker r (finished reason)) s () v
handshake-preserves H.returnResult mode w (admissionWorker r (countPublished p e)) s () v
handshake-preserves H.returnResult mode w (admissionWorker r (awaitHandshake p e)) s () v
handshake-preserves H.returnResult mode w (admissionWorker r (commitHandshake e result)) s () v
handshake-preserves H.returnResult mode w (admissionWorker r (countHandshake result)) s () v
handshake-preserves H.returnResult mode w (admissionWorker r (notifyInbound info)) s () v
handshake-preserves H.returnResult mode w (admissionWorker r (completedHandshake result)) s () v
handshake-preserves H.returnResult mode w (admissionWorker r impossibleHandshake) s () v
