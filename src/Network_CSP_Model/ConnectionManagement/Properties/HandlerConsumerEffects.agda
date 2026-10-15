{-# OPTIONS --guardedness #-}

-- Heap-preserving effects of parent publication and handshake consumption.
-- This is an explicit interference alphabet, not all dispatcher actions.
module ConnectionManagement.Properties.HandlerConsumerEffects where

open import Data.Nat using (suc; _≤?_)
open import Data.List using ([]; _∷_; _++_; length)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.Entries using (Present; put-preserves-present)
open import ConnectionManagement.Properties.HandlerCleanup using (put-entries)
import ConnectionManagement.Rules.Handshake as H
import ConnectionManagement.Rules.Server as S
import ConnectionManagement.Rules.CM as CM

-- Exact immutable-store equality plus retention of mutable entry identities.
record Effect (s s′ : State) : Set where
  constructor effect
  field
    handlersSame : handlers s′ ≡ handlers s
    resultsSame : handshakeResults s′ ≡ handshakeResults s
    socketsSame : sockets s′ ≡ sockets s
    entriesRetained : ∀ e → Present e (entries (cm s)) → Present e (entries (cm s′))
open Effect public

success-effect : ∀ w a e h f decision s →
  Effect s (H.applySuccess w a e h f decision s)
success-effect w a e h f (H.update st provenance) s =
  effect refl refl refl (λ ref → put-preserves-present e ref st (entries (cm s)))
success-effect w a e h f (H.retain provenance) s = effect refl refl refl (λ _ p → p)
success-effect w a e h f (H.disconnect reason) s = effect refl refl refl (λ _ p → p)
success-effect w a e h f H.impossible s = effect refl refl refl (λ _ p → p)

terminate-effect : ∀ w a e reason s {s′} → H.terminateResult w a e reason s ≡ just s′ →
  Effect s s′
terminate-effect w a e reason s eq with lookup e (entries (cm s)) | mapCell (cm s)
... | nothing | _ = case eq of λ ()
... | just _ | taken _ = case eq of λ ()
... | just _ | full m with lookupConnection (key (request a)) m
...   | nothing = subst (Effect s) (just-injective eq) (effect refl refl refl (λ _ p → p))
...   | just current with e ≟ current
...     | no _ = subst (Effect s) (just-injective eq) (effect refl refl refl (λ _ p → p))
...     | yes _ = subst (Effect s) (just-injective eq)
  (effect refl refl refl (λ ref → put-preserves-present e ref (H.errorState (request a) reason) (entries (cm s))))

worker-effect : ∀ act mode w a s {s′} → H.stepWorker mode w a act s ≡ just s′ →
  Effect s s′
worker-effect H.readResult mode w (admissionWorker r acquireMap) s ()
worker-effect H.readResult mode w (admissionWorker r (count l)) s ()
worker-effect H.readResult mode w (admissionWorker r (prepare l)) s ()
worker-effect H.readResult mode w (admissionWorker r (selectEntry l p)) s ()
worker-effect H.readResult mode w (admissionWorker r (forkHandler l p e)) s ()
worker-effect H.readResult mode w (admissionWorker r (publish l p e)) s ()
worker-effect H.readResult mode w (admissionWorker r (reject l reason)) s ()
worker-effect H.readResult mode w (admissionWorker r (closeSocket reason)) s ()
worker-effect H.readResult mode w (admissionWorker r (finished reason)) s ()
worker-effect H.readResult mode w (admissionWorker r (countPublished p e)) s ()
worker-effect H.readResult mode w (admissionWorker r (commitHandshake e result)) s ()
worker-effect H.readResult mode w (admissionWorker r (countHandshake result)) s ()
worker-effect H.readResult mode w (admissionWorker r (notifyInbound info)) s ()
worker-effect H.readResult mode w (admissionWorker r (returnHandshake result)) s ()
worker-effect H.readResult mode w (admissionWorker r (completedHandshake result)) s ()
worker-effect H.readResult mode w (admissionWorker r impossibleHandshake) s ()
worker-effect H.readResult mode w a@(admissionWorker r (awaitHandshake p e)) s eq with lookup p (handshakeResults s)
... | nothing = case eq of λ ()
... | just result = subst (Effect s) (just-injective eq) (effect refl refl refl (λ _ p → p))
worker-effect H.commitResult mode w (admissionWorker r acquireMap) s ()
worker-effect H.commitResult mode w (admissionWorker r (count l)) s ()
worker-effect H.commitResult mode w (admissionWorker r (prepare l)) s ()
worker-effect H.commitResult mode w (admissionWorker r (selectEntry l p)) s ()
worker-effect H.commitResult mode w (admissionWorker r (forkHandler l p e)) s ()
worker-effect H.commitResult mode w (admissionWorker r (publish l p e)) s ()
worker-effect H.commitResult mode w (admissionWorker r (reject l reason)) s ()
worker-effect H.commitResult mode w (admissionWorker r (closeSocket reason)) s ()
worker-effect H.commitResult mode w (admissionWorker r (finished reason)) s ()
worker-effect H.commitResult mode w (admissionWorker r (countPublished p e)) s ()
worker-effect H.commitResult mode w (admissionWorker r (awaitHandshake p e)) s ()
worker-effect H.commitResult mode w (admissionWorker r (countHandshake result)) s ()
worker-effect H.commitResult mode w (admissionWorker r (notifyInbound info)) s ()
worker-effect H.commitResult mode w (admissionWorker r (returnHandshake result)) s ()
worker-effect H.commitResult mode w (admissionWorker r (completedHandshake result)) s ()
worker-effect H.commitResult mode w (admissionWorker r impossibleHandshake) s ()
worker-effect H.commitResult mode w a@(admissionWorker r (commitHandshake e (negotiated h f))) s eq with lookup e (entries (cm s))
... | nothing = case eq of λ ()
... | just st = subst (Effect s) (just-injective eq) (success-effect w a e h f (H.decideSuccess r h f st) s)
worker-effect H.commitResult mode w a@(admissionWorker r (commitHandshake e query)) s eq = terminate-effect w a e handshakeQuery s eq
worker-effect H.commitResult mode w a@(admissionWorker r (commitHandshake e (handlerError cls err))) s eq = terminate-effect w a e (handshakeError cls err) s eq
worker-effect H.readResultCounters mode w (admissionWorker r acquireMap) s ()
worker-effect H.readResultCounters mode w (admissionWorker r (count l)) s ()
worker-effect H.readResultCounters mode w (admissionWorker r (prepare l)) s ()
worker-effect H.readResultCounters mode w (admissionWorker r (selectEntry l p)) s ()
worker-effect H.readResultCounters mode w (admissionWorker r (forkHandler l p e)) s ()
worker-effect H.readResultCounters mode w (admissionWorker r (publish l p e)) s ()
worker-effect H.readResultCounters mode w (admissionWorker r (reject l reason)) s ()
worker-effect H.readResultCounters mode w (admissionWorker r (closeSocket reason)) s ()
worker-effect H.readResultCounters mode w (admissionWorker r (finished reason)) s ()
worker-effect H.readResultCounters mode w (admissionWorker r (countPublished p e)) s ()
worker-effect H.readResultCounters mode w (admissionWorker r (awaitHandshake p e)) s ()
worker-effect H.readResultCounters mode w (admissionWorker r (commitHandshake e result)) s ()
worker-effect H.readResultCounters mode w (admissionWorker r (notifyInbound info)) s ()
worker-effect H.readResultCounters mode w (admissionWorker r (returnHandshake result)) s ()
worker-effect H.readResultCounters mode w (admissionWorker r (completedHandshake result)) s ()
worker-effect H.readResultCounters mode w (admissionWorker r impossibleHandshake) s ()
worker-effect H.readResultCounters mode w a@(admissionWorker r (countHandshake result)) s eq with mapCell (cm s)
... | taken _ = case eq of λ ()
... | full m with countIncoming (entries (cm s)) m
...   | nothing = case eq of λ ()
...   | just _ with result | mode
...     | connected info | responderMode = subst (Effect s) (just-injective eq) (effect refl refl refl (λ _ p → p))
...     | connected info | noResponderMode = subst (Effect s) (just-injective eq) (effect refl refl refl (λ _ p → p))
...     | disconnected reason | _ = subst (Effect s) (just-injective eq) (effect refl refl refl (λ _ p → p))
worker-effect H.enqueueInbound mode w (admissionWorker r acquireMap) s ()
worker-effect H.enqueueInbound mode w (admissionWorker r (count l)) s ()
worker-effect H.enqueueInbound mode w (admissionWorker r (prepare l)) s ()
worker-effect H.enqueueInbound mode w (admissionWorker r (selectEntry l p)) s ()
worker-effect H.enqueueInbound mode w (admissionWorker r (forkHandler l p e)) s ()
worker-effect H.enqueueInbound mode w (admissionWorker r (publish l p e)) s ()
worker-effect H.enqueueInbound mode w (admissionWorker r (reject l reason)) s ()
worker-effect H.enqueueInbound mode w (admissionWorker r (closeSocket reason)) s ()
worker-effect H.enqueueInbound mode w (admissionWorker r (finished reason)) s ()
worker-effect H.enqueueInbound mode w (admissionWorker r (countPublished p e)) s ()
worker-effect H.enqueueInbound mode w (admissionWorker r (awaitHandshake p e)) s ()
worker-effect H.enqueueInbound mode w (admissionWorker r (commitHandshake e result)) s ()
worker-effect H.enqueueInbound mode w (admissionWorker r (countHandshake result)) s ()
worker-effect H.enqueueInbound mode w (admissionWorker r (returnHandshake result)) s ()
worker-effect H.enqueueInbound mode w (admissionWorker r (completedHandshake result)) s ()
worker-effect H.enqueueInbound mode w (admissionWorker r impossibleHandshake) s ()
worker-effect H.enqueueInbound mode w a@(admissionWorker r (notifyInbound info)) s eq with suc (length (inboundInfo s)) ≤? 100
... | no _ = case eq of λ ()
... | yes _ = subst (Effect s) (just-injective eq) (effect refl refl refl (λ _ p → p))
worker-effect H.returnResult mode w (admissionWorker r acquireMap) s ()
worker-effect H.returnResult mode w (admissionWorker r (count l)) s ()
worker-effect H.returnResult mode w (admissionWorker r (prepare l)) s ()
worker-effect H.returnResult mode w (admissionWorker r (selectEntry l p)) s ()
worker-effect H.returnResult mode w (admissionWorker r (forkHandler l p e)) s ()
worker-effect H.returnResult mode w (admissionWorker r (publish l p e)) s ()
worker-effect H.returnResult mode w (admissionWorker r (reject l reason)) s ()
worker-effect H.returnResult mode w (admissionWorker r (closeSocket reason)) s ()
worker-effect H.returnResult mode w (admissionWorker r (finished reason)) s ()
worker-effect H.returnResult mode w (admissionWorker r (countPublished p e)) s ()
worker-effect H.returnResult mode w (admissionWorker r (awaitHandshake p e)) s ()
worker-effect H.returnResult mode w (admissionWorker r (commitHandshake e result)) s ()
worker-effect H.returnResult mode w (admissionWorker r (countHandshake result)) s ()
worker-effect H.returnResult mode w (admissionWorker r (notifyInbound info)) s ()
worker-effect H.returnResult mode w (admissionWorker r (completedHandshake result)) s ()
worker-effect H.returnResult mode w (admissionWorker r impossibleHandshake) s ()
worker-effect H.returnResult mode w a@(admissionWorker r (returnHandshake result)) s eq = subst (Effect s) (just-injective eq) (effect refl refl refl (λ _ p → p))


-- Only the two parent operations that can run around handler publication.
data ParentAction : S.AdmissionAction → Set where
  publish : ParentAction S.putMapBack
  counters : ParentAction S.readCounters

parent-worker : ∀ act → ParentAction act → ∀ w a s {s′} →
  S.stepWorker w a act s ≡ just s′ → Effect s s′
parent-worker S.readCounters counters w (admissionWorker r acquireMap) s ()
parent-worker S.readCounters counters w (admissionWorker r (count l)) s ()
parent-worker S.readCounters counters w (admissionWorker r (prepare l)) s ()
parent-worker S.readCounters counters w (admissionWorker r (selectEntry l p)) s ()
parent-worker S.readCounters counters w (admissionWorker r (forkHandler l p e)) s ()
parent-worker S.readCounters counters w (admissionWorker r (publish l p e)) s ()
parent-worker S.readCounters counters w (admissionWorker r (reject l reason)) s ()
parent-worker S.readCounters counters w (admissionWorker r (closeSocket reason)) s ()
parent-worker S.readCounters counters w (admissionWorker r (finished reason)) s ()
parent-worker S.readCounters counters w (admissionWorker r (awaitHandshake p e)) s ()
parent-worker S.readCounters counters w (admissionWorker r (commitHandshake e result)) s ()
parent-worker S.readCounters counters w (admissionWorker r (countHandshake result)) s ()
parent-worker S.readCounters counters w (admissionWorker r (notifyInbound info)) s ()
parent-worker S.readCounters counters w (admissionWorker r (returnHandshake result)) s ()
parent-worker S.readCounters counters w (admissionWorker r (completedHandshake result)) s ()
parent-worker S.readCounters counters w (admissionWorker r impossibleHandshake) s ()
parent-worker S.readCounters counters w a@(admissionWorker r (countPublished p e)) s eq with mapCell (cm s)
... | taken _ = case eq of λ ()
... | full m with countIncoming (entries (cm s)) m
...   | nothing = case eq of λ ()
...   | just _ = subst (Effect s) (just-injective eq) (effect refl refl refl (λ _ p → p))
parent-worker S.putMapBack publish w (admissionWorker r acquireMap) s ()
parent-worker S.putMapBack publish w (admissionWorker r (count l)) s ()
parent-worker S.putMapBack publish w (admissionWorker r (prepare l)) s ()
parent-worker S.putMapBack publish w (admissionWorker r (selectEntry l p)) s ()
parent-worker S.putMapBack publish w (admissionWorker r (forkHandler l p e)) s ()
parent-worker S.putMapBack publish w (admissionWorker r (closeSocket reason)) s ()
parent-worker S.putMapBack publish w (admissionWorker r (finished reason)) s ()
parent-worker S.putMapBack publish w (admissionWorker r (countPublished p e)) s ()
parent-worker S.putMapBack publish w (admissionWorker r (awaitHandshake p e)) s ()
parent-worker S.putMapBack publish w (admissionWorker r (commitHandshake e result)) s ()
parent-worker S.putMapBack publish w (admissionWorker r (countHandshake result)) s ()
parent-worker S.putMapBack publish w (admissionWorker r (notifyInbound info)) s ()
parent-worker S.putMapBack publish w (admissionWorker r (returnHandshake result)) s ()
parent-worker S.putMapBack publish w (admissionWorker r (completedHandshake result)) s ()
parent-worker S.putMapBack publish w (admissionWorker r impossibleHandshake) s ()
parent-worker S.putMapBack publish w (admissionWorker r (reject l forbidden)) s ()
parent-worker S.putMapBack publish w (admissionWorker r (reject l forkFailed)) s ()
parent-worker S.putMapBack publish w a@(admissionWorker r (publish l p e)) s eq with CM.putMap l (insertConnection (key r) e (savedMap l)) (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst (Effect s) (just-injective eq) (effect refl refl refl (λ ref present → subst (Present ref) (sym (put-entries l (insertConnection (key r) e (savedMap l)) (cm s) putEq)) present))
parent-worker S.putMapBack publish w a@(admissionWorker r (reject l hardLimitReached)) s eq with CM.restoreMap l (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst (Effect s) (just-injective eq) (effect refl refl refl (λ ref present → subst (Present ref) (sym (put-entries l (savedMap l) (cm s) putEq)) present))
