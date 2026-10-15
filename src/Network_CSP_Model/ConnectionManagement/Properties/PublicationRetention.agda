{-# OPTIONS --guardedness #-}

-- Publication and handler-exit boundaries preserve existing reference chains.
-- Cleanup execution, negotiation consumers and IG updates remain separate.
module ConnectionManagement.Properties.PublicationRetention where

open import Data.Bool using (true; false)
open import Data.Bool.ListAction using (any)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst)
open import Data.Maybe.Properties using (just-injective)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
open import ConnectionManagement.Properties.StateRetention
open import ConnectionManagement.Properties.IGTableRetention using (fresh-lookup)
open import ConnectionManagement.Properties.HandlerCapture using (exit-retains)
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.Handshake as H
import ConnectionManagement.Rules.Cleanup as C
import ConnectionManagement.Rules.IGRegistration as IG

-- A fresh promise write preserves all previously available results.
fresh-result-retains : ∀ p result s → lookup p (handshakeResults s) ≡ nothing →
  Retains s (record s { handshakeResults = put p result (handshakeResults s) })
fresh-result-retains p result s absent = record
  { handlersRetained = λ _ _ found → found
  ; resultsRetained = λ q r found → fresh-lookup p q result r (handshakeResults s) absent found
  ; entriesRetained = λ _ present → present; socketsRetained = λ _ present → present }

publication-retains : ∀ w result s {s′} → H.publishBoundary w result s ≡ just (H.published s′) →
  Retains s s′
publication-retains w result s eq with lookup w (handlers s) | lookup w (cleanups s)
... | nothing | _ = case eq of λ ()
... | just _ | just _ = case eq of λ ()
... | just h | nothing with any (λ p → does (p ≟ handlerPromise h)) (promises s)
...   | false = case eq of λ ()
...   | true with lookup (handlerPromise h) (handshakeResults s) in found
...     | just _ = case eq of λ ()
...     | nothing with just-injective eq
...       | refl = fresh-result-retains (handlerPromise h) result s found

step-effects : ∀ w result outcome c {c′} → advance (handlerPublication w result outcome) c ≡ just c′ →
  Retains (world c) (world c′) × inboundGovernor c′ ≡ inboundGovernor c
step-effects w result outcome c eq
  with any (λ v → does (v ≟ w)) (publicationFaults c)
... | true = case eq of λ ()
... | false with H.publishBoundary w result (world c) in published | outcome
...   | nothing | _ = case eq of λ ()
...   | just (H.published s) | resultWritten with just-injective eq
...     | refl = publication-retains w result (world c) published , refl
step-effects w result outcome c eq | false | just (H.published s) | duplicateWrite = case eq of λ ()
step-effects w result outcome c eq | false | just H.writerBlocked | resultWritten = case eq of λ ()
step-effects w result outcome c eq | false | just H.writerBlocked | duplicateWrite with just-injective eq
... | refl = reframe _ refl refl (λ _ p → p) (λ _ p → p) , refl

