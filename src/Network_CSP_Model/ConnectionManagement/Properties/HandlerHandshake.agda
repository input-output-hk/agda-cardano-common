{-# OPTIONS --guardedness #-}

-- Handshake consumers retain original references even when removing map entries.
module ConnectionManagement.Properties.HandlerHandshake where

open import Data.Nat using (suc; _≤?_)
open import Data.List using ([]; _∷_; _++_; length)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.Entries using (Present; put-preserves-present)
open import ConnectionManagement.Properties.HandlerReferences
open import ConnectionManagement.Properties.HandlerAdmission using (reframe)
import ConnectionManagement.Rules.Handshake as H

import ConnectionManagement.Properties.HandlerConsumerEffects as Effects

-- Keep the existing chain API, using the shared effect proof so that
-- pre-publication resource evidence can use the same source-rule analysis.
from-effect : ∀ {q mid s s′ ig} → Effects.Effect s s′ → Chain q mid s ig → Chain q mid s′ ig
from-effect {s′ = s′} eff = reframe s′ (Effects.handlersSame eff) (Effects.resultsSame eff)
  (Effects.entriesRetained eff) (λ sock p → subst (Present sock)
    (sym (Effects.socketsSame eff)) p)

success-chain : ∀ w a e h f decision s {q mid ig} → Chain q mid s ig →
  Chain q mid (H.applySuccess w a e h f decision s) ig
success-chain w a e h f decision s = from-effect (Effects.success-effect w a e h f decision s)

terminate-chain : ∀ {q mid ig} w a e reason s {s′} → H.terminateResult w a e reason s ≡ just s′ →
  Chain q mid s ig → Chain q mid s′ ig
terminate-chain w a e reason s eq = from-effect (Effects.terminate-effect w a e reason s eq)

worker-chain : ∀ {q mid ig} act mode w a s {s′} → H.stepWorker mode w a act s ≡ just s′ →
  Chain q mid s ig → Chain q mid s′ ig
worker-chain act mode w a s eq = from-effect (Effects.worker-effect act mode w a s eq)

-- Consumer steps leave lifecycle frames and the IG execution engine untouched.
step-preserves : ∀ w a c {c′} → advance (handshakeStep w a) c ≡ just c′ →
  ∀ q → TrackedChain q c → TrackedChain q c′
step-preserves w a c eq q (f , found , chain) with lookup w (admissions (world c))
... | nothing = case eq of λ ()
... | just a₀ with H.stepWorker (responder c) w a₀ a (world c) in stepped
...   | nothing = case eq of λ ()
...   | just s′ with just-injective eq
...     | refl = f , found , worker-chain a (responder c) w a₀ (world c) stepped chain
