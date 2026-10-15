{-# OPTIONS --guardedness #-}

-- Capture-retention API, now derived from the shared dispatcher edit witness.
module ConnectionManagement.Properties.HandlerCaptureInvariant where

open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerCapture
open import ConnectionManagement.Properties.HandlerEvolutionInvariant using (advance-evolves)

advance-retains : ∀ a c {c′} → advance a c ≡ just c′ →
  Retains (handlerLifecycles c) (handlerLifecycles c′)
advance-retains a c eq = evolution-retains (advance-evolves a c eq)

-- Arbitrary finite action sequences, including other workers' actions.
exec-retains : ∀ {c as c′} → Executes c as c′ →
  Retains (handlerLifecycles c) (handlerLifecycles c′)
exec-retains {c} done = retains-refl (handlerLifecycles c)
exec-retains (next {c = c} {c₁ = c₁} {c₂ = c₂} {a = a} eq rest) =
  retains-trans {handlerLifecycles c} {handlerLifecycles c₁} {handlerLifecycles c₂}
    (advance-retains a c eq) (exec-retains rest)
replay-retains : ∀ as c {c′} → replay as c ≡ just c′ →
  Retains (handlerLifecycles c) (handlerLifecycles c′)
replay-retains as c eq = exec-retains (replay-sound as c eq)
