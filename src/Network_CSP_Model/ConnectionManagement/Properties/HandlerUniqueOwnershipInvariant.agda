{-# OPTIONS --guardedness #-}

-- Unique tracked ownership is preserved by arbitrary successful machine steps.
module ConnectionManagement.Properties.HandlerUniqueOwnershipInvariant where

open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerUniqueOwnership
open import ConnectionManagement.Properties.HandlerEvolutionInvariant using (advance-evolves)

advance-preserves : ∀ a c {c′} → advance a c ≡ just c′ →
  Unique (handlerLifecycles c) → Unique (handlerLifecycles c′)
advance-preserves a c eq = evolution-preserves (advance-evolves a c eq)
exec-preserves : ∀ {c as c′} → Unique (handlerLifecycles c) → Executes c as c′ →
  Unique (handlerLifecycles c′)
exec-preserves unique done = unique
exec-preserves unique (next {c = c} {a = a} eq rest) =
  exec-preserves (advance-preserves a c eq unique) rest
replay-preserves : ∀ as c {c′} → Unique (handlerLifecycles c) → replay as c ≡ just c′ →
  Unique (handlerLifecycles c′)
replay-preserves as c unique eq = exec-preserves unique (replay-sound as c eq)

-- Tracking starts empty for every responder mode and supplied world state.
initial-unique : ∀ mode s → Unique (handlerLifecycles (initial mode s))
initial-unique mode s = refl
reachable-unique : ∀ mode s {as c′} → Executes (initial mode s) as c′ →
  Unique (handlerLifecycles c′)
reachable-unique mode s = exec-preserves (initial-unique mode s)
