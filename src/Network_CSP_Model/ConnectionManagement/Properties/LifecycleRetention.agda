{-# OPTIONS --guardedness #-}

-- Lifecycle actions preserve the world and retain installed references.
-- No frame or chain for the observed handler is needed by this effect theorem.
module ConnectionManagement.Properties.LifecycleRetention where

open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerAnchors using (Anchors)
open import ConnectionManagement.Properties.HandlerEvolution using (step-anchors)
import ConnectionManagement.Rules.HandlerLifecycle as L

step-effects : ∀ w a c {c′} → advance (handlerStep w a) c ≡ just c′ →
  world c′ ≡ world c × Anchors (inboundGovernor c) (inboundGovernor c′)
step-effects w a c eq with L.step w a (handlerLifecycles c) (inboundGovernor c) (world c) in stepped
... | nothing = case eq of λ ()
... | just (rt′ , ig′) with just-injective eq
...   | refl = refl , step-anchors w a (handlerLifecycles c) (inboundGovernor c) (world c) stepped
