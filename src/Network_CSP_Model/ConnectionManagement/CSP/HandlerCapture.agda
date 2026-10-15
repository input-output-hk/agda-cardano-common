{-# OPTIONS --guardedness #-}

-- Raw process reachability inherits capture retention. Do not assume the
-- renderer is injective or recover a configuration from process equality.
module ConnectionManagement.CSP.HandlerCapture where

open import Data.List using (map)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Process_Trees
open import ConnectionManagement.Machine
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (exec-inv)
open import ConnectionManagement.Properties.HandlerCapture using (Retains)
open import ConnectionManagement.Properties.HandlerCaptureInvariant using (exec-retains)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (_⟹⟨_⟩_)

-- Every process reached by a finite raw action trace has a representing
-- configuration which retains every mux capture from the starting state.
raw-reachability-retains : ∀ {c as P} → Process c ⟹⟨ map label as ⟩ P →
  Σ Configuration (λ c′ → P ≡ Process c′ ×
    Retains (handlerLifecycles c) (handlerLifecycles c′))
raw-reachability-retains reach with exec-inv reach
... | c′ , same , run = c′ , same , exec-retains run
