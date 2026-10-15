{-# OPTIONS --guardedness #-}

-- Raw process reachability preserves unique tracked ownership.
module ConnectionManagement.CSP.HandlerUniqueOwnership where

open import Data.List using (map)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Process_Trees
open import ConnectionManagement.Machine
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (exec-inv)
open import ConnectionManagement.Properties.HandlerUniqueOwnership using (Unique)
open import ConnectionManagement.Properties.HandlerUniqueOwnershipInvariant using (exec-preserves; initial-unique)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (_⟹⟨_⟩_)

raw-reachability-unique : ∀ {c as P} → Unique (handlerLifecycles c) →
  Process c ⟹⟨ map label as ⟩ P →
  Σ Configuration (λ c′ → P ≡ Process c′ × Unique (handlerLifecycles c′))
raw-reachability-unique unique reach with exec-inv reach
... | c′ , same , path = c′ , same , exec-preserves unique path
initial-reachability-unique : ∀ mode s {as P} →
  Process (initial mode s) ⟹⟨ map label as ⟩ P →
  Σ Configuration (λ c′ → P ≡ Process c′ × Unique (handlerLifecycles c′))
initial-reachability-unique mode s = raw-reachability-unique (initial-unique mode s)
