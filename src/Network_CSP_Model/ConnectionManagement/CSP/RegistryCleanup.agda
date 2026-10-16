{-# OPTIONS --guardedness #-}

-- Preserve a certified invocation across any finite raw registry CSP execution.
module ConnectionManagement.CSP.RegistryCleanup where

open import Data.List using (List; map)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Process_Trees
open import ConnectionManagement.Rules.OriginRegistry
open import ConnectionManagement.Rules.AttributedOrigin using (Action)
open import ConnectionManagement.Properties.RegistryAttachment using (Attached)
open import ConnectionManagement.Properties.RegistryCleanup using (registry-preserves)
open import ConnectionManagement.CSP.OriginRegistry using (Process; all-exec-inv)
open import ConnectionManagement.CSP.AttributedOrigin using (Channel; label)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (_⟹⟨_⟩_)

-- Initial certification is explicit; arbitrary pre-seeded phases prove nothing.
raw-preserves : ∀ {s es P w hid tk f} → Attached w hid tk f (machine s) →
  Process s ⟹⟨ es ⟩ P →
  Σ (List Action) (λ as → Σ State (λ s′ → es ≡ map label as × P ≡ Process s′ ×
    Executes s as s′ × Attached w hid tk f (machine s′)))
raw-preserves certificate execution with all-exec-inv execution
... | as , s′ , labels , endpoint , path =
  as , s′ , labels , endpoint , path , registry-preserves path certificate
