{-# OPTIONS --guardedness #-}

-- Every finite raw registry execution from start has unique endpoint identities.
module ConnectionManagement.CSP.RegistryUnique where

open import Data.List using (List; map)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Process_Trees
open import ConnectionManagement.Rules.OriginRegistry
open import ConnectionManagement.Rules.AttributedOrigin using (Action)
open import ConnectionManagement.Properties.RegistryUnique
open import ConnectionManagement.CSP.OriginRegistry using (Process; all-exec-inv)
open import ConnectionManagement.CSP.AttributedOrigin using (Channel; label)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (_⟹⟨_⟩_; traces)

-- Unlike descriptor origin, this claim requires no resource support evidence.
raw-unique : ∀ {c es P} → Process (start c) ⟹⟨ es ⟩ P →
  Σ (List Action) (λ as → Σ State (λ s →
    es ≡ map label as × P ≡ Process s × Executes (start c) as s × Unique (entries s)))
raw-unique execution with all-exec-inv execution
... | as , s , labels , endpoint , path =
  as , s , labels , endpoint , path , reachable-unique path

trace-unique : ∀ {c es} → traces (Process (start c)) es →
  Σ (List Action) (λ as → Σ State (λ s →
    es ≡ map label as × Executes (start c) as s × Unique (entries s)))
trace-unique (_ , execution) with raw-unique execution
... | as , s , labels , endpoint , path , unique = as , s , labels , path , unique
