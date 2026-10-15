{-# OPTIONS --guardedness #-}

-- Every finite raw CSP execution from a fresh observation has a certified state.
module ConnectionManagement.CSP.OriginMonitorInvariant where

open import Data.List using (List; map)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Process_Trees
import ConnectionManagement.Machine as Open
open import ConnectionManagement.Rules.OriginMonitor
open import ConnectionManagement.Properties.HandlerResources using (Resources)
open import ConnectionManagement.Properties.OriginMonitorInvariant
open import ConnectionManagement.CSP.OriginMonitor using (Process; all-exec-inv)
open import ConnectionManagement.CSP.Process using (Channel; label)
open import Semantics.Failures {E = Channel} {I = ExtI Channel}
  using (_⟹⟨_⟩_; traces)

-- The result includes the actual process endpoint, not just some valid state.
raw-invariant : ∀ {t c es P} → Resources (workerId t) (Open.world c) →
  Process t (start c) ⟹⟨ es ⟩ P →
  Σ (List Open.Action) (λ as → Σ State (λ s →
    es ≡ map label as × P ≡ Process t s × Executes t (start c) as s × Invariant t s))
raw-invariant resources execution with all-exec-inv execution
... | as , s , labels , endpoint , path =
  as , s , labels , endpoint , path , reachable-invariant path resources

trace-invariant : ∀ {t c es} → Resources (workerId t) (Open.world c) →
  traces (Process t (start c)) es →
  Σ (List Open.Action) (λ as → Σ State (λ s →
    es ≡ map label as × Executes t (start c) as s × Invariant t s))
trace-invariant resources (_ , execution) with raw-invariant resources execution
... | as , s , labels , endpoint , path , inv = as , s , labels , path , inv
