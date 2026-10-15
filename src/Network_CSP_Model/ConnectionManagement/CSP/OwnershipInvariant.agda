{-# OPTIONS --guardedness #-}

-- The full machine ownership invariant transferred to arbitrary finite raw CSP
-- executions/traces. Endpoint recovery avoids assuming renderer injectivity.
module ConnectionManagement.CSP.OwnershipInvariant where

open import Data.List using (List; map)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Process_Trees using (ExtI)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.Ownership
open import ConnectionManagement.Properties.OwnershipInvariant
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (step-inv; all-exec-inv)
open import Semantics.LTS {E = Channel} {I = ExtI Channel}
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (_⟹⟨_⟩_; traces)

owned-step : ∀ {c act P} → Ownership (world c) → Process c ─[ ev (label act) ]─► P →
  Σ Configuration (λ c′ → P ≡ Process c′ × Ownership (world c′))
owned-step {c} {act} own step with step-inv {c = c} {a = act} step
... | c′ , enabled , endpoint = c′ , endpoint , advance-preserves act c enabled own

-- Every finite raw execution has a recovered, owned endpoint and machine path.
owned-execution : ∀ {c es P} → Ownership (world c) → Process c ⟹⟨ es ⟩ P →
  Σ (List Action) (λ actions → Σ Configuration (λ c′ →
    es ≡ map label actions × P ≡ Process c′ × Executes c actions c′ × Ownership (world c′)))
owned-execution {c} own trace with all-exec-inv {c = c} trace
... | actions , c′ , labels , endpoint , path =
  actions , c′ , labels , endpoint , path , exec-preserves own path

owned-trace : ∀ {c es} → Ownership (world c) → traces (Process c) es →
  Σ (List Action) (λ actions → Σ Configuration (λ c′ →
    es ≡ map label actions × Executes c actions c′ × Ownership (world c′)))
owned-trace {c} own (_ , trace) with owned-execution {c = c} own trace
... | actions , c′ , labels , endpoint , path , valid = actions , c′ , labels , path , valid
