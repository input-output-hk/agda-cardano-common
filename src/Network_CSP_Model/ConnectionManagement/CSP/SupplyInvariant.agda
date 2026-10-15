{-# OPTIONS --guardedness #-}

-- The full machine supply-bound invariant transferred to arbitrary finite raw CSP
-- executions/traces. Endpoint recovery avoids assuming renderer injectivity.
module ConnectionManagement.CSP.SupplyInvariant where

open import Data.List using (List; map)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Process_Trees using (ExtI)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.SupplyBounds
open import ConnectionManagement.Properties.SupplyInvariant
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (step-inv; all-exec-inv)
open import Semantics.LTS {E = Channel} {I = ExtI Channel}
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (_⟹⟨_⟩_; traces)

bounded-step : ∀ {c act P} → SupplyBounds (world c) → Process c ─[ ev (label act) ]─► P →
  Σ Configuration (λ c′ → P ≡ Process c′ × SupplyBounds (world c′))
bounded-step {c} {act} bounded step with step-inv {c = c} {a = act} step
... | c′ , enabled , endpoint = c′ , endpoint , advance-preserves act c enabled bounded

-- Every finite raw execution has a recovered, bounded endpoint and machine path.
bounded-execution : ∀ {c es P} → SupplyBounds (world c) → Process c ⟹⟨ es ⟩ P →
  Σ (List Action) (λ actions → Σ Configuration (λ c′ →
    es ≡ map label actions × P ≡ Process c′ × Executes c actions c′ × SupplyBounds (world c′)))
bounded-execution {c} bounded trace with all-exec-inv {c = c} trace
... | actions , c′ , labels , endpoint , path =
  actions , c′ , labels , endpoint , path , exec-preserves bounded path

bounded-trace : ∀ {c es} → SupplyBounds (world c) → traces (Process c) es →
  Σ (List Action) (λ actions → Σ Configuration (λ c′ →
    es ≡ map label actions × Executes c actions c′ × SupplyBounds (world c′)))
bounded-trace {c} bounded (_ , trace) with bounded-execution {c = c} bounded trace
... | actions , c′ , labels , endpoint , path , valid = actions , c′ , labels , path , valid
