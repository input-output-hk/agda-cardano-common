{-# OPTIONS --guardedness #-}

-- Reference preservation for finite raw CSP traces of lifecycle actions only.
module ConnectionManagement.CSP.HandlerReferences where

open import Data.List using (map; []; _∷_)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Machine
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (exec-inv; exec-intro)
open import ConnectionManagement.Properties.HandlerReferences
open import ConnectionManagement.CSP.HandlerOutcomes using (n₅; n₆; n₇)
open import ConnectionManagement.Scenarios.Admission using (child₀)
import ConnectionManagement.Rules.HandlerLifecycle as L
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (_⟹⟨_⟩_)

raw-reachability-preserves : ∀ {c as P} → LifecycleOnly as →
  Process c ⟹⟨ map label as ⟩ P → ∀ q → TrackedChain q c →
  Σ Configuration (λ c′ → P ≡ Process c′ × TrackedChain q c′)
raw-reachability-preserves only reach q chain with exec-inv reach
... | c′ , same , path = c′ , same , exec-preserves only path q chain

-- A nonvacuous normal-exit suffix: closing the job pool updates the mux,
-- then buffer completion changes the frame while retaining all references.
normal-chain : TrackedChain child₀ n₅
normal-chain = _ , refl , record
  { originalHandler = _; publishedHandle = _; negotiatedFlow = _
  ; handleValue = _; muxValue = _; handlerFound = refl; promiseFound = refl
  ; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl
  ; entryPresent = _ , refl; socketPresent = _ , refl }

suffix = handlerStep child₀ L.jobPoolClosed ∷ handlerStep child₀ L.finishBuffer ∷ []
suffix-path : Executes n₅ suffix n₇
suffix-path = next {c₁ = n₆} refl (next refl done)
suffix-references : TrackedChain child₀ n₇
suffix-references = exec-preserves (more (more empty)) suffix-path child₀ normal-chain
suffix-csp : Process n₅ ⟹⟨ map label suffix ⟩ Process n₇
suffix-csp = exec-intro suffix-path
