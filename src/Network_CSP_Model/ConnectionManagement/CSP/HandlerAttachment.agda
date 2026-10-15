{-# OPTIONS --guardedness #-}

-- Creation at attachment followed by preservation along a lifecycle-only suffix.
module ConnectionManagement.CSP.HandlerAttachment where

open import Data.List using (map; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerAttachment
open import ConnectionManagement.Properties.HandlerReferences using (TrackedChain; LifecycleOnly; exec-preserves)
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (exec-inv; exec-intro)
open import ConnectionManagement.CSP.IGRegistration using (registered)
open import ConnectionManagement.CSP.HandlerLifecycle using (tracked; cancelError)
open import ConnectionManagement.Scenarios.Admission using (child₀)
import ConnectionManagement.Rules.HandlerLifecycle as L
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (_⟹⟨_⟩_)

-- The chain is a conclusion, not a premise. Existence of the raw trace supplies
-- successful attachment and successful subsequent lifecycle steps.
raw-attachment-creates : ∀ {w err c as P} →
  CreationPremises w (world c) (inboundGovernor c) → LifecycleOnly as →
  Process c ⟹⟨ map label (handlerStep w (L.attach err) ∷ as) ⟩ P →
  Σ Configuration (λ c′ → P ≡ Process c′ × TrackedChain w c′)
raw-attachment-creates {w} {err} {c} premises only reach with exec-inv reach
... | c′ , same , next attached rest = c′ , same ,
  exec-preserves only rest w (advance-creates w err c premises attached)

-- Registration fixture has no lifecycle frame before attachment.
registered-premises : CreationPremises child₀ (world registered) (inboundGovernor registered)
resources registered-premises h refl = (_ , refl) , (_ , refl)
coherent registered-premises h hid flow hd m refl refl refl refl = refl

before-untracked : lookup child₀ (handlerLifecycles registered) ≡ nothing
before-untracked = refl
newlyAttached : Configuration
newlyAttached = tracked L.monitoring registered
attachment-path : Executes registered (handlerStep child₀ (L.attach cancelError) ∷ []) newlyAttached
attachment-path = next refl done
created-chain : TrackedChain child₀ newlyAttached
created-chain = advance-creates child₀ cancelError registered registered-premises refl
attachment-csp : Process registered ⟹⟨ map label (handlerStep child₀ (L.attach cancelError) ∷ []) ⟩ Process newlyAttached
attachment-csp = exec-intro attachment-path
