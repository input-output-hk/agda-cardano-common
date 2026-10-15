{-# OPTIONS --guardedness #-}

-- Raw CSP reference guarantees across lifecycle, publication and exit actions.
module ConnectionManagement.CSP.HandlerBoundaries where

open import Data.List using (List; map; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerReferences using (TrackedChain)
open import ConnectionManagement.Properties.HandlerBoundaries
open import ConnectionManagement.Properties.HandlerAttachment using (CreationPremises; advance-creates)
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (exec-inv; exec-intro)
open import ConnectionManagement.CSP.HandlerReferences using (normal-chain)
open import ConnectionManagement.CSP.HandlerAttachment using (newlyAttached; created-chain)
open import ConnectionManagement.CSP.HandlerOutcomes using (n₅; n₆; n₇; n₈)
open import ConnectionManagement.Scenarios.Admission using (child₀)
import ConnectionManagement.Rules.HandlerLifecycle as L
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (_⟹⟨_⟩_)

raw-handler-preserves : ∀ {c as P} → HandlerActions as →
  Process c ⟹⟨ map label as ⟩ P → ∀ q → TrackedChain q c →
  Σ Configuration (λ c′ → P ≡ Process c′ × TrackedChain q c′)
raw-handler-preserves only reach q chain with exec-inv reach
... | c′ , same , path = c′ , same , handler-exec-preserves only path q chain

-- Creation composes with the broader suffix; allocation premises are unchanged.
raw-attachment-handler-creates : ∀ {w err c as P} →
  CreationPremises w (world c) (inboundGovernor c) → HandlerActions as →
  Process c ⟹⟨ map label (handlerStep w (L.attach err) ∷ as) ⟩ P →
  Σ Configuration (λ c′ → P ≡ Process c′ × TrackedChain w c′)
raw-attachment-handler-creates {w} {err} {c} premises only reach with exec-inv reach
... | c′ , same , next attached rest = c′ , same ,
  handler-exec-preserves only rest w (advance-creates w err c premises attached)

-- Body completion enters cleanup with the original resources still referenced.
exitActions : List Action
exitActions = handlerStep child₀ L.jobPoolClosed ∷ handlerStep child₀ L.finishBuffer ∷ handlerExit child₀ ∷ []
exit-path : Executes n₅ exitActions n₈
exit-path = next {c₁ = n₆} refl (next {c₁ = n₇} refl (next refl done))
exit-coverage : HandlerActions exitActions
exit-coverage = lifecycle (lifecycle (exit empty))
cleanup-entry-chain : TrackedChain child₀ n₈
cleanup-entry-chain = handler-exec-preserves exit-coverage exit-path child₀ normal-chain
exit-csp : Process n₅ ⟹⟨ map label exitActions ⟩ Process n₈
exit-csp = exec-intro exit-path

-- Duplicate publication reports its fault; it cannot overwrite the result.
duplicate : Configuration
duplicate = record newlyAttached { publicationFaults = child₀ ∷ [] }
duplicate-path : Executes newlyAttached (handlerPublication child₀ query duplicateWrite ∷ []) duplicate
duplicate-path = next refl done
duplicate-chain : TrackedChain child₀ duplicate
duplicate-chain = handler-exec-preserves (publication empty) duplicate-path child₀ created-chain
duplicate-csp : Process newlyAttached ⟹⟨ map label (handlerPublication child₀ query duplicateWrite ∷ []) ⟩ Process duplicate
duplicate-csp = exec-intro duplicate-path

overwrite-refused : advance (handlerPublication child₀ query resultWritten) newlyAttached ≡ nothing
overwrite-refused = refl
repeat-fault-refused : advance (handlerPublication child₀ query duplicateWrite) duplicate ≡ nothing
repeat-fault-refused = refl
publication-after-exit-refused : advance (handlerPublication child₀ query duplicateWrite) n₈ ≡ nothing
publication-after-exit-refused = refl
