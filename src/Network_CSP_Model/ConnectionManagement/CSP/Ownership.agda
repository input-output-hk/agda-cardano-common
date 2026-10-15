{-# OPTIONS --guardedness #-}

-- Transfer the proved close and map-action cases to raw CSP steps. No invariant claim
-- about arbitrary actions, hidden steps, fairness, or eventual map release.
module ConnectionManagement.CSP.Ownership where

open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Process_Trees using (ExtI)
open import ConnectionManagement.Domain
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.Ownership
open import ConnectionManagement.Properties.OwnershipSteps
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (step-inv)
import ConnectionManagement.Rules.Cleanup as Cleanup
open import Semantics.LTS {E = Channel} {I = ExtI Channel}

-- Explicit coverage: these are precisely the two actions whose cases are proved.
data CloseAction : Action → Set where
  closed : ∀ w → CloseAction (cleanupStep w Cleanup.closeHandlerSocket)
  failed : ∀ w err → CloseAction (cleanupStep w (Cleanup.failSocketClose err))

open import Data.Maybe using (just)

close-action-preserves : ∀ {a c c′} → CloseAction a → advance a c ≡ just c′ →
  Ownership (world c) → Ownership (world c′)
close-action-preserves {c = c} (closed w) = close-advance w c
close-action-preserves {c = c} (failed w err) = fail-advance w err c

-- Recover an owned machine endpoint; process equality does not assume that the
-- renderer is injective on configurations.
close-step-preserves : ∀ {a c P} → CloseAction a → Ownership (world c) →
  Process c ─[ ev (label a) ]─► P →
  Σ Configuration (λ c′ → P ≡ Process c′ × Ownership (world c′))
close-step-preserves {a} {c} covered own step with step-inv {c = c} {a = a} step
... | c′ , enabled , endpoint = c′ , endpoint , close-action-preserves covered enabled own

-- Map-changing actions have their own coverage family; CloseAction remains
-- available to existing consumers with its original, narrower meaning.
import ConnectionManagement.Rules.Server as Server
open import ConnectionManagement.Properties.OwnershipMapDispatcher

data MapAction : Action → Set where
  admissionTake : ∀ w → MapAction (admissionStep w Server.take)
  admissionPublish : ∀ w → MapAction (admissionStep w Server.putMapBack)
  admissionRestore : ∀ w → MapAction (admissionStep w Server.restore)
  cleanupTake : ∀ w → MapAction (cleanupStep w Cleanup.takeCleanupMap)
  cleanupPublish : ∀ w → MapAction (cleanupStep w Cleanup.publishCleanupMap)
  cleanupRestore : ∀ w → MapAction (cleanupStep w Cleanup.restoreCleanupMap)

map-action-preserves : ∀ {a c c′} → MapAction a → advance a c ≡ just c′ →
  Ownership (world c) → Ownership (world c′)
map-action-preserves {c = c} (admissionTake w) = admission-lift Server.take take-admission-worker w c
map-action-preserves {c = c} (admissionPublish w) = admission-lift Server.putMapBack publish-admission-worker w c
map-action-preserves {c = c} (admissionRestore w) = admission-lift Server.restore restore-admission-worker w c
map-action-preserves {c = c} (cleanupTake w) = cleanup-lift Cleanup.takeCleanupMap take-cleanup-worker w c
map-action-preserves {c = c} (cleanupPublish w) = cleanup-lift Cleanup.publishCleanupMap publish-cleanup-worker w c
map-action-preserves {c = c} (cleanupRestore w) = cleanup-lift Cleanup.restoreCleanupMap restore-cleanup-worker w c

map-step-preserves : ∀ {a c P} → MapAction a → Ownership (world c) →
  Process c ─[ ev (label a) ]─► P →
  Σ Configuration (λ c′ → P ≡ Process c′ × Ownership (world c′))
map-step-preserves {a} {c} covered own step with step-inv {c = c} {a = a} step
... | c′ , enabled , endpoint = c′ , endpoint , map-action-preserves covered enabled own
