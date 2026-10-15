{-# OPTIONS --guardedness #-}

-- Actual dispatcher coverage for admission/cleanup take, publication and restore.
-- Unsupported phase/action pairs are inverted explicitly; no rule is changed.
module ConnectionManagement.Properties.OwnershipMapDispatcher where

open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Function using (case_of_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.State
open import ConnectionManagement.Properties.Ownership
open import ConnectionManagement.Properties.OwnershipMapSteps
open import ConnectionManagement.Machine using (world; advance; admissionStep; cleanupStep)
import ConnectionManagement.Rules.CM as CM
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.Cleanup as Cleanup

take-admission-worker : ∀ w a s {s′} → lookup w (admissions s) ≡ just a →
  Server.stepWorker w a Server.take s ≡ just s′ → Ownership s → Ownership s′
take-admission-worker w (admissionWorker r (count l)) s found () own
take-admission-worker w (admissionWorker r (prepare l)) s found () own
take-admission-worker w (admissionWorker r (selectEntry l p)) s found () own
take-admission-worker w (admissionWorker r (forkHandler l p e)) s found () own
take-admission-worker w (admissionWorker r (publish l p e)) s found () own
take-admission-worker w (admissionWorker r (reject l hardLimitReached)) s found () own
take-admission-worker w (admissionWorker r (reject l forbidden)) s found () own
take-admission-worker w (admissionWorker r (reject l forkFailed)) s found () own
take-admission-worker w (admissionWorker r (closeSocket reason)) s found () own
take-admission-worker w (admissionWorker r (finished reason)) s found () own
take-admission-worker w (admissionWorker r (countPublished p e)) s found () own
take-admission-worker w (admissionWorker r (awaitHandshake p e)) s found () own
take-admission-worker w (admissionWorker r (commitHandshake e result)) s found () own
take-admission-worker w (admissionWorker r (countHandshake result)) s found () own
take-admission-worker w (admissionWorker r (notifyInbound info)) s found () own
take-admission-worker w (admissionWorker r (returnHandshake result)) s found () own
take-admission-worker w (admissionWorker r (completedHandshake result)) s found () own
take-admission-worker w (admissionWorker r impossibleHandshake) s found () own
take-admission-worker w (admissionWorker r acquireMap) s found eq own with CM.takeMap w (cm s) in takenEq
... | nothing = case eq of λ ()
... | just (l , c′) = subst Ownership (just-injective eq) (admission-take w r s found takenEq own)

publish-admission-worker : ∀ w a s {s′} → lookup w (admissions s) ≡ just a →
  Server.stepWorker w a Server.putMapBack s ≡ just s′ → Ownership s → Ownership s′
publish-admission-worker w (admissionWorker r acquireMap) s found () own
publish-admission-worker w (admissionWorker r (count l)) s found () own
publish-admission-worker w (admissionWorker r (prepare l)) s found () own
publish-admission-worker w (admissionWorker r (selectEntry l p)) s found () own
publish-admission-worker w (admissionWorker r (forkHandler l p e)) s found () own
publish-admission-worker w (admissionWorker r (reject l forbidden)) s found () own
publish-admission-worker w (admissionWorker r (reject l forkFailed)) s found () own
publish-admission-worker w (admissionWorker r (closeSocket reason)) s found () own
publish-admission-worker w (admissionWorker r (finished reason)) s found () own
publish-admission-worker w (admissionWorker r (countPublished p e)) s found () own
publish-admission-worker w (admissionWorker r (awaitHandshake p e)) s found () own
publish-admission-worker w (admissionWorker r (commitHandshake e result)) s found () own
publish-admission-worker w (admissionWorker r (countHandshake result)) s found () own
publish-admission-worker w (admissionWorker r (notifyInbound info)) s found () own
publish-admission-worker w (admissionWorker r (returnHandshake result)) s found () own
publish-admission-worker w (admissionWorker r (completedHandshake result)) s found () own
publish-admission-worker w (admissionWorker r impossibleHandshake) s found () own
publish-admission-worker w (admissionWorker r (publish l p e)) s found eq own with CM.putMap l (insertConnection (key r) e (savedMap l)) (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst Ownership (just-injective eq)
  (admission-put w (admissionWorker r (publish l p e)) (countPublished p e) l (insertConnection (key r) e (savedMap l)) s found refl refl putEq own)
publish-admission-worker w (admissionWorker r (reject l hardLimitReached)) s found eq own with CM.putMap l (savedMap l) (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst Ownership (just-injective eq)
  (admission-put w (admissionWorker r (reject l hardLimitReached)) (closeSocket hardLimitReached) l (savedMap l) s found refl refl putEq own)

restore-admission-worker : ∀ w a s {s′} → lookup w (admissions s) ≡ just a →
  Server.stepWorker w a Server.restore s ≡ just s′ → Ownership s → Ownership s′
restore-admission-worker w (admissionWorker r acquireMap) s found () own
restore-admission-worker w (admissionWorker r (count l)) s found () own
restore-admission-worker w (admissionWorker r (prepare l)) s found () own
restore-admission-worker w (admissionWorker r (selectEntry l p)) s found () own
restore-admission-worker w (admissionWorker r (forkHandler l p e)) s found () own
restore-admission-worker w (admissionWorker r (publish l p e)) s found () own
restore-admission-worker w (admissionWorker r (reject l hardLimitReached)) s found () own
restore-admission-worker w (admissionWorker r (closeSocket reason)) s found () own
restore-admission-worker w (admissionWorker r (finished reason)) s found () own
restore-admission-worker w (admissionWorker r (countPublished p e)) s found () own
restore-admission-worker w (admissionWorker r (awaitHandshake p e)) s found () own
restore-admission-worker w (admissionWorker r (commitHandshake e result)) s found () own
restore-admission-worker w (admissionWorker r (countHandshake result)) s found () own
restore-admission-worker w (admissionWorker r (notifyInbound info)) s found () own
restore-admission-worker w (admissionWorker r (returnHandshake result)) s found () own
restore-admission-worker w (admissionWorker r (completedHandshake result)) s found () own
restore-admission-worker w (admissionWorker r impossibleHandshake) s found () own
restore-admission-worker w (admissionWorker r (reject l forbidden)) s found eq own with CM.putMap l (savedMap l) (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst Ownership (just-injective eq)
  (admission-put w (admissionWorker r (reject l forbidden)) (closeSocket forbidden) l (savedMap l) s found refl refl putEq own)
restore-admission-worker w (admissionWorker r (reject l forkFailed)) s found eq own with CM.putMap l (savedMap l) (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst Ownership (just-injective eq)
  (admission-put w (admissionWorker r (reject l forkFailed)) (closeSocket forkFailed) l (savedMap l) s found refl refl putEq own)

take-cleanup-worker : ∀ w h p s {s′} → lookup w (cleanups s) ≡ just p →
  Cleanup.stepWorker w h p Cleanup.takeCleanupMap s ≡ just s′ → Ownership s → Ownership s′
take-cleanup-worker w h (cleanupSelect l) s found () own
take-cleanup-worker w h (cleanupClose l m tail) s found () own
take-cleanup-worker w h (cleanupPublish l m tail) s found () own
take-cleanup-worker w h (cleanupRestore l err) s found () own
take-cleanup-worker w h (cleanupWaiting st) s found () own
take-cleanup-worker w h (cleanupFinalize st outcome) s found () own
take-cleanup-worker w h (cleanupCount outcome) s found () own
take-cleanup-worker w h (cleanupDone outcome) s found () own
take-cleanup-worker w h cleanupAcquire s found eq own with CM.takeMap w (cm s) in takenEq
... | nothing = case eq of λ ()
... | just (l , c′) = subst Ownership (just-injective eq) (cleanup-take w s found takenEq own)

publish-cleanup-worker : ∀ w h p s {s′} → lookup w (cleanups s) ≡ just p →
  Cleanup.stepWorker w h p Cleanup.publishCleanupMap s ≡ just s′ → Ownership s → Ownership s′
publish-cleanup-worker w h cleanupAcquire s found () own
publish-cleanup-worker w h (cleanupSelect l) s found () own
publish-cleanup-worker w h (cleanupClose l m tail) s found () own
publish-cleanup-worker w h (cleanupRestore l err) s found () own
publish-cleanup-worker w h (cleanupWaiting st) s found () own
publish-cleanup-worker w h (cleanupFinalize st outcome) s found () own
publish-cleanup-worker w h (cleanupCount outcome) s found () own
publish-cleanup-worker w h (cleanupDone outcome) s found () own
publish-cleanup-worker w h (cleanupPublish l m tail) s found eq own with CM.putMap l m (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst Ownership (just-injective eq)
  (cleanup-put w (cleanupPublish l m tail) (Cleanup.afterPublish tail) l m s found refl (after-publish-no-lease tail) putEq own)

restore-cleanup-worker : ∀ w h p s {s′} → lookup w (cleanups s) ≡ just p →
  Cleanup.stepWorker w h p Cleanup.restoreCleanupMap s ≡ just s′ → Ownership s → Ownership s′
restore-cleanup-worker w h cleanupAcquire s found () own
restore-cleanup-worker w h (cleanupSelect l) s found () own
restore-cleanup-worker w h (cleanupClose l m tail) s found () own
restore-cleanup-worker w h (cleanupPublish l m tail) s found () own
restore-cleanup-worker w h (cleanupWaiting st) s found () own
restore-cleanup-worker w h (cleanupFinalize st outcome) s found () own
restore-cleanup-worker w h (cleanupCount outcome) s found () own
restore-cleanup-worker w h (cleanupDone outcome) s found () own
restore-cleanup-worker w h (cleanupRestore l err) s found eq own with CM.putMap l (savedMap l) (cm s) in putEq
... | nothing = case eq of λ ()
... | just c′ = subst Ownership (just-injective eq)
  (cleanup-put w (cleanupRestore l err) (cleanupDone (cleanupError err)) l (savedMap l) s found refl refl putEq own)

-- Shared lifts retain all lookup and Maybe failure cases of Machine.advance.
admission-lift : ∀ action →
  (∀ w a s {s′} → lookup w (admissions s) ≡ just a →
    Server.stepWorker w a action s ≡ just s′ → Ownership s → Ownership s′) →
  ∀ w c {c′} → advance (admissionStep w action) c ≡ just c′ →
    Ownership (world c) → Ownership (world c′)
admission-lift action preserves w c eq own with lookup w (admissions (world c)) in found
... | nothing = case eq of λ ()
... | just a with Server.stepWorker w a action (world c) in stepped
...   | nothing = case eq of λ ()
...   | just s′ = subst (λ config → Ownership (world config)) (just-injective eq)
  (preserves w a (world c) found stepped own)

cleanup-lift : ∀ action →
  (∀ w h p s {s′} → lookup w (cleanups s) ≡ just p →
    Cleanup.stepWorker w h p action s ≡ just s′ → Ownership s → Ownership s′) →
  ∀ w c {c′} → advance (cleanupStep w action) c ≡ just c′ →
    Ownership (world c) → Ownership (world c′)
cleanup-lift action preserves w c eq own
  with lookup w (handlers (world c)) | lookup w (cleanups (world c)) in found
... | nothing | _ = case eq of λ ()
... | just h | nothing = case eq of λ ()
... | just h | just p with Cleanup.stepWorker w h p action (world c) in stepped
...   | nothing = case eq of λ ()
...   | just s′ = subst (λ config → Ownership (world config)) (just-injective eq)
  (preserves w h p (world c) found stepped own)
