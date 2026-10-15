{-# OPTIONS --guardedness #-}

-- Entry and promise supply bounds are preserved by EVERY action of the current partial
-- machine. This is not whole-state validity, source refinement, or liveness.
module ConnectionManagement.Properties.SupplyInvariant where

open import Data.Bool using (true; false)
open import Data.Bool.ListAction using (any)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.State
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.SupplyBounds
open import ConnectionManagement.Properties.SupplyAdmission
open import ConnectionManagement.Properties.SupplyCleanup
open import ConnectionManagement.Properties.SupplyHandshake
import ConnectionManagement.Rules.Handshake as H
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.Cleanup as Cleanup

-- The abstract publication boundary changes promise results only. Duplicate
-- publication is handled separately by the machine's publication-fault list.
publication-preserves : ∀ w result s {s′} → H.publishBoundary w result s ≡ just (H.published s′) →
  SupplyBounds s → SupplyBounds s′
publication-preserves w result s eq bounded with lookup w (handlers s) | lookup w (cleanups s)
... | nothing | _ = case eq of λ ()
... | just _ | just _ = case eq of λ ()
... | just h | nothing with any (λ p → does (p ≟ handlerPromise h)) (promises s)
...   | false = case eq of λ ()
...   | true with lookup (handlerPromise h) (handshakeResults s)
...     | just _ = case eq of λ ()
...     | nothing with just-injective eq
...       | refl = bounded

advance-preserves : ∀ action c {c′} → advance action c ≡ just c′ →
  SupplyBounds (world c) → SupplyBounds (world c′)
advance-preserves (admissionStep w action) c eq bounded with lookup w (admissions (world c))
... | nothing = case eq of λ ()
... | just a with Server.stepWorker w a action (world c) in stepped
...   | nothing = case eq of λ ()
...   | just s′ = subst (λ config → SupplyBounds (world config)) (just-injective eq)
  (admission-preserves action w a (world c) stepped bounded)
advance-preserves (cleanupStep w action) c eq bounded
  with lookup w (handlers (world c)) | lookup w (cleanups (world c))
... | nothing | _ = case eq of λ ()
... | just _ | nothing = case eq of λ ()
... | just h | just p with Cleanup.stepWorker w h p action (world c) in stepped
...   | nothing = case eq of λ ()
...   | just s′ = subst (λ config → SupplyBounds (world config)) (just-injective eq)
  (cleanup-preserves action w h p (world c) stepped bounded)
advance-preserves (handshakeStep w action) c eq bounded with lookup w (admissions (world c))
... | nothing = case eq of λ ()
... | just a with H.stepWorker (responder c) w a action (world c) in stepped
...   | nothing = case eq of λ ()
...   | just s′ = subst (λ config → SupplyBounds (world config)) (just-injective eq)
  (handshake-preserves action (responder c) w a (world c) stepped bounded)
advance-preserves (handlerExit w) c eq bounded
  with lookup w (handlers (world c)) | lookup w (cleanups (world c))
... | nothing | _ = case eq of λ ()
... | just _ | just _ = case eq of λ ()
... | just _ | nothing = subst (λ config → SupplyBounds (world config)) (just-injective eq) bounded
advance-preserves (handlerPublication w result outcome) c eq bounded
  with any (λ v → does (v ≟ w)) (publicationFaults c)
... | true = case eq of λ ()
... | false with H.publishBoundary w result (world c) in published | outcome
...   | nothing | _ = case eq of λ ()
...   | just (H.published s′) | resultWritten =
  subst (λ config → SupplyBounds (world config)) (just-injective eq)
    (publication-preserves w result (world c) published bounded)
...   | just H.writerBlocked | duplicateWrite =
  subst (λ config → SupplyBounds (world config)) (just-injective eq) bounded
...   | just (H.published _) | duplicateWrite = case eq of λ ()
...   | just H.writerBlocked | resultWritten = case eq of λ ()

-- Arbitrary finite execution, with no restriction on actions or scheduling.
exec-preserves : ∀ {c actions c′} → SupplyBounds (world c) → Executes c actions c′ → SupplyBounds (world c′)
exec-preserves bounded done = bounded
exec-preserves bounded (next {c = c} {a = action} eq rest) = exec-preserves (advance-preserves action c eq bounded) rest

-- Replay inherits the same invariant; a failed replay is not an execution.
replay-preserves : ∀ actions c {c′} → SupplyBounds (world c) → replay actions c ≡ just c′ → SupplyBounds (world c′)
replay-preserves actions c bounded eq = exec-preserves bounded (replay-sound actions c eq)
