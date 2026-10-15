{-# OPTIONS --guardedness #-}

-- Exclusive lease ownership is preserved by EVERY action of the current partial
-- machine. This is not whole-state validity, source refinement, or liveness.
module ConnectionManagement.Properties.OwnershipInvariant where

open import Data.Product using (_,_)
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.InboundRelease as Release
import ConnectionManagement.Rules.RemoteState as Remote
import ConnectionManagement.Rules.Pruning as Prune
import ConnectionManagement.Rules.HandlerLifecycle as Life
open import Data.List using ([]; _∷_)
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
open import ConnectionManagement.Properties.Ownership
open import ConnectionManagement.Properties.OwnershipNeutral
open import ConnectionManagement.Properties.OwnershipAdmission
open import ConnectionManagement.Properties.OwnershipCleanup
open import ConnectionManagement.Properties.OwnershipHandshake
open import ConnectionManagement.Properties.OwnershipMapDispatcher using (admission-lift; cleanup-lift)
import ConnectionManagement.Rules.Handshake as H

-- The abstract publication boundary changes promise results only. Duplicate
-- publication is handled separately by the machine's publication-fault list.
publication-preserves : ∀ w result s {s′} → H.publishBoundary w result s ≡ just (H.published s′) →
  Ownership s → Ownership s′
publication-preserves w result s eq own with lookup w (handlers s) | lookup w (cleanups s)
... | nothing | _ = case eq of λ ()
... | just _ | just _ = case eq of λ ()
... | just h | nothing with any (λ p → does (p ≟ handlerPromise h)) (promises s)
...   | false = case eq of λ ()
...   | true with lookup (handlerPromise h) (handshakeResults s)
...     | just _ = case eq of λ ()
...     | nothing with just-injective eq
...       | refl = own

-- Entry-only edits preserve the map lease census and allocation supplies.
release-edit-preserves : ∀ edit s {s′} → Release.applyEdit edit s ≡ just s′ →
  Ownership s → Ownership s′
release-edit-preserves nothing s eq own = subst Ownership (just-injective eq) own
release-edit-preserves (just (e , st)) s eq own with lookup e (entries (cm s)) in found
... | nothing = case eq of λ ()
... | just old with just-injective eq
...   | refl = own

-- Sequential proof of the pure helper; Machine publishes only the final
-- state, so intermediate writes are not observable execution steps.
prune-edits-preserves : ∀ edits s {s′} → Prune.applyEdits edits s ≡ just s′ →
  Ownership s → Ownership s′
prune-edits-preserves [] s eq own = subst Ownership (just-injective eq) own
prune-edits-preserves (edit ∷ edits) s eq own
  with Release.applyEdit (just edit) s in changed
... | nothing = case eq of λ ()
... | just s₁ = prune-edits-preserves edits s₁ eq
  (release-edit-preserves (just edit) s changed own)

advance-preserves : ∀ action c {c′} → advance action c ≡ just c′ →
  Ownership (world c) → Ownership (world c′)
advance-preserves (handlerStep w action) c eq own
  with Life.step w action (handlerLifecycles c) (inboundGovernor c) (world c)
... | nothing = case eq of λ ()
... | just (rt , ig) = subst (λ config → Ownership (world config)) (just-injective eq) own
advance-preserves (remoteStep action) c eq own
  with Life.allowRemote action (handlerLifecycles c) (world c)
... | false = case eq of λ ()
... | true with Remote.step (promotionHardLimit c) (pruningGeneration c) action (remoteCall c) (inboundGovernor c) (world c)
... | nothing = case eq of λ ()
... | just p with Prune.applyEdits (Remote.edits p) (world c) in edited
...   | nothing = case eq of λ ()
...   | just s = subst (λ config → Ownership (world config)) (just-injective eq)
  (prune-edits-preserves (Remote.edits p) (world c) edited own)
advance-preserves (releaseStep action) c eq own
  with Life.allowRelease action (handlerLifecycles c) (world c)
... | false = case eq of λ ()
... | true with Release.step action (inboundRelease c) (inboundGovernor c) (world c)
... | nothing = case eq of λ ()
... | just p with Release.applyEdit (Release.edit p) (world c) in edited
...   | nothing = case eq of λ ()
...   | just s = subst (λ config → Ownership (world config)) (just-injective eq)
  (release-edit-preserves (Release.edit p) (world c) edited own)
advance-preserves (igStep action) c eq own
  with Life.allowIG action (handlerLifecycles c)
... | false = case eq of λ ()
... | true with IG.step (responder c) action (inboundGovernor c) (inboundInfo (world c))
... | nothing = case eq of λ ()
... | just (ig , queue) = subst (λ config → Ownership (world config)) (just-injective eq) own
advance-preserves (admissionStep w action) c = admission-lift action (admission-worker action) w c
advance-preserves (cleanupStep w action) c = cleanup-lift action (cleanup-worker action) w c
advance-preserves (handshakeStep w action) c eq own with lookup w (admissions (world c)) in found
... | nothing = case eq of λ ()
... | just a with H.stepWorker (responder c) w a action (world c) in stepped
...   | nothing = case eq of λ ()
...   | just s′ = subst (λ config → Ownership (world config)) (just-injective eq)
  (handshake-worker action (responder c) w a (world c) found stepped own)
advance-preserves (handlerExit w) c eq own
  with Life.mayExit w (handlerLifecycles c)
... | false = case eq of λ ()
... | true with lookup w (handlers (world c)) | lookup w (cleanups (world c)) in found
... | nothing | _ = case eq of λ ()
... | just _ | just _ = case eq of λ ()
... | just _ | nothing = subst (λ config → Ownership (world config)) (just-injective eq)
  (cleanup-new w (world c) found own)
advance-preserves (handlerPublication w result outcome) c eq own
  with any (λ v → does (v ≟ w)) (publicationFaults c)
... | true = case eq of λ ()
... | false with H.publishBoundary w result (world c) in published | outcome
...   | nothing | _ = case eq of λ ()
...   | just (H.published s′) | resultWritten =
  subst (λ config → Ownership (world config)) (just-injective eq)
    (publication-preserves w result (world c) published own)
...   | just H.writerBlocked | duplicateWrite =
  subst (λ config → Ownership (world config)) (just-injective eq) own
...   | just (H.published _) | duplicateWrite = case eq of λ ()
...   | just H.writerBlocked | resultWritten = case eq of λ ()

-- Arbitrary finite execution, with no restriction on actions or scheduling.
exec-preserves : ∀ {c actions c′} → Ownership (world c) → Executes c actions c′ → Ownership (world c′)
exec-preserves own done = own
exec-preserves own (next {c = c} {a = action} eq rest) = exec-preserves (advance-preserves action c eq own) rest

-- Replay inherits the same invariant; a failed replay is not an execution.
replay-preserves : ∀ actions c {c′} → Ownership (world c) → replay actions c ≡ just c′ → Ownership (world c′)
replay-preserves actions c own eq = exec-preserves own (replay-sound actions c eq)
