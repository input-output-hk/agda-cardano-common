{-# OPTIONS --guardedness #-}

-- Current/captured map references and admission publication captures survive
-- every action of the inbound dispatcher.
module ConnectionManagement.Properties.MapReferencesInvariant where

open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
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
open import ConnectionManagement.Properties.StateMapReferences
open import ConnectionManagement.Properties.MapReferencesAdmission
open import ConnectionManagement.Properties.MapReferencesCleanup
open import ConnectionManagement.Properties.MapReferencesHandshake
import ConnectionManagement.Rules.Handshake as H
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.Cleanup as Cleanup

-- The abstract publication boundary changes promise results only. Duplicate
-- publication is handled separately by the machine's publication-fault list.
publication-preserves : ∀ w result s {s′} → H.publishBoundary w result s ≡ just (H.published s′) →
  Valid s → Valid s′
publication-preserves w result s eq valid with lookup w (handlers s) | lookup w (cleanups s)
... | nothing | _ = case eq of λ ()
... | just _ | just _ = case eq of λ ()
... | just h | nothing with any (λ p → does (p ≟ handlerPromise h)) (promises s)
...   | false = case eq of λ ()
...   | true with lookup (handlerPromise h) (handshakeResults s)
...     | just _ = case eq of λ ()
...     | nothing with just-injective eq
...       | refl = valid

-- Entry-only edits retain references in every certificate component.
release-edit-preserves : ∀ edit s {s′} → Release.applyEdit edit s ≡ just s′ →
  Valid s → Valid s′
release-edit-preserves nothing s eq valid = subst Valid (just-injective eq) valid
release-edit-preserves (just (e , st)) s eq valid with lookup e (entries (cm s)) in found
... | nothing = case eq of λ ()
... | just old with just-injective eq
...   | refl = write-preserves e st s valid

-- Sequential proof of the pure helper; Machine publishes only the final
-- state, so intermediate writes are not observable execution steps.
prune-edits-preserves : ∀ edits s {s′} → Prune.applyEdits edits s ≡ just s′ →
  Valid s → Valid s′
prune-edits-preserves [] s eq valid = subst Valid (just-injective eq) valid
prune-edits-preserves (edit ∷ edits) s eq valid
  with Release.applyEdit (just edit) s in changed
... | nothing = case eq of λ ()
... | just s₁ = prune-edits-preserves edits s₁ eq
  (release-edit-preserves (just edit) s changed valid)

advance-preserves : ∀ action c {c′} → advance action c ≡ just c′ →
  Valid (world c) → Valid (world c′)
advance-preserves (handlerStep w action) c eq valid
  with Life.step w action (handlerLifecycles c) (inboundGovernor c) (world c)
... | nothing = case eq of λ ()
... | just (rt , ig) = subst (λ config → Valid (world config)) (just-injective eq) valid
advance-preserves (remoteStep action) c eq valid
  with Life.allowRemote action (handlerLifecycles c) (world c)
... | false = case eq of λ ()
... | true with Remote.step (promotionHardLimit c) (pruningGeneration c) action (remoteCall c) (inboundGovernor c) (world c)
... | nothing = case eq of λ ()
... | just p with Prune.applyEdits (Remote.edits p) (world c) in edited
...   | nothing = case eq of λ ()
...   | just s = subst (λ config → Valid (world config)) (just-injective eq)
  (prune-edits-preserves (Remote.edits p) (world c) edited valid)
advance-preserves (releaseStep action) c eq valid
  with Life.allowRelease action (handlerLifecycles c) (world c)
... | false = case eq of λ ()
... | true with Release.step action (inboundRelease c) (inboundGovernor c) (world c)
... | nothing = case eq of λ ()
... | just p with Release.applyEdit (Release.edit p) (world c) in edited
...   | nothing = case eq of λ ()
...   | just s = subst (λ config → Valid (world config)) (just-injective eq)
  (release-edit-preserves (Release.edit p) (world c) edited valid)
advance-preserves (igStep action) c eq valid
  with Life.allowIG action (handlerLifecycles c)
... | false = case eq of λ ()
... | true with IG.step (responder c) action (inboundGovernor c) (inboundInfo (world c))
... | nothing = case eq of λ ()
... | just (ig , queue) = subst (λ config → Valid (world config)) (just-injective eq) valid
advance-preserves (admissionStep w action) c eq valid with lookup w (admissions (world c)) in found
... | nothing = case eq of λ ()
... | just a with Server.stepWorker w a action (world c) in stepped
...   | nothing = case eq of λ ()
...   | just s′ = subst (λ config → Valid (world config)) (just-injective eq)
  (admission-preserves action w a (world c) stepped
    (admission-valid w a (world c) found valid) valid)
advance-preserves (cleanupStep w action) c eq valid
  with lookup w (handlers (world c)) | lookup w (cleanups (world c)) in found
... | nothing | _ = case eq of λ ()
... | just _ | nothing = case eq of λ ()
... | just h | just p with Cleanup.stepWorker w h p action (world c) in stepped
...   | nothing = case eq of λ ()
...   | just s′ = subst (λ config → Valid (world config)) (just-injective eq)
  (cleanup-preserves action w h p (world c) stepped
    (cleanup-valid w p (world c) found valid) valid)
advance-preserves (handshakeStep w action) c eq valid with lookup w (admissions (world c)) in found
... | nothing = case eq of λ ()
... | just a with H.stepWorker (responder c) w a action (world c) in stepped
...   | nothing = case eq of λ ()
...   | just s′ = subst (λ config → Valid (world config)) (just-injective eq)
  (handshake-preserves action (responder c) w a (world c) stepped valid)
advance-preserves (handlerExit w) c eq valid
  with Life.mayExit w (handlerLifecycles c)
... | false = case eq of λ ()
... | true with lookup w (handlers (world c)) | lookup w (cleanups (world c)) in found
... | nothing | _ = case eq of λ ()
... | just _ | just _ = case eq of λ ()
... | just _ | nothing = subst (λ config → Valid (world config)) (just-injective eq)
  (cleanup-update w cleanupAcquire (world c) tt valid)
advance-preserves (handlerPublication w result outcome) c eq valid
  with any (λ v → does (v ≟ w)) (publicationFaults c)
... | true = case eq of λ ()
... | false with H.publishBoundary w result (world c) in published | outcome
...   | nothing | _ = case eq of λ ()
...   | just (H.published s′) | resultWritten =
  subst (λ config → Valid (world config)) (just-injective eq)
    (publication-preserves w result (world c) published valid)
...   | just H.writerBlocked | duplicateWrite =
  subst (λ config → Valid (world config)) (just-injective eq) valid
...   | just (H.published _) | duplicateWrite = case eq of λ ()
...   | just H.writerBlocked | resultWritten = case eq of λ ()

-- Arbitrary finite execution, with no restriction on actions or scheduling.
exec-preserves : ∀ {c actions c′} → Valid (world c) → Executes c actions c′ → Valid (world c′)
exec-preserves valid done = valid
exec-preserves valid (next {c = c} {a = action} eq rest) = exec-preserves (advance-preserves action c eq valid) rest

-- Replay inherits the same invariant; a failed replay is not an execution.
replay-preserves : ∀ actions c {c′} → Valid (world c) → replay actions c ≡ just c′ → Valid (world c′)
replay-preserves actions c valid eq = exec-preserves valid (replay-sound actions c eq)
