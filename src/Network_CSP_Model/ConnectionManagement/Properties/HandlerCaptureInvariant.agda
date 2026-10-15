{-# OPTIONS --guardedness #-}

-- Every successful dispatcher step retains existing tracked mux captures.
-- No validity premise, scheduling restriction or action whitelist is imposed.
module ConnectionManagement.Properties.HandlerCaptureInvariant where

open import Data.Bool using (true; false)
open import Data.Bool.ListAction using (any)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (DecEq-Id)
open import ConnectionManagement.State using (inboundInfo)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerCapture
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.Handshake as H
import ConnectionManagement.Rules.Cleanup as C
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.InboundRelease as Release
import ConnectionManagement.Rules.RemoteState as Remote
import ConnectionManagement.Rules.Pruning as Prune

-- Equality transport only; the substantive lifecycle lemmas live one layer down.
advance-retains : ∀ a c {c′} → advance a c ≡ just c′ →
  Retains (handlerLifecycles c) (handlerLifecycles c′)
advance-retains (handlerStep w a) c eq
  with L.step w a (handlerLifecycles c) (inboundGovernor c) (world c) in stepped
... | nothing = case eq of λ ()
... | just (rt , ig) = subst (λ cfg → Retains (handlerLifecycles c) (handlerLifecycles cfg))
  (just-injective eq) (step-retains w a (handlerLifecycles c) (inboundGovernor c) (world c) stepped)
advance-retains (remoteStep a) c eq with L.allowRemote a (handlerLifecycles c) (world c)
... | false = case eq of λ ()
... | true with Remote.step (promotionHardLimit c) (pruningGeneration c) a (remoteCall c) (inboundGovernor c) (world c)
...   | nothing = case eq of λ ()
...   | just p with Prune.applyEdits (Remote.edits p) (world c)
...     | nothing = case eq of λ ()
...     | just s = subst (λ cfg → Retains (handlerLifecycles c) (handlerLifecycles cfg))
  (just-injective eq) (remote-retains a (handlerLifecycles c))
advance-retains (releaseStep a) c eq with L.allowRelease a (handlerLifecycles c) (world c)
... | false = case eq of λ ()
... | true with Release.step a (inboundRelease c) (inboundGovernor c) (world c)
...   | nothing = case eq of λ ()
...   | just p with Release.applyEdit (Release.edit p) (world c)
...     | nothing = case eq of λ ()
...     | just s = subst (λ cfg → Retains (handlerLifecycles c) (handlerLifecycles cfg))
  (just-injective eq) (release-retains a (handlerLifecycles c))
advance-retains (igStep a) c eq with L.allowIG a (handlerLifecycles c)
... | false = case eq of λ ()
... | true with IG.step (responder c) a (inboundGovernor c) (inboundInfo (world c))
...   | nothing = case eq of λ ()
...   | just (ig , queue) = subst (λ cfg → Retains (handlerLifecycles c) (handlerLifecycles cfg))
  (just-injective eq) (retains-refl (handlerLifecycles c))
advance-retains (admissionStep w a) c eq with Server.stepPrefix w a (world c)
... | nothing = case eq of λ ()
... | just s = subst (λ cfg → Retains (handlerLifecycles c) (handlerLifecycles cfg))
  (just-injective eq) (retains-refl (handlerLifecycles c))
advance-retains (handshakeStep w a) c eq with H.stepHandshake (responder c) w a (world c)
... | nothing = case eq of λ ()
... | just s = subst (λ cfg → Retains (handlerLifecycles c) (handlerLifecycles cfg))
  (just-injective eq) (retains-refl (handlerLifecycles c))
advance-retains (cleanupStep w a) c eq with C.stepCleanup w a (world c)
... | nothing = case eq of λ ()
... | just s = subst (λ cfg → Retains (handlerLifecycles c) (handlerLifecycles cfg))
  (just-injective eq) (retains-refl (handlerLifecycles c))
advance-retains (handlerExit w) c eq with L.mayExit w (handlerLifecycles c)
... | false = case eq of λ ()
... | true with C.beginCleanupBoundary w (world c)
...   | nothing = case eq of λ ()
...   | just s = subst (λ cfg → Retains (handlerLifecycles c) (handlerLifecycles cfg))
  (just-injective eq) (exit-retains w (handlerLifecycles c))
advance-retains (handlerPublication w result outcome) c eq
  with any (λ v → does (v ≟ w)) (publicationFaults c)
... | true = case eq of λ ()
... | false with H.publishBoundary w result (world c) | outcome
...   | nothing | _ = case eq of λ ()
...   | just (H.published s) | resultWritten = subst (λ cfg → Retains (handlerLifecycles c) (handlerLifecycles cfg))
  (just-injective eq) (retains-refl (handlerLifecycles c))
...   | just H.writerBlocked | duplicateWrite = subst (λ cfg → Retains (handlerLifecycles c) (handlerLifecycles cfg))
  (just-injective eq) (retains-refl (handlerLifecycles c))
...   | just (H.published _) | duplicateWrite = case eq of λ ()
...   | just H.writerBlocked | resultWritten = case eq of λ ()

-- Arbitrary finite action sequences, including other workers' actions.
exec-retains : ∀ {c as c′} → Executes c as c′ →
  Retains (handlerLifecycles c) (handlerLifecycles c′)
exec-retains {c} done = retains-refl (handlerLifecycles c)
exec-retains (next {c = c} {c₁ = c₁} {c₂ = c₂} {a = a} eq rest) =
  retains-trans {handlerLifecycles c} {handlerLifecycles c₁} {handlerLifecycles c₂}
    (advance-retains a c eq) (exec-retains rest)
replay-retains : ∀ as c {c′} → replay as c ≡ just c′ →
  Retains (handlerLifecycles c) (handlerLifecycles c′)
replay-retains as c eq = exec-retains (replay-sound as c eq)
