{-# OPTIONS --guardedness #-}

-- Every successful dispatcher step has one of the allowed runtime edit forms.
-- No validity premise, scheduling restriction or action whitelist is imposed.
module ConnectionManagement.Properties.HandlerEvolutionInvariant where

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
open import ConnectionManagement.Properties.HandlerEvolution
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.Handshake as H
import ConnectionManagement.Rules.Cleanup as C
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.InboundRelease as Release
import ConnectionManagement.Rules.RemoteState as Remote
import ConnectionManagement.Rules.Pruning as Prune

-- Equality transport only; the substantive lifecycle lemmas live one layer down.
advance-evolves : ∀ a c {c′} → advance a c ≡ just c′ →
  Evolution (handlerLifecycles c) (handlerLifecycles c′)
advance-evolves (handlerStep w a) c eq
  with L.step w a (handlerLifecycles c) (inboundGovernor c) (world c) in stepped
... | nothing = case eq of λ ()
... | just (rt , ig) = subst (λ cfg → Evolution (handlerLifecycles c) (handlerLifecycles cfg))
  (just-injective eq) (step-evolves w a (handlerLifecycles c) (inboundGovernor c) (world c) stepped)
advance-evolves (remoteStep a) c eq with L.allowRemote a (handlerLifecycles c) (world c)
... | false = case eq of λ ()
... | true with Remote.step (promotionHardLimit c) (pruningGeneration c) a (remoteCall c) (inboundGovernor c) (world c)
...   | nothing = case eq of λ ()
...   | just p with Prune.applyEdits (Remote.edits p) (world c)
...     | nothing = case eq of λ ()
...     | just s = subst (λ cfg → Evolution (handlerLifecycles c) (handlerLifecycles cfg))
  (just-injective eq) (remote-evolves a (handlerLifecycles c))
advance-evolves (releaseStep a) c eq with L.allowRelease a (handlerLifecycles c) (world c)
... | false = case eq of λ ()
... | true with Release.step a (inboundRelease c) (inboundGovernor c) (world c)
...   | nothing = case eq of λ ()
...   | just p with Release.applyEdit (Release.edit p) (world c)
...     | nothing = case eq of λ ()
...     | just s = subst (λ cfg → Evolution (handlerLifecycles c) (handlerLifecycles cfg))
  (just-injective eq) (release-evolves a (handlerLifecycles c))
advance-evolves (igStep a) c eq with L.allowIG a (handlerLifecycles c)
... | false = case eq of λ ()
... | true with IG.step (responder c) a (inboundGovernor c) (inboundInfo (world c))
...   | nothing = case eq of λ ()
...   | just (ig , queue) = subst (λ cfg → Evolution (handlerLifecycles c) (handlerLifecycles cfg))
  (just-injective eq) unchanged
advance-evolves (admissionStep w a) c eq with Server.stepPrefix w a (world c)
... | nothing = case eq of λ ()
... | just s = subst (λ cfg → Evolution (handlerLifecycles c) (handlerLifecycles cfg))
  (just-injective eq) unchanged
advance-evolves (handshakeStep w a) c eq with H.stepHandshake (responder c) w a (world c)
... | nothing = case eq of λ ()
... | just s = subst (λ cfg → Evolution (handlerLifecycles c) (handlerLifecycles cfg))
  (just-injective eq) unchanged
advance-evolves (cleanupStep w a) c eq with C.stepCleanup w a (world c)
... | nothing = case eq of λ ()
... | just s = subst (λ cfg → Evolution (handlerLifecycles c) (handlerLifecycles cfg))
  (just-injective eq) unchanged
advance-evolves (handlerExit w) c eq with L.mayExit w (handlerLifecycles c)
... | false = case eq of λ ()
... | true with C.beginCleanupBoundary w (world c)
...   | nothing = case eq of λ ()
...   | just s = subst (λ cfg → Evolution (handlerLifecycles c) (handlerLifecycles cfg))
  (just-injective eq) (exit-evolves w (handlerLifecycles c))
advance-evolves (handlerPublication w result outcome) c eq
  with any (λ v → does (v ≟ w)) (publicationFaults c)
... | true = case eq of λ ()
... | false with H.publishBoundary w result (world c) | outcome
...   | nothing | _ = case eq of λ ()
...   | just (H.published s) | resultWritten = subst (λ cfg → Evolution (handlerLifecycles c) (handlerLifecycles cfg))
  (just-injective eq) unchanged
...   | just H.writerBlocked | duplicateWrite = subst (λ cfg → Evolution (handlerLifecycles c) (handlerLifecycles cfg))
  (just-injective eq) unchanged
...   | just (H.published _) | duplicateWrite = case eq of λ ()
...   | just H.writerBlocked | resultWritten = case eq of λ ()

