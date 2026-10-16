{-# OPTIONS --guardedness #-}

-- Attachment certificates describe retained identity, not live resources.
module ConnectionManagement.Properties.RegistryCleanup where

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (sym; subst)
import ConnectionManagement.Machine as Open
open import ConnectionManagement.Rules.OriginRegistry
open import ConnectionManagement.Rules.OriginMonitor using (muxId)
open import ConnectionManagement.Properties.RegistryAttachment using (Attached; identify)
open import ConnectionManagement.Properties.HandlerReferences using (Chain; TrackedChain)
open import ConnectionManagement.Properties.HandlerOrigin using (origin-exec)
import ConnectionManagement.Properties.HandlerDispatcherInterference as Dispatcher
import ConnectionManagement.Properties.HandlerManagement as Management
import ConnectionManagement.Properties.OriginRegistry as Registry

-- Convert the exact captured-mux equality back to the existing tracked predicate.
tracked : ∀ {w hid tk f c} → Attached w hid tk f c → TrackedChain w c
tracked {w} {c = c} certificate = Attached.frame certificate , Attached.frameFound certificate ,
  subst (λ mid → Chain w mid (Open.world c) (Open.inboundGovernor c))
    (sym (Attached.captured certificate)) (Attached.chain certificate)

-- All successful dispatcher actions, including exit and finalization, retain
-- the certificate. No readiness, socket-open or map-membership field is added.
open-preserves : ∀ {c as c′ w hid tk f} → Open.Executes c as c′ →
  Attached w hid tk f c → Attached w hid tk f c′
open-preserves {w = w} path certificate = identify
  (Management.all-exec-preserves path w (tracked certificate))
  (Dispatcher.all-chain path (Attached.chain certificate))
  (origin-exec path (Attached.origin certificate))

registry-preserves : ∀ {s as s′ w hid tk f} → Executes s as s′ →
  Attached w hid tk f (machine s) → Attached w hid tk f (machine s′)
registry-preserves path = open-preserves (Registry.exec-projects path)
