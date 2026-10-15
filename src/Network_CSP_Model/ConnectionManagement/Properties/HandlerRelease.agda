{-# OPTIONS --guardedness #-}

-- Entry edits retain resource identities; release changes only IG control state.
module ConnectionManagement.Properties.HandlerRelease where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.Entries using (put-preserves-present)
open import ConnectionManagement.Properties.HandlerCleanup using (reframe)
open import ConnectionManagement.Properties.HandlerReferences
open import ConnectionManagement.Properties.HandlerAnchors using (Anchors)
open import ConnectionManagement.Properties.HandlerCapture using (release-retains)
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.InboundRelease as R
import ConnectionManagement.Rules.Pruning as P
import ConnectionManagement.Rules.IGRegistration as IG

open import ConnectionManagement.Properties.ReleaseRetention public using
  (engine-anchors; select-execution; worker-execution; release-execution)
import ConnectionManagement.Properties.ReleaseRetention as Retention
import ConnectionManagement.Properties.CleanupRetention as Cleanup

-- Preserve the existing chain API using handler-independent edit effects.
edit-chain : ∀ edit s {s′ q mid ig} → R.applyEdit edit s ≡ just s′ → Chain q mid s ig → Chain q mid s′ ig
edit-chain edit s eq = Cleanup.retains-chain (Retention.edit-retains edit s eq)
edits-chain : ∀ edits s {s′ q mid ig} → P.applyEdits edits s ≡ just s′ → Chain q mid s ig → Chain q mid s′ ig
edits-chain edits s eq = Cleanup.retains-chain (Retention.edits-retains edits s eq)

-- The real dispatcher applies the edit atomically and may note cancellation.
step-preserves : ∀ a c {c′} → advance (releaseStep a) c ≡ just c′ →
  ∀ q → TrackedChain q c → TrackedChain q c′
step-preserves a c eq q (f , found , chain) with L.allowRelease a (handlerLifecycles c) (world c)
... | false = case eq of λ ()
... | true with R.step a (inboundRelease c) (inboundGovernor c) (world c) in stepped
...   | nothing = case eq of λ ()
...   | just p with R.applyEdit (R.edit p) (world c) in applied
...     | nothing = case eq of λ ()
...     | just s with just-injective eq
...       | refl with release-retains a (handlerLifecycles c) q f found
...         | g , retained , same = g , retained , subst (λ mid → Chain q mid s (R.governor p)) (sym same)
  (anchors-preserve-chain (engine-anchors (release-execution a (inboundRelease c) (inboundGovernor c) (world c) stepped))
    (edit-chain (R.edit p) (world c) applied chain))
