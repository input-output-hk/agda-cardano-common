{-# OPTIONS --guardedness #-}

-- Remote promotion/demotion, including scored pruning, retain original chains.
module ConnectionManagement.Properties.HandlerRemote where

open import Data.Bool using (true; false)
open import Data.Nat using (suc; _≤?_)
import Data.Nat as Nat
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
open import ConnectionManagement.Properties.HandlerReferences
open import ConnectionManagement.Properties.HandlerRelease using (edits-chain; engine-anchors)
open import ConnectionManagement.Properties.HandlerCapture using (remote-retains)
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.RemoteState as R
import ConnectionManagement.Rules.Pruning as P
import ConnectionManagement.Rules.IGRegistration as IG

open import ConnectionManagement.Properties.RemoteRetention public using
  (commit-execution; plain-execution; prune-execution; capacity-execution; select-execution; worker-execution; remote-execution)

step-preserves : ∀ a c {c′} → advance (remoteStep a) c ≡ just c′ →
  ∀ q → TrackedChain q c → TrackedChain q c′
step-preserves a c eq q (f , found , chain) with L.allowRemote a (handlerLifecycles c) (world c)
... | false = case eq of λ ()
... | true with R.step (promotionHardLimit c) (pruningGeneration c) a (remoteCall c) (inboundGovernor c) (world c) in stepped
...   | nothing = case eq of λ ()
...   | just p with P.applyEdits (R.edits p) (world c) in applied
...     | nothing = case eq of λ ()
...     | just s with just-injective eq
...       | refl with remote-retains a (handlerLifecycles c) q f found
...         | g , retained , same = g , retained , subst (λ mid → Chain q mid s (R.governor p)) (sym same)
  (anchors-preserve-chain (engine-anchors (remote-execution (promotionHardLimit c) (pruningGeneration c) a (remoteCall c) (inboundGovernor c) (world c) stepped))
    (edits-chain (R.edits p) (world c) applied chain))
