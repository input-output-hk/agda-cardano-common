{-# OPTIONS --guardedness #-}

-- Concurrent WithoutQueue child events. Parent identities, masks and physical
-- peer-monitor binding belong to the integrating wrapper, not this primitive.
module ConnectionManagement.Negative.ConcurrentPool where

open import Data.Bool using (true; false)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (put)
import ConnectionManagement.Rules.JobPoolKernel as Kernel
module Pool = Kernel ℕ false
module Queued = Kernel ℕ true

j₀ j₁ : JobId
j₀ = ident 0
j₁ = ident 1
c1 c2 c3 c4 c5 c6 c7 : Pool.State
c1 = record Pool.initial { handles = (j₀ , Pool.bodyRunning) ∷ [] }
c2 = record c1 { handles = put j₁ Pool.bodyRunning (Pool.handles c1) }
c3 = record c2 { handles = put j₁ (Pool.deregisterPending Pool.normalExit) (Pool.handles c2) }
c4 = record c3 { registered = j₁ ∷ [] }
c5 = record c4 { handles = put j₁ (Pool.deregistered Pool.normalExit) (Pool.handles c4); registered = [] }
c6 = record c5 { registered = j₀ ∷ [] }
c7 = record c6 { phase = Pool.closing; snapshot = j₀ ∷ []; remaining = j₀ ∷ [] }
first-parent-forks : Pool.step (Pool.forkConcurrent j₀) Pool.initial ≡ just c1
first-parent-forks = refl
second-parent-forks-with-first-gap-open : Pool.step (Pool.forkConcurrent j₁) c1 ≡ just c2
second-parent-forks-with-first-gap-open = refl
fast-second-child-returns : Pool.step (Pool.bodyReturnedWith j₁ 42) c2 ≡ just c3
fast-second-child-returns = refl
fast-child-dereg-retries : Pool.step (Pool.deregister j₁) c3 ≡ nothing
fast-child-dereg-retries = refl
second-parent-registers-independently : Pool.step (Pool.registerConcurrent j₁) c3 ≡ just c4
second-parent-registers-independently = refl
registered-fast-child-deregisters : Pool.step (Pool.deregister j₁) c4 ≡ just c5
registered-fast-child-deregisters = refl
first-gap-still-blocks-close : Pool.step (Pool.beginClose []) c5 ≡ nothing
first-gap-still-blocks-close = refl
first-parent-registers-later : Pool.step (Pool.registerConcurrent j₀) c5 ≡ just c6
first-parent-registers-later = refl
settled-registry-closes : Pool.step (Pool.beginClose (j₀ ∷ [])) c6 ≡ just c7
settled-registry-closes = refl
removed-child-not-in-snapshot : Pool.snapshot c7 ≡ j₀ ∷ []
removed-child-not-in-snapshot = refl
no-duplicate-registration : Pool.step (Pool.registerConcurrent j₁) c4 ≡ nothing
no-duplicate-registration = refl
no-historic-reregistration : Pool.step (Pool.registerConcurrent j₁) c5 ≡ nothing
no-historic-reregistration = refl
no-unknown-registration : Pool.step (Pool.registerConcurrent j₁) Pool.initial ≡ nothing
no-unknown-registration = refl
no-reused-child-identity : Pool.step (Pool.forkConcurrent j₁) c5 ≡ nothing
no-reused-child-identity = refl
no-fork-after-close-start : Pool.step (Pool.forkConcurrent (ident 2)) c7 ≡ nothing
no-fork-after-close-start = refl
with-queue-rejects-concurrent-fork : Queued.step (Queued.forkConcurrent j₀) Queued.initial ≡ nothing
with-queue-rejects-concurrent-fork = refl
with-queue-rejects-concurrent-register : Queued.step (Queued.registerConcurrent j₀) Queued.initial ≡ nothing
with-queue-rejects-concurrent-register = refl

schedule : List Pool.Action
schedule = Pool.forkConcurrent j₀ ∷ Pool.forkConcurrent j₁ ∷
  Pool.bodyReturnedWith j₁ 42 ∷ Pool.registerConcurrent j₁ ∷
  Pool.deregister j₁ ∷ Pool.registerConcurrent j₀ ∷ Pool.beginClose (j₀ ∷ []) ∷ []
initialized-path : Pool.Executes Pool.initial schedule c7
initialized-path = Pool.next first-parent-forks
  (Pool.next second-parent-forks-with-first-gap-open
  (Pool.next fast-second-child-returns (Pool.next second-parent-registers-independently
  (Pool.next registered-fast-child-deregisters (Pool.next first-parent-registers-later
  (Pool.next settled-registry-closes Pool.done))))))
