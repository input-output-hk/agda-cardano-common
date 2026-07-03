{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Deadlock-freedom for the renamed Cardano Network multiplexer.
--
-- `NetworkA = RenNet.renameMap Network` (over the `Net_Api Payload`
-- alphabet) is deadlock-free: the generic `rename-DeadlockFree` theorem
-- (Task A) lifts the proven `DeadlockFree Network` (over `Net Payload`)
-- across the injective alphabet embedding `ιNet`.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.NetworkADeadlockFreeThm where

open import Data.Unit using (⊤; tt)
open import Class.DecEq using (DecEq)
open import Relation.Nullary using (yes)
open import Relation.Binary.PropositionalEquality using (refl)
open import Process_Trees using (ExtI)
open import Level using (0ℓ)

-- Extract `p1` by instantiating NetworkRefinementGen at the trivial ⊤ payload.
-- `p1` is data-independent so the choice of Data does not matter.
instance
  decEq⊤ : DecEq ⊤
  decEq⊤ = record { _≟_ = λ _ _ → yes refl }

open import CSP.Examples.Cardano_network.NetworkRefinementGen ⊤ using (p1)

-- Bring Net, Net_Api, and their equality into scope.
open import CSP.Examples.Cardano_network.Net p1 using (Net; Net_Api)

-- Bring Payload and its DecEq instance into scope from Data p1.
open import CSP.Examples.Cardano_network.Data p1 using (Payload; DecEq-Payload)

-- Bring NetworkA, ιNet, ιNet⁻¹, ιNet-linv into scope.
open import CSP.Examples.Cardano_network.NetCommon p1
  using (NetworkA; ιNet; ιNet⁻¹; ιNet-linv)

-- Import the cross-alphabet rename-DeadlockFree at the SAME ι instance
-- that NetCommon uses, supplying the alphabet types explicitly so that Agda
-- can resolve the level parameters without ambiguity.
open import CSP.Laws.Traces.RenameDeadlock
    {ℓ = 0ℓ} {ℓe₁ = 0ℓ} {ℓe₂ = 0ℓ}
    {E₁ = Net Payload} {E₂ = Net_Api Payload}
    ιNet ιNet⁻¹ ιNet-linv
  using (rename-DeadlockFree)

-- Import the target DeadlockFree (over Net_Api Payload).
open import Semantics.Deadlock {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (DeadlockFree)

-- `d₀ : Payload` is needed as a parameter because NetworkDeadlockFreeThm
-- requires an inhabitant of the payload type to construct the bisimulation key.
module _ (d₀ : Payload) where

  open import CSP.Examples.Cardano_network.NetworkDeadlockFreeThm
    Payload ⦃ DecEq-Payload ⦄ d₀
    using (network-deadlockFree)

  -- The renamed Network multiplexer over Net_Api Payload is deadlock-free:
  -- rename preserves deadlock-freedom, applied to the proven DeadlockFree Network.
  NetworkA-deadlockFree : DeadlockFree NetworkA
  NetworkA-deadlockFree = rename-DeadlockFree network-deadlockFree
