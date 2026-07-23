{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Final deadlock-freedom theorem for the Cardano `Network` example.
--
-- Instantiates the generic liveness/progress results from
-- `NetworkDeadlockFree` at the fixed single-channel instance `p1`
-- (defined in `NetworkRefinementGen`) and combines them with the master
-- DR-bisimulation key `net≈DR` (from `NetworkRefinementGenExp`) to
-- deliver the concrete goal: `DeadlockFree Network`.
------------------------------------------------------------------------

open import Class.DecEq using (DecEq)
open import Process_Trees using (ExtI)

module CSP.Examples.Cardano_network.NetworkVerification.NetworkDeadlockFreeThm
  (Data : Set) ⦃ _ : DecEq Data ⦄ (d₀ : Data) where

-- Bring in `p1` from the Gen module (the fixed single-channel instance).
open import CSP.Examples.Cardano_network.NetworkVerification.NetworkRefinementGen Data using (p1)

-- Bring Net into scope (for the Semantics.Deadlock instantiation).
open import CSP.Examples.Cardano_network.Net p1 using (Net)

-- Bring in `net≈DR` from GenExp (master key: Network ≈DR CopySpec over p1).
open import CSP.Examples.Cardano_network.NetworkVerification.NetworkRefinementGenExp Data using (net≈DR)

-- Bring `Network` into scope (from the Network module at p1).
open import CSP.Examples.Cardano_network.Network p1 Data using (Network)

-- `DeadlockFree` from Semantics.Deadlock, instantiated at the shared alphabet.
open import Semantics.Deadlock {E = Net Data} {I = ExtI (Net Data)} using (DeadlockFree)

-- Bring in the generic results instantiated at p1: Progress CopySpec and the transfer.
open import CSP.Examples.Cardano_network.NetworkVerification.NetworkDeadlockFree p1 Data d₀
  using (network-progress; network-deadlockFree-fromBisim)

-- The Cardano Network multiplexer (single-channel instance p1) is deadlock-free:
-- transfer deadlock-freedom from CopySpec across the master key net≈DR.
network-deadlockFree : DeadlockFree Network
network-deadlockFree = network-deadlockFree-fromBisim (net≈DR d₀)
