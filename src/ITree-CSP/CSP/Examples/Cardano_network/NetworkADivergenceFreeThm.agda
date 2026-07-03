{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Divergence-freedom for the renamed Cardano Network multiplexer.
--
-- `NetworkA = RenNet.renameMap Network` (over `Net_Api Payload`) is
-- divergence-free: the generic `rename-DivergenceFree` theorem lifts the
-- proven `DivergenceFree Network` (over `Net Payload`) across the injective
-- alphabet embedding `ιNet`.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.NetworkADivergenceFreeThm where

open import Data.Unit using (⊤; tt)
open import Class.DecEq using (DecEq)
open import Relation.Nullary using (yes)
open import Relation.Binary.PropositionalEquality using (refl)
open import Process_Trees using (ExtI)
open import Level using (0ℓ)

-- Extract `p1` (data-independent) via the trivial ⊤ payload.
instance
  decEq⊤ : DecEq ⊤
  decEq⊤ = record { _≟_ = λ _ _ → yes refl }

open import CSP.Examples.Cardano_network.NetworkRefinementGen ⊤ using (p1)
open import CSP.Examples.Cardano_network.Net p1 using (Net; Net_Api)
open import CSP.Examples.Cardano_network.Data p1 using (Payload; DecEq-Payload)
open import CSP.Examples.Cardano_network.NetCommon p1
  using (NetworkA; ιNet; ιNet⁻¹; ιNet-linv)

-- Cross-alphabet rename-DivergenceFree at the SAME ι instance NetCommon uses.
open import CSP.Laws.Traces.RenameDivergence
    {ℓ = 0ℓ} {ℓe₁ = 0ℓ} {ℓe₂ = 0ℓ}
    {E₁ = Net Payload} {E₂ = Net_Api Payload}
    ιNet ιNet⁻¹ ιNet-linv
  using (rename-DivergenceFree)

-- Target DivergenceFree (over Net_Api Payload) — lives in DeadlockDR.
open import Semantics.DeadlockDR {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (DivergenceFree)

module _ (d₀ : Payload) where

  open import CSP.Examples.Cardano_network.NetworkDivergenceFreeThm
    Payload ⦃ DecEq-Payload ⦄ d₀
    using (Network-divergenceFree)

  -- The renamed Network multiplexer over Net_Api Payload is divergence-free:
  -- rename preserves divergence-freedom, applied to DivergenceFree Network.
  NetworkA-divergenceFree : DivergenceFree NetworkA
  NetworkA-divergenceFree = rename-DivergenceFree Network-divergenceFree
