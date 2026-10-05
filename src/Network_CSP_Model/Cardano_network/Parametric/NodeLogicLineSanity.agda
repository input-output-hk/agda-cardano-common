{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — `Parametric.NodeLogic`'s LINE SANITY
-- WITNESS, as its own import-by-nobody leaf.
--
-- SPLIT OUT OF `Parametric.NodeLogic` ON 2026-09-23.  The witness below
-- is the ONLY reason `NodeLogic` ever mentioned `Parametric.LineInstance`,
-- and `LineInstance → Assembly → DiamondInstance → FourNode.*` drags the
-- entire four-node estate (99 `FourNode.*` modules, including
-- `FourNode.Liveness.LTL.BlockLivenessProof` and the `R2_Bisim` chain)
-- into the closure of EVERY importer of `NodeLogic` — the whole Leios
-- layer included.  That made each Leios endpoint a ~20 GB cold rebuild
-- and OOM-killed several verification runs.  `NodeLogic` itself needs
-- nothing from the line; only this witness does, so the witness moved
-- here and nothing imports this file.
--
-- The term is UNCHANGED from `NodeLogic`'s original `lineRelaySystem`.
--
-- Sanity check: the relay logic at the three-node line
--
-- `Parametric.LineInstance` witnesses `systemOf (λ _ → Skip)` — the
-- scaffolding over a DERIVED `endpointsOf`.  This is the same witness
-- with the trivial logic replaced by the real relay logic, every node
-- starting from an empty store.  The line's degree-2 middle node
-- exercises the non-empty-tail path through `⦀⁺` and its two degree-1
-- ends exercise the `⦀⁺ P [] = P` path.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.NodeLogicLineSanity where

open import Data.List using ([])

open import CSP.Examples.Cardano_network.Parametric.NodeLogic
  using (module Generic)
open import CSP.Examples.Cardano_network.Parametric.LineInstance
  using (lineParams; line)
open import CSP.Examples.Cardano_network.ApiAlphabet lineParams using (apiES)
open import CSP.Examples.Cardano_network.Parametric.Node lineParams line apiES
  using (Proc; systemOf)

-- the three-node line running the relay logic at every node, each store initially
-- empty: a TYPECHECKING WITNESS that `nodeLogic` really is a `Parametric.Node` `lg`
lineRelaySystem : Proc
lineRelaySystem = systemOf (λ n → Generic.nodeLogic lineParams line apiES n [])
