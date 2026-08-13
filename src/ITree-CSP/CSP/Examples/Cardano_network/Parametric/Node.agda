{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — the generic node over a `Topology`.
--
-- The campaign's four nodes have so far been four hand-written
-- definitions.  This module replaces them by ONE definition, `node`,
-- driven by the graph layer of `Parametric.Topology`: a node runs the
-- mini-protocol bundle of every link incident to it (interleaved),
-- synchronised with its application logic on the api alphabet, and the
-- whole network interleaves all nodes against the medium on `ioES`
-- with the io events hidden.
--
-- The role convention — the ONE thing that must be right — is
-- `miniProtocols l d (opposite d)`: the node sitting at direction `d`
-- of link `l` runs the CLIENT peers on its own direction `d` and the
-- SERVER peers on the opposite one.  This is exactly the convention of
-- the existing `nodeA`…`nodeD` (e.g. A is the `lo` endpoint of both AB
-- and AC and runs `miniProtocols linkAB lo hi`).
--
-- `apiES` is a MODULE PARAMETER rather than a local definition on
-- purpose.  `apiSet`/`apiSet-dec`/`apiES` live inside
-- `FourNode.FourNodeDiamond`, not in a shared module; re-deriving them
-- here would build a *different* `EventSet` record from a different
-- (though pointwise-equal) decision function, and two such records are
-- not `refl`-equal.  Taking the diamond's own `apiES` keeps
-- `Parametric.DiamondInstance`'s faithfulness gate definitional.
------------------------------------------------------------------------

open import Data.List using (List; map)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic using (⊤)
open import Level using (0ℓ)

open import Process_Trees using (PTree; ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Parametric.Topology using (Topology; opposite)
import CSP.Examples.Cardano_network.Net as N
import CSP.Examples.Cardano_network.Data as D
import CSP.Operators as O

module CSP.Examples.Cardano_network.Parametric.Node
  (p : Params) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p})) where

open import CSP.Examples.Cardano_network.Base using (Dir)
open N p using (Link; Net_Api; Net_Api-≟)
open D p using (Payload)
open import CSP.Examples.Cardano_network.NetCommon p using (CopySpecBreakableA; ioES)
open import CSP.Examples.Cardano_network.NetworkPar p using (miniProtocols)
open O {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (_⦀_; _∥⇘_⇙_; _∖_; ⦀⁺; ⦀Fin⁺)
open Topology t using (Node; numNodes-1; endpointsOf)

-- the process type every node, logic and system in this module inhabits
Proc : Set₁
Proc = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})

-- the mini-protocol bundle of ONE incident endpoint `(l , d)`: client peers on the
-- node's own direction `d`, server peers on the opposite direction
bundleAt : Link × Dir → Proc
bundleAt ld = miniProtocols (proj₁ ld) (proj₂ ld) (opposite (proj₂ ld))

-- the bundles of every link incident to `n`, interleaved in `endpointsOf`'s order
-- (`⦀` is not commutative up to `≡`, so that order is part of the interface)
linkBundles : Node → Proc
linkBundles n = ⦀⁺ (bundleAt (proj₁ (endpointsOf n))) (map bundleAt (proj₂ (endpointsOf n)))

-- a node: its link bundles synchronised with its application logic on the api alphabet
node : Node → Proc → Proc
node n lg = linkBundles n ∥⇘ apiES ⇙ lg

-- the whole network: all nodes interleaved, synchronised with the (breakable copy)
-- medium on `ioES`, io hidden; `break` events stay observable (∉ ioES)
systemOf : (Node → Proc) → Proc
systemOf lg = (CopySpecBreakableA ∥⇘ ioES ⇙ (⦀Fin⁺ numNodes-1 (λ n → node n (lg n)))) ∖ ioES
