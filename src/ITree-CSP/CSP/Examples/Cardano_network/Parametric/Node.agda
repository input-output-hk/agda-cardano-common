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
-- The bundle builder is a PARAMETER (`bundleAtWith`/`nodeWith`/
-- `systemOfWithNode`), with two instantiations, exactly as the medium is:
-- `node`/`systemOf` use the CONFIG-DRIVEN `nodeBundle`, so a node's peers
-- and the medium's cells are read off the same `Params.linkConfig`;
-- `nodeUniform`/`systemOfUniform`/`systemOfCopyUniform` use the uniform
-- `miniProtocols`, which is what `FourNode`'s hand-written nodes run and
-- hence the only instantiation keeping `diamond-faithful` definitional.
--
-- The role convention — the ONE thing that must be right — is
-- `mk l d (opposite d)`: the node sitting at direction `d`
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
open import CSP.Examples.Cardano_network.NetCommon p using (CopySpecBreakableA; NetworkLinkBreakableA; ioES)
open import CSP.Examples.Cardano_network.NetworkPar p using (miniProtocols; nodeBundle)
open O {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (_⦀_; _∥⇘_⇙_; _∖_; ⦀⁺; ⦀Fin⁺)
open Topology t using (Node; numNodes-1; endpointsOf)

-- the process type every node, logic and system in this module inhabits
Proc : Set₁
Proc = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})

-- the peer bundle of ONE incident endpoint `(l , d)` for an ARBITRARY bundle
-- builder `mk`: client peers on the node's own direction `d`, server peers on the
-- opposite direction
bundleAtWith : (Link → Dir → Dir → Proc) → Link × Dir → Proc
bundleAtWith mk ld = mk (proj₁ ld) (proj₂ ld) (opposite (proj₂ ld))

-- the bundles of every link incident to `n` under `mk`, interleaved in
-- `endpointsOf`'s order (`⦀` is not commutative up to `≡`, so that order is part
-- of the interface)
linkBundlesWith : (Link → Dir → Dir → Proc) → Node → Proc
linkBundlesWith mk n =
  ⦀⁺ (bundleAtWith mk (proj₁ (endpointsOf n))) (map (bundleAtWith mk) (proj₂ (endpointsOf n)))

-- a node over an arbitrary bundle builder: its link bundles synchronised with its
-- application logic on the api alphabet
nodeWith : (Link → Dir → Dir → Proc) → Node → Proc → Proc
nodeWith mk n lg = linkBundlesWith mk n ∥⇘ apiES ⇙ lg

-- THE DEFAULT endpoint bundle: the CONFIG-DRIVEN one, so a node's peers and the
-- medium's cells are read off the SAME `Params.linkConfig` and cannot disagree
bundleAt : Link × Dir → Proc
bundleAt = bundleAtWith nodeBundle

-- the default node's link bundles (config-driven)
linkBundles : Node → Proc
linkBundles = linkBundlesWith nodeBundle

-- THE DEFAULT NODE: config-driven peers.  A `linkConfig`/peer mismatch is what made
-- every Leios announcement unreachable before `5c16c3ff`; this instantiation makes
-- such a mismatch unstatable.  `CSP.Examples.Cardano_network.BundleBridge` relates
-- the two builders by a theorem — `nodeBundle∼miniProtocols-lo` at `∼` and
-- `nodeBundle≈FDminiProtocols` at `≈FD`, under a `FullConfig` hypothesis — so the
-- switch of default is not a change of semantics on a fully-configured link.
node : Node → Proc → Proc
node = nodeWith nodeBundle

-- the UNIFORM node: every mini-protocol regardless of `linkConfig`.  Retained
-- because `FourNode.FourNodeDiamond`'s hand-written nodes are built from
-- `miniProtocols`, so only this instantiation keeps `diamond-faithful`
-- definitional and hence `blockLiveness-generic` transportable by `subst`.
nodeUniform : Node → Proc → Proc
nodeUniform = nodeWith miniProtocols

-- the whole network over an ARBITRARY medium `med` and an ARBITRARY node builder
-- `mk`: all nodes interleaved, synchronised with `med` on `ioES`, io hidden;
-- `break` events stay observable (∉ ioES)
systemOfWithNode : (Node → Proc → Proc) → Proc → (Node → Proc) → Proc
systemOfWithNode mk med lg = (med ∥⇘ ioES ⇙ (⦀Fin⁺ numNodes-1 (λ n → mk n (lg n)))) ∖ ioES

-- the network over an arbitrary medium, with the DEFAULT (config-driven) nodes.
-- The medium is an explicit argument because the campaign needs the SAME
-- composition over two different ones — see the two instantiations below.
systemOfWith : Proc → (Node → Proc) → Proc
systemOfWith = systemOfWithNode node

-- THE DEFAULT NETWORK: over the CONCRETE per-link multiplexer, every link's
-- `NetworkLink` cell independently breakable.  This is the primary object of the
-- development — the abstract copy medium below is the specification side of it.
systemOf : (Node → Proc) → Proc
systemOf = systemOfWith NetworkLinkBreakableA

-- the same network over the ABSTRACT breakable copy medium.  It is what the
-- hand-written `FourNode` systems (and hence the banked liveness theorems) are
-- built over; `NetworkVerification.NetworkLinkEquiv.netLink≈FD` (`NetworkLink ≈FD
-- CopySpec`) is the equivalence relating the two media.
systemOfCopy : (Node → Proc) → Proc
systemOfCopy = systemOfWith CopySpecBreakableA

-- the concrete-medium network over UNIFORM nodes: the only instantiation that is
-- definitionally the hand-written `FourNode` system (`DiamondInstance.diamond-faithfulₗ`)
systemOfUniform : (Node → Proc) → Proc
systemOfUniform = systemOfWithNode nodeUniform NetworkLinkBreakableA

-- the copy-medium network over UNIFORM nodes: what `DiamondInstance.diamond-faithful`
-- and hence `blockLiveness-generic` are stated over
systemOfCopyUniform : (Node → Proc) → Proc
systemOfCopyUniform = systemOfWithNode nodeUniform CopySpecBreakableA
