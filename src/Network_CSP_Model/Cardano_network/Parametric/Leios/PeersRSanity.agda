{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — TYPECHECKING WITNESS that the reporting
-- bundle builder `Leios.PeersR.nodeBundleR` plugs into
-- `Parametric.Node`'s builder slot exactly where the stock
-- `NetworkPar.nodeBundle` does, at the three-node line instance.
--
-- This mirrors `Parametric.Node.bundleAt`/`systemOf` (which are
-- `bundleAtWith nodeBundle` / `systemOfWithNode node`) and
-- `Parametric.LineInstance.lineSystem`.  It proves no property; it
-- certifies that Tasks 2-4 can build the Linear-Leios system as
-- `systemOfWithNode (nodeWith nodeBundleR) med lg` with NO edit to
-- `Parametric/Node.agda`.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.Leios.PeersRSanity where

open import Data.Product using (_×_)

open import CSP.Examples.Cardano_network.Base using (Dir)
open import CSP.Examples.Cardano_network.Parametric.LineInstance using (lineParams; line)
open import CSP.Examples.Cardano_network.Net lineParams using (Link; Net_Api; Net_Api-≟)
open import CSP.Examples.Cardano_network.Data lineParams using (Payload)
open import CSP.Examples.Cardano_network.NetCommon lineParams using (NetworkLinkBreakableA)
open import CSP.Examples.Cardano_network.ApiAlphabet lineParams using (apiES)
open import CSP.Examples.Cardano_network.Parametric.Node lineParams line apiES
  using (Proc; bundleAtWith; nodeWith; systemOfWithNode)
open import CSP.Examples.Cardano_network.Parametric.Leios.PeersR lineParams
  using (nodeBundleR)

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (Skip)

-- the reporting bundle of one incident endpoint, the counterpart of `Node.bundleAt`
lineBundleAtR : Link × Dir → Proc
lineBundleAtR = bundleAtWith nodeBundleR

-- the whole line network built over the reporting bundles, the counterpart of
-- `LineInstance.lineSystem` — this is the shape Tasks 2-4 instantiate with
-- `nodeLogicL` in place of the trivial `Skip` logic
lineSystemR : Proc
lineSystemR = systemOfWithNode (nodeWith nodeBundleR) NetworkLinkBreakableA (λ _ → Skip)
