# Four-node diamond — prioritised medium

`FourNodeDiamond` over the BlockFetch≻LeiosFetch-prioritised link-indexed
medium `NetworkLinkPriA` (Task 4), reusing the existing node bundles
`nodeA`/`nodeB`/`nodeC`/`nodeD` and `ioES` verbatim (no node-logic changes).
This is a construction-only deliverable — no property is proved here.

```agda
{-# OPTIONS --guardedness #-}
```

```agda
open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤)

open import Process_Trees using (PTree; ExtI)

module CSP.Examples.Cardano_network.Priority.FourNodeDiamondPri where
```

Reuse `FourNodeDiamond`'s concrete `Params` instance `p` and its node bundles
`nodeA`…`nodeD` verbatim, so `NetworkLinkPriA` is instantiated at the
same `Params` (hence the same `linkConfig`) the node bundles were built
against. `ioES` is not re-exported by `FourNodeDiamond` (it is pulled in there
via a non-`public open import`), so it is imported here directly from
`NetCommon p` — the very definition `FourNodeDiamond` itself uses:

```agda
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using (p; b1; nodeA; nodeB; nodeC; nodeD)
open import CSP.Examples.Cardano_network.Data p using (Payload)
open import CSP.Examples.Cardano_network.Net p using (Net_Api; Net_Api-≟)
open import CSP.Examples.Cardano_network.NetCommon p using (ioES)
open import CSP.Examples.Cardano_network.Priority.NetworkLinkPri p using (NetworkLinkPriA)

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (_∥⇘_⇙_; _⦀_; _∖_)
```

The whole network over the prioritised `NetworkLinkPriA` medium (in place of
`NetworkA`), io hidden — otherwise identical wiring to `FourNodeDiamond.system`:

```agda
-- FourNodeDiamond with the BlockFetch≻LeiosFetch-prioritised NetworkLink medium; A pinned to producing b1.
systemPri : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
systemPri = (NetworkLinkPriA ∥⇘ ioES ⇙ (nodeA b1 ⦀ (nodeB ⦀ (nodeC ⦀ nodeD)))) ∖ ioES
```
