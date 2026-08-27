# Four-node diamond over a *breakable* medium — fault-injection demo

The healthy four-node diamond (`FourNodeDiamond.lagda.md`) runs its links over
the (FD-equivalent) `CopySpec` medium, which never fails. This module re-runs the
*same* four nodes over the **breakable** medium `CopySpecBreakableA`, where each
link `l` runs normally until its dedicated `break l` fault-injection event fires,
after which that link terminates (`Skip`, √) — the `break` event is the observable
marker that the link is broken. The `break` events are *not* in
the hidden io set `ioES`, so they stay observable at the top level.

```text
        A
       / \
      B   C
       \ /
        D
```

```agda
{-# OPTIONS --guardedness #-}
```

```agda
import Data.Unit as U
open import Data.Unit.Polymorphic using (⊤)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Level using (0ℓ)
open import Process_Trees using (PTree; ExtI)

module CSP.Examples.Cardano_network.FourNode.FourNodeDiamondBreakable where
```

The healthy diamond supplies the shared `Params` `p`, the four nodes, and the
four link identifiers — all top-level, so a plain `using (…)` import works:

```agda
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; Block₃; nodeA; nodeB; nodeC; nodeD
        ; linkAB; linkAC; linkBD; linkCD )
```

The breakable medium and the io sync set from `NetCommon p`; the `break` channel
and the alphabet from `Net p`; the `Payload` data domain from `Data p`:

```agda
open import CSP.Examples.Cardano_network.NetCommon p
  using ( CopySpecBreakableA; breakableLinkA; NetworkLinkBreakableA; ioES )
open import CSP.Examples.Cardano_network.Net p
  using ( break; Net_Api; Net_Api-≟; Link )
open import CSP.Examples.Cardano_network.Data p using (Payload)

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; _∖_; Skip )
```

The labelled-transition system over the `Net_Api Payload` alphabet (same
instantiation the other examples use):

```agda
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; sVis; ev; evl; evLabel )
```

## The broken system

The whole diamond, but over the breakable copy medium instead of `CopySpec`.
Exactly the `System_CopySpec` composition of `FourNodeDiamond`, with the medium
swapped for `CopySpecBreakableA`; the `break` events remain observable (`∉ ioES`),
while `input`/`output` are still hidden.

```agda
-- the four-node diamond over the breakable medium, A producing `blkA`; break events stay observable (∉ ioES)
breakableSystem : Block₃ → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
breakableSystem blkA = (CopySpecBreakableA ∥⇘ ioES ⇙ (nodeA blkA ⦀ (nodeB ⦀ (nodeC ⦀ nodeD)))) ∖ ioES
```

The same diamond over the **concrete** per-link multiplexer `NetworkLinkBreakableA`
instead of the abstract `CopySpecBreakableA`. This is sound because
`NetworkLink ≈FD CopySpec` lifts through `⦀Fin numLinks`; only the medium operand
changes, so the composition shape is identical to `breakableSystem`.

```agda
-- the same diamond (A producing `blkA`) over the concrete NetworkLink mux (breakable); only the medium operand differs from breakableSystem
breakableSystemₗ : Block₃ → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
breakableSystemₗ blkA = (NetworkLinkBreakableA ∥⇘ ioES ⇙ (nodeA blkA ⦀ (nodeB ⦀ (nodeC ⦀ nodeD)))) ∖ ioES
```

## Isolated-medium break witness

The key behavioural fact: fault injection actually works. On the *isolated*
breakable link `breakableLinkA linkBD` — `linkMediumA linkBD △ (break linkBD ⟶₀ Skip)`
— the `break linkBD` event fires as a visible LTS step, and the link terminates
(√, to `Skip`).

Concretely, `force (linkMediumA linkBD △ (break linkBD ⟶₀ Skip))` is definitionally
the interrupt's `react (△-merge nP nQ Q) (△-τ …)` node (both operands are `react`s).
Its visible offer at `break linkBD` reduces via `△-merge`: the copy-medium side `nP`
offers nothing on `break` (`renameMap`'s inverse maps `break ↦ nothing`), while the
`break linkBD ⟶₀ Skip` side `nQ` offers it, so the merged offer is `just Skip`.
Hence `sVis refl refl` (first `refl` = the `react` node; second `refl` = the offer
resolving to `just Skip`), with the resulting state `P′ = Skip`.

Form used: the preferred **visible LTS step** (`sVis refl refl`); no fallback needed.

```agda
-- break linkBD fires on the isolated link medium, terminating it (→ Skip, √)
break-fires : ∃[ P′ ] (breakableLinkA linkBD ─[ ev (evl (evLabel U.⊤ (break linkBD) U.tt)) ]─► P′)
break-fires = Skip , sVis {at = U.⊤ , break linkBD} {a = U.tt} refl refl
```

## Reading the witness — and a documented limitation

A full behavioural trace of `breakableSystem` — a healthy-vs-broken contrast over the
whole diamond — is **intractable** to normalise in Agda, for exactly the reason
`FourNodeDiamond.lagda.md` documents: taking even a single `─[ l ]─►` step of the
composed `∖ ioES` / `∥⇘` / `⦀` / breakable-medium term forces the entire
medium-plus-peers tree to weak-head normal form (≈2.5 min, ≈20 GB per step), and a
meaningful trace is 150+ such steps. So only the *isolated-link* witness is given
here; it runs on one link alone and is cheap.

The intended reading of the witness is: `breakableSystem blkA` can perform `break linkBD`
(for any choice of A's produced block `blkA`).
After it does, link BD's medium cell has terminated (`Skip`, √) — its mini-protocol
channels (`input`/`output` for link BD) are permanently refused (a terminated cell
offers nothing further), so link BD's `input.c ? d → output.c ! d` copy relay never
completes again. Consequently the **B → D relay dies**: `nodeB`'s
`produce linkBD` server and `nodeD`'s `consume linkBD` client block forever on the
severed link. The **A → C → D path is unaffected**, since links AC and CD remain
healthy — so a block produced by `A` can still reach `D` via `C`, just not via `B`.
This is precisely the resilience property a diamond topology is meant to provide:
a single-link fault degrades but does not disconnect the network.
```
