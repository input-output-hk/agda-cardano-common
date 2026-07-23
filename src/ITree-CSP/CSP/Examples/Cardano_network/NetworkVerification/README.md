# NetworkVerification — behavioural proofs about the medium

Failures-divergences correctness proofs for the Cardano network **multiplexer**
(`Network`) against its behavioural **copy specification** (`CopySpec`), plus the
deadlock-freedom and divergence-freedom that follow. Everything here is over the
current `Link × Dir` config-driven medium (see the parent `Network.agda`), at the
single-channel instance `p1` (`numLinks = 1`, `linkConfig _ = (lo , N2N_KeepAlive) ∷ []`).

All 10 modules below typecheck with **0 postulates** and no `NON_TERMINATING`.
The folder also carries the link-indexed `NetworkLink`/`CopySpec` equivalence
work, now COMPLETE: as of Milestone 2b the general per-link `perLink`
(`(l : Link) → linkConfig l ≢ [] → Unique (linkConfig l) → NetOneLink l ≈DR
linkCopy l`) is PROVED in the `PerLink/` subsystem (`Leaf` → `Fold` → `Exp`
`⦀⋆`-fold expansion) — the last axiom is GONE. `NetworkLinkEquiv.agda` declares
**0 postulates**; the four headline theorems (`netLink≈DR`/`≈FD`/`⊑FD`/
`spec⊑FD-Link`) hold for any per-link `≢ [] × Unique` config, and the
all-singleton results (`netLink≈DR-single` / `netLink≈FD-single`) are now
corollaries. The whole subsystem is axiom-free modulo only the FD layer's
certified König/classical inputs, as everywhere else.

## The master key

Everything rests on one theorem — a **divergence-respecting weak bisimulation**
between the multiplexer and the copy spec:

```agda
net≈DR : Network ≈DR CopySpec          -- (Data → …, generalised in the payload)
```

proved via the **expansion** technique (`Semantics.Expansion`: `Expand`/`_⪰_`/
`⪯→≈DR`), with the composite mux inverted **per side** (`TxSide` / `RxSide`
separately) so the whole 6-leaf term never has to be normalised at once. From
`net≈DR` the failures-divergences / trace refinements and the liveness properties
follow by generic transfer lemmas.

## Dependency structure

```
NetworkRefinement            (Data = ⊤ base: expansion proof, net≈DR/net≈FD)
      │
      ▼
NetworkRefinementGen         (generalise the base in the payload Data)
      │
      ▼
NetworkRefinementGenExp      (net≈DR : Data → Network ≈DR CopySpec, + net≈FD/⊑FD/⊑T)
      │
      ├────────────► NetworkRefinementGenSanity   (Data := ⊤ ⇒ original headline)
      │
      ├────────────► NetworkDeadlockFreeThm ◄──── NetworkDeadlockFree (liveness groundwork)
      │                     │
      │                     ▼
      │              NetworkADeadlockFreeThm       (lift to renamed NetworkA)
      │
      └────────────► NetworkDivergenceFreeThm
                            │
                            ▼
                     NetworkADivergenceFreeThm     (lift to renamed NetworkA)

NetworkSanity                (standalone: reduction / refl sanity of Network)
```

## Files

| File | Proves | Depends on (within this folder) |
|---|---|---|
| [`NetworkRefinement.agda`](NetworkRefinement.agda) | The base expansion proof at `Data = ⊤`: `net≈DR : Network ≈DR CopySpec`, and downstream `net≈FD`, `net⊑FD`/`spec⊑FD`, `net⊑T`/`spec⊑T`. Contains the per-side phase expansions (`expA`/`expB`/`expG`) and step inversions (`sim-Tx-*`/`sim-Rx-*`) that characterise every τ / visible step of each side. | — (the foundation) |
| [`NetworkRefinementGen.agda`](NetworkRefinementGen.agda) | Generalises the base proof in the forwarded payload `(Data : Set) ⦃ DecEq Data ⦄` (the explicit-decode discipline that keeps the writer offers reducing for abstract `Data`). | [`NetworkRefinement`](NetworkRefinement.agda) |
| [`NetworkRefinementGenExp.agda`](NetworkRefinementGenExp.agda) | The generic-`Data` headline results: `net≈DR : Data → Network ≈DR CopySpec`, `net≈FD`, `net⊑FD`/`spec⊑FD`, `net⊑T`/`spec⊑T`. | [`NetworkRefinementGen`](NetworkRefinementGen.agda) |
| [`NetworkRefinementGenSanity.agda`](NetworkRefinementGenSanity.agda) | Certifies the generalisation is conservative: instantiating at `Data := ⊤` recovers the original headline `Network ≈FD CopySpec` (`_ = net≈FD tt`). | [`NetworkRefinementGenExp`](NetworkRefinementGenExp.agda) |
| [`NetworkDeadlockFree.agda`](NetworkDeadlockFree.agda) | Deadlock-freedom groundwork: the per-`(l,d,id)` `Copy` buffer's progress/liveness invariants, and `network-deadlockFree-fromBisim : Network ≈DR CopySpec → DeadlockFree Network`. | — (uses the generic liveness layer) |
| [`NetworkDeadlockFreeThm.agda`](NetworkDeadlockFreeThm.agda) | `network-deadlockFree : DeadlockFree Network` — applies the groundwork to `net≈DR`. | [`NetworkDeadlockFree`](NetworkDeadlockFree.agda), [`NetworkRefinementGen`](NetworkRefinementGen.agda), [`NetworkRefinementGenExp`](NetworkRefinementGenExp.agda) |
| [`NetworkDivergenceFreeThm.agda`](NetworkDivergenceFreeThm.agda) | `DivergenceFree-CopySpec` (the copy spec cannot diverge) and `Network-divergenceFree : DivergenceFree Network` (transferred across `net≈DR` by `drbisim-divergenceFree`). | [`NetworkRefinementGen`](NetworkRefinementGen.agda), [`NetworkRefinementGenExp`](NetworkRefinementGenExp.agda) |
| [`NetworkADeadlockFreeThm.agda`](NetworkADeadlockFreeThm.agda) | `NetworkA-deadlockFree : DeadlockFree NetworkA` — deadlock-freedom lifted to the renamed (`Net ↪ Net_Api`) multiplexer via `rename-DeadlockFree`. | [`NetworkDeadlockFreeThm`](NetworkDeadlockFreeThm.agda), [`NetworkRefinementGen`](NetworkRefinementGen.agda) |
| [`NetworkADivergenceFreeThm.agda`](NetworkADivergenceFreeThm.agda) | `NetworkA-divergenceFree : DivergenceFree NetworkA` — divergence-freedom lifted to `NetworkA` via `rename-DivergenceFree`. | [`NetworkDivergenceFreeThm`](NetworkDivergenceFreeThm.agda), [`NetworkRefinementGen`](NetworkRefinementGen.agda) |
| [`NetworkSanity.agda`](NetworkSanity.agda) | Standalone reduction / `refl` sanity checks on `Network` at `p1`: e.g. `offers-input` (the medium offers `input l0 d0 N2N_KeepAlive`), `hidden-sndmsg`/`hidden-tx` (the internal wire channels are hidden). | — |

## Typechecking

From the repository `src/` directory (never the repo root):

```
cd <repo>/src
agda CSP/Examples/Cardano_network/NetworkVerification/NetworkADeadlockFreeThm.agda
agda CSP/Examples/Cardano_network/NetworkVerification/NetworkADivergenceFreeThm.agda
```

The two `NetworkA*Thm` modules sit at the top of the dependency DAG, so checking
them transitively checks the whole chain. Note `NetworkRefinement.agda` is large
(~4300 lines) and slow to typecheck (minutes).

## Notes

- The port from the earlier per-protocol `Conn` model preserved the expansion
  proof rather than rebuilding it. One genuine semantic change was needed: the
  config-driven drainers (`Transmitter`/`Receiver`/`SndAck`/`RcvAck`) accept their
  event at **any** `(l, d, id)` (the old model implicitly pinned non-configured
  instances via an empty `Conn = Fin 0`), so the `sim-Tx-ev` / `sim-Rx-ev` `ack` /
  `tx` disjuncts are stated in a **generalised** form (`ackLbl-at` / `txLbl-at` +
  the `*-class-gen` classifiers).
- `≈DR`/`≈FD`/`⊑FD`/`⊑T` and the transfer lemmas (`drbisim→≈FD`,
  `drbisim-divergenceFree`, `rename-DeadlockFree`, `rename-DivergenceFree`) live in
  the generic `Semantics.*` layer.
