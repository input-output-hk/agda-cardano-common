# Cardano network example

A formalisation of the Cardano/Ouroboros **node-to-node (N2N) mini-protocols**
and their composition over a shared network medium, built on the repository's
generic CSP-over-process-trees layer (`Process_Trees`, `Semantics/*`, `CSP/*`).

Each mini-protocol (KeepAlive, ChainSync, BlockFetch, TxSubmission2, and the
Leios protocols in the data layer) is written as a pair of **API-driven peer
processes** (`PTree`) over a small per-protocol event type, then *renamed* into
one shared alphabet `Net_Api Payload`. Peers talk to each other only through a
**network medium** — either the faithful multiplexer `Network` or its behavioural
specification `CopySpec` (a per-connection `input.c → output.c` copy), which are
`≈FD`-equivalent. On top of this, whole-node and whole-network **systems** are
assembled by parallel-composing peers with the medium and hiding the wire
traffic, and several **behavioural properties** (deadlock-freedom,
divergence-freedom, trace/failures-divergences refinement against specs) are
proved.

## Reading order (newcomer path)

`Params` → `Base` → `Data` → `Net` → `Network` → a peer module (e.g. `ChainSync`)
→ `NetCommon` → `NetworkPar` → `FourNodeDiamond`. The large `*Refinement*` files
are self-contained proof developments and can be read last.

## Layering

```
Params ─▶ Base ─▶ Data ─▶ Net ─▶ Network ─▶ NetCommon ─▶ NetworkPar ─▶ FourNodeDiamond
                                    │            │             │
                          (peers) KeepAlive/ChainSync/BlockFetch/TxSubmission
                                    │
                          (proofs) Network*{DeadlockFree,DivergenceFree}Thm,
                                   Network*Refinement*, BlockFetch*Refinement*
```

## Foundations — parameters & data

| Module | Lines | Purpose |
|---|--:|---|
| `Params.agda` | 41 | The abstract data-domain bundle: opaque types (`Cookie`, `Block`, `Txid`, `LSlot`, …) that CSPm had to enumerate for FDR, each with a `DecEq` field, plus `numConns : IDs → ℕ` (connections per protocol). Every scenario supplies a concrete `Params`. |
| `Base.agda` | 96 | Parameter-free finite control enums: the protocol ids `IDs` (`N2N_ChainSync`/`N2N_BlockFetch`/`N2N_TxSubmission`/`N2N_KeepAlive`/`N2N_LeiosNotify`/`N2N_LeiosFetch`), `BlockingStyle`, etc., with `DecEq`. |
| `Data.agda` | 637 | Derived structured types over the abstract domains (`Point`, `ChainRange`, `Header`, `Tip`, `Tx`, `Vote`), the per-protocol **message** datatypes, and the shared `Payload`. |
| `Net.agda` | 1327 | The shared network event type `Net` (8 wire channels `input`/`output`/`sndmsg`/`rcvmsg`/`tx`/`sndack`/`rcvack`/`ack`) and `Net_Api` (adds the peer-local `apiXX`/`done` channels and the `ApiXXTag`/`ApiXXCar` API surfaces), with decidable equality `Net-≟`/`Net_Api-≟`. |

## The network medium

| Module | Lines | Purpose |
|---|--:|---|
| `Network.agda` | 268 | The multiplexer `Network` (a faithful PTree rendering of the CSPm `Network`: `Inputs`/`Outputs` leaves synchronised with `Transmitter`/`Receiver`/`SndAck`/`RcvAck` over `tx`/`ack`), **and** its behavioural spec `CopySpec` = per-connection `input.id.c ? d → output.id.c ! d` copy. Generic in the forwarded `Data`. |
| `NetCommon.agda` | 128 | Renames `Net ↪ Net_Api`; defines the renamed medium `NetworkA`, the renamed spec `CopySpecA`, the `{\| input, output \|}` sync set `ioES`, and the `withNet`/`clientServerNet` composition helpers. |
| `NetworkPar.agda` | 312 | Renames each protocol's peers into `Net_Api` (`KAclientA`/`KAserverA`, `CSclientA`/`CSserverA`, `BFclientA`/`BFserverA`, `TSclientA`/`TSserverA`), and bundles them: `miniProtocols` (all four protocols' client+server for one link) and `nodeNetwork`. |
| `NetModel.agda` | 204 | Standalone state-position abstraction of the `Network` leaves (per-leaf position enums `IP`/`TP`/`RP`/… for Inputs/Transmitter/RcvAck/Outputs/Receiver/SndAck); a reasoning aid for the medium's reachable configurations. Not imported by the others. |

## Mini-protocol peers

Each module defines a small per-protocol event type, its `DecEq`, and the
**client** and **server** peer FSMs as productive `iter` loops driven by `apiXX`
API events. (The renaming into `Net_Api` happens in `NetworkPar`.)

| Module | Lines | Protocol |
|---|--:|---|
| `KeepAlive.agda` | 266 | KeepAlive (cookie ping/response). |
| `ChainSync.agda` | 349 | ChainSync (consumer tracks producer's chain: RequestNext / AwaitReply / RollForward / RollBackward / FindIntersect). |
| `BlockFetch.lagda.md` | 1221 | BlockFetch (RequestRange → StartBatch → Block* → BatchDone / NoBlocks; ClientDone). Literate. |
| `TxSubmission.agda` | 342 | TxSubmission2 (tx-id / tx request-reply, blocking & pipelined). |

## Scenario / system

| Module | Lines | Purpose |
|---|--:|---|
| `FourNodeDiamond.lagda.md` | 278 | The four-node diamond scenario (edges A–B, A–C, B–D, C–D over one shared medium). Adds per-node **application logic** (`produce`/`consume`) that drives the CS+BF peers via `apiES`, realising a Praos-style block flow **A → {B,C} → D**; exposes `system` (over `NetworkA`) and `System_CopySpec` (over `CopySpecA`). Also documents why an explicit has-trace to D is intractable. Literate. |

## Verification — network (medium) properties

| Module | Lines | Purpose |
|---|--:|---|
| `NetworkDeadlockFree.agda` | 466 | Deadlock-freedom groundwork: the per-connection `Copy` buffer and its progress/liveness invariants. |
| `NetworkDeadlockFreeThm.agda` | 41 | Final deadlock-freedom theorem for `Network`, via the generic liveness results. |
| `NetworkDivergenceFreeThm.agda` | 128 | Divergence-freedom for `Network` (ports the generic `CopySpec` non-divergence invariant). |
| `NetworkADeadlockFreeThm.agda` | 63 | Deadlock-freedom lifted to the **renamed** multiplexer `NetworkA` via `rename-DeadlockFree`. |
| `NetworkADivergenceFreeThm.agda` | 52 | Divergence-freedom lifted to `NetworkA` via `rename-DivergenceFree`. |
| `NetworkRefinement.agda` | 4284 | Single-channel refinement `Network` vs `CopySpec` (instance `p1`: one KeepAlive connection). |
| `NetworkRefinementGen.agda` | 3137 | The single-channel refinement **generalised** in the forwarded payload `Data`. |
| `NetworkRefinementGenExp.agda` | 592 | Later steps of the generalised refinement. |
| `NetworkRefinementGenSanity.agda` | 29 | Instantiates the generalised refinement at `Data := ⊤` (sanity). |
| `NetworkSanity.agda` | 91 | Reduction / `refl`-style sanity checks for `Network` at the smallest non-trivial parameters. |

## Verification — BlockFetch refinements

| Module | Lines | Purpose |
|---|--:|---|
| `BlockFetchAbsRefinement.agda` | 3776 | Divergence-freedom of the hidden BlockFetch processes ⇒ `⊑D` (abstract client/server vs abstract spec). |
| `BlockFetchAbsRefinementBisim.agda` | 3914 | `clientServerBF ∖ msgBF ≈DR BFabstractP ∖ msgBF`, directly as a divergence-respecting weak bisimulation. |
| `BlockFetchNetRefinement.agda` | 3612 | Divergence-freedom of the hidden BlockFetch **network** processes. |
| `BlockFetchNetRefinementNet.agda` | 930 | `net-noDiv`: the hidden network process's `Good` graph over reachable joint configs. |
| `BlockFetchNetRefinementBisim.agda` | 8562 | `BFnetSpec ∖ bfMsgES ≈DR networkBF ∖ ioBF`, directly as a divergence-respecting weak bisimulation. |

## Probes / miscellaneous

| Module | Lines | Purpose |
|---|--:|---|
| `EvBothProbe.agda` | 131 | Feasibility probe showing the `evBoth` (par-`brBoth`) ⊓-overlap never fires in the single-channel `Network` compositions. |

## Typechecking

From the repository's `src/` directory (never the repo root):

```
cd src && agda CSP/Examples/Cardano_network/FourNodeDiamond.lagda.md
```

Any module's imports are checked transitively. All modules use
`{-# OPTIONS --guardedness #-}`; there is no `NON_TERMINATING`. Build artefacts
go to `src/_build/`.

## Related documentation

- Algebraic-law validation status: `src/CSP/Laws_status.md`.
