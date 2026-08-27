# Cardano network example

A formalisation of the Cardano/Ouroboros **node-to-node (N2N) mini-protocols**
and their composition over a shared network medium, built on the repository's
generic CSP-over-process-trees layer (`Process_Trees`, `Semantics/*`, `CSP/*`).

Each mini-protocol (KeepAlive, ChainSync, BlockFetch, TxSubmission2, and the
Leios protocols in the data layer) is written as a pair of **API-driven peer
processes** (`PTree`) over a small per-protocol event type, then *renamed* into
one shared alphabet `Net_Api Payload`. Peers talk to each other only through a
**network medium** — either the faithful multiplexer `Network` or its behavioural
specification `CopySpec` (a per-`(link, direction, protocol)` `input.l.d.id →
output.l.d.id` copy), which are `≈FD`-equivalent. On top of this, whole-node and
whole-network **systems** are
assembled by parallel-composing peers with the medium and hiding the wire
traffic, and several **behavioural properties** (deadlock-freedom,
divergence-freedom, trace/failures-divergences refinement against specs) are
proved.

## Reading order (newcomer path)

`Params` → `Base` → `Data` → `Net` → `Network` → a peer module (e.g. `ChainSync`)
→ `NetCommon` → `NetworkPar` → `FourNode/FourNodeDiamond`. The large `*Refinement*` files
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
| `Params.agda` | 49 | The abstract data-domain bundle: opaque types (`Cookie`, `Block`, `Txid`, `LSlot`, …) that CSPm had to enumerate for FDR, each with a `DecEq` field, plus `numLinks : ℕ` (the number of protocol-independent TCP links, `Link = Fin numLinks`) and `linkConfig : Fin numLinks → List (Dir × IDs)` (which `(direction, protocol)` instances actually run on each link; unlisted ⇒ absent). Every scenario supplies a concrete `Params`. |
| `Base.agda` | 113 | Parameter-free finite control enums: the protocol ids `IDs` (`N2N_ChainSync`/`N2N_BlockFetch`/`N2N_TxSubmission`/`N2N_KeepAlive`/`N2N_LeiosNotify`/`N2N_LeiosFetch`), `BlockingStyle`, and **`Dir`** (`lo`/`hi` — which endpoint of a link initiates that link's mini-protocol instance), etc., with `DecEq`. |
| `Data.agda` | 637 | Derived structured types over the abstract domains (`Point`, `ChainRange`, `Header`, `Tip`, `Tx`, `Vote`), the per-protocol **message** datatypes, and the shared `Payload`. |
| `Net.agda` | 1334 | The shared network event type `Net` and `Net_Api`, both re-indexed by the pair `(l : Link) (d : Dir)` in place of the old per-protocol `Conn`: 8 wire channels `input`/`output`/`sndmsg`/`rcvmsg`/`tx`/`sndack`/`rcvack`/`ack` each take `(l : Link) (d : Dir) → IDs → …`. A "connection" is now a protocol-independent TCP link plus a direction distinguishing the two client/server mini-protocol instances the link can run; `Net_Api` adds the peer-local `apiXX`/`done` channels (also `(l, d)`-indexed) and the `ApiXXTag`/`ApiXXCar` API surfaces, with decidable equality `Net-≟`/`Net_Api-≟`. |

## The network medium

| Module | Lines | Purpose |
|---|--:|---|
| `Network.agda` | 266 | The multiplexer `Network` (a faithful PTree rendering of the CSPm `Network`: `Inputs`/`Outputs` leaves synchronised with `Transmitter`/`Receiver`/`SndAck`/`RcvAck` over `tx`/`ack`), **and** its behavioural spec `CopySpec` = per-`(l, d, id)` `input.l.d.id ? x → output.l.d.id ! x` copy. Both are **config-driven** over `linkConfig`: the replicated interleavings (`Inputs`, `CopySpec`, …) instantiate one live cell per `(d, id)` configured on each link `l`, and an unconfigured instance contributes no cell (empty list ⇒ `Skip`). Generic in the forwarded `Data`. |
| `NetCommon.agda` | 129 | Renames `Net ↪ Net_Api`; defines the renamed medium `NetworkA`, the renamed spec `CopySpecA`, the `{\| input, output \|}` sync set `ioES`, and the `withNet`/`clientServerNet` composition helpers. |
| `NetworkPar.agda` | 326 | Renames each protocol's peers into `Net_Api` (`KAclientA`/`KAserverA`, `CSclientA`/`CSserverA`, `BFclientA`/`BFserverA`, `TSclientA`/`TSserverA`), each now taking an explicit `(l : Link) (d : Dir)`. Bundles them two ways: `miniProtocols l cl sv` (uniform — every protocol, client on direction `cl`, server on `sv`; faithful port of the old fixed-arity bundle) and the **config-driven** `nodeBundle l cl sv` (via `clientPeer`/`serverPeer` dispatch, reading only the `(direction, protocol)` instances that `linkConfig l` actually configures; unconfigured/Leios instances ⇒ `Skip`). The old `nodeNetwork` has been removed in favour of these. |
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
| `FourNode/FourNodeDiamond.lagda.md` | 287 | The four-node diamond scenario (edges A–B, A–C, B–D, C–D over one shared medium), using the **uniform** `miniProtocols` bundle (all four protocols on every link). Adds per-node **application logic** (`produce`/`consume`) that drives the CS+BF peers via `apiES`, realising a Praos-style block flow **A → {B,C} → D**; exposes `system` (over `NetworkA`) and `System_CopySpec` (over `CopySpecA`). Also documents why an explicit has-trace to D is intractable. Literate. |
| `FourNode/FourNodeDiamondCfg.lagda.md` | 302 | The same diamond scenario, but with a **non-uniform, `linkConfig`-driven** per-link setup (via `nodeBundle`): each link carries only ChainSync + BlockFetch in both directions — KeepAlive/TxSubmission/Leios are unconfigured, so no peers or medium cells are instantiated for them. Demonstrates the config-driven medium/`NetworkPar` machinery on a trimmed alphabet. Literate. |
| `FourNode/FourNodeDiamondBreakable.lagda.md` | 120 | The same four nodes as `FourNode/FourNodeDiamond`, but composed over the **breakable** medium `CopySpecBreakableA` instead of `CopySpec`, exposing `breakableSystem`. Fault injection is demonstrated via the isolated-link witness `break-fires : breakableLinkA linkBD ─[ break linkBD ]─► Skip` (the `break` event fires as a visible LTS step and the link terminates, √). A full composed-system trace is documented as intractable for the same reason as in `FourNode/FourNodeDiamond`, so only the isolated-medium witness is given; the module's closing discussion reasons informally about the consequence (the B→D relay dies, while the A→C→D path stays healthy). Literate. |

## Verification — network (medium) properties

| Module | Lines | Purpose |
|---|--:|---|
| `NetworkVerification/NetworkDeadlockFree.agda` | 466 | Deadlock-freedom groundwork: the per-connection `Copy` buffer and its progress/liveness invariants. |
| `NetworkVerification/NetworkDeadlockFreeThm.agda` | 41 | Final deadlock-freedom theorem for `Network`, via the generic liveness results. |
| `NetworkVerification/NetworkDivergenceFreeThm.agda` | 128 | Divergence-freedom for `Network` (ports the generic `CopySpec` non-divergence invariant). |
| `NetworkVerification/NetworkADeadlockFreeThm.agda` | 63 | Deadlock-freedom lifted to the **renamed** multiplexer `NetworkA` via `rename-DeadlockFree`. |
| `NetworkVerification/NetworkADivergenceFreeThm.agda` | 52 | Divergence-freedom lifted to `NetworkA` via `rename-DivergenceFree`. |
| `NetworkVerification/NetworkRefinement.agda` | 4284 | Single-channel refinement `Network` vs `CopySpec` (instance `p1`: one KeepAlive connection). |
| `NetworkVerification/NetworkRefinementGen.agda` | 3137 | The single-channel refinement **generalised** in the forwarded payload `Data`. |
| `NetworkVerification/NetworkRefinementGenExp.agda` | 592 | Later steps of the generalised refinement. |
| `NetworkVerification/NetworkRefinementGenSanity.agda` | 29 | Instantiates the generalised refinement at `Data := ⊤` (sanity). |
| `NetworkVerification/NetworkSanity.agda` | 91 | Reduction / `refl`-style sanity checks for `Network` at the smallest non-trivial parameters. |

## Verification — BlockFetch refinements

| Module | Lines | Purpose |
|---|--:|---|
| `BlockFetchRefinement/BlockFetchAbsRefinement.agda` | 3776 | Divergence-freedom of the hidden BlockFetch processes ⇒ `⊑D` (abstract client/server vs abstract spec). |
| `BlockFetchRefinement/BlockFetchAbsRefinementBisim.agda` | 3914 | `clientServerBF ∖ msgBF ≈DR BFabstractP ∖ msgBF`, directly as a divergence-respecting weak bisimulation. |
| `BlockFetchRefinement/BlockFetchNetRefinement.agda` | 3612 | Divergence-freedom of the hidden BlockFetch **network** processes. |
| `BlockFetchRefinement/BlockFetchNetRefinementNet.agda` | 930 | `net-noDiv`: the hidden network process's `Good` graph over reachable joint configs. |
| `BlockFetchRefinement/BlockFetchNetRefinementBisim.agda` | 8562 | `BFnetSpec ∖ bfMsgES ≈DR networkBF ∖ ioBF`, directly as a divergence-respecting weak bisimulation. |

## Probes / miscellaneous

| Module | Lines | Purpose |
|---|--:|---|
| `EvBothProbe.agda` | 131 | Feasibility probe showing the `evBoth` (par-`brBoth`) ⊓-overlap never fires in the single-channel `Network` compositions. |

## Link/direction model — status notes

- **Link breakage is modelled.** Rather than a static feature of
  `Network`/`CopySpec`, a broken link is modelled *dynamically*, on top of the
  existing static `Link`/`Dir` medium, using the CSP interrupt operator `_△_`
  (`CSP/Operators.agda`) together with a new observable event
  `break : (l : Link) → Net_Api Data ⊤` (declared in `Net.agda`'s `Net_Api`,
  deliberately **not** in `ioES`, so it stays observable at the top level even
  after `∖ ioES` hides the wire traffic). `Network.agda` now exposes the
  per-link copy bundle `linkCopy : Link → NetProc` (used both by `CopySpec`
  and by the breakable medium). `NetCommon.agda` renames it into `Net_Api`
  (`linkMediumA l = RenNet.renameMap (linkCopy l)`) and interrupts each link
  with its own fault event: `breakableLinkA l = linkMediumA l △ (break l ⟶₀
  Skip)` — link `l` runs normally until `break l` fires, after which it
  **terminates (√)** rather than deadlocking: the cell goes to `Skip`, so its
  `input`/`output` channels are permanently refused because the link has
  finished, not because it has stalled.
  `CopySpecBreakableA = ⦀Fin numLinks breakableLinkA` composes every link
  independently-breakable. `FourNode/FourNodeDiamondBreakable.lagda.md` demonstrates this
  on the four-node diamond (see the scenario table above); a full
  composed-system trace remains intractable to normalise (same reason as
  `FourNode/FourNodeDiamond`), so only an isolated-medium witness
  (`break-fires`) is proved, showing `break linkBD` fires as a visible LTS
  step and drives the link to `Skip`.
- **`NetworkVerification/` — ported to `Link × Dir` and green.** All 10 modules
  (the `NetworkRefinement*` expansion chain building `net≈DR : Network ≈DR
  CopySpec`, the deadlock-/divergence-freedom theorems, the renamed-`NetworkA`
  lifts, and the sanity checks) typecheck against the current
  `Link`/`Dir`/`linkConfig` medium with **0 postulates**. The single-channel
  instance is now `numLinks = 1`, `linkConfig _ = (lo , N2N_KeepAlive) ∷ []`.
- **Not yet ported to `Link × Dir`.** The `BlockFetchRefinement/` subfolder,
  `EvBothProbe.agda`, and `NetModel.agda` were written against the earlier
  per-protocol `Conn` model and are kept in the tree for later re-porting;
  `Params`, `Base`, `Data`, `Net`, `Network`, `NetCommon`, `NetworkPar`, the
  mini-protocol peers, the three `FourNode/FourNodeDiamond*` scenarios, the
  `Terminable/` subfolder, and now `NetworkVerification/` are current.

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
