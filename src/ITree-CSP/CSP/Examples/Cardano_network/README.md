# Cardano network example

A formalisation of the Cardano/Ouroboros **node-to-node (N2N) mini-protocols** and their composition over a shared network medium, built on the repository's generic CSP-over-process-trees layer (`Process_Trees`, `Semantics/*`, `CSP/*`).
Each mini-protocol (KeepAlive, ChainSync, BlockFetch, TxSubmission2, LeiosNotify, LeiosFetch) is written as a pair of **API-driven peer processes** (`PTree`) over a small per-protocol event type, then *renamed* into one shared alphabet `Net_Api Payload`. Peers talk to each other only through a **network medium** — either the faithful multiplexer `Network` (or its link-indexed rendering `NetworkLink`) or its behavioural specification `CopySpec` (a per-`(link, direction, protocol)` `input.l.d.id → output.l.d.id` copy), which are `≈FD`-equivalent. On top of this, whole-node and whole-network **systems** are assembled by parallel-composing peers with the medium and hiding the wire traffic, and several **behavioural properties** (deadlock-freedom, divergence-freedom, trace/failures-divergences refinement against specs) are
proved.

## Reading order (newcomer path)

`Params` → `Base` → `Data` → `Net` → `Network` → a peer module (e.g. `ChainSync`) → `NetCommon` → `NetworkPar` → `FourNode/FourNodeDiamond`, then `Parametric/Topology` → `Parametric/Node` for the N-node generalisation. The large `*Refinement*` files are self-contained proof developments and can be read last.

## Layering

```
Params ─▶ Base ─▶ Data ─▶ Net ─▶ Network ─▶ NetCommon ─▶ NetworkPar ─▶ FourNodeDiamond
                                    │            │             │
                          (peers) KeepAlive/ChainSync/BlockFetch/TxSubmission/
                                  LeiosNotify/LeiosFetch
                                    │
                          (proofs) Network*{DeadlockFree,DivergenceFree}Thm,
                                   Network*Refinement*, BlockFetch*Refinement*
```

## Foundations — parameters & data

| Module | Lines | Purpose |
|---|--:|---|
| `Params.agda` | 58 | The abstract data-domain bundle: opaque types (`Cookie`, `Block`, `Txid`, `LSlot`, …) that CSPm had to enumerate for FDR, each with a `DecEq` field, plus `numLinks : ℕ` (the number of protocol-independent TCP links, `Link = Fin numLinks`) and `linkConfig : Fin numLinks → List (Dir × IDs)` (which `(direction, protocol)` instances actually run on each link; unlisted ⇒ absent). Every scenario supplies a concrete `Params`. |
| `Base.agda` | 113 | Parameter-free finite control enums: the protocol ids `IDs` (`N2N_ChainSync`/`N2N_BlockFetch`/`N2N_TxSubmission`/`N2N_KeepAlive`/`N2N_LeiosNotify`/`N2N_LeiosFetch`), `BlockingStyle`, and **`Dir`** (`lo`/`hi` — which endpoint of a link initiates that link's mini-protocol instance), etc., with `DecEq`. |
| `Data.agda` | 643 | Derived structured types over the abstract domains (`Point`, `ChainRange`, `Header`, `Tip`, `Tx`, `Vote`), the per-protocol **message** datatypes, and the shared `Payload`. |
| `Net.agda` | 1502 | The shared network event type `Net` and `Net_Api`, both re-indexed by the pair `(l : Link) (d : Dir)` in place of the old per-protocol `Conn`: 8 wire channels `input`/`output`/`sndmsg`/`rcvmsg`/`tx`/`sndack`/`rcvack`/`ack` each take `(l : Link) (d : Dir) → IDs → …`. A "connection" is now a protocol-independent TCP link plus a direction distinguishing the two client/server mini-protocol instances the link can run; `Net_Api` adds the peer-local `apiXX`/`done` channels (also `(l, d)`-indexed, one `apiXX` per mini-protocol including `apiLN`/`apiLF`) and the `ApiXXTag`/`ApiXXCar` API surfaces, plus the node-local `store`/`env` channels (a node's block store, and the environment forging into it) and the fault-injection trigger `break : (l : Link) → Net_Api Data ⊤`, with decidable equality `Net-≟`/`Net_Api-≟`. |

## The network medium

| Module | Lines | Purpose |
|---|--:|---|
| `Network.agda` | 273 | The multiplexer `Network` (a faithful PTree rendering of the CSPm `Network`: `Inputs`/`Outputs` leaves synchronised with `Transmitter`/`Receiver`/`SndAck`/`RcvAck` over `tx`/`ack`), **and** its behavioural spec `CopySpec` = per-`(l, d, id)` `input.l.d.id ? x → output.l.d.id ! x` copy. Both are **config-driven** over `linkConfig`: the replicated interleavings (`Inputs`, `CopySpec`, …) instantiate one live cell per `(d, id)` configured on each link `l`, and an unconfigured instance contributes no cell (empty list ⇒ `Skip`). Generic in the forwarded `Data`. |
| `NetworkLink.agda` | 137 | A second rendering of the same CSPm `Network`, replicated **per TCP link**: `NetOneLink l = (TxSideₗ l ∥{\|tx,ack\|}∥ RxSideₗ l) ∖ {\|tx,ack\|}` with link-local `Transmitterₗ`/`Receiverₗ`/`SndAckₗ`/`RcvAckₗ` buffers, and `NetworkLink = ⦀Fin numLinks NetOneLink`. Its `≈DR` equivalence with `CopySpec` is proved in `NetworkVerification/NetworkLinkEquiv.agda`. |
| `NetCommon.agda` | 172 | Renames `Net ↪ Net_Api`; defines the renamed media `NetworkA` and `NetworkLinkA`, the renamed spec `CopySpecA`, the `{\| input, output \|}` sync set `ioES`, the per-link renamed cells `linkMediumA`/`netLinkMediumA`, their `break`-interrupted variants and the breakable media `CopySpecBreakableA`/`NetworkLinkBreakableA`, and the `withNet`/`clientServerNet` composition helpers. |
| `NetworkPar.agda` | 441 | Renames **all six** protocols' peers into `Net_Api` (`KAclientA`/`KAserverA`, `CSclientA`/`CSserverA`, `BFclientA`/`BFserverA`, `TSclientA`/`TSserverA`, `LNclientA`/`LNserverA`, `LFclientA`/`LFserverA`), each now taking an explicit `(l : Link) (d : Dir)`. Bundles them two ways: `miniProtocols l cl sv` (uniform — all twelve peers, client on direction `cl`, server on `sv`) and the **config-driven** `nodeBundle l cl sv` (via `clientPeer`/`serverPeer` dispatch, reading only the `(direction, protocol)` instances that `linkConfig l` actually configures; a direction that is neither `cl` nor `sv` contributes `Skip`). `clientPeer`/`serverPeer` are total on `IDs` — the Leios ids now have real peers. The old `nodeNetwork` has been removed in favour of these. |
| `BundleBridge.agda` | 241 | Relates the two bundle builders of `NetworkPar` on a link whose config lists exactly the twelve instances (`FullConfig`, a propositional equality with the literal list). Both endpoints are proved but at different strengths: `cl ≡ lo` at `∼` (only `⦀⋆`'s trailing `Skip` differs), `cl ≡ hi` only at `≈FD` — there each entry's role inverts, needing six `⦀-exchange-FD` transpositions, and the module records the three-way-offer counterexample refuting exchange at `∼`. |
| `ApiAlphabet.agda` | 84 | The `{\| all api channels \|}` sync set `apiES` for any `Params` — the api analogue of `NetCommon`'s `ioES`, hoisted out of the scenarios that were each re-deriving it. Deliberately *not* used by the diamond, whose faithfulness gate needs its own `apiES` term to stay `refl`-equal. |
| `MediumEquivA.agda` | 295 | The **breakable-medium** equivalence `NetworkLinkBreakableA ≈DR CopySpecBreakableA`: `NetworkVerification/PerLink`'s per-link `perLink` lifted through `cong-renameMap` → `cong-△` → `cong-⦀Fin`, carrying `perLink`'s two honest hypotheses (`linkConfig l ≢ []`, `Unique (linkConfig l)`). The new work is the post-rename alphabet family `linkAlphaA` (which must mention `break`) and the `NoRet` invariant that feeds `cong-△`'s `Sep△` obligations. |
| `NetModel.agda` | 204 | Standalone state-position abstraction of the `Network` leaves (per-leaf position enums `IP`/`TP`/`RP`/… for Inputs/Transmitter/RcvAck/Outputs/Receiver/SndAck); a reasoning aid for the medium's reachable configurations. Not imported by the others. |

## Mini-protocol peers

Each module defines a small per-protocol event type, its `DecEq`, and the **client** and **server** peer FSMs as productive `iter` loops driven by `apiXX` API events. (The renaming into `Net_Api` happens in `NetworkPar`.)

| Module | Lines | Protocol |
|---|--:|---|
| `KeepAlive.agda` | 273 | KeepAlive (cookie ping/response). |
| `ChainSync.agda` | 353 | ChainSync (consumer tracks producer's chain: RequestNext / AwaitReply / RollForward / RollBackward / FindIntersect). |
| `BlockFetch.lagda.md` | 1225 | BlockFetch (RequestRange → StartBatch → Block* → BatchDone / NoBlocks; ClientDone). Literate. |
| `TxSubmission.agda` | 346 | TxSubmission2 (tx-id / tx request-reply, blocking & pipelined). |
| `LeiosNotify.agda` | 255 | LeiosNotify (id 18): from `stIdle` the consumer requests the next notification (`MsgLNRequestNext` → `stBusy`) or terminates (`MsgLNDone`); in `stBusy` the producer replies with exactly one of four notifications (block announcement, block offer, block-txs offer, votes offer) and returns to `stIdle`. Wire events `sendLN`/`receiveLN`; api events `apiLNev`. |
| `LeiosFetch.agda` | 373 | LeiosFetch (id 19): from `stIdle` the consumer requests an endorser block (`MsgLFBlockRequest`), selective txs (`MsgLFBlockTxsRequest`), votes (`MsgLFVotesRequest`) or a block range (`MsgLFBlockRangeRequest`), or terminates (`MsgLFDone`); the producer delivers in the matching busy state. The block-range case **streams**: several `MsgLFNextBlockAndTxsInRange` before a final `MsgLFLastBlockAndTxsInRange`. Wire events `sendLF`/`receiveLF`; api events `apiLFev`. |

## Scenario / system — `FourNode/`

| Module | Lines | Purpose |
|---|--:|---|
| `FourNode/FourNodeDiamond.lagda.md` | 317 | The four-node diamond scenario (edges A–B, A–C, B–D, C–D over one shared medium), using the **uniform** `miniProtocols` bundle (all six protocols on every link). Adds per-node **application logic** (`produce`/`consume`) that drives the CS+BF peers via `apiES`, realising a Praos-style block flow **A → {B,C} → D**; exposes `system` (over `NetworkA`) and `System_CopySpec` (over `CopySpecA`). Also documents why an explicit has-trace to D is intractable. Literate. |
| `FourNode/FourNodeDiamondCfg.lagda.md` | 316 | The same diamond scenario, but with a **non-uniform, `linkConfig`-driven** per-link setup (via `nodeBundle`): each link carries only ChainSync + BlockFetch in both directions — KeepAlive/TxSubmission/Leios are unconfigured, so no peers or medium cells are instantiated for them. Demonstrates the config-driven medium/`NetworkPar` machinery on a trimmed alphabet. Literate. |
| `FourNode/FourNodeDiamondBreakable.lagda.md` | 134 | The same four nodes as `FourNode/FourNodeDiamond`, but composed over the **breakable** medium `CopySpecBreakableA` instead of `CopySpec`, exposing `breakableSystem`. Fault injection is demonstrated via the isolated-link witness `break-fires : breakableLinkA linkBD ─[ break linkBD ]─► Skip` (the `break` event fires as a visible LTS step and the link terminates, √). A full composed-system trace is documented as intractable for the same reason as in `FourNode/FourNodeDiamond`, so only the isolated-medium witness is given; the module's closing discussion reasons informally about the consequence (the B→D relay dies, while the A→C→D path stays healthy). Literate. |
| `FourNode/BreakableSystemEquiv.agda` | 440 | `∀ blkA → breakableSystemₗ blkA ≈DR breakableSystem blkA` — `MediumEquivA`'s medium equivalence lifted through the whole `(· ∥⇘ ioES ⇙ nodes) ∖ ioES` composition by `cong-Par⊤-L` then `cong-∖`, the two systems differing only in the medium operand. The real work is the two `Sep ioES` obligations, discharged from `OffersOnly` witnesses on each side. |

`FourNode/Liveness/` holds the block-liveness campaign for the breakable diamond
— 164 modules in two independent routes (`LTL/`, the headline `blockLiveness⁺`,
and `CSP_Refinement/`) over one shared `≈DR` bisimulation (`R2_Bisim/`). It has
its own layout guide: [`FourNode/Liveness/README.md`](FourNode/Liveness/README.md).

## Verification — network (medium) properties

The folder has its own guide, with the dependency DAG and the per-file statements: [`NetworkVerification/README.md`](NetworkVerification/README.md).

| Module | Lines | Purpose |
|---|--:|---|
| `NetworkVerification/NetworkDeadlockFree.agda` | 475 | Deadlock-freedom groundwork: the per-connection `Copy` buffer and its progress/liveness invariants. |
| `NetworkVerification/NetworkDeadlockFreeThm.agda` | 41 | Final deadlock-freedom theorem for `Network`, via the generic liveness results. |
| `NetworkVerification/NetworkDivergenceFreeThm.agda` | 128 | Divergence-freedom for `Network` (ports the generic `CopySpec` non-divergence invariant). |
| `NetworkVerification/NetworkADeadlockFreeThm.agda` | 63 | Deadlock-freedom lifted to the **renamed** multiplexer `NetworkA` via `rename-DeadlockFree`. |
| `NetworkVerification/NetworkADivergenceFreeThm.agda` | 52 | Divergence-freedom lifted to `NetworkA` via `rename-DivergenceFree`. |
| `NetworkVerification/NetworkRefinement.agda` | 4451 | Single-channel refinement `Network` vs `CopySpec` (instance `p1`: one KeepAlive connection). |
| `NetworkVerification/NetworkRefinementGen.agda` | 3339 | The single-channel refinement **generalised** in the forwarded payload `Data`. |
| `NetworkVerification/NetworkRefinementGenExp.agda` | 598 | Later steps of the generalised refinement. |
| `NetworkVerification/NetworkRefinementGenSanity.agda` | 29 | Instantiates the generalised refinement at `Data := ⊤` (sanity). |
| `NetworkVerification/NetworkSanity.agda` | 109 | Reduction / `refl`-style sanity checks for `Network` at the smallest non-trivial parameters. |
| `NetworkVerification/NetworkLinkOffers.agda` | 266 | The per-link alphabets `linkAlpha l` and the two `OffersOnly` confinement results (`NetOneLink l` / `linkCopy l` only ever offer link-`l` events), plus `linkAlpha-disj` — the pairwise-`Disj` premises of `cong-⦀Fin`. |
| `NetworkVerification/NetworkLinkEquiv.agda` | 165 | The headline `NetworkLink ≈DR CopySpec` (and `≈FD`/`⊑FD`/`spec⊑FD-Link`), one application of `cong-⦀Fin` over `NetworkLinkOffers` fed by the per-link `perLink` of `PerLink/`. **0 postulates**; holds for any per-link `≢ [] × Unique` config, with the all-singleton results as corollaries. |
| `NetworkVerification/NetworkLinkSanity.agda` | 66 | Instantiates the postulate-free all-singleton `NetworkLink ≈FD CopySpec` at a two-link scenario (KeepAlive on link 0, BlockFetch on link 1), `Data := ⊤`. |
| `NetworkVerification/PerLink/` | 5 modules | The per-link obligation `perLink : (l : Link) → linkConfig l ≢ [] → Unique (linkConfig l) → NetOneLink l ≈DR linkCopy l`, built `State` → `Decode` → `Leaf` → `Fold` → `Exp` (the `⦀⋆`-fold expansion). |
| `NetworkVerification/Liveness/` | 25 modules | Node-level liveness groundwork for the diamond (`NodeA`/`NodeBC`/`NodeD`, their offer lemmas, and the `PipePair*` failure-simulation chain). |
| `NetworkVerification/LivenessSpike.agda` | 232 | A **disposable** feasibility spike for the four-node liveness campaign (imported by nothing; unsolved metas / postulates permitted there only). |

## Verification — BlockFetch refinements

| Module | Lines | Purpose |
|---|--:|---|
| `BlockFetchRefinement/BlockFetchAbsRefinement.agda` | 3776 | Divergence-freedom of the hidden BlockFetch processes ⇒ `⊇D` (abstract client/server vs abstract spec). |
| `BlockFetchRefinement/BlockFetchAbsRefinementBisim.agda` | 3914 | `clientServerBF ∖ msgBF ≈DR BFabstractP ∖ msgBF`, directly as a divergence-respecting weak bisimulation. |
| `BlockFetchRefinement/BlockFetchNetRefinement.agda` | 3612 | Divergence-freedom of the hidden BlockFetch **network** processes. |
| `BlockFetchRefinement/BlockFetchNetRefinementNet.agda` | 930 | `net-noDiv`: the hidden network process's `Good` graph over reachable joint configs. |
| `BlockFetchRefinement/BlockFetchNetRefinementBisim.agda` | 8562 | `BFnetSpec ∖ bfMsgES ≈DR networkBF ∖ ioBF`, directly as a divergence-respecting weak bisimulation. |

## `Parametric/` — the topology-generic (N-node) layer

Replaces the diamond's four hand-written nodes by one graph-driven definition, and states the network properties over an arbitrary topology. 31 modules, grouped:

| Group | Modules | Purpose |
|---|--:|---|
| Graph & node scaffolding (`Topology`, `Node`, `NodeLogic`, `Assembly`, `FoldGate`) | 5 | `Topology` is the network graph (nodes, each link's `lo`/`hi` endpoints, each node's incident `(link, own-direction)` list); `Node` builds one generic `node`/`systemOf` from it, with the peer-bundle builder as a parameter (config-driven `nodeBundle` or uniform `miniProtocols`); `NodeLogic` supplies the topology-generic **looping relay** logic (per-endpoint client/server/LN thread quadruples against a `blockStore`); `Assembly`'s `systemN-mono` is the N-ary `⊑FD` assembly lemma (node fold + medium + the first `∖ ioES`); `FoldGate` pins the `⦀Fin⁺` `refl`s the fold relies on as a regression test. |
| Announcement safety (`Announce*`) | 12 | The campaign's headline: `announceSafeT` — *a network of honest relays never announces an unforged block* — at `⊑T` over the concrete per-link multiplexer, for **every** `Params` and `Topology`, with `LinkCfgWf p` (per-link config non-empty and duplicate-free) as its only premise. `AnnounceSafeNegative`/`AnnounceBad*` are the negative controls. Full assumption list: [`Parametric/AnnouncementSafety.md`](Parametric/AnnouncementSafety.md). |
| Block provenance (`BlockProvenance*`) | 8 | Provenance as a **payload** invariant: the assume-guarantee carrier `Wf` ("every block I emit is well-announced, provided every block I was handed was") and its congruences, since every component in the chain is a relay; `BlockProvenanceSafe` bridges `Wf` to the announcement-safety carrier's `Safe` under the `Covers G` side condition. |
| Topology instances (`LineInstance`, `StarInstance`, `DiamondInstance`, `LeiosInstance`) | 4 | A three-node line (derived `endpointsOf` via `mkTopology`), a five-node star (scaffolding test — `numNodes ≢ numLinks`, degree-1 and degree-4 nodes, node logic `Skip`), the four-node diamond plus **the faithfulness gate** (`systemOfCopyUniform (diamondLogic blkA) ≡ breakableSystem blkA` by `refl`, over both media), and the first concrete Leios scenario with non-trivial `EB`/`EBHash`/`Block` so `announceOK` is non-degenerate. |
| `RelayLive`, `Spike/HideDiverge` | 2 | `RelayLive` is the **reachability witness** — without it every statement above `NodeLogic` would be vacuously true of a relay that cannot move (two such defects were found and fixed this way). `Spike/HideDiverge` settles the assembly lemma's precondition: hiding `ioES` over looping nodes does **not** diverge, because `ioES` hides only `input`/`output` and every peer cycle passes through an `api…` event. |

## `Priority/` — Praos-over-Leios priority

BlockFetch (Praos) prioritised over LeiosFetch (Leios) at each link's send arbiter, via the generic channel-level `Priᶜ` of `CSP/Priority/`: `BfOverLf.agda` (163) is the order, `NetworkLinkPri.agda` (201) overlays it on the per-link `Inputsₗ` send queue (so LeiosFetch is *delayed, not lost*), `TxSidePriOneLink.agda` (237) proves P1 prune-under-contention / P2 delayed-not-lost / P3 no-deadlock on a concrete one-link `Params`, and `FourNodeDiamondPri.lagda.md` (47) is the whole-diamond construction over the prioritised medium. See [`Priority/README.md`](Priority/README.md).

## `Terminable/` — graceful shutdown (experimental)

Self-contained inside the subfolder, because the parent `Net`/`Net_Api` alphabet has no `mdone`: `NetT.agda` (168) is a local alphabet — the parent's eight wire channels plus a per-instance `mdone l d id` — `NetworkT.agda` (468) is the terminable medium (each copy cell runs normally until its own `mdone` fires, then terminates √), `NetworkTRefinement.agda` (888) is the single-instance terminable refinement carrier generic in the payload `Data`, and `FourNodeDiamondTerminable.lagda.md` (173) is the shutdown demo with local driver nodes. `mdone` is deliberately outside `ioES`, so it stays observable.

## Probes / miscellaneous

| Module | Lines | Purpose |
|---|--:|---|
| `EvBothProbe.agda` | 131 | Feasibility probe showing the `evBoth` (par-`brBoth`) ⊓-overlap never fires in the single-channel `Network` compositions. |

## Link/direction model — status notes

- **Link breakage is modelled.** Rather than a static feature of `Network`/`CopySpec`, a broken link is modelled *dynamically*, on top of the existing static `Link`/`Dir` medium, using the CSP interrupt operator `_△_` (`CSP/Operators.agda`) together with a new observable event `break : (l : Link) → Net_Api Data ⊤` (declared in `Net.agda`'s `Net_Api`, deliberately **not** in `ioES`, so it stays observable at the top level even after `∖ ioES` hides the wire traffic). `Network.agda` now exposes the per-link copy bundle `linkCopy : Link → NetProc` (used both by `CopySpec` and by the breakable medium). `NetCommon.agda` renames it into `Net_Api` (`linkMediumA l = RenNet.renameMap (linkCopy l)`) and interrupts each link with its own fault event: `breakableLinkA l = linkMediumA l △ (break l ⟶₀ Skip)` — link `l` runs normally until `break l` fires, after which it **terminates (√)** rather than deadlocking: the cell goes to `Skip`, so its `input`/`output` channels are permanently refused because the link has finished, not because it has stalled.  `CopySpecBreakableA = ⦀Fin numLinks breakableLinkA` composes every link independently-breakable. `FourNode/FourNodeDiamondBreakable.lagda.md` demonstrates this on the four-node diamond (see the scenario table above); a full composed-system trace remains intractable to normalise (same reason as `FourNode/FourNodeDiamond`), so only an isolated-medium witness (`break-fires`) is proved, showing `break linkBD` fires as a visible LTS step and drives the link to `Skip`.
- **`NetworkVerification/` — ported to `Link × Dir` and green.** All 10 modules (the `NetworkRefinement*` expansion chain building `net≈DR : Network ≈DR CopySpec`, the deadlock-/divergence-freedom theorems, the renamed-`NetworkA` lifts, and the sanity checks) typecheck against the current `Link`/`Dir`/`linkConfig` medium with **0 postulates**; the link-indexed `NetworkLink ≈DR CopySpec` work (`NetworkLinkEquiv`/`NetworkLinkOffers` over `PerLink/`) is likewise complete and postulate-free. The single-channel instance is now `numLinks = 1`, `linkConfig _ = (lo , N2N_KeepAlive) ∷ []`.
- **Not yet ported to `Link × Dir`.** The `BlockFetchRefinement/` subfolder, `EvBothProbe.agda`, and `NetModel.agda` were written against the earlier per-protocol `Conn` model and are kept in the tree for later re-porting; `Params`, `Base`, `Data`, `Net`, `Network`, `NetworkLink`, `NetCommon`, `NetworkPar`, the six mini-protocol peers, the `FourNode/` scenarios, and the `NetworkVerification/`, `Parametric/`, `Priority/` and `Terminable/` subfolders are current.

## Typechecking

From the repository's `src/` directory (never the repo root):

```
cd src && agda CSP/Examples/Cardano_network/FourNode/FourNodeDiamond.lagda.md
```

Any module's imports are checked transitively. All modules use `{-# OPTIONS --guardedness #-}`; there is no `NON_TERMINATING`. Build artefacts go to `src/_build/`.

## Related documentation

- Algebraic-law validation status: `src/CSP/Laws_status.md`.
