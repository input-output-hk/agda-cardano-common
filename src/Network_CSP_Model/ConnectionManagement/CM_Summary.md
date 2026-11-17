# Connection-management model: what it establishes, what it found, and a shutdown design

## 1. Summary

- The project models the connection manager (CM), inbound governor (IG), outbound governor (OG), Server admission, and selected handler, mux and protocol lifecycles. It separates logical connection state from physical thread completion.
- Source mapping, model proofs, initialized examples, bounded exploration and Haskell replays provide complementary evidence. G0–G5 are met at their declared scopes; there is no full model-to-Haskell refinement theorem or universal progress result.
- Positive results cover primitive contracts, configured inbound/outbound lifecycles, concurrent incarnations, map ownership/uniqueness, handler-reference validity, and conditional shutdown certificates for collected handlers and owned callers.
- Three older CM findings—retained reservations, incomplete over-limit release, and unpublished handshake results—were re-tested at [IntersectMBO/ouroboros-network](https://github.com/IntersectMBO/ouroboros-network) [`2f1c154f248659b89523d5679ca532f442e7ed2a`](https://github.com/IntersectMBO/ouroboros-network/tree/2f1c154f248659b89523d5679ca532f442e7ed2a). The older IG overlap wedge remains evidence at [`4b3ab7664f609a1aee0f0c24dcfcfd0ab899fc42`](https://github.com/IntersectMBO/ouroboros-network/tree/4b3ab7664f609a1aee0f0c24dcfcfd0ab899fc42), without re-testing at the current pin.
- A self-purged handler can outlive CM shutdown: replay confirms this at the CM/tracer boundary. Late admission has separately replayed halves, but the combined Server race remains unconfirmed. Foreign callers exposed a model ownership artefact.
- Recommend Server-owned admission workers joined without cancellation, plus a historical CM handler registry swept at shutdown, with CM callers confined to their owning scopes.
- A small production prototype supports conditional quiescence. Publication failure, blocked cleanup and notification backpressure still prevent progress in explicit tests; resolve these before treating it as a generally terminating fix.

## 2. What the model is

This is a source-derived, executable model for engineers investigating connection ownership, races and teardown. Its objective is both to find source problems and to explore a correct design. It is independent of the repository's broader network-medium proofs and the older standalone GovernorWedge study. Readers do not need Agda to use the evidence summaries or review the proposed patch.

CM is shared state operated on callers' stacks, rather than a service thread. The machine represents interleavings between CM operations, IG decisions, OG jobs and monitors, Server admission workers, handlers, handshake promises, mux pools and protocol invocations. A connection-map entry, socket, handler, mux and protocol job have separate identities and lifetimes. Taking/restoring the map, committing STM, publishing a promise, sending cancellation, receiving it, running cleanup and obtaining an actual Async result are separate events. This exposes assumptions that a connection-state diagram alone would hide.

The current source authorities are [IntersectMBO/ouroboros-network](https://github.com/IntersectMBO/ouroboros-network) at [**`2f1c154f248659b89523d5679ca532f442e7ed2a`**](https://github.com/IntersectMBO/ouroboros-network/tree/2f1c154f248659b89523d5679ca532f442e7ed2a) and [IntersectMBO/ouroboros-consensus](https://github.com/IntersectMBO/ouroboros-consensus) at [**`2e44d98a843168ba3b189e305820b79943ac7d1e`**](https://github.com/IntersectMBO/ouroboros-consensus/tree/2e44d98a843168ba3b189e305820b79943ac7d1e). These are fixed revisions, not today's upstream status. [SourceLedger](SourceLedger.md) preserves historical pins and migration evidence. CM Core, IG, Server and JobPool are byte-identical between the historical CM pin of [IntersectMBO/ouroboros-network](https://github.com/IntersectMBO/ouroboros-network) [`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`](https://github.com/IntersectMBO/ouroboros-network/tree/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d) and the promoted [IntersectMBO/ouroboros-network](https://github.com/IntersectMBO/ouroboros-network) pin; byte comparison alone is not re-testing.

The reviewed `LocalLifecycle` profile starts after listener/governor setup: empty CM, one listener, two ordinary known peers, and known/established/active targets 2/2/1. These are scenario values. Peras, peer sharing, roots, discovery, churn and big-ledger policy are outside the profile. Transport, protocol, tracer and application outcomes have explicit contracts.

The [configured bundle][bundle] contains hot ChainSync, BlockFetch, TxSubmission2, LeiosNotify and LeiosFetch; warm is empty; established contains KeepAlive. Descriptor modes are demand-start for the hot group and grouped `StartOnDemandAny` for KeepAlive. Effective policy differs by direction: [initiator starts override descriptors with `StartEagerly`][start-init], while [IG responder starts retain descriptor modes][start-resp]. Duplex permits bearer reuse, not automatic execution of every callback. Payloads, drivers, DB readiness and private resources retain reviewed [protocol contracts](ProtocolContracts.md).

### Evidence and gates

| Evidence kind | What to take from it |
| --- | --- |
| Source audit/mapping | Operations and exception boundaries located at a fixed revision; supplied contracts and exclusions remain visible. |
| Model proof | A guarantee for every execution admitted by the named model layer and premises. It does not by itself establish source fidelity. |
| Initialized finite witness | A concrete executable lifecycle or counterexample from the stated initializer; existence, not inevitable completion. |
| Bounded exploration and checked shrinking | Coverage within a declared alphabet and bounds; shrinking preserves execution and the same violation, without global minimality. |
| Implementation replay | Selected operations in pinned Haskell, under recorded schedules and supplied inputs; finite observations, not universal implementation guarantees. |

[GateAudit](GateAudit.md) records acceptance as follows:

| Gate | Accepted scope |
| --- | --- |
| G0: domain/source mapping | Reviewed finite LocalLifecycle profile and explicit operation contracts. |
| G1: primitives | Selected map, STM, fork, promise, queue, timeout and cancellation contracts. |
| G2: combined lifecycle | Reviewed initialized finite lifecycles, including configured inbound/outbound bundles. |
| G3: concurrency | Initialized finite two-peer and same-key overlap histories. |
| G4: semantic bridge | Full raw supervised machine/process correspondence, including refusals of disabled actions. |
| G5: exploration/replay | Declared finite enumeration, checked exports/shrinking, and classified source-operation tests. |

The model is untimed: expiration inputs establish no deadline. Finite examples and searches establish neither fairness nor universal progress, delivery or deadlock freedom. G4 connects two representations of the model, not the model to Haskell. Selected one-listener scopes, initialization and callback contracts remain material limits. Full application behavior and arbitrary scheduling remain outside acceptance.

## 3. What it establishes

The [verified-properties summary](../review/connection-management-verified-properties-summary.md) gives exact theorem names and premises. The following is the engineering reading of those results.

### Reproduced behaviours

| Result | Evidence kind and premises |
| --- | --- |
| Primitive and branch coverage | Executable rules plus paired enabled/refusal controls cover 90/90 selected primitive contracts. The branch inventory has 99 rows: 67 implemented, 19 contracted, 13 excluded, zero missing. This accounts for reviewed boundaries; it is not universal branch execution or IO/IOSim equivalence. |
| Six lifecycle obligations | Initialized finite witnesses cover clean inbound, clean outbound, duplex reuse, handshake failure/cleanup, successful hot demotion and timeout/Cooling/Cold. They require their supplied transport/protocol outcomes; the configured extensions cover all six protocol numbers. The production timeout path uses mux shutdown and direct handler cleanup, without an invented foreign release. |
| Concurrent connections | Initialized OwnedCallers histories cover two executing peers (294 events) and three same-key incarnations with another key present (303). Old TIME_WAIT finalizers preserve newer bindings. The overlap endpoint intentionally retains live handlers; it is not a shutdown result. |
| Source policy inputs | Configured inbound/outbound runs use retry/clearing values 5/120, selected V15 data and explicit Tx V2. Proofs establish seed/split/comparator independence only for reached finite decisions, fixing eligible sets, clocks/order and outcomes; they establish no probability distribution. |
| Successful source controls | Actual-CM IOSim replays confirm cleanup after post-open configuration failure, transition to inbound-idle with spare capacity, and self-pruning of only the selected connection. M6 revalidates these at the current pin using synthetic transport/handshake inputs. |

The [exploration record](Exploration/README.md) distinguishes exact enabled-edge and bounded-reachability proofs from running an exhaustive search. Completeness holds only within the declared finite alphabet, depth and allocation cutoff. Checked text transport preserves actions and initialized endpoints; checked reductions retain the late, self-purge and foreign violations while shortening 50→46, 85→82 and 192→183 events. These are model traces, not automatically Haskell replay scripts.

### Proved guarantees

| Guarantee | Evidence kind, premises and practical scope |
| --- | --- |
| Exclusive map ownership | Model invariant: starting with valid ownership, each step preserves one matching claimant for a taken map and none for a full map. An initialized OG/CM execution lift retains this guarantee. |
| Map/key uniqueness | Model invariants preserve uniqueness from valid initial maps; caller-table and peer/key ownership have separate execution proofs. This does not assert arbitrary whole-store validity. |
| Handler/reference validity, CM-I4c | Model theorem: every run from successful `initialize (O.initial c₀) g` satisfies `FullValidity`, without extra invariant/history premises. It covers physical resources/captures, phases, handle/mux/promise chains, failure snapshots, controls, jobs, pools and saved-call ownership. The unrestricted-initializer claim is false. |
| Shutdown certificate, SI5 | Model theorem: successful initialization and an outer run reaching finished relays imply returned Server, closed peer pools/scopes, snapshot job results and joined relays. CM is closed with its snapshot drained; the closing wait observed every collected handler result. It covers that snapshot, not every historical handler or raw admission worker. |
| Quiet IG and caller residue | Under the finished-outer-run premises, IG is exited/inactive with no pending inbound-release or remote CM call. With `O.initial`, any remaining acquire/release frame is foreign to peer jobs and monitors and has no result. This explains residue rather than certifying arbitrary external callers. |
| Process semantics | Model correspondence relates dispatcher executions to raw process traces and equates stable refusal with disabled actions at every state, without initialization or finite-alphabet premises. It is not source refinement. |

The shutdown results are conditional on reaching their endpoints. They neither claim that every handler appears in the live map nor prove eventual return. The design variants in section 5 deliberately strengthen ownership and historical coverage beyond this source-derived snapshot certificate.

## 4. What it found

The [issues summary](../review/connection-management-identified-issues-summary.md) is the classification authority. All seven entries below matter; model fidelity corrections are recorded separately.

### Four earlier findings

| Finding | Revision and re-testing | Observation and source |
| --- | --- | --- |
| Socket-open failure leaves a reservation | Established at [`96ee6e0`](https://github.com/IntersectMBO/ouroboros-network/tree/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d); re-tested at [`2f1c154`](https://github.com/IntersectMBO/ouroboros-network/tree/2f1c154f248659b89523d5679ca532f442e7ed2a) in M6. | Actual CM/IOSim injection makes `openToConnect` throw while `ReservedOutbound` remains. Subsequent acquisitions return `ConnectionExists`; integrated governor replay eventually forgets the peer while CM retains the reservation. See the [historical acquire path][open-old] and [current acquire path][open-current]. This is not a real OS-exhaustion/deployment test. |
| Over-limit release reports success without completing the transition | Established at [`96ee6e0`](https://github.com/IntersectMBO/ouroboros-network/tree/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d); re-tested at [`2f1c154`](https://github.com/IntersectMBO/ouroboros-network/tree/2f1c154f248659b89523d5679ca532f442e7ed2a) in M6. | Actual CM API replay selects another connection for pruning. The surviving released connection stays `OutboundDup Ticking` instead of becoming inbound-idle. See the [historical over-limit branch][release-old] and [same branch at the current pin][release-current]. Spare-capacity and self-pruning controls distinguish the failure. |
| Unpublished handshake result strands a caller | Established at [`96ee6e0`](https://github.com/IntersectMBO/ouroboros-network/tree/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d); CM and Server probes re-tested at [`2f1c154`](https://github.com/IntersectMBO/ouroboros-network/tree/2f1c154f248659b89523d5679ca532f442e7ed2a) in M6, using plain mux. | Injected faults after negotiation but before promise publication leave the caller waiting after handler completion and map cleanup. See [historical handler publication][publication-old], [current handler ordering][publication-current] and the [inbound promise read][promise-read]. Actual Server replay observes admission workers blocked after scope return. Deployment relevance depends on the injected faults. |
| IG wedge from overlapping incarnations | Separate study at [`4b3ab76`](https://github.com/IntersectMBO/ouroboros-network/tree/4b3ab7664f609a1aee0f0c24dcfcfd0ab899fc42); **not re-tested at [`2f1c154`](https://github.com/IntersectMBO/ouroboros-network/tree/2f1c154f248659b89523d5679ca532f442e7ed2a)**. | A stale mux callback [looks up the current mux by connection key][wedge-callback], potentially selecting a newer live incarnation; the [IG completion path waits for it][wedge-wait]. Field observations, source analysis and checked model witnesses support this finding, rather than an M6 native replay. See [GovernorWedge scope and limits](../GovernorWedge/README.md#1-what-this-is). |

For the first three, [SourceReplay/M6](SourceReplay/README.md#m6-revalidation-at-network-2f1c154-9-november-2026) records exact controls and limitations. Fault injection and finite observations do not establish permanent leaks, production deadlock or deployment frequency. The Server report also records instrumentation/garbage-collection limits; external recovery remains possible.

### Self-purged handler outliving CM shutdown — replay-confirmed

The [current CM finalizer][shutdown] reads the connection map once, then cancels/waits for handlers found there. [Ordinary cleanup][cleanup] removes the binding before its counter tracer and physical completion. An empty map therefore does not imply every handler has finished.

In the direct-CM replay, admission succeeds and its worker is joined. A supplied buffer-acquisition failure starts actual handler cleanup. The socket closes exactly once, the binding disappears, and the cleanup counter tracer pauses. The actual CM-created handler still has no Async result before and after CM returns. Opening the gate lets it finish; the unpaused control has its result before return.

This confirms behavior at the tested CM/tracer boundary, with controlled inputs, not deployment frequency or every tracer. [Replay records](SourceReplay/README.md#handler-self-purge-before-the-cm-returns-12-november-2026) and increment 99 retain that classification. The prototype separately extends testing to the full Server/IG/accept route.

### Late admission — separate halves confirmed, combined race unconfirmed

[Server forks admission workers and discards their handles][workers]; its [surrounding action, IG and accept-loop scopes][scopes] do not join them. CM snapshots without marking the API closed, and [inbound include][include] has no shutdown guard.

An initialized model witness closes CM over an empty snapshot, returns Server, then lets an already-forked worker create a handler. On source, IOSimPOR explores 628 schedules within 20,000 schedule/20 branching bounds and finds Server/CM returned before the worker's first step, leaving an accepted connection unreleased. Separately, a retained CM handle accepts an include after shutdown and forks a handler. No explored unpatched trace combines that delayed Server worker with its late include. [Late-admission evidence](SourceReplay/README.md#late-admission-after-the-cm-shutdown-10-november-2026) therefore supports a strong candidate, not a confirmed combined race; bounded absence does not prove unreachability.

### Foreign callers — model artefact

The unrestricted model lets an external worker retain a CM handle, begin an outbound call and survive shutdown. Production outbound calls belong to [governor peer jobs and monitors][owned-calls]; the surviving frame belongs to the external caller's stack. Proofs classify residual frames as foreign, and an owned-callers variant excludes them. The deliberately external-caller replay is an environment/ownership correction, not a library cleanup defect.

### Model corrections, not further source defects

Fidelity work corrected primitive restoration/cancellation, timeout continuations, source policy inputs and protocol start modes. Inbound release originally lacked physical cancellation receipt: the corrected model separates send, target receipt, release return, protected cleanup and result publication. The [source inbound-release path][release-in] masks the sender, captures the handler and sends cancellation; the target can receive it during the [explicitly unmasked TIME_WAIT delay][timewait]. Receipt is not completion. Increment 82 supplies the initialized clean lifecycle. The issues summary also tracks earlier A1–A9 and SI4-F1 mapping limitations; extending these model rules is not a Haskell bug fix.

## 5. Shutdown design recommendation and prototype

Adopt the ownership/registry design in [DesignContract](DesignContract.md):

1. Retain Server admission Asyncs. Protect fork/registration together, preserve child masking, stop/join accept loops, and join every worker **without cancellation** before CM shutdown. Observe errors without skipping remaining joins, on every teardown route.
2. Retain every [inbound][inbound] and [outbound][outbound] CM handler Async independently of the live map. Make successful birth inseparable from registration. Preserve history across deletion, replacement, pruning and rollback.
3. Preserve existing snapshot cleanup, then sweep historical handlers: skip completed ones, cancel pending ones through permitted sites, and wait for every physical result. Quiesce owned callers before freezing history. Preserve [handler cleanup masking and unmasked TIME_WAIT][handler-finally].

Why these pieces are necessary:

| Alternative | Failure |
| --- | --- |
| Own, cancel and join admissions | Cancellation after handler fork but before publication can make [`modifyTMVar` restore the old map][restore], losing the child binding. Joining the worker does not join its child. Evidence includes a standalone primitive-contract probe, not a full CM/Server replay. |
| Own and join admissions without handler history | Joined workers can leave self-purged or failed-handshake handlers pending outside the map. Initialized model counterexamples retain both cases. |
| Join handlers only on failure/query | Successful admission followed by self-purge bypasses that join. |

The combined model proves endpoint quiescence: at completed teardown, admission workers are joined and every physical handler has a result, including historical registrations. It excludes late admission/fork at shutdown boundaries. These are safety guarantees **if those boundaries are reached**, not eventual-shutdown theorems. [ServerOwnedHandlers properties](Properties/ServerOwnedHandlers.agda) state `quiescence`, `historical-quiescence`, `no-late-admission` and `no-late-fork`, under explicit initialization and variant-execution premises. The no-outbound-frame theorem belongs separately to [OwnedCallers](Properties/OwnedCallers.agda).

### Prototype result and progress conditions

The 16 November [production prototype patch](SourceReplay/QuiescentShutdownPrototype.patch) changes six files: 695 additions/28 deletions, including only 60 additions/27 deletions in production code. It retains the old snapshot finalizer and handler masking/TIME_WAIT behavior; admission joins run inside the IG callback. History is retained until CM exit, without an early reclamation policy.

All eleven original defect/control properties reproduce on pristine production code; four positive quiescence assertions fail there. The prototype passes eighteen IOSim checks, including full Server self-purge, rollback, five teardown routes, and POR at 20,000/20 bounds with 597 schedules per property. Four checks deliberately confirm failed progress. Existing coverage passes 37 properties at 100 cases and IG-race at 10; IG-race at 100 hits the same 60-second limit on baseline and prototype. These are recorded results, not checks rerun for this documentation update. [DesignContract](DesignContract.md#prototype-result) and the [prototype replay record](SourceReplay/README.md#quiescent-shutdown-prototype-increment-100) give the exact scope.

Progress still requires terminal handshake publication or recovery, terminating notification after IG exit, scheduled workers, released map leases, and terminating callbacks/handler cleanup. The prototype deadlocks with permanently blocked cleanup, an unpublished promise, or 101 late producers filling IG's [capacity-100 queue][queue] after its exit. Normal placement lets IG consume during joins; it does not solve IG-first teardown. A watchdog must report failure, not bypass waits and declare quiescence. Publication and notification progress obligations therefore remain unsatisfied.

## 6. Next steps

Discuss the prototype upstream as a concrete ownership fix with conditional progress. Decide terminal-promise recovery and IG notification/drain policy first, then add positive progress controls and check shutdown ordering against the model. Agree callback termination contracts and historical-handle reclamation requirements.

Complete dedicated physical-result tests for remaining detachments: outbound failure/query/alias paths, pruning/replacement, TIME_WAIT tails, fork failures and multiple listeners. Preserve unpatched controls and the unconfirmed classification of the combined late-admission race. Revalidate the historical IG wedge separately before extending its source-version claim. Broader application coverage, full source refinement and universal progress remain distinct obligations beyond the accepted finite gates.

## 7. Pointers

- [Verified properties summary](../review/connection-management-verified-properties-summary.md): positive results, exact evidence kinds and premises.
- [Identified issues summary](../review/connection-management-identified-issues-summary.md): every finding, revision and classification.
- [November architecture review](../review/connection-management-architecture-review-2026-11.md): source mapping, runtime assembly and semantic/exploration boundaries.
- [DesignContract](DesignContract.md): recommendation, rejected alternatives, proof scope, progress obligations and prototype.
- [GateAudit](GateAudit.md): G0–G5 acceptance scopes and remaining obligations.
- [SourceReplay README](SourceReplay/README.md): patches, source controls, reproduction instructions, schedules and exclusions.
- [SourceLedger](SourceLedger.md), [BranchMatrix](BranchMatrix.md) and [Exploration README](Exploration/README.md): operation mapping, profile coverage and checked search/shrinking guarantees.

[bundle]: https://github.com/IntersectMBO/ouroboros-consensus/blob/2e44d98a843168ba3b189e305820b79943ac7d1e/ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/Network/NodeToNode.hs#L1963-L2100
[start-init]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerStateActions.hs#L1180-L1198
[start-resp]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor.hs#L777-L795
[open-old]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1264-L1832
[open-current]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1392-L1832
[release-old]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1903-L1939
[release-current]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1903-L1939
[publication-old]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionHandler.hs#L324-L455
[publication-current]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionHandler.hs#L379-L518
[promise-read]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L895-L897
[wedge-callback]: https://github.com/IntersectMBO/ouroboros-network/blob/4b3ab7664f609a1aee0f0c24dcfcfd0ab899fc42/ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor.hs#L692-L699
[wedge-wait]: https://github.com/IntersectMBO/ouroboros-network/blob/4b3ab7664f609a1aee0f0c24dcfcfd0ab899fc42/ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor.hs#L397-L397
[owned-calls]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerStateActions.hs#L777-L1107
[release-in]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1107-L1260
[queue]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor/InformationChannel.hs#L35-L54
[shutdown]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L524-L550
[cleanup]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L606-L665
[workers]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/Server.hs#L239-L254
[scopes]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/Server.hs#L147-L186
[include]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L801-L880
[inbound]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L839-L879
[outbound]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1532-L1563
[restore]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L2373-L2379
[handler-finally]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L580-L713
[timewait]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L667-L668
