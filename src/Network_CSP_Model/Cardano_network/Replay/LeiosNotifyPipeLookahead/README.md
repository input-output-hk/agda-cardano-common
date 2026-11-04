# LeiosNotifyPipeLookahead replay bridges and validation

Protocol definitions and productive PTree constructors live in
[`Cardano_network/LeiosNotifyPipeLookahead/`](../../LeiosNotifyPipeLookahead/README.md).
The native entry point is
[`Cardano_network.LeiosNotifyPipeLookahead`](../../LeiosNotifyPipeLookahead.agda).
This directory consumes those models; the protocol modules do not import Replay.

The [`tools/`](tools/README.md) subdirectory contains the controlled Haskell
capture harness, Python certificate generator, bounded Agda checker and recorded
experiment results.

| Module | Purpose |
| --- | --- |
| `ClientBridge.agda` | Both finite trace directions between the independent client rules and its source-operation PTree |
| `DriverBridge.agda` | Both finite record-trace directions for the generic paired driver prefix tree |
| `ServerEventsBridge.agda` | Roundtrip native event realization and exact-action injectivity at every endpoint |
| `ServerBridge.agda` | Both native `LNPEv` step/trace directions, return classification and native shutdown guards |
| `ServerBridgeTests.agda` | Exact-field native notification/shutdown/fault witnesses and negative controls |
| `ClientEventsBridge.agda` | Explicit visible/erased action partition and exact retained-payload realization |
| `ClientNetworkBridge.agda` | Both native client step/trace directions with declared callback erasure and exact return value |
| `ClientNetworkTests.agda` | Native receiver/Send races, post-Quit handling, cancellation drain and callback visibility controls |
| `DriverEventsBridge.agda` | Canonical full-packet native paired record roundtrip and injectivity |
| `DriverNetworkBridge.agda` | Both finite native paired step/trace directions against the independent driver product |
| `DriverEndpointBridge.agda` | Actual local native client/server executions and matching wire projections for each product run |
| `DriverNetworkTests.agda` | Delayed Sends, Canceled/normal-after-Quit shutdown, endpoint witnesses and FIFO/pending-record controls |
| `NodeDriverBridge.agda` | One-way native paired/endpoint realization of combined production node-policy runs |
| `NodeDriverTests.agda` | Fresh node-policy schedules with forecast/termination inputs, exact credit/queue transactions and shutdown |
| `ExportFixtures.agda` | Pure TSV rendering of four checked node wire histories, evaluated by Agda DefaultCompute for controlled Haskell comparison |
| `RuntimeCheck.agda` | Sound interpretation of supplied finite schedules at the independent node-policy rules; no exhaustive search claim |
| `RuntimeCheckTests.agda` | Seven negative controls for forecast, callback bypass, admission, empty queue, commit, selector and FIFO guards |
| `RuntimeCertificates.agda` | Concatenation of checked runs with exact wire equalities, plus server-only policy-to-core projection |
| `RuntimeInstance.agda` | Shared exact model and native bridge instance for generated runtime certificates |
| `ConservationBridge.agda` | Universal native paired finite-trace FIFO and server request/reply accounting through actual source inversion |
| `ConservationTests.agda` | Reachable delayed-Send/fault/cancellation controls, phantom/swapped/duplicated packet exclusions and a refuted naive prefix equality |
| `ConservationNativeTests.agda` | Concrete node/native delayed-Send, Canceled and selected-normal-after-Quit instances of the general conservation endpoints |
| `ShutdownBridge.agda` | Native shutdown persistence, flag/new-selection guarantees and precise role-specific Done completion through actual step/trace inversion |
| `ShutdownTests.agda` | Fresh registered-job and both Done-ordering counterexamples, completion and no-new-request/normal-selection controls |
| `ShutdownNativeTests.agda` | Fresh production node/native Receive-Done before Send-Done, both-peer completed work, pending hook and native future no-request proofs |
| `SchedulingBridge.agda` | Constructive native hidden accessibility/divergence exclusion and bounds on actual shutdown LTS steps |
| `SchedulingTests.agda` | Fresh client drain budget, unretired-send state and arbitrary completion-token reachability controls |
| `SchedulingNativeTests.agda` | Native/node accessibility, reachable final-hook bound and an environment-stuttering scope counterexample |
| `ProgressBridge.agda` | Conditional source/runtime completion realized as actual native paths with native step bounds; structural progress stays explicit |
| `ProgressTests.agda` | Inhabited reachable handoff runtimes with arbitrary finite waiting; starvation, exception, premature EOF and malformed-state controls |
| `ProgressNativeTests.agda` | Actual fresh native Done handoff with concrete runtime premises, Receive-before-Send completion and bounded native continuations |
| `ServerDrainBridge.agda` | General fresh paired server completion realized as native continuations, native inversion and conditional runtime paths; no unproved structural server-progress premise |
| `ServerDrainTests.agda` | Fresh outstanding reply/Quit-marker example, ten-operation server drain, composed twenty-two-operation clean closure, client phase/reply accounting and invalid-slot controls |
| `ServerDrainNativeTests.agda` | Fresh source/native/runtime instances of the general server-drain endpoints |
| `PairedDrainBridge.agda` | General fresh full paired native continuations, exact native target inversion and given-runtime native completion with operation bounds |
| `RunRuntime.agda` | Constructed successful runtime schedules and inhabited response/no-failure/maximality witnesses for supplied finite example paths; no production fairness inference |
| `PairedDrainTests.agda` | General full completion/runtime/maximal endpoints, fresh delayed-Quit and held-handler examples, and unreachable missing-Done/dropped-reply/duplicate-Done controls |
| `PairedDrainNativeTests.agda` | Actual production-policy delayed Send-Quit/Send-Done ordering with full clean native/runtime closure |
| `CompletionBridge.agda` | Independently counted native hidden flushes, exact source-count correspondence, work conservation, successful-close/recorded-Done counts and native operation lower bounds |
| `CompletionTests.agda` | Universal idle/mixed/unretired counts, finite EOF control, all-state production-policy occupancy bounds and unbounded retained completions |
| `CompletionNativeTests.agda` | Arbitrarily long occupancy-one policy/native histories, exact n-flush and n+12-native-operation shutdowns, and closure from observed Send-Done |
| `Tests.agda`, `ClientTests.agda`, `DriverTests.agda`, `NodeTests.agda` | Inhabited source schedules and negative controls |
| `NativeTests.agda`, `NativeReachability.agda` | Native server PTree steps and constructive completed-bookkeeping reachability |
| `ClientNativeTests.agda`, `DriverNativeTests.agda` | Source-operation PTree witnesses and executable negative controls |

The source models, assumptions, findings and full validation record are documented
in the [protocol README](../../LeiosNotifyPipeLookahead/README.md). Pinned source
URLs and checksums are in its [`sources.json`](../../LeiosNotifyPipeLookahead/sources.json).

The server bridge retains readiness API events and the source model's abstract
admission outcomes. Its `realize` theorem supplies a native execution for every
source run. `sound` reconstructs a source run from every native finite execution.
The native client bridge keeps all wire records and normal API deliveries while
erasing the explicitly classified callback decisions and successful generic
Canceled handling. It retains the exact return value; the node-specific fault
policy remains a separate component. The native paired driver product now has
both trace directions and endpoint projection certificates. `NodeDriverModel`
now binds both node-policy components in the paired product and proves a one-way
native realization. The generic native target remains broader: its acceptance
alone does not certify a node-policy witness or the node's abnormal-exit outcome.
An exact policy PTree/inversion theorem, ordinary CSP/legacy-medium composition
equivalence, wider Haskell differential coverage/full node-callback validation
and certified wire/raw-log search remain separate
tasks in the [numbered plan](../../../../docs/specs/leiosnotify-pipe-lookahead-plan.md).

Run the validation roots from `src/`:

```sh
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/NativeTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/NativeReachability.agda
agda --safe Cardano_network/LeiosNotifyPipeLookahead/Rank.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/ClientTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/DriverTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/NodeTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/ClientNativeTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/DriverNativeTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/ServerBridgeTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/ClientNetworkTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/DriverNetworkTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/NodeDriverTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/ExportFixtures.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/RuntimeCheckTests.agda +RTS -M2G -RTS
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/RuntimeInstance.agda +RTS -M2G -RTS
```

The original eight roots and the native entry point passed after the directory refactor.
Logs and the exit-code manifest are in `/tmp/leiosnotify-lookahead-layering-20261103/`.
The new server bridge root and four relevant downstream roots passed with logs in
`/tmp/leiosnotify-lookahead-server-bridge-20261103/`.
The new client root and five relevant downstream roots passed with logs in
`/tmp/leiosnotify-lookahead-client-network-20261103/`.
The new paired driver root and five relevant downstream roots passed with logs in
`/tmp/leiosnotify-lookahead-driver-network-20261103/`.
The combined node-policy root, DriverNetworkTests, NodeTests and native entry
point passed with logs in `/tmp/leiosnotify-lookahead-node-policy-20261103/`.
The pure fixture exporter passes safe checking and normalization. The
[controlled Haskell harness](tools/README.md)
passes 80 experiments and all 40 applicable Agda wire-history comparisons;
the full artifact directory is `/tmp/leiosnotify-haskell-final-20261103/`.

T3.3's additional supplied-schedule certificates are produced by
[`certify.py`](tools/certify.py), which checks
small parts using `agda --safe`, proves their concatenation, and realizes the
exact original rows in the native paired or local-server tree. Its Python
planner is untrusted. Failure to find or check a supplied schedule is
inconclusive. It is not the proposed exhaustive wire-only/raw-log checker.
The [OOM diagnosis](../../../../docs/notes/leiosnotify-pipe-lookahead-oom.md)
describes the shared instance, abstract parts and bounded execution. Generated
sources and logs stay outside the repository.
All 40 additional captured histories passed through 22 distinct safely checked
certificates, bringing the total to 80: 70 paired histories and 10 server-only
adversarial histories. The [T3.3 result record](tools/results-t33-20261103.json)
ties the batch to its sources and artifacts under
`/var/tmp/leiosnotify-t33-20261103/verified/`. Peak sampled RSS was 1.15 GiB;
there were zero batch budget failures. The four helpers and all 1003 generated
Agda files pass strict proof scans with zero findings.

T4.1.1 now has general accounting theorems in the protocol layer:
`ServerConservation`, `DriverConservation` and `NodeConservation`.
`ConservationBridge` applies them to every actual fresh native paired finite
trace, with exact matching records and target state. Its two concrete checking
roots and the [bounded check wrapper](tools/check_agda.py)
are documented in the [conservation note](../../../../docs/notes/leiosnotify-pipe-lookahead-conservation.md).
T4.1.2 now has `ClientAccounting`, `ClientShutdown`, `ServerShutdown`,
`DoneOrigin`, `DriverShutdown` and `NodeShutdown` in the protocol layer, with
`ShutdownBridge` lifting the guarantees to actual native traces. Its nine
new modules pass safe checking and strict audits. The
[shutdown note](../../../../docs/notes/leiosnotify-pipe-lookahead-shutdown.md)
gives exact Done/registration conditions and fresh counterexamples. Broader
progress/resource results remain T4.2.2/T4.3. T4.2.1 now has universal paired/node
hidden accessibility, native divergence exclusion and conditional bounds on all
remaining shutdown operations. Its eight modules pass safe checking and strict
audits. The [scheduling note](../../../../docs/notes/leiosnotify-pipe-lookahead-scheduling.md)
states the precise native/projected-node operation counts and remaining progress
assumptions.

T4.2.2 now adds seven safely checked modules for conditional model/runtime
completion and concrete final-Done progress. `ProgressBridge` keeps the structural
invariant and runtime assumptions explicit. `ProgressTests` and
`ProgressNativeTests` are the bounded checking roots. The
[progress note](../../../../docs/notes/leiosnotify-pipe-lookahead-progress.md)
states the exact premises, inhabited examples and controls. General fresh paired
local progress through the preceding reply/marker drain remains T4.2.2.3;
unconditional implementation liveness is not claimed.

T4.2.2.3 now proves the general fresh paired server drain and supplies client
control/reply invariants. Its eight modules pass safe checking through
`ServerDrainTests.agda` and `ServerDrainNativeTests.agda`, with strict zero-finding
audits. The [server-drain note](../../../../docs/notes/leiosnotify-pipe-lookahead-server-drain.md)
distinguishes universal server closure from the remaining general client/packet/
Done connection and full paired completion (T4.2.2.3.3).

T4.2.2.3.3 now completes that full fresh structural-progress theorem using
`CommandFlow`, `ResponseFlow`, `ReplyLedger`, `ClientDrain` and `PairedDrain` in
the protocol layer. Its nine modules pass safe checking through
`PairedDrainTests.agda` and `PairedDrainNativeTests.agda`, with strict audits.
The [paired-drain note](../../../../docs/notes/leiosnotify-pipe-lookahead-paired-drain.md)
states exact endpoints and retained runtime/implementation assumptions. General
structural progress is proved; external responsiveness/failure conditions still
cannot be inferred from accepted finite logs. T4.3 resource results are recorded below.

T4.3.1 now completes exact bookkeeping/flush counts with six safely checked and
strictly audited modules. `CompletionAccounting`, `CompletionDriver` and
`SequentialCompletion` are in the protocol layer; `CompletionTests.agda` and
`CompletionNativeTests.agda` are the checking roots. The
[completion-cost note](../../../../docs/notes/leiosnotify-pipe-lookahead-completion-cost.md)
distinguishes universal counts and actual native step bounds from the selected
low-occupancy policy family, machine representation and measured runtime cost.
T4.3.2 resource and representation results follow below.

T4.3.2 adds `ClientBounds`, `ResourceBounds`, `QueueBudget`, `NodeQueueBounds`
and `Representation` in the protocol layer, with `ResourceFixtures` and
`ResourceNativeTests` under Replay. The seven modules pass safe checking and
strict audits. Every fresh fixed-depth policy run has conservative live-resource
envelopes; the full-pipe Quit witness needs one extra marker slot. Historical
server deferred jobs remain unbounded, so depth cannot discharge their finite
Int-range premise. Signed arrival-counter range remains a separate obligation.
See the [resource-bounds note](../../../../docs/notes/leiosnotify-pipe-lookahead-resource-bounds.md)
and [result record](tools/results-t432-20261104.json).

## Runtime investigation

The [completion-cost topic](../../../../docs/notes/leiosnotify-pipe-lookahead-completion-cost.md)
maintains T5.1.1 history counts, T5.1.2 quiet baseline profiles and T5.2.1 Nat
heap/arithmetic diagnostics. T5.2.2's [runtime profiles](../../../../docs/notes/leiosnotify-pipe-lookahead-progress.md#pinned-haskell-blocking-and-failure-experiments)
cover blocking, injected failures and credit/queue accounting. The topics link
committed records, reproduction commands and source pins, keeping runtime
outcomes distinct from model guarantees. These finite fixtures do not establish a verified repair, full
Haskell refinement or production-node severity.

The [source audit](../../../../docs/notes/leiosnotify-pipe-lookahead-source-audit.md#remaining-implementation-and-replay-obligations)
collects the remaining runtime, representation and replay obligations. The
[numbered plan](../../../../docs/specs/leiosnotify-pipe-lookahead-plan.md#t5-investigate-potential-implementation-problems)
tracks continuation at T6.3.2. The source audit also holds the
T5.3 classification and resource-candidate decision. Arbitrary-log lookahead checking remains T7;
source bridges and controlled-schedule certificates do not supply that checker.

The separate [CollectOne candidate design](../../../../docs/specs/leiosnotify-collect-one-design.md)
has compiled type/constructor feasibility and separate safe reference
[Model/Contract](../../../../docs/specs/leiosnotify-collect-one-design.md#t612-behavior-and-observation-contract)
definitions. Their witness/guard root is
[CollectOne/ContractTests.agda](CollectOne/ContractTests.agda).
[T6.2.1 preservation](../../../../docs/specs/leiosnotify-collect-one-design.md#t621-finite-source-and-wire-preservation)
now proves both finite local source-action and exact wire inclusions without
extra premises. [T6.2.2 conditional resources/progress](../../../../docs/specs/leiosnotify-collect-one-design.md#t622-conditional-resources-and-local-progress)
now prove B+1 registered inventory, exact early/final collection accounting,
shutdown safety, internal accessibility and finite local completion/operation
bounds. [CollectOne/ResourceTests.agda](CollectOne/ResourceTests.agda) has fresh
sequential, burst, selected-send and empty-Notification examples. The unfinished-work
premise is now discharged by [T6.2.2.3](../../../../docs/specs/leiosnotify-collect-one-design.md#t6223-paired-policy-resource-bounds)
for the independent candidate paired node model: ≤1005 registered/completed jobs.
[CollectOne/NodeResourceTests.agda](CollectOne/NodeResourceTests.agda) constructs
honest arbitrary-length paired histories, real hits/misses, delayed hooks and
full endpoint closure. Candidate native/converse paired/Haskell correspondence
remain open. [T6.3.1 actual-driver comparison](../../../../docs/notes/leiosnotify-pipe-lookahead-completion-cost.md#collectone-actual-driver-comparison)
now passes fresh baseline/candidate schedules, histories and quiet profiles
(1224 processes), with reduced retention/shutdown cost and a small allocation
increase. T6.3.2 patch review is next. No new Agda capture realization, arbitrary-log
mode or raw-node-log verdict is added.
