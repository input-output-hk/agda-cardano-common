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
| `Wire/ServerQuotient.agda` | Both exact standalone server source/wire inclusions and exhaustive source decision |
| `Wire/ServerTests.agda` | Source-language acceptance/rejection controls at both callback contracts |
| `Wire/ClientSound.agda`, `Wire/ClientComplete.agda`, `Wire/ClientQuotient.agda` | Both generic client initial source/wire inclusions and exhaustive decision with explicit Return inhabitant |
| `Wire/ClientTests.agda` | Single extra early reply, delayed Request Send, real Quit-marker drain, EOF and rejection controls |
| `WireNative.agda`, `WireServerNative.agda` | Declared deletion observation, exact native server realization and native wire decision |
| `WireServerNativeTests.agda` | Exact native normal/cancellation/EOF/fault witnesses and callback-contract separation |
| `Wire/ServerAdapter.agda`, `Wire/ServerAdapterTests.agda` | Lossless normalized server Msg mapping; located invalid-input versus exhaustive protocol verdicts |
| `Wire/ServerAdapterNative.agda`, `Wire/ServerAdapterNativeTests.agda` | Canonical summary-Params native realization/decision and payload/agency regressions |
| `DriverPrefixBoundsTests.agda` | Reachable delayed-hook regressions for exact commit/decode tallies and input-relative FIFO bounds |
| `ClientCallbackBasisTests.agda` | Finite unit-return callback targets for arbitrary signed depths and actual paired hidden moves |
| `BasisAdequacy.agda`, `BasisAdequacyTests.agda` | Whole-run payload renaming into an input-relative basis while fixing every recorded value |
| `UniqueBasisAdequacy.agda`, `UniqueBasisAdequacyTests.agda` | Duplicate-free candidate basis with membership equivalence, all-state transition/run transport and unchanged old retraction |
| `DriverUniqueTests.agda` | Actual repeated-exchange source/native witnesses, exact inner Votes refutations and representative/EOF gates |
| `LocalPrecheck.agda`, `LocalPrecheckTests.agda` | Necessary exact local quotient languages derived from existing source projections |
| `PacketPrecheck.agda`, `PacketPrecheckTests.agda` | Merge-independent common packet prefixes from exact channel conservation |
| `PacketCountPrecheck.agda`, `PacketCountPrecheckTests.agda` | Necessary receive lead of at most one pending Send in either direction, with unbounded queued Sends |
| `CreditPrecheck.agda`, `CreditPrecheckTests.agda` | Recorded client replies require recorded server Request credit, including replies with pending Send hooks |
| `ShutdownPrecheck.agda`, `ShutdownPrecheckTests.agda` | Recorded client Done requires server Quit Receive, preserving a pending Send-Done hook |
| `DriverPrecheckTests.agda`, `DriverCreditPrecheckTests.agda` | Guard-specific refutations, actual Lead witnesses and histories passing necessary guards but requiring complete search |
| `DriverShutdownPrecheckTests.agda` | Fifth-guard integration, explicit pending Send-Done source witness and a five-guard ordering-cycle gate |
| `PrefixTransport.agda`, `PrefixTransportTests.agda` | Exact conservation-derived receive bounds at every visible source prefix, with cut lemmas |
| `CycleObstruction.agda`, `CycleObstructionTests.agda` | Kernel prefix-cut obstruction and source refutation for the whole n-at-least-three cycle family |
| `CycleObstructionNative.agda`, `CycleObstructionNativeTests.agda` | Existing native soundness transports the generic obstruction to all matching native PTree traces |
| `CostProbe.agda`, `CostProbeTests.agda`, `CostProbeMain.agda` | Separate diagnostic stages reuse production parsing/decisions, with common field forcing and distinct guard-only tags |
| `ReadyGateOrder.agda`, `ReadyGateOrderTests.agda` | Exact callback-enumeration fast path preserving proof-bearing menus, duplicates, priorities and target order |
| `MenuProbe.agda`, `MenuProbeTests.agda`, `MenuProbeMain.agda` | Internal basis/readiness/menu/order diagnostic with source anchors and explicitly arbitrary nonce states |
| `DriverBasisExecutionTests.agda` | All restricted hidden families, exact existing payloads and delayed-hook menu regressions |
| `DriverDecide.agda`, `DriverDecideTests.agda` | Exhaustive unrestricted source compatibility for two typed endpoint prefixes and all their merges |
| `DriverDecideNative.agda`, `DriverDecideNativeTests.agda` | Native paired realization/refutation, exact decoded rows and local endpoint witnesses |
| `WireClientNative.agda`, `WireClientNativeTests.agda` | Generic Params/Return standalone client wire transport for every actual native path |
| `Wire/ClientAdapter*.agda`, `Wire/PairedAdapter*.agda` | Lossless normalized client/paired source/native decisions and regression witnesses |
| `Wire/LoggerObservation.agda`, `Wire/LoggerObservationTests.agda` | Typed post-lexical logger tags/fields, lossless selected-row observation and exact adapter transport |
| `LookaheadReport.agda`, `LookaheadReportTests.agda` | Tagged normalized-input reports, parser/agency failures and original source-line diagnostics |
| `LookaheadMain.agda` | Dedicated stdlib IO CLI; typechecked/compiled separately from safe proof roots |
| `DriverSearchTests.agda` | Computed full normal/cancellation shutdown, delayed Send and exact payload rejection under the ordered search |
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
tracks raw observation/capture evidence and stronger node-profile work.
The source audit also holds the T5.3 classification and resource-candidate
decision. The typed paired engine below completes its generic search scope;
Normalized profile/CLI delivery is implemented below; raw fidelity remains open.

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
increase. The [T6.3.2 review bundle](tools/patches/collect-one/README.md) is now
source/apply checked. No new runtime capture realization, arbitrary-log CLI mode
or raw-node-log verdict is added by that proposal.

## Exact server wire replay

The protocol-side [Wire/Server](../../LeiosNotifyPipeLookahead/Wire/Server.agda)
has a deterministic transition relation and a decision procedure that recurses
on typed wire rows. [ServerQuotient](Wire/ServerQuotient.agda) proves exact
equivalence to the detailed fresh server source language for both `genericNext`
and `nodeNext`, with arbitrary exact notification values. Its `decide-source`
constructs a detailed source witness or refutes all matching internal schedules;
there is no fuel cutoff or finite notification basis.

[WireServerNative.For.decide](WireServerNative.agda) transports this decision
to actual native PTree wire prefixes, through [WireNative](WireNative.agda).
The native witness retains callback API events before projection. The theorem
fixes Params/link/direction, excludes termination ticks, and treats EOF as a
prefix even with outstanding requests. `nodeNext` constrains reply kinds,
without adding NodeModel credit/FIFO or paired client-policy evidence.

Timestamp/length metadata and raw payload parsing remain outside this decision.
The generic client source quotient and normalized server adapter below are
separate results. Optional wire bounds and raw observation correctness remain open.
The normalized server adapter below now implements its own validation.
Unsupported or malformed raw rows must not be silently erased. See the
[implemented design scope](../../../../docs/specs/leiosnotify-lookahead-replay-design.md#implemented-server-wire-checking)
and [integration record](tools/results-parallel-20261105.json).

Reproduce the safe regression roots serially from the repository root:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/check_agda.py \
  Cardano_network/Replay/LeiosNotifyPipeLookahead/Wire/ServerTests.agda \
  Cardano_network/Replay/LeiosNotifyPipeLookahead/WireServerNativeTests.agda \
  --out /tmp/leiosnotify-server-wire-check
```

The final check freshly regenerates only the six new module interfaces and
reuses unchanged dependencies. Both roots pass; strict audit of the six files
finds no holes/unsafe additions. Peak sampled process RSS is about 1.1 GiB,
under the existing serial resource guards; this does not prove every future
Agda workload stays within memory.

The [capture audit](tools/capture-audit/README.md) finds zero Notify RequestNext
records in both requested logs and two nearby alternatives. Build provenance
is unknown. This is missing evidence for fresh replay, not a protocol rejection;
no fresh capture or T8.2 replay verdict is claimed.

### Normalized server input adapter

[ServerAdapter](Wire/ServerAdapter.agda) accepts a declared role and ordered
parser outcomes `List (Maybe LeiosNotifySession.E)`. It validates server agency
and every input position. A failed parse/unsupported row or wrong direction
produces a located invalid-input result; no row is dropped. Successful mapping
roundtrips exactly, including absent announcement metadata and ordered duplicate
votes. Its verdict distinguishes invalid input from exhaustive source-language
rejection and acceptance with a detailed source witness.

[ServerAdapterNative](Wire/ServerAdapterNative.agda) additionally realizes or
refutes matching native traces at the explicit summary `exactParams` instance
and fixed link/direction. These are existential canonical realizations of the
typed summary schema, not a proof that arbitrary deployed raw/native events
have been parsed correctly. Lexical/field validation stays with the parser;
timestamps, envelope length, full bodies and signatures are outside the schema.
Failure positions are input indices, not original file/thread coordinates.

This completes T7.3.2.1's normalized server adapter scope. Raw observation
correspondence and capture completeness remain open. The client/paired adapters,
profiles and dedicated CLI are now implemented below. See the
[task breakdown](../../../../docs/specs/leiosnotify-pipe-lookahead-plan.md#remaining-work-and-parallel-waves-after-2eeb5111).

## Generic client source replay

[ClientQuotient](Wire/ClientQuotient.agda) connects the protocol-side
[Wire/Client](../../LeiosNotifyPipeLookahead/Wire/Client.agda) to actual
`ClientModel.Run` prefixes after erasing only continue/terminate/handled
callbacks. It preserves exact normal/Canceled values and the source's
receiver-before-Send ordering. `Lead` permits one extra reply before its delayed
Request Send; EOF there is a prefix, while another extra reply or Quit is rejected.

`source→quotient` is generic in Notification and Return. `quotient→source`,
`equivalence` and `decide-source` explicitly take a Return inhabitant; the
regressions use unit. Completeness constructs a source schedule with permissible
generic dynamic depths, real collection operations and the actual dummy Quit
receiver. Rejection excludes every matching initial client source schedule.
This proves language equivalence, not final-state bisimulation or a depth-1000
node-policy witness. [WireClientNative](WireClientNative.agda) now lifts this
quotient to every actual native path, allowing arbitrary final trees and
explicitly erasing callback/API observations. Params and Return stay generic;
decision takes a real Return inhabitant. Normalized adapters below use unit.
See the [client source record](Wire/result-client-20261105.json) and
[native record](tools/result-client-native-20261105.json).

## Parallel replay prerequisites

The [input-prefix bounds and callback-target design](../../../../docs/specs/leiosnotify-lookahead-replay-design.md#checked-prefix-bounds-and-callback-targets)
links exact physical hook/FIFO count proofs and finite unit-return callback
enumeration. These support future paired search without assuming unique hidden
successors. The [wave record](tools/results-replay-wave2-20261105.json) retains
the combined fresh checks of 14 new modules, strict audit and scoped remaining
work. The following wave supplies packet adequacy, complete menus and their
paired decision integration; no raw-log verdict follows from those proofs alone.

## Typed paired driver replay

[DriverDecide](DriverDecide.agda) decides compatibility of two typed endpoint
prefixes with the original detailed `DriverModel`. `SourceTrace` existentially
quantifies an order-preserving merge and actual fresh source run. Acceptance
constructs both; rejection refutes every source schedule and permitted merge.
It preserves exact observed values, local order, pending Send/Receive records
and prefix EOF. Inputs are distinct protocol-side client/server row types from
[DriverRows](../../LeiosNotifyPipeLookahead/DriverRows.agda).

The checker takes Notification equality, an explicit normal representative and
the server `genericNext`/`nodeNext` contract. Return is unit and client callbacks
use the generic successful contract. A finite basis is fixed from both complete
inputs before search; [BasisAdequacy](BasisAdequacy.agda) proves that no matching
original execution is lost. Complete restricted menus and existing hidden
accessibility feed the generic [two-list decider](../../../Semantics/Replay/TwoListDecide.agda).
There is no guessed queue cap, fuel cutoff, state equality or finite global
state graph. Termination does not establish practical cost on large captures;
resource exhaustion remains inconclusive.

[DriverDecideNative.At](DriverDecideNative.agda) additionally decides existential
native paired PTree realizability at fixed Params and endpoint coordinates.
It produces exact canonical packet witnesses and the existing local native
endpoint realizations; native-to-source soundness covers every actual trace in
that product. Its normal representative is `votes []`. This does not validate
a supplied physical event list, arbitrary envelope metadata or the fixed node
credit/queue/client policy. Normalized adapters, manifests and the dedicated CLI
now implement the delivery path below; raw fidelity remains separate.

The [maintained design](../../../../docs/specs/leiosnotify-lookahead-replay-design.md#certified-paired-source-and-native-decision)
and [wave record](tools/results-replay-wave3-20261105.json) retain exact theorem
scopes, computed small decisions, delayed-Send witness roundtrips and final
checks. No new real capture or raw-log verdict is claimed.

## Normalized input and CLI delivery

[Wire/ClientAdapter](Wire/ClientAdapter.agda) and
[Wire/PairedAdapter](Wire/PairedAdapter.agda) preserve every parser-outcome
position and exact normalized summary value. Client mapping reuses server
payload encoding with an agency flip. Exact roundtrips, no row loss and mapping
uniqueness connect their decisions to the existing source languages; native
wrappers supply both directions and exhaustive native rejection. Wrong role,
agency and unparsed/unsupported input remain distinct from protocol rejection.
Typed-summary exactness does not prove raw-log parsing or deployed fidelity.

The separate compiled [LookaheadMain](LookaheadMain.agda) accepts these forms:

```text
LookaheadMain --notify-lookahead FILE --role client|server
  --next-contract generic-next|node-next --observation driver-log --assume-fresh
LookaheadMain --paired-notify-lookahead PAIR
  --next-contract generic-next|node-next --observation driver-log --assume-fresh
```

Use the shown order. Local input has a `role client`/`role server` header and
existing normalized Notify events; paired input uses the existing `pair
LeiosNotifyP ...` format and original positive source lines. This profile has
generic successful client callbacks and unit return, without a depth cap.
Server contract is explicit and unused by the standalone client. Legacy
`Replay/Main.agda` modes keep their original targets.

Prefer the [manifest runner](tools/replay_lookahead.py), which validates
[profile declarations](tools/profiles/README.md), artifact hashes and normalized
rows/source maps before invoking an explicit binary. It preserves local order,
duplicates, declared endpoint identity/generation and original source lines,
without inferring a timestamp merge or authenticating the raw capture. Unknown
deployed provenance remains unknown. Required fresh/ordered/lossless statements
are assertions, not established facts. Raw sources are only hashed.

| Runner exit | Result |
| --- | --- |
| 0 | Accepted model prefix |
| 1 | Exhaustive protocol rejection under the declared profile |
| 2 | Invalid manifest/artifact/normalized input |
| 3 | Missing required capture assertions |
| 4 | Resource limit, checker failure or another inconclusive execution |

The direct CLI emits a first-line verdict tag and exits 0/1/2 for completed
reports. A stdlib IO exception may exit without a tag; exit code alone cannot
establish protocol rejection. The runner requires the matching tag and code,
kills timed-out checker groups, bounds normalized reads/output/heap, and keeps
timeouts or heap exhaustion inconclusive. Successful EOF is always a prefix,
not proof of closure. Whole-prefix rejection reports no invented minimal index.

The [build/run guide](tools/README.md#normalized-lookahead-cli-and-manifest-runner)
and [wave record](tools/results-replay-wave4-20261105.json) retain commands,
12 fresh safe proof/report checks, the separate IO entry-point build, 62 real
CLI regressions and 10 real-binary manifest smoke cases. Tests use synthetic
normalized inputs; no complete real capture or deployment-conformance verdict
is added. Formal raw/logger correspondence remains open; the subsequent
executable raw/artifact check is described below.

## Typed logger-schema observation

[Wire/LoggerObservation](Wire/LoggerObservation.agda) models the supported
post-lexical logger schema before it becomes `LeiosNotifySession.E`. Namespace
direction and message tag, `data.kind` direction and message fields are
independent inputs, so contradictions can be rejected. Both RequestNext namespace
spellings are supported. Announcement metadata must be all absent or all present;
Votes retain their decoded hashes, voter IDs, order and duplicates.

`normalize-faithful` and its converse characterize successful normalization by
tag/direction agreement and exact retained fields. `input` uses `map normalize`,
so an invalid selected hook stays `nothing` at its original position. The
universe-polymorphic `Mapped` relation proves successful observation preserves
length, order and unique outputs, with reusable reconstruction and post-mapping
lemmas. Existing client/server adaptation also preserves the role derived from
direction and message agency. A wrong-role hook cannot silently adapt.

Client, server and paired acceptance transport in both directions through this
explicit observation relation, preserving the original callback contract and
both local orders. [The tests](Wire/LoggerObservationTests.agda) include exact
duplicate Votes, optional/partial metadata, inconsistent tags/directions,
invalid-position retention, wrong-role rejection and an inhabited idle-close
paired acceptance.

This is a theorem about typed selected hooks with already decoded fields. It
does not verify JSON/UTF-8/hex parsing, the Python implementation, file/thread
coordinates, physical logger emission or capture freshness. Unrelated file rows
and Serialised observations are outside this selected-hook alphabet. The
executable supplied-file checks below remain a separate boundary.

## Raw input correspondence and capture preflight

The [capture preflight guide](tools/capture-preflight/README.md) diagnoses the
missing RequestNext/Votes evidence and records four explicit Silence overrides
in an inspected local testnet configuration. Its configuration fragment is
unapplied; use by the historical deployment is unknown. Preflight inventories
request hooks and observed NewMux boundaries, never issuing a protocol verdict
or certifying capture completeness. Fresh acquisition and provenance remain
outstanding.

The [strict raw helper](tools/raw-input/README.md) validates driver-hook records,
reuses the existing Notify summary encoding, and writes a selected local trace,
legacy source-line map and detailed byte/thread map. It preserves exact selected
order and duplicates, including vote order. Host, literal connection, role,
observed NewMux generation and after-Done segment are selected explicitly.
Malformed or unknown driver-hook records fail before endpoint filtering;
Serialised observations are excluded explicitly and counted separately.
Missing metadata remains missing, and observed boundaries do not prove freshness.

The opt-in [raw replay coordinator](tools/replay_raw_lookahead.py) rederives all
three artifacts from the supplied raw bytes, then calls the unchanged manifest
runner. Its separate [bindings example](tools/raw-replay-bindings.example.json)
names selectors and detailed maps; raw/local/source-map paths still come from
the existing replay manifest. It watches file identity/size/mtime/ctime across
verification and execution. Artifact mismatch is invalid input, while mutation
or resource exhaustion is inconclusive. These checks are not authentication or
a filesystem transaction. Python and physical logger correspondence remain
trust boundaries; no new Agda raw-parser or implementation theorem is claimed.

The [cost measurements](tools/replay-cost/README.md) reuse the existing compiled
baseline checker on synthetic schedules: 86 cases accepted, three paired cases timed out
and 16 larger cases were explicitly not run. Local checks through 64 exchanges
were inexpensive, but even some one-exchange normal closed pairs exceeded five
seconds. Run local checks first and retain limits for paired search. An accepted
shorter prefix never substitutes for an inconclusive full history. The
[wave record](tools/results-replay-wave5-20261105.json) retains source identities,
runtime controls, real-binary synthetic smoke checks and the strict original-log
preflight; it contains no new complete-testnet replay verdict.

## Certified input-dependent search ordering

[DriverSearchOrder](../../LeiosNotifyPipeLookahead/DriverSearchOrder.agda) assigns
priorities using the remaining endpoint rows and stably sorts the existing
proof-bearing hidden moves. It favors matching payload/transport, useful
housekeeping and termination when Quit is next. Every original move remains,
including fault, speculative continuation and unmatched callback alternatives.
The all-state soundness/completeness lemmas refer to the same basis-restricted
relation for every contract and input suffix; no search heuristic is installed
as a new protocol policy.

The generic [OrderedDecider](../../../Semantics/Replay/TwoListDecide.agda) requires
these facts and the existing hidden accessibility certificate. Its original
`Decider` interface transparently keeps its prior order. `DriverDecide` now uses
the ordered instance while retaining the same whole-input basis/adequacy and
unrestricted `SourceTrace`. Acceptance still constructs one original execution;
rejection still refutes every source schedule and permitted merge. Native
transport and normalized/raw interfaces keep the same premises and meanings.

The [comparison and scale record](tools/search-order/README.md) supersedes the
baseline timeout findings for its retained fixtures. Full normal closed one-
exchange and four-request cancellation histories change from five-second
timeouts to approximately 15 ms acceptance. All 84 original scale cases and
21 follow-up cases complete through 64 exchanges; one already-fast open-prefix
measurement is slightly slower, so there is no universal improvement claim.
Quit/Done, exact payloads, negative controls and EOF races remain checked. Six
changed/new Agda sources have safe checks and a resolved source audit; the
[wave-6 record](tools/results-replay-wave6-20261105.json) retains build identities,
62 CLI regressions and three raw-input real-binary smokes. Fresh acquisition is
outside the active work at the user's request.

## Unique payload basis and rejection limits

[UniqueBasisAdequacy](UniqueBasisAdequacy.agda) uses standard-library
deduplication on the original complete-input candidate list. Every original
normal value remains permitted and no new value is introduced. Its all-state
hidden step/run transports preserve identical source/target states and exact
visible labels in both directions, for arbitrary Notification and Return. Fresh
source adequacy reuses the unchanged old retraction and its computation gates.
`DriverDecide` switches only that adequacy import; the public unrestricted
`SourceTrace` and native bridge premises remain unchanged.

This deduplicates whole callback candidate values. Repeated log rows and duplicate
Votes inside a single payload remain exact. The
[independent regression guide](tools/basis-regressions/README.md) links a
parametric actual two-exchange source witness under both contracts, retaining
eight visible records and native realization. It demonstrates five candidates
becoming one when the representative equals that repeated whole payload. Direct
packet-conservation proofs exclude trimming or reordering its internal Votes,
independently of the search result. All 18 identical runtime fixtures match on
the old and new binaries: 14 accepted prefixes and four completed rejections.

The [unique-basis baseline study](tools/rejection-cost/README.md) deliberately separates
completed controls from resource limits. Of 72 prepared cases per binary, nine
controls complete as expected, nine negative series stop at size one with a
two-second timeout, and 54 larger cases are not run. Those nine timeouts contain
six distinct byte sequences; no growth or repeated-versus-distinct conclusion
is established. Deduplication does not solve these closed-negative cases.

The rebuilt checker also passes the original 105 positive scale/follow-up
checks, 62 CLI regressions and three raw-input smoke cases. A repeated normal
64-exchange pair takes about 44 ms in this run versus about 125 ms in the prior
ordered-binary run; cancellation remains about 34 ms. These are single synthetic
measurements, not universal speedup or deployment claims. The
[wave-7 record](tools/results-replay-wave7-20261105.json) retains source/build
identities, proof checks and limits. The subsequent proved necessary prechecks
below resolve the retained negative cases without changing the source language.

## Proved necessary prechecks

The public paired decision now checks five necessary conditions before using
the original complete search:

1. [LocalPrecheck](LocalPrecheck.agda) projects an actual source run to the
   existing client/server sources and their proved exact wire quotients. All
   typed rows and complete payload values are retained in their local order.
2. [PacketPrecheck](PacketPrecheck.agda) proves that recorded Send/Receive lists
   agree at every common packet position. Merge-independent histories and
   original channel conservation justify this for both directions; unmatched
   suffixes remain allowed.
3. [PacketCountPrecheck](PacketCountPrecheck.agda) proves that recorded receives
   can exceed peer recorded sends by at most one, independently per direction.
   That one is the actual pending Send hook. Pending Receive/FIFO suffixes remain
   present, and queued Sends can exceed Receives arbitrarily.
4. [CreditPrecheck](CreditPrecheck.agda) proves that recorded client normal or
   Canceled replies cannot outnumber recorded server Request receives. It reuses
   exact server accounting, packet conservation and the pending server Send
   invariant. A committed reply with its Send hook pending still consumes actual
   request credit. Quit and Done contribute no reply credit.
5. [ShutdownPrecheck](ShutdownPrecheck.agda) proves that a recorded client Done
   Receive requires a recorded server Quit Receive. The physical Done-origin
   invariant and ordinary pre-Quit reader phases justify this for every original
   fresh run. The server's Send-Done hook may still be pending; no strict
   recorded-Send-first requirement is added.

Each necessity theorem takes the same unrestricted initial `DriverModel.Run`
and exact `DriverRows.Merge`. No guard adds source/capture premises, an inhabited
Return assumption, or a protocol policy. Equality is needed only for deciding
exact packet compatibility. `DriverDecide.precheck-necessary` retains the original
three conditions; `full-precheck-necessary` adds reply credit, and
`all-precheck-necessary` adds shutdown origin. In each case
a failure refutes the unchanged `SourceTrace`. All-guard success still calls the
byte-unchanged `For.check` source-search module and its existing unique-basis
adequacy/accessibility. Native transport retains its previous target/premises.

[DriverPrecheckTests](DriverPrecheckTests.agda) supplies actual source Lead
acceptance, distinct guard failures and both forms of insufficiency. The local
and packet-prefix pair can pass an impossible excessive-receive input, which
the count guard now refutes. All three earlier guards pass a client reply with
no server records; the new credit guard now refutes it directly.
[DriverCreditPrecheckTests](DriverCreditPrecheckTests.agda) retains a further
counterexample: client `Send Quit, Recv Done`, server empty. All four earlier
guards pass, but the server cannot commit Done without recording Quit. The fifth
guard now refutes that input directly; the complete backend independently rejects
it. [DriverShutdownPrecheckTests](DriverShutdownPrecheckTests.agda) preserves an
explicit actual source witness with client Done already recorded and server
Send-Done still pending, under both callback contracts in the component tests.
Public replay also accepts that unfinished final hook and ordinary idle close.

The same integration tests prove all five predicates pass a different input:
the client alternates three early reply Receives with Request Sends, while the
server records all three Request Receives before its first Reply Send. A
source-reviewed ordering-cycle argument first identified this incompatibility:
single pending Send slots create mutually dependent operations.
The original kernel gate proves guard success; the later general
[prefix obstruction](#prefix-transport-and-kernel-cycle-obstruction) now refutes
the source family at every size at least three. A separate compiled probe accepts the feasible
two-round control and exhaustively rejects the three/four-round inputs in about
one second each. The general theorem is supplied by the later prefix proof,
independently of those concrete runtime results. The public checker still calls complete search after all five
guards pass, and guard success never replaces a paired source witness.

The [regression guide](tools/precheck/README.md) retains an initial prefix-only
274-case run with one unexpected count-deficit timeout, its exact source snapshot
and nonzero result. After adding the proved count guard, the same 274 input bytes,
checker flags, expected statuses and diagnostics all match. The 72-case rejection
matrix now completes through size 64; its slowest measured case is about 25 ms.
The extra three-Receives/one-Send case changes from a two-second timeout to about
13 ms rejection. Valid one-pending-Send races in both directions, normal after
Quit, both callback contracts, exact inner Votes and all prior positive/CLI
controls remain checked. The deliberately missing-file CLI case remains
inconclusive. The [wave-8 record](tools/results-replay-wave8-20261105.json) retains
proof/build/source identities and operational bounds. These synthetic results
are not universal tractability, logger fidelity or implementation refinement.

The subsequent [83-case stress comparison](tools/search-stress/README.md) fixes
77 distinct inputs before measuring the three-guard and request-credit binaries.
All 26 orphan-reply negatives through 128 preceding exchanges now reject in
about 13–44 ms; 24 were previously timed out or unrun. The one-exchange orphan
Done still times out, with larger members unrun. Two large positive cases also
cross the two-second ceiling after completing near that limit in the baseline;
the study retains that performance qualification. All 274 original regression
expectations still match on the new binary. Separate matched probes of those
two large positives accept in all 12 runs below two seconds, using an explicit
five-second ceiling; they do not replace the original two timeouts. The
[wave-9 record](tools/results-replay-wave9-20261105.json) retains the safe checks,
typed logger-schema evidence, build and bounded runtime identities. This is
additional necessary refutation, not a general tractability result.

The [shutdown continuation](tools/shutdown-stress/README.md) preserves the same
83 stress inputs and budgets. All 35 negative cases now complete, including all
nine orphan-Done sizes through 128 preceding exchanges; eight were previously
inconclusive or unrun. The full result is 30 accepted prefixes, 35 rejections,
seven positive timeouts and 11 skipped larger positives. No completed verdict
disagrees with its expectation, and all 274 original regressions still match.
The separate cycle probe preserves the distinction between the kernel guard
gate, reviewed causal explanation and concrete compiled refutations. The
[wave-10 record](tools/results-replay-wave10-20261105.json) retains proof/build
identities, independent review and exact operational limits. No changes to guard
order or successor menus are justified by the earlier matched timing evidence.

## Prefix transport and kernel cycle obstruction

[PrefixTransport](PrefixTransport.agda) derives the receive-lead bounds at every
visible prefix of an original fresh run, retaining exact events and both packet
histories. Hidden steps preserve conservation without adding log rows. Its
`Bounded` certificate, `cut` and `source-prefix-bounds` reuse the existing packet
balance and one-pending-Send arithmetic; excess Sends remain unrestricted.

[CycleObstruction](CycleObstruction.agda) proves a stronger cut: a client prefix
`Recv, Send, Recv` cannot coexist with three initial server command Receives,
regardless of the message values or remaining tails. Before the first server
Send, a second client Receive would violate its one-packet lead. The server's
third Receive needs a second recorded client Send, which is beyond that blocked
client Receive. The proof checks the finite frontier cases rather than reducing
complete replay.

For client `(Recv normal a, Send RequestNext)^n` and server
`(Recv RequestNext)^n ++ (Send normal a)^n`, `no-source` therefore excludes every
matching original run whenever `3 ≤ n`. Notification, Return, payload and
callback contract remain generic. The tests combine this refutation with the
existing all-five-guard success controls at three/four rounds. The two-round
abstract prefix certificate is a boundary control, not a claim that prefix
bounds alone construct a source execution.

[CycleObstructionNative](CycleObstructionNative.agda) composes this theorem with
the existing native-to-source sound bridge. It excludes every matching actual
native PTree trace at the supplied Params/contract/link/direction coordinates;
no canonical-event-encoding premise is added. This remains a result about the
formal native model and its declared observation, not deployed Haskell fidelity.

The production verifier continues to use its five guards and complete backend.
The separate [cost diagnostic](tools/cost-profile/README.md) invokes its actual
parser, adapters, guard and decision functions in explicit stages. A common
forcing pass visits all retained fields before each stage; guard success has a
distinct diagnostic tag and is never reported as protocol acceptance. Timings
include shared decoding/forcing/startup and do not give exact additive stage
CPU times.

## Exact readiness enumeration

[ReadyGateOrder](ReadyGateOrder.agda) avoids traversing the callback alphabet
when the server sender is not `claimed`, or when its Quit flag is true. The old
lookup already returns no callback successor for every candidate in those
states. Claimed/false delegates to the original enumeration, including its
reader-active and callback-contract checks. This fast path does not exclude the
independent cancellation transition or a normal reply selected before Quit.

The theorem `readyMoves-exact` preserves the entire dependent list, including
transition certificates, for every state, contract and basis. Empty bases,
duplicate values and unreachable states are covered. Equality lifts through the
same eight-family concatenation and old stable score/sort to
`orderedTargets-exact`. Existing soundness and completeness transport along that
equality, with no new protocol or capture premise.

The [internal diagnostic](tools/menu-profile/README.md) compares actual raw and
gated readiness, menus and ordered targets on one forced production basis. Five
anchor states have explicit source witnesses; the reader-inactive/claimed
control and positive completed-counter perturbations are labeled arbitrary.
Whole-input ranking contexts are not asserted to be remaining suffixes of those
witnesses. Full-state forcing totals are collision-prone diagnostics, with no
source verdict. Source-level repetitions and generated-call evidence do not
establish a universal physical-call or anti-hoisting guarantee.

`DriverDecide` now selects this exact interface through one import; its source
predicate, five prechecks and search body are unchanged. Eight downstream safe
roots and all 274 expected regression outcomes pass. The fixed 20 positive
ordinary CLI inputs now all accept, including both prior distinct-512 timeouts.
Stress counts remain 35 rejections, 30 acceptances, seven timeouts and
11 skips; two deadline crossings cause two further run/skip changes. The three
cycle outcomes are unchanged. These are bounded samples,
not a universal search-time or OOM result. The
[wave-12 record](tools/results-replay-wave12-20261105.json) retains build,
proof, independent review and comparison evidence. Certificate extraction still
delegates to old `target-sound`, so this gate does not eliminate every possible
original-menu reconstruction.
