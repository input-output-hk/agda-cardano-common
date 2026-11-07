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
| `ReadyGateOrder.agda`, `ReadyGateOrderTests.agda` | Exact callback-enumeration fast path preserving proof-bearing menus, duplicates, priorities and target order |
| `DriverBasisExecutionTests.agda` | All restricted hidden families, exact existing payloads and delayed-hook menu regressions |
| `DriverDecide.agda`, `DriverDecideTests.agda` | Exhaustive unrestricted source compatibility for two typed endpoint prefixes and all their merges |
| `DriverDecideNative.agda`, `DriverDecideNativeTests.agda` | Native paired realization/refutation, exact decoded rows and local endpoint witnesses |
| `WireClientNative.agda`, `WireClientNativeTests.agda` | Generic Params/Return standalone client wire transport for every actual native path |
| `Wire/ClientAdapter*.agda`, `Wire/PairedAdapter*.agda` | Lossless normalized client/paired source/native decisions and regression witnesses |
| `Cardano_network.LeiosNotifyPipeLookahead.NodeClientExecution`, `NodeClientExecutionTests.agda` | Exact existing node-policy selectors and finite scheduling menus; fixed depth and Cancel fault guards |
| `Wire/NodeClientPolicy.agda`, `Wire/NodeClientPolicyTests.agda` | Finite adequate hidden callbacks, inherited accessibility, exact independent source-language equivalence and exhaustive local policy decision |
| `Wire/NodeClientAdapter.agda`, `NodeClientReport.agda`, `NodeClientReportTests.agda` | Existing lossless normalized fields/agency validation with a separate policy witness, explicit local profile and located errors |
| `Wire/LoggerObservation.agda`, `Wire/LoggerObservationTests.agda` | Typed post-lexical logger tags/fields, lossless selected-row observation and exact adapter transport |
| `LookaheadReport.agda`, `LookaheadReportTests.agda` | Tagged normalized-input reports, parser/agency failures and original source-line diagnostics; silenced local/paired reports and the `undetermined` status |
| `LookaheadMain.agda` | Dedicated stdlib IO CLI; typechecked/compiled separately from safe proof roots |
| `Wire/ServerSilencedTests.agda`, `Wire/ClientSilencedTests.agda` | Concrete decisions of the protocol-layer silenced server/client languages, including hidden-row rejection and the client `Lead` abstraction |
| `Silenced.agda` | The `driver-log-no-request-votes` hidden predicates `isVotes` and `hiddenKind` (RequestNext/Votes in either direction) |
| `WireSilencedNative.agda` | Server/client `equivalence` between each silenced local language and native traces with the same hidden full rows; `decide-native` |
| `Wire/SilencedAdapter.agda`, `Wire/SilencedAdapterTests.agda` | Normalized silenced local adapter: a present hidden-kind row is `invalid`, never erased; verdict rows carry their input-translation evidence |
| `PairedSilenced.agda`, `PairedSilencedTests.agda` | Paired silenced `check`: certified `accepted`/`rejected`, and evidence-carrying `undetermined` when only the canonical reconstruction fails |
| `PairedSilencedNative.agda` | `At.equivalence` between the paired silenced source predicate and native paired traces; `At.check-native` transports `check` |
| `BoundedRelation.agda`, `BoundedRelationTests.agda` | Inclusions of the bounded `LeiosNotifyPipeline` languages in the lookahead wire languages and four counterexamples to the converses or to `nodeNext` |
| `DriverSearchTests.agda` | Computed full normal/cancellation shutdown, delayed Send and exact payload rejection under the ordered search |
| `ClientEventsBridge.agda` | Explicit visible/erased action partition and exact retained-payload realization |
| `ClientNetworkBridge.agda` | Both native client step/trace directions with declared callback erasure and exact return value |
| `ClientNetworkTests.agda` | Native receiver/Send races, post-Quit handling, cancellation drain and callback visibility controls |
| `DriverEventsBridge.agda` | Canonical full-packet native paired record roundtrip and injectivity |
| `DriverNetworkBridge.agda` | Both finite native paired step/trace directions against the independent driver product |
| `DriverEndpointBridge.agda` | Actual local native client/server executions and matching wire projections for each product run |
| `DriverNetworkTests.agda` | Delayed Sends, Canceled/normal-after-Quit shutdown, endpoint witnesses and FIFO/pending-record controls |
| `NodeDriverBridge.agda` | One-way native paired/endpoint realization of combined production node-policy runs |
| `NodeDriverNetworkBridge.agda`, `NodeDriverNetworkTests.agda` | Exact full-policy native step/path inversion, explicit input witnesses, wire-language equivalence and fault/guard controls |
| `NodeDriverWireCoreNative.agda`, `NodeDriverWireCoreTests.agda` | Cycle-eliminating wire core with all-state source/native language equivalence and hidden accessibility |
| `NodeBasisAdequacy.agda`, `NodeBasisAdequacyTests.agda` | Fresh full-node whole-input eligible-offer basis adequacy; exact observed values/duplicates and explicit nonfresh fixing premise |
| `NodeDriverWireReplay.agda`, `NodeDriverDecide.agda`, `NodeDriverDecideTests.agda` | Complete full node-policy menus/accessibility instantiate the shared one-list/two-list engines, with original source witnesses and exhaustive rejection |
| `NodeDriverDecideNative.agda`, `Wire/NodePairedAdapter.agda`, `NodeDriverReport.agda` | Actual full-policy native paired decisions, lossless normalized adaptation and distinct full-node reports |
| `Wire/NodePolicyObservation.agda`, `Wire/NodePolicyObservationTests.agda` | Reusable universe-polymorphic ordered mapping/recovery, full-node typed observations and actual native transport/decisions; exact malformed/payload controls |
| `NodeDriverTests.agda` | Fresh node-policy schedules with forecast/termination inputs, exact credit/queue transactions and shutdown |
| `ExportFixtures.agda` | Pure TSV rendering of four checked node wire histories, evaluated by Agda DefaultCompute for controlled Haskell comparison |
| `RuntimeCheck.agda` | Sound supplied-schedule interpretation and instruction existence for every finite full-policy run; no exhaustive wire-only search claim |
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
| `Tests.agda`, `ClientTests.agda`, `DriverTests.agda`, `NodeTests.agda` | Inhabited source schedules and negative controls |
| `NativeTests.agda` | Native server PTree steps |
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
The [exact full-policy native tree](../../LeiosNotifyPipeLookahead/README.md#exact-full-policy-native-tree)
now has both step/finite-trace directions, wire-observation equivalence and
complete shared selectors, including Cancel failure. Its explicit input channel
retains the queue, fault flag and external witnesses. Ordinary CSP/legacy-medium
composition equivalence,
wider Haskell differential coverage/full node-callback validation
and formal raw/lexical logger correspondence remain separate
tasks in the [numbered plan](../../../../docs/specs/leiosnotify-pipe-lookahead-plan.md).

Run the validation roots from `src/`:

```sh
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/NativeTests.agda
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
Generated
sources and logs stay outside the repository.
All 40 additional captured histories passed through 22 distinct safely checked
certificates, bringing the total to 80: 70 paired histories and 10 server-only
adversarial histories. The T3.3 result record (historical development evidence removed)
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
cannot be inferred from accepted finite logs.

## Runtime investigation

T5.2.2's [runtime profiles](../../../../docs/notes/leiosnotify-pipe-lookahead-progress.md#pinned-haskell-blocking-and-failure-experiments)
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
and integration record (historical development evidence removed).

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

The capture audit (historical investigation tooling removed) found zero Notify RequestNext
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
See the client source and native records (historical development evidence removed).

## Parallel replay prerequisites

The [input-prefix bounds and callback-target design](../../../../docs/specs/leiosnotify-lookahead-replay-design.md#checked-prefix-bounds-and-callback-targets)
links exact physical hook/FIFO count proofs and finite unit-return callback
enumeration. These support future paired search without assuming unique hidden
successors. The wave record (historical development evidence removed) retains
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
and wave record (historical development evidence removed) retain exact theorem
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
and wave record (historical development evidence removed) retain commands,
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

The cost measurements (historical investigation tooling removed) reuse the existing compiled
baseline checker on synthetic schedules: 86 cases accepted, three paired cases timed out
and 16 larger cases were explicitly not run. Local checks through 64 exchanges
were inexpensive, but even some one-exchange normal closed pairs exceeded five
seconds. Run local checks first and retain limits for paired search. An accepted
shorter prefix never substitutes for an inconclusive full history. The
wave record (historical development evidence removed) retains source identities,
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

The comparison and scale record (historical investigation tooling removed) supersedes the
baseline timeout findings for its retained fixtures. Full normal closed one-
exchange and four-request cancellation histories change from five-second
timeouts to approximately 15 ms acceptance. All 84 original scale cases and
21 follow-up cases complete through 64 exchanges; one already-fast open-prefix
measurement is slightly slower, so there is no universal improvement claim.
Quit/Done, exact payloads, negative controls and EOF races remain checked. Six
changed/new Agda sources have safe checks and a resolved source audit; the
wave-6 record (historical development evidence removed) retains build identities,
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
independent regression guide (historical investigation tooling removed) links a
parametric actual two-exchange source witness under both contracts, retaining
eight visible records and native realization. It demonstrates five candidates
becoming one when the representative equals that repeated whole payload. Direct
packet-conservation proofs exclude trimming or reordering its internal Votes,
independently of the search result. All 18 identical runtime fixtures match on
the old and new binaries: 14 accepted prefixes and four completed rejections.

The unique-basis baseline study (historical investigation tooling removed) deliberately separates
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
wave-7 record (historical development evidence removed) retains source/build
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
The original kernel gate proves guard success; a later general
prefix obstruction (historical investigation tooling removed) refuted
the source family at every size at least three. A separate compiled probe accepts the feasible
two-round control and exhaustively rejects the three/four-round inputs in about
one second each. The public checker still calls complete search after all five
guards pass, and guard success never replaces a paired source witness.

The regression guide (historical development evidence removed) retains an initial prefix-only
274-case run with one unexpected count-deficit timeout, its exact source snapshot
and nonzero result. After adding the proved count guard, the same 274 input bytes,
checker flags, expected statuses and diagnostics all match. The 72-case rejection
matrix now completes through size 64; its slowest measured case is about 25 ms.
The extra three-Receives/one-Send case changes from a two-second timeout to about
13 ms rejection. Valid one-pending-Send races in both directions, normal after
Quit, both callback contracts, exact inner Votes and all prior positive/CLI
controls remain checked. The deliberately missing-file CLI case remains
inconclusive. The wave-8 record (historical development evidence removed) retains
proof/build/source identities and operational bounds. These synthetic results
are not universal tractability, logger fidelity or implementation refinement.

The subsequent 83-case stress comparison (historical investigation tooling removed) fixes
77 distinct inputs before measuring the three-guard and request-credit binaries.
All 26 orphan-reply negatives through 128 preceding exchanges now reject in
about 13–44 ms; 24 were previously timed out or unrun. The one-exchange orphan
Done still times out, with larger members unrun. Two large positive cases also
cross the two-second ceiling after completing near that limit in the baseline;
the study retains that performance qualification. All 274 original regression
expectations still match on the new binary. Separate matched probes of those
two large positives accept in all 12 runs below two seconds, using an explicit
five-second ceiling; they do not replace the original two timeouts. The
wave-9 record (historical development evidence removed) retains the safe checks,
typed logger-schema evidence, build and bounded runtime identities. This is
additional necessary refutation, not a general tractability result.

The shutdown continuation (historical investigation tooling removed) preserves the same
83 stress inputs and budgets. All 35 negative cases now complete, including all
nine orphan-Done sizes through 128 preceding exchanges; eight were previously
inconclusive or unrun. The full result is 30 accepted prefixes, 35 rejections,
seven positive timeouts and 11 skipped larger positives. No completed verdict
disagrees with its expectation, and all 274 original regressions still match.
The separate cycle probe preserves the distinction between the kernel guard
gate, reviewed causal explanation and concrete compiled refutations. The
wave-10 record (historical development evidence removed) retains proof/build
identities, independent review and exact operational limits. No changes to guard
order or successor menus are justified by the earlier matched timing evidence.

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

The internal diagnostic (historical investigation tooling removed) compares actual raw and
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
wave-12 record (historical development evidence removed) retains build,
proof, independent review and comparison evidence. Certificate extraction still
delegates to old `target-sound`, so this gate does not eliminate every possible
original-menu reconstruction.

## Certificate consumption and compiled demand

The [compiled-demand account](../../../../docs/specs/leiosnotify-lookahead-replay-design.md#certificate-demand-versus-ordinary-verdicts)
resolves the preceding runtime question for the retained wave-12 build: the
ordinary report discards accepted witnesses, and accessibility is erased.
Later `target-sound` reconstruction is not demanded by its status/text/exit
path. Certificates already inspected to score menu choices are a different
operation. Several textual basis applications also do not establish repeated
ordinary preparation; the live ordered-target closure shares one basis thunk.

The separate diagnostic (historical investigation tooling removed) deliberately
forces every outer `B.Tau` constructor alongside its target state. Its sums
are not proof identities, protocol verdicts or a complete-witness normalization.
Source anchors, arbitrary nonce perturbations and whole-input ranking contexts
retain their previous scope. This experiment cannot establish a speedup of the
ordinary CLI, which does not demand the measured extraction.

The fixed 108-slot diagnostic completes 100 cases, with two claimed/distinct-64
timeouts and six larger skips; all 50 completed old/direct comparisons agree.
Some forced-consumer allocations fall, while observed timings vary in both
directions. Direct extraction still reconstructs the gated sorted menu, rather
than reusing a physically cached target list. The
wave-13 record (historical development evidence removed) retains safe checks,
source/generated review, bounded build and original checkpointed monitor rows.
All existing production sources and the prior CLI executable retain their bytes;
earlier replay regressions are historical evidence and were not rerun here.

## Fixed node-client control replay

The explicit `node-client-control` profile checks
[`NodeClientModel`](../../LeiosNotifyPipeLookahead/NodeClientModel.agda) with unit
return. It retains depth 1000, forecast/stop source actions, normal handling and
the abnormal unexpected-Canceled state. It does not infer the actual truth of
unlogged forecast/governor inputs or restrict the existing generic paired model.
The source audit (historical development evidence removed) and
dependency audit (historical development evidence removed)
find the latest inspected consensus files and dependency pins unchanged from the
user's reference revision; the model pin stays intact.

`Wire/NodeClientPolicy` instantiates `Semantics.Replay.Decide` with finite sound
and complete source menus. Existing client potential proves hidden accessibility
on every state. Both trace directions retain the target and all erased source
choices; rejection excludes every matching initial source execution. No finite
global state graph, guessed fuel, payload representative or extra reachable-state
premise is used. All new proof roots pass bounded `--safe` checks, with zero
integrity-audit findings.

```sh
LookaheadMain --notify-lookahead client.txt --role client --client-policy node-client-control --observation driver-log --assume-fresh
```

Select `clientCallbacks: "node-client-control"` in a `localclient` manifest for
the same route. This standalone local selection is unsupported for server/paired
mode; the distinct full-node paired profile (historical development evidence removed)
requires explicit `nodePolicy: "full-node"` in a paired manifest. Existing
`--next-contract` forms remain generic; `node-next` is a server callback contract,
not an implicit node-client selection. Invalid role/agency/parsing remains
separate from exhaustive policy rejection. EOF is a finite prefix and can retain
a pending handler or fault; it does not prove successful termination.

All 80 CLI expectations pass, including 62 unchanged legacy cases and the one
intentional missing-file inconclusive. Two genuine public-coordinator runs then
accept `RequestNext, Quit, Canceled, Done` and reject the local-policy separation
`RequestNext, RequestNext, Canceled, normal, RequestNext`. That separation is
accepted by the generic client; it is not asserted as a fresh honest paired
nodeNext execution. See the workflow and evidence (historical development evidence removed)
and record (historical development evidence removed). Capture fidelity,
formal raw lexical transport and full NodeDriver/native policy inversion remain
outside this local control theorem.

## Silenced observation replay

The `driver-log-no-request-votes` observation is for logs whose configuration
silences RequestNext and Votes in both directions. The protocol-layer
[ServerSilenced](../../LeiosNotifyPipeLookahead/Wire/ServerSilenced.agda) and
[ClientSilenced](../../LeiosNotifyPipeLookahead/Wire/ClientSilenced.agda)
define `Silenced` as the erasure (`erase`) of some full wire trace of the exact
server or client language. `decide-silenced` decides it exactly: acceptance
goes through `fill-sound`, which supplies a concrete full trace, and rejection
goes through `erase-complete`. [WireSilencedNative](WireSilencedNative.agda)
transports both directions to native traces with the same hidden rows
(`Server.equivalence`, `Client.equivalence`, `decide-native`).

[Wire/SilencedAdapter](Wire/SilencedAdapter.agda) reuses the existing
normalized translations. A RequestNext or Votes row that is present is reported
as `invalid` at its position (`silenced kind present: RequestNext/Votes`),
unless an earlier translation failure takes precedence. Such a row is never
erased by the checker. [PairedSilenced](PairedSilenced.agda) `check` returns:

- `accepted`, with a `SilencedSourceTrace` built from the canonical
  reconstruction (`reconstruct-erases`);
- `rejected`, only when a local silenced check fails (`local-necessary`). This
  refutes every hidden schedule;
- `undetermined`, when both local checks pass but the exact paired decider
  refutes the canonical hidden-request reconstruction. This is **not a
  refutation**: another hidden schedule may exist.

`SilencedAdapter.paired` lifts this to the two normalized inputs: its
`checked` result carries `Client.Rows`/`Server.Rows` for both inputs and the
`check` outcome on their translations, and `SilencedAdapter.exclude` turns a
rejection into a refutation of `PairedAccepted` over every valid translation.
[PairedSilencedNative](PairedSilencedNative.agda) gives `At.equivalence` with
native paired traces and `At.check-native`. `LookaheadReport.localSilenced` and
`pairedSilenced` (which matches on `SilencedAdapter.paired`) expose the forms through `LookaheadMain`; checker exit 3 is `undetermined`. The
[tools guide](tools/README.md#silenced-observation-and-capture-batch-replay)
gives the CLI, the coordinator mapping (`model-undetermined`, exit class 4, no
protocol verdict) and the `capture_batch.py` multi-host runner.

Claim boundary. Silenced acceptance is not full-observation acceptance, and
prefix acceptance is not completion. Acceptance constrains only the order of
Quit, Canceled and Done: at most one Quit, Done only after Quit, nothing after
Done; under `node-next` also no Canceled before Quit and no visible notification
after the first post-Quit Canceled; and in paired mode FIFO consistency of the
visible replies. It cannot check request credit, pipelining depth,
notification/request counts, Votes or payload-level request/reply matching.

The [October 29 replay note](../../../../docs/notes/leiosnotify-silenced-capture-replay.md)
records one capture: all 2,221 local sessions and all 159 literal pairs are
`accepted-prefix` under both server contracts. That uniform acceptance is weak
conformance evidence; only the constructed controls in the note demonstrate
discrimination. The capture contains neither Canceled before Quit nor a
notification after a post-Quit Canceled, so it does not exercise the
generic/node distinction. Plan Task 8 (fresh captures under full observation)
is pending; when captures are supplied it runs with
`capture_batch.py --observation driver-log`.

### Silenced replay validation

Run 7 November 2026 at `7b1c0099`, serially from `src/`, with the sandbox
disabled. The interfaces of the 15 modules these roots check were deleted first (13 new;
`LookaheadReport` and `LookaheadReportTests` modified; the also-modified
`LookaheadMain` is compiled by the build below, not by these roots), and each
root printed literal `Checking` lines for its new modules:

```sh
systemd-run --user --scope -q -p MemoryMax=25G -- agda +RTS -M20G -RTS --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/Wire/ServerSilencedTests.agda
systemd-run --user --scope -q -p MemoryMax=25G -- agda +RTS -M20G -RTS --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/Wire/ClientSilencedTests.agda
systemd-run --user --scope -q -p MemoryMax=25G -- agda +RTS -M20G -RTS --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/Wire/SilencedAdapterTests.agda
systemd-run --user --scope -q -p MemoryMax=25G -- agda +RTS -M20G -RTS --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/PairedSilencedTests.agda
systemd-run --user --scope -q -p MemoryMax=25G -- agda +RTS -M20G -RTS --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/PairedSilencedNative.agda
systemd-run --user --scope -q -p MemoryMax=25G -- agda +RTS -M20G -RTS --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/LookaheadReportTests.agda
systemd-run --user --scope -q -p MemoryMax=25G -- agda +RTS -M20G -RTS --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/BoundedRelationTests.agda
```

All seven exited 0, in 2 to 10 seconds each. The `LookaheadMain` build in
`/var/tmp/leiosnotify-silenced-build` was regenerated with the
[two-stage build](tools/README.md#normalized-lookahead-cli-and-manifest-runner);
GHC found every module up to date, so the binary is unchanged. Then, from the
repository root:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/test_lookahead_cli.py \
  --binary /var/tmp/leiosnotify-silenced-build/LookaheadMain --out /var/tmp/leiosnotify-silenced-task10-cli
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/capture_batch.py --selftest
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/capture_batch.py --selftest \
  --checker /var/tmp/leiosnotify-silenced-build/LookaheadMain --out /var/tmp/leiosnotify-silenced-task10-smoke
```

The CLI suite passed 66 of 66 cases (62 earlier cases and 4 silenced cases),
with the one expected operational inconclusive. Both `capture_batch.py`
self-tests passed, with the fake checker and with the real binary.

## Bounded and lookahead wire languages

[BoundedRelation](BoundedRelation.agda) relates the bounded
[`LeiosNotifyPipeline`](../LeiosNotifyPipeline.agda) specification to the
lookahead wire languages. Both sides read the same rows through the existing
`ServerAdapter.decode` and `ClientAdapter.decode`, so no new encoding is
introduced. The results hold for every depth:

- `server-included-generic`: every bounded server trace is in the lookahead
  server language under `genericNext`.
- `client-included`: every bounded client trace is in the lookahead client
  language.
- `node-canceled-open`: there is **no** server inclusion under `nodeNext`. The
  bounded server may send Canceled while the session is open, and `nodeNext`
  rejects that.
- The converses fail:
  - `normal-after-quit`: the lookahead server under `nodeNext` sends a normal
    reply after Quit, which the bounded server rejects.
  - `over-depth` and `over-depth-lookahead`: `depth + 1` requests are rejected
    by the bounded server but accepted by the lookahead server under both
    contracts.
  - `client-lead`: the lookahead client receives a reply before its delayed
    request Send (the `Lead` state), which the bounded client rejects.

These are language relations over wire rows. They do not relate the two
models' internal states, and they say nothing about the deployed node.
`BoundedRelationTests` checks the translations by `refl` and runs both
deciders on every counterexample. It computes the inclusions at depths 2 and
1000, and it applies the counterexamples at depths 1 and 1000.
