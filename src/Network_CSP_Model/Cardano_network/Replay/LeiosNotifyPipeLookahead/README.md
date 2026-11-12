# LeiosNotifyPipeLookahead replay bridges and validation

This directory replays normalized LeiosNotify logs against the pinned lookahead
model: a pipelined client and a lookahead server, following consensus
`2416493bfdbe93b761b3a4bb1ccf2b4a913e5e4b`. The protocol definitions and
productive PTree constructors live in
[`Cardano_network/LeiosNotifyPipeLookahead/`](../../LeiosNotifyPipeLookahead/README.md);
the native entry point is
[`Cardano_network.LeiosNotifyPipeLookahead`](../../LeiosNotifyPipeLookahead.agda).
This directory consumes those models; the protocol modules never import Replay.
Pinned source URLs and checksums are in
[`sources.json`](../../LeiosNotifyPipeLookahead/sources.json).

The [`tools/`](tools/README.md) subdirectory holds the CLI coordinators, the raw
input helper, the capture preflight, the multi-host batch runner, the bounded
Agda checker wrapper and the controlled Haskell comparison harness.

The legacy checker [`Main.agda`](../Main.agda) is separate and keeps its bounded
`LeiosNotifyPipe` targets; see the [replay README](../README.md).

## Entry points

<a id="normalized-input-and-cli-delivery"></a>

The compiled [`LookaheadMain`](LookaheadMain.agda) accepts exactly these forms
(arguments in the order shown):

| Form | Model checked |
| --- | --- |
| `--notify-lookahead FILE --role client\|server --next-contract C --observation driver-log --assume-fresh` | One endpoint, generic successful client callbacks, unit return |
| `--paired-notify-lookahead PAIR --next-contract C --observation driver-log --assume-fresh` | Both endpoints through the paired driver model |
| `--notify-lookahead FILE --role client --client-policy node-client-control --observation driver-log --assume-fresh` | The node's fixed-depth client policy |
| `--paired-notify-lookahead PAIR --node-policy full-node --observation driver-log --assume-fresh` | The combined production node policy, both endpoints |
| `--notify-lookahead FILE --role client\|server --next-contract C --observation driver-log-no-request-votes --assume-fresh` | One endpoint, RequestNext and Votes rows hidden |
| `--paired-notify-lookahead PAIR --next-contract C --observation driver-log-no-request-votes --assume-fresh` | Both endpoints, RequestNext and Votes rows hidden |

`C` is the server callback contract: `generic-next` (the server may select
Canceled at any time) or `node-next` (the node's normal-only selection). It is
unused by a standalone client. The usage text does not list the two silenced
forms, so that existing outputs stay byte-identical.

Local input is a `role client`/`role server` header followed by normalized
Notify events. Paired input is the existing `pair LeiosNotifyP ...` format with
original source lines.

The first output line is the verdict tag, and the exit code matches it:

| Exit | Tag | Meaning |
| --- | --- | --- |
| 0 | `accepted-prefix` | The input is a prefix of some model run under the declared observation |
| 1 | `protocol-rejected` | No model run explains the input; certified |
| 2 | `invalid-input` | Parse, role or agency failure, or a hidden-kind row under the silenced observation |
| 3 | `undetermined` | Silenced paired mode only: the canonical reconstruction failed; not a refutation |

A stdlib IO exception may exit without a tag; an exit code alone never
establishes a rejection. EOF is always a prefix, never proof of closure. Every
form asserts a fresh initial state.

Prefer the [manifest runner](tools/replay_lookahead.py), which validates
[profile declarations](tools/profiles/README.md), artifact hashes, normalized rows
and source maps before invoking an explicit binary:

| Runner exit | Result |
| --- | --- |
| 0 | Accepted model prefix |
| 1 | Exhaustive protocol rejection under the declared profile |
| 2 | Invalid manifest, artifact or normalized input |
| 3 | Missing required capture assertions |
| 4 | Inconclusive: resource limit, checker failure, tag/code mismatch, or `model-undetermined` |

The runner requires the matching tag and exit code, kills timed-out checker
process groups and bounds input, output and heap. Fresh, ordered and lossless
capture statements in a manifest are assertions, not established facts. For
whole multi-host captures use [`capture_batch.py`](tools/README.md#silenced-observation-and-capture-batch-replay).

## Modules

### Source and native bridges

| Module | Purpose |
| --- | --- |
| `ClientBridge.agda` | Both finite trace directions between the client rules and its source-operation PTree |
| `DriverBridge.agda` | Both finite record-trace directions for the generic paired driver prefix tree |
| `ServerEventsBridge.agda` | Native event realization roundtrip and exact-action injectivity at every endpoint |
| `ServerBridge.agda` | Both native `LNPEv` step/trace directions, return classification and native shutdown guards |
| `ClientEventsBridge.agda` | Visible/erased action partition and exact retained-payload realization |
| `ClientNetworkBridge.agda` | Both native client step/trace directions with declared callback erasure and exact return value |
| `DriverEventsBridge.agda` | Canonical full-packet native paired record roundtrip and injectivity |
| `DriverNetworkBridge.agda` | Both finite native paired step/trace directions against the driver product |
| `DriverEndpointBridge.agda` | Local native client/server executions and matching wire projections for each product run |

### Local wire replay and adapters

| Module | Purpose |
| --- | --- |
| `Wire/ServerQuotient.agda` | Both server source/wire inclusions and exhaustive source decision |
| `Wire/ClientSound.agda`, `Wire/ClientComplete.agda`, `Wire/ClientQuotient.agda` | Both client source/wire inclusions and exhaustive decision, given a Return inhabitant |
| `WireNative.agda`, `WireServerNative.agda` | Declared deletion observation, exact native server realization and native wire decision |
| `WireClientNative.agda` | Standalone client wire transport for every native path, generic in Params and Return |
| `Wire/ServerAdapter.agda`, `Wire/ClientAdapter.agda`, `Wire/PairedAdapter.agda` | Lossless normalized-event mapping with located invalid input versus exhaustive protocol verdicts |
| `Wire/ServerAdapterNative.agda`, `Wire/ClientAdapterNative.agda`, `Wire/PairedAdapterNative.agda` | Native realization and decision at the summary `exactParams` instance |
| `Wire/LoggerObservation.agda` | Typed post-lexical logger tags/fields and exact adapter transport |
| `LookaheadReport.agda` | Tagged reports, located errors and the silenced/`undetermined` reports |
| `LookaheadMain.agda` | Stdlib IO entry point; compiled separately from the safe proof roots |

### Paired decision

| Module | Purpose |
| --- | --- |
| `DriverDecide.agda` | Exhaustive source compatibility of two typed endpoint prefixes over all their merges |
| `DriverDecideNative.agda` | Native paired realization/refutation with exact decoded rows and endpoint witnesses |
| `BasisAdequacy.agda`, `UniqueBasisAdequacy.agda` | Input-relative payload basis, deduplicated, preserving every original execution |
| `LocalPrecheck.agda`, `PacketPrecheck.agda`, `PacketCountPrecheck.agda`, `CreditPrecheck.agda`, `ShutdownPrecheck.agda` | Five proved necessary conditions checked before the complete search |
| `ReadyGateOrder.agda` | Exact callback-enumeration fast path preserving every proof-bearing menu |

### Node policy

| Module | Purpose |
| --- | --- |
| `Wire/NodeClientPolicy.agda`, `Wire/NodeClientAdapter.agda`, `NodeClientReport.agda` | Fixed-depth node-client policy: exact source-language equivalence and exhaustive local decision |
| `NodeDriverBridge.agda` | One-way native realization of combined production node-policy runs |
| `NodeDriverNetworkBridge.agda` | Full-policy native step/path inversion and wire-language equivalence |
| `NodeDriverWireCoreNative.agda` | Cycle-eliminating wire core with all-state source/native language equivalence |
| `NodeBasisAdequacy.agda` | Fresh full-node eligible-offer basis adequacy |
| `NodeDriverWireReplay.agda`, `NodeDriverDecide.agda`, `NodeDriverDecideNative.agda`, `Wire/NodePairedAdapter.agda`, `NodeDriverReport.agda` | Full node-policy paired decision, native transport, normalized adaptation and reports |
| `Wire/NodePolicyObservation.agda` | Full-node typed observations and native transport |

### Silenced observation and bounded relation

| Module | Purpose |
| --- | --- |
| `Silenced.agda` | Hidden predicates `isVotes` and `hiddenKind` (RequestNext/Votes in either direction) |
| `WireSilencedNative.agda` | `equivalence` between each silenced local language and native traces; `decide-native` |
| `Wire/SilencedAdapter.agda` | Silenced local and paired adapters; verdict rows carry their input-translation evidence |
| `PairedSilenced.agda` | Paired silenced `check`: certified `accepted`/`rejected`, otherwise evidence-carrying `undetermined` |
| `PairedSilencedNative.agda` | `At.equivalence` with native paired traces and `At.check-native` |
| `BoundedRelation.agda` | Bounded `LeiosNotifyPipeline` languages versus the lookahead wire languages |

### Property bridges

| Module | Purpose |
| --- | --- |
| `ConservationBridge.agda` | FIFO and server request/reply accounting on every fresh native paired finite trace |
| `ShutdownBridge.agda` | Shutdown persistence, new-selection guarantees and role-specific Done completion on native traces |
| `SchedulingBridge.agda` | Native hidden accessibility, divergence exclusion and shutdown step bounds |
| `ProgressBridge.agda` | Conditional runtime completion realized as native paths; structural premises explicit |
| `ServerDrainBridge.agda`, `PairedDrainBridge.agda` | Fresh server drain and full paired structural progress as native continuations |
| `RunRuntime.agda` | Constructed runtime schedules for supplied finite example paths; no fairness inference |

### Haskell comparison modules

| Module | Purpose |
| --- | --- |
| `ExportFixtures.agda` | Pure TSV rendering of checked node wire histories, evaluated by Agda for comparison |
| `RuntimeCheck.agda` | Sound interpretation of supplied finite schedules; no exhaustive-search claim |
| `RuntimeCertificates.agda`, `RuntimeInstance.agda` | Concatenation of checked runs and the shared instance for generated certificates |

Most modules above have a `*Tests.agda` (and, where relevant, `*NativeTests.agda`)
companion with concrete witnesses and negative controls. `Tests.agda`,
`ClientTests.agda`, `DriverTests.agda`, `NodeTests.agda`, `NativeTests.agda`,
`ClientNativeTests.agda` and `DriverNativeTests.agda` cover the source models
and their PTrees directly.

## Bridge scope

The server bridge retains readiness API events and the source model's abstract
admission outcomes. `realize` supplies a native execution for every source run;
`sound` reconstructs a source run from every native finite execution. The native
client bridge keeps all wire records and normal API deliveries, erasing only the
classified callback decisions and successful generic Canceled handling. It
retains the exact return value; the node-specific fault policy is a separate
component.

The paired driver product has both trace directions and endpoint projection
certificates. `NodeDriverModel` binds both node-policy components and has a
one-way native realization; the separate
[exact full-policy native tree](../../LeiosNotifyPipeLookahead/README.md#exact-full-policy-native-tree)
has both directions, wire-observation equivalence and complete selectors,
including Cancel failure. The generic native target is broader than the node
policy: generic acceptance alone does not certify a node-policy witness.

## Local wire replay

<a id="exact-server-wire-replay"></a>

The protocol-side [Wire/Server](../../LeiosNotifyPipeLookahead/Wire/Server.agda)
is a deterministic counter machine over typed wire rows. [ServerQuotient](Wire/ServerQuotient.agda)
proves it equivalent to the detailed fresh server source language under both
`genericNext` and `nodeNext`, with arbitrary exact notification values.
`decide-source` constructs a source witness or refutes all matching internal
schedules; there is no fuel cutoff or finite notification basis.
[WireServerNative.For.decide](WireServerNative.agda) transports this to native
PTree wire prefixes at fixed Params, link and direction. `nodeNext` constrains
reply kinds only; it adds no NodeModel credit/FIFO evidence.

<a id="generic-client-source-replay"></a>
[ClientQuotient](Wire/ClientQuotient.agda) relates
[Wire/Client](../../LeiosNotifyPipeLookahead/Wire/Client.agda) to `ClientModel.Run`
prefixes after erasing continue/terminate/handled callbacks. It keeps exact
normal/Canceled values and receiver-before-Send ordering: the `Lead` state
permits one reply before its delayed Request Send. The result is language
equivalence, not final-state bisimulation or a depth-1000 policy witness.
[WireClientNative](WireClientNative.agda) lifts it to every native path.

<a id="normalized-server-input-adapter"></a>
The adapters map `List (Maybe LeiosNotifySession.E)` exactly. A failed parse,
unsupported row or wrong direction is located invalid input, and no row is
dropped. Mapping uniqueness ties each decision to the input. The native adapter
wrappers give existential canonical realizations of the typed summary schema
at `exactParams`; they do not prove that raw deployed events were parsed
correctly. Failure positions are input indices, not file/thread coordinates.

## Typed paired driver replay

[DriverDecide](DriverDecide.agda) decides whether two typed endpoint prefixes are
compatible with the detailed fresh `DriverModel`. `SourceTrace` existentially
quantifies an order-preserving merge and an actual source run: acceptance
constructs both, and rejection refutes every source schedule and merge. Exact
values, local order, pending Send/Receive records and prefix EOF are preserved.
The checker takes Notification equality, an explicit normal representative and
the server contract; client callbacks use the generic successful contract with
unit return.

The search is complete without a queue cap, fuel, state equality or a finite
global state graph:

- <a id="unique-payload-basis-and-rejection-limits"></a>A finite payload basis is fixed from both inputs and deduplicated;
  [BasisAdequacy](BasisAdequacy.agda) and [UniqueBasisAdequacy](UniqueBasisAdequacy.agda)
  prove that no original execution is lost.
- Complete restricted hidden menus and the existing accessibility certificate
  feed the generic [two-list decider](../../../Semantics/Replay/TwoListDecide.agda).
- [DriverSearchOrder](../../LeiosNotifyPipeLookahead/DriverSearchOrder.agda)
  orders the proof-bearing hidden moves by the remaining input; every move stays,
  so ordering affects cost, never the verdict.
- [ReadyGateOrder](ReadyGateOrder.agda) skips callback enumeration where none can
  fire; `readyMoves-exact` and `orderedTargets-exact` prove the menus unchanged.

<a id="proved-necessary-prechecks"></a>
Five necessary conditions run before the search, each proved for the same
unrestricted `DriverModel.Run` and `DriverRows.Merge`. A failure refutes
`SourceTrace`; success still runs the complete search.

1. [LocalPrecheck](LocalPrecheck.agda): both endpoints are in their exact local
   wire languages.
2. [PacketPrecheck](PacketPrecheck.agda): recorded Send and Receive lists agree
   at every common packet position.
3. [PacketCountPrecheck](PacketCountPrecheck.agda): recorded receives exceed peer
   sends by at most one (the pending Send hook) in each direction.
4. [CreditPrecheck](CreditPrecheck.agda): recorded client replies cannot outnumber
   recorded server Request receives.
5. [ShutdownPrecheck](ShutdownPrecheck.agda): a recorded client Done requires a
   recorded server Quit receive; a pending server Send-Done stays allowed.

`DriverDecide.all-precheck-necessary` combines them.
[DriverDecideNative.At](DriverDecideNative.agda) decides native paired PTree
realizability at fixed Params and endpoint coordinates (normal representative
`votes []`).

Termination does not bound practical cost: paired search is sensitive to
schedule order on large inputs. Check local endpoints first and keep explicit
limits; resource exhaustion is inconclusive, and an accepted shorter prefix
never substitutes for an inconclusive full history.

## Typed logger-schema observation

[Wire/LoggerObservation](Wire/LoggerObservation.agda) models the post-lexical
logger schema: namespace direction and tag, `data.kind` direction and message
fields are independent inputs, so contradictions are rejected. Both RequestNext
namespace spellings are supported; announcement metadata is all absent or all
present; Votes keep hashes, voter IDs, order and duplicates.
`normalize-faithful` and its converse characterize successful normalization, and
client, server and paired acceptance transport both ways through this relation.
It does not verify JSON/UTF-8/hex parsing, the Python code, file coordinates or
physical logger emission.

## Raw input correspondence and capture preflight

The [capture preflight](tools/capture-preflight/README.md) inventories request
hooks and NewMux boundaries and records the testnet configuration that silences
RequestNext and Votes. The [raw helper](tools/raw-input/README.md) validates
driver-hook records, reuses the Notify summary encoding and writes a selected
local trace with line and byte/thread maps. The opt-in
[raw replay coordinator](tools/replay_raw_lookahead.py) rederives those artifacts
from the raw bytes before calling the manifest runner; artifact mismatch is
invalid input, while file mutation or resource exhaustion is inconclusive. These
are executable checks of supplied bytes, not theorems about Python or the logger.

## Fixed node-client control replay

The `node-client-control` profile checks
[`NodeClientModel`](../../LeiosNotifyPipeLookahead/NodeClientModel.agda) with unit
return: depth 1000, forecast/stop source actions, normal handling and the
unexpected-Canceled fault state. `Wire/NodeClientPolicy` instantiates the
frontier decider [`Semantics.Replay.Frontier`](../../../Semantics/Replay/Frontier.agda)
with finite sound and complete menus, inherited hidden accessibility and
decidable policy-state equality; rejection excludes every matching initial
source execution. The frontier keeps the set of states reachable by the
processed rows and expands each distinct hidden-closure state once per row.
The path-by-path `Semantics.Replay.Decide` search it replaces re-explored
equivalent main/receiver interleavings and exhausted a 2 GB heap on
real-capture sessions of a few thousand rows once the 1000-request window was full.
It does not infer the truth of unlogged forecast/governor inputs. Select it with
`clientCallbacks: "node-client-control"` in a `localclient` manifest; the paired
full-node profile needs `nodePolicy: "full-node"`. `node-next` is a server
contract, not a client policy.

## Silenced observation replay

The `driver-log-no-request-votes` observation is for logs whose configuration
silences RequestNext and Votes in both directions. The protocol-layer
[ServerSilenced](../../LeiosNotifyPipeLookahead/Wire/ServerSilenced.agda) and
[ClientSilenced](../../LeiosNotifyPipeLookahead/Wire/ClientSilenced.agda)
define `Silenced` as the erasure (`erase`) of some full wire trace of the exact
server or client language. `decide-silenced` decides it exactly: acceptance
goes through `fill-sound`, which supplies a concrete full trace, and rejection
goes through `erase-complete`. [WireSilencedNative](WireSilencedNative.agda)
transports both directions to native traces with the same hidden rows.

[Wire/SilencedAdapter](Wire/SilencedAdapter.agda) reuses the normalized
translations. A RequestNext or Votes row that is present is reported as
`invalid` at its position (`silenced kind present: RequestNext/Votes`), unless
an earlier translation failure takes precedence; such a row is never erased.
[PairedSilenced](PairedSilenced.agda) `check` returns:

- `accepted`, with a `SilencedSourceTrace` built from the canonical
  reconstruction (`reconstruct-erases`);
- `rejected`, only when a local silenced check fails (`local-necessary`), which
  refutes every hidden schedule;
- `undetermined`, when both local checks pass but the exact paired decider
  refutes the canonical hidden-request reconstruction. This is **not a
  refutation**: another hidden schedule may exist.

`SilencedAdapter.paired` lifts this to the two normalized inputs: its result
carries `Client.Rows`/`Server.Rows` for both inputs, and `SilencedAdapter.exclude`
turns a rejection into a refutation over every valid translation.
[PairedSilencedNative](PairedSilencedNative.agda) gives `At.equivalence` with
native paired traces and `At.check-native`.

Claim boundary: silenced acceptance is not full-observation acceptance, and a
prefix is not completion. Acceptance constrains only the order of Quit, Canceled
and Done: at most one Quit, Done only after Quit, nothing after Done; under
`node-next` also no Canceled before Quit and no visible notification after the
first post-Quit Canceled; and in paired mode FIFO consistency of the visible
replies. It cannot check request credit, pipelining depth, notification/request
counts, Votes or payload-level request/reply matching.

The [October 29 replay note](../../../../docs/notes/leiosnotify-silenced-capture-replay.md)
records one capture: all 2,221 local sessions and all 159 literal pairs are
`accepted-prefix` under both server contracts. That uniform acceptance is weak
conformance evidence; only the constructed controls in the note demonstrate
discrimination. The capture contains neither Canceled before Quit nor a
notification after a post-Quit Canceled, so it does not exercise the
generic/node distinction. Replaying fresh captures under full observation
(`capture_batch.py --observation driver-log`) awaits captures with RequestNext
and Votes logged.

## Bounded and lookahead wire languages

[BoundedRelation](BoundedRelation.agda) relates the bounded
[`LeiosNotifyPipeline`](../LeiosNotifyPipeline.agda) specification to the
lookahead wire languages. Both sides read the same rows through the existing
`ServerAdapter.decode` and `ClientAdapter.decode`. The results hold for every
depth:

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

These are language relations over wire rows. They do not relate internal states
and say nothing about the deployed node. `BoundedRelationTests` checks the
translations by `refl` and runs both deciders on every counterexample.

## Paired-model properties

The protocol layer proves conservation (`ServerConservation`,
`DriverConservation`, `NodeConservation`), shutdown (`ClientShutdown`,
`ServerShutdown`, `DoneOrigin`, `DriverShutdown`, `NodeShutdown`), hidden
scheduling bounds, conditional runtime completion and full fresh paired
structural progress (`CommandFlow`, `ResponseFlow`, `ReplyLedger`,
`ClientDrain`, `PairedDrain`). The bridges listed above lift each result to
native traces. Exact statements and premises are in the
[conservation](../../../../docs/notes/leiosnotify-pipe-lookahead-conservation.md),
[shutdown](../../../../docs/notes/leiosnotify-pipe-lookahead-shutdown.md),
[scheduling](../../../../docs/notes/leiosnotify-pipe-lookahead-scheduling.md),
[progress](../../../../docs/notes/leiosnotify-pipe-lookahead-progress.md),
[server-drain](../../../../docs/notes/leiosnotify-pipe-lookahead-server-drain.md)
and [paired-drain](../../../../docs/notes/leiosnotify-pipe-lookahead-paired-drain.md)
notes. Structural progress is proved; external responsiveness and failure
conditions cannot be inferred from accepted finite logs.

## Controlled Haskell comparison

The [harness](tools/README.md) builds the unchanged pinned peers and drivers and
runs eight STM-controlled schedules, five times each at `-N1` and `-N2`. All 80
captured wire histories (70 paired, including interrupted prefixes, and 10
server-only adversarial histories) match safely checked Agda witnesses: 40 match
the four histories rendered by `ExportFixtures`, and the other 40 match 22
certificates from [`certify.py`](tools/certify.py), which checks small parts with `agda --safe`,
proves their concatenation and realizes the exact rows in the native tree. Its
Python planner is untrusted; failing to find a schedule is inconclusive. These
runs do not execute all production node callbacks or certify CBOR/socket
behavior.

## Validation

Run from `src/`, one Agda process at a time and with a heap cap
(`+RTS -M<n>G -RTS`). Source models and PTrees:

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

Replay, silenced observation and bounded relation:

```sh
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/Wire/ServerTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/WireServerNativeTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/Wire/ServerSilencedTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/Wire/ClientSilencedTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/Wire/SilencedAdapterTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/PairedSilencedTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/PairedSilencedNative.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/LookaheadReportTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/BoundedRelationTests.agda
```

Every other `*Tests.agda` module in this directory is also a standalone root.
`tools/check_agda.py` runs roots serially with the replay runner's resource
limits. Build `LookaheadMain` with the two-stage command in
[tools/README.md](tools/README.md#normalized-lookahead-cli-and-manifest-runner),
then from the repository root:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/test_lookahead_cli.py \
  --binary "$LOOKAHEAD_BUILD/LookaheadMain" --out /var/tmp/lookahead-cli-check
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/capture_batch.py --selftest
```

Recorded results: at `7b1c0099` all seven silenced, report and bounded roots
typechecked from deleted interfaces; at `6b52b420` the six roots touched by the
final fixes were rechecked. At both commits the CLI suite passed 66 of 66 cases
(including one intentional operational inconclusive) and both `capture_batch.py`
self-tests passed, with the fake checker and with the real binary.

## Open boundaries

- Formal raw lexical/logger correspondence: the Python normalizer and raw helper
  are executable checks, not proved.
- Full NodeDriver/native policy inversion and CSP/legacy-medium composition
  equivalence.
- Haskell implementation refinement; the comparison above is controlled
  differential evidence only.
- Full-observation replay of real captures: no capture with RequestNext logged
  is available yet.

The [numbered plan](../../../../docs/specs/leiosnotify-pipe-lookahead-plan.md)
and the [source audit](../../../../docs/notes/leiosnotify-pipe-lookahead-source-audit.md)
track these; earlier measurement records remain in git history.
