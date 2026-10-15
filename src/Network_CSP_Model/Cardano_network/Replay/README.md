# Trace replay

The executable checks normalized LeiosFetch and LeiosNotifyP events against the first-order
session specification. It accepts prefixes, including unfinished sessions at
EOF. An accepted prefix is not evidence of delivery or successful completion.

## One model for interleaved sessions

`LeiosFetchInterleaved.agda` folds the generic heterogeneous product in
`Semantics/Replay/Interleave.agda` into a finite session model. The manifest
fixes each session's role and initial state. A tagged event changes only its
session; a silent step advances one component. Each client has its own FIFO
queue and bound `K`, and each server has its own outstanding request.

The generic `projection-equivalence` theorem proves that a global trace is
permitted exactly when both component projections are permitted. Recursively,
`check` decides the finite product using local deciders: `yes` carries a trace
witness of the product, and `no` refutes product trace membership. This avoids
searching all permutations of independent server silent steps. No new
postulates, termination overrides, or classical assumptions are introduced.
The generic product, instance, parser, reporting and tests use `--safe`.

The generic product permits different event and state types and universes on
its two sides. Future mini-protocol replay specifications can therefore be
combined through the same product once their local replay interfaces and
deciders are provided. The executable combines both protocols through `Sessions.agda` and
`ParseSessions.agda`; the original Fetch-only modules remain library APIs.

## Configurable Notify pipeline depth (2026-10-14)

The executable accepts independent Fetch and Notify bounds:

```sh
Main FILE [K_FETCH]
Main --notify FILE [K_NOTIFY]
Main --interleaved FILE [K_FETCH [K_NOTIFY]]

# Use the audited prototype's request-count limits:
/tmp/leios-replay-build/Main --notify /tmp/notify-session.txt 1000
/tmp/leios-replay-build/Main --interleaved /tmp/leios-replay-20261014/interleaved.txt 150 1000
```

Defaults remain **Fetch 4, Notify 1**. A single interleaved bound still applies
to Fetch. Bounds are nonnegative decimal integers; malformed or extra arguments
print usage. Notify zero disables requests but permits an empty prefix or Done.

`LeiosNotifyPipeline.agda` supplies a safe specification parameterized by depth
and role. Each session is either `openN n`, counting outstanding requests, or
closed. RequestNext increments `n` only below the bound. Any of the four
notification kinds decrements it only when positive. Done requires zero and
closes permanently. Client commands are Send and responses Recv; server commands
are Recv and responses Send. All other transitions reject. EOF may leave pending
requests. Each interleaved session has its own counter, and diagnostics display
that count. Payload validity is outside this model; RequestNext identifies no
hash, so credits do not require a hash FIFO.

`Sessions.modelWithDepth` and `checkWithDepth` pass the two bounds to their
respective components. `SessionReport.reportWithDepth` and
`reportNotifyWithDepth` expose them to the CLI. Original `model`, `check`,
`report`, and `reportNotify` calls retain depth-one Notify defaults.

**Proof scope:** the original `LeiosNotifySession` and `NotifyBridge` remain
unchanged. `depth-one-step` proves transition agreement under the state embedding;
`depth-one-traces` proves bidirectional trace equivalence between the original
machine and the new model at depth one. The decider and heterogeneous product
are certified for every bound. There is no PTree correspondence theorem for
larger depths: the existing `LeiosNotifyP` peers still alternate at depth one.
This extension checks bounded pipelined wire order, not prototype byte budgets,
shared application state, or the composed node.

Mixed and standalone Notify rejection reports binary-search prefix membership
using prefix closure, then retrieve the preceding accepted state. This reduces
the number of repeated prefix decisions from linear to logarithmic in the event
count; parsing, each decision, and product projection still have their own cost.
The original Fetch-only reporter retains its sequential scan.

Validation includes `NotifyPipelineTests.agda` for fill/refill/drain, both roles,
overflow, underflow, busy Done, closed sessions, zero, prefixes, session isolation,
independent bounds, and diagnostics. The old bridge tests still check with
`agda --safe`. Compiled CLI tests cover legacy calls, malformed arguments,
mixed bounds, and acceptance of 1,000 requests versus rejection of the 1,001st.

The requested latest test input was
`/home/rye/YE_Workspace_Research/Workspace_IOG/Tests_Experiments/cardano-node-20261014.log`.
Normalization produced **3,621 sessions and 73,271 events** in
`/tmp/leios-replay-20261014`: 1,682 Fetch sessions and 1,939 Notify sessions.
There are no normalized Notify RequestNext records. At Fetch 150 / Notify 1,000,
the full interleaved checker rejects at global event **3,329**, session **67**:
a received BlockAnnouncement with outstanding count zero. Its preceding 3,328
events accept. Prefix closure therefore rules out acceptance of the complete
normalized stream, regardless of later events. No requests were synthesized;
this finding does not by itself establish a prototype violation or identify why
request records are absent from the log.

## LeiosNotifyP and mixed-protocol replay (2026-10-13)

This section describes the original depth-one reference and initial extension.
The executable now uses the configurable model above.

**Implemented:** `LeiosNotifySession` models the existing depth-one
`LeiosNotifyP` control flow. `Sessions` folds Fetch and Notify specifications
into one heterogeneous product; `ParseSessions` routes each event using its
manifest entry. The older Fetch-only modules remain available as library APIs.
The CLI now uses `SessionReport` for interleaved input.

| Current state | Client event | Server event | Next state |
|---|---|---|---|
| idle | Send RequestNext | Recv RequestNext | busy |
| busy | Recv notification | Send notification | idle |
| idle | Send Done | Recv Done | closed |

A notification is one of `BlockAnnouncement`, `BlockOffer`, `BlockTxsOffer`,
or `Votes`. All other transitions reject. In particular, repeated requests,
unsolicited notifications, Done while busy, and events after Done reject.
The machine has no silent transitions; finite successor enumeration and
trivial τ accessibility give a total trace decider. Empty traces and outstanding
requests at EOF accept as prefixes. This reference model has exactly one
outstanding request; `LeiosNotifyPipeline` now supplies the executable's
independently configurable Notify bound.

The mixed adapter preserves the original tracer namespace on **every event
row**, in both the global stream and per-session files. For example:

```text
sessions notify:client fetch:client
0 LeiosNotify.Remote.Send.RequestNext
1 LeiosFetch.Remote.Send.BlockRequest ab 7
0 LeiosNotify.Remote.Receive.BlockOffer cd 8 20
1 LeiosFetch.Remote.Receive.Block ab 20
```

Per-session files omit only the leading numerical session id. The namespace
identifies protocol, wire direction and message kind without consulting the
manifest. `Receive` corresponds to the legacy `Recv`; both Notify request
namespace spellings (`RequestNext` and `NotificationRequestNext`) are accepted.
The parser rejects a namespace belonging to another protocol, including shared
message names such as Done. The manifest still assigns each independent state
machine its protocol and role. Legacy `Send/Recv Message` input remains valid,
and the Fetch-only adapter retains its previous output format.

The normalized Notify payload grammar below uses the legacy direction/message
notation; namespace-form rows carry exactly the same trailing payload fields:

```text
<Send|Recv> RequestNext
<Send|Recv> BlockAnnouncement -
<Send|Recv> BlockAnnouncement <ebHash> <ebSlot> <ebBodySize>
<Send|Recv> BlockOffer <ebHash> <ebSlot> <ebBytesSize>
<Send|Recv> BlockTxsOffer <ebHash> <ebSlot>
<Send|Recv> Votes -
<Send|Recv> Votes <rbHash>:<voterId>,<rbHash>:<voterId>,...
<Send|Recv> Done
```

Hashes are hexadecimal naturals; slots, sizes and voter ids are decimal
naturals. `-` denotes an absent announcement header or an empty vote list.
The parser retains these fields, but control transitions do not constrain them:
RequestNext names no hash, and this replay does not validate blocks or votes.

For example, the following is one accepted product trace:

```text
sessions notify:client fetch:client notify:server
0 Send RequestNext
1 Send BlockRequest ab 7
2 Recv RequestNext
0 Recv BlockOffer cd 8 20
2 Send Votes -
1 Recv Block ab 20
```

Manifest entries are `fetch:client`, `fetch:server`, `notify:client` and
`notify:server`. Bare `client` and `server` retain their old Fetch meaning.
Protocol-inappropriate messages and undeclared session ids are parse errors.
Each Notify session has its own idle/busy/closed state; a notification cannot
consume another session's request. Product trace membership is decided using
the same proved projection equivalence as Fetch-only interleaving.

Compile `Main.agda` as described below, then run:

```sh
python3 -I tools/trace-replay/leios_adapter.py LOG /tmp/leios-mixed
/tmp/leios-replay-build/Main --interleaved /tmp/leios-mixed/interleaved.txt 4
/tmp/leios-replay-build/Main --notify /tmp/notify-session.txt
```

Standalone Notify input starts with `role client` or `role server` and has
untagged events. Its report uses the product format with one session. Existing
`Main FILE [K]` and `leiosfetch_adapter.py` remain Fetch-only entry points.
The mixed adapter groups by `(connectionId, role, protocol)` and generation,
assigns ids in first-event order, and preserves raw-file ordering. Done ends
only its own protocol/role session; NewMux closes **all protocols and roles**
on that connection. Mux Dead still does not split. Mixed per-session filenames
include the protocol, and `index.tsv` appends a protocol column. The source-map
and rejection-index conventions remain unchanged.

**Correspondence with the original peers:** `NotifyBridge.client-bridge` and
`NotifyBridge.server-bridge` establish both directions for the existing
`LNPclientStClient` and `LNPserverStClient`, at `replayParams`, link 0, direction
`hi`. They retain wire direction and all six message kinds, while erasing all
notification payloads and omitting local API/done events. Completeness chooses
canonical payloads; it does not reconstruct logged hashes, slots, sizes, or
votes. Unlike the Fetch client bridge, this proof needs no replacement peer.
It is a standalone-peer result, not a bridge to `NodeLogicL`, a shared store,
or the composed node/network. The proof uses `--guardedness` and typechecks
with command-line `agda --safe`; the local spec, product and parser use `--safe`.

**Log coverage matters:** the adapter never synthesizes RequestNext. The
available `govstall-a1-20260927-full-head10000.log` extract contains 461 Notify
records and no Notify RequestNext records. Normalization yields 87 total
Fetch/Notify sessions; strict replay rejects at global event 2, session 1,
a received BlockAnnouncement at raw line 271. This is not sufficient evidence
of an implementation violation: the input is an extract and lacks the request
evidence required by this model. The locally inspected prototype also has
pipelined Notify peers, whereas Agda `LeiosNotifyP` is depth-one. Bounded pipelining is now supported by the replay extension above. A
correspondence proof for the pipelined prototype and an observation model for
missing requests remain separate work.

Validation includes `NotifyTests.agda` (positive witnesses, negative controls,
protocol parsing and interleaving), `NotifyBridge.agda` and explicit client/server trace witnesses in
`NotifyBridgeTests.agda` checked with `--safe`,
existing Fetch decision/product tests and both Fetch bridge endpoints, adapter
selftests, and compiled CLI integration tests:

```sh
python3 -I tools/trace-replay/leios_adapter.py --selftest
python3 -I tools/trace-replay/test_notify_replay.py /tmp/leios-replay-build/Main
```

## Run (Fetch-only normalization)

From `src/`, compile outside the repository:

```sh
agda --compile --compile-dir=/tmp/leios-replay-build Cardano_network/Replay/Main.agda
```

From the repository root, normalize one node's raw log and check the single
interleaved stream:

```sh
python3 -I tools/trace-replay/leiosfetch_adapter.py LOG /tmp/leios-replay-log
/tmp/leios-replay-build/Main --interleaved /tmp/leios-replay-log/interleaved.txt 4
```

The existing `Main FILE [K]` mode and per-session adapter files remain available.
`K` defaults to 4 in both modes. The CLI prints accepted, rejected, or parse-error
reports; its process exit status does not encode these verdicts.

## Format and session identity

```text
sessions client server client
0 Send BlockRequest ab 5
1 Recv BlockRequest cd 6
2 Send BlockRequest ef 7
1 Send Block cd 100
0 Recv Block ab 100
```

Session ids are zero-based positions in the header. Undeclared ids are parse
errors. Local event fields use the same syntax as `Parse.agda`, including
hexadecimal hashes and decimal slots and sizes. An empty log is `sessions`
with no events.

The adapter assigns ids in first-event order. Id `i` corresponds to `sNNNN`
in `index.tsv`, where `NNNN = i + 1`. The manifest thus fixes a role for each
connection/role/generation. A new generation is allocated after `Done` or at a
`Net.Mux.Remote.NewMux` boundary. Both roles of that connection end at `NewMux`;
`Net.Mux.Remote.State Dead` is not a boundary. Distinct peers and duplex roles
have separate state, and a reused connection never inherits the old queue.

`interleaved.txt` preserves raw-file event order, rather than concatenating
sessions or sorting timestamps. Its companion `interleaved.src` contains
`raw-line timestamp session-id` for each event. `index.tsv` retains the
connection id, role, first/last timestamps and `done`/`mux`/`eof` end reason.
A rejection reports the global 1-based event index, the zero-based session id,
and that component's state after the preceding accepted global prefix. Event
index `i` maps to normalized line `i + 1` and row `i` of `interleaved.src`.
Mixed/Notify rejection diagnostics binary-search prefix membership; the
Fetch-only reporter retains its sequential prefix scan.

## Scope of the result

This model is independent interleaving of session specifications. The manifest
and adapter establish session identity and boundaries; the Agda model does not
certify the raw-log adapter, mux lifecycle, or the provenance of those tags.
An externally relabelled stream may describe different sessions.

The existing PTree bridges still apply to individual projections: the existing
LeiosFetchP server with serving threads/store, and the new FIFO LeiosFetchPipe
client. There is no new PTree bridge to the composed node or network here.
In particular, independent server witnesses do not establish a common body
store, and acceptance does not verify shared node logic, payload validity,
cross-node send/receive matching, or delivery liveness. Adding shared state and
synchronisation requires a stronger model and additional bridge proofs.

## Verification

```sh
cd src
agda Cardano_network/Replay/InterleavedTests.agda
agda Cardano_network/Replay/NotifyTests.agda
agda Cardano_network/Replay/NotifyPipelineTests.agda
agda --safe Cardano_network/Replay/NotifyBridgeTests.agda
agda Cardano_network/Replay/Main.agda
```

From the repository root:

```sh
python3 -I tools/trace-replay/leiosfetch_adapter.py --selftest
```

The Agda tests include explicit positive product witnesses and negative
refutations, independent client bounds, cross-session isolation, server silent
steps, mixed roles, wrong hashes, closed sessions, new generations, valid
unfinished prefixes, malformed manifests, unknown tags and empty logs.
Adapter tests check order, exact agreement of each projection with the existing
session files, source mappings, `NewMux`/`Dead`, post-Done generations and empty
logs.
