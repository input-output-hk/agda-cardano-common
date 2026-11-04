# Controlled LeiosNotify lookahead experiments

This harness exercises the actual pinned `leiosNotifyClientPeerPipelined` and
`leiosNotifyServerPeerLookahead`, through `runPipelinedPeerWithLimits` and
`runLookaheadFixedSenderPeerWithLimits`. It supports T3.2 and T3.3
in the [numbered plan](../../../../../docs/specs/leiosnotify-pipe-lookahead-plan.md).
The separate completion-history, quiet profiling and Nat audit fixtures below
support T5.1.1/T5.1.2/T5.2.1/T5.2.2; the bounded Agda checker and historical result
records also support the T4 proof stages.

This directory lives beside the replay bridges and certificates under
`Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/`. Run the commands below
from the repository root. Historical result JSON files retain the source paths
and hashes recorded at the time of each run, before the tooling was relocated
from `tools/leiosnotify-lookahead/`; their bytes are preserved.

The baseline peer/driver entry points stay unchanged; separately named candidate
and diagnostic copies below are recorded explicitly. The build exports source from
consensus `2416493bfdbe93b761b3a4bb1ccf2b4a913e5e4b` and typed-protocols
`9b4627221ae5d649f2303c6926a8dba3f9934658`, and checks a locked network archive
for `2f1c154f248659b89523d5679ca532f442e7ed2a`. Core peer/driver file hashes must
match the model's existing
[`sources.json`](../../../LeiosNotifyPipeLookahead/sources.json).

## Scenarios

| Case | Controlled schedule and observed outcome | Agda comparison |
| --- | --- | --- |
| `idle-quit` | Initial Left () decision; Quit/Done with no RequestNext | `NodeDriverTests.idle-source` |
| `cancel-blocked-next` | One admitted request; `next` stays blocked; Quit produces Canceled then Done | `shutdown-source` |
| `delayed-send-prefix` | Server Receive RequestNext and client Receive Offer precede their delayed Send records; normal handler succeeds; peers then interrupted | `delayed-source` wire prefix |
| `selected-normal` | Exact Offer selected before Quit, channel commit held until the original Quit Effect completed; normal packet sent after the true flag | `late-normal-source` |
| `before-quit-flag` | Two queued normals sent FIFO after Recv Quit but before the held Quit Effect sets the flag | Checked fresh paired node/native certificate, all 10 captures |
| `excessive` | Synthetic channel writer supplies 1001 requests with no eligible notifications; request 1001 throws the actual excessive-requests exception | Checked fresh node-server/native-server certificate, all 10 captures; not an honest paired-client run |
| `terminate-at-capacity` | Actual client reaches depth 1000 with no replies; termination interrupts its STM wait and drains 1000 cancellations | Checked fresh paired node/native certificate for each exact 4004-row capture |
| `arrived-before-publication` | At depth 1000, one normal receiver increments arrived; its result publication is held; client selects blocking Collect; termination waits for publication, then 999 cancellations drain | Checked fresh paired node/native certificates for each 4004-row capture, plus reachable held-publication checkpoints |

In the publication experiment, an observer wraps the original Receiver Effect
and pauses after its action returns but before ReceiverDone reaches the driver's
publication path. Another observer records the selected blocking Collect. The
controller requests termination while the result is held, records that Quit has
not occurred, then releases publication. The run completes. This demonstrates a
scheduling dependency; it does not establish a permanent deadlock or a bound on
real-world shutdown latency.

## Observation and scope

STM barriers control schedules without sleeps. The tracer assigns a sequence
number atomically when it appends each record. Raw TSV includes case, sequence,
actor, record kind, exact test payload and Haskell thread ID. `Send` and `Recv`
come from the original limits driver's hooks. Channel commit/decode retain their
original ordering relative to those hooks. Instrumentation also records callback,
controller, handler and peer-effect boundaries; these are separate from wire rows.

The transport uses the original connected in-memory channels and the original
`codecLeiosNotifyId`, whose payloads are typed `AnyMessage` values. Limits wrappers
are active, with the existing test size of one per message. These experiments do
not validate CBOR bytes, real sockets, mux framing, codec fragmentation, byte-size
limits or time-limit expiry.

The harness supplies controlled callback results. Normal continuations use depth
1000 and termination returns unit. For the small cases, checkDone blocks after a
specified number of continuations until termination. The capacity cases keep
returning Right 1000 and exercise the peer's own full-pipe/arrived guard.
Admission/enqueue/next callbacks reproduce the equality guard, credit consumption
and FIFO behavior in the model; they do not execute the full node's forecast,
governor, announcement pump, ledger or relay-validation code. The normal handler
reports a successful supplied outcome. No unexpected-Canceled node-handler fault
is asserted reachable from an honest fresh pair.

The build replaces only the large `Ouroboros.Consensus.Util.IOLike` import surface
with a five-name re-export shim. Those implementations come from the unchanged
pinned `NormalForm.StrictTVar` and `NormalForm.Invariant` modules. Expensive
NoThunks invariants retain their source default of disabled. The shim and all
exported source hashes are recorded. Peers and drivers are compiled locally,
rather than trusting the existing cached consensus/network build.

[`ExportFixtures.agda`](../ExportFixtures.agda)
imports the checked node witnesses and serializes their actual `wireRows` lists.
The runner checks that module using `agda --safe`, then evaluates `rendered` using
Agda's `DefaultCompute` normalizer. Expected rows are derived from the model,
not copied into Python. The comparison preserves endpoint, Send/Recv direction,
order, multiplicity and every displayed payload field. Callback/handler/hook rows
are deliberately outside this wire profile. Their full timing correspondence is
not inferred from wire equality. Dropping Canceled, changing an Offer size, and
moving a Receive after its matching Send are negative controls for the comparison.

The first four comparisons establish that these observed **wire histories** equal
particular histories with checked source and native trace witnesses. They are
finite sampled implementation evidence, not a universal Haskell refinement
theorem. The interrupted case remains a prefix. This runner is not an exhaustive
replay checker for arbitrary node logs and does not change existing CLI modes.

## Run

The supplied [`build-packages.json`](build-packages.json) records the coherent
installed package roots used with GHC 9.6.7. This is a local experiment build
manifest, not a portable dependency installer. Another environment can supply its
own manifest with `--build-packages` and `--package-db`. Dependencies are not
installed and the supplied git checkouts are not modified.

Obtain the pinned network archive:

```sh
curl -L --fail \
  https://codeload.github.com/IntersectMBO/ouroboros-network/tar.gz/2f1c154f248659b89523d5679ca532f442e7ed2a \
  -o /tmp/leiosnotify-network-2f1c154.tar.gz
```

Its SHA-256 must be
`1ba2548f87248d2561d544d09f75e5856464d7936501737a71396ffba8054db3`.
The consensus and typed-protocols git repositories must contain their pinned
revisions; their checked-out branches can differ because export uses git objects.

From this repository:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/run.py \
  --consensus /path/to/ouroboros-consensus \
  --typed-protocols /path/to/typed-protocols \
  --network-archive /tmp/leiosnotify-network-2f1c154.tar.gz
```

The runner creates a fresh `/tmp/leiosnotify-schedules-*` directory. An explicit
`--out` must be a new directory outside the repository. It builds the harness,
checks/normalizes the Agda fixtures, and runs all eight cases five times at each
of `+RTS -N1` and `+RTS -N2`. Each case has a ten-second fixture timeout; expiration
is reported as a harness failure, not a protocol-rejection verdict.

Artifacts include source hashes, GHC command, package database dump, Agda checking
and normalization records, derived `model.tsv`, each raw schedule TSV, and
`report.json` with assertions and negative-control results. A source-only observed
schedule with no model-comparison flag must not be presented as an Agda-certified
paired trace.

## Recorded run

On 3 November 2026, GHC 9.6.7 and Agda 2.8.0 passed all 80 scheduled experiments,
all 40 applicable Agda wire-history comparisons, and all 30 comparison negative
controls. The [compact result record](results-20261103.json) includes source
revisions, fixture/exporter/runner hashes, per-case counts and full report hash.
Raw TSV, source/build manifests and Agda normalization responses are under
`/tmp/leiosnotify-haskell-final-20261103/`. No allocation, residency or shutdown
latency measurements were taken.

The [T3.3 follow-up record](results-t33-20261103.json) adds the remaining 40
comparisons using 22 distinct Agda certificates. All 80 captured wire histories
now match checked model witnesses: 70 paired histories (including interrupted
prefixes) and 10 adversarial server-only histories. All new checking and
normalization processes exited zero, with a maximum sampled RSS of 1.15 GiB
and zero budget failures. Seven kernel schedule controls pass, and strict scans
of the four new helpers and all 1003 generated Agda sources have zero findings.
These memory measurements concern Agda verification, not Haskell peer residency.
Full follow-up artifacts are under
`/var/tmp/leiosnotify-t33-20261103/verified/`. The original result record and raw
Haskell captures are preserved unchanged.

## Certify the remaining captured schedules

`certify.py` proposes finite schedules for `before-quit-flag`, `excessive`,
`terminate-at-capacity` and `arrived-before-publication`. It reads the original
captures without changing or sorting their rows. For every distinct proposed
schedule/wire history, Agda checks the source execution, exact raw wire equality
and native trace realization. Identical full schedules and wire rows can share
a certificate; distinct interleavings are checked separately.

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/certify.py \
  --captures /tmp/leiosnotify-haskell-final-20261103 \
  --out /var/tmp/leiosnotify-runtime-certificates
```

A single captured case can be checked with:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/certify.py \
  /tmp/leiosnotify-haskell-final-20261103/N1-0.tsv \
  --case terminate-at-capacity \
  --out /var/tmp/leiosnotify-capacity-certificate
```

Use a fresh output directory outside the repository. The `excessive` case proves
a fresh **server-only** run: 1000 admissions followed by failure on request
1001. It does not fabricate an honest client. The other three cases prove
combined node-policy runs from the initial state and exact native paired traces.
The publication case additionally proves a reachable held-result checkpoint:
main control is blocking Collect, the receiver is awaiting publication,
`arrived = 1`, and termination is requested at that same state. This supplies
model reachability consistent with the controlled fixture; it is not a proof of
every observer/callback timing in Haskell.

The Python planner supplies untrusted instruction data. `RuntimeCheck.sound`
constructs independent model evidence only when evaluation succeeds; local
reflexivity checks bind each part to the supplied original rows, and a proved
concatenation lemma preserves the whole history. Agda's `--safe` checking and
DefaultCompute output comparison are both required for success. A planner,
checker, timeout or memory-budget failure is inconclusive, not protocol rejection.
This tool supports these controlled captures; it is not an exhaustive checker
for arbitrary production logs. Existing CLI modes are unchanged.

Each Agda child runs serially with a 2 GiB GHC heap limit, a sampled 3 GiB RSS
watchdog, timeouts and interruption cleanup. The
[OOM diagnosis](../../../../../docs/notes/leiosnotify-pipe-lookahead-oom.md) records the
previous failures and measured improvement. These limits are implemented by
`certify.py`; they do not apply automatically to direct Agda invocations or the
original `run.py` harness.

To repeat the bounded prerequisite/prefix measurements and exercise both memory
guards deliberately:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/certify.py \
  /tmp/leiosnotify-haskell-final-20261103/N1-0.tsv \
  --diagnose --out /var/tmp/leiosnotify-memory-diagnosis
```

This checks the shared instance, seven schedule guard controls and original
32/128/512-row prefixes, then expects isolated failures under deliberately tiny
RSS and heap budgets. It does not run a full captured-case certificate.

Artifacts include generated `.agda` proofs, source hashes, checking logs,
normalization JSONL, per-process resource measurements, `model.tsv`, and a
`report.json` tying each verdict to its original capture hash. `progress.json`
records completed cases if the batch is interrupted. Generated artifacts are
kept outside the repository; prefer disk-backed `/var/tmp` when `/tmp` quotas
are tight. Resource values are sampled RSS, not cumulative GHC allocations.

## Check property modules with the same limits

`check_agda.py` applies the same bounded Agda execution to ordinary repository
checking roots, without needing a runtime capture. Module arguments are relative
to `src/`. All roots are checked serially with `--safe`, a 2 GiB heap limit,
sampled 3 GiB RSS watchdog and a timeout. The sequence stops on the first failed
check; a memory/timeout failure is inconclusive.

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/check_agda.py \
  Cardano_network/Replay/LeiosNotifyPipeLookahead/ConservationTests.agda \
  Cardano_network/Replay/LeiosNotifyPipeLookahead/ConservationNativeTests.agda \
  --out /var/tmp/leiosnotify-conservation-checks
```

Source hashes, checking logs, resource JSON and `report.json` go outside the
repository. Prefer disk-backed `/var/tmp`. The
[T4.1.1 record](results-t41-20261103.json) covers the new general server/transport,
node-policy and native conservation theorems; the
[conservation note](../../../../../docs/notes/leiosnotify-pipe-lookahead-conservation.md)
states the exact finite-safety scope and remaining progress/resource obligations.

The [T4.1.2 shutdown record](results-t412-20261103.json) covers nine additional
modules: persistent shutdown/publication, corrected client work inventory,
physical Done origin and exact role-specific Done guarantees. Its two bounded
roots are `ShutdownTests.agda` and `ShutdownNativeTests.agda` under
`Cardano_network/Replay/LeiosNotifyPipeLookahead/`. The
[shutdown note](../../../../../docs/notes/leiosnotify-pipe-lookahead-shutdown.md)
includes the checking command and fresh counterexamples to the stronger empty
hook/client/network interpretations of a Done event.

The [T4.2.1 record](results-t421-20261103.json) covers eight more safely checked
modules for hidden accessibility and shutdown operation bounds. Its roots are
`SchedulingTests.agda` and `SchedulingNativeTests.agda` under the same Replay
directory. The [scheduling note](../../../../../docs/notes/leiosnotify-pipe-lookahead-scheduling.md)
gives the bounded command, exact native/projected-driver scopes, component work
distinctions and the remaining T4.2.2 progress assumptions.

The [T4.2.2 record](results-t422-20261103.json) covers seven safely checked modules
for conditional model/runtime completion and a concrete final-Done progress
instance. Its checking roots are `ProgressTests.agda` and
`ProgressNativeTests.agda` in the same directory, using the same bounded wrapper.
The [progress note](../../../../../docs/notes/leiosnotify-pipe-lookahead-progress.md)
separates structural progress from scheduler/IO responsiveness, failures and
premature EOF. General fresh paired structural progress remains T4.2.2.3.

The [T4.2.2.3 component record](results-t4223-20261104.json) covers eight more
safely checked modules for general fresh server drain and client phase/reply
invariants. Its roots are `ServerDrainTests.agda` and
`ServerDrainNativeTests.agda` under the same directory and bounded wrapper.
The [server-drain note](../../../../../docs/notes/leiosnotify-pipe-lookahead-server-drain.md)
states the universal server theorem, the actual twenty-two-operation full
example, and the remaining general client/packet/Done connection (T4.2.2.3.3).

The [T4.2.2.3.3 record](results-t42233-20261104.json) covers nine safely checked
modules completing the full fresh paired structural-progress proof. Its roots
are `PairedDrainTests.agda` and `PairedDrainNativeTests.agda` under the same
directory and bounded wrapper. The
[paired-drain note](../../../../../docs/notes/leiosnotify-pipe-lookahead-paired-drain.md)
states the general source/native/runtime endpoints, inhabited examples and
unreachable-state controls, and retained external runtime assumptions. Next is
T4.3.1 completed-bookkeeping/flush-count resource analysis.

The [T4.3.1 record](results-t431-20261104.json) covers six safely checked modules
for universal completion/work conservation, exact source/paired/native flush
counts and an arbitrary-length low-occupancy production-policy family. Its roots
are `CompletionTests.agda` and `CompletionNativeTests.agda` under the same Replay
directory and bounded wrapper. The
[completion-cost note](../../../../../docs/notes/leiosnotify-pipe-lookahead-completion-cost.md)
states the exact n-flush/n+12-operation family and all-state natural resource
certificates, with runtime representation/heap/time conclusions kept separate.
T4.3.2 resource/representation results follow below.

T4.3.2 adds seven safely checked modules for conservative fixed-depth live-resource
bounds, exact pre-Quit notification accounting, a fresh full-pipe Quit/native
marker control and unbounded historical deferred indices. The bounded roots are
`ResourceFixtures.agda`, `Representation.agda` in the protocol folder, and
`ResourceNativeTests.agda`; the fixture/native roots are in the Replay folder.
The [resource note](../../../../../docs/notes/leiosnotify-pipe-lookahead-resource-bounds.md)
gives the exact command and assumptions. The
[result record](results-t432-20261104.json) records final source hashes, audits,
resource reports and the stopped earlier proof expansion. T5.1.1 follows below.

## Low occupancy completion histories

`CompletionHistory.hs` and `completion_history.py` implement T5.1.1. They reuse
the pinned source export, package settings and limits drivers, while streaming
wire rows and keeping only strict small fixture counters. The original eight
schedule fixture remains `Main.hs`; `run.py` retains its existing build defaults.

From the repository root, with the pinned dependency objects and archive ready:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/completion_history.py \
  --consensus /path/to/ouroboros-consensus \
  --typed-protocols /path/to/typed-protocols \
  --network-archive /tmp/leiosnotify-network-2f1c154.tar.gz \
  --out /var/tmp/leiosnotify-completion-history
```

The default sweep uses 0, 1, 10, 100, 1000 and 10000 exchanges, constant callback
depths 1/1000, RTS capabilities 1/2, and three repetitions. Each observed run has
a wire-only control omitting peer-counting wrappers. The fixture checks exact
FIFO offer fields and counts registered receivers, collections, server job
registrations, entered flushes and successful flush continuations. Private driver
TVars are not sampled. Depth 1000 uses controlled callback readiness and retains
the optional-Collect race; observed receiver work before Quit stays at most two.
Depth 1 uses blocking Collect and stays at most one before Quit.

The recorded sweep passed all 144 runs, all 72 endpoint-stream comparisons and
five malformed-capture controls. Each n-exchange observed run registers n server
jobs with zero pre-Quit flushes, then completes n successful flushes. The
[result record](results-t511-20261104.json) and
[completion-cost topic](../../../../../docs/notes/leiosnotify-pipe-lookahead-completion-cost.md#pinned-haskell-history-experiment)
state the exact observation boundaries. Full artifacts are under
`/var/tmp/leiosnotify-t511-20261104/final/`.

The Python runner independently validates each session's original wire rows and
snapshots; it does not generate new Agda certificates for these captures.
Wire-only controls compare the four endpoint/direction streams, not their global
interleaving. This count experiment is not a baseline timing or residency
benchmark. The original eight-schedule harness was also recompiled through the
unchanged build defaults and passed at `-N1`/`-N2`, including its six corruption
controls. That regression used the earlier checked `model.tsv` and verified the
exporter's unchanged source hash; it did not rerun Agda normalization.
The quiet profiling section below accounts for logging/observer overhead.

## Quiet completion profiles

`CompletionProfile.hs` and `completion_profile.py` implement T5.1.2. They keep
aggregate wire/handler checks without streaming packet rows or wrapping peers.
The baseline compiles the original pinned peer/Core/driver/limits sources.
A separate diagnostic build exports an additional fixed-sender entry point that
exposes a getter for the existing waiting/completed TVars once at initialization.
Its generated patch preserves every original function body and counter update;
it is a measurement aid in exported sources, not a protocol repair.

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/completion_profile.py \
  --consensus /path/to/ouroboros-consensus \
  --typed-protocols /path/to/typed-protocols \
  --network-archive /tmp/leiosnotify-network-2f1c154.tar.gz \
  --depths 1 1000 \
  --out /var/tmp/leiosnotify-completion-profiles
```

The sweep builds baseline/diagnostic variants at `-O0` and `-O2`, using 0, 1000,
10000 and 100000 exchanges, RTS `-N1`/`-N2`, and five repetitions. Both modes hold
the final callback until all replies were handled and server Send records ran.
The diagnostic also waits for all sender retirements before sampling counters.
A major GC precedes the pre-Quit live-heap sample. The monotonic timer covers
release of the final callback through both driver returns; packet output and
explicit major GCs are outside that interval. Allocation is a cumulative RTS
counter difference through a post-driver major GC, including fixed controller
and cleanup overhead. Checkpoint live heap is whole-fixture data, not an
allocation attribution to one protocol object. Forced pre-GC can perturb the
subsequent timing even though its duration is excluded.

The [profiling result](results-t512-20261104.json) and
[maintained topic](../../../../../docs/notes/leiosnotify-pipe-lookahead-completion-cost.md#quiet-baseline-profiles-and-private-counters)
record baseline statistics separately from diagnostic samples. Four corrupted
measurement controls test negative time, missing major GC, invalid allocation
delta and fabricated private counters. Generated `ghc-command.json` records the
effective optimization, diagnostic and RTS flags and agrees with
`build.log.resources.json`. Full artifacts are under
`/var/tmp/leiosnotify-t512-20261104/final-v2/`.

The model and original Haskell source checkouts are unchanged. No new Agda trace
certificates are generated for these profiles. T5.2.1's separate attribution
experiment follows below; no repair is introduced by these fixtures.

## Nat heap and arithmetic audit

`NatAudit.hs`, `NatArithmetic.hs` and `nat_audit.py` implement T5.2.1. The runner
exports the pinned sources and appends a copied server with a callback saving
its busy-loop Nat root. A second copy forces that argument at each entry.
Original server functions remain unchanged; the fixed-sender diagnostic getter
is the same copied entry point used in T5.1.2. No upstream checkout is modified.

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/nat_audit.py \
  --consensus /path/to/ouroboros-consensus \
  --typed-protocols /path/to/typed-protocols \
  --network-archive /tmp/leiosnotify-network-2f1c154.tar.gz \
  --out /var/tmp/leiosnotify-nat-audit
```

The default sweep has 252 fresh-process heap cases: seven history sizes
(0, 1, 2, 10, 1000, 10000, 100000), depth 1000, O0/O2, N1/N2, three repetitions,
and three cases per configuration: nonforcing inspection, checkpoint forcing,
and a strict busy-loop diagnostic. It reuses `CompletionProfile.hs` as a generated
helper with only its module name changed. All replies must be handled and
retired before the held pre-Quit checkpoint. The busy argument then represents
n−1 while the driver completed counter is n. Numeric-only heap snapshots are
strictly evaluated during inspection; the saved root is released before final
GC. Raw closure sizes exclude the terminal value and are distinct from total
fixture live heap. There is no timing benchmark in this instrumented walker.

Four arithmetic processes compile against unchanged pinned Core and deliberately
forge edge inputs using `unsafeIntToNat`. Delayed overflow and bottom probes
check nonforcing heap inspection. Scalar exceptions/wraparound do not establish
that a fresh peer reaches those inputs. The strict variant is diagnostic and
may change exception timing; it is not a verified repair and does not eliminate
historical completed jobs or flush work.

The [audit record](results-t521-20261104.json) and
[maintained explanation](../../../../../docs/notes/leiosnotify-pipe-lookahead-completion-cost.md#nat-heap-attribution-and-arithmetic)
record exact shapes, controls, scalar outputs and source/build hashes. Four
corrupted heap captures are rejected by fixture validation. The primary artifacts
are under `/var/tmp/leiosnotify-t521-20261104/final-v4/`; earlier size-sampling
prototypes are superseded. The runner uses the existing heap/RSS/time guards.
No Agda source or prior count/profile fixture is changed, and no new Agda trace
certificate is generated. T5.2.2 blocking/exception/accounting tests follow below.

## Blocking, failure and credit schedules

`FailureSchedules.hs` and `failure_schedules.py` implement T5.2.2. The compiled
pinned peers, Core, typed driver and limits files are unchanged. The generated
`FixtureBase` helper is the original `Main.hs` with its module name changed.
Sender/handler wrappers and the original Quit Effect observer expose barrier
and cleanup boundaries. No strictness variant or private counter getter is used.

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/failure_schedules.py \
  --consensus /path/to/ouroboros-consensus \
  --typed-protocols /path/to/typed-protocols \
  --network-archive /tmp/leiosnotify-network-2f1c154.tar.gz \
  --out /var/tmp/leiosnotify-failure-schedules
```

The default sweep runs 14 scenarios at O0/O2 and N1/N2, three times each: 168
fresh processes. They cover blocked next, held/released/canceled/failing sends,
faults in admission/next/checkDone/handler acquisition/handler body, held handlers,
full-depth Quit with an empty or full eligible queue, and ordinary credit/queue
drain. Optional `--cases`, `--optimizations`, `--capabilities` and `--repeat`
select a smaller diagnostic sweep. Closed gates and observed `BlockedOnSTM`
thread states establish named finite checkpoints; timeouts are inconclusive.

The independent Python validator checks exact wire counts, fault/cancel versus
success outcomes, barrier ordering, cleanup of exposed workers and each credit/
queue ledger. After both endpoint scopes exit, actual FIFO contents are checked
against the ledger. The fixture's eligibility, callback and in-memory identity
codec contracts do not execute the complete node pump/ledger/governor or certify
whole-connection cleanup. Opposite endpoints are canceled explicitly after a
fault; local driver cleanup does not establish automatic remote cancellation.

See the [progress topic](../../../../../docs/notes/leiosnotify-pipe-lookahead-progress.md#pinned-haskell-blocking-and-failure-experiments)
for the maintained explanation, including remaining eligible notifications at
Done, the role-local handler boundary and the runtime theorem's premises. The
[result record](results-t522-20261104.json) preserves all six source pins,
aggregate ledgers, controls and hashes. Primary artifacts are under
`/var/tmp/leiosnotify-t522-20261104/final/`. Four corrupted captures fail fixture
validation; no new Agda/native trace certificates or arbitrary-log rejection
results are generated. Next is T5.3 evidence classification.


## Targeted T5 reproducers

The [T5.3 classification](../../../../../docs/notes/leiosnotify-pipe-lookahead-source-audit.md#t53-evidence-classification-and-repair-decision)
links each finding to its trigger and scope. The
[audit record](results-t53-20261104.json) preserves 24 fresh reproducer commands,
executable/capture hashes and validator outcomes. These reuse earlier builds;
no independent compilation or new statistical benchmark is claimed.

To reconstruct a small sweep from the pinned dependency inputs, set these paths
and choose a **new output directory** for every invocation:

```sh
LEIOS_TOOLS=src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools
LEIOS_CONSENSUS=/path/to/ouroboros-consensus
LEIOS_TYPED=/path/to/typed-protocols
LEIOS_ARCHIVE=/path/to/network-2f1c154.tar.gz

python3 -I -B "$LEIOS_TOOLS/completion_history.py" \
  --consensus "$LEIOS_CONSENSUS" --typed-protocols "$LEIOS_TYPED" \
  --network-archive "$LEIOS_ARCHIVE" --counts 1 10 --repeat 1 \
  --out /var/tmp/leiosnotify-small-history

python3 -I -B "$LEIOS_TOOLS/nat_audit.py" \
  --consensus "$LEIOS_CONSENSUS" --typed-protocols "$LEIOS_TYPED" \
  --network-archive "$LEIOS_ARCHIVE" --counts 2 --repeat 1 \
  --optimizations O2 --capabilities 1 \
  --out /var/tmp/leiosnotify-small-nat

python3 -I -B "$LEIOS_TOOLS/failure_schedules.py" \
  --consensus "$LEIOS_CONSENSUS" --typed-protocols "$LEIOS_TYPED" \
  --network-archive "$LEIOS_ARCHIVE" --optimizations O2 --capabilities 1 \
  --repeat 1 --out /var/tmp/leiosnotify-small-failures
```

The history runner also supplies both depth/capability settings and wire-only
controls; the Nat runner supplies peek/force/strict cases and scalar checks.
For one failure trigger, add `--cases held-send-release`,
`--cases held-handler-release`, or the other exact names above. These optional
small sweeps are reproduction instructions, not additional runs asserted by the
T5.3 record. The capacity-queue trigger deliberately retains depth 1000.

When retained artifacts are available, individual bounded commands are:

```sh
/var/tmp/leiosnotify-t511-20261104/final/completion-history \
  1 1 observed +RTS -N1 -M256M -K64M -RTS
/var/tmp/leiosnotify-t521-20261104/final-v4/lazy-O2/nat-audit \
  2 1000 peek +RTS -N1 -T -M256M -K64M -RTS
/var/tmp/leiosnotify-t522-20261104/final/O2/failure-schedules \
  held-send-release +RTS -N1 -M256M -K64M -RTS
```

For the Nat intervention use `force` instead of `peek`, and for the strict
comparison use `strict-O2/nat-audit` with `peek`. For the historical-growth
comparison use 10 exchanges instead of 1. The record retains exact commands for
all six fault boundaries, handler/send cancellation, queue controls, arithmetic
and the two baseline profiling samples. RTS `-T` is required by the Nat/profile
probes. Individual invocations have internal fixture deadlines; the runners
also supply process-group lifetime/RSS guards and independent capture validation.
No bare command substitutes for those validators or for an Agda certificate.

CollectOne design feasibility follows below; T6.1.2 defines its behavior
contract next. Classification itself introduces no protocol/model repair, and
the baseline remains the target for later T7 replay work.


## CollectOne design probe

`collect_one_design.py` appends a separately exported
`leiosNotifyServerPeerLookaheadCollectOne` copy to exported pinned source. Its
busy loop makes at most one optional `FlushSender` attempt on old registered
jobs before `AwaitLookahead` registers the current one. Original entry points,
Core, typed driver, limits and baseline Agda/checker targets are unchanged.

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/collect_one_design.py \
  --consensus /path/to/ouroboros-consensus \
  --typed-protocols /path/to/typed-protocols \
  --network-archive /path/to/network-2f1c154.tar.gz \
  --out /var/tmp/leiosnotify-collect-one-design
```

GHC compiles the candidate and `CollectOneProbe.hs` with the pinned API.
Eight scripted constructor paths check zero/hit/miss registration indices,
immediate Await after either poll result, and early-plus-final flush accounting.
The probe inspects one ready responder result to safely expose existential
sender endpoints. It does not execute the concurrent driver or establish that
an injected hit corresponds to an actual completed token. The Python sanity
check enumerates 210 poll/register states at B=0..8; it is not a universal proof.

The [design](../../../../../docs/specs/leiosnotify-collect-one-design.md) states the
conditional B+1 argument and warns against assuming the baseline live-work
bound for a changed candidate. The [record](results-t611-20261104.json) preserves
source, patch, effective-command and probe hashes. Primary artifacts are under
`/var/tmp/leiosnotify-t611-20261104/design-v3/`, including `candidate.patch`.
All original source bodies are checked unchanged; build/probe subprocesses use
the established heap/RSS/time guards. No Agda source is edited/rebuilt and no
concurrent behavior, heap or latency improvement is established. T6.1.2's
reference contract, T6.2 proofs and T6.3.1 runtime comparison are recorded
separately below.


## CollectOne reference contract

T6.1.2 defines the candidate's source behavior and local wire/outcome contract in
`Cardano_network/LeiosNotifyPipeLookahead/Candidates/CollectOne/Model.agda` and
`Contract.agda`. They are independent of Replay. The new witness/guard root is:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/check_agda.py \
  Cardano_network/Replay/LeiosNotifyPipeLookahead/CollectOne/ContractTests.agda \
  --out /var/tmp/leiosnotify-collect-one-contracts
```

The [behavior/observation contract](../../../../../docs/specs/leiosnotify-collect-one-design.md#t612-behavior-and-observation-contract)
explains guards, atomic retirement races, pending replies, true Quit, rejection,
fault labels and the initial-state wire-preservation target. The
[result record](results-t612-20261104.json) records successful safe checking,
strict zero-finding audit and the three-file protocol dependency closure with
no Replay import. Primary final artifacts are under
`/var/tmp/leiosnotify-t612-20261104/contracts-v4/`. Peak stage sampled RSS is
about 310 MiB; external library interfaces were reused.

The 28 checked definitions include fresh zero-index registration, ready/missing
completion races, selected normal after flag, an early hit retaining a selected
payload through three requests, cancellation without next, generic/node policy
distinction and separate rejection/fault-prefix outcomes. Negative checks exclude
spurious polling, consuming the current request, premature Done and false success.
No candidate Haskell run/rebuild, native PTree bridge, search/CLI or baseline
preservation/resource theorem is supplied here. Those remain separate from
reference-contract typechecking. The subsequent T6.2.1 proof follows below;
T6.2.2 local/paired-policy results and T6.3.1 runtime comparison follow after it; T6.3.2 is next.


## CollectOne finite source/wire preservation

T6.2.1 adds `Forward.agda`, `Backward.agda` and `Preservation.agda` under the
protocol candidate folder, plus this replay-side witness root:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/check_agda.py \
  Cardano_network/Replay/LeiosNotifyPipeLookahead/CollectOne/PreservationTests.agda \
  --out /var/tmp/leiosnotify-collect-one-preservation
```

`candidate-in-baseline` and `baseline-in-candidate` retain the entire finite
source-action sequence from fresh initial states. `wire-equivalence` follows
using the unchanged Contract projection. Theorems quantify every Notification
carrier/contract/sequence, with no new resource, range, readiness or inhabitance
premise. The proof is on mathematical reference Runs; no candidate Haskell run,
PTree/native/paired correspondence, fault/tick/divergence equivalence or runtime
improvement is inferred.

The [maintained proof explanation](../../../../../docs/specs/leiosnotify-collect-one-design.md#t621-finite-source-and-wire-preservation)
describes extra retained baseline tokens and reverse mandatory-poll normalization.
Examples transport exact selected values, generic cancellation and rejection.
A two-request case checks two baseline shutdown flushes versus one early and
one final candidate flush: equal traces need not have identical hidden work.

The [record](results-t621-20261104.json) preserves exact statements, source hashes,
safe checks, strict zero-finding audit and protocol dependency layering. Primary
artifacts are under `/var/tmp/leiosnotify-t621-20261104/preservation-v2/`.
Peak stage sampled RSS is about 552 MiB under the existing serial heap/RSS/time
guards. Unchanged imports/external interfaces are reused; no earlier source or
result identity is changed. The subsequent T6.2.2 local conditional results follow below;
T6.2.2.3 premise discharge and T6.3.1 comparison are checked below; T6.3.2 is next.

## CollectOne conditional resources and local progress

T6.2.2.1/.2 add `Accounting`, `Bounds`, `Safety`, `Rank` and `Progress` under the
candidate protocol directory, with inhabited/negative examples under Replay:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/check_agda.py \
  Cardano_network/Replay/LeiosNotifyPipeLookahead/CollectOne/ResourceTests.agda \
  --out /tmp/leiosnotify-collect-one-resources
```

The [maintained explanation](../../../../../docs/specs/leiosnotify-collect-one-design.md#t622-conditional-resources-and-local-progress)
states every premise. Registered jobs/completed tokens are at most B+1 when
unfinished old work is at most B at every actual optional-poll miss. That count
includes sent-but-unretired control. Exact accounting retains both early hits
and final flushes. Local shutdown safety/accessibility/completion need no
resource premise; with the budgeted fresh prefix, later successful shutdown has
at most B+1 flushes and every finite continuation has at most `3+5(B+1)` model
operations. No runtime responsiveness/latency or production policy bound is inferred.

`ResourceTests` constructs arbitrary finite sequential histories with one retained
token, arbitrary unscheduled backlogs showing why the premise is essential, a
two-request burst rejecting too-small B, held-selected accounting, rejected
current work and a reachable empty-Notification shutdown. Its small `budget?`
helper decides premises on supplied proof objects; it is not a raw-log checker.

All six new modules are freshly safe-checked after removing only their generated
interfaces. Other imports reuse existing interfaces. Final sampled RSS is about
370 MiB under the serial 2 GiB heap/3 GiB sampled RSS/900-second guards. Strict
audit has zero findings and protocol layering has no Replay dependency.
[The record](results-t622-20261104.json) preserves check/audit/source identities;
primary artifacts are under `/tmp/leiosnotify-t622-20261104/final/`.
Earlier sources and result identities are unchanged; no Haskell experiment is
run. The subsequent **T6.2.2.3** proof below discharges the unfinished-work
premise for the candidate paired-policy model. **T6.3.1** runtime comparison follows it; T6.3.2 is next.

## CollectOne paired-policy premise discharge

T6.2.2.3 adds independent candidate `DriverModel`, `NodeModel` and
`NodeDriverModel`, plus the `NodeForward` simulation and `NodeBounds` proof.
The client rules, credit transactions, message alphabet, FIFO queues and four
pending hook boundaries are retained. Accepted admission enters candidate
inspection; no numerical bound is added as a transition guard.

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/check_agda.py \
  Cardano_network/Replay/LeiosNotifyPipeLookahead/CollectOne/NodeResourceTests.agda \
  --out /tmp/leiosnotify-collect-one-node-resources
```

Every fresh candidate policy run has a fresh baseline run with the exact same
wire/policy action list. Their client, packets/hooks and credit queue are equal;
baseline completions retain the candidate's early collections as ghost tokens.
The existing baseline waiting bound is applied to this constructed history,
proving candidate waiting ≤1003 and unfinished work ≤1004. Projection then gives
a real `Budgeted 1004` source run and **registered jobs/completed tokens ≤1005**,
with no caller-supplied resource premise.

After actual server Quit, all successful server source closes have ≤1005 final
flushes and every finite server source continuation has ≤5028 source operations.
These are not bounds on all paired/transport/input operations or runtime time,
blocked I/O, allocation or machine arithmetic. Candidate native/converse paired
and Haskell correspondence remain open.

`NodeResourceTests` witnesses arbitrary-length honest sequential histories with
one retained token, a genuine two-request poll miss, Receive-before-Send hook
orders and paired endpoint closure after Quit/Done. Two rounds compute one ghost
early collection in the baseline. These are new candidate-policy witnesses, not
relabelled baseline proof objects or Haskell runs.

The [maintained explanation](../../../../../docs/specs/leiosnotify-collect-one-design.md#t6223-paired-policy-resource-bounds)
and [record](results-t6223-20261104.json) retain exact statements and provenance.
All six new modules are freshly safe-checked after removing only their generated
interfaces; unchanged dependencies/external interfaces are reused. Final sampled
RSS is about 622 MiB under the serial 2 GiB heap/3 GiB sampled RSS/900-second
guards. Strict audit of the six new files has zero findings; protocol imports
contain no Replay dependency. Primary logs are under
`/tmp/leiosnotify-t6223-20261104/final/`; identities and summaries are retained
in the result record. No earlier source/result identity changes and no Haskell
experiment runs in T6.2.2.3. The subsequent **T6.3.1** actual-driver comparison
is recorded below; **T6.3.2** patch review is next.

## CollectOne actual-driver comparison

`collect_one_runtime.py` builds fresh baseline and candidate versions of the
existing T3/T5 fixtures. The original baseline sources stay intact; generated
fixture copies select the separately named T6.1.1 candidate. All installed
package/compiler, source-pin, import-shim and identity-codec scopes above apply.

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/collect_one_runtime.py \
  --consensus /path/to/ouroboros-consensus \
  --typed-protocols /path/to/typed-protocols \
  --network-archive /path/to/network-2f1c154.tar.gz \
  --out /var/tmp/leiosnotify-collect-one-runtime
```

Defaults are O0/O2, N1/N2, depths 1/1000 and three fresh repetitions, covering
eight schedule cases, fourteen blocking/failure cases, history sizes
0/1/10/1000/10000 and quiet/diagnostic sizes 0/1000/10000/100000. Output must be a
new directory outside the repository. Disk-backed storage is preferred for
these many builds/captures. Builds and runs are serial with the existing 2 GiB
compiler heap, 256 MiB fixture heap, sampled 3 GiB process RSS and finite
timeouts. Quiet profile order alternates baseline/candidate by repetition.

The [record](results-t631-20261104.json) preserves 20 builds, 1224 passing fixture
processes and 64 rejected corruption checks. Exact endpoint wire streams match;
the forced scheduling/fault assertions pass. In observed sequential histories,
the candidate retains one job and performs one final flush. The
[maintained comparison](../../../../../docs/notes/leiosnotify-pipe-lookahead-completion-cost.md#collectone-actual-driver-comparison)
contains quiet heap/shutdown medians and the 0.22–0.46% total-allocation increase
at 100000 exchanges. Throughput is not measured. Diagnostic getter builds have
different retirement gates and supply counter evidence only; their performance
is not compared. No runtime Agda capture certificate is generated here.

Primary artifacts are `/var/tmp/leiosnotify-t631-20261104/full/`; compact method,
quiet summaries, source/build/raw-report identities and limitations are retained
in the record. All guarded commands passed with peak sampled process RSS about
451 MiB and no resource-budget failures. Prior proof/fixture/helper/result
sources are unchanged. Upstream node wiring, socket/mux/CBOR behavior, arithmetic
refinement, general liveness and deployed impact remain outside these fixtures.
**Next is T6.3.2:** package the minimal patch and scoped recommendation.
