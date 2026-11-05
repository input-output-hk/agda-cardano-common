# Shutdown precheck stress comparison

This wave follows `ae0420d6` and measures a future ShutdownPrecheck executable
against the recorded Credit-gated result. It changes no old producer, fixture
inventory, report, proof module or binary. It acquires no logs and does not run
the baseline executable again.

[shutdown_stress.py](shutdown_stress.py) calls the unchanged
[83-case harness](../search-stress/search_stress.py) and protects 21 old files
against their exact committed bytes. These include all search-stress and
precheck artifacts, the workload/classifier producers and the wave 9 aggregate.
The [old-evidence ledger](frozen-old-evidence-20261105.json) retains those hashes
without changing their source files.
The [frozen inventory](../search-stress/inventory-20261105.json) remains the
authority for every fixture hash, expected outcome, review annotation and
command template. It contains 83 names and 77 distinct input hashes; the six
duplicate Canceled-policy cases retain their original interpretation.

The baseline is the committed
[Credit stress record](../search-stress/result-search-stress-credit-20261105.json),
SHA-256 `3f1b20c56394c3edcb1f91d92eed7211a58ee4f69e7f84b04b7955a0349bfed9`,
for executable SHA-256
`045b3a6ccdd86db4fc1b1629597dbf8cbea40e2e767d96b3e05ec5e4e332b022`.
Its actual outcomes are 27 rejections, 28 accepted prefixes, nine timeouts and
19 skipped larger cases. It is historical runtime evidence, not a rerun under
the current modified source. New executable provenance belongs to the root
integration build record; current checkout hashes alone do not establish it.

## Fixed comparison contract

The comparison keeps all original expected outcomes and uses exactly the same
two-second per-case wall ceiling, 512M RTS heap, sampled 3 GiB process-group RSS
ceiling, 65536-byte output cap and 180-second global budget. The fixed harness
stops larger members of a family/payload series after an inconclusive result.
Global budget exhaustion skips a case rather than reducing its per-case ceiling.
512M is a heap limit, not a whole-process RSS limit.

The target is the orphan Done family: a client closes after n discharged serial
rounds while the server records no Quit Receive. At n=1 this previously timed
out; n=2 through n=128 were skipped. A necessary shutdown condition is expected
to refute these inputs directly, but the black-box timing does not instrument
which branch runs. Larger positive traces remain deadline sensitive, as retained
in the old [matched budget probe](../search-stress/result-budget-probe-20261105.json).

Run the pure preparation controls first:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/shutdown-stress/shutdown_stress.py --selftest
```

They check the old 274-case pure matrix and its 177 historical fixture hashes,
the 83 exact stress inputs, all protected source/evidence hashes, and deliberate
fixture/expected-outcome/review/flag/limit drift. No model process launches.

Only after the root coordinator grants the single heavy slot, run:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/shutdown-stress/shutdown_stress.py \
  --binary /absolute/path/to/reviewed/LookaheadMain --expected-sha256 ACTUAL_BINARY_SHA256 \
  --out /tmp/new-shutdown-stress
```

The output directory must be new and outside the repository. The unchanged
harness writes its full report and fixture/log artifacts below `harness/`.
The coordinator writes `comparison.json` with all completed outcomes, timeouts,
skips, protected hashes and exact flags. A nonzero harness result remains
nonzero; failed final integrity checks exit 2, while fixture/flag drift aborts
with an error. No expected outcome is relaxed
to make the run pass. A necessary precheck is never treated as sufficient for
acceptance, and a timeout never becomes protocol rejection.

## Separate ordering-cycle probe

The supplemental [cycle_probe.py](cycle_probe.py) has three fixtures, separate
from the fixed 83-case comparison. Let A be exactly `BlockOffer 43 23 31`:

```text
client: [Recv A, Send RequestNext] repeated n times
server: [Recv RequestNext] repeated n times, then [Send A] repeated n times
```

The source-reviewed expectations are n=2 accepted and n=3/4 rejected. All five
necessary predicates are reviewed as passing: the local languages accept,
packet prefixes match, final pending-Send bounds hold, Reply credit is n≤n,
and no Quit/Done records exercise the shutdown condition. These are review
annotations, not kernel fixture theorems or runtime branch instrumentation.

For n=2, the server's first physical reply can remain pending its Send hook
while the client receives it, records Request Send1 and physically commits
Request2. The server records Request Receive2, finishes Reply Send1, then
handles the second reply and remaining hooks.

For n≥3, the reviewed incompatibility argument is a strict cycle. The server
must record Request Receive3 before Reply Send1. Physical Request3 requires
Client Request Send2, which follows Client Reply Receive2. Physical Reply2
requires Reply Send1 to clear the sole `pendingServerSend` slot and advance
the server's send continuation. A completed checker verdict can test this
model hypothesis; a timeout remains inconclusive. The argument has no new
kernel refutation in this area.

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/shutdown-stress/cycle_probe.py --selftest
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/shutdown-stress/cycle_probe.py \
  --binary /absolute/path/to/reviewed/LookaheadMain --expected-sha256 ACTUAL_BINARY_SHA256 \
  --out /tmp/new-shutdown-cycle-probe
```

The root must grant its execution after the main comparison. Each case has the
same two-second/512M/3 GiB/65536-byte limits, with six seconds globally. An
inconclusive n=3 skips n=4; no baseline run or new capture is introduced.
Actual measurement results are retained separately below. The
[cycle inventory](cycle-inventory-20261105.json) freezes its three
literal input texts, hashes and annotations. Neither a finite regression matrix
nor these necessary guards establish precheck sufficiency, capture completeness
or deployed conformance.

## Measured shutdown-gated comparison

The coordinator supplied executable
`/var/tmp/leiosnotify-wave10-cli-20261105/generated/LookaheadMain`, SHA-256
`c8f9ce34ca59b4e150570cedb55e068601f736d3eb192934d492dda711d0af82`.
Root integration evidence owns its compiled source/build association. The
[durable result](result-shutdown-stress-20261105.json) retains exact flags,
fixture hashes, every outcome and the transient full-report identity.

| Outcome | Recorded wave 9 Credit run | New shutdown run |
| --- | ---: | ---: |
| Protocol rejected | 27 | 35 |
| Accepted prefix | 28 | 30 |
| Inconclusive timeout | 9 | 7 |
| Larger-series not run | 19 | 11 |
| Total seconds | 31.282014 | 28.752487 |

All 35 negative cases complete as rejection, including all nine orphan Done
sizes from zero to 128 preceding exchanges. Eight orphan Done cases are newly
completed: the previous one-exchange timeout and seven larger series skips.
There are no unexpected completed outcomes or disagreements with a previously
completed verdict. All 83 input identities, expectations, review annotations,
launched flags and limits match the frozen inventory.

Two deadline-sensitive positives also complete in this run:
pipeline/repeated at 2048 exchanges in 1.852452 seconds, and delayed-send/repeated
at 4096 in 1.763711 seconds. These recoveries are measured observations, not
universal cost improvements. Total run times cover different launched subsets
because of stop-on-inconclusive behavior. The original wave 9 reports and its
matched probes remain untouched.

The seven remaining inconclusive runs all hit the wall deadline. They are
serial/repeated and pipeline/repeated at 4096 exchanges; serial, pipeline and
delayed-send/distinct at 512; and both cancel-drain policies at 2048. Eleven
larger cases remain skipped. There is no heap-exhaustion outcome. The maximum
sampled process-group RSS is 524016 KiB, below its separate 3 GiB ceiling.
The main harness exits 1 because these timeouts/skips do not satisfy all expected
completed outcomes; no expectation is relaxed. All 21 protected old files,
candidate binary, observed harness sources and legacy Main retain their hashes.

## Measured ordering-cycle probe

The [separate result](result-ordering-cycle-20261105.json) retains these exact
compiled-checker outcomes under the two-second per-case ceiling:

| n | Reviewed expectation | Actual result | Seconds |
| --- | --- | --- | ---: |
| 2 | Accepted prefix | Accepted prefix | 0.012773 |
| 3 | Protocol rejected | Protocol rejected | 1.088702 |
| 4 | Protocol rejected | Protocol rejected | 1.049507 |

All three cases complete; none is skipped or timed out. The probe exits 0,
takes 2.152999 seconds overall and reaches 286332 KiB peak sampled group RSS.
Both new script hashes, all protected old evidence and the candidate binary
remain unchanged.

These are concrete model verdicts for the exact three synthetic inputs. Their
five-guard-pass metadata remains source review rather than runtime branch
instrumentation. Root's
[DriverShutdownPrecheckTests](../../DriverShutdownPrecheckTests.agda) additionally
contains an abstract n=3 all-five-pass gate; it does not prove a universal
ordering-cycle family refutation. This area introduces no such kernel theorem.
The remaining complete fallback continues to distinguish joint compatibility
from necessary-condition success. No additional model runs are performed.
