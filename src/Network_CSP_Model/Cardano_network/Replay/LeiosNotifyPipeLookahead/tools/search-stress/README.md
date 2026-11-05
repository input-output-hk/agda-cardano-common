# Paired search stress controls

This area extends measurement after `05eace4e` without changing old fixture
producers, proof modules, reports or binaries. All inputs are synthetic normalized
prefixes. It acquires no logs and makes no deployed conformance claim.

[search_stress.py](search_stress.py) reuses
[precheck fixture formatting](../precheck/precheck_regressions.py),
[replay-cost workloads and measurement](../replay_cost.py), and the existing
strict CLI verdict classifier. It first runs the old 274-case pure inventory
controls, including 177 historical fixture-hash comparisons. Pure selftests
launch no checker process.

## New inventory and review boundary

The default inventory contains 83 named cases, with 77 distinct input hashes:

| Category | Construction | Sizes | Named cases |
| --- | --- | --- | ---: |
| Positive | serial, pipeline, delayed-send and cancel-drain, each with repeated/distinct payload policy | 128, 256, 512, 1024, 2048, 4096 | 48 |
| Negative | early orphan reply after discharged serial rounds, repeated payloads | 0, 1, 2, 4, 8, 16, 32, 64, 128 | 9 |
| Negative | same early orphan shape, distinct payloads | 1, 2, 4, 8, 16, 32, 64, 128 | 8 |
| Negative | recorded client request followed by orphan reply, repeated payloads | 0, 1, 2, 4, 8, 16, 32, 64, 128 | 9 |
| Negative | client Quit/Done without server Quit Receive, after discharged serial rounds | 0, 1, 2, 4, 8, 16, 32, 64, 128 | 9 |

Cancel-drain's Canceled replies carry no normal payload. Its two policy names
therefore share six input hashes. They are not independent protocol patterns.
The duplicate empty-prefix distinct orphan control is omitted.
The [frozen inventory](inventory-20261105.json) records every exact fixture hash,
command template, expected outcome and review annotation before any comparison
with a future binary.

All cases are reviewed as passing the three necessary guards committed at
`05eace4e`: both local wire languages, exact common packet prefixes and final
pending-Send count bounds. The Python selftest checks exact packet-prefix/count
arithmetic and generated shapes, but does not reimplement the local Agda checker.
Local validity and expected final verdicts remain **source-review annotations**.
They are not runtime branch instrumentation or new kernel family theorems.

At the committed three-guard baseline, the original
[DriverPrecheckTests](../../DriverPrecheckTests.agda) has a kernel control for an
initial normal client Reply Receive with an empty server history: all three
guards pass, and complete search refutes the source trace. The later public
decision adds Credit and can refute that same history before full search.
The new [DriverCreditPrecheckTests](../../DriverCreditPrecheckTests.agda) retains
an independent all-four-guard-pass zero-prefix orphan Done control, with both
public and backend rejection. These small abstract controls do not certify every
payload or padded fixture generated here. Completed binary decisions provide
their own model-level results; exhausted budgets provide none.

## Why the negative shapes are expected to fail

Let `P(n)` be the two endpoint histories of n serial Request/reply exchanges,
with the existing workload's final Quit/Done removed. Both local quotients end
in Open 0. No reply credit remains at the server.

```text
early orphan:
  client: P(n), Recv A
  server: P(n)

requested orphan:
  client: P(n), Send RequestNext, Recv A
  server: P(n)

orphan Done:
  client: P(n), Send Quit, Recv Done
  server: P(n)
```

For early orphan, the client's one extra Receive enters Lead. The requested
variant supplies a recorded client Request instead. Both are independently
valid client prefixes, and the extra response is outside the common packet
prefix. Its one-record lead satisfies the pending-Send bound. Nevertheless, the
server cannot enable an additional reply without another **recorded** Request
Receive: physical decode alone does not advance its source continuation.

Orphan Done closes the client locally, while the server remains Open 0. Command
and response prefixes still agree, with exactly one unmatched suffix in each
direction. The server cannot enable Done until its Quit Receive is recorded.
Done/Quit are excluded from the separate ReplyCredit condition being developed;
this control distinguishes that reply-credit guard from complete compatibility.

These constructions were reviewed against the actual
[driver source](../../../../LeiosNotifyPipeLookahead/DriverModel.agda),
[client quotient](../../../../LeiosNotifyPipeLookahead/Wire/Client.agda), and
[server quotient](../../../../LeiosNotifyPipeLookahead/Wire/Server.agda).
The existing positive producers document source schedules separately. EOF is
always a finite prefix, never evidence of successful physical completion.

## Bounded execution and comparison

Run pure controls first:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/search-stress/search_stress.py --selftest
```

Model runs require the coordinator's single heavy slot. The immutable baseline
binary is `/var/tmp/leiosnotify-wave8-count-cli-20261105/generated/LookaheadMain`,
SHA-256 `d7bf4b88247a87a535d3e1639603c90c69b09a0a138a808c4fb8932de4726938`.
Once the slot is granted:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/search-stress/search_stress.py \
  --binary /var/tmp/leiosnotify-wave8-count-cli-20261105/generated/LookaheadMain \
  --out /tmp/new-lookahead-search-stress --timeout 2 --total-timeout 180
```

Use a new output directory outside the repository. Every launched case has the
same two-second wall ceiling, 512M RTS heap, sampled 3 GiB process-group RSS
ceiling and 65536-byte retained output limit. No smaller per-case timeout is
substituted when the total budget is nearly exhausted. The harness stops larger
sizes of a family/payload series after its first inconclusive result. A completed
unexpected result stops further launches for diagnosis. Measured fixtures, exact
argv, output hashes, source/binary identities and legacy Main preservation are
retained. Process groups are killed and reaped on limits by the shared runner.

Optional increasing `--positive-sizes` and `--negative-sizes` lists have at most
twelve entries each, bounded by 16384. Each fixture is capped at eight MiB.
Repeated runs or future-binary comparisons must preserve the same inventory,
expectations and ceilings; use an explicit `--expected-sha256` for another
reviewed binary. Later source development does not change which guards exist in
the immutable baseline executable. Its black-box timing alone cannot identify
the internal branch taken.

The harness exits nonzero if any expected case is inconclusive/not run, any
completed verdict is unexpected, or an input producer/binary/legacy Main changes.
Thus a limited run can be useful evidence while deliberately failing its full
expectation target. It never promotes timeout to protocol rejection.

## Measured three-precheck baseline

The baseline executable above belongs to committed `05eace4e`, even though the
current checkout can contain later uncommitted guard development. Current Agda
source hashes in the report are review/preservation snapshots; they are not a
compilation manifest for that older executable. The measured binary hash and
this distinction are explicit in the result.

The [baseline record](result-search-stress-baseline-20261105.json) retains all
83 cases and the full transient report identity. The run takes 36.537699 seconds
and exits 1 because 11 timeouts and 39 larger-series skips do not satisfy the
expected completed outcomes. It contains 30 accepted prefixes and three
completed rejections, with no unexpected completed verdict. Sources, executable
and legacy Main retain their before/after hashes.

All three zero-prefix negatives complete as rejection. Each first padded
negative at n=1 times out at two seconds; later members of those four series
are skipped. This includes orphan Done, which the separate ReplyCredit guard
is not designed to reject. These timeouts remain inconclusive despite the
source-reviewed impossibility argument.

| Positive family/policy | Largest measured accepted size | First timeout |
| --- | ---: | ---: |
| serial/repeated | 2048 | 4096 |
| pipeline/repeated | 2048 | 4096 |
| delayed-send/repeated | 4096 | None in the requested series |
| serial/distinct | 256 | 512 |
| pipeline/distinct | 256 | 512 |
| delayed-send/distinct | 256 | 512 |
| cancel-drain/repeated | 1024 | 2048 |
| cancel-drain/distinct | 1024 | 2048 |

The maximum sampled process-group RSS is 539836 KiB, below the separate 3 GiB
RSS ceiling. The RTS 512M heap ceiling is not a 512 MiB whole-process RSS cap.
All eleven inconclusive runs hit the wall timeout; no heap-exhaustion result is
reported. These are single-host bounded observations, not universal size or
time guarantees. No post-timeout larger case is reported as completed.

## Credit-gated comparison

The coordinator supplied the newly compiled candidate executable
`/var/tmp/leiosnotify-wave9-cli-20261105/generated/LookaheadMain`, SHA-256
`045b3a6ccdd86db4fc1b1629597dbf8cbea40e2e767d96b3e05ec5e4e332b022`.
Root integration evidence owns its source/build association; current checkout
hashes alone are not that association. The original harness and inventory are
unchanged. The [candidate record](result-search-stress-credit-20261105.json) and
[comparison record](comparison-search-stress-20261105.json) verify every one of
the 83 fixture hashes, expected outcomes, review annotations, command templates
and actual launched flags, with the same ceilings.

| Outcome | Three-guard baseline | Credit-gated candidate |
| --- | ---: | ---: |
| Accepted prefix | 30 | 28 |
| Protocol rejected | 3 | 27 |
| Inconclusive timeout | 11 | 9 |
| Larger-series not run | 39 | 19 |
| Total seconds | 36.537699 | 31.282014 |

The total times cover different launched subsets because each series stops at
its first inconclusive case; they are not a matched per-case speed comparison.

All 26 orphan Reply negatives now complete as rejection through 128 preceding
exchanges, taking 0.012740–0.044039 seconds. That includes 24 newly completed
cases: three prior timeouts and 21 prior series skips. Orphan Done at one
preceding exchange still times out, leaving seven larger cases skipped. This
preserves the distinction between a necessary credit condition and full paired
compatibility.

The fixed two-second run also loses two prior positive completions:
pipeline/repeated at 2048 exchanges and delayed-send/repeated at 4096. The later
pipeline size is consequently skipped. No completed verdict disagrees between
executables, but these operational deadline crossings are retained explicitly.
The candidate's largest sampled process-group RSS is 525780 KiB. Its exit 1
remains intentional because its nine timeouts and 19 skips do not satisfy all
expected completed outcomes.

## Separate matched deadline probe

Those two crossings motivate a separate bounded diagnostic, preserving both
original 83-case reports. [budget_probe.py](budget_probe.py) uses the same two
exact frozen inputs, with three repetitions per executable/input. First-binary
order alternates and is balanced across the six matched pairs. The probe allows
five seconds per case, 512M RTS heap, sampled 3 GiB RSS and 60 seconds globally.
It launches at most 12 model processes.

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/search-stress/budget_probe.py --selftest
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/search-stress/budget_probe.py \
  --baseline-binary /var/tmp/leiosnotify-wave8-count-cli-20261105/generated/LookaheadMain \
  --candidate-binary /var/tmp/leiosnotify-wave9-cli-20261105/generated/LookaheadMain \
  --out /tmp/new-lookahead-budget-probe
```

The [probe record](result-budget-probe-20261105.json) retains all 12 runs and
exact source/fixture/binary identities. All 12 accept, each below two seconds,
and the whole probe takes 22.115100 seconds. Sources and binaries retain their
before/after hashes; maximum sampled process-group RSS is 526224 KiB.

| Input | Baseline mean seconds | Candidate mean seconds | Candidate/baseline mean |
| --- | ---: | ---: | ---: |
| pipeline/repeated, 2048 exchanges | 1.773674 | 1.815529 | 1.023598 |
| delayed-send/repeated, 4096 exchanges | 1.871144 | 1.883251 | 1.006470 |

These means describe three repetitions on one host. The original deadline
crossings were not reproduced in these supplemental probes; the measurements
do not establish a universal causal slowdown or a statistical regression claim.
Passing a five-second probe does not retroactively complete either original
two-second timeout. Large distinct-payload positives and orphan Done remain
documented limits, and no further model runs are performed for this wave.
