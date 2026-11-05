# Paired search order regressions

These tools measure the explicit compiled lookahead checker on tiny synthetic
normalized inputs. They do not capture node logs or establish deployment
conformance. Wave-5 cost tools and evidence are read-only dependencies.

## Measured baseline and minimization

The supplied wave-4 binary has SHA-256
`59ad059459a312819372c826570aa1f3b3597f4309eaafc3adcc55d76d12f5d4`.
Initial probes used a 512M RTS heap, a five-second per-case ceiling, sampled
3 GiB process-group RSS ceiling, bounded output, and a 29-second total ceiling.
Their external full report is
`/tmp/leiosnotify-search-order-baseline-20261105/report.json`;
[initial-probes-20261105.json](initial-probes-20261105.json) retains compact
measurements and artifact/source identities.

| Paired endpoint inputs | Observed result |
| --- | --- |
| One normal exchange, then both Quit/Done sequences | Timeout at 5 seconds |
| Four requests, Quit, four Canceled replies, Done | Timeout at 5 seconds |
| One normal exchange, both files ending at Quit | Timeout at 5 seconds |
| Same exchange with server Done only | Timeout at 5 seconds |
| Same exchange with client Done only | Timeout at 5 seconds |
| One request, Quit, Canceled, Done | Accepted prefix in 0.026 seconds |
| Two requests, Quit, two Canceled replies, Done | Accepted prefix in 1.697 seconds |
| Three-request cancellation drain | Timeout under the remaining approximately 2.27 seconds; **not a five-second result** |

The smaller normal example removes both Done rows and still times out. This
localizes the observed difficulty to reaching Quit or earlier scheduling work;
it does not establish a globally minimal trace. EOF after an ordinary reply was
inexpensive in the earlier cost report. The diagnostic truncated traces do not
replace complete Quit/Done cases in the regression comparison below.

## Source inspection and diagnosis

The old `DriverBasisExecution.menus` lists client internal work, server internal
work, client callbacks, server callbacks, commits, then decodes. The old client
callback menu lists `continueMoves ++ (terminateMoves ++ handledMoves)`.
`TwoListDecide` tries the client visible head, server visible head, then hidden
targets in list order. Generated Haskell preserves this left-biased recursive
search. Its accessibility arguments are erased; they do not serve as a runtime
fuel counter. No visited-state table appears in that worker.

A likely costly detour is a client at `poll` whose next command record is Quit:
a continuation callback can register and physically commit another Request
before the termination callback is attempted. That pending Request Send cannot
be replaced by a Quit record. Other independently enabled scheduling work can
produce many doomed paths before backtracking. These observations motivate
suffix-sensitive priorities for termination, physical operations enabling the
next record, and the exact demanded callback value. **The causal attribution is
an inference from source and timing, not an instrumented execution profile.**
Reordering must retain every old successor and its evidence.

The observed payload basis is also occurrence-based: both Send and Receive
occurrences are retained and `normalChoices` preserves duplicates. Repeated
payloads can therefore provide repeated equivalent callback candidates. This
is another possible source of repeated work, not a measured attribution or a
recommendation to discard candidates without a completeness proof.

## Reproduce the fixed comparison

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/search-order/compare_search.py --selftest
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/search-order/compare_search.py \
  --baseline /var/tmp/leiosnotify-wave4-cli-20261105/generated/LookaheadMain \
  --candidate /absolute/path/to/new/LookaheadMain \
  --out /tmp/new-search-order-comparison --timeout 5 --total-timeout 90
```

The output directory must be new and outside the repository. Every actual
comparison run gets the full same per-case budget; the total ceiling skips a
case rather than silently shortening that case's budget. Runs are serial and
retain executable, source, fixture, output and generated-Haskell hashes. A
resource failure is inconclusive, while a completed `protocol-rejected` result
is an exhaustive model refutation under the declared capture/profile premises.

The ten fixtures include full `normalclosed1` and `cancel4`, a full delayed-Send
positive, three EOF races, three short completed negative controls, and a wrong
agency control. `serial(1)` and `pipeline(1)` are byte-identical, so one measured
fixture explicitly represents both original cost names; it is not two
independent measurements. Their SHA-256 is
`aa35b6c34d492c7518b7d8de8776f2dc0f5d47239e04b55e79f43d4d363ae2f0`.
The four-cancellation fixture SHA-256 is
`21de71676e70a55a9e473391361da416578871ff594cd4b5becaafa8d6812a7e`.
These match the original wave-5 cost fixtures exactly. Both primary cases keep
all Request, reply, Quit and Done rows.

A later candidate-only scale run can reuse the immutable original tool:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/replay_cost.py \
  --binary /absolute/path/to/new/LookaheadMain --out /tmp/new-search-order-scale \
  --sizes 1,2,4,8,16,32,64 --payloads repeated --timeout 5 --total-timeout 120
```

That tool stops a series after an inconclusive result. A formal decision
procedure does not imply practical success within these operational budgets.
No deployed provenance, timestamp-based causality, clean completion from EOF,
or whole-network property follows from this experiment.

## Candidate measurement

The wave-6 candidate binary SHA-256 is
`609d2a99ab0f918f3f485b12dd0682e78f701adba9e585372b8fd3b0b6b3e7c6`.
The same five-second/512M comparison completed all ten candidate expectations.
The full normal one-exchange trace changed from baseline timeout to accepted
prefix in 0.014562 seconds; the complete four-cancellation trace changed from
timeout to accepted prefix in 0.015349 seconds. These are censored baseline
comparisons, not exact speedup ratios. All three short negative controls
completed as protocol rejection on both binaries; the agency control remained
invalid input, and delayed completion/EOF races remained accepted prefixes.

The candidate-only original matrix completed **84/84** accepted prefixes:
three modes, four workload families, and sizes 1, 2, 4, 8, 16, 32 and 64. All
closed families retain Quit and Done. Paired size-64 times were 0.125 seconds
(serial), 0.115 seconds (pipeline), 0.033 seconds (cancellation drain), and
0.114 seconds (delayed Send). The greatest sampled process-group RSS in that
matrix was 24,464 KiB. These small positive fixtures do not establish bounds for
large captures or difficult negative inputs.

The original 21 follow-up fixtures also completed with byte-for-byte hash
agreement. To repeat them:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/search-order/followup_search.py --selftest
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/search-order/followup_search.py \
  --binary /absolute/path/to/new/LookaheadMain --out /tmp/new-search-order-followup \
  --timeout 5 --total-timeout 120
```

Distinct-payload delayed completion at size 64 took 0.135 seconds versus the
original 0.365 seconds. The ordinary reply-prefix control took 0.115 seconds
versus 0.074 seconds; request-only size 64 remained approximately 0.023 seconds.
Thus this record does not claim that every input became faster. No new
instrumented profiling was performed to assign the small differences a cause.

[The compact result record](result-search-order-20261105.json) retains commands,
actual binary/source/fixture hashes, per-case timing/status summaries and full
external report identities. Compiler/source associations and formal checks are
owned by the root build record; observed checkout hashes alone are not build
attestation. No original wave-5 file, core model, shared status document or
source checker was edited for this measurement task.
