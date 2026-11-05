# Actual paired-replay stage costs

This is a diagnostic after `e3451e2c`, not a production checker optimization.
The original verifier/model sources, old 83/274-case evidence and production
executable remain unchanged. No capture is acquired. The
[result record](result-cost-profile-20261105.json) binds actual safe checks,
compilation, generated function calls, runtime output and explicit limits.

## Production functions, separate diagnostic labels

[CostProbe](../../CostProbe.agda) reuses the existing paired parser and
`PairedAdapter.translate` at `exactParams`. Each invocation decodes the supplied
bytes once into a pair of actual typed client/server row lists. The selected
mode then invokes the production function on that pair:

| Mode | Actual operation | Successful final tag |
| --- | --- | --- |
| `decode-only` | Production parser/typed adapter and common field forcing | `decode-complete` |
| `prechecks-only` | `DriverDecide.all-prechecks?` for `AllPrechecks` | `preconditions-passed` |
| `backend-only` | Unchanged `DriverDecide.For.check` | `backend-accepted` |
| `public-decide` | Actual `DriverDecide.decide` | `complete-accepted` |
| Ordinary paired CLI | Unchanged existing `LookaheadMain` | `accepted-prefix` |

Precondition success is **not acceptance**. Its report says full verification
was not run, and the host report keeps `source_verdict: null`. The backend/public
functions retain exactly `Dec (SourceTrace contract client server)`, with the
original unrestricted fresh source run and order-preserving merge semantics.
No checker, transition rule or parser is copied into the diagnostic.

The profile remains generic successful client callbacks, unit return and the
explicit `node-next` server callback contract, with fresh-state assertions and
prefix EOF. It does not select a fixed node pipeline depth or certify the
whole-node credit/queue policy.

The existing [ordinary CLI](../README.md#normalized-lookahead-cli-and-manifest-runner)
is a separate contextual comparison, using its original c8f9ce34 binary. No
production flag or source definition is changed and no production rebuild is
performed for this matrix.

## Shared forcing and measurement scope

Before its selected stage,
[CostProbeMain](../../CostProbeMain.agda) prints `typed-input-ready`, row counts
and a forcing sum. That fold traverses every typed protocol-row constructor,
optional announcement branch, vote-list spine, duplicate vote and retained
natural payload field. Re-encoding uses the existing exact adapters. Printing
the sum before the selected stage forces those values through the sequential
IO continuation rather than touching only the list lengths.

The sum is deliberately **not an identity hash**: reordered votes can collide,
as an explicit [pure gate](../../CostProbeTests.agda) demonstrates. Exact fixture
SHA-256 identifies the bytes; each mode uses the same actual decoder. Successful
diagnostic modes additionally agree on their row counts and forcing sum. Header
and original-source metadata discarded by the typed adapter is not traversed by
this forcing fold. It does not claim full native body/signature field coverage.

Each mode is a fresh process. Every elapsed time and RTS allocation count
includes startup, parsing and reporting. Diagnostic modes additionally share
the forcing pass; the ordinary CLI has no added pass. Forcing can affect later
lazy evaluation/sharing. There is **no exact additive subtraction** of times or
allocations, and marker arrival times are not phase timers: stdout may be
buffered under pipes. No GHC profiling libraries or new timing FFI are needed.

## Fixed input matrix and controls

The [fixture record](fixtures-20261105.json) retains 22 exact input identities:

- Serial and pipeline positives, repeated payloads at 64, 128, 256, 512, 1024
  and 2048 exchanges.
- The same two families with distinct payloads at 64, 128, 256 and 512.
- A late malformed Votes field: every mode, including the ordinary CLI, must
  retain the same production parser error at paired input line 5.
- A typed but phase-invalid client Done with an empty server: decoding succeeds,
  actual preconditions fail, and public typed/ordinary decisions reject.

These are 110 mode slots. The phase-invalid backend slot is deliberately not
run: backend-only measurements are reserved for the known positive family after
an actual measured `preconditions-passed`. A parser-error backend label cannot
reach the backend because shared decoding fails first. Expected positive
outcomes retain the existing workload's source-schedule rationale, not new
kernel witnesses for every larger generated input.

[cost_profile.py](cost_profile.py) reuses `replay_cost.measure` for process-group
cleanup, time/output/RSS limits and GNU-time metrics. Its diagnostic tag reader
only reclassifies completed unknown-protocol-tag output when the exact mode tag
and exit code agree. Existing timeout, heap, RSS, output and IO failures remain
inconclusive. Invalid input stays distinct, and a guard tag never becomes
`accepted-prefix`.

Every launched run has a two-second ceiling, 512M RTS heap, sampled 3 GiB
process-group RSS ceiling and 65536-byte retained output limit; the whole matrix
has 90 seconds. Larger members of an inconclusive stage/family/payload series
are skipped, and no shrunken timeout is substituted near the global limit.
The RTS heap cap is distinct from total process RSS. Allocations are cumulative
bytes allocated over the run, not live heap or retained memory. Killed runs may
emit no RTS statistics; those fields remain unknown rather than zero.

## Build and run

The [builder](build_probe.py) runs Agda generation and GHC separately, each with
2G heap and sampled 3 GiB RSS ceilings, in a new disk-backed `/var/tmp` directory.
Pure [CostProbeTests](../../CostProbeTests.agda) must first be checked with the
project's bounded `--safe` runner. The IO entry point uses existing stdlib IO/
environment/exit bindings and is typechecked during compilation, not advertised
as a safe theorem module.

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/check_agda.py \
  Cardano_network/Replay/LeiosNotifyPipeLookahead/CostProbeTests.agda \
  --out /tmp/new-cost-probe-safe
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/cost-profile/build_probe.py \
  --out /var/tmp/new-cost-probe-build
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/cost-profile/cost_profile.py --selftest
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/cost-profile/cost_profile.py \
  --probe-binary /var/tmp/new-cost-probe-build/generated/CostProbeMain \
  --probe-sha256 ACTUAL_PROBE_SHA256 \
  --paired-binary /var/tmp/leiosnotify-wave10-cli-20261105/generated/LookaheadMain \
  --out /tmp/new-cost-profile
```

The coordinator must grant the heavy slot for compiler/model execution; pure
host selftests launch no model processes. Disk-backed build writes can require
the environment's existing escalation mechanism. No config/node operation is
performed by these commands.

## Actual validation and function association

The first fresh safe check passes both pure modules at 1096.1 MiB sampled RSS,
reusing unchanged cached dependencies. Strict audit of all three new Agda files
finds zero holes/trust declarations. The unchanged `ShutdownPrecheck.agda`
dependency emits its existing PatternShadowsConstructor warnings; these are
retained in the evidence rather than modifying that production source.

Agda generation passes in 42.230 seconds at 1249664 KiB sampled RSS. Separate
GHC compilation passes in 38.321 seconds at 588756 KiB. No initial build or
proof failure occurs. The diagnostic binary is
`/var/tmp/leiosnotify-wave11-cost-probe-20261105/generated/CostProbeMain`, SHA-256
`8479d816afc1985cd9ecaf4901dcb73ec7474c931c942abf7df611d4f5e226a3`.

The [generated Haskell manifest](generated-haskell-sha256-20261105.json) retains
503 module hashes. The result record additionally records actual generated
wrapper calls to `DriverDecide.all-prechecks?`, `DriverDecide.For.check` and
`DriverDecide.decide`, alongside their source and compiled module identities.
This is compiled function association, not just a source-only timing estimate.
Current checkout hashes are not substituted for the old CLI's build provenance;
its [previous build record](../results-replay-wave10-20261105.json) remains the
source of that association. The
[preservation ledger](frozen-production-and-inventories-20261105.json) verifies
the existing source/evidence bytes against committed `e3451e2c`.

## Actual measured results

All 20 positive inputs pass the actual `AllPrechecks`. The nine operational
controls complete with their fixed outcomes; the guard-fail backend slot is not
run. Six positive verification runs time out: serial and pipeline with distinct
payloads at 512, in each of backend-only, public-decide and ordinary paired CLI.
No completed outcome is unexpected. The full matrix takes 38.777441 seconds and
exits 1 because six timeouts do not meet their expected completed outcomes.
Sources and both binaries retain before/after hashes. Maximum sampled group
RSS is 527340 KiB; there is no heap-exhaustion observation.

For serial/distinct with 256 exchanges, observed whole-process results are:

| Mode | Seconds | Cumulative allocation, decimal GB |
| --- | ---: | ---: |
| decode-only | 0.063888 | 0.154 |
| prechecks-only | 0.054105 | 0.157 |
| backend-only | 0.906047 | 2.571 |
| public-decide | 0.896220 | 2.575 |
| ordinary paired CLI | 0.899980 | 2.575 |

The guard row's slightly smaller time than decoding is variation, not negative
guard cost. In particular, **2.571 GB is cumulative allocation**, not peak RSS,
heap occupancy, a leak or an OOM event. The modes do not provide exact additive
subtraction of parser/forcing/guard/backend costs.

At 512 distinct serial exchanges, decode-only and prechecks-only finish in
about 0.106 seconds; all three full-verification modes reach the two-second
deadline and have unknown final allocation statistics. Pipeline/distinct shows
the same coarse separation. At 2048 repeated pipeline exchanges, decoding and
prechecks take about 0.356/0.376 seconds, versus about 1.845 seconds for the
unchanged backend.

**Inference at this diagnostic scope:** the expensive distinct-payload behavior
persists in the unchanged full backend, while necessary-condition checking
completes quickly on these inputs. This does not distinguish basis construction,
search, witness construction or other costs inside `For.check`. No optimization,
universal complexity bound, deployed throughput result or new capture verdict
is established by this matrix.
