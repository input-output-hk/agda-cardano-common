# Bounded menu profiling

This diagnostic measures the actual production finite notification basis and
hidden successor menus, including the old ordering and the proposed
[`ReadyGateOrder`](../../ReadyGateOrder.agda). It produces **no protocol
membership verdict**. The kernel proof that gated and old lists have exactly
the same elements, evidence and order is independent of these measurements.

## Repaired diagnostic build

[`build-menu-probe-20261105.json`](build-menu-probe-20261105.json) binds the
repaired Agda sources, exact build commands, all 505 generated Haskell hashes,
sharing excerpts and executable. Both bounded compiler stages completed:
Agda generation 43.339 s / 1,241,944 KiB sampled peak RSS, GHC 38.723 s /
647,228 KiB. Compiler heap caps were 2G; sampled RSS cap was 3 GiB. The generated
entrypoint uses `-O0`, `-threaded` and `-rtsopts`.

The initial successful compiler run exposed a diagnostic defect: Agda expanded
`let` bindings so the basis was prepared twice and three result projections
could rerun the iteration function. No benchmark was launched with that binary.
[`initial-sharing-failure-20261105.json`](initial-sharing-failure-20261105.json)
retains its original source texts, build identity and generated excerpts. The
repair uses constructor-pattern function arguments. Two independent read-only
reviews checked the regenerated Haskell before GHC/runtime: one `Prepared`
runtime value is shared by basis forcing and reporting; one iteration result
is passed to the renderer, whose three fields are bound once.

The repaired executable is
`/var/tmp/leiosnotify-wave12-menu-probe-shared-20261105/generated/MenuProbeMain`,
SHA256 `1fd3be0bbc5f1881a1b57f8ad2c5169ce48e8c0b27d28e94218f1f4f4b0e2af8`.
This diagnostic build does not rebuild the production replay executable.

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/menu-profile/build_probe.py --stage agda --out /var/tmp/leiosnotify-wave12-menu-probe-shared-20261105
# Inspect generated Prepared and Totals runtime sharing before continuing.
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/menu-profile/build_probe.py --stage ghc --out /var/tmp/leiosnotify-wave12-menu-probe-shared-20261105
```

Both stages use a new disk-backed directory; generation and GHC are separate so
sharing can be reviewed between them. The GHC stage verifies the source and
entire generated Haskell manifest have not changed.

## Frozen microprofile

[`fixtures-20261105.json`](fixtures-20261105.json) freezes nine exact existing
pipeline inputs from the committed [cost-profile inventory](../cost-profile/fixtures-20261105.json):
repeated and distinct payloads at 64, 128, 256 and 512 exchanges, plus repeated
1024. The reused fixture producers and the 29 selected historical tool/evidence files remain unchanged.

Each input runs basis-only once, then three old/gated mode pairs at each of six
snapshots: initial, claimed, selected, after-quit, closed and
inactive-reader-claimed. Each menu mode requests 100 source-level calls with a
varied completed-counter nonce. The gate checks only sender=claimed and
quitFlag=false. The inactive-reader-claimed control still delegates to the old
ready scan despite producing an empty result.

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/menu-profile/menu_profile.py --binary /var/tmp/leiosnotify-wave12-menu-probe-shared-20261105/generated/MenuProbeMain --expected-sha256 1fd3be0bbc5f1881a1b57f8ad2c5169ce48e8c0b27d28e94218f1f4f4b0e2af8 --iterations 100 --out /tmp/leiosnotify-menu-profile-20261105
```

Each process has a 2 s wall limit, 512M RTS heap cap, sampled 3 GiB process-group
RSS cap and 64 KiB output cap; total runtime is limited to 90 s. Larger cases in
a family stop after an inconclusive result. The observed matrix finished in
48.504 s: **331 completed, two timeouts, no skips**. Both timeouts were distinct
512 at the claimed snapshot, ordered-old and ordered-gated. All **161 completed
old/gated comparisons agree** in target counts and forcing sums. No completed
output mismatch occurred. `all_expected=false` retains the two timeouts.

[`result-menu-profile-20261105.json`](result-menu-profile-20261105.json) retains
every slot, sampled resource result, diagnostic output summary, artifact hash,
mode, snapshot and command. Every `protocolVerdict` is null. The baseline
[Agda ledger](baseline-agda-sha256-20261105.json) records all 1,031 committed
Agda files **before** any authorized production import change. These sources,
29 old evidence/tool files, the binary and diagnostic sources were unchanged
through this microprofile. This historical ledger is not asserted to describe a
later candidate build.

For distinct 512 (513 basis values), the whole-process cumulative allocations
show the bounded opportunity and its limit:

| Snapshot / mode | Old allocated bytes | Gated allocated bytes | Targets across requested calls |
| --- | ---: | ---: | ---: |
| initial / ready | 1,353,425,616 | 1,297,913,880 | 0 |
| initial / ordered | 1,355,930,768 | 1,300,417,328 | 200 |
| claimed / ready | 1,917,392,696 | 1,917,512,056 | 51,300 |
| inactive-reader-claimed / ready | 1,394,955,560 | 1,394,976,624 | 0 |

The disabled initial ready scan avoids about 55.5 MB of cumulative allocation
across the requested source-level calls. The two delegation controls show no
similar saving. Initial basis-only already allocates 1,297,662,928 bytes; that
common cost is still paid in each process. These are **cumulative allocations**,
not peak RSS, live heap usage or OOM results.

All times include startup, parsing and full typed-input forcing, common basis
construction, menu work and output. Buffered readiness markers are not timing
boundaries. Timing differences are not exact phase subtractions. Nonces make
source-level state arguments vary, but zero targets may not force a nonce;
physical evaluation count and universal anti-hoisting are not proved.
Count/state/position sums can collide and do not certify list equality. Five
snapshot anchors have fresh-source witnesses only at nonce zero; positive
nonces and every inactive-reader-claimed state are arbitrary diagnostic states.
Ranking uses the whole input, without claiming that input reached a snapshot.

## Full replay comparison coordinator

[`full_replay.py`](full_replay.py) is separate from the diagnostic. With an
explicit root-authorized `--allow-order-import`, it permits exactly one existing
source change: `DriverDecide` imports `ReadyGateOrder` instead of
`DriverSearchOrder`. Every other committed Agda byte and the 29 selected historical tool/evidence
files must match `a1b7b948`. It reuses the exact old 83 stress inputs, three ordering
cycle inputs and 20 positive ordinary paired-CLI inputs, flags and expected
outcomes. Historical outcome records are the baseline; the old executable is
not rerun. Timeouts/skips stay inconclusive and expectations are never relaxed.
The root supplies the compiled-source association and candidate executable hash.

The original frozen production-ledger selftest is deliberately not reasserted
after the authorized import change. Host selftests validate fixture hashes,
classifier failure controls and the 83/3/20 coordinator without launching a
model:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/menu-profile/full_replay.py --selftest
# Before the authorized production import change only:
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/menu-profile/menu_profile.py --selftest
```

## Full replay trial and retained coordination failure

The root built the exact one-import candidate at
`/var/tmp/leiosnotify-wave12-cli-20261105/generated/LookaheadMain`, SHA256
`867e1ab15b0d61d8ec1fe33dec3b645f3bf38d6216c30204e1bfcabc8d6f78d0`.
The root's separate build record owns its compilation provenance. This folder's
live-source ledger is a preservation check, not that build provenance. The
unchanged historical baseline executable is SHA256
`c8f9ce34ca59b4e150570cedb55e068601f736d3eb192934d492dda711d0af82`.

The trial launched this command using the original coordinator source retained
in the failure record:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/menu-profile/full_replay.py --binary /var/tmp/leiosnotify-wave12-cli-20261105/generated/LookaheadMain --expected-sha256 867e1ab15b0d61d8ec1fe33dec3b645f3bf38d6216c30204e1bfcabc8d6f78d0 --allow-order-import --out /tmp/leiosnotify-menu-full-replay-20261105
```

All 95 launched monitor runs returned across 106 slots (11 were skipped) before
a host aggregation assertion failed. It confused an old diagnostic row's
`name` suffix `_paired-cli` with its actual `fixture_name`.
[`full-coordination-failure-20261105.json`](full-coordination-failure-20261105.json)
retains the exact original coordinator source/hash, command, exception and
captured 20-case positive monitor console. The corrected coordinator prefers
`fixture_name`, has a regression control for the differing names, and
checkpoints every positive monitor result before final aggregation. **It was
not rerun.**

[`recover_full.py`](recover_full.py) recovered the same original artifacts,
launching zero model processes. The resulting
[`result-full-replay-20261105.json`](result-full-replay-20261105.json) retains the
original complete 83-case and cycle reports. Positive statuses and monotonic
elapsed seconds come from the captured original monitor console; stdout,
stderr, GNU time and RTS data are independently parsed and hashed. The original
per-positive sampled process-group RSS and overall monotonic elapsed time were
not checkpointed: they remain null. GNU time child peak RSS is retained as its
own distinct metric. The recovered exit zero follows the original monitor's
accepted classification; a separately saved waitpid field is unavailable.

| Inventory | Historical baseline | Candidate |
| --- | --- | --- |
| 83 stress slots | 35 reject / 30 accept / 7 timeout / 11 skipped | Same counts |
| 3 cycle inputs | n=2 accept; n=3,4 reject | Same outcomes |
| 20 ordinary positives | 18 accept / 2 timeout | 20 accept |

No completed verdict disagrees with the historical baseline. Stress identities
still matter despite equal totals: pipeline repeated 2048 crossed from accepted
to timeout; its 4096 case consequently changed from timeout to skipped.
Delayed-send distinct 512 crossed from timeout to accepted; its 1024 case was
therefore attempted and timed out, instead of being skipped. These crossings
remain explicit. The two historical ordinary distinct-512 timeouts completed
as accepted at 1.568 s (serial) and 1.529 s (pipeline). Overall `all_expected`
remains false because stress timeouts and skips are inconclusive.

For the same ordinary distinct-256 CLI inputs, cumulative RTS allocation fell
from 2,574,600,544 to 1,220,472,896 bytes (serial), and from 2,360,043,208 to
1,149,422,824 bytes (pipeline). Observed elapsed times were 0.900 to 0.477 s and
0.807 to 0.435 s. These are historical-versus-current bounded observations with
the same fixture/flag identities, rather than repeated matched trials or a
universal speed guarantee. Historical distinct-512 timeouts have no complete
RTS allocation totals, so no allocation ratio is reported for them. Full replay
results retain the production `SourceTrace` meaning; menu diagnostics alone do
not supply that verdict.
