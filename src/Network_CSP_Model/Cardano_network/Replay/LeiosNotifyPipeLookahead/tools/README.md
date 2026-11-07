# LeiosNotify lookahead tools

Use `replay_lookahead.py` for normalized replay and `replay_raw_lookahead.py`
for raw-log replay. `lookahead_manifest.py`, `profiles/` and `raw-input/`
provide configuration and normalization. See the [replay guide](../README.md).

`check_agda.py` and `certify.py` support bounded Agda checks and certificates.
`run.py` and `Main.hs` retain controlled peer/driver regression scenarios.

Profiling, search stress, completion-history, arithmetic investigation and
candidate-patch tools and their associated reports have been removed.
Development evidence bundles and dated result reports have also been removed.
Historical research notes may still describe their earlier results.

## Normalized lookahead CLI and manifest runner

The wave after `1f5d4eb7` adds standalone native client transport, exact
normalized client/paired adapters, a dedicated CLI and explicit profile
manifests. [The replay guide](../README.md#normalized-input-and-cli-delivery)
states the generic successful-client/unit-return scope, prefix semantics and
raw-fidelity limitations. Existing `Replay/Main.agda` is unchanged.

Build `LookaheadMain` separately. Use a fresh disk-backed output directory;
splitting generation and GHC avoids holding both heaps simultaneously. From
the repository root:

```sh
LOOKAHEAD_BUILD=/var/tmp/leiosnotify-lookahead-build
agda --compile --ghc-dont-call-ghc -i src \
  --compile-dir="$LOOKAHEAD_BUILD" \
  --ghc-flag=-O0 --ghc-flag=-threaded --ghc-flag=-rtsopts \
  src/Cardano_network/Replay/LeiosNotifyPipeLookahead/LookaheadMain.agda \
  +RTS -M2G -RTS
ghc --make -O0 -threaded -rtsopts -i"$LOOKAHEAD_BUILD" \
  -main-is MAlonzo.Code.Cardano_network.Replay.LeiosNotifyPipeLookahead.LookaheadMain \
  "$LOOKAHEAD_BUILD/MAlonzo/Code/Cardano_network/Replay/LeiosNotifyPipeLookahead/LookaheadMain.hs" \
  -o "$LOOKAHEAD_BUILD/LookaheadMain" +RTS -M2G -RTS
```

`LookaheadMain` is the new ordinary IO/environment/exit boundary; it is not a
safe theorem module. Its proof/report dependencies are checked separately with
`--safe`. Build evidence records the actual generated GHC command and toolchain;
the commands above reproduce the same two-stage method. Installed library
interface caches may need to be generated on first use of stdlib exit bindings.

Copy a [profile example](profiles/README.md), replace its illustrative capture
assertions/paths with actual declarations, and supply normalized local or paired
input in the existing grammar. Then use the bounded runner:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/replay_lookahead.py \
  --checker "$LOOKAHEAD_BUILD/LookaheadMain" --manifest /path/to/manifest.json
```

Default runtime limits are 60 seconds, 512M checker heap and 16 MiB aggregate
normalized input/source-map bytes. Raw source hashes stream. The runner validates
declared artifacts, preserves each role's order/coordinates and checks the
binary's verdict tag against its exit code. Output is JSON. Exit classes are
0 accepted prefix, 1 protocol rejected, 2 invalid input, 3 missing capture
assertions, and 4 inconclusive/resource/checker failure. Untagged direct CLI IO
exceptions are inconclusive, never a rejection proof. The validator alone
neither opens captures nor executes the checker.

Lightweight isolated checks and the compiled-CLI regression suite are:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/lookahead_manifest.py --selftest
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/replay_lookahead.py --selftest
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/test_lookahead_cli.py \
  --binary "$LOOKAHEAD_BUILD/LookaheadMain" --out /tmp/new-lookahead-cli-regressions
```

The wave record (historical development evidence removed) retains 12 fresh safe
modules, the separately typechecked/compiled IO entry point, 93 manifest
selftests, 27 fake-checker runner controls, 62 real compiled CLI regressions
and 10 real-binary manifest smoke cases. The compiled CLI cases complete with
no runtime budget failure, and legacy Main hashes match. One intentionally
tiny runner timeout is classified inconclusive. These synthetic tests do not
establish raw-log fidelity, source-map authenticity, whole-node completion,
large-capture performance or deployed implementation refinement.

## Raw capture preparation and correspondence

Start with the [capture preflight guide](capture-preflight/README.md). The
inspected local testnet config silences RequestNext and Votes in both directions;
the [example overlay](capture-preflight/notify-debug-overlay.example.json) is an
unapplied fragment for review against the actual deployed configuration. The
strict October 29 rescan confirms the old missing-request diagnosis, without
attributing that capture to the inspected config or rejecting the protocol.

The [raw helper guide](raw-input/README.md) specifies the accepted envelope,
selectors, canonical maps and limits. Normalize each explicitly selected endpoint
into a new output directory, retaining raw originals:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/raw-input/lookahead_raw.py \
  normalize --raw /captures/client.log --selector /work/client-selector.json \
  --out /work/client
```

The outputs are `local.txt`, `local.src`, `map.jsonl` and `selector.json`.
Repeat for the server when checking a pair. The selector names exact `host`,
`connection`, `role`, `observedMuxGeneration` and `segmentAfterDone`; generation
zero means no NewMux was observed. No freshness or peer identity is inferred.

Prepare an existing [profile manifest](profiles/README.md), naming each endpoint's
`local.txt` as `file`, original log as `source`, and `local.src` as `sourceMap`.
For local mode, `checkerInput.file` can name that same `local.txt`. For paired
mode, assemble `pair.txt` with the existing
[paired session helper](../../LogProcessing/paired_sessions.py) and its existing
manifest format; it takes the endpoint fields `node`, `connection`, `generation`,
`capture`, `file`, `source` and `sourceMap`, rather than the entire new profile
manifest. Pairing and fresh/ordered/lossless assertions must have an operator's
stated basis. Keep unknown deployed revisions unknown.

Copy the [raw bindings example](raw-replay-bindings.example.json), retain exactly
the roles in the replay manifest, and replace selectors/maps with the actual
selection. Detailed-map paths resolve relative to this bindings file. Then run:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/replay_raw_lookahead.py \
  --checker "$LOOKAHEAD_BUILD/LookaheadMain" \
  --manifest /work/replay-manifest.json --raw-bindings /work/raw-bindings.json
```

This opt-in coordinator rederives every selected normalized event and canonical
line/byte/thread-map row before invoking the unchanged normalized runner. Selected
event omission, payload/coordinate tampering and extra rows fail distinctly from
model rejection. Exit classes remain 0 accepted prefix, 1 completed model
rejection, 2 invalid input, 3 missing declarations and 4 inconclusive. File
mutation/deletion and allocation failures remain inconclusive. The checker still
requires a matching verdict tag and exit code.

The default raw limits apply per endpoint scan: 16 GiB, ten million lines and
300 seconds, with the raw helper's bounded line/lifecycle state. The default
16 MiB aggregate metadata budget here includes the manifests, checker input,
local traces and both map formats. `--max-raw-bytes`, `--max-raw-records`,
`--max-raw-seconds` and `--max-input-bytes` override these explicitly; the
checker's separate `--timeout` defaults to 60 seconds and `--heap` to 512M.
Repeated scans of a shared raw file are deliberate, bounded and not an event
deduplication strategy. This is executable correspondence to supplied bytes,
not a formal proof about Python, a lossless logger or the deployed implementation.

Run the new controls with:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/capture_preflight.py --selftest
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/raw-input/test_lookahead_raw.py
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/test_replay_raw_lookahead.py
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/test_replay_raw_lookahead.py \
  --binary "$LOOKAHEAD_BUILD/LookaheadMain"
```

The cost guide (historical investigation tooling removed) records severe observed schedule-order
sensitivity in paired search. It recommends local-first checks and explicit
paired limits, preserving the full trace and inconclusive results. It adds no
checker optimization. The wave record (historical development evidence removed)
consolidates the new validation; no Agda source or existing binary is changed.

## Silenced observation and capture batch replay

When the logger silences RequestNext and Votes in both directions, use the
existing CLI forms with `--observation driver-log-no-request-votes`:

```sh
LookaheadMain --notify-lookahead FILE --role client|server \
  --next-contract generic-next|node-next --observation driver-log-no-request-votes --assume-fresh
LookaheadMain --paired-notify-lookahead PAIR \
  --next-contract generic-next|node-next --observation driver-log-no-request-votes --assume-fresh
```

`LookaheadMain`'s usage text intentionally does not list these forms, because
the existing modes keep byte-identical output. A silenced RequestNext/Votes row
in the input is `invalid-input`; the checker never erases it. Checker exit 3 is
`undetermined`: both local silenced checks pass but no paired protocol verdict
exists. It is only reachable in silenced paired mode. `replay_lookahead.py`
reports it as `model-undetermined` with exit class 4 and no protocol verdict.

`capture_batch.py` replays every Notify session of a multi-host raw capture:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/capture_batch.py \
  --raw /captures/all-hosts.log --checker "$LOOKAHEAD_BUILD/LookaheadMain" \
  --out /var/tmp/new-batch-dir --observation driver-log-no-request-votes \
  [--timeout 60] [--heap 512M]
```

The tool works as follows:

- It splits the log by its top-level JSON `host` field. A Notify or NewMux row
  without one is an input error (exit 2), and no DIR is created.
- It runs `normalize_logs.split_into(..., include_notify=True)` on each host
  subset. Other lines are blanked, so the source maps keep raw line numbers.
- Each server session runs locally under `generic-next` and `node-next`. Each
  client session runs once, with contract `-`.
- A client at host A on connection `x y` is paired only with the unique server
  at another host on the literal `y x` with the same generation. Generation is
  `<NewMux rows for that host/connection before the session>.<Done segment>`.
  Addresses are never canonicalized. Each pair runs under both contracts.
- Runs are sequential. Each run gets a timeout and an `+RTS -M<heap> -RTS` cap.
  A timeout, the output budget or heap exhaustion gives `resource-inconclusive`.
  An exit code that disagrees with the first-line tag gives
  `checker-inconclusive`.

DIR must be new. It receives:

- `results.jsonl`, one row per run with the keys `host connection role
  generation mode contract status exit seconds firstDiagnostic sourceFile`.
  Paired rows have `host: [client, server]` and `role: pair`.
- `summary.json`, counts keyed `mode/role/contract/status` plus `pairedMatched`
  and `pairedUnmatched` (sessions in no pair).
- `input.sha256`.
- The `sessions/` and `pairs/` inputs that were checked.

`--selftest` uses a synthetic two-host capture and a fake checker, plus a
timeout control. `--selftest --checker BIN --out DIR` runs the same assertions
with a real binary. Silenced acceptance is not full-observation acceptance.
