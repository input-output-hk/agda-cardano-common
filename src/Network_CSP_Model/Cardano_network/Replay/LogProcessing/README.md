# Mini-protocol log processing

Python scripts for adapting captured mini-protocol logs, preparing explicit
client/server pairs and testing the compiled trace replay checker. The scripts
use Python's standard library and support isolated execution with `python3 -I`.

| Script | Purpose |
|---|---|
| `normalize_logs.py` | Normalize raw mini-protocol logs into sessions, an interleaved stream and source maps; use `--fetch-only` for legacy Fetch-only output |
| `paired_sessions.py` | Assemble an explicitly declared fresh ChainSync, LeiosNotifyP or LeiosFetchP pair from a JSON manifest |
| `chainsync_pair.py` | Compatibility entry point for the paired-session normalizer |
| `test_*_replay.py` | Compiled-checker regressions for standalone/mixed protocols and paired ChainSync/Leios captures |

The scripts remain siblings because the compatibility entry point
and tests locate each other relative to `__file__`. They can be invoked from
any working directory by supplying their paths; no package installation is
required. Relative paths inside a pair manifest resolve against the manifest's
directory.

From this directory:

```sh
python3 -I normalize_logs.py --help
python3 -I normalize_logs.py --selftest
python3 -I normalize_logs.py /path/to/node.log /tmp/replay-input
python3 -I normalize_logs.py /path/to/node.log /tmp/fetch-input --fetch-only
python3 -I paired_sessions.py manifest.json /tmp/paired-input.txt
```

`normalize_logs.py` replaces both former adapter entry points. Its default
includes Fetch, Notify, BlockFetch, ChainSync and TxSubmission2 with protocol-tagged
session headers and filenames. `--fetch-only` retains the former Fetch-only
role headers, unqualified filenames and output fields. `--no-mux-split` and
`--exclude-txsubmission2` remain explicit options; the latter is unnecessary
and rejected with `--fetch-only`. Run `--selftest` without input paths or other
options to check both formats and the CLI diagnostics.

To run all six CLI regression suites, first compile `Replay/Main.agda` as
explained in the [replay README](../README.md), then run:

```sh
for test in test_*_replay.py; do
  python3 -I "$test" /tmp/leios-replay-build/Main
done
```

The checker accepts finite prefixes. Raw-log completeness, session identity and
fresh endpoint pairing remain input requirements; normalization does not
invent omitted protocol events. See the [replay README](../README.md) for
protocol coverage, observation limits and proof scope.
