# Mini-protocol log processing

Python scripts for adapting captured mini-protocol logs, preparing explicit
client/server pairs and testing the compiled trace replay checker. The scripts
use Python's standard library and support isolated execution with `python3 -I`.

| Script | Purpose |
|---|---|
| `normalize_logs.py` | Normalize raw mini-protocol logs into sessions, an interleaved stream and source maps; use `--fetch-only` for legacy Fetch-only output |
| `paired_sessions.py` | Assemble an explicitly declared fresh ChainSync, LeiosNotifyP or LeiosFetchP pair from a JSON manifest |
| `chainsync_pair.py` | Compatibility entry point for the paired-session normalizer |
| `test_connection_lifecycle.py` | Raw-log generation, boundary evidence and ambiguity regressions |
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

## Devnet captures without NewMux

Choose `--connection-lifecycle` when the capture provides connection-manager
handshake and cleanup records rather than mux creation records:

```sh
python3 -I normalize_logs.py /path/to/node.log /tmp/devnet-replay --connection-lifecycle
python3 -I test_connection_lifecycle.py
```

This mode uses `Net.ConnectionManager.Remote.ConnectionHandler.HandshakeSuccess`
to open a generation and `Net.ConnectionManager.Remote.ConnectionCleanup` from
that same handler thread to close it. Structured lifecycle socket addresses are
matched to textual wire `connectionId` values, including IPv6. A cleanup closes
all open protocol/role sessions for that generation as interrupted prefixes.
A later handshake may then open a fresh generation. Each generation is numbered
from zero for its address pair; a session's global `sNNNN` identifier remains unique.

`connections.tsv` records each generation's handler thread, handshake and cleanup
raw line numbers and timestamps. In this mode, `index.tsv` also appends
`connectionGeneration`, `handlerThread` and `handshakeLine`; its `end` may be
`connection`. Event rows and source maps keep their original order and coordinates.

The capture must be ordered and from one node process, with handshake evidence
before its wire events and thread IDs on handler and wire records. A new handler
before the old one is cleaned up, a wire event outside a live generation, and a
known old wire thread appearing in a newer generation produce input errors.
Cleanups from other/old handler threads cannot close the current generation.
A duplicate handshake on the current handler does not reset the protocol state.
Mux errors, `Dead`, repeated `Init` and repeated `FindIntersect` do not authorize
resets. This mode uses the declared connection lifecycle instead of NewMux and
cannot be combined with `--no-mux-split`; `--fetch-only` remains available.

Thread binding is additional consistency evidence, not proof of physical packet
provenance. It cannot disambiguate arbitrary reordered, missing or multi-process
logs, or a delayed actor never previously observed in the capture. Use a fresh
output directory per attempt; an input error can leave incomplete output files.
The default NewMux mode and its legacy output schema remain unchanged.

## Regression checks

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
