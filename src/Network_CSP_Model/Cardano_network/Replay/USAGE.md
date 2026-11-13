# Replay usage

Both executables accept **normalized traces**, not raw JSON. `Main --help` and
`LookaheadMain --help` provide standalone command references with defaults,
preparation commands, examples and verdict meanings; `-h` also works.
Run examples from the repository root unless stated otherwise.

## Choose a checker

| Model/input | Executable |
|---|---|
| LeiosFetch, bounded prototype Notify, ChainSync, BlockFetch, TxSubmission2 | `Main` |
| Implementation-lookahead Notify, including silenced RequestNext/Votes | `LookaheadMain` |
| Independent local sessions in raw-file order | `Main --interleaved` |
| Communication consistency between matched opposite endpoints | A paired mode |

Accepted means an allowed **prefix** under the selected model, bound and capture
assumptions. It does not establish successful completion, payload validity or
deployed conformance. IO failures, timeouts and heap exhaustion are inconclusive.

## Build outside the repository

From `src/`, with the libraries from `csp-ptree.agda-lib` registered:

```sh
cd src
FETCH_BUILD=/tmp/leios-replay-build
NOTIFY_BUILD=/tmp/leiosnotify-replay-build
agda --compile --ghc-dont-call-ghc --compile-dir="$FETCH_BUILD" \
  --ghc-flag=-O --ghc-flag=-threaded --ghc-flag=-rtsopts \
  Cardano_network/Replay/Main.agda +RTS -M2G -RTS
ghc --make -O -threaded -rtsopts -i"$FETCH_BUILD" \
  -main-is MAlonzo.Code.Cardano_network.Replay.Main \
  "$FETCH_BUILD/MAlonzo/Code/Cardano_network/Replay/Main.hs" \
  -o "$FETCH_BUILD/Main" +RTS -M2G -RTS
agda --compile --ghc-dont-call-ghc --compile-dir="$NOTIFY_BUILD" \
  --ghc-flag=-O --ghc-flag=-threaded --ghc-flag=-rtsopts \
  Cardano_network/Replay/LeiosNotifyPipeLookahead/LookaheadMain.agda \
  +RTS -M2G -RTS
ghc --make -O -threaded -rtsopts -i"$NOTIFY_BUILD" \
  -main-is MAlonzo.Code.Cardano_network.Replay.LeiosNotifyPipeLookahead.LookaheadMain \
  "$NOTIFY_BUILD/MAlonzo/Code/Cardano_network/Replay/LeiosNotifyPipeLookahead/LookaheadMain.hs" \
  -o "$NOTIFY_BUILD/LookaheadMain" +RTS -M2G -RTS
cd ..
```

Separate generation and GHC compilation reduce peak memory. Use `-O` for large
captures. **`-rtsopts` enables runner heap caps.** “Most RTS options are disabled”
means relink with that flag and rerun; it is not a protocol rejection.

## Prepare raw logs

Keep originals and preserve file order. The adapter accepts node JSON,
journal-prefixed JSON and supervisor `message` wrappers. Do not sort timestamps
or concatenate unrelated node logs into a single local replay.

```sh
REPLAY=src/Cardano_network/Replay
RAW=/path/to/node.log
OUT=$(mktemp -d /tmp/mini-replay.XXXXXX)
MAIN=/tmp/leios-replay-build/Main
LOOKAHEAD=/tmp/leiosnotify-replay-build/LookaheadMain
TOOLS="$REPLAY/LeiosNotifyPipeLookahead/tools"
python3 -I -B "$REPLAY/LogProcessing/normalize_logs.py" \
  "$RAW" "$OUT/normalized"
```

The output directory must be new or empty. Default normalization selects all five
protocols and splits connection generations at NewMux. Options:

| Option | Effect |
|---|---|
| `--fetch-only` | Select compatible Fetch records with legacy role-only headers |
| `--exclude-txsubmission2` | Explicitly omit TxSubmission2 if control evidence is missing |
| `--connection-lifecycle` | Use successful handshake/matching handler cleanup instead of NewMux |

Lifecycle mode requires handshake evidence before wire events and thread IDs;
it rejects ambiguous generations and writes `connections.tsv`. It cannot be
combined with `--no-mux-split`. Malformed selected rows stop normalization with
the raw line number; partial output is not a completed normalization.

### LeiosFetch grammar and diagnostics

The current [Fetch parser](LeiosFetchParse.agda) requires `role client` or
`role server` on line 1, then one event per line with this grammar:

```text
<Send|Recv> BlockRequest <hash> <slot>
<Send|Recv> Block <hash> <bytes>
<Send|Recv> BlockTxsRequest <hash> <slot> <numTxs> <bitmaps>
<Send|Recv> BlockTxs <numTxs> <txsBytesSize>
<Send|Recv> Done
```

Hashes and bitmap words are lowercase hex without `0x`; other numbers are
decimal naturals. Bitmaps are `-` for none or `idx:word,idx:word,...`, with
decimal indices. No blank lines or comments are accepted; keep provenance in
a sidecar note. Request `numTxs` must equal bitmap popcount in both roles.
Valid bitmaps have at most 268 entries, strictly ascending indices below 268,
and nonzero words below `2^64`. Offset `64i + r` uses bit `63 − r` of word `i`.
The adapter rejects old `BlockTxs` records carrying any of `ebHash`, `ebSlot`
or `bitmaps` with `old LeiosFetch schema: BlockTxs carries ebHash/ebSlot/bitmaps (pre-e9a99ea74); not supported`.
The parser also rejects that obsolete normalized reply grammar.

A rejected standalone Fetch session prints the rejected event, model state,
then a third line such as `reason: client: reply count mismatch at index 2`.
`wire:` names decoder/state/depth/FIFO/byte-cap checks; `client:` names the
receiving client's count/hash checks, **including on server-role sessions**.
Client sends require every bitmap offset below `maxTxs = 17142`; a padding
offset rejects with `client: request offset exceeds maxTxs`. Server receives
still accept decoder-valid padding offsets through 17151.
Only client receives (including draining) enforce the reply count cap
`maxTxs = 17142` and byte caps `txsCap = 550000`, `ebCap = 660000`.
Server sends have no such caps; checked replies still match the request count/hash.
These are one-sided checks on logged sizes, not checks of full encoded wire sizes. The diagnostic is a best-effort explanation of the checked
reading, not a separate proof; it can say `none: no failed check` when that
reading does not explain a rejection. A client may silently stop and drain
replies by kind without count/hash matching, retaining wire checks and forbidding
new requests. Thus an accepted prefix need not have passed every client check.
When only the draining reading accepts, the standalone report keeps
`accepted (<n> events)` on line 1 and adds `note: checked reading fails at index
<i>: <reason>; accepted only as a draining client` on line 2.
The argument that a later request rules out draining assumes the client's reply
handler ran before its next send; with a separate pipelined receiver thread the
log may show the request first, so such a rejection means "the client erred or
the server misbehaved", not necessarily the precise order printed.
The [bridge statements](README.md#current-schema-leiosfetch-replay-2026-11-11)
return accepted representatives existentially at a coarser observation; counts
are bridged in stage 3.

### Other schema limitations

* Standard TxSubmission2 logs omit `RequestTxIds.blocking` and ID-reply emptiness
  evidence (`txIdCount` or a structured `txIds` array). Agency text does not
  supply all required evidence. Use enriched logs or explicitly exclude it.
* There is no `--exclude-fetch` or control-only normalization flag. For other
  protocols in an incompatible Fetch capture, prepare an explicitly selected
  copy by replacing excluded protocol rows with blank lines, retaining the
  original and documenting exclusions. This preserves line numbers but changes
  bytes/hashes. Never claim to have checked excluded protocols. Notify batch
  processing below already selects Notify independently of Fetch/TxSubmission2.
* Neither executable provides a KeepAlive replay mode.

## Run Main

```sh
"$MAIN" --interleaved "$OUT/normalized/interleaved.txt" 150 1 100 300 4
"$MAIN" --chainsync /work/chainsync-client.txt 300
"$MAIN" --blockfetch /work/blockfetch-client.txt 100
"$MAIN" --txsubmission2 /work/txsubmission-server.txt 4
"$MAIN" /work/fetch-client.txt 150
"$MAIN" --notify /work/prototype-notify-client.txt 1000
```

| Protocol | Default depth | Bound applies to |
|---|---:|---|
| Fetch | 150 | Client outstanding requests |
| Prototype Notify | 1 | Outstanding credits |
| BlockFetch | 100 | Client pipeline |
| ChainSync | 300 | Client RequestNext pipeline |
| TxSubmission2 | 4 | Requester/server pipeline |

Bounds are decimal naturals, including zero. Interleaved optional bounds are
positional in the table's order. Sequential servers ignore client bounds.
`--blockfetch-client FILE [K]` and `--blockfetch-server FILE` remain available.
Use LookaheadMain for lookahead Notify; increasing the prototype bound does not
select that implementation model.

A local file has a role header and directions relative to that endpoint:

```text
role client
Send RequestNext
Recv RollForward
```

The example uses `--chainsync`. An interleaved file instead declares components
and uses zero-based session IDs:

```text
sessions chainsync:client blockfetch:server
0 Send RequestNext
1 Recv RequestRange
0 Recv RollForward
1 Send NoBlocks
```

Interleaving checks independent component states, not matching communication
between nodes. Main prints `accepted`, `rejected` or `parse error`; **its process
exit status does not encode those verdicts**. Read stdout. Rejection is relative
to model/bound and capture assumptions; missing events, wrong boundaries or a
version mismatch can explain it without an implementation violation.

## Run lookahead Notify

For a capture with RequestNext and Votes enabled:

```sh
python3 -I -B "$TOOLS/capture_batch.py" \
  --raw "$RAW" --checker "$LOOKAHEAD" --out "$OUT/notify" \
  --observation driver-log --timeout 60 --heap 512M
cat "$OUT/notify/summary.json"
```

The output directory must be new. Individual verdicts/diagnostics are in
`results.jsonl`; checked inputs are retained in `sessions/` and any `pairs/`.
The batch requires top-level host fields and uses NewMux/Done boundaries.
For supervisor logs or handshake-based generations, normalize selected records
with the normalizer and run the resulting local files explicitly:

```sh
"$LOOKAHEAD" --notify-lookahead /work/notify-client.txt --role client \
  --next-contract generic-next --observation driver-log --assume-fresh
"$LOOKAHEAD" --notify-lookahead /work/notify-server.txt --role server \
  --next-contract node-next --observation driver-log --assume-fresh
```

Use **exactly this argument order**. `generic-next` permits server callback
selection of Canceled; `node-next` uses normal-only selection. These forms use
generic successful client callbacks; a local client ignores the server contract.
`node-next` alone does not select production client policy. For explicit policies:

```sh
"$LOOKAHEAD" --notify-lookahead /work/notify-client.txt --role client \
  --client-policy node-client-control --observation driver-log --assume-fresh
"$LOOKAHEAD" --paired-notify-lookahead /work/pair.txt \
  --node-policy full-node --observation driver-log --assume-fresh
```

The local policy has fixed depth 1000. The paired full-node policy also includes
application credit/FIFO controls. External inputs remain existential choices;
these checks do not certify actual forecast/governor truth or deployed conformance.

If the logger silenced **both** RequestNext and Votes, use
`--observation driver-log-no-request-votes` with a generic-contract form. Present
rows of those kinds are invalid input; do not erase logged rows to obtain
acceptance. Node-policy modes do not support silenced observation. There is no
user depth option. `--assume-fresh` asserts initial state, not freshness detection.

| Binary exit | First-line tag | Meaning |
|---:|---|---|
| 0 | `accepted-prefix` | Some model run explains this prefix |
| 1 | `protocol-rejected` | No run explains it under the selected assumptions |
| 2 | `invalid-input` | Parse, agency or argument failure |
| 3 | `undetermined` | Silenced paired mode has no verdict; not rejection |

Require tag/exit agreement. Untagged IO failure, timeout or heap exhaustion is
inconclusive. `--help`/`-h` exit 0 with no verdict tag. No arguments retain the
invalid-input usage report and exit 2.

For capture declarations and artifact validation, prepare an actual manifest
from the [profile examples](LeiosNotifyPipeLookahead/tools/profiles/README.md):

```sh
python3 -I -B "$TOOLS/replay_lookahead.py" \
  --checker "$LOOKAHEAD" --manifest /work/manifest.json
python3 -I -B "$TOOLS/replay_raw_lookahead.py" \
  --checker "$LOOKAHEAD" --manifest /work/manifest.json \
  --raw-bindings /work/raw-bindings.json
```

Replace illustrative assertions with evidence. Normalized runner defaults are
60 seconds, 512M heap and 16 MiB aggregate input metadata; raw scans have separate
limits. Runner exits differ from binary exits: 0 accepted, 1 rejected, 2 invalid
input, 3 missing declarations, 4 inconclusive (including undetermined). See the
[raw correspondence guide](LeiosNotifyPipeLookahead/tools/README.md).

## Identify sessions and count lifecycles

A local history is keyed by **node, connection addresses, connection generation,
protocol and local role**. It starts at the first observed protocol event in that
lifetime. A duplex connection can have both client and server histories; both
ends can also be recorded separately across nodes.

* Done (BlockFetch: ClientDone) closes only its protocol/role session.
* NewMux closes all open protocol/role sessions on its connection in default mode.
* Lifecycle mode instead uses successful handshakes and matching handler cleanups.
* Cleanup can interrupt Notify without Quit/Canceled/Done. EOF also allows an
  unfinished prefix. Neither establishes graceful protocol termination.

Thus 16 local Notify histories can be 8 local connection-lifetime observations
with two roles each, including both ends where available. They do not imply
16 NewMux events, physical connections or graceful shutdowns.

```sh
column -t -s $'\t' "$OUT/normalized/index.tsv" | less -S
rg -F '127.2.0.2:3002' "$OUT/normalized/index.tsv"
```

`index.tsv` lists session ID, connection, role, events, first/last event timestamps,
end reason and protocol. Lifecycle mode appends generation, handler and handshake
line. `connections.tsv` supplies actual handshake/cleanup coordinates: the last
protocol event time is not the connection close time.

Event i in a local `.txt` is line i+1 (after the role header) and row i of `.src`,
which gives raw line and timestamp. Interleaved maps also carry a zero-based
session ID. IDs follow first-event order: `s0001` corresponds to interleaved ID 0.

## Pair opposite endpoints

Pair a client with the **remote server** for the same conversation. Two opposite
roles at one node are different conversations. Verify reversed addresses, peer
identity and handshake/cleanup windows. Generation labels are local counters:
generation 1 at one node may match generation 0 at a peer with a later capture.
Do not pair by label alone or concatenate raw logs into a pair.

Create a manifest, replacing all illustrative fields:

```json
{
  "protocol": "ChainSync",
  "connection": "node1-node2",
  "session": "matched-lifetime",
  "client": {
    "node": "node1", "connection": "node1-node2", "generation": "0",
    "capture": "fresh", "file": "client.txt",
    "source": "node1.log", "sourceMap": "client.src"
  },
  "server": {
    "node": "node2", "connection": "node2-node1", "generation": "0",
    "capture": "fresh", "file": "server.txt",
    "source": "node2.log", "sourceMap": "server.src"
  }
}
```

```sh
python3 -I -B "$REPLAY/LogProcessing/paired_sessions.py" \
  /work/pair-manifest.json /work/pair.txt
"$MAIN" --paired-chainsync /work/pair.txt 300
```

Protocol names are `ChainSync`, `BlockFetch`, `TxSubmission2`, `LeiosFetchP` and
`LeiosNotifyP`. Other Main paired modes are `--paired-blockfetch`,
`--paired-txsubmission2`, `--paired-fetch` and `--paired-notify`, with the same
protocol defaults as their local modes. For lookahead Notify:

```sh
"$LOOKAHEAD" --paired-notify-lookahead /work/notify-pair.txt \
  --next-contract node-next --observation driver-log --assume-fresh
```

The helper preserves per-endpoint order and original source coordinates without
imposing cross-node timestamp order. Missing remote logs cannot be reconstructed
by mirroring local events. The batch helper matches literal reversed addresses
at different hosts with equal generation labels; verify the labels' real meaning.
Check endpoints locally first and use bounded runners for paired search. A full
history timeout remains inconclusive; an accepted shorter prefix does not replace it.
