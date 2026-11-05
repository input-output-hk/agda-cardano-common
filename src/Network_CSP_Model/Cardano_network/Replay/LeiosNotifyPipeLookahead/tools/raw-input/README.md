# Raw Notify input correspondence

`lookahead_raw.py` rederives a selected endpoint's normalized events and original
coordinates from untouched structured JSON bytes. This is executable input
correspondence, **not an Agda proof of Python, the logger or deployed Haskell**.
The existing normalized adapters and checker retain their theorem scopes.

The implementation reuses
[`normalize_notify`](../../../LogProcessing/normalize_logs.py) for field encoding
and [`paired_sessions.event`](../../../LogProcessing/paired_sessions.py) for the
existing normalized grammar. Strict envelope checks precede those helpers:
missing message kinds and contradictory direction cannot acquire defaults.

## Supported raw schema

Input is UTF-8, one structured JSON object per physical line, optionally after
a journal prefix. A supervisor wrapper may contain one node object in `message`
or a JSON string in `message`. Outer physical line and byte positions are kept.
Nonblank unstructured/malformed lines, duplicate JSON keys, non-finite numbers
(including overflow such as `1e999`) and unrecognized envelope shapes fail.
Blank lines are counted. Ordinary other namespaces are counted and ignored.

Notify rows use `ns = LeiosNotify.Remote.Send.KIND` or
`LeiosNotify.Remote.Receive.KIND`, `host`, a single-token `at`, and `data` with:

- `kind = Send` or `Recv`, agreeing with the namespace.
- `msg.kind` with the explicit constructor name below.
- A literal `connectionId` under `peer`, `bearer`, or `data` itself. Structured
  local/remote address objects are also supported. Multiple supplied IDs must
  agree. Literal socket spelling is retained without DNS/NAT/IP canonicalization.

| Namespace kind | Required `msg.kind` | Canonical retained fields |
| --- | --- | --- |
| RequestNext or NotificationRequestNext | MsgLeiosNotificationRequestNext | None |
| Quit | MsgQuit | None |
| BlockAnnouncement | MsgLeiosBlockAnnouncement | Either all `ebHash`, `ebSlot`, `ebBodySize`, or all absent |
| BlockOffer | MsgLeiosBlockOffer | `ebHash`, `ebSlot`, `ebBytesSize` |
| BlockTxsOffer | MsgLeiosBlockTxsOffer | `ebHash`, `ebSlot` |
| Votes | MsgLeiosVotes | Array `votes`, each containing `rbHash` and `voterId` |
| Canceled | MsgCanceled | None |
| Done | MsgDone | None |

Hex strings must be nonempty and are encoded lowercase. Natural fields must be
JSON integers at least zero; booleans and floating-point values are rejected.
Absent announcement metadata encodes `-`; partial/null metadata is invalid.
Vote order and duplicate votes remain exact. An empty vote list encodes `-`.
Additional native header/body/signature fields are outside this summary schema.

The complete Notify family is validated **before endpoint selection**. Unknown
kinds, bad fields or agency contradictions on another endpoint still fail the
scan; a selector cannot hide an invalid selected-family record. The separate
`LeiosNotify.Remote.Serialised.*` observation family is explicitly excluded and
counted rather than treated as a second wire-message stream.

## Explicit selection and generations

An endpoint selector has exactly these fields:

```json
{
  "host": "node-a",
  "connection": "10.0.0.1:3001 10.0.0.2:3001",
  "role": "client",
  "observedMuxGeneration": 1,
  "segmentAfterDone": 0
}
```

Role follows protocol message agency, not an inferred Haskell peer entry point.
Observed NewMux generations are counted independently per host/literal
connection, beginning at 1; 0 means no preceding NewMux was observed. Done closes
that role's segment; a subsequent row advances `segmentAfterDone`. Another
NewMux starts a new generation with segment 0. Mux Dead does not split rows.
None of these coordinates establishes freshness or capture completeness. A
selector matching no rows fails rather than silently producing an empty check.

## Normalize and verify

From the repository root, with an explicit selector file:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/raw-input/lookahead_raw.py \
  normalize --raw /path/to/node.jsonl --selector /path/to/selector.json \
  --out /tmp/new-notify-endpoint
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/raw-input/lookahead_raw.py \
  verify --raw /path/to/node.jsonl --selector /path/to/selector.json \
  --normalized /tmp/new-notify-endpoint/local.txt \
  --source-map /tmp/new-notify-endpoint/local.src \
  --detailed-map /tmp/new-notify-endpoint/map.jsonl
```

The output directory must be new and is published after the complete scan.
`local.txt` has the existing role header and canonical Send/Recv grammar.
`local.src` has raw line and original timestamp on each row, compatible with
the existing paired assembler. `map.jsonl` additionally retains source path,
line, byte offset/length, exact raw-line SHA-256, original namespace, canonical
event, host/connection/role, generation/segment, thread fields and preceding
NewMux coordinates. `selector.json` retains the explicit selection.

Verification compares the entire canonical bytes of all three artifacts against
fresh rederivation, including row counts and EOF. Reformatting a detailed map or
moving the raw source path requires regeneration. Every source line is read in
file order; timestamps do not sort rows, and repeated identical messages remain
distinct. A changed payload, metadata-only change, coordinate change, additional
row or omitted row fails correspondence. Raw and artifact identity/size/times
are checked for concurrent change, but these checks are not authentication or a
filesystem transaction.

Successful output is `correspondence-checked` with `protocolVerdict: null` and
exit 0. Invalid schema/selection/correspondence exits 2. Resource limits or
changing files exit 4 as inconclusive. No successful invocation is a protocol
acceptance/rejection verdict. The separate raw replay coordinator can run the
existing model checker after this correspondence check.

## Python API and resource limits

`scan_raw(path, *, limits=None)` returns a one-use iterable. Each yielded dict
has the detailed-map fields plus normalized `direction` (`Send`/`Recv`) and
`kind`. After complete consumption, `scan.summary` has file hash/signature,
counts and lifecycle-state totals. An incomplete/failed scan has no summary.

`normalize_selected(raw_path, selector, output_dir, *, limits=None)` publishes
the endpoint artifacts and returns their identities. The read-only
`verify_selected(raw_path, selector, normalized_path, source_map_path,
detailed_map_path, *, limits=None)` returns the same scope/status with verified
raw/artifact hashes and signatures. Invalid input raises `RawInputError`;
`ResourceLimitError`, a subclass, distinguishes incomplete bounded work.

Limits are an optional dict; unknown keys fail:

| Key | Default | Scope |
| --- | ---: | --- |
| max_line_bytes | 1 MiB | Each original raw physical line |
| max_raw_bytes | 16 GiB | Complete raw file/actual scan |
| max_records | 10,000,000 | Physical raw lines |
| max_states | 100,000 | Retained generation/role-segment keys |
| max_metadata_bytes | 16 MiB | Accounted retained lifecycle key payload plus fixed allowance per key |
| max_seconds | 300 | Elapsed raw scan, including consumer work between yields |
| max_artifact_bytes | 16 MiB | Aggregate selected local/source/detailed-map artifacts |

Raw lines and output are streamed. The state/key budgets constrain retained
metadata; they are not an operating-system RSS guarantee. Python object overhead
and parsed JSON also consume memory. CLI limit flags use hyphenated key names.
Exit 4 must never be promoted to protocol rejection.

## Validation and remaining obligations

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/raw-input/test_lookahead_raw.py
```

The synthetic regressions cover all eight kinds, both agencies, optional
announcement metadata, ordered duplicate Votes, duplicate complete events,
byte-exact UTF-8 coordinates, wrappers, explicit generation reuse, unknown and
malformed selected rows, payload/thread/artifact tampering, strict JSON and
resource controls. The [result record](result-raw-input-20261105.json) retains
source identities and validation evidence.

No original logger emission or log shipping fidelity is proved. Missing
RequestNext cannot be repaired by this normalizer. Deployment provenance,
freshness/order/losslessness and endpoint pairing still need independent
evidence. Full native payload correspondence, formal Python correctness and
real complete testnet replay remain open. No Agda source was changed here.
