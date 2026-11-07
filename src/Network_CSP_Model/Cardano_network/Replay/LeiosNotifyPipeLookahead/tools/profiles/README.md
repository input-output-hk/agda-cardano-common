# Lookahead replay manifests

`lookahead_manifest.py` validates the supported profile and explicit capture
declarations before a runner invokes the dedicated `LookaheadMain`. It uses only
Python's standard library. It never executes a checker, opens a capture, verifies
a capture checksum, or issues a protocol verdict. Legacy `Replay/Main.agda` modes
and the older `LogProcessing/paired_sessions.py` manifests are unchanged.

```sh
python3 -I ../lookahead_manifest.py --selftest
python3 -I ../lookahead_manifest.py --example paired
python3 -I ../lookahead_manifest.py manifest-paired.example.json
```

The examples contain **illustrative capture assertions**, not evidence about an
existing capture. Replace those assertions and paths before using them. A
`ready` result means required assumptions have been declared in supported form;
it does not establish that they are true. Paths can be absent while this
structural validator reports `ready`.

The structural schema is [manifest-v1.schema.json](manifest-v1.schema.json).
Examples are provided for [local client](manifest-localclient.example.json),
[local server](manifest-localserver.example.json),
[paired](manifest-paired.example.json), and explicit
[node-client control](manifest-nodeclient.example.json) and
[full-node paired](manifest-full-node.example.json) inputs. The Python validator additionally
checks distinct paired node identity declarations and classifies missing capture
assertions. JSON Schema validation alone is not the complete readiness check.

## Supported profile

The version is `leiosnotify-lookahead-manifest-v1`, protocol `LeiosNotifyP`.
Every profile explicitly records:

| Field | Supported value |
|---|---|
| `mode` | `localclient`, `localserver`, or `paired` |
| `observation` | `driver-log` |
| `clientCallbacks` | `generic-successful`, or `node-client-control` with `localclient` or explicit paired `nodePolicy: full-node` |
| `nodePolicy` | Optional; if supplied it must be `full-node` with paired mode, node-client-control and node-next |
| `return` | `unit` |
| `serverContract` | Explicit `generic-next` or `node-next` |
| `eof` | `prefix` |

`node-client-control` selects the standalone `NodeClientModel` source language:
fixed depth 1000, unit return, successful normal handlers and an explicit
unexpected-Canceled failure state. Forecast/stop decisions remain existential
source inputs. This does not establish actual forecast/governor truth, the
combined `NodeDriverModel` credit/FIFO policy, observed exceptions or deployed
implementation conformance. A Canceled Receive before its Quit Send hook is not
alone a policy violation: inspection can wait until the stop flag is published.
EOF remains a prefix, including prefixes compatible with an unobserved fault.

Without `nodePolicy`, this local selection is supported only with
`mode: "localclient"`; paired and local-server requests are rejected rather than
routed to the generic checker. The legacy
`serverContract` field remains required and validated, but is unused by this
local policy. The report marks `serverContractUsed: false` and emits
`--client-policy node-client-control` without `--next-contract`.

The distinct `nodePolicy: "full-node"` profile requires `mode: "paired"`,
`clientCallbacks: "node-client-control"` and `serverContract: "node-next"`.
It selects the unchanged full `NodeDriverModel` including the depth-1000 client,
credit/FIFO application queue and Cancel-handler fault. Its report marks
`serverContractUsed: true`, preserves existential external inputs, and emits
`--paired-notify-lookahead FILE --node-policy full-node --observation driver-log --assume-fresh`.
It has no local-server/client fallback. See the
proofs, build and checked CLI/coordinator evidence (historical development evidence removed).
Actual input truth and capture/deployment correspondence remain external.

The generic client profile does not select a fixed depth or the deployed node's
credit/queue policy. `node-next` identifies the server callback contract only.
It does not claim that the entire checker is a fixed node-policy checker. The
client profile declarations remain visible in local-server manifests for a
uniform profile vocabulary; the local-server theorem does not check a client.

`checkerInput` separates the normalized checker input from capture provenance:

```json
{"format": "paired-v1", "file": "pair.txt", "sha256": null}
```

Use `local-v1` for either local mode: its file has an existing `role client` or
`role server` header and normalized message lines. Use `paired-v1` for an existing
`PairedParse` input: pair declaration, two fresh endpoint declarations, and
role/source-line-tagged rows. This validator does not assemble files or check
their headers, rows, coordinates, or consistency with the manifest. That belongs
to the runner/input adapter. It introduces no new trace syntax or timestamp sort.

## Capture and provenance declarations

`connection` and `session` identify the declared local or paired check. Each
selected endpoint has `node`, local `connection`, `generation`, and `file`.
Exactly `client` is allowed in local-client mode, exactly `server` in local-server
mode, and both are required in paired mode. Pairing is explicitly declared; no
reverse-address, NAT, DNS, or generation equivalence is inferred. Distinct node
identity declarations match the existing paired-input format's requirement.

The endpoint `file` names its input/session artifact. Optional `source` and
`sourceMap` must appear together to name a raw capture and its original-line
coordinate map. Paths resolve relative to the manifest directory and can contain
spaces. These paths are metadata here; this validator does not invent source
coordinates or verify the map. Optional `sha256`, `sourceSha256`, and
`sourceMapSha256` are **declared**, unverified hashes. `checkerInput.sha256` has the
same status until a runner verifies its file bytes.

A fresh initial-state assertion and ordered/lossless capture assertions are
required for `ready`:

```json
{
  "capture": "fresh",
  "captureEvidence": {
    "ordered": true,
    "lossless": true,
    "basis": "Operator assertion: explain the actual capture boundary and collection method"
  }
}
```

`basis` is the stated basis for these **assertions**, not a certificate checked by
Python. Missing assertions, `capture: "unknown"` or `"partial"`, and absent/false
ordered or lossless assertions yield `missing-capture-evidence`. Suffix
initialization is unsupported. A partial EOF remains acceptable when the capture
starts fresh and preserves all selected records up to its cutoff. Prefix
acceptance does not establish successful completion, including when `Done`
appears elsewhere in a capture.

Endpoint `provenance` optionally records `sourceRevision` (full immutable 40-digit
SHA), `binarySha256`, `buildId`, and `note`. Missing/null values remain visibly
unknown. These too are declarations; source/build attribution is not verified by
this module. Unknown deployed provenance permits conditional model checking but
does not imply deployed conformance.

`model.consensusRevision` separately names the modeled upstream pin
`2416493bfdbe93b761b3a4bb1ccf2b4a913e5e4b`. An omitted `model` uses this known model
pin; it is never copied into deployed `provenance.sourceRevision`.
`model.repositoryRevision`, if supplied, is a declared model-repository SHA. A
runner should separately record the actual checker build/source identity.

## Python interface and executable boundary

`validate_manifest(data, base_dir)` takes a decoded object without reading files.
`load_manifest(path)` reads only that JSON manifest and rejects duplicate keys at
every nesting level, malformed JSON, and non-JSON numeric constants. Both return
a JSON-compatible report:

| Report field | Meaning |
|---|---|
| `status` | `ready`, `invalid-input`, or `missing-capture-evidence` |
| `errors` | Located structural/profile errors |
| `missingEvidence` | Located missing capture assertions |
| `protocolVerdict` | Always `null`; only the actual checker can decide a trace |
| `profile` | Explicit requested profile and callback contract |
| `endpoints` | Resolved artifact paths and declared identity/evidence/provenance |
| `model` | Model pin, separate from deployed provenance |
| `checkerInput` | Resolved normalized input path and declared checksum |
| `checkerArguments` | Argument list for a ready profile, otherwise `null` |

Structural errors take precedence over missing evidence while both lists remain
available. Standalone process exit codes are `0` for `ready`, `2` for
`invalid-input`, and `3` for `missing-capture-evidence`. None means protocol
rejection.

Arguments for the dedicated executable are returned without an executable name:

```text
--notify-lookahead FILE --role client|server --next-contract generic-next|node-next --observation driver-log --assume-fresh
--paired-notify-lookahead PAIR --next-contract generic-next|node-next --observation driver-log --assume-fresh
--notify-lookahead FILE --role client --client-policy node-client-control --observation driver-log --assume-fresh
```

The runner must use the argument list directly, validate input/header/coordinate
and optional checksum consistency, retain declared assumptions and unknown
provenance in its report, and keep input/evidence failures separate from actual
protocol rejection. This manifest validator is operational input checking, not
an Agda proof or a replacement for the certified checker.

The node-client manifest extension record (historical development evidence removed)
retains 108 pure controls and 36 exact legacy-report comparisons. It records no
checker invocation or protocol verdict; example input files may remain absent.
