# LeiosNotify capture preflight

This prepares T8.1. It does not start nodes, change deployed configurations or
decide protocol compatibility. The original four captures and their historical
[audit](../capture-audit/README.md) remain unchanged.

## A concrete configuration finding

**Confirmed local-source finding:** the local config file matches HEAD in
`input-output-hk/ouroboros-leios` at
[`614b10d21691e40ed3a3e5a3462b08497fcfe443`](https://github.com/input-output-hk/ouroboros-leios/blob/614b10d21691e40ed3a3e5a3462b08497fcfe443/testnet/config/config.json)
contains these entries in `testnet/config/config.json`:

```json
"LeiosNotify.Remote": {"maxFrequency": 0, "severity": "Debug"},
"LeiosNotify.Remote.Receive.RequestNext": {"severity": "Silence"},
"LeiosNotify.Remote.Receive.Votes": {"severity": "Silence"},
"LeiosNotify.Remote.Send.RequestNext": {"severity": "Silence"},
"LeiosNotify.Remote.Send.Votes": {"severity": "Silence"}
```

The four specific `Silence` entries must be considered when inspecting the
actual runtime configuration; observing the parent `Debug` setting is not enough.
The [example overlay](notify-debug-overlay.example.json) changes those four
entries to explicit `Debug` and `maxFrequency: 0`. It is an **unapplied fragment**,
not a standalone node config. Merge the entries into a copy of the actual build's
configuration, retaining its other fields, namespace spellings and backend
settings. Review the effective tracer configuration and confirm emitted events
with the preflight before a long capture. No external config is edited here.

**Inference:** this local configuration is a plausible explanation for the
simultaneous absence of RequestNext and Votes in the old logs. Its use by the
deployed nodes has not been established. The old capture's build/configuration
provenance remains unknown; this finding does not identify a lost line or prove
that Votes was generated.

The inspected source path is:

| Layer | Source and inspected behavior |
| --- | --- |
| Protocol/driver selection | Consensus `2416493bfdbe93b761b3a4bb1ccf2b4a913e5e4b`, `Ouroboros/Consensus/Network/NodeToNode.hs`: the client uses `runPipelinedPeerWithLimits`; the server uses `runLookaheadFixedSenderPeerWithLimits`; both receive `tLeiosNotifyTracer` |
| Message namespace/severity | Same consensus pin, `tracing/Ouroboros/Consensus/Tracing/Leios.hs`: RequestNext and all seven other kinds have named namespaces; message severity is `Debug` |
| Machine message object | Same pin, `LeiosDemoTypes.messageLeiosNotifyToObject`: RequestNext emits `kind: MsgLeiosNotificationRequestNext`; other messages use their existing metadata summaries |
| Direction envelope | Network `4b3ab7664f609a1aee0f0c24dcfcfd0ab899fc42`, `tracing/Ouroboros/Network/Tracing/Driver.hs`: `Send`/`Receive` namespace prefixes, `Send`/`Recv` machine direction values, severity/privacy delegated to message metadata |
| Testnet configuration | Leios `614b10d21691e40ed3a3e5a3462b08497fcfe443`, `testnet/config/config.json`: parent Debug plus the four Silence overrides above |

The message's ultimate privacy default and the complete node-to-backend runtime
wiring were not established from these files. The available main `cardano-node`
checkout at `97036a66bcf8c89f687ae57a048eecc0389977ef` has no Leios tracing matches,
so it must not be treated as the deployed Leios node source. The
[source evidence](source-evidence-20261105.json) retains exact paths, SHA-256,
HEAD blob comparisons and attribution limits. No public URL was fetched to
establish these local-source findings.

The previous [exporter audit](../capture-audit/README.md#nearby-exporter-risks-with-attribution-limits)
also remains relevant: a nearby example query omits RequestNext/Votes/Quit/Canceled,
and timestamp-only page advancement can lose ties. Those scripts' use for the
old captures is unproven. Prefer untouched per-node structured output for this
preflight; do not reconstruct omitted requests or deduplicate identical messages.

## Run a short request-exercise preflight

1. Record actual deployed binary hashes, immutable source revisions, boot IDs,
   tracer configuration hashes and backend/export settings. Record unknowns as
   unknown; the model's pin is not deployed provenance.
2. Prepare the effective Notify tracer settings for the actual build. Retain all
   eight message kinds in both directions, plus connection/mux/session lifecycle
   records. Inspect logger/forwarder/exporter limits and drops separately.
3. Start original structured capture before a controlled fresh connection.
   Exercise at least one RequestNext on each endpoint of the selected operation.
   Preserve node identity, literal socket IDs, thread metadata when available and
   original source order. A Receive hook can precede a delayed Send log record.
4. Run the analyzer on the unchanged per-node files, with an explicit role when
   checking one side. Select a particular host/connection if the files contain
   other unrelated Notify sessions:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/capture_preflight.py \
  /path/to/client.log --expect-role client --host client-node \
  --connection '127.0.0.1:3001 127.0.0.1:3002'
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/capture_preflight.py \
  /path/to/server.log --expect-role server --host server-node \
  --connection '127.0.0.1:3002 127.0.0.1:3001'
```

5. Confirm `Send.RequestNext` for the client and `Receive.RequestNext` for the
   server. The tool can inventory both files together with `--expect-role both`,
   but it does not establish that those files represent a matching pair.
6. Then extend collection to ordinary replies, pending requests at Quit,
   cancellation draining, idle Quit and interrupted prefixes. Treat Votes as
   scenario coverage: exercise it when supported; absence is not automatically
   loss. Hash untouched captures and retain lifecycle/configuration evidence.
7. Use the existing [manifest runner](../profiles/README.md) after normalization
   and explicit session selection. Capture diagnostics are separate from model
   acceptance/rejection. EOF remains a prefix, and Done does not prove whole-node
   cleanup.

## Analyzer contract and limits

[capture_preflight.py](../capture_preflight.py) reuses
[the strict raw parser](../raw-input/lookahead_raw.py) before selecting any host,
connection or role. Supported Notify malformed/unknown rows fail explicitly,
even outside the eventual selection. Namespace and machine discriminator/direction
must agree. RequestNext and NotificationRequestNext namespace aliases both map to
RequestNext. Serialised observations are explicitly excluded and counted by the
raw parser; driver Send/Receive observations are the selected boundary.

Reports retain per-source/host/literal connection/observed mux generation/
after-Done segment/role counts and source coordinates. Client segments require
the Send RequestNext hook; server segments require Receive RequestNext. Both
hooks are required only when both roles are selected. A first reply is allowed.
An idle Quit trace may be valid but does not satisfy this **request-exercise**
preflight. Other absent message kinds are informational coverage.

| Exit | Status | Meaning |
| --- | --- | --- |
| 0 | `preflight-observations-present` | Selected segments contain their request hooks and preceding NewMux candidates |
| 3 | `missing-capture-evidence` | Missing selected role/records, request hooks or NewMux candidates |
| 2 | `invalid-input` | Invalid file/schema/selected-family record or unsupported option value |
| 4 | `resource-inconclusive` | Scan/line/state/segment budget or changing source prevents completion |

Every result has `protocolVerdict: null`. Status 0 does not certify freshness,
losslessness, causality, paired identity, deployed provenance or compatibility.
NewMux is only observed boundary evidence. No handshake-to-generation inference
or timestamp-based merge is introduced. Missing thread IDs remain reported,
rather than being invented or treated as a mandatory wire-replay field.

Defaults per input file are 16 GiB raw bytes, one MiB per line, ten million records,
300 seconds and the shared parser's 100000 lifecycle states. The combined report
retains at most 10000 selected segments; excess is inconclusive. CLI flags expose
the raw byte/line/record/time and segment limits. Sources are read serially.
For imported use, `analyze(paths, expected_role='observed', max_segments=10000,
host=None, connection=None, limits=None)` returns the report or raises the shared
`RawInputError`/`ResourceLimitError`; callers must not turn those into rejection.

Run the isolated controls with:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/capture_preflight.py --selftest
```

The [result record](result-preflight-20261105.json) retains actual validation and
source identities. Twenty embedded controls and five CLI controls pass. A final
guarded strict scan of `cardano-node-20261029.log` rereads all 2680000 records
and 292073 Notify rows, retaining the original raw SHA-256 from the old audit.
It again finds zero RequestNext and Votes; 2221 role segments lack request-hook
evidence, and 2119 also lack preceding NewMux candidates. Exit 3 is
`missing-capture-evidence`, with `protocolVerdict: null`. The scan takes about
16.04 seconds and 38152 KiB peak child RSS under a 384 MiB address-space limit.
All four parser/preflight source hashes match before and after that final scan.
An earlier scan during helper development is retained as preliminary and
superseded by this hash-guarded run. No original testnet capture is replayed by
this component, and no new node or capture is started.
