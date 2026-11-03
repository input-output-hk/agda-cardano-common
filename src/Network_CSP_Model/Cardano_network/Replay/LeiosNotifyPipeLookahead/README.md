# LeiosNotifyPipeLookahead replay bridges and validation

Protocol definitions and productive PTree constructors live in
[`Cardano_network/LeiosNotifyPipeLookahead/`](../../LeiosNotifyPipeLookahead/README.md).
The native entry point is
[`Cardano_network.LeiosNotifyPipeLookahead`](../../LeiosNotifyPipeLookahead.agda).
This directory consumes those models; the protocol modules do not import Replay.

| Module | Purpose |
| --- | --- |
| `ClientBridge.agda` | Both finite trace directions between the independent client rules and its source-operation PTree |
| `DriverBridge.agda` | Both finite record-trace directions for the generic paired driver prefix tree |
| `ServerEventsBridge.agda` | Roundtrip native event realization and exact-action injectivity at every endpoint |
| `ServerBridge.agda` | Both native `LNPEv` step/trace directions, return classification and native shutdown guards |
| `ServerBridgeTests.agda` | Exact-field native notification/shutdown/fault witnesses and negative controls |
| `ClientEventsBridge.agda` | Explicit visible/erased action partition and exact retained-payload realization |
| `ClientNetworkBridge.agda` | Both native client step/trace directions with declared callback erasure and exact return value |
| `ClientNetworkTests.agda` | Native receiver/Send races, post-Quit handling, cancellation drain and callback visibility controls |
| `DriverEventsBridge.agda` | Canonical full-packet native paired record roundtrip and injectivity |
| `DriverNetworkBridge.agda` | Both finite native paired step/trace directions against the independent driver product |
| `DriverEndpointBridge.agda` | Actual local native client/server executions and matching wire projections for each product run |
| `DriverNetworkTests.agda` | Delayed Sends, Canceled/normal-after-Quit shutdown, endpoint witnesses and FIFO/pending-record controls |
| `NodeDriverBridge.agda` | One-way native paired/endpoint realization of combined production node-policy runs |
| `NodeDriverTests.agda` | Fresh node-policy schedules with forecast/termination inputs, exact credit/queue transactions and shutdown |
| `ExportFixtures.agda` | Pure TSV rendering of four checked node wire histories, evaluated by Agda DefaultCompute for controlled Haskell comparison |
| `RuntimeCheck.agda` | Sound interpretation of supplied finite schedules at the independent node-policy rules; no exhaustive search claim |
| `RuntimeCheckTests.agda` | Seven negative controls for forecast, callback bypass, admission, empty queue, commit, selector and FIFO guards |
| `RuntimeCertificates.agda` | Concatenation of checked runs with exact wire equalities, plus server-only policy-to-core projection |
| `RuntimeInstance.agda` | Shared exact model and native bridge instance for generated runtime certificates |
| `Tests.agda`, `ClientTests.agda`, `DriverTests.agda`, `NodeTests.agda` | Inhabited source schedules and negative controls |
| `NativeTests.agda`, `NativeReachability.agda` | Native server PTree steps and constructive completed-bookkeeping reachability |
| `ClientNativeTests.agda`, `DriverNativeTests.agda` | Source-operation PTree witnesses and executable negative controls |

The source models, assumptions, findings and full validation record are documented
in the [protocol README](../../LeiosNotifyPipeLookahead/README.md). Pinned source
URLs and checksums are in its [`sources.json`](../../LeiosNotifyPipeLookahead/sources.json).

The server bridge retains readiness API events and the source model's abstract
admission outcomes. Its `realize` theorem supplies a native execution for every
source run. `sound` reconstructs a source run from every native finite execution.
The native client bridge keeps all wire records and normal API deliveries while
erasing the explicitly classified callback decisions and successful generic
Canceled handling. It retains the exact return value; the node-specific fault
policy remains a separate component. The native paired driver product now has
both trace directions and endpoint projection certificates. `NodeDriverModel`
now binds both node-policy components in the paired product and proves a one-way
native realization. The generic native target remains broader: its acceptance
alone does not certify a node-policy witness or the node's abnormal-exit outcome.
An exact policy PTree/inversion theorem, ordinary CSP/legacy-medium composition
equivalence, wider Haskell differential coverage/full node-callback validation
and certified wire/raw-log search remain separate
tasks in the [numbered plan](../../../../docs/specs/leiosnotify-pipe-lookahead-plan.md).

Run the validation roots from `src/`:

```sh
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/NativeTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/NativeReachability.agda
agda --safe Cardano_network/LeiosNotifyPipeLookahead/Rank.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/ClientTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/DriverTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/NodeTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/ClientNativeTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/DriverNativeTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/ServerBridgeTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/ClientNetworkTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/DriverNetworkTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/NodeDriverTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/ExportFixtures.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/RuntimeCheckTests.agda +RTS -M2G -RTS
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/RuntimeInstance.agda +RTS -M2G -RTS
```

The original eight roots and the native entry point passed after the directory refactor.
Logs and the exit-code manifest are in `/tmp/leiosnotify-lookahead-layering-20261103/`.
The new server bridge root and four relevant downstream roots passed with logs in
`/tmp/leiosnotify-lookahead-server-bridge-20261103/`.
The new client root and five relevant downstream roots passed with logs in
`/tmp/leiosnotify-lookahead-client-network-20261103/`.
The new paired driver root and five relevant downstream roots passed with logs in
`/tmp/leiosnotify-lookahead-driver-network-20261103/`.
The combined node-policy root, DriverNetworkTests, NodeTests and native entry
point passed with logs in `/tmp/leiosnotify-lookahead-node-policy-20261103/`.
The pure fixture exporter passes safe checking and normalization. The
[controlled Haskell harness](../../../../tools/leiosnotify-lookahead/README.md)
passes 80 experiments and all 40 applicable Agda wire-history comparisons;
the full artifact directory is `/tmp/leiosnotify-haskell-final-20261103/`.

T3.3's additional supplied-schedule certificates are produced by
[`certify.py`](../../../../tools/leiosnotify-lookahead/certify.py), which checks
small parts using `agda --safe`, proves their concatenation, and realizes the
exact original rows in the native paired or local-server tree. Its Python
planner is untrusted. Failure to find or check a supplied schedule is
inconclusive. It is not the proposed exhaustive wire-only/raw-log checker.
The [OOM diagnosis](../../../../docs/notes/leiosnotify-pipe-lookahead-oom.md)
describes the shared instance, abstract parts and bounded execution. Generated
sources and logs stay outside the repository.
All 40 additional captured histories passed through 22 distinct safely checked
certificates, bringing the total to 80: 70 paired histories and 10 server-only
adversarial histories. The [T3.3 result record](../../../../tools/leiosnotify-lookahead/results-t33-20261103.json)
ties the batch to its sources and artifacts under
`/var/tmp/leiosnotify-t33-20261103/verified/`. Peak sampled RSS was 1.15 GiB;
there were zero batch budget failures. The four helpers and all 1003 generated
Agda files pass strict proof scans with zero findings.
