# Mini-protocol lifecycle contracts

Reviewed 13 November 2026, batch 1 / [Supervision increment 88](Supervision.md#eighty-eighth-increment-g0-chainsync-blockfetch-and-registry-contracts).
Batch 1's three [branch rows](BranchMatrix.md) are **contracted**, with executable
ordering guards. They no longer lack a reviewed lifecycle contract. This is a
source review and finite model evidence, not Haskell refinement or full G2
configured-bundle acceptance.

Current acceptance includes both configured directions and the source-selected
inputs. [Increment 96](Supervision.md#ninety-sixth-increment-source-policy-profile-and-seed-history-abstraction)
checks both initialized runs using 5/120, the selected V15 data/flow and Tx V2.
Its policy result covers the four reached finite selection histories.
Driver, payload, DB and application observations still use the contracts below.
[Branch matrix](BranchMatrix.md), [gate audit](GateAudit.md).

## Configured outbound coupling (increment 92)

[ConfiguredProtocols](ConfiguredProtocols.agda) composes the three kernels with
one actual supervised runtime. It binds immutable worker/mux/direction/number/
generation/job captures and exposes actual frontend edges plus contract
observations. Missing or foreign captures cannot alias a physical job by number.
The normal outbound wrapper checks all physical executing-to-return transitions,
including inherited aliases; synchronous failure and cancellation cannot bypass
its normal-return gate. The raw runtime and all earlier theorem statements remain
unchanged apart from the explicitly approved obsolete installer diagnostics.

Termination observes the captured peer's actual PSA control. Batch-1 fetch
registration uses batch-2 dq/dying state; KeepAlive's finalizer snapshot observes
the actual captured fetch registration. Its fetch-done observation requires that
fetch cleanup and CS done actually occurred. Batch-3 ChainSync starts after its
batch-1 candidate acquisition, releases shared state before candidate/sync
cleanup, and closes its outer bracket only after sync done. Notify/Fetch/CS
share the single batch-3 presence/accounting state, without a refcount.

[FullConfiguredWitness](Negative/FullConfiguredWitness.agda) runs 381 wrapper
inputs (322 actual frontend events) from the usual initializer, with hot
2/3/4/18/19, empty warm and established 8. All six physical initiators return
through their finished normal contracts, then publish/deregister/expose Async
results. KeepAlive sends/observes its first response before control; CS/BF each
drain an outstanding reply; Notify drains after Quit and Fetch collects before
its next control read. The clean finite schedule uses the absent-fetch KA
finalizer branch; the coupled present-fetch branch remains a guarded contract.

These are source-operation observation contracts. They do not implement payload,
codec, STM registry identity, DB readiness, source policy RNG or universal
progress. The second selected establishment job remains registered at `J.begin`.
This increment uses the reduced policy fixture. Increment 96 checks the
source-configured outbound run. Endpoint and premature-step facts
are in [FullConfiguredFacts](Negative/FullConfiguredFacts.agda); the entire
projected history executes in [OwnedCallers](Negative/FullConfiguredCallers.agda).

## Configured inbound coupling (increment 94)

[ConfiguredResponders](ConfiguredResponders.agda) is separate from the outbound
wrapper. It binds actual responder identities, accepts only server contract
actions, and selects TxSubmission V2 explicitly. It reads no outbound PSA peer
or control: remote Done/Quit, pipeline draining and private bracket cleanup
precede normal body return. Missing/unwinding/cancelled physical pool handles
cannot bypass that gate; [enabled/refusal examples](Negative/ConfiguredResponders.agda)
and [raw cancellation](Negative/InboundConfiguredCancellation.agda) check it.

[InboundConfiguredWitness](Negative/InboundConfiguredWitness.agda) supplies
246 wrapper inputs / 208 frontend events from the existing full 2/2/1 initializer,
including demand-triggered Any KeepAlive and all six clean responder contracts,
publication/Async availability, graceful mux/pool exit, handler cleanup and IG
unregistration. The handler receives cancellation at unmasked TIME_WAIT after
normal mux/body return; its result is `asyncException 42`, not a normal Async
return. [Endpoint facts](Negative/InboundConfiguredFacts.agda),
[startup facts](Negative/InboundConfiguredStarts.agda),
[premature controls](Negative/InboundConfiguredControls.agda) and
[OwnedCallers](Negative/InboundConfiguredCallers.agda) retain these distinctions.
At increment 94, concrete source RNG/selection, version/data and V2 logic
instantiation were open. Increment 96 closes these for the selected finite
profile. Readiness, driver, DB and private-resource events remain reviewed
contracts. [Increment 94](Supervision.md#ninety-fourth-increment-responder-contracts-and-full-configured-inbound-lifecycle),
[gate audit](GateAudit.md).

The batch acceptance paragraphs below retain their original review scopes.
Increments 92, 94 and 96 record their configured-execution and source-input
follow-ups.

## Authority, observations and implementation boundary

Sources were read using read-only `git show` at the ledger pins: network
`2f1c154f248659b89523d5679ca532f442e7ed2a` and consensus
`2e44d98a843168ba3b189e305820b79943ac7d1e`. The retained replay78 network
checkout has that exact HEAD; the consensus object is available in its local
repository. These are immutable source links, independent of checkout locations.

| Source alias | Git blob read at its pin |
| --- | --- |
| [Bundle] | `b2f3e96e8458592e2eee7dd4fd33174b4d6c63c3` |
| [CSClient] | `ac7abf0c54ed09063cc37533934c41ab1871bdb7` |
| [CSServer] | `213cc9bb6ddb9184b58aa797a331e62166a8012b` |
| [BFClient] | `341e006ddad51df247a1be294a49a3a6def6da11` |
| [BFServer] | `94ed7a23ebbc7f346823892503ec301aa10a080e` |
| [Registry] | `49f8f855d31925c8d73156e4ca18545ce2a02170` |
| [Control] | `78cab7192c71fc140cea7f586917ef3a909325f8` |

**Implement** means a guard/transition in [ProtocolContracts.agda](ProtocolContracts.agda)
and a tested finite path or refusal in [Negative/ProtocolContracts](Negative/ProtocolContracts.agda).
**Contract** means an input certified by the named source operation, under the
[primitive STM/mask/exception contracts](PrimitiveMatrix.md). **Exclude** means
no corresponding claim in this CM lifecycle abstraction. Source events must
be projected at these boundaries; arbitrary result inputs do not satisfy them.

The kernel represents **one captured peer/connection incarnation**, one invocation
of each bracket, and distinct fixed physical children. It retains the captured
`doneVar` after sync-map deletion. New incarnations/restarts require new captured
state and the source registry's absence checks; the kernel is not a concurrent
multi-peer registry implementation. Its `fresh` phases mean the selected peer
has no older registry occupant; `registerSync`/`registerFetch` cannot be replayed
in this state. Context and KeepAlive readiness are successful external STM
observations, not a model of KeepAlive's complete lifecycle. KeepAlive dying is
monotone within this captured bracket. No fairness or eventual readiness is assumed.

`await` records a blocked operation; `ready` certifies its actual return.
Outstanding counts passed at `terminate`/`chainUninteresting` certify the real
pipeline count at that boundary. `collect` certifies one actual collected reply.
The kernel does not verify the pipeline implementation or synthesize replies.
A control read only occurs at its documented site. A `ready` observation must
respect the actual STM alternative priority, especially BlockFetch's
Terminate-first choice. No time bound, message delivery, eventual drain, or
universal graceful demotion follows.

## ChainSync

### Initiator

| Lifecycle item and source lines | Disposition and exact contract |
| --- | --- |
| Outer synchronization before candidate registration: [Bundle] 1453–1472; [Registry] 217–257 | **Implement** `registerSync`, `rendezvous`, `enterCandidate`: candidate publication is refused before the fetch client starts it. **Contract** the real per-peer map absence/identity and successful STM commits. |
| Inner candidate/CSJ handle, watcher and leaky bucket: [CSClient] 365–461, 463–489 | **Implement** candidate presence/removal before outer done. **Contract** bucket/watcher allocation, watcher cancellation/join, CSJ registration/unregistration and successful unwind observation. CSJDisabled deletes the handle; CSJEnabled unregisters context and traces afterwards. Invalid-block watcher and bucket exceptions may end the body. **Exclude** density, jump selection and validation correctness claims. |
| Local control: [CSClient] 1295–1335 | **Implement** `terminate chainClient n` only at active next-step, then drain before done. **Contract** actual `atomically controlMessageSTM`; Terminate gives `AskedToTerminate`, other values proceed to the jumping instruction. A ledger/jumping/receive wait is not automatically interrupted by setting Terminate. |
| Jump instruction, peer/driver receive and forecast/ledger waits: [CSClient] 1313–1335, 1846–1887, 1940–1957; [Bundle] 1473–1496 | **Implement** distinct blocked `jumping`, `channel`, `ledger` phases with observed readiness. **Contract** the real forecast projection: it retries while the intersection survives and the projection is absent, may exit when intersection disappears, or throw if the candidate is unsuitable. LoP pause/resume brackets the time/forecast check. Network byte/time limits and Leios callbacks may also block/throw; readiness certifies they returned. **Exclude** ledger/payload/Leios safety and shared Leios allocation proofs; the shared-resource branch row remains open. |
| Graceful result and cleanup: [CSClient] 927–939, 1630–1645, 2259–2297; [Bundle] 1497; [Registry] 249–257 | **Implement** `chainUninteresting` / Terminate drain, inner candidate removal, then `signalSyncDone`. **Contract** actual result is `ChainSyncInitiatorResult r` with trailing bytes, where `r` is `ForkTooDeep`, `NoMoreIntersection`, `RolledBackPastIntersection`, or `AskedToTerminate`. These result payloads/trailing bytes are erased to normal body completion at this boundary. The generic mux still owns trailing-byte restoration. |
| Exceptions/masking: [CSClient] 927–939; [Registry] 224–257; [Mux] 558–568 | **Implement** synchronous versus cancellation outcomes, acquisition interruption cleanup and no normal return before outer done. **Contract** bracket acquisition/release masking, restored body masking and actual exception receipt per PrimitiveMatrix. Cancellation during the interruptible startVar wait runs `unregister`; acquired bodies unwind the inner brackets before outer unregister. CSClient's tracing catch rethrows. Cleanup exceptions can replace a body exception under the primitive bracket contract; the supplied synchronous ErrorId is the final escaping exception after unwinds. Successful resource-removal observations are required, not inferred from a thrown exception alone. |

A normal ChainSync result can leave other mini-protocols on the bearer running
([CSClient] 2259–2270). This contract never turns it directly into CM release,
physical handler exit, or Cold. Missing control observation or a blocked drain
can delay PSA deactivation; timeout/mux cancellation is handled by the existing
CM supervision contracts.

### Responder

| Lifecycle item and source lines | Disposition and exact contract |
| --- | --- |
| Follower acquisition and private registry: [Bundle] 1504–1524; [CSServer] 63–68 | **Implement** `acquireServer chainServer` and cleanup-before-finished. **Contract** actual follower creation and selected/tentative chain choice; bracketWithPrivateRegistry's followerClose and resource cleanup must complete before a successful server result. |
| Requests, ChainDB waits and control: [CSServer] 274–331 | **Implement** blocked `channel` and `follower` phases. **Contract** request/FindIntersect receives, nonblocking followerInstruction, followerInstructionBlocking at the tip, followerForward and atomic current-tip reads. **Exclude** an initiator control-message read on the responder: none is passed here. A local demotion control does not wake its follower wait. |
| Termination/result/errors: [CSServer] 274–280; [Bundle] 1503–1524 | **Implement** peer Done → cleaning → finished normal, or body error/actual async receipt → cleanup. **Contract** normal result `((), trailing)` only after the private bracket returns; follower/driver/trace exceptions escape after unwind. Acquisition failure allocates no successfully acquired follower in this kernel. Ordinary bracket release is masked, not asserted uninterruptible; cleanup failure/pending async delivery follows PrimitiveMatrix. **Exclude** block-serving node-to-client transformations at [CSServer] 117–257; this is the node-to-node header responder. |

The responder has no fetch-client registry synchronization. A normal result feeds
existing responder completion/status monitoring; mux stop/handler cleanup and CM
release remain subsequent, separate operations.

## BlockFetch

### Initiator

| Lifecycle item and source lines | Disposition and exact contract |
| --- | --- |
| Acquisition prerequisites: [Registry] 85–139 | **Implement** register refusal without context/KeepAlive, while dying, or after this fetch invocation is registered; synchronization before the body. **Contract** older fetch absence, ctxVar initialization, KeepAlive dqRegistry membership, policy STM allocation and keepRegistry insertion in the same successful transaction. It may retry without partial insertion. Policy failure aborts that transaction. |
| Waiting for ChainSync: [Registry] 129–153 | **Implement** registered-before-rendezvous phase; acquisition exception/async receipt removes fetch registration without entering the body or waiting for ChainSync done. **Contract** shutdown status, ksVar signal and keepRegistry deletion happen in that cleanup transaction. A successful rendezvous fills startVar and marks fetch Ready atomically. |
| Fetch work/control: [BFState] 543–558; [Control] 43–57; [BFClient] 110–133, 182–190 | **Implement** `fetchWork` wait, Terminate there or at active sender boundary, and collect/drain before Done. **Contract** `acknowledgeFetchRequest` selects the Terminate alternative first, otherwise takes fetch work; Continue/Quiesce retry that alternative and permit available work. The accepted request, not merely queued work, updates tracking. Terminate does not instantly abort an already blocked receive or addFetchedBlock operation. |
| Receive/database work and failures: [BFClient] 193–290; [BFInterface] 240–265 | **Implement** blocked `channel` / `database` observations and synchronous error outcome. **Contract** matched-header/block verification, fetch accounting, driver receive/limits and addFetchedBlock effects. Wrong block/invalid body throw; addFetchedBlock runs before completion accounting. ChainDB async submission/processing readiness is supplied by its actual operation, with no invented durable-write guarantee. **Exclude** consensus validity and full fetch scheduling correctness. |
| Normal value: [BFClient] 182–190; [Bundle] 1545–1557 | **Implement** no clean completion until outstanding replies drain and registry cleanup finishes. **Contract** body returns unit; application returns `(NoInitiatorResult, trailing)` after its bracket. Result payload erasure does not bypass generic mux egress drain. |
| Cleanup and masking: [Registry] 155–207 | **Implement** BF cleaning retains fetch entry until captured CS done; explicit `cancelSync` observation permits CS unwind; removal before done is refused. **Contract** status becomes Shutdown, normal exit waits up to `deactivateTimeout`, exceptional exit up to **1 second**. The unregister body uses `uninterruptibleMask`; only its timeout/done wait is run through the supplied `unmask`, restoring the enclosing release mask (normally MaskedInterruptible under generalBracket), rather than promising Unmasked execution. If KeepAlive is dying it immediately throwTo's CS then waits done and cleans; otherwise timeout expiry or exception in the restored-mask wait causes throwTo and an uninterruptible done/cleanup fallback. throwTo receipt and timeout expiry are observed inputs, not guaranteed progress. Cleanup deletes fetch entry, signals ksVar and deletes keep entry atomically. `fetchCleanupInterrupted` records actual delivery at an interruptible operation in that restored-mask wait, retains cancellation as the escaping outcome, and still requires CS done/cleanup. `cleanupFailure` retains a replacement synchronous cleanup exception. Neither observation fabricates completion. |

In particular, fetch Shutdown does **not** itself supply a new ChainSync control
read. A graceful CS return needs its own control/natural result and readiness.
The BF finalizer can remain blocked in throwTo/done even after a local timeout;
no bounded shutdown claim follows from the one-second/deactivateTimeout values.

### Responder

| Lifecycle item and source lines | Disposition and exact contract |
| --- | --- |
| Request, stream and resource lifetime: [Bundle] 1564–1574; [BFServer] 83–146 | **Implement** acquisition, blocked `channel` / `database`, and private-registry cleanup before return. **Contract** withRegistry, ChainDB.stream and iteratorNext; UnknownRange returns NoBlocks, a real iterator starts a batch, exhaustion closes it before BatchDone. Resource operations certify actual return and may block or throw. |
| Errors, result and control: [BFServer] 101–112, 135–146; [Bundle] 1563–1574 | **Implement** peer Done or error/actual cancellation receipt → cleanup → finished. **Contract** normal unit plus driver trailing bytes; NoGenesisBlock throws, BlockGCed closes iterator then throws, other IO/driver/trace exceptions unwind the resource registry. Registry cleanup failures follow the bracket exception-replacement contract and require their own observed outcome. **Exclude** a local initiator control check and fetch/sync registration on this direction: neither is present. |

## Shared registration synchronization

### Initiators

| Source obligation | Disposition |
| --- | --- |
| CS sync-map insertion, interruptible start wait, candidate bracket outside/inside order: [Registry] 224–249; [Bundle] 1453–1472 | **Implement** syncEntry → rendezvous/start → candidate. **Contract** peer key and exact captured thread/startVar/doneVar identity; source absence checks wait for older same-peer cleanup. No candidate is inferred merely from a physical job's birth. |
| BF fetch/keep registration, ready/start handshake: [Registry] 95–153 | **Implement** prerequisites and rendezvous, plus separate failed-acquisition cleanup. **Contract** successful STM atomicity, context/policy and KeepAlive resource semantics. Acquisition failure after insertion cleans its own registrations. CS waiting failure signals done/removes sync entry. |
| CS inner cleanup precedes done/map deletion; BF retains entry until captured done: [Registry] 155–207, 251–257 | **Implement** candidate removal → signalSyncDone → removeFetch. **Contract** full inner unwinds have really occurred and final cleanup transaction succeeds; timeout/cancellation cannot fabricate done or infer handler completion. The source may remove a sync map entry before BF consumes its captured doneVar, which the model preserves. |
| Restart/multiple incarnations and full KeepAlive sharing | **Contract** caller maintains the stated fresh captured-slot and distinct-child premises. **Exclude** an initialized multi-incarnation registry implementation from this batch. Existing CM overlap proofs are not proofs of this application registry. |

### Responders

**Exclude** fetch/sync/KeepAlive client-registration dependencies for both
responders: [Bundle] 1499–1524 and 1559–1574 use independent private resource
registries. Their cleanup still gates their own body results. Duplex negotiation
does not introduce a client registry on the responder direction.

## Connection-management boundary and checked scope

[ProtocolContractJobs](ProtocolContractJobs.agda) checks physical executing
children using `W.collector`, protocol numbers **2 (ChainSync)** / **3 (BlockFetch)**
([wire assignments] 475–479) and initiator/responder direction; bindings are distinct fixed JobIds of one
captured connection. Numbers must correspond to its actual negotiated bundle.
It does not reinterpret synthetic protocol 1. `complete` accepts only a finished
normal or synchronous outcome, then executes actual `MuxProtocolJobs.step` with
`protocolReturned` or `protocolException`. `complete-via` proves the real generic
edge exists; `complete-enabled` supplies its converse with all readiness premises.
Normal completion still requires a real wanton and later egress drain, status
commit, physical return, queue publication, deregistration and Async result.
Cancellation is refused by the completion selector: it remains a pool/handler
unwind outcome, never a synchronous protocol error fabricated here.

This is a **conditional body adapter**, not a replacement full frontend. The
caller owns startup/fork/registration, mux/handler/pool cancellation and all
post-body operations on the same physical state. An instantiation must route
these four children's body observations/results through this dispatcher and
preserve lifecycle metadata across physical steps; raw generic result injection
is outside this contract. There is no claimed full configured initialized run
or a theorem that every existing frontend satisfies this interface.

Existing [MuxJobTypes](Rules/MuxJobTypes.agda),
[MuxProtocolJobs](MuxProtocolJobs.agda), [MuxHandlerSupervision](MuxHandlerSupervision.agda)
and [MuxHandlerExit](MuxHandlerExit.agda) retain their statements and semantics.
Source [Mux] 529–568 waits for unsent/held egress on normal return, catches
synchronous failures into protocol exception results, and does not run that
handler on asynchronous exceptions. Existing supervision consumes those outcomes;
PSA demotion may wait/timeout, mux stop enqueues shutdown, handler finally owns
physical cleanup, and release remains its owner's separate action. None of the
new kernel events directly releases CM, demotes a peer, closes a socket or
publishes a handler Async result.

The enabled startup/clean/error/server paths and refusal controls are in
[Negative/ProtocolContracts](Negative/ProtocolContracts.agda). The adapter's
[controls](Negative/ProtocolContractJobs.agda) cover value selection, cancellation,
blocked/unfinished cleanup refusals, and a positive **conditional** clean-client
example retaining a real underlying job edge. They prove no eventual progress.
Validation and unperformed heavy checks for batch 1 are recorded in increment 88.
Batch 2 below contracts TxSubmission2 and KeepAlive. G0 and G2 full-profile
status remain partly met; LeiosNotify, LeiosFetch and shared Leios-resource
contracts remain missing.

[Bundle]: https://github.com/IntersectMBO/ouroboros-consensus/blob/2e44d98a843168ba3b189e305820b79943ac7d1e/ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/Network/NodeToNode.hs
[CSClient]: https://github.com/IntersectMBO/ouroboros-consensus/blob/2e44d98a843168ba3b189e305820b79943ac7d1e/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/MiniProtocol/ChainSync/Client.hs
[CSServer]: https://github.com/IntersectMBO/ouroboros-consensus/blob/2e44d98a843168ba3b189e305820b79943ac7d1e/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/MiniProtocol/ChainSync/Server.hs
[BFClient]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/lib/Ouroboros/Network/BlockFetch/Client.hs
[BFState]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/lib/Ouroboros/Network/BlockFetch/ClientState.hs
[BFInterface]: https://github.com/IntersectMBO/ouroboros-consensus/blob/2e44d98a843168ba3b189e305820b79943ac7d1e/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/MiniProtocol/BlockFetch/ClientInterface.hs
[BFServer]: https://github.com/IntersectMBO/ouroboros-consensus/blob/2e44d98a843168ba3b189e305820b79943ac7d1e/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/MiniProtocol/BlockFetch/Server.hs
[Registry]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/lib/Ouroboros/Network/BlockFetch/ClientRegistry.hs
[Control]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/api/lib/Ouroboros/Network/ControlMessage.hs
[Mux]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/network-mux/src/Network/Mux.hs

[wire assignments]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/cardano-diffusion/lib/Cardano/Network/NodeToNode.hs


## Batch 2 authority and executable boundary

Reviewed 13 November 2026 at model HEAD `96b3bd4`; see
[increment 89](Supervision.md#eighty-ninth-increment-g0-txsubmission2-and-keepalive-contracts).
Both rows are **contracted**, with the CM-visible guards **implemented** in
[ProtocolContracts2](ProtocolContracts2.agda) and the conditional typed mux-body
adapter [ProtocolContractJobs2](ProtocolContractJobs2.agda). Existing Agda modules
and statements are unchanged. The boundary and primitive contracts above apply.
The pinned blobs below were read with read-only `git show`, including consensus
NodeKernel/mempool operations, both inbound Tx logic variants and the shared
KeepAlive/BlockFetch registries. No unpinned checkout content is evidence here.

| Alias | Blob at the existing ledger pin |
| --- | --- |
| [TxOut] | `f52d7ceef4b04bec9c006ab0b1c37425cec55ed6` |
| [TxIn1] | `f5d16b2456807e216d7b917516c1cf39688da598` |
| [TxIn2] | `baaf2c3492088bf414011e6b57a94596829ff160` |
| [TxRegistry] | `948092f8e0c6dbaadd061bafbd467d3005273cf4` |
| [TxClientPeer] | `4dfbe820abe6b022e232454771d5295f3343c33e` |
| [TxServerPeer] | `9c7bd48becc7893d6e7f322113c88e40cd544bd6` |
| [KA] | `f33ce105fdd9d9eebf6f5a36d1065e14cded9670` |
| [KARegistry] | `d4b3ccf9dd4b8dd3eac7ed556590b05e110ee443` |
| [KAClientPeer] | `10691762b9a1e449d29695127717a3bf73880a10` |
| [KAServerPeer] | `e47d34e45e0aae5d2dc062584144898815a410ea` |
| [KernelTx] | `3ee89fddf8ce329eb193bbe6300e67976ab04e9f` |
| [MempoolInit] | `468361ac9900983cd241035963c9bf622905f66d` |
| [MempoolAPI] | `a75d2d7047c225771635489ad12541438120bca9` |
| [MempoolUpdate] | `8d9c9a3b4b542db867e70d373ebc4f33d0bdf96e` |

Each state denotes one captured connection incarnation and one invocation per
selected endpoint. Select **one** of `txServerV1`/`txServerV2` for the actual
application's `txSubmissionLogicVersion` ([Bundle] 539–578, 1616–1635); TxSubmission2
is the wire protocol for both. The adapter checks physical executing children,
number **4** / **8**, and direction ([wire assignments] 481–485). Bindings must be
fixed, distinct and owned by the same captured connection/mux; choosing V1/V2 is
an instantiation premise, not an invented wire-version negotiation.

`idle` is an abstract operation boundary, not a complete protocol state. Request
validation, exact legal request sites, unacknowledged transaction windows,
startup Init/initial delay/joinTiers order, successful driver sends/receives and
resource allocation remain **contract** inputs. `issue`/`collect` certify actual
pipelined request/collection operations, not arbitrary changes to a counter.
`blockingIds` additionally certifies the real unacknowledged-window condition;
its zero-depth guard alone does not establish that condition. `ready` certifies
the entire selected operation returned; it does not promise it will return.
`start keepClient` certifies successful dq registration and initial ping send;
it deliberately ends at the response wait, before any local control decision.
An acquisition failure certifies no acquired bracket resource; failure after
acquisition/initial send instead uses `fail`/`receiveCancel` and cleanup.

## TxSubmission2

### Initiator

| Lifecycle item and pinned source lines | Disposition and exact contract |
| --- | --- |
| Start/receive: [Bundle] 1576–1597; [TxClientPeer] 85–109 | **Implement** one-shot start, channel/snapshot wait observations and no clean return at an idle receive. **Contract** MsgInit send, runPeerWithLimits, codec/byte/time/egress/tracer operations and actual legal request reception. It is the tx **outbound supplier** despite being called Client. There is no fetch-work or ChainDB follower wait on this path. |
| Blocking tx-id request: [TxOut] 106–161; [Control] 43–55 | **Implement** `blockingRequest` → `txBlocking`, work return or Terminate → `donePending` → observed Done send. **Contract** ack/request/window validation, nonempty mempool snapshot wait and the atomic left-biased `timeoutWithControlMessage`: Terminate wins if both alternatives can commit; Continue/Quiesce retry the control alternative and permit available work. `workAvailable` is valid only for an actual successful work alternative, never when Terminate would win. No wallclock timeout is installed by this helper. |
| Nonblocking ids / requested bodies: [TxOut] 163–220; [KernelTx] 1098–1126; [MempoolInit] 128–130 | **Implement** distinct channel and snapshot waits which refuse Terminate. **Contract** snapshot return/lookup and missing-body filtering; a removed transaction can be omitted. A control change cannot interrupt these operations or an unrelated driver receive. RequestTxs contains no control read. **Exclude** transaction validity, full acknowledgement/window/payload correctness and mempool fairness proofs. |
| Result / exceptions / brackets: [TxOut] 46–82, 106–116, 140–143, 163–167, 193–209; [Bundle] 1588–1597 | **Implement** Done-send-before-normal-completion, synchronous errors and actual cancellation as separate outcomes. **Contract** protocol validation exceptions, driver/trace/mempool exceptions and inherited body masking. This application has no local registry bracket; `cleanup txClient` observes completion of any enclosing driver unwind, not a fabricated registry deletion. Normal body result is unit, lifted to `(NoInitiatorResult, trailing)`. Terminate produces Done only in the blocking request state, not at every scheduler iteration. |

### Responder

| Lifecycle item and pinned source lines | Disposition and exact contract |
| --- | --- |
| Setup / variant selection: [Bundle] 551–578, 1599–1635; [TxServerPeer] 101–106; [TxIn1] 139–144; [TxIn2] 165–172 | **Implement** separate V1/V2 endpoints and initial-delay wait observations. **Contract** wire MsgInit receipt before server setup, configured delay and, for V2, joinTiers after that delay. V1 runs directly; V2 wraps the driver in withPeer, so registration precedes even MsgInit receive. No initiator control STM is passed to either responder. |
| Pipeline and normal termination: [TxIn1] 159–220; [TxIn2] 299–380; [TxServerPeer] 59–91, 112–139 | **Implement** counted issue/collect, blocking request only at zero depth, peer Done only at that blocking request, then cleanup. **Contract** actual request choice/window condition, typed driver receives and opportunistic versus blocking collection. MsgDone is a response to a blocking tx-id request; normal responder result is unit (V1/V2 termination tracer must return). **Exclude** a local Terminate check or a generic Done reception while pipelined work remains. |
| Mempool / work waits: [TxIn1] 239–250, 310–331; [TxIn2] 191–279; [TxRegistry] 746–785, 911–925; [KernelTx] 1128–1150 | **Implement** snapshot/submission waits for both variants and V2-only shared-generation/claimable-change waits. **Contract** scheduler/STM returns, actual counter change or optional registered-delay expiry (no unconditional timer), V1/V2 mempoolAddTxs return and V2 applySubmittedTxs. Spurious workless wakeups may park again. No fairness, eventual expiry, submission success or durable ChainDB insertion is assumed. |
| Concrete submission blocking: [MempoolAPI] 363–375; [MempoolUpdate] 87–128, 203–218, 239–263 | **Contract** per-transaction remote/all FIFO MVar acquisition and release, SVar acquisition, size-change STM retry after capacity failure, ledger-table reads and configured validation timeout. Partial batch additions can remain after an exception because addTxs is mapM, not one atomic transaction. `submission` covers these nested waits/unwinds; changing CM control cannot unblock them. **Exclude** internal FIFO/SVar/ledger semantics and weighted fairness from this CM kernel. |
| V2 registry cleanup / masking: [TxRegistry] 605–681 | **Implement** `retireTx` before `cleanup txServerV2`; normal completion cannot skip either. **Contract** bracket acquisition allocates per-peer in-flight/counters cells and atomic registration/tier entry under a captured `(peeraddr, registration)` key. Finalizer obtains time, atomically scrubs this peer's shared in-flight contributions and retires counters/removes cells, then leaves tier in a **separate** transaction. Acquisition/release are masked under ordinary bracket; body restores prior mask, not necessarily Unmasked. Release is not asserted uninterruptible; `releaseCancelled txServerV2` certifies actual async receipt at a blocking interruptible operation in the release mask and exits cancelled without certifying remaining cleanup. Exception replacement obeys PrimitiveMatrix. |
| Errors / V1 cleanup: [TxIn1] 232–269; [TxIn2] 359–415; [Bundle] 1607–1635 | **Implement** synchronous/actual async body exit, observed cleanup, and escaping finalizer error replacing the outcome. **Contract** overlarge/unrequested replies, invalid bodies, mempool, policy, tracer and driver exceptions. V1 has no withPeer registry to remove. V2 cancellation does not imply successful scrub/tier removal; `cleanupError` may finish with a synchronous replacement error without those resource-success certificates. Final asynchronous unwind remains a cancellation outcome outside ordinary mux synchronous error selection. |

Normal Tx return feeds the generic mux result; it does not itself stop mux,
release CM, demote or exit the handler. Failure may trigger those existing
supervision paths. A hot-protocol demotion can wait until a valid blocking
request/control read; receive/submission/park delays do not become immediate
completion when control changes.

## KeepAlive

### Initiator

| Lifecycle item and pinned source lines | Disposition and exact contract |
| --- | --- |
| Established bundle / acquisition: [wire assignments] 303–313; [Bundle] 1727–1757; [KARegistry] 49–62 | **Implement** one-shot dq registration/ping start and retained dq presence. **Contract** successful atomic absence check against older same-peer dq entry and defaultGSV insertion. Retry has no partial insertion; acquisition interruption/failure before commit acquires nothing. Source established-group selection/start remains the existing frontend's obligation; this batch adds no initialized nonempty established bundle. |
| First ping / response / sample: [KA] 55–59, 77–95; [KAClientPeer] 45–53 | **Implement** response wait before the first control site; `ready keepClient` certifies cookie check, sample update, tracer return and delay registration. **Contract** random cookie/time, dq membership assertion/update and actual reply; cookie mismatch throws KeepAliveCookieMissmatch. Terminate does not short-circuit the first ping or an outstanding response. **Exclude** RTT/DeltaQ accuracy, random distribution, numeric time and eventual reply guarantees. |
| Control/delay: [KA] 63–75, 94–103; [Bundle] 1748–1753 | **Implement** `keepDecision`, Terminate → Done pending, interval return → next ping/response wait, Done-send-before-cleanup. **Contract** registered delay is 10 seconds in this bundle; decisionSTM reads control first: Terminate returns immediately even if delay not fired; Continue **and Quiesce** wait for delay, then yield Continue. `intervalElapsed` certifies this actual non-Terminate return and next send; it is invalid if Terminate would have won. This is an untimed observation, not a deadline or periodic-progress proof. |
| Finalizer without fetch: [KARegistry] 64–84 | **Implement** `keepSnapshot false` removes dq and finishes only after body exit/Done. **Contract** actual atomic keepRegistry lookup is Nothing and dq deletion commits. No fetch job is fabricated or required when absent. Normal result is unit, lifted to `(NoInitiatorResult, trailing)` only after bracket returns. |
| Finalizer with fetch: [KARegistry] 67–96; [Registry] 95–122, 198–207 | **Implement** snapshot marks dying, separate captured fetch cancellation receipt, then captured done signal before dq/dying removal. Cancellation receipt alone cannot finish KeepAlive. **Contract** exact keepRegistry `(ThreadId, ksVar)` captured by the finalizer, actual throwTo AsyncCancelled receipt, readTMVar ksVar and successful atomic dq/dying deletion. BF registration checks dq presence and absence from dying; BF cleanup signals ksVar and deletes keepRegistry. That signal is cleanup synchronization, not necessarily the physical BF Async result. |
| Masking / errors: [KARegistry] 49–50, 66–96; [KAClientPeer] 49–53 | **Implement** body sync/cancel outcomes and refusal of further async receipt throughout KeepAlive cleanup (including throwTo/join); an observed escaping synchronous cleanup fault finishes with replacement error and retains dq/dying metadata rather than claiming removal. **Contract** ordinary bracket acquire/body masks and **uninterruptibleMask_ for the entire finalizer**, with no local timeout or restore window. Blocked throwTo/readTMVar can therefore prevent return indefinitely; source exceptions/assertions and driver/tracer failures may end the body. A finalizer fault may leave registry residue. **Exclude** bounded cancellation, guaranteed finalizer success, or a direct finalizer async-receipt branch. |

The captured fetch snapshot/done inputs must be projected from the same peer,
connection incarnation and actual registry bracket as batch 1's fetch cleanup.
Batch 2 does not implement a concurrent shared registry or automatically feed
its dq/dying fields into batch 1's state. A combined instantiation must couple
successful KA start with batch 1 keepAliveReady, propagate the captured dying
snapshot to keepAliveDying, and certify fetchDone from the matching ksVar after
fetch removal; batch 1's monotone dying flag cannot be reused for a new bracket.
This explicit cross-adapter contract prevents treating unrelated result/cancel
observations as registry readiness. Multiple incarnations require fresh captured
state; neither kernel proves registry identity/refinement for arbitrary clients.

### Responder

| Lifecycle item and pinned source lines | Disposition and exact contract |
| --- | --- |
| Receive/respond/Done: [Bundle] 1759–1773; [KA] 106–112; [KAServerPeer] 24–37 | **Implement** channel wait, observed peer Done → cleanup → finished normal, body error and cancellation paths. **Contract** echo the actual received cookie, driver send/receive/limits/tracing and unit result with trailing bytes. **Exclude** a local control or interval wait, dq/fetch registration and a KeepAlive client finalizer on this direction: none is present. `cleanup keepServer` is driver-unwind completion, not registry removal. |

KeepAlive is established-group work, so ending the hot group alone is not a
KeepAlive Terminate observation. Its own termination/result and group supervision
remain distinct. Normal completion still waits on mux egress before status/
physical result publication; synchronous errors use existing mux error reporting,
asynchronous cancellation remains physical pool/handler unwind. KA/BF cleanup
can delay established deactivation and handler shutdown, even after control/mux
stop is requested. Release, mux shutdown enqueue, handler finally, socket close,
logical demotion and physical Async result remain separate existing operations.

## Batch 2 checked scope and remaining gates

[Lifecycle controls](Negative/ProtocolContracts2.agda) check enabled Tx initiator,
V1/V2 responder, KA alone/captured-fetch, KA responder, error/cancel/acquisition
and cleanup replacement schedules, plus source-specific refusals.
[Job controls](Negative/ProtocolContractJobs2.agda) check clean/error/cancel/
unfinished result selection and positive Tx/KA completion conditional on a real
matching physical child and real generic mux edge. `complete-via` retains that
edge; `complete-enabled` introduces it under those premises. Existing mux egress,
result queue, status commit, job deregistration and handler cleanup are reused.
This is no new initialized application or full-bundle clean witness. The source
operation projection, shared-resource coupling, control alternative priority and
mask/readiness obligations above remain contracts; no native replay, Haskell
refinement, universal progress or whole-node shutdown theorem follows.

At batch 2, G0/G2 were partly met with **66 implemented / 16 contracted /
14 excluded / 3 missing** rows. The three missing contracts were LeiosNotify,
LeiosFetch and shared Leios allocation/cleanup. The later batches and configured
runs are documented on this page. Increment 89 records the original validation
and deferred heavy modules.

[TxOut]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/lib/Ouroboros/Network/TxSubmission/Outbound.hs
[TxIn1]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/lib/Ouroboros/Network/TxSubmission/Inbound/V1.hs
[TxIn2]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/lib/Ouroboros/Network/TxSubmission/Inbound/V2.hs
[TxRegistry]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/lib/Ouroboros/Network/TxSubmission/Inbound/V2/Registry.hs
[KA]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/lib/Ouroboros/Network/KeepAlive.hs
[KARegistry]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/lib/Ouroboros/Network/KeepAlive/Registry.hs
[TxClientPeer]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/TxSubmission2/Client.hs
[TxServerPeer]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/TxSubmission2/Server.hs
[KAClientPeer]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/KeepAlive/Client.hs
[KAServerPeer]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/KeepAlive/Server.hs
[KernelTx]: https://github.com/IntersectMBO/ouroboros-consensus/blob/2e44d98a843168ba3b189e305820b79943ac7d1e/ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/NodeKernel.hs
[MempoolInit]: https://github.com/IntersectMBO/ouroboros-consensus/blob/2e44d98a843168ba3b189e305820b79943ac7d1e/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Mempool/Init.hs
[MempoolAPI]: https://github.com/IntersectMBO/ouroboros-consensus/blob/2e44d98a843168ba3b189e305820b79943ac7d1e/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Mempool/API.hs
[MempoolUpdate]: https://github.com/IntersectMBO/ouroboros-consensus/blob/2e44d98a843168ba3b189e305820b79943ac7d1e/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Mempool/Update.hs

## Batch 3 authority and executable boundary

Reviewed 13 November 2026 at HEAD `156c0ac`; [increment 90](Supervision.md#ninetieth-increment-g0-leios-protocol-and-shared-resource-contracts).
Read-only `git show` at consensus **`2e44d98a843168ba3b189e305820b79943ac7d1e`**
verified these blobs (the bundle blob is unchanged from batch 1):

| Alias | Blob |
| --- | --- |
| [Notify] | `d0bedfb26d6190a386694bfc55e5832f41680f7d` |
| [Fetch] | `1a403a4b636f5b40576e8b030aca729a7fc808b6` |
| [Logic] | `2f3f4b5a926df486309b1f7099faeeef1547b899` |
| [LeiosDbAPI] | `2efa560dfe9d9b7979fc2bff74c6df04253ba62f` |
| [LeiosDbSQLite] | `d5f10344d0bfb8dde22b28068c15569ff6b5b2c9` |

All three rows are **contracted**, with CM-visible order guards implemented in
[ProtocolContracts3](ProtocolContracts3.agda), finite enabled/refusal
[controls](Negative/ProtocolContracts3.agda), and a conditional
[typed job adapter](ProtocolContractJobs3.agda) with
[job controls](Negative/ProtocolContractJobs3.agda). No existing Agda module or
theorem statement changes. The independent `Cardano_network` wire models do not
supply CM bracket/resource semantics, and synthetic mux protocol 1 is not recast
as a configured application. Numbers **18/19** come from [Notify] 117–118 and
[Fetch] 103–104; the sharing ChainSync initiator retains number 2.

Each endpoint is one fixed invocation for a captured connection key. `start`
certifies a successful bracket acquisition/driver entry; an acquisition failure
before acquiring any resource uses `acquisitionFailed`. For the sharing ChainSync endpoint, `acquisitionFailed` concerns failure to acquire
the nested shared bracket after entering outer CS scopes, so it still requires
`outerClosed`; other outer-CS acquisition failures belong to batch 1. Partial
acquisition or nested writer/pump setup failure must project its actual acquired-prefix unwind,
not assert that no resource was acquired. `await` records a blocked operation;
`ready`, `issue`, `collect`, `innerClosed`, `deletePeer` and `refundPeer` certify
actual source operation returns. `idle` is an operation boundary, not the full
wire state. Legal send sites, positive/configured depth limits, credit bounds,
arrived counters, actual STM alternative priority and exact response callbacks
remain source-instance obligations. Counts represent collected requests/deferred
sends; they do not establish wire correspondence or callback completion by
arbitrary counter changes. No fairness, readiness or eventual shutdown is assumed.

## LeiosNotify

### Initiator

| Lifecycle item and source lines | Disposition and exact contract |
| --- | --- |
| Control and forecast gate: [Bundle] 615–659; [Notify] 549–588 | **Implement** `checkControl`, forecast/arrival waits, and Terminate from the same control-check transaction, including while it retries. **Contract** successful STM observations: Terminate returns `Left ()` before the immutable-tip forecast; Continue **and Quiesce** require `awaitImmTipCanForecastNow` and return the configured depth. At capacity, the transaction reads control before waiting for `arrived > 0`; ordinary Collect is selected only when ephemerally blocking. It does not block forever in Collect merely because depth is full. |
| Pending replies and effects: [Notify] 590–624; [Bundle] 633–644, 660–768 | **Implement** outstanding issue/collection and callback wait observations. **Contract** receivers, ledger/header/offer/vote validation, mempool/cache/kernel/DB and tracer effects; their synchronous faults (including unexpected MsgCanceled before draining) escape. After `AlreadyDraining`, receiver callbacks are skipped, but actual reply collection is still required. **Exclude** payload correctness, credit accounting algorithms and announcement delivery from this CM kernel. |
| Quit and return: [Notify] 553–566, 626–635; [Bundle] 1866–1889 | **Implement** Terminate → `quitting` → actual `quitSent` → drain to zero → observed MsgDone. With a nonempty pipe the additional Quit receiver does not consume MsgDone; drain still precedes that final Await. **Contract** successful driver completion with `((), trailing)`; wrapper returns `(NoInitiatorResult, trailing)`. No Fetch-style Done send is substituted for Quit/Done handshake. |
| Bracket, masks and faults: [Bundle] 1880–1889, 1841–1864 | **Implement** actual body sync/cancel outcome, inner driver unwind, then shared delete/refund before finished. **Contract** ordinary bracket acquisition/release mask and restored body mask, limits/codec/channel exceptions and cleanup failures under [PrimitiveMatrix D-MASK/D-ASYNC](PrimitiveMatrix.md#resolved-dependency-evidence). This is not an uninterruptible shared finalizer. Cleanup exception replaces the body outcome and need not certify resource removal. |

### Responder

| Lifecycle item and source lines | Disposition and exact contract |
| --- | --- |
| Request/lookahead and work waits: [Notify] 637–706; [Bundle] 769–935 | **Implement** received request/deferred-send count, work/channel waits and received Quit while sender work waits. **Contract** first ordinary Await, then lookahead handoff; credit increment can throw `ExnLeiosNotifyExcessiveRequests`. Sender STM is **Quit-first** `orElse`: once quitVar is true it emits MsgCanceled, otherwise it waits on FIFO `next`. Pump waits on EB notifications/votes (ordered alternatives), gates offers, and only enqueues with credit. There is no local responder control-message read. |
| Termination: [Notify] 695–723 | **Implement** received Quit → draining → actual flushes → zero → Done send. **Contract** quitVar is set before flush so senders can emit cancellations; MsgDone follows all spawned sends, and normal peer result is unit. Pending sender work cannot be discarded by immediate normal completion. |
| Pump supervision and cleanup: [Bundle] 914–935, 1891–1909; [Notify] 736–765 | **Implement** an `innerRelease` barrier before result; `innerClosed` certifies complete pump release. **Contract** `withAsync pump`, `link` propagation of pump failure, lookahead driver sender/receiver ownership, and withAsync cancel/join semantics. Pump registers central queue view under an MVar, loops in STM, and its `finally` deletes that view under the same MVar. Successful inner closure requires actual pump finalizer completion and child join; receipt of cancellation alone is insufficient. The kernel does not expose an interruptible pump-join shortcut; dependency-specific cleanup masking remains D-ASYNC. Setup failure need not imply the pump ever registered. **Exclude** independent physical pump IDs and full central relay/FIFO correctness. |
| Results and resources: [Bundle] 1891–1909 | **Contract** `((), trailing)` after inner scope closure; normal/synchronous/cancel outcomes stay distinct. This responder has no `bracketLeiosPeer` or BlockFetch registry membership. Tracer, driver, pump and release exceptions may escape and replace an earlier outcome. |

Notify termination/results feed existing mux supervision; neither direction's
Done alone is mux stop, handler exit, CM release or a completed demotion. Hot
Terminate can be observed at its legal STM gate; peer replies/Done and pump
cleanup can still delay physical completion indefinitely.

## LeiosFetch

### Initiator

| Lifecycle item and source lines | Disposition and exact contract |
| --- | --- |
| Work/control choice: [Bundle] 937–956; [Logic] 707–772; [Fetch] 604–641 | **Implement** legal check sites, zero-depth command wait, and nonzero-depth `noCommand` → blocked collection → recheck. **Contract** `nextLeiosFetchClientCommand` first atomically tests Terminate, then dequeues work, else supplies blocking `awaitStopOrRequest` with the **same stop-first** order. Quiesce is not Terminate. With zero outstanding, execute that wait; with outstanding replies, `Left next` instead selects `Collect Nothing` and cannot read control again until a collection returns. Terminate is therefore not an immediate interrupt of this Collect. A job selected at the depth cap is retained until collection; real depth/send choices are certified inputs, not proved by this counter abstraction. |
| Receiver effects / DB waits: [Fetch] 644–675; [Logic] 774–812, 1006–1007, 1455 | **Implement** callback/DB blocking observations and prohibition of local control/normal completion there. **Contract** actual inline receiver processing, kernel/cache MVar operations, writer submissions/awaits, validation, mempool reads and exceptions. On draining, skip callback effects but still collect wire replies. Reuse existing [MuxProtocolJobs DB waits](MuxProtocolJobs.agda) and [historical DB replay](SourceReplay/README.md#m6-revalidation-at-network-2f1c154-9-november-2026): cancelling an awaiter does not retract committed queued work. The new adapter does not automatically pair an abstract `database` wait with a concrete writer job; a source projection must keep both consistent. |
| Termination/result: [Fetch] 622–625, 677–687; [Bundle] 1911–1935 | **Implement** stop → drain all outstanding replies → **send MsgDone** → inner scope cleanup. Fetch does not await a Notify-style MsgDone reply. **Contract** result `(NoInitiatorResult, trailing)` after driver returns unit and nested writer scope closes. |
| Resources, masks and faults: [Bundle] 1925–1935; [LeiosDbAPI] 193–197 | **Implement** writer/driver inner closure before shared peer deletion/refund. An inner writer-close fault or interruption still enters the enclosing shared finalizer with that new outcome; only a fault in the shared finalizer can leave its own cleanup uncertified. **Contract** outer `bracketLeiosPeer`, nested `withWriter = bracket openWriter closeWriter`, successful/partial acquisitions, restored body mask and masked interruptible release. Actual sync/async receipts and DB/driver/tracer failures are observations; there is no local catch converting cancellation into a clean result. **Exclude** SQLite/FFI close internals and universal write durability. |

### Responder

| Lifecycle item and source lines | Disposition and exact contract |
| --- | --- |
| Request/DB/response: [Fetch] 545–568; [Bundle] 957–962, 1937–1951; [Logic] 230–285 | **Implement** channel/DB waits with normal Done refused during DB work. **Contract** sequential nonpipelined handler (despite pipelined initiator), reader context, body/transaction lookup and response send. Unknown requested block and malformed stored encoding throw; tracer/DB/channel/driver errors can also escape. Requests beyond this abstraction's legal input protocol are not silently successful. There is no responder control/work-selection STM or shared peer-vars bracket. |
| Termination, reader and result: same ranges; [LeiosDbAPI] 193–194 | **Implement** received MsgDone → inner reader/driver cleanup → finished. **Contract** `withReader = bracket openReader closeReader`, masked acquisition/release, restored body mask, actual synchronous/async faults at permitted sites and replacement errors. Return `((), trailing)` only after cleanup. **Exclude** reader connection internals, data validity and response-delivery guarantees. |

Both directions use the existing generic body result/egress/pool path. A DB wait,
pipeline drain, writer/reader close or remote Done may delay demotion and handler
exit. Protocol completion alone does not create CM release, mux shutdown, Cold,
socket cleanup or an Async result; these retain their existing separate rules.

## Shared Leios peer resources

### Initiator clients: ChainSync, Notify and Fetch

| Lifecycle item and source lines | Disposition and exact contract |
| --- | --- |
| Acquisition/sharing: [Bundle] 1473, 1819–1857, 1880, 1925 | **Implement** first-or-later `start` sets shared presence without refcounting; distinct fixed invocations can start while siblings run. **Contract** fresh `newLeiosPeerVars` allocation followed by atomic **get-or-create** under full `MkPeerId ConnectionId` key. If present, use existing vars and discard unused fresh vars. Actual cell identity, big-ledger attribute, connection incarnation and all partial acquisition prefixes are certified inputs. This is separate from [Registry]'s CS/BF synchronization and KeepAlive's doneVar: no BF registry done/removal inference follows. |
| First exit and cleanup ordering: [Bundle] 1819–1835, 1859–1864 | **Implement** each successful bracket exit deletes presence **before** refund, even with other clients live. There is **no reference count or last-client wait**. `innerClosed` must certify all nested scopes first, including Fetch's writer. For ChainSync, the shared bracket is **inside** its candidate/sync brackets ([Bundle] 1456–1474): delete/refund precedes batch-1 candidate/watcher/sync cleanup, certified by a separate `outerClosed` barrier before whole-job completion. **Contract** delete is atomic; refund takes the outstanding MVar, applies `removePeerFromOutstanding`, then restores it. These are two operations; no atomic delete+refund assumption. |
| Accounting removal: [Logic] 1142–1171; [Bundle] 1828–1835 | **Implement** separate `charged` residue, successful refund clears it, and decision-loop `account` refuses absent map entries. **Contract** actual per-peer bytes, EB-peer sets and job maps are removed, and job multiplicities unpicked under outstanding lock. Decision loop re-reads the live peer map **inside** that lock; this serializes increments against removal. **Exclude** numerical byte/multiplicity correctness, scheduling/fairness and complete concurrent decision-loop implementation. The Boolean is an abstraction, not a conservation theorem. |
| Siblings/stragglers: [Bundle] 1844–1847, 1860–1864 | **Implement** idempotent later cleanup and late allocation after deletion; no restart of the same invocation. **Contract** new invocations/captured cell identities must be tracked externally. Deletion is by **peer key**, not comparison with captured `_peerVars`: an older exiting sibling may delete a re-created entry. The kernel deliberately makes no generation-isolation or immunity claim for that entry; operational coupling/teardown-together is an explicit source assumption, not a proved guarantee. |
| Masking, exceptions and result | **Implement** body sync/cancel exit, release faults replacing outcomes, and actual async receipt while blocked acquiring the refund MVar, retaining residue. **Contract** ordinary bracket acquisition/release masking, body restoration and MVar exception restoration from PrimitiveMatrix. Pure delete offers no ordinary async delivery site. If acquisition fails, only its successfully acquired prefix is unwound. Failure after delete need not refund outstanding work, and normal bracket return requires both observed successes. **Exclude** unconditional cleanup progress or immediate/independent sibling cleanup. |

### Responders

[Bundle] 1891–1909 and 1937–1951 do **not** use `bracketLeiosPeer` for these
responders. **Exclude** shared initiator peer-vars allocation/removal for them;
**contract** their actual private resources (Notify pump/central view, Fetch
reader) as specified above. This does not remove the responder failure paths.

### CM boundary and remaining acceptance

`ProtocolContractJobs3` binds fixed distinct physical children to the captured
connection and checks live executing child, number and direction on every
endpoint event. Shared `account` is a source-certified environment input.
`complete-via` exposes the actual generic mux edge and `complete-enabled`
constructs it from explicit real-child/egress premises; enabled examples are
**conditional**, not a constructed initialized application run. Only finished
normal or synchronous outcomes select generic return/exception. Finished
cancellation, blocked work, unfinished drain, inner close and refund cannot
become clean/synchronous body results. Pump failure is an observed body failure;
this kernel does not claim a new physical nested-pool invariant.

Historical batch-3 acceptance boundary, superseded by increment 92 above:
**66 implemented / 19 contracted / 14 excluded / 0 missing** at that checkpoint.
G0 **cannot yet be called met**: executable LocalLifecycle configuration must
still reconcile two-peer targets, bundle/group selection and concrete source
PRNG seed/selection assumptions. A full configured-bundle initialized clean
witness (including nonempty established/KeepAlive group and these protocol/job
contracts on shared resources) is still absent; reduced protocol-1 witnesses and
conditional adapters do not provide it. This also blocks G2 full-profile
acceptance. Batch 3 completes the three lifecycle reviews; it adds no native
replay, universal progress, Haskell refinement or whole-node shutdown claim.

[Notify]: https://github.com/IntersectMBO/ouroboros-consensus/blob/2e44d98a843168ba3b189e305820b79943ac7d1e/ouroboros-consensus/src/ouroboros-consensus/LeiosDemoOnlyTestNotify.hs
[Fetch]: https://github.com/IntersectMBO/ouroboros-consensus/blob/2e44d98a843168ba3b189e305820b79943ac7d1e/ouroboros-consensus/src/ouroboros-consensus/LeiosDemoOnlyTestFetch.hs
[Logic]: https://github.com/IntersectMBO/ouroboros-consensus/blob/2e44d98a843168ba3b189e305820b79943ac7d1e/ouroboros-consensus/src/ouroboros-consensus/LeiosDemoLogic.hs
[LeiosDbAPI]: https://github.com/IntersectMBO/ouroboros-consensus/blob/2e44d98a843168ba3b189e305820b79943ac7d1e/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Storage/LeiosDB/API.hs
[LeiosDbSQLite]: https://github.com/IntersectMBO/ouroboros-consensus/blob/2e44d98a843168ba3b189e305820b79943ac7d1e/ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/Storage/LeiosDB/Impl/SQLite.hs


## Historical increment 91 configuration boundary

The installer refusal below was superseded by increment 92 above; the retained
prefix and conditional-adapter results keep their original scopes.

The [pinned configuration reconciliation](BranchMatrix.md#pinned-locallifecycle-profile--increment-91)
identifies an earlier execution blocker: source established KeepAlive **8** is
`StartOnDemandAny`, rejected by the then-current model's handle installer. The initialized
[24-event diagnostic](Negative/FullConfiguredBlocked.agda) and its
[OwnedCallers prefix certificate](Negative/FullConfiguredBlockedCallers.agda)
do not instantiate these three adapters. They remain conditional; no protocol
contract state is injected or declared completed to bypass allocation. Warm is
empty in this selected source profile. Increment 91 records the configuration
and full-execution work that remained at that checkpoint.
