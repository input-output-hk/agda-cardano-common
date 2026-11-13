# ChainSync and BlockFetch lifecycle contracts

Reviewed 13 November 2026, batch 1 / [Supervision increment 88](Supervision.md#eighty-eighth-increment-g0-chainsync-blockfetch-and-registry-contracts).
The three [branch rows](BranchMatrix.md) are **contracted**, with executable
ordering guards. They no longer lack a reviewed lifecycle contract. This is a
source review and finite model evidence, not Haskell refinement or full G2
configured-bundle acceptance.

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
Validation and unperformed heavy checks are recorded in increment 88. G0 and G2
full-profile status remain partly met; TxSubmission2, KeepAlive, LeiosNotify,
LeiosFetch and shared Leios-resource contracts are still missing.

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
