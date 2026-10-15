# Initial source-to-transition ledger

**Updated 15 October 2026.** Companion to [DESIGN.md](DESIGN.md).

All network paths and line ranges below refer to
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`. Consensus protocol contracts use
`585a86117618ff86d7d5b541f9d23b03356d4c3a`. These are fixed baselines, not a claim
about the latest branch heads.

This is an initial implementation ledger. **Expanded** entries define selected
operation boundaries checked against the source. **Family** entries locate the
required behavior but still need per-branch transcription before coding. These design statuses alone do not mean implemented, tested, or proved.
The implementation coverage below is tracked separately. An unexpanded branch is not implicitly
unreachable and must never silently become `nothing` in `advance`.

## Current implementation coverage

The [CM primitives](Rules/CM.agda) implement map take/put/restore, captured-entry
writes and the entry-selection transaction. The [server prefix](Rules/Server.agda)
executes admission after handoff through map publication and the subsequent counter
read, ending at handshake wait. It includes normal hard-limit rejection and
forbidden/fork-failure restoration and socket closure. The inbound-count projection
also follows `Core.hs:174–215`, which is needed by `Core.hs:557–562`.

[Map-lock properties](Properties/MapLocks.agda), [prefix witnesses](Scenarios/Admission.agda)
and [a negative control](Negative/HeapRollback.agda) typecheck. They establish
primitive guarantees and model-prefix behavior, not source refinement or complete
coverage of these rule families. Accepted-socket handoff is the fixture boundary;
`SERVER.ACCEPT/HANDOFF`, child body execution and general exception/supervision behavior
are not implemented. See [scope](README.md).

[Handshake rules](Rules/Handshake.agda) now transcribe the inbound result consumer
in `Core.hs:897–1101`: separate read, success update or error/query cleanup, counter
read, IG enqueue and return. `Types.hs:266–322` supplies non-consuming promise reads
and duplicate-write exceptions. `InformationChannel.hs:35–54` supplies the queue
bound of 100. `ConnectionHandler.hs:186–200` supplies the two error classes;
`401–460` locates the abstract publication boundary. Actual negotiation, handle/mux
allocation and delayed query shutdown remain unimplemented. Handler cleanup is now
implemented separately from an abstract exit boundary; see §4.2.

[Handshake witnesses](Scenarios/Handshake.agda), [local reference lemmas](Properties/Entries.agda),
[success preservation](Properties/Handshake.agda) and the [stale-result negative
control](Negative/StaleHandshake.agda) check this slice. They do not establish
source reachability for injected replacement/self-connection fixtures, whole-state
validity, exception unwinding, or IG registration. Enqueueing a notification is not
registering or running a responder.

The [combined dispatcher](Machine.agda) delegates to these rule families with a
fixed responder mode and explicit duplicate-publication faults. The [CSP
interpretation](CSP/README.md) renders that dispatcher directly, proves raw
step/finite-trace correspondence, and reuses the dependency's hiding laws. This
adds a semantics for the existing rules, not new source coverage. Scope diagnostics
identify selected unimplemented continuations without inventing progress events.

## 1. Rule record and naming

Every implemented rule receives a stable identifier, for example
`CM.MAP.TAKE`, plus a branch discriminator where needed. Record:

```text
id; source SHA/path/range; enclosing function; worker/caller;
entry continuation; captured inputs; guard;
read set; write set; resource/lock effects;
atomicity; successor continuation/result;
retry conditions; synchronous exceptions; async delivery/masking;
diagnostic label; external observation (if any);
abstraction justification; scenario coverage; validation witness/property.
```

Events in the ledger name actual state changes or diagnostic labels, not new
channels inserted into the Haskell design. Calls execute in their caller's frame.
Do not omit a real queue-writing tracer as “logging.” Pure diagnostic tracing can
be abstracted only with its assumptions recorded.

## 2. Shared primitives and helper audit

| ID | Source | Worker / boundary | Required behavior | Status |
|---|---|---|---|---|
| `CM.MAP.TAKE/BODY/PUT/RESTORE` | [Core helpers][cm-helpers] | Caller of IO `modifyTMVar` | Map taken in STM, IO body, put or saved-map restoration; current heap survives restoration | Expanded §4 |
| `CM.MAP.STM` | [Core helpers][cm-helpers] | Caller of STM helpers | Take/body/put in one commit; retry rolls back all tentative writes | Expanded §4 |
| `SYNC.FIRST` | [Synchronisation][sync] | STM caller | `FirstToFinish` uses alternative semantics; preserve ordering of operands | Family: specialize each call site |
| `SYNC.ALL` | [PeerStateActions results][results] | Action/monitor caller | Preserve result/error aggregation and empty-bundle behavior; not an arbitrary “all done” flag | Family |
| `JOB.FORK/REGISTER` | [JobPool fork][job-fork] | Parent and newly runnable child | Parent masked, child can execute before registry insertion | Expanded §5 |
| `JOB.COMPLETE/DEREGISTER` | [JobPool fork][job-fork] | Job child | Queue result only for `WithQueue`; deregister waits for registration; async exceptions excluded from ordinary error handler | Expanded §5 |
| `JOB.WAIT/CANCEL` | [JobPool][job-pool] | OG or scope owner | `waitForJob` reads unbounded TQueue; pool close cancels jobs with source masking/join behavior | Family |
| `IG.QUEUE` | [InformationChannel][info] | Producers and IG | Capacity 100 TBQueue; FIFO write and whole-queue flush in caller STM | Expanded §6 |
| `MUX.STOP/STOPPED` | [Mux API][mux-api] | Calling action/IG thread | Stop writes `CmdShutdown` to an unbounded command TQueue; stopped reads mux status and may retry | Family |
| `EXN.DELIVER` | Call sites plus pinned concurrency dependencies | Sender/target/scope owner | Distinguish request, blocking `throwTo`, permitted delivery, unwinding and termination | Family; dependency audit required |
| `TIMER/PROMISE` | [Handler][handler], [OG loop][og], [Actions][actions] | Owner and observer | Capture fresh token/promise, readiness, read, cancellation; preserve timeout winner ordering | Family; dependency audit required |

The mux also has its own execution/job machinery and an egress queue. Do not
identify any of those with the IG information queue or OG job-completion queue.
The first model abstracts detailed egress scheduling through an explicit contract;
it must not add a bounded queue to a source-unbounded channel.

## 3. Component coverage index

### Server and runtime wiring

| ID | Source | State/effect and continuation boundary | Status |
|---|---|---|---|
| `WIRE.START/SUPERVISE` | [Diffusion][diffusion], [Server.with][server] | Initiator/responder wiring; IG public state to OG when enabled; server action/IG/accept-loop failure propagation | Family |
| `SERVER.RATE.READ` | [RateLimiting][rate] | Atomic count read, then decide no delay/soft delay/hard wait | Expanded: read separate from admission |
| `SERVER.RATE.WAIT` | [RateLimiting][rate] | Hard wait for count below limit, then any remaining minimum delay; soft delay is separate | Family |
| `SERVER.ACCEPT` | [acceptLoop][accept] | Interruptible accept; socket held after success; aborted-accept delay versus fatal failure | Family |
| `SERVER.HANDOFF` | [acceptLoop][accept] | Masked interval, local-address lookup, async admission; close on relevant failures; parent resumes next accept | Expanded §4 |

### CM and handler operations

| ID | Source | State/effect and continuation boundary | Status |
|---|---|---|---|
| `CM.INCLUDE` | [Inbound admission][include] | Lock map, check hard limit, select/overwrite/create entry, fork handler, restore map, await handshake | Expanded §4 |
| `CM.INCLUDE.RESULT` | [Inbound admission][include] | Read captured entry, branch on current state and handshake result, negotiated update, notification transaction, return | Family; source branches mandatory |
| `CM.ACQUIRE.SELECT` | [Outbound acquisition][acquire] | Remote-address lookup and PRNG state; return existing connection/error/wait/reservation branch | Family |
| `CM.ACQUIRE.CONNECT` | [Outbound acquisition][acquire] | Reserve unknown local address, socket/connect, update local key, fork handler and await negotiation | Family |
| `CM.ACQUIRE.REUSE` | [Outbound acquisition][acquire] | Duplex reuse, current entry/handle captures and CM transition; reject unsupported unidirectional reuse | Family |
| `CM.RELEASE.IN` | [Inbound release][release-in] | Lookup key, atomic state/result decision, trace/count read, possible cancellation, assertion evaluation, return | Expanded §7 |
| `CM.RELEASE.OUT` | [Outbound release][release-out] | Per-constructor release decisions, pruning, idle/termination waits and later cancellation | Family |
| `CM.REMOTE.WARM` | [Remote promotion][remote-warm] | Promotion transitions and relevant pruning/cancellation | Family |
| `CM.REMOTE.COLD` | [Remote demotion][remote-cold] | Demotion by exact key/entry, state-dependent results | Family |
| `CM.PRUNE` | [Pruning helper][prune] and operation call sites | Candidate selection, committed state changes, subsequent cancellation | Family; do not fuse phases |
| `HANDLER.PUBLISH/RUN` | [ConnectionHandler][handler] | Negotiate, allocate control bundle/mux handle, publish promise, then enter mux execution | Expanded ordering; failure/query branches still Family |
| `HANDLER.CLEANUP` | [forkConnectionHandler cleanup][cleanup] | Identity-sensitive map cleanup, entry updates, socket/timeout/cancellation obligations | Expanded §4.2; cleanup slice implemented with exit/timeout/close boundaries |

### IG

| ID | Source | State/effect and continuation boundary | Status |
|---|---|---|---|
| `IG.BATCH` | [Setup and batch selection][ig-batch] | Read time, arm inactivity timer, choose STM alternative, prefix generated event if applicable, flush queue | Expanded §6 |
| `IG.NEW` | [Event handling][ig-events] | Read published state; keep existing entry or prepare/start responders and register new entry | Family |
| `IG.FINISHED` | [MuxFinished handler][ig-finished] | Capture currently registered mux by key; wait on captured mux; prepare unregister decision | Expanded §6 |
| `IG.PROTOCOL.END` | [Event handling][ig-events] | Current registration, outcome, and restart behavior | Family |
| `IG.REMOTE` | [Event handling][ig-events] | WaitIdle, promote/demote, maturity and idle-state transitions | Family |
| `IG.COMMIT` | [CommitRemote/publication][ig-commit] | Caller-run CM release; CommitTr/KeepTr/unsupported handling against captured state | Expanded §7 |
| `IG.PUBLISH` | [CommitRemote/publication][ig-commit] | Commit prepared decision under masking, then traces/continuation | Expanded boundary; specialize each decision |
| `IG.TRACER` | [Mux tracer][ig-tracer] | Sample active flag; producer STM reads counters/IG state; conditional retries and atomic message bursts | Expanded §6; branch transcription needed |
| `IG.EXIT` | [Setup and exception handler][ig-batch] | Set inactive, final queue flush, trace and rethrow; already captured active reads remain possible | Expanded boundary |

### OG, peer actions and protocol lifecycle

| ID | Source | State/effect and continuation boundary | Status |
|---|---|---|---|
| `OG.DECIDE` | [Governor loop][og] | Inputs/time, ordered guarded alternatives, timed decision, private state and published view | Family |
| `OG.LAUNCH` | [Governor loop][og] | Publish view/traces then fork selected jobs individually; parent continuation retained | Expanded boundary |
| `OG.COMPLETE` | [Monitor.jobs][og-monitor] | Read completion in guarded STM; apply captured completion function to current OG state/time | Expanded boundary; defunctionalize per job |
| `OG.ESTABLISH/CLOSE` | [EstablishedPeers][established] | Target/eligibility guards, in-progress changes, establish/close jobs, exception completions | Family |
| `OG.ACTIVATE/DEMOTE` | [ActivePeers][active] | Guards, captured peer handle, hot promotion/demotion jobs and completion bookkeeping | Family |
| `ACTION.ESTABLISH` | [PeerStateActions][actions] | Acquire; initialize controls/results; start selected groups; publish Warm; fork monitor | Family |
| `ACTION.ACTIVATE` | [PeerStateActions][actions] | State-dependent controls/start operations and status publication | Family |
| `ACTION.DEACTIVATE` | [Deactivation and close][actions-close] | Guarded control transaction, all-hot-results wait, status-sensitive result branch or stop/cooling/error | Expanded milestones §8 |
| `ACTION.CLOSE` | [Deactivation and close][actions-close] | All-temperature termination, result wait and CM release/error/timeout paths | Family |
| `PEER.MONITOR` | [Peer monitoring][actions-monitor] | First-result alternatives, concurrent demotion/close, source Cold condition | Family |
| `OG.DEMOTE.ERROR` | [Demotion job][demote-job] | Separate timed wait for Cold; timeout-dependent completion membership changes | Expanded milestones §8 |
| `PROTOCOL.CONTRACT` | [Consensus bundle][bundle], [Notify][notify], [Fetch][fetch], [BlockFetch registry][registry] | Control reads, pending work, blocking, run results and bracket cleanup | Family; initial per-protocol contracts required |

## 4. Expanded admission and map-lock boundaries

### `SERVER.HANDOFF`

Caller: accept loop after a successful `runAccept`. Captured values: accepted
socket, remote address and next accept action. The source masking scope protects
handoff; it does not make the entire sequence one transaction. Obtain the local
address, construct the key and fork an admission worker. The child runs the CM
include operation with the captured hard limit. Disconnected and exception paths
close the socket. The parent continues accepting independently.

The initial socket-ownership obligation begins at acceptance, before map insertion.
Fork is an observable machine step but not a rendezvous requiring IG or OG to be
ready. Source synchronous exceptions and interruptible operations still need their
correct handlers; “masked” does not imply “cannot throw.” [acceptLoop][accept]

### `CM.INCLUDE`: branch table under map ownership

Caller: admission worker. First take the map TMVar using IO `modifyTMVar`.
Read the incoming count over the held map's entry references in its source STM
transaction. If adding one would exceed the hard limit, retain the map and return
the disconnected result after putting it back.

Otherwise select the exact-key entry and execute the source entry transaction:

| Existing entry state | Effect |
|---|---|
| Absent | Allocate a fresh mutable entry containing unnegotiated inbound state |
| Reserved outbound | Write unnegotiated inbound state into the existing entry |
| Unnegotiated | Write unnegotiated inbound state into the existing entry |
| Any established outbound/inbound/duplex state, including outbound idle | Throw the source forbidden-operation exception |
| Terminating or terminated | Allocate a fresh mutable entry |

Fork the connection handler at its source point, retaining the selected entry and
handshake promise. Return an updated map to the helper, which publishes it in a
separate transaction. Only then does the caller proceed to the handshake promise
wait. The child may run before the map is put back. [Admission][include]

**Read set:** map binding captured under ownership, entry TVars for counting and
selection, identity supply. **Write set:** selected entry or fresh entry/supply,
promise allocation, child worker state, then map publication. These are several
steps, not one combined write set committed atomically.

**Exception restoration:** put back the saved map binding structure; retain
earlier committed entry changes and IO effects. Model the source cleanup handlers
for any created socket/child. Whole-state rollback is incorrect.

The comment above the overwrite code mentions replacement, but the executable
reserved/unnegotiated branches write the existing TVar and return that same entry.
Transcribe executable branches, not an isolated comment. [Admission][include]

### 4.1 Implemented inbound handshake consumer

| Model operation | Pinned source | Atomicity and result |
| --- | --- | --- |
| `publishBoundary` | `ConnectionHandler.hs:422–455`, `Types.hs:297–317` | Abstract entry at handler `writePromise`; ordinary publication or explicit duplicate-write exception. No negotiation/allocation rule implied. |
| `readResult` | `Core.hs:897` | One non-consuming STM read; retains the result and captured entry across subsequent scheduling. |
| `commitResult` / `decideSuccess` | `Core.hs:909–965` | One entry-only STM; every constructor has an outcome, including impossible-state exception. No global-map wait. |
| `commitResult` / `terminateResult` | `Core.hs:1007–1101` | One STM reads captured entry and full map, compares entry identities, updates and deletes only if still current. |
| `readResultCounters` | `Core.hs:968`, `1073` | Separate map/entry read; can block behind another map owner. |
| `enqueueInbound` | `Core.hs:984–989`, `InformationChannel.hs:35–54` | Connected responder-mode results enter the capacity-100 FIFO. No IG-active guard or drain added. |
| `returnResult` | `Core.hs:990–995`, `1075` | Explicit CM API return; server handling remains later work; handler cleanup is a separate rule family. |

`OutboundIdleState` uses the pre-existing flow in the new entry but reports the
negotiated result flow in `Connected`/`NewConnectionInfo`. `OutboundUniState` and
`OutboundDupState` retain the existing entry while reporting outbound provenance.
These are transcribed branch behaviors, not evidence that arbitrary mismatched
flow fixtures are source-reachable.

### 4.2 Implemented handler cleanup

[Cleanup rules](Rules/Cleanup.agda) transcribe `forkConnectionHandler`'s finalizer
at `Core.hs:594–713`. The fork now retains the connection key as well as entry,
socket and promise references. `beginCleanupBoundary` assumes body exit and prevents
later publication by that body; it does not run negotiation, mux, query delay, or
rethrow policy. Ordinary trace calls are abstracted as total/nonblocking. Counter
reads are retained. Socket-close success/failure and delay readiness are explicit
inputs, not derived from transport or a clock model.

| Model operation | Source | Atomicity and effects |
| --- | --- | --- |
| `takeCleanupMap` | `606`, helper `2366–2380` | Take map separately; retain a saved map lease. |
| `selectCleanupEntry` | `607–653` | One entry STM while holding map. All ordinary constructors write `Terminated Nothing` and propose identity-guarded purge. Already-Terminated proposes purge without writing. Terminating retains state/map and captures the TIME_WAIT branch. |
| `closeHandlerSocket` | `655–662` | Socket IO while map remains taken; proposed map is still unpublished. |
| `failSocketClose` / `restoreCleanupMap` | `658/661`, helper exception branch | Mark socket outcome uncertain; restore saved map, retain committed entry writes, expose cleanup error. |
| `publishCleanupMap` | helper completion | Put proposed map separately; route to counter read or TIME_WAIT. |
| `timeWaitElapsed` / `interruptTimeWait` | `666–669` | Untimed environment completion/interruption of unmasked delay; both enter finally. |
| `finishTimeWait` | `677–709` | One STM writes captured entry and identity-guards deletion. If map is taken, neither effect commits. Uses captured state, not a refreshed decision. |
| `readCleanupCounters` | `665/713` | Separate full-map/entry read, then finalizer completion or delayed interruption propagation. |

The Terminating branch is the only valid entrance to TIME_WAIT. Therefore the
captured abstract-state comparison in the finalizer requests a write even if the
current entry has since changed. A different mapped EntryId protects that binding;
a changed WorkerId in the same entry does not. Already-Terminated in the initial
selection preserves its error, unlike the finalizer reached from Terminating.

[Cleanup properties](Properties/Cleanup.agda) prove local purge, map-cell,
reference-preservation and atomic-blocking facts. [Scenarios](Scenarios/Cleanup.agda)
cover result/cleanup ordering, close failure, interruption and replacement fixtures.
The [negative control](Negative/CleanupAtomicity.agda) refutes splitting the final
STM into an exposed entry write followed by a blocking map acquisition. These are
model properties under stated boundaries, not source refinement or race-reachability
proofs. No global exception/masking semantics or real-time liveness claim is made.

## 5. Expanded job-pool boundaries

`forkJob'` masks the parent, forks the child, then inserts the child's handle in
the pool registry. The child runs its action under the supplied restore operation.
Its ordinary exception handler excludes asynchronous exceptions. On normal result,
`WithQueue` publishes to its unbounded TQueue; `WithoutQueue` publishes no result
queue item. Deregistration is a later transaction which retries if the parent's
insertion has not happened yet. Exception cleanup also deregisters. [JobPool fork][job-fork]

Consequences for the model:

- Result readiness, completion consumption and job deregistration are distinct.
- A completion can be consumed while deregistration is still pending.
- Parent registry insertion is not fused with the child's first operation.
- Async cancellation does not automatically produce an ordinary failure completion.
- OG decision jobs use `WithQueue`. Per-peer monitoring jobs use `WithoutQueue`.
  Mux use of the helper has its own pool and must not share either registry.

The model should use explicit child phases `action`, `handleError`, `publish`,
`deregister`, `done`, with captured result/error where applicable. Cancelled-child
phases follow the exception stack and source pool cleanup semantics rather than
unconditionally traversing the normal result path.

## 6. Expanded IG boundaries

### Batch selection

The IG samples time and arms an inactivity timer, then runs ordered STM
alternatives. A maturity event or first ready idle-commit event can be prefixed to
the flushed queue. Other alternatives flush a nonempty queue or produce an
inactivity event. Preserve the source fold/alternative order and captured time;
do not choose an arbitrary ready peer or replace the sampled time each retry.
The exact interaction with freshness and timer helpers is part of per-branch
transcription. [Batch selection][ig-batch]

After the transaction, the batch is IG-local state and queue capacity is available
to producers again. IG handles events sequentially, reading published state for
each event. It does not hold a transaction open across the whole batch.

### `MuxFinished`

At the handler's published-state read, resolve the event's key. If no entry exists,
continue with no decision. Otherwise capture that entry's mux, await
`Mux.stopped` in STM, then prepare removal by key from the captured IG state and
later publish it. The event contains a key, not the originating mux identity.
The wait cannot switch target simply because another map binding would now be
found. [Handler][ig-finished]

### Producer tracing and exit

The mux tracer first reads IG's active flag outside the later event-specific STM
transaction. Preserve that captured boolean. Protocol-start/end branches consult
published IG state and responder counters. A completion can enqueue three messages
in one commit; a full queue retries the entire transaction. Producer blocking
therefore blocks that source worker, not an invented asynchronous logging service.
[Tracer][ig-tracer]

IG exit first sets the active flag false, then performs a final queue flush, then
traces/rethrows. A tracer that already sampled true retains that value. Do not
claim exit atomically disables every in-flight producer. A live IG blocked in an
event handler does not execute this exit path merely because it is blocked.
[Exception handler][ig-batch]

## 7. Expanded inbound release and caller continuation

Caller: IG handling `CommitRemote`, or another permitted caller specified by the
scenario. Capture the connection key; lookup and current-entry read occur inside
the release transaction, so they need not identify the mux in IG's snapshot.

Selected source branches, before later assertion evaluation/cancellation:

| Current CM condition | State effect | Nominal result / later work |
|---|---|---|
| No map binding | None | CommitTr, no cancellation |
| Reserved / unnegotiated / outbound unidirectional | None | UnsupportedState |
| Outbound duplex, Ticking | Mark Expired | KeepTr |
| Outbound duplex, Expired | Unexpected/assertion path | Do not assume KeepTr returns with assertions enabled |
| Outbound idle | None | CommitTr plus unexpected/assertion handling |
| Inbound idle | Mark Terminating | CommitTr; capture handler for cancellation |
| Inbound active | Mark Terminating | UnsupportedState; capture handler and assertion handling |
| Duplex | Change to outbound duplex Ticking | UnsupportedState plus assertion handling |
| Terminating | None | CommitTr |
| Terminated | None | UnsupportedState |

The release transaction returns pending effects and its result. Source code then
traces the transition, reads/traces counters, requests cancellation with `throwTo`
where applicable, evaluates pending assertion handling, and finally returns. The
counter read can itself wait for the map TMVar; cancellation can block its sender.
Preserve inline assertion evaluation as well as deferred assertion handling.
[Inbound release][release-in]

The IG remains in this call until return or exception. After successful return:
CommitTr prepares unregister; KeepTr prepares RemoteCold; UnsupportedState yields
no decision. Publication is a separate masked STM action. Do not collapse CM update,
cancellation and IG publication, or force a nominal result to return through an
assertion exception. [IG CommitRemote][ig-commit]

## 8. Expanded demotion milestones

1. OG selects a source-permitted demotion and records in-progress work.
2. The job captures the peer connection handle and calls deactivation.
3. In the PeerHot branch, one STM transaction writes hot Terminate and warm Continue.
4. The action waits for hot results under its deactivation timeout. All-success,
   error and concurrent peer-status changes have distinct handling.
5. Timeout enqueues mux stop, conditionally updates Cooling, and throws; mux cleanup
   is not completed by this step.
6. The job's synchronous-error handler waits for observed Cold under a separate
   demotion timeout. Timeout of this outer wait changes the returned completion's
   treatment of active/established peers.
7. OG later consumes the completion against its then-current state.

Per-peer monitoring runs concurrently throughout. A return from deactivation does
not unconditionally imply that peer status is Warm: preserve state checks and the
source PeerWarm shortcut. Do not carry over HotDemotion's simplified immediate
post-timeout outcome. [Actions][actions-close], [Demotion job][demote-job]

## 9. Source expansion and implementation checklist

Before declaring a selected rule implemented:

- Give every source case either a rule or a proved/explained scenario exclusion.
- Distinguish impossible-state exceptions from disabled transitions.
- Follow helper implementations and all enclosing masking/bracket scopes.
- Identify fields captured before a wait; do not refresh them on resumption.
- Give every allocated object an explicit lifetime and cleanup responsibility.
- Record the semantic effect of any omitted trace, assertion, IO or policy hook.
- Add a small reachable witness or guard/branch check appropriate to the rule.

Priority expansion order: map primitives → accept/admission/handler → IG batch and
registration → outbound acquisition/peer establishment → OG jobs/monitoring →
activation/demotion → release/cleanup → combined race scenarios. Add assertions,
exceptions and cleanup while implementing each path, not after its happy path is
declared complete.

The generic concurrency dependency's promise/timeout/exception semantics and the
full protocol lifecycle contracts remain explicit audit items. No source-refinement
or complete-ledger claim is made by this initial document.

## Pinned references

[cm-helpers]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L2364-L2400
[sync]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/monoidal-synchronisation/src/Data/Monoid/Synchronisation.hs
[job-fork]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/network-mux/src/Control/Concurrent/JobPool.hs#L113-L177
[job-pool]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/network-mux/src/Control/Concurrent/JobPool.hs
[info]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor/InformationChannel.hs#L35-L54
[mux-api]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/network-mux/src/Network/Mux.hs#L121-L180
[diffusion]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/Diffusion.hs#L625-L825
[server]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/Server.hs#L134-L180
[accept]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/Server.hs#L188-L254
[rate]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/Server/RateLimiting.hs#L68-L139
[include]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L778-L1040
[acquire]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1264-L1832
[release-in]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1107-L1260
[release-out]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1834-L2060
[remote-warm]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L2061-L2252
[remote-cold]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L2253-L2355
[prune]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L720-L777
[cleanup]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L570-L719
[handler]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionHandler.hs#L324-L455
[ig-batch]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor.hs#L182-L280
[ig-events]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor.hs#L278-L598
[ig-finished]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor.hs#L400-L415
[ig-commit]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor.hs#L529-L598
[ig-tracer]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor.hs#L625-L735
[og]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/Governor.hs#L497-L725
[og-monitor]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/Governor/Monitor.hs#L97-L150
[established]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/Governor/EstablishedPeers.hs
[active]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/Governor/ActivePeers.hs
[demote-job]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/Governor/ActivePeers.hs#L961-L1080
[actions]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerStateActions.hs
[actions-monitor]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerStateActions.hs#L600-L855
[actions-close]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerStateActions.hs#L985-L1107
[results]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerStateActions.hs#L361-L435
[bundle]: https://github.com/IntersectMBO/ouroboros-consensus/blob/585a86117618ff86d7d5b541f9d23b03356d4c3a/ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/Network/NodeToNode.hs
[notify]: https://github.com/IntersectMBO/ouroboros-consensus/blob/585a86117618ff86d7d5b541f9d23b03356d4c3a/ouroboros-consensus/src/ouroboros-consensus/LeiosDemoOnlyTestNotify.hs#L529-L723
[fetch]: https://github.com/IntersectMBO/ouroboros-consensus/blob/585a86117618ff86d7d5b541f9d23b03356d4c3a/ouroboros-consensus/src/ouroboros-consensus/LeiosDemoOnlyTestFetch.hs#L591-L687
[registry]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/BlockFetch/ClientRegistry.hs#L75-L193
