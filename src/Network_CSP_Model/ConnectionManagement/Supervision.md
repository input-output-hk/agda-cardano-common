# Supervision integration workstream

The objective is to connect cancellation and joining to actual CM effects and
the remaining diffusion scopes, then derive completed shutdown from the required
certificates. A completed governor job-pool close alone does not establish full
shutdown.

Source authority remains network pin
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`. This work does not change that pin,
resolve a new dependency version, or promote conditional snapshots into source
reachability witnesses. The detailed source evidence is in
[the pool audit](../review/connection-management-pool-supervision-source-audit-2026-10-27.md)
and [the peer-policy audit](../review/connection-management-a6-source-audit-2026-10-27.md).

## Milestones and completion criteria

Keep these IDs stable when recording progress or changing implementation scope.
The descriptions below are the implementation plan as of 27 October 2026;
validation and commit status must be checked in the current worktree.

| ID | Scope and required result | Current workstream position |
| --- | --- | --- |
| SI1 | Standalone one-owner governor-pool lifecycle: immutable registry snapshot, sequential cancel/wait, queue preservation, and certificates for snapshot Async results. | Committed in `8c79b9a`; checked within the snapshot contract. This is not full shutdown. |
| SI2 | CM caller cancellation and governor adapter: executable source-compatible cancellation effects, explicit bracket/handoff context, asynchronous-exception propagation, and job termination only after the modeled local unwind. | Committed in `8c79b9a`; real cleanup, capture/supply induction, initialized runs and pool-close certificate checked within the stated profile. |
| SI3 | Separate PSA background-thread registry/pool plus provider, churn and governor Async scopes, with their actual ownership and unwinding order. | Committed in `bb11970`. Initialized nonempty close, component certificates and capture/supply preservation pass. |
| SI4 | CM handler/mux lifetime and cleanup, connection-manager scope, and responder Server scopes, including remaining handler sends and joins. | Active: typed FIFO, group/whole-pool unwind, buffer/CM cleanup, partial startup and async callback paths checked within their profiles. SI4-F1 (graceful TraceStopped/IG callback) is corrected in the worktree; remaining failure windows and outer/Server integration remain open. |
| SI5 | Derive `completeShutdown` only from all required scope certificates; remove dependence on an externally asserted whole-supervision completion boundary. | Requires SI2–SI4. |

The current production-policy wrapper's explicit completed-supervision boundary
remains a scoped assumption until SI5. No theorem about a smaller component may
be substituted for those remaining obligations.

## Current executable integration

`GovernorPool` couples the ordinary `Subsystem` and production peer-policy stage
to `JobPoolLifecycle Body`. Successful raw fork/register, body-return, queue and
deregistration transitions drive the pool metadata; independent pool inputs
cannot fabricate a body result. Publication checks the exact job identity,
arguments and outcome, while retry-delay input remains checked by the original
subsystem. Once a body has returned, the adapter permits masked publication and
normal deregistration but refuses a new cancellation delivery in that gap.

`Rules/CallerCancellation` detaches the cancelled caller's acquisition/release
continuation into an explicit unwind frame. It preserves the entire `CM.core`
at detachment; subsequent close/remove/counter steps invoke the real
`OutboundAcquire.step` writer. The adapter blocks only that caller's old CM and
job continuations, retains the historical job, and permits unrelated work.
Cancelled deregistration removes the actual source pool entry without fabricating
a governor completion. Lease ownership and nested-map uniqueness are preserved
by detachment and every caller cleanup step, reusing existing writer theorems.

`Properties/GovernorPool` projects coupled executions into actual executions of
the separate pool component. Its `from-initial` theorem derives observable Async
results for the captured governor-pool snapshot when a finite coupled execution
reaches closedPool. This projection does not erase CM writes into raw subsystem
stutters. The source configuration actually retains their effects.

A failed socket close is significant: the source cleanup exception replaces the
original AsyncCancelled. `recoverCloseFailure` restores the raised close exception
to the awaiting peer job and resumes the ordinary peer-policy path. Depending on
the fixed classifier, it can produce a normal failed completion or attempt fatal
node delivery. Pool recovery from bodyUnwinding is exposed only at this adapter
boundary, not as a way to undo an observed terminal result.

The adapter records protected cleanup regions across counter PCs and splits
handler fork from successful bracket handoff. `deliverOpenCancellation` explicitly
acknowledges an interruptible blocked socket-acquire operation. These source
boundary inputs do not establish complete exception-mask semantics or source
reachability for arbitrary injected snapshots. `Properties/CallerCancellationCapture` retains the detached EntryId certificate,
and `Properties/GovernorPoolSupply` proves a combined invariant over ordinary
runtime captures, all detached cleanup captures, and shared supply bounds.
Deleting a caller slot therefore does not lose the premise needed by later
cleanup writes. The real initializer discharges both capture runtimes; initial
shared entry/promise bounds remain explicit. Existing raw Subsystem theorem
statements have not been changed or silently generalized.

SI3 now supplies the separate actual background-thread registry described below.
It is not `Subsystem.monitors`, which records only followup operations. SI4/SI5
remain open; no full shutdown action is derived or added by this integration.

## SI2 validation checkpoint (27 October 2026)

This SI1/SI2 implementation checkpoint was validated on top of `4f3b159`. These changes are
new implementation work, rather than required review corrections. All checks ran
sequentially with Agda 2.8.0 and `+RTS -M2G -RTS`:

- `Rules/CallerCancellation.agda` and `Properties/CallerCancellation.agda`.
- `GovernorPool.agda` and `Properties/GovernorPool.agda`.
- `Negative/GovernorPool.agda`.
- Amended `Rules/JobPoolLifecycle.agda`, `Properties/JobPoolClose.agda` and
  `Negative/JobPoolLifecycle.agda`.

All exited 0 with Checking output across the incremental checks. The final
GovernorPool projection was rechecked after tightening the owned-caller begin
guard. The final acceptance endpoint checks **118 equations**, including two
initialized close executions: a 21-action pre-resource cancellation retains the
reservation, while a 25-action socket-open/cancel/cleanup/deregister/Async-result/
join run closes the socket, removes the map alias, terminates the captured entry
and publishes no ordinary failed completion. Both instantiate the generic coupled
close certificate. Handoff, release/pruning, close-error recovery, exact normal
outcomes, masking and independent progress controls also pass; the later
injected snapshots remain conditional controls, not source-reachability proofs.

The amended pool primitive adds `resumeAfterUnwindError`, permitted only from
bodyUnwinding. This models a finalizer exception replacing cancellation; the
coupled adapter gates it on a recorded socket-close failure. Existing pool-close
certificate types remain unchanged. The prior 65-equation, three-execution
standalone acceptance endpoint also passes.

Four unchanged regression endpoints passed using cached interfaces:
`Negative/{ProductionPolicy,SubsystemSupply,SubsystemOwnership,SubsystemMapUnique}`.
The local proof audit of eight implementation/proof/acceptance files found zero
holes, postulates or unsafe flags. Whitespace checks passed. Initial elaboration
failures concerned imports, Maybe coverage, projection transports and explicit
impossible-constructor cases; all were resolved without weakening statements or
introducing trust assumptions. Final checks had no warnings. Independent source
and proof reviews found no substantive defect.

No Haskell replay, source-pin migration, dependency-version resolution or
unrelated heavy build was run. The
old Subsystem proofs retain their original scope. The new caller writer has
map-uniqueness and lease-ownership preservation, while `GovernorPool.from-initial`
certifies only its pool's captured Async handles after an actual finite run.

The subsequent capture/supply increment also passed: the induction predicate
is `SubsystemSupply.Valid (machine s)` paired with `All` detached cleaning-frame
capture validity. `from-initial` proves entry/promise bounds after every finite
coupled execution from `GovernorPool.initial (CM.initial c) g`, requiring only
the initial shared supply bounds. Real raw steps retain all pending detached
references; cancellation transfers the capture; cleanup advances it and preserves
both ordinary and detached runtimes. Acceptance applies this theorem while the
original caller slot is already absent and again after each initialized close.

The pool engine is now factored into `JobPoolKernel Result queued` and
`JobPoolCloseKernel`, with the original public modules retaining their queued
specialization. In queue-free mode, body return proceeds directly to normal
deregistration and `publishCompletion` is unavailable. The new
`Negative/WithoutQueuePool` endpoint checks normal and cancelled initialized
executions and applies queue-free close certificates. This is a prerequisite,
not a background-thread registry or SI3 completion claim.

The two new capture/supply modules, queue-mode kernel/certificate, the amended
queued acceptance endpoint, and the queue-free endpoint all passed sequential
Agda checks with Checking output. The final governor acceptance rechecked under
the factored kernel and includes the new capture/supply applications. A final
local audit covers thirteen files with zero findings. Queue-mode matching used
explicit helper functions after Agda rejected matching on a module parameter;
no check was disabled and no theorem weakened.

That SI2 checkpoint was committed as `8c79b9a` before starting SI3 below.
`Subsystem.monitors` cannot stand in for the actual thread registry. SI4 and SI5
remain outstanding, and no completeShutdown derivation is claimed.

## Acquisition cancellation matrix

CM acquisition has no outer `mask` ([Core.hs:1273–1276][acquire-start]); its public
API is a projection ([Types.hs:577–596][api]). JobPool restores the job action,
and the peer-state-actions bracket restores its body, so the ordinary caller
path is unmasked. Nested resource acquisition, fork and cleanup regions have
their own masking rules.

| Acquisition context / modeled PC | Cancellation effect and guard |
| --- | --- |
| `selecting`, before initial STM commits | An interrupted transaction rolls back. Do not fabricate a new reservation. |
| `count (allocatePromise ...)`, `allocatePromise`, before socket acquisition | Reservation insertion already committed, but the socket bracket is not installed. Cancellation can retain `ReservedOutbound`; no CM reservation cleanup is automatically available. |
| `openSocket`, executing bracket resource acquisition | `bracketOnError` masks resource acquisition. Delivery is possible at an interruptible operation, not at every abstract boundary. If acquisition does not return a resource, its release handler does not run. |
| `configureSocket`, `bindSocket`, `connectSocket`, `localAddress`, `updateAddress`, before handler fork | These belong to the restored bracket body. Cancellation invokes its error cleanup: close the socket first, then delete this captured entry's aliases and write `Terminated Nothing`. |
| Handler exists, but bracket body has not returned | Still inside the parent's error bracket. Parent cleanup may run while the handler also exists. This needs a separate explicit pre-handoff boundary. |
| `connectedCommit`, `count (awaitResult ...)`, `awaitResult` | Successful bracket return has transferred cleanup ownership to the handler. Caller cancellation abandons the call; it does not automatically cancel or join that handler. |
| `commitResult`, before/after handshake transaction | Cancellation of a blocked transaction rolls back its state writes and IG enqueue together. Already committed changes remain. There is no socket-bracket rollback after handoff. |
| `waitingInbound` | Abandon the captured inbound wait; do not clean up the borrowed inbound connection. |
| Error cleanup `closeError`, `removeError`, its counter trace | Cleanup is uninterruptible. Reject a second cancellation delivery in this region. Close failure prevents subsequent map cleanup and may replace the original exception. |

The initial reservation is inserted at [Core.hs:1399–1431][reservation]. The
socket bracket, cleanup and restored body are at
[1451–1535][socket-bracket]. The handler fork and successful body return are
separate source boundaries at [1531–1537][handoff]. Connected commit and promise
wait are at [1537–1584][await-result]; the handshake write and optional bounded IG
enqueue share STM at [1600–1664][handshake]. The borrowed inbound wait is at
[1666–1755][inbound-wait].

A model that jumps directly from `forkHandler` to `connectedCommit` omits the
forked-but-pre-handoff cancellation window. Fork itself uses `mask_`
([Core.hs:579–592][handler-fork]); that does not mask the whole surrounding
acquisition body or the later connected commit.

`count` wrappers cannot determine cancellation permission from their shape or
final fault alone. Preserve the inherited region. The cleanup's counter trace
at [1469][socket-bracket] is uninterruptible; ordinary acquisition traces at
1423, 1582, 1661 and 1754 inherit the caller context. In particular, a cleanup
`count (complete (raised ...))` must not be mistaken for an ordinary cancellable
return with the same result constructor.

The concrete socket implementation documents a blocking IO-manager association
inside opening ([Snocket.hs:394–407][socket-open]). Its lower-level exception
handling is not a general proof that every possible opening failure closes every
OS resource. Keep acquisition failure and returned-resource cleanup distinct.

## Exception propagation through the caller

Peer-state actions catch acquisition with `try` as `SomeException`, including
asynchronous exceptions ([PeerStateActions.hs:784–801][psa-catch]). Under the
pinned base policy an ordinary cancellation selects `ShutdownPeer` and is
re-thrown as the same asynchronous exception. The peer-state bracket restores
`PeerCold`. The outer JobPool handler excludes `SomeAsyncException`
([JobPool.hs:147–164][job-exceptions]), so this path must not manufacture an
ordinary failed governor completion.

Keep cancellation distinct from the coarse abstract `ioFailure ErrorId` used by
normal policy examples. Do not allow an opaque classifier to turn a known
cancellation exception into a production IO-manager fatal error. Custom open
policies remain a separate profile.

## Release cancellation matrix

Outbound release has no outer mask or rollback handler
([Core.hs:1840–1844][release-start]); its PSA caller also has no enclosing mask
or release-on-cancel bracket ([PeerStateActions.hs:1050–1105][psa-close]).

| Release context / modeled PC | Cancellation effect |
| --- | --- |
| `transaction`, before STM commit | Roll back the transaction. |
| After demotion commit: `count`, `armTimer`, `waitIdle` | Abandon the timer wait with committed `OutboundIdle` retained. Do not invent handler cancellation or state rollback. |
| `timeoutWrite`, before its STM commit | Preserve the prior state; after commit, preserve `Terminating`. |
| `count (cancel ...)`, `cancel`, `delivering` | Cancellation may interrupt the sender before or while sending. Delivery acknowledgment is not handler termination. Already delivered target effects remain possible. |
| `prune` | All selected victim writes committed before the sequential send phase. Cancellation can leave a pending send tail; do not undo writes or acknowledge undelivered sends. |

Demotion, timer registration, ordered STM wakeup and handler send are at
[Core.hs:1875–2034][release-wait]. Release intentionally uses `throwTo` without
waiting for handler time-wait completion. Pruning atomically writes victim states
then performs later sequential sends ([Core.hs:762–777][prune]); release runs
that action at [2042–2046][release-prune].

## Remaining supervision boundaries

Handler `finally` cleanup is independent of caller cancellation. Its map/socket
work is uninterruptible; its time-wait delay explicitly unmasks, with a final
state/map update even if interrupted ([Core.hs:595–710][handler-cleanup]). A
caller-pool join is therefore not a handler-cleanup certificate.

The governor WithQueue pool and PSA WithoutQueue background-monitor pool are
separate. Diffusion nests PSA, providers, governor Async, then churn Async. Scope
unwinding cancels/waits churn before governor, then unwinds provider scopes and
PSA, while other threads may continue concurrently
([Diffusion.hs:767–826][diffusion-scopes]). Server adds independent action,
inbound-governor and accept-loop scopes ([Server.hs:147–175][server]). SI3 and
SI4 must account for these before SI5 derives full completion.

This checkpoint records source evidence and implementation obligations. It makes
no new validation, source-refinement, cleanup-liveness or full-shutdown claim.

[acquire-start]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1273-L1276
[api]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Types.hs#L577-L596
[reservation]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1399-L1431
[socket-bracket]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1451-L1535
[handoff]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1531-L1537
[await-result]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1537-L1584
[handshake]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1600-L1664
[inbound-wait]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1666-L1755
[handler-fork]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L579-L592
[socket-open]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/Snocket.hs#L394-L407
[psa-catch]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerStateActions.hs#L784-L801
[job-exceptions]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/network-mux/src/Control/Concurrent/JobPool.hs#L147-L164
[release-start]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1840-L1844
[psa-close]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerStateActions.hs#L1050-L1105
[release-wait]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1875-L2034
[prune]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L762-L777
[release-prune]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L2042-L2046
[handler-cleanup]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L595-L710
[diffusion-scopes]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/Diffusion.hs#L767-L826
[server]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/Server.hs#L147-L175


## SI3 source-derived integration checklist

This source-verified checklist guided the SI3 implementation and remains the
source-to-model scope contract. The executable implementation and validation
checkpoint follow it; the remaining CM/handler/server scopes are SI4.

- Split background creation, registration and successful establishment return.
  [PSA:836–852][si3-spawn] calls `JobPool.forkJob` before returning the peer
  handle. [JobPool:122–145][si3-register] masks each spawning parent across fork
  and registry insertion; the child can act before insertion, but deregistration
  waits for its entry. Do not interpret atomic `J.launchMonitor`/job completion
  as all three boundaries. Keep the pre-registration mask and the subsequent
  in-bracket establishment-return window explicit: cancellation after
  registration but before successful establishment return restores `PeerCold`
  while the already spawned monitor remains independently owned.
- Model multiple spawning parents. The PSA pool is shared by concurrent
  establishment jobs, unlike the governor's single spawning loop. Each parent
  has its own masked fork/registration gap. A single `parentFork : Maybe ...`
  kernel must not be presented as preserving all concurrent parent gaps. Use
  multiple-parent tracking, or an explicit source-adapter certificate with a
  clearly limited serialization/coverage claim. Queue-free operation alone does
  not solve this ownership issue.
- Keep a physical background-thread registry with a captured peer reference and
  fresh thread identity. `Sub.monitors` contains only a temporary followup
  operation; its absence is not physical thread termination. `monitorStarted`
  is not registry or join evidence. Bind each `pollPeer`/followup caller to its
  captured physical worker, so a detached, cancelled or completed thread cannot
  resume through an independently supplied caller ID.
- Distinguish monitor outcomes. Normal waiting observes `PeerCold` directly or
  waits for CM demotion and atomically writes `PeerCold`
  ([PSA:673–695][si3-wait]); normal exit traces hot duration, clearing its saved
  promotion time ([PSA:651–660][si3-duration], [773–775][si3-loop]). Protocol-error
  result branches update cooling and recurse; they do not by themselves throw
  an ordinary exception. Clean hot results invoke deactivation and recurse;
  clean warm/established results invoke close and recurse
  ([PSA:709–767][si3-loop]).
- Represent the synchronous-error handler separately. It waits for outbound
  demotion, writes `PeerCold`, traces hot duration/error, then rethrows; the
  outer Job handler returns `Just exception`. The inner handler explicitly
  excludes asynchronous exceptions ([PSA:836–849][si3-spawn]). Cancellation can
  interrupt its demotion wait: do not write cold unless that transaction has
  committed. The ordinary error identity must remain captured if a conditional
  source-projection claim depends on it.
- On asynchronous cancellation, retain already committed controls, status,
  partial starts, promotion time and CM release effects. There is no monitor
  cancellation finalizer that forces `PeerCold` or runs the ordinary error
  handler. If an active followup owns a CM release, detach/unwind that captured
  caller and retain its pending send tail. Then distinguish local unwind,
  deregistration and Async result availability. Do not fabricate a governor
  completion or any WithoutQueue result publication.
- Begin outer PSA pool close only after governor Async completion/join and the
  intervening provider scope joins. A governor-pool `closedPool` certificate is
  a prerequisite inside governor unwinding, not the governor Async result.
  Diffusion nesting requires churn, governor, local-root provider, ledger-peer
  provider, then PSA pool scope exit
  ([Diffusion:767–826][si3-order],
  [PeerSelectionActions:84–102][si3-providers]). Other monitor and handler
  activity can continue during these waits. SI4 handler/CM/server certificates
  and SI5 derived shutdown remain separate obligations.

[si3-spawn]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerStateActions.hs#L836-L852
[si3-register]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/network-mux/src/Control/Concurrent/JobPool.hs#L122-L145
[si3-wait]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerStateActions.hs#L673-L695
[si3-duration]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerStateActions.hs#L651-L660
[si3-loop]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerStateActions.hs#L709-L775
[si3-order]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/Diffusion.hs#L767-L826
[si3-providers]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerSelectionActions.hs#L84-L102


## SI3 executable integration and validation (27 October 2026)

Commit `8c79b9a` contains SI1/SI2. This SI3 checkpoint was validated on top of it.
`PeerSupervision` now owns a physical monitor-thread registry, a separate
WithoutQueue pool, and the outer Async scope coordinator. It routes followups
through each captured worker and refuses untracked launch, caller substitution,
or resumption after cancellation. It refines the original atomic launch into
fork, parent registration, PSA return and governor-job return. A spawning parent's
own masked gap blocks its cancellation delivery while other parents/children
continue. Cancellation after insertion but before PSA return restores Cold;
after successful PSA return it preserves the peer, independently of job return.

`JobPoolKernel` admits concurrent fork/register only in queue-free mode and
requires every outstanding insertion to settle before the outer snapshot. The
queued governor specialization keeps its previous single-owner behavior.
Historical removed children are not re-registered or mistaken for live gaps.
A child can return before its own insertion, but cannot deregister before it.

Normal monitor exit and its duration-variable clear are distinct from a followup
operation finishing. An active followup must complete before the physical loop
exits. Ordinary thrown errors enter a captured demotion wait and write Cold only
when that wait commits; exit tracing then clears promotion time. Asynchronous
cancellation bypasses that handler, retains committed peer/control/release effects
and promotion time, and produces no governor completion. Blocking interruptibility
in a masked error handler is an explicit observation. `monitorException` is an
observed synchronous throw, not a proof that every supplied error is reachable.

`Rules/AsyncScope` models churn, governor, local-root provider and ledger-peer
provider. Its join cursor follows that nesting order, while independent thread
completion can occur earlier. Governor pool close requires delivered cancellation
or an explicit independent exception-entry observation. Governor Async body exit
requires its own pool closed; the outer monitor snapshot requires the Async scope
joins completed. Thread local-body exit remains an explicit component boundary;
provider/churn internals and startup before those scopes are entered are outside
this ordinary-profile coordinator. No eventuality or full Haskell refinement is
claimed. The four scope statuses are stored as finite fields, avoiding nested
callback histories while preserving the getter/snapshot-builder interfaces.

`Properties/PeerSupervision` projects every coupled step and finite execution to
three actual operational traces: the governor pool, physical monitor pool and
Async scope coordinator. From the real initializer and the three observed closed
states, its certificate gives terminal Async results for both captured snapshots
and all four scope joins. Real CM/peer writes remain in the source execution;
only the separate metadata components are projected. `PeerSupervisionSupply`
preserves ordinary and detached captures plus shared entry/promise bounds across
all coupled actions/interleavings, requiring only initial shared bounds.

Validation used Agda 2.8.0 and `+RTS -M2G -RTS`, one process at a time. The new
rules, component/capture-supply proofs and all acceptance layers passed. The
maintained endpoint is `Negative/PeerSupervision.agda`, which publicly reexports
three checked layers: `PeerSupervisionScenarios`, `PeerSupervisionGovernorClose`
and `PeerSupervisionClosing`. They retain **144 named reflexivity equations**,
an initialized 44-action monitor spawn, a 26-action empty-scope close and an
initialized **81-action nonempty close**. The latter actually queues the normal
governor result while the owner is unwinding, joins that job, joins the provider
scopes, and cancels/deregisters/joins the captured monitor. It instantiates both
pool/scope certificates and the capture/supply theorem. A concrete handler remains
present afterward, an explicit control against calling this full shutdown.
`Negative/ConcurrentPool` adds 17 equations and an initialized seven-action
registration-race execution. Conditional snapshot controls remain distinguished
from initialized model executions and from implementation reachability.

The initial monolithic acceptance check exhausted its 2 GB heap. Explicit
component snapshots, finite scope fields, and separate checked scenario/governor/
closing proof layers resolved it without increasing the heap limit, deleting
cases, changing theorem statements or adding axioms. Earlier elaboration fixes
covered inaccessible private module aliases, constructor names and store order.
Final checks produced no warnings. Logs are under
`/tmp/cm-review-20261027/si3-*.log`; generic component proof logs are also under
`a6-checks/` at that location. The queued-pool compatibility check passed with
Checking output. Final regression checks of `Negative/WithoutQueuePool` rechecked;
`Negative/{GovernorPool,SubsystemSupply,SubsystemOwnership,SubsystemMapUnique}`
passed with cached interfaces. The twelve-file local proof audit found zero
findings. Whitespace checks passed. No replay, upstream source/spec edit,
dependency upgrade or unrelated heavy proof build was run.

Next is SI4: audit and connect actual handler creation and post-handshake mux
job ownership, callback/pool/buffer unwind, CM finalizers and responder-server
scope joins. Existing `HandlerLifecycle.jobPoolClosed` and other local completion
inputs must not be promoted to a whole-scope certificate without their own
captured job/cleanup evidence. The initialized remaining handler is the concrete
starting fixture. SI5 will consume the resulting certificates; no full shutdown
transition has been derived here.


## SI4 first increment: CM scope traversal

SI3 is committed as `bb11970`. The first SI4 increment adds
`Rules/CMShutdown`, `Properties/CMShutdown` and `Negative/CMShutdown`.
The [source audit](../review/connection-management-si4-source-audit-2026-10-27.md)
records why the CM algorithm differs from JobPool close and why Server listener
joins cannot establish admission quiescence.

The coordinator snapshots current map entry references once, reads their heap
cells later, sends cancellations with separate delivery acknowledgments, then
waits collectively for the collected Async results. Repeated references are
preserved. Store enumeration abstracts source Map key order; no ordering
refinement is claimed. Arbitrary shared-store and result-observation inputs may
interleave with coordinator steps, without a fictitious global closed flag.
`closed-from-initial` certifies an exhausted traversal and a witness of the actual
successful final wait, with the exact observation oracle used at that boundary.
It does not assume future oracle values or certify uncollected handlers.

Physical Async-result observations remain explicit adapter obligations. They
must ultimately follow actual mux-pool, buffer, CM finalizer and result-publication
steps; neither delivery acknowledgment nor a historical handler capture suffices.
This increment does not connect those physical lifetimes or derive full shutdown.
The source audit describes the remaining mux startup/generation/group-cancel and
Server/IG scope obligations. SI4 and SI5 remain open.


Validation on 27 October 2026: all three new Agda modules passed with fresh
Checking output, Agda 2.8.0, `+RTS -M2G -RTS`, sequentially and without warnings.
Acceptance contains 32 named reflexivity controls, a nine-action bulk traversal,
the generic final-wait certificate application, and a ten-action product
execution: empty CM capture/traverse/close followed by the seven real inbound
admission actions from `CSP.Fixtures.start` to `waiting`. A handler and its owned
socket then exist while the coordinator remains closed with an empty snapshot.
The fixture starts after accepted-child handoff; this is not a derivation of the
full Server prefix or a Haskell replay. Other controls cover delayed entry reads,
Terminated skipping, duplicate references, missing historical handlers,
map-lock blocking and refusal to finish with only some results available.

The acceptance check initially reported two implicit inference metas in its
path-lifting helper; explicit source/target/action arguments resolved them.
The final three-file local proof audit found zero holes, postulates or unsafe
flags; whitespace passed. Existing theorem files were not modified. No broad
unrelated proof rebuild, source change or replay was run. Logs are
`/tmp/cm-review-20261027/si4-cmshutdown-{rules,negative}.log` and
`/tmp/si4-cmshutdown-properties.log`. This CM traversal increment is committed
as `2c39700`.

Next executable obligation: track physical handler identity from the real fork
and bind pre-handshake cancellation, promise catch regions and CM finalizer
completion to Async result publication. Then build the physical mux startup and
per-direction/per-generation job pool, with its separate interruptible group
close and buffer boundary, before supplying post-handshake observations to the
CM coordinator. Server listener/action/IG ordering and admission quiescence must
remain explicit before SI5 consumes a whole-scope certificate.


## SI4 second increment: pre-handshake handler completion

`HandlerSupervision` is a bounded inbound pre-handshake adapter over the actual
`Machine` dispatcher and `CMShutdown` coordinator. It initializes only without
pre-existing handlers/cleanups/lifecycle frames/publication faults and captures
the physical child's original `HandlerStart` at the successful admission fork.
No later key lookup changes that child's captured entry, socket or promise.
The historical handler heap is not adopted as an active Async registry.

Setup return and blocked-setup interruptibility are explicit local observations.
Ordinary async delivery is allowed in the unmasked handshake; its catch must
publish the real `handlerError protocolViolation` promise, rethrow, then enter
the actual CM finalizer. Observed blocked cancellation in masked setup bypasses
that promise because setup is outside the catch. This first profile supplies no
successful-handshake/mux completion shortcut.

All finalizer transitions invoke existing cleanup writers. Completion retains
both the original cancellation error and actual cleanup outcome. A close error
replaces the effective exception and can leave socket-close uncertainty.
`cleanupDone`, finalizer return and Async result publication are separate
boundaries. The last publication checks the real cleanup outcome again. The CM
coordinator receives only the registry's `resultReady`; callers cannot inject an
oracle or acknowledge a cancellation without coupled delivery/finished-target
evidence. During TIME_WAIT a coupled delivery invokes the real interruption
step, whose termination/purge continuation still must run before result return.

Raw handler publication/exit/lifecycle/cleanup and release/pruning cancellation
acknowledgments are refused by this adapter. Ordinary independent source actions
retain the original guards. Delivery coupling for release/pruning senders, outer
peer supervision, outbound physical fork, normal/synchronous handler outcomes,
mux jobs and Server scopes remain later integration work. No global closed flag
freezes later admissions; a closed snapshot is not whole-node shutdown.


`Properties/HandlerSupervision` projects every successful wrapper step and every
finite interleaving into actual `Machine.Executes` and `CMShutdown.Executes`
paths. Its `closed-from-initial` certificate retains a drained traversal and a
`PhysicalWait` with the actual wrapper finish transition and its registry-derived
oracle. The checkpoint remains meaningful after independent source actions;
it does not assert the same oracle at every later state. Existing Machine supply,
map-uniqueness and lease-ownership theorems lift through the projected real source
execution, with their original initial premises and no new runtime validity gate.

Integration must eventually start at the real outer initializer so all physical
forks are tracked. The SI3 endpoint's retained post-handshake handler cannot simply
be adopted into this empty-registry initializer. Outbound birth and successful
handshake/mux startup must be coupled before replaying that entire outer history.


Validation on 27 October 2026: `HandlerSupervision.agda`,
`Properties/HandlerSupervision.agda` and `Negative/HandlerSupervision.agda` all
passed with fresh Checking output, sequentially in Agda 2.8.0 with
`+RTS -M2G -RTS`, without warnings. The final acceptance check includes the
initialized 24-action fork/cancel/promise/finalizer/result/CM-close execution,
73 named reflexivity controls, and the initialized ten-action empty-close then
late-admission execution. It instantiates the generic physical-wait certificate,
actual Machine trace projection, supply preservation and both successful and
failed-cleanup result-publication checkpoints. The latter checkpoints retain the
original captured thread and the real cleanupDone observation at publication.
The generic map and lease-ownership corollaries preserve their explicit initial
premises; no whole-state validity is assumed by execution guards.

Controls additionally cover masked setup without a promise, refusal of raw
handler and cancellation-acknowledgment bypasses, wrong workers, failed socket
close/map restoration/exception replacement, and a child finalizer blocked by
its parent's outstanding map lease. A two-action consumer suffix from the
reachable caught publication checks protocolViolation's actual Terminated/purge
effect. TIME_WAIT interruption controls are conditional snapshots, not initialized
source reachability witnesses. The source exports and exception classifier were
checked at the existing network pin; no pin change or Haskell replay was run.

Initial checker failures were nested-with clause association, a fixture argument
name collision, and implicit inference of trace inputs erased by reduction.
Explicit clauses/arguments resolved them without modifying existing semantics,
weakening theorem statements, raising the heap limit or adding trust assumptions.
The final three-file proof audit had zero findings; whitespace checks passed.
Logs: `/tmp/cm-review-20261027/si4-handler-{rules,properties,negative-final}.log`.
No unrelated proof rebuild was run. This second SI4 increment is uncommitted.

Next is outbound physical birth and successful-handshake/mux ownership, including
fresh directional run identities, real pool startup, the separate interruptible
mini-protocol group close, final pool joins and buffer release. Couple these from
the true outer initializer, retaining the earlier peer supervision proofs and
late-admission behavior. Release/pruning sender acknowledgments and Server/IG
scope completion still need integration before SI5 can derive full shutdown.


## SI4 third increment: outbound physical birth and mux-startup prerequisite

`OutboundHandlerSupervision` extends the pre-handshake physical registry across
actual outbound acquisition/release and inbound interleavings. `O.core` is the
only stored dispatcher configuration; the inherited handler state is a view,
so handler writes replace that core without losing pending callers, operation
results or the random-generation field. Outbound `forkOK` captures the actual
new HandlerStart immediately, before `commitConnected`. Physical child freshness
also excludes active admission/outbound caller identifiers and retained physical
history. This is a symbolic worker-identity profile, not an implementation
ThreadId ordering theorem.

Raw `O.inbound` cannot bypass handler gates; raw outbound release delivery is
also refused until a coupled delivery adapter exists. The real source operation
still has its original guard for every enabled step. The initializer refuses
existing handler captures while retaining any supplied caller runtime; arbitrary
such runtimes require the existing capture/supply premises. The ordinary
`O.initial` corollaries derive empty-runtime capture validity and require only
the shared world's initial allocation bounds.

`Properties/OutboundHandlerSupervision` projects every step and finite execution
to actual `OutboundMachine.Executes` and `CMShutdown.Executes`. New outbound
writers remain real source steps, rather than stutters justified by an old
inbound invariant. Its capture and combined runtime/supply corollaries reuse the
actual outbound proof endpoints. The closed certificate retains the exhausted
snapshot and inherited physical wait at the actual handler-view boundary, with
no claim about all historical or later handlers.

The standalone `Rules/MuxStartup Result` is the next prerequisite, with a generic
result type so mux infrastructure and later mini-protocol actors can share one
WithQueue pool. It separates observed success publication, buffer acquisition,
bearer construction, run/Starting/egress/pool setup, each infrastructure fork and
registry insertion, Mature and monitor entry. Its startup phases retain the
muxer/demuxer physical identities; child completion can run between parent steps.
Neither `MuxRuntime.ready` nor an existing pool snapshot initializes ownership.

Success publication remains an explicit observed boundary in this component:
no theorem yet couples it to a successful handler promise in the physical
outbound adapter. It supplies no buffer-release, shutdown, group-cancel or join
action, and no successful/mux handler result can be published through the bounded
pre-handshake adapter. The next integration must couple that boundary and actual
startup to each captured handler before deriving post-handshake completion.


Validation on 27 October 2026: all six new modules passed with Agda 2.8.0,
`+RTS -M2G -RTS`, one process at a time, without final warnings. The outbound
adapter, its property endpoint and its acceptance endpoint had fresh Checking
output. MuxStartup rules checked transitively during the first property check;
the subsequent explicit rule command passed using that cached interface. Final
MuxStartup property and acceptance commands had fresh Checking output. The first
transitive rule output remains in the tool transcript rather than a preserved
log; the explicit rule log is empty because that check was cached.

Outbound acceptance has 54 named reflexivity controls, an initialized 28-action
acquisition/child-before-Connected/cancellation/cleanup/result/CM-close execution,
and applications of the actual source/coordinator projections, physical-wait,
capture and combined runtime/supply certificates. Initialized inbound/outbound
interleavings preserve pending callers, and empty-close/later-admission still
captures new physical children. An initialized 14-action local run closes a CM
snapshot that skipped the ReservedOutbound entry while the already forked child
remains alive. This does not derive the full diffusion prefix: outer caller joins
and scoped API use still need integration before claiming a source shutdown race.

Mux-startup acceptance includes 15 named reflexivity controls, a 13-action
initialized startup, actual same-pool fork/register projections, distinct physical
capture certificates, refusal of out-of-order/reused identities and early monitor
entry, plus a fast-child interleaving. The child returns and publishes to the
queue before insertion, cannot deregister early, then inserts/deregisters and
publishes its Async result before the demuxer fork. A final initialized run still
reaches monitor entry with that first child already unregistered; the historical
capture certificate and actual pool trace both apply. These remain standalone
component executions with observed body/publication boundaries, not successful
handler-source refinement or completed mux shutdown.

Proof-checker repairs concerned names colliding with existing constructors,
implicit argument inference, with-abstraction equality transport and an explicit
All constructor for initial bounds. All were resolved in the new files without
modifying the old rules or weakening statements. The final six-file local proof
audit found zero holes, postulates or unsafe flags; whitespace passed. Source
exports for Core, ConnectionHandler, Mux and JobPool were compared again against
the pinned Git objects. No replay, pin change or unrelated proof rebuild was run.
Logs: `/tmp/cm-review-20261027/si4-outbound-handler-{rules,properties,negative}.log`
and `si4-mux-startup-{rules,properties,negative}.log` in the same directory.
All work after `2c39700`, including the prior pre-handshake increment, remains
uncommitted. The pre-existing `.claude` symlink is untouched.

Next executable action: couple successful handshake/handle allocation and actual
promise publication to each captured handler's mux-startup instance, including
the masked post-handshake/buffer/bearer interval. Do not leave the old handshaking
cancellation path enabled after success or infer physical startup from M.ready.
Then add fresh directional/generation mini-protocol ownership in the same pool,
exact result publication, separate interruptible group cancellation, final pool
joins and buffer release before enabling post-handshake CM finalization. Reconnect
the outer peer-supervision history from its true initializer and finish Server/IG
scopes with admission quiescence explicit. SI4/SI5 and full shutdown remain open.


## SI4 fourth increment: successful handler to mux-startup coupling

`MuxHandlerSupervision Result` is an additive wrapper over
OutboundHandlerSupervision. It retains one shared outbound source, records
inbound/outbound birth provenance only at successful real fork transitions, and
keeps a separate startup frame for each observed successful handler. Its
initializer rejects pre-existing physical handlers and pre-existing IG
handles/muxes rather than adopting their ownership.

`negotiate` is the explicit restored-handshake-success observation. It captures
the registered handler's original references, protocol bundle and flow, and
immediately disables that handler's old handshaking/cancellation/body/cleanup/
result paths. Birth provenance selects actual `installHandle` for inbound or
mode/flow-sensitive `installOutboundHandle` for outbound, using the captured key;
mutable CM entry provenance is never consulted for this decision.

`publishSuccess` invokes the real `OutboundMachine.inbound` handler-publication
writer and the selected `MuxStartup.observePublication` in the same transition.
Handle allocation alone does not publish a promise. After publication, independent
callers may consume the result and enqueue requests while the buffer, bearer and
physical infrastructure startup remain pending. Each handler then advances its
own startup instance through the same queued-pool fork/register transitions.
Infrastructure JobIds must be fresh across all captured mux pool histories,
including deregistered children; the per-pool certificate alone is not described
as a proof of global uniqueness.

Raw handle installation and independent publication observations are blocked.
Inherited old handler and CM-delivery actions cannot bypass a captured success
frame. Monitor/tracer/job actions for its allocated mux are also parked until a
physical protocol/monitor adapter extends this startup prefix; ordinary command
enqueue and unrelated actors retain their original guards. There is no successful
body-exit, pool-close, buffer-release, CM-finalizer or Async-result shortcut.
Masked setup failures, blocking interruption and startup unwind remain future
branches, not a theorem that those interruptions cannot happen.


`Properties/MuxHandlerSupervision` projects every step and finite execution to
actual OutboundMachine and CMShutdown executions, retaining the physical final
wait, and to a separate startup execution for every selected handler. Its
initialized monitoring certificate gives that handler's distinct captured
infrastructure identities and actual same-pool history. The source projection
lifts existing capture/runtime-supply theorems with their original premises;
new allocation and publication writes are not erased into old-wrapper stutters.
A local `Publication` witness retains the actual source promise write and matching
startup observation. `startup-parent-registry` proves every startup-only step
leaves the physical parent handler table unchanged; a child Async result does
not fabricate the parent handler's result.

Validation on 27 October 2026: the new model, property and acceptance modules all
passed with fresh Checking output, sequentially at Agda 2.8.0 with
`+RTS -M2G -RTS`, without final warnings. The maintained endpoint is
`Negative/MuxHandlerSupervision.agda`. It contains 104 named reflexivity controls,
an initialized 27-action outbound fork/success/publication/monitor-entry run,
actual inbound second-handler birth and independent per-handler startup histories,
and an actual CM-consumer/IG request-enqueue suffix before buffer/job startup.
Generic source/coordinator/selected-handler projections, monitoring/pool-history,
publication, capture/supply and parent-registry certificates are instantiated.
A three-action initialized empty CM close also instantiates the inherited
physical-wait certificate; it does not assert future quiescence.

Controls cover publication before buffer/physical jobs, refusal of independent
publication observation and raw install/cleanup/exit/cancellation bypasses,
mode/flow-sensitive outbound tracer selection versus inbound tracer selection,
foreign-pool body results, globally fresh captured mux-job identities even after
deregistration, and another pool forking during the first parent's insertion gap.
The birth-policy control with an overwritten mutable CM entry is a conditional
snapshot; the real initialized paths are labeled separately. Negotiation return,
local buffer/bearer/setup boundaries and child body outcomes remain explicit
component observations, not implementation refinement or eventuality claims.

Checker repairs concerned local names colliding with existing constructors;
there was no old-rule change, theorem weakening, heap increase or new trust
assumption. Final three-file local proof audit: zero findings. Tracked diffs and
new-file whitespace checks passed. ConnectionHandler, Mux and JobPool exports
were compared again with the pinned Git objects. No Haskell replay, source-pin
migration, unrelated proof build or commit was performed. Logs are
`/tmp/cm-review-20261027/si4-mux-handler-{rules,properties,negative,negative-final}.log`.
All work after `2c39700` remains uncommitted; `.claude` remains untouched.

Next executable obligation: extend each captured startup's SAME physical pool
with directional/generation mini-protocol jobs and an exact result sum that can
also represent muxer/demuxer outcomes. Bind protocol fork/start, body result,
queue publication and deregistration to actual source operations without using
legacy runningJobs/finishedJobs cells as physical identities. Then permit mux
monitor processing through that adapter, including interruptible MiniProtocolJob
group cancellation, final pool close/joins, async-vs-normal tracer ordering and
buffer release before CM finalizer entry. Masked setup/startup failure and
interruption branches need their real unwind, too. Preserve independent actors,
per-parent insertion masks and late admissions while integrating outer scopes.
SI4/SI5 and full shutdown remain open.


## SI4 fifth increment: physical protocol generations in the same pools

`MuxProtocolJobs` instantiates the existing handler/startup wrapper with
`MuxJobTypes.TypedResult`: muxer and demuxer outcomes plus protocol direction,
number, generation and outcome. Protocol forks extend each captured frame's
existing `Startup.pool` through real JobPoolKernel transitions. They do not
initialize a second pool or reconstruct physical threads from running flags.
Captured protocol metadata binds JobId to owner handler, mux, direction, number
and fresh generation. Clean slot completion permits a new generation; error
completion leaves that slot busy, even after publication/deregistration.

Responder creation requires the actual selected forkPending callback and couples
`IG.forkResponder` with the physical Pool.fork. Parent insertion is a separate
step. Initiator creation is an explicit observed source miniProtocolJob fork:
known configured number, readiness, slot and pending-work guards are checked,
but the legacy PeerActions running flag is not used as evidence. Initiator
command selection, directional capability and peer result-action integration are
still boundary contracts rather than proven frontend histories.

`protocolReturned` records return from the protocol action; `commitClean` is the
explicit Wanton-drained readiness observation and actual responder completion/
status commit. The egress byte queue itself is not modeled by that observation.
Synchronous errors bypass the wait and preserve non-Idle status. Local completion
commit leaves the physical bodyRunning. `returnProtocol` separately records the
JobResult return to JobPool, and only then can `publishProtocol` queue its exact
typed result. Deregistration and Async result publication remain separate. This
exposes the post-completion unmasked body window for future cancellation; it does
not assume every committed completion will eventually be queued.

New `IG.publishJobOccurrence mid index` removes one exact finished occurrence.
The old number-based action remains unchanged for old profiles. The adapter
tracks responder pending JobIds in append order, locates the selected physical
job, checks its source number/outcome and typed direction/generation/outcome,
then couples source occurrence publication with that job's Pool publication.
A newer run can therefore publish before an older preempted run of the same
number. Initiator outcomes publish to the authoritative physical pool and local
completion metadata; they do not fabricate a PeerActions or OutboundMachine
initiator writer. The legacy mux completion list is only the responder projection
here, not the complete shared queue.

Infrastructure results also use the same typed pool, including inside their
parent insertion gaps. Arbitrary inherited child-result input and raw monitor/job
bypasses are blocked. Typed controls allow command selection, on-demand start and
tracer continuation only after physical startup, respecting the selected owner's
parent insertion gap and physical result priority. A previously selected start
may finish tracing/forking after a result arrives. There is no result-consumption,
group-cancel, cancellation/unwind, pool-join or handler-finalization shortcut.

`Properties/MuxProtocolJobs` projects every successful step and finite execution
to actual OutboundMachine executions and actual selected-handler Pool executions.
New protocol forks cannot be projected through the older startup-only grammar;
the proof uses JobPoolKernel directly. The selected pool starts empty at the real
initializer. Existing pending-capture and combined runtime/supply facts lift
through the actual source trace with their original premises.


Local checked observations additionally retain the physical fork metadata/source
callback (or explicit initiator-fork contract), completion commit and unchanged
pool/bodyRunning window, actual body return, exact typed publication, and selected
responder ordinal/source occurrence. They are instantiated in the acceptance
endpoint together with source/pool execution and capture/supply certificates.

Validation on 28 October 2026 used Agda 2.8.0 and `+RTS -M2G -RTS`, sequentially,
with no final warnings. The two new runtime/type modules, final property endpoint,
new occurrence controls and final protocol-job acceptance all had fresh Checking
output. The modified old proof statements were retained and checked through
Properties/{HandlerIG,IGRetention,OriginMonitorInvariant}; existing
Negative/TracerAttachment also passed. It initially failed only because the
sandbox could not refresh an external csp-ptree interface; an explicitly escalated
retry succeeded without dependency source edits.

The new Negative/MuxProtocolJobs endpoint contains 142 named reflexivity controls.
Its initialized 38-action physical birth/publication/caller/IG-queue/startup prefix
feeds a 13-action fast responder run that commits, returns and queues before
parent insertion, then inserts/deregisters/publishes its Async result. Other
initialized model executions cover same-number opposite directions, a clean
initiator restart before the older body return with newer error publication first,
mixed infrastructure/protocol outcomes, early infrastructure publication before
insertion and completion of an already selected start after a result arrives.
The responder same-number ordinal-overtaking suffix uses an explicitly
conditional frontend request after a genuine older clean commit; it is not an
initialized ordinary-IG restart witness. Source IG normally restarts from the mux
completion trace. Five separate ProtocolJobOccurrence controls check indexed
publication, retained older data, legacy compatibility and refusal cases.

The first acceptance import closure exhausted 2 GB in CSP/InboundRelease before
reaching the new scenarios. New data-only Negative/MuxProtocolFixtures removed
the heavy CSP/old-negative dependency while preserving actual initialized steps
and all intended controls; no heap increase or case deletion was used. The older
CSP/InboundRelease endpoint was subsequently checked **in isolation**, freshly at
the same 2 GB limit, and passed. Final test imports therefore remain cheap rather
than relying on that whole expensive closure. Compiler repairs were local names,
nested-with scope and equality transport, not weakened statements or disabled
checks. The source audit also prompted the clean commit/body-return split before
final checking, preserving the future cancellation window.

The final thirteen-file local proof audit found three heuristic question-mark
hits, all inspected pre-existing natural-number decision operators in
IGRegistration (two ≤? and one <?), and no actual holes or unsafe additions.
Tracked and all six new files' whitespace checks passed. Mux/JobPool exports were
compared against the unchanged pin. No Haskell replay, source-pin migration or
commit was performed. Logs are under `/tmp/cm-review-20261028/`:
`protocol-occurrence-{handler,retention,origin,negative,tracer}.log`,
`protocol-jobs-{types,rules,properties,negative,negative-final}.log`, and
`protocol-jobs-inbound-release-isolated.log`. Earlier failed attempts were
reported; successful retry logs contain final results. All changes after
`77cc590` remain uncommitted and `.claude` is untouched.

Next: consume the typed physical FIFO head through a verified mux-monitor bridge,
including infrastructure failures and the responder projection/initiator result
bridge. Do not let the legacy responder-only list skip a preceding physical
infrastructure or initiator item. Group decisions must count the current physical
registered MiniProtocolJob subset, not historical metadata or protocol slot
activity. Then implement distinct interruptible group cancel/join, full pool
shutdown, buffer release and captured CM finalization. Cancellation after clean
completion but before body return must retain the committed completion/status
while producing no queued normal/error JobResult; exact pending-occurrence
bookkeeping must remain aligned. Synchronous exception-handler and post-return
masked publication regions also need their correct delivery guards. SI4/SI5,
outer scope integration and full shutdown remain open.


## SI4 sixth increment: typed FIFO monitor handling

The preceding protocol-job increment is committed as `a641636`. The requested
commit-first phase completed before this new work; its only amendment removed an
extra blank EOF line and final staged whitespace passed. Prior Agda evidence was
not rerun solely for that commit.

`JobPoolKernel.consumeCompletion` now removes one actual WithQueue head while
the pool is open. Empty, queue-free and closing pools refuse it. Existing generic
close statements are unchanged: queue removal preserves captured-handle and
closed-registry facts. `IGRegistration` adds status-only failure/stopped writes
and a separate Dead trace; lifecycle/retention coverage includes those operations
in both appropriate runtime modes. Old legacy completion actions are unchanged.

`MuxResultMonitor isBearerClosed` consumes the authoritative physical FIFO head
into a per-handler held state, then handles it in a separate event. The selected
responder generation/outcome is matched against its captured job and legacy
responder head before invoking the real source monitor action. While held, that
responder item remains in the legacy projection until handling; the representation
relation includes the held item as well as the remaining physical FIFO. Initiator
and infrastructure heads never consume an unrelated responder projection item.

Status writes precede error/Dead tracing. Responder errors complete their actual
exception-tracer callback and afterFailure continuation before the separate Dead
trace. Initiator completion traces ignored by IG are explicit local observations;
clean traces include DeltaQ before continuation, while error DeltaQ follows Dead.
Muxer errors always fail. Demux BearerClosed stops normally only when the CURRENT
registered MiniProtocolJob count is zero at handling. Counting ignores historical
removed jobs and slot activity; it includes completed/published jobs still in the
physical registry. The classifier parameter is an explicit source-exception
contract, not derived from the numeric ErrorId.

The owning monitor cannot resume commands/forks or select another item while
handling/tracing/finished. Independent child return, publication, insertion and
removal and other actors retain their original guards. Handling has no queue-empty
precondition: new results can arrive while the selected item is held. Normal or
failed monitor finish requires actual Dead callback return and matching mux
status, and changes only its local PC. It does not certify an empty queue, closed
pool, released buffer or parent handler Async result.

`Properties/MuxResultMonitor` projects every step/finite execution to real
OutboundMachine and selected-handler JobPool executions; initialized pool,
capture and runtime/supply corollaries retain their original premises. Local
Dequeue evidence retains the exact original head/tail, actual kernel removal and
stored selected value. Handle evidence retains captured generation matching,
actual source effects, the current registry/job captures and group count at that
step, and the classifier/count choice. Finished evidence retains actual callback
return, matching status and an unchanged underlying runtime.

Validation on 28 October 2026: the new model, property and final acceptance
endpoints passed with fresh Checking output in Agda 2.8.0, with
`+RTS -M2G -RTS` and no final warnings. Helper/kernel checks and regressions passed:
Properties/{JobPoolCloseKernel,HandlerIG,IGRetention,OriginMonitorInvariant},
new Negative/MuxMonitorEffects (13 named controls and two old close-certificate
applications), and existing Negative/{JobPoolLifecycle,WithoutQueuePool,
ConcurrentPool,TracerAttachment}. Kernel/source rule changes were checked
transitively; the final property/acceptance checks were fresh. One consume test
attempt was interrupted after process overlap was noticed; the final consume
check and remaining regressions ran individually and passed. No concurrent Agda
process remained afterward.

Negative/MuxResultMonitor contains 145 named reflexivity controls and initialized
main paths for clean/error results in both directions, infrastructure results,
current-registered count versus inactive/removed history, and the dequeue/count
race: mini count one at dequeue, child publication/deregistration, count zero at
handling, normal Stopped/Dead finish with a protocol tail still queued. A new child
publication during a blocked callback is also an actual initialized execution.
Wrong projection/generation fixtures are conditional controls. Unrelated-owner
controls check delegation guards, not successful execution of a nonexistent
second owner. Six local certificate applications and generic source/pool/capture/
supply applications passed against those paths.

An initial acceptance check exhausted 2 GB while expanding chained computed
snapshots. Flat explicit snapshots resolved it without raising the heap limit or
removing any case. Remaining checker repairs concerned local names, fixture
parentheses, exhaustive patterns and equality transport, not weakened statements
or altered model guards. The final thirteen-file local audit had only the three
known pre-existing Nat ≤?/<? operator false positives in IGRegistration, no actual
holes or unsafe additions. Tracked and four new files' whitespace checks passed,
including exactly one EOF newline. Pinned Mux/JobPool exports were verified.
No replay, source-pin change, unrelated build or second commit was performed.
Logs: `/tmp/cm-review-20261028/typed-monitor-{close,retention,source-retention,origin,
consume,queued,queuefree,concurrent,tracer,rules,properties,negative,negative-final}.log`.
The first chained-fixture failure is historical; final logs retain passing runs.
New work after `a641636` is uncommitted; `.claude` remains untouched.

Next is the distinct interruptible MiniProtocolJob group cancel/join operation,
using a one-shot snapshot of CURRENT registered protocol handles. Keep muxer and
demuxer alive during graceful egress drain, then perform the outer whole-pool
snapshot/cancel/join before buffer release and captured CM finalization. Async
cancellation of the owner during group cancellation/drain must abandon that
cursor and enter whole-pool unwind, immediately disabling its normal continuation
before the later async Failed write. Preserve committed clean completion without
fabricating a queue result if delivery precedes body return. Old normal/sync
masked publication can outrun cancellation. Monitor-local finished remains only
a prerequisite: actual pool/buffer/body outcome and rethrow-policy effects still
need coupling before parent Async results, outer scopes and SI5 full shutdown.

## SI4 seventh increment: group shutdown and distinct whole-pool close

`MuxGroupShutdown isBearerClosed` layers over the same captured physical pools
and typed monitor. Actual stop callers append CmdShutdown without a status or
tracer-return guard; enqueue remains available before physical startup, while a
callback is pending, and after monitor return. Selection still requires settled
parent insertion and the monitor's physical result priority. Stopping trace,
status write and current-registered MiniProtocolJob snapshot are separate steps.
The group cursor requests, delivers and joins sequentially while the underlying
pool remains open. It targets captured protocol jobs only; slot activity and
historical job tables do not define membership.

Unmasked body cancellation uses a real kernel interruptJob step and actual child
unwind, deregistration and Async-result boundaries. A clean commit before body
return can be cancelled without any typed queue result; exact ghost occurrence
removal preserves the source Idle/result commit. Synchronous jobHandler capture
refuses ordinary async delivery, allowing normal masked publication to win.
Explicit observed synchronous unwind replacement can instead enter the actual
protocol error path before an ordinary result is queued. Delegation guards prevent
an interrupted body from resuming its old return/commit continuation. Independent
children, other owners and ordinary source actors keep their existing guards.

Group completion permits observed empty egress or timeout, then Stopped and
TraceStopped. **Correction, 28 October (SI4-F1):** the pinned IG tracer handles
TraceStopped by publishing MuxFinished and clearing counters. The original
adapter omitted that callback; the twelfth increment below corrects it and
updates these initialized graceful witnesses. TraceStopped does not close the pool or emit
a TraceState Dead event. Monitor return or
observed owner abort enables a separate actual Kernel.beginClose snapshot of all
CURRENT registered jobs, including infrastructure, followed by sequential
uninterruptible cancellation/joins and actual finishClose. Owner abort seals the
normal cursor immediately; its Failed write and Dead trace wait for whole-pool
closure. An abandoned group cursor is not silently completed by that operation.
Removed history is outside the whole snapshot even when its Async result has not
arrived. ScopeDone records only this local outcome and pool closure.

`Properties/MuxGroupShutdown` projects every step and finite execution to actual
OutboundMachine and each selected physical JobPool execution. It lifts initial
pool, capture and supply facts with unchanged premises. The initialized
whole-closed-from-initial theorem certifies result availability for precisely the
actual whole-pool snapshot. Local observation records expose exact group capture,
eligible delivery, available-result join, actual unwind intermediate, owner-abort
stuttering, and actual whole-pool begin/finish steps. They do not yet establish a
separate global all-group-snapshot terminal invariant.

Source mapping and limitations are recorded in the SI4 source audit's
“Interruptible group shutdown and whole-pool unwind” section. Buffer release,
captured CM cleanup, proper handler body outcomes/rethrow policy and parent Async
completion remain the next integration obligations. Startup/tracer interruption
and remaining Server/IG/outer scope histories remain open. SI4/SI5, CM-I4c and the
overall G0–G5 objective are still in progress.

Validation on 28 October 2026: the new model and full properties endpoint passed
fresh Agda 2.8.0 checks using `+RTS -M2G -RTS`, exit zero without warnings. The
property check includes the appended delivery, join, abort and whole-close local
observations (`group-shutdown-properties-final.log`). The initial and extended
flat acceptance matrix and final theorem applications passed fresh at 2 GB
(`group-shutdown-negative.log`, `group-shutdown-negative-final.log`). No heap
increase or case deletion was used.

Shared helper changes passed the close/retention/origin endpoints and existing
Negative/{JobPoolLifecycle,WithoutQueuePool,ConcurrentPool,TracerAttachment}
regressions. New Negative/MuxGroupEffects has 19 conditional helper controls;
these require the adapter to supply ordering. External enqueue additions were
rechecked through affected retention/origin/effects/tracer endpoints. Logs are
`/tmp/cm-review-20261028/group-shutdown-{rules,properties,properties-final,close,
retention,igretention,origin,effects,queued,queuefree,concurrent,tracer}.log` and
`group-shutdown-enqueue-{retention,igretention,origin,effects,tracer}.log`.
Checks ran one Agda process at a time. No Haskell replay, source-pin change or
unrelated proof build was performed. All new work after `a641636` remains
uncommitted; `.claude` is untouched.


Negative/MuxGroupShutdown composes actual initialized paths for the 30-step
normal group/drain/whole-close suffix, committed clean cancellation with timeout,
masked error publication winning cancellation, explicit synchronous unwind
replacement, independent infrastructure publication, 25-step group-abort and
20-step removed-history-abort suffixes, and drain interruption. It checks physical
FIFO priority, actual stop enqueue before startup and the masked insertion gap.
The main paths use no injected conditional source worlds; unwind, drain and trace
observations remain explicit contracts. Generic source/pool/capture/supply results,
three initialized whole-snapshot terminal certificates and the local observation
records are applied to these paths. The removed-history example deliberately
retains a deregistered handle without an Async result after whole close.

Final audit scanned all seventeen pending Agda files: only three inspected
pre-existing Nat decision operators in IGRegistration were reported, with no
actual holes or unsafe additions. Tracked/new-file whitespace checks passed,
including exactly one EOF newline. These are local proof/source checks, not a
term-level audit of all dependency assumptions or implementation replay.

## SI4 eighth increment: buffer scope, captured CM finally and parent results

`MuxHandlerExit isBearerClosed` extends the same group/monitor/protocol/startup
state without creating another pool or adopting existing handler records. A
successful mux owner's physical history stays in the original registry; a new
exit record carries typed outcomes that the earlier ErrorId-only pre-handshake
phases cannot represent. Normal return, async exception, original synchronous
exception and peer-wrapped exception remain distinct.

Exit starts only after actual mux ScopeDone and closedPool, using the original
startup frame's HandlerStart and matching source registration. Observed buffer
scope return preserves that mux outcome. An observed provider exception can
replace it, and cannot be used to turn an exception into normal success. Since
withBuffer is a supplied callback, these observations are provider contracts,
not a proof of concrete memory release. Synchronous failures then enter the
captured-context rethrow-policy boundary and require the error trace to return.
ShutdownPeer rethrows ExceptionInHandler; ShutdownNode requires observed main
receipt before rethrowing the original error. Async failures bypass this classifier.

The adapter invokes actual OutboundMachine handlerExit and cleanupStep actions,
retaining map acquisition, captured entry selection, socket close, prospective
map publication/restoration, TIME_WAIT finally and counter reads. Each cleanup
operation checks the original HandlerStart against the source registration.
Cleanup failure overrides the body outcome outside the already-exited classifier.
The local frame records whether the actual failure operation was synchronous
socket close or asynchronous TIME_WAIT interruption, and matches its ErrorId at
completion. Shared CleanupOutcome alone cannot establish that exception class.
Parent result availability requires actual cleanupDone, the matching local
cleanup-completion stage and explicit Async-result publication. resultOf exposes
the typed value only after that publication.

CM snapshot capture/read/send/collective wait use the same coordinator in the
physical-handler state. Delivery to a waiting/group/draining mux is coupled to
actual owner abort before acknowledging throwTo; TIME_WAIT delivery executes the
actual cleanup interruption before acknowledgment. The result oracle combines
the new successful-mux exit records with the old pre-handshake physical history.
The old pre-handshake final-wait bypass is disabled in this adapter. A completed
pool, send acknowledgment, cleanupDone or removed map entry alone cannot satisfy
the successful owner's result observation. Independent admissions, source actors,
children and other owners remain enabled under their existing guards.

`Properties/MuxHandlerExit` projects all steps and finite executions to actual
OutboundMachine and selected physical JobPool histories, retaining initialized
capture and supply premises and whole-snapshot terminal certificates. Publication
observations retain the actual cleanupDone result and local predecessor. Its
PhysicalWait retains the actual wrapper finishClose call, exact combined result
oracle and primitive final-wait observations. These local certificates do not
assert global all-history termination or eventual progress.

The remaining profile gaps include CM delivery in buffer/policy/trace windows,
setup/startup and custom tracer failure/unwind, plus outer Server/IG/governor
histories and admission quiescence. Normal error-trace return and node delivery
are still observations, not a node-exit theorem. SI4/SI5, CM-I4c and G0–G5 remain
open. Source mapping: the SI4 audit's “Buffer scope, handler outcome and CM finally”
section. All work after `a641636` remains uncommitted.

Validation on 28 October 2026: Agda 2.8.0 checks passed at `+RTS -M2G -RTS`,
exit zero without warnings, for the new runtime, Properties/MuxHandlerExit,
Negative/MuxHandlerExitFixtures and all three acceptance endpoints:
Negative/{MuxHandlerExit,MuxHandlerExitOutcomes,MuxHandlerExitCM}. The final
property and acceptance checks have fresh Checking output. The runtime was also explicitly freshly checked after invalidating only its own
interface (`handler-exit-rules-final.log`);
source comments and documentation were not used as a reason for unrelated builds.
No old theorem type, transition or build setting was changed in this increment.

Initialized paths cover normal and async mux outcomes through actual CM cleanup
and parent Async publication; both peer/node rethrows after an observed buffer
exception; socket-close failure with map restoration before publication; and the
combined CM snapshot/read/send/owner-abort/whole-pool-close/CM-finalizer/result-wait
path. It refuses collective close before result publication, early finalizer or
result shortcuts, async classification and node rethrow before delivery. Generic
source/pool/capture/supply results and actual Publication/PhysicalWait certificates
are applied. The separate TIME_WAIT delivery/finally/counter/result fixture is
explicitly conditional on an already-entered finalizer, not an initialized trace.
Buffer, policy, trace-return and node-delivery observations remain contracts.

Several initial checks exhausted the 2 GB heap while elaborating helpers and
re-exported controller aliases at the concrete classifier. Generic lift helpers,
shared-state snapshot builders and private internal module aliases resolved that
cost; acceptance was split by responsibility. No case was removed and no heap or
safety setting was relaxed. Final logs are in `/tmp/cm-review-20261028/`:
`handler-exit-{rules-final,properties-final,fixtures,negative-final,outcomes,cm}.log`.
Scratch probes and earlier checks are historical diagnostic evidence, not final
acceptance. The final runtime log retains its fresh Checking line.

The final pending-worktree audit scanned 23 Agda files: only the three previously
inspected Nat decision-operator false positives in IGRegistration were reported;
all six new exit-layer files had zero findings. No holes or unsafe additions.
Tracked/new-file whitespace and exactly-one-EOF-newline checks passed. Pinned
source objects were compared locally; no Haskell replay, source-pin change,
commit, push or unrelated heavy proof build was performed. `.claude` is unchanged.

## SI4 ninth increment: observed post-mux cancellation windows

Commit-first completed as `a173dd0` (26 files), bundling typed FIFO monitoring,
group/whole-pool shutdown and handler exit. Prior successful checks were not
rerun solely for that commit; staged whitespace passed. `.claude` was excluded.
The following cancellation-window work is uncommitted after that anchor.

`MuxExitCancellation` shares MuxHandlerExit.State directly. It adds observed
interruptible buffer-provider, classifier error-trace and node-send delivery;
there is no second registry, JobPool or source configuration. Buffer delivery
retains the provider-unwind boundary with an async outcome. Classifier-trace/send
cancellation seals that continuation and exits the handler with the new async
exception. A separately observed synchronous error-trace exception escapes as
the new original synchronous error, without reclassification or the old peer
wrapper. Provider teardown can still replace pending cancellation with a new
synchronous error. No post-Mx.run cancellation invents a mux Failed/Dead write.

Pure masked policy selection/rethrow and uninterruptible finalizer stages are
not generalized delivery points. Named windows are operation/mask contracts;
provider/tracer implementation masks are not derived from a numeric ErrorId or
from the phase alone. Interrupted node send does not certify main nonreceipt,
exception retraction or node exit. The old explicit TIME_WAIT interruption and
finished-target acknowledgment keep their separate source guards.

CM delivery takes the actual awaitDelivery target, records the same observed
operation delivery, then performs actual coordinator acknowledgment. The sender
still cannot finish the collective wait until the provider/body/CM finally and
explicit parent Async-result publication settle. `Properties/MuxExitCancellation`
projects all steps and finite executions to actual OutboundMachine and selected
JobPool traces; initialized capture/supply and whole-snapshot facts retain their
old premises. Delivery and ShutdownDelivery records retain exact predecessor,
window, receiver, intermediate and acknowledgment. The final wait reuses the
checked physical-result oracle and its actual wrapper call.

Validation on 28 October 2026: Agda 2.8.0 runtime, properties and acceptance checks
passed at `+RTS -M2G -RTS`; the final property and expanded acceptance checks were
fresh, exit zero without warnings. The runtime was also checked transitively
after its explicit helper type declarations. Logs:
`/tmp/cm-review-20261028/exit-cancellation-{rules,properties,negative,negative-final}.log`.
Private internal module aliases keep the concrete proof layer small. No heap or
safety setting was changed, and no previous theorem statement was weakened.

Negative/MuxExitCancellation has actual initialized paths for buffer cancellation
through provider return, CM cleanup, Async result and collective close; classifier
trace and blocked node-send cancellation through actual cleanup/result publication;
and a synchronous error-tracer exception through cleanup/result publication.
Actual CM snapshot/read/send/delivery/ack prefixes are also checked for the tracer
and node-send windows. Refusals cover pure masked stages, wrong windows, stale
tracer/policy/send continuation, premature finalizer and premature collective wait.
Generic source/pool/capture/supply, exact delivery and physical-wait certificates
are applied. A provider-finalizer replacement step uses the initialized buffer
prefix. Source callbacks and exception-delivery observations remain contracts.

All three new Agda files passed the scoped proof audit with zero findings.
Tracked/new-file whitespace and exactly one EOF newline passed. Pinned Core and
ConnectionHandler exports were compared locally. No Haskell replay, source-pin
change, unrelated proof build, push or second commit was performed.

Next: post-publication setup/startup and mux/IG-tracer failure/unwind, before
outer Server/IG/governor histories. Keep actual fork/insertion gaps and current
whole-pool snapshots; no fabricated successful startup or pool/body result may
bridge a setup failure. Admission quiescence and full shutdown remain separate.
SI4/SI5, CM-I4c and overall G0–G5 remain open.

## SI4 tenth increment: partial startup and synchronous mux-tracer unwind

`MuxStartupUnwind` layers over the same cancellation/handler state, physical
handler history and queued pools. It records the original published handler,
mux identity, partial startup PC, callback at failure, exception class and lexical
scope route. Its exception type has only synchronous/asynchronous failures;
there is no fabricated successful-body outcome. The three routes distinguish
failure before provider callback invocation, failure inside its buffer scope
before pool acquisition, and failure inside an acquired JobPool bracket.

Named setup sites cover buffer/bearer setup, TraceStarting, egress/label setup,
pool acquisition, infrastructure forks before birth, Mature and timeout setup.
The model refuses ordinary async delivery in existing fork/insertion gaps. A
selected fault immediately seals that owner's startup/monitor controller while
independent children, other owners and ordinary source actors keep their guards.
The partial startup PC is retained even after physical parent result publication;
it is not rewritten into monitoring or G.ScopeDone to reuse an exit gate.

An entered pool closes through actual current-registry beginClose, sequential
cancellation, child unwind/removal, Async-result joins and finishClose. Synchronous
failure then leaves the mux's prior status/callback intact and hands a failed
body to the buffer scope. It does not invent Failed/Dead. Startup async delivery
inside that bracket instead closes the pool BEFORE actual Failed/Dead/rethrow;
pre-catch delivery does not enter that later catch. A synchronous exception from
the catch's own tracer replaces the original async outcome without re-entering
the catch or rewriting its Failed value. Before buffer callback invocation the
handoff goes directly to body classification; otherwise provider unwind remains
outstanding. The existing typed policy/CM-finalizer/parent-result sequence is
reused, including the actual CM send acknowledgment and collective result wait.

For monitor tracing, caller mux-tracer entry is distinct from IG STM failure.
The new guard permits the first custom tracer leg or actual tracerFailed evidence,
plus the existing explicit initiator trace observation. A pending commitTrace
alone is not an exception certificate. The conditional successor-registration
control executes real IG.commitTracer, including prefix/retry precedence, before
observing the descriptor exception. Callback failure is retained rather than
changed into a successful return. Source audit details are in the SI4 audit's
“Partial startup and synchronous mux-tracer unwind” section.

`Properties/MuxStartupUnwind` projects every plan, successful action and finite
execution to actual OutboundMachine and each selected physical JobPool history.
Initial capture/supply and current whole-snapshot terminal facts keep their
premises. Selection retains the real owner lookup, settled parent insertion,
successful publication, exact mux lookup, scope route and original callback.
PhysicalWait retains the actual nested wrapper finishClose call and the combined
physical-result oracle. These are operational/source-contract certificates, not
universal progress or implementation refinement.

Acceptance is split into data-only Fixtures and five acceptance endpoints:
Negative/MuxStartupUnwind, Branches, Interleavings, CM and Sites. Initialized
paths cover two-engine Mature failure through actual close, provider exit,
peer rethrow, CM finally and parent result; pre-buffer and bearer failure;
zero-engine startup async close/Failed/Dead/finally/result; pre-catch cancellation;
all named setup and graceful stopping/stopped trace sites; and custom monitor
tracer failure through the actual pool close. The masked-gap path publishes an
infrastructure result before insertion, waits to remove it, then closes an empty
current snapshot while its removed historical Async result is still unavailable.
A separate initialized CM path captures/reads/sends, acknowledges startup delivery,
then waits through pool/provider/finalizer/result before collective close. The
successor-registration descriptor control is conditional, not an initialized
second-handler history. An initialized exception from async-catch Dead tracing
retains the original Failed status and hands off the replacement sync error.

Next remains async mux/IG callback delivery, some ignored/DeltaQ tracer windows,
post-close catch cancellation, earlier allocation/publication gaps and additional
child-finalizer failure classes, followed by outer Server/IG/governor histories.
Named helper/provider/trace faults are observations; their unmodeled internal
resources and mask implementations are not proved by the fault label. Admission
quiescence, full shutdown, SI4/SI5, CM-I4c and overall G0–G5 remain open.

Validation on 28 October 2026: all eight new modules passed Agda 2.8.0 with
`+RTS -M2G -RTS`, one process at a time, exit zero without warnings. The runtime
was freshly rechecked through the tightened-tracer interleavings closure; the
final properties, fixture and acceptance closures have Checking output. Final
commands used Properties/MuxStartupUnwind and
Negative/{MuxStartupUnwind,MuxStartupUnwindBranches,MuxStartupUnwindInterleavings,
MuxStartupUnwindCM,MuxStartupUnwindSites}. Imports checked the runtime and generic
fixture transitively. One larger property recheck initially exhausted 2 GB while
freshly checking the changed runtime; the subsequent serial interleavings check
completed that runtime/property/fixture/main closure at the same limit. No heap
increase, scenario removal or safety relaxation was used. Checker repairs were
local scoping/equality transport and exact wrapper projection, not weakened goals.
No old model or theorem statement was changed in this increment.

Logs are in `/tmp/cm-review-20261028/`:
`startup-unwind-{rules,properties,properties-final,fixtures,negative,branches,
interleavings,interleavings-final,cm,cm-final,sites,sites-final}.log`.
Earlier logs are historical where a later final log supersedes them. Eight-file
local proof audit: zero findings. Tracked/new-file whitespace and exactly one EOF
newline passed. Exact pinned source objects were compared locally; there was no
Haskell replay, upstream/pin change, unrelated build, commit or push. This and the
preceding cancellation-window increment remain uncommitted after `a173dd0`;
`.claude` is untouched. Source-fidelity and finite model evidence remain separate
from implementation replay and a term-level audit of dependency assumptions.


## Eleventh increment: async mux/IG callback interruption (28 October 2026)

`MuxStartupUnwind.unmaskedMuxCallback` observes async delivery at a published,
monitoring owner with a settled fork/registration gap. Callback read/STM and
post-commit continuations retain their exact source snapshot. Selection changes
only fault metadata; `Properties/MuxStartupUnwind.cancellation-keeps-base` proves
that the source, pool and held monitor state are unchanged. Existing controllers
are sealed for that owner while physical children and other actors can proceed.
The original callback is not cleared to Returned to satisfy an exit guard.

The real current-pool snapshot must close before the catch writes Failed.
Separate `recordInterruptedMuxFailure` and `traceInterruptedMuxDead` operations
preserve the old successful-return guards. The status write leaves the abandoned
callback intact; the subsequent operation invokes a new Dead callback, retaining
the original callback in the fault record. Its queue/counter transaction can retry.
Provider unwind, the captured CM finally and physical Async-result publication
remain required. The existing source/pool execution projections, initialized
capture/supply and snapshot-terminal certificates cover the new actions.

Initialized acceptance paths cover a held responder completion at its pending
IG STM transaction, and a start tracer after its atomic counter/event burst has
committed but before a protocol fork. The former does not commit the interrupted
transaction; the latter does not roll back the already committed burst. Both
close the actual infrastructure snapshot and invoke Failed/Dead in order.
`Negative/MuxCallbackCancellationCM` additionally drives the CM snapshot/read/send,
actual callback delivery acknowledgment, collective wait, buffer exit, original
CM cleanup and physical parent result. Delivery and pool close cannot shortcut
the remaining cleanup/result obligations. Queue-full Dead retry controls are
conditional snapshots, not initialized queue-saturation witnesses.

The exact pinned Mux, JobPool, ConnectionHandler and InboundGovernor source
objects were byte-compared with the local audit exports. Mux.hs:254–279 places
the async catch after the pool bracket; InboundGovernor.hs:635–720 uses an active
read followed by atomic event/counter effects. Delivery observations and provider/
mask contracts remain explicit. No implementation replay or full-shutdown claim
follows from these finite model executions.

### Newly verified source-fidelity issue SI4-F1

The earlier audit incorrectly called TraceStopped ignored by IG. At this pin,
Mux.hs:565 emits TraceStopped; InboundGovernor.hs:719–728 routes it to the same
MuxFinished/counter-clear STM branch as TraceState Dead. The current
`MuxGroupShutdown.observeTraceStopped` is only a local phase change and skips
that effect, retry and interruption boundary. Its initialized graceful examples
therefore cannot be presented as complete source-faithful graceful shutdown.
The correction is required before extending those graceful claims: model the
actual callback invocation, active sample, atomic commit/retry, and return before
monitor return/whole-pool close. Preserve existing Failed/Dead distinctions.
This finding changes the next task's priority; the current async-callback paths
start from non-graceful initialized monitor histories.


Validation for the eleventh increment: Agda 2.8.0 checked thirteen targeted
endpoints serially with `+RTS -M2G -RTS`, all exit zero without warnings:
`Properties/{SubsystemSupply,SubsystemReferences,OriginMonitorInvariant}`,
`MuxStartupUnwind`, `Properties/MuxStartupUnwind`,
`Negative/{MuxCallbackCancellation,MuxCallbackCommitted,MuxCallbackCancellationCM,
MuxStartupUnwindBranches,MuxStartupUnwindInterleavings,MuxStartupUnwindCM,
MuxStartupUnwindSites,MuxGroupEffects}`. Each final log contains its Checking
line. Two aggregate fresh-dependency/property attempts exhausted 2 GB; checking
the runtime separately and then its property closure succeeded at the same limit.
No scenario was removed, statement weakened, heap increased or safety disabled.

The thirteen-file static audit flags three existing question-mark comparison
operators in IGRegistration (≤? and <?), verified unchanged from HEAD, rather
than proof holes. No new holes, postulates or checker bypasses were introduced.
Whitespace and one-EOF checks pass for all sixteen changed/new source and
documentation files. Final logs are `/tmp/cm-review-20261028/callback-final-*.log`;
`callback-properties-cold-heap.log` preserves the final aggregate heap failure,
and `callback-proof-audit.log` records the heuristic audit. No checker remains
running. These changes are uncommitted after `d47f109`; `.claude` is untouched.
No Haskell replay, source-pin change, full-system shutdown proof, commit or push
was performed. Next: correct SI4-F1, then resume the remaining callback/failure
windows and outer Server/IG/governor composition.


## Twelfth increment: SI4-F1 graceful TraceStopped correction (28 October 2026)

Rechecked exact pinned Mux.hs and InboundGovernor.hs against the audit exports.
Mux.hs:555–570 writes Stopped before TraceStopped; InboundGovernor.hs:719–728
recognizes TraceStopped and TraceState Dead with the same active-gated,
atomic MuxFinished/counter-clear transaction. This fixes the source-fidelity
issue identified in the eleventh increment; the network pin is unchanged.

`Rules/IGRegistration.traceGracefulMuxStopped` identifies the real graceful
source event separately from `traceMuxDead`. `MuxGroupShutdown` now enters
`stoppedTracing`, samples active, attempts the real tracer transaction, and
requires its returned callback at Stopped before `finishStoppedTrace` permits
monitor return. Only then may whole-pool closure start. A full queue retries;
no callback return, counter clear, notification or normal pool exit is invented.
The callback itself does not join or close the still-live infrastructure pool.
No-IG attachment and an attached inactive tracer remain distinct branches.

`Properties/MuxGroupShutdown.StoppedReturn` and `finish-stopped-observation`
expose the exact owner/mux lookups, Stopped status, returned callback, and next
phase of every successful graceful return. Generic source/pool execution
projections cover each new action; initialized capture/supply and snapshot-result
certificates retain their original statements. Mux retention, handler chains,
subsystem references and origin classification cover the new source operation.

Initialized normal, clean-cancellation, error-publication-race and unwind-error
witnesses now include the callback's invocation, active sample, commit and
return. Their post-callback snapshots retain the notification and cleared
counters through whole-pool close and downstream CM cleanup. The old acceptance
claim that source state was unchanged by TraceStopped was false at the pin; it
is replaced by explicit Stopped-status and MuxFinished-publication checks.

`Negative/MuxStoppedTracer` checks blocked return/closure at each boundary,
100-slot retry versus 99-slot atomic success, captured-active semantics,
inactive/no-IG behavior, and the return certificate. Full/inactive/no-IG controls
are explicitly conditional snapshots, not initialized saturation or attachment
reachability claims. `MuxStoppedTracerCancellation` supplies an initialized
history through real graceful group cancellation and pending TraceStopped
callback, then observed async delivery, actual whole-pool close, Failed/Dead
and provider handoff. The abandoned graceful notification is not committed;
the new Dead invocation publishes once. The old callback remains in the fault
record and its old controllers cannot resume. Returned-callback cancellation
uses the existing ordinary abort guard and retains already committed effects.

The new cancellation endpoint imports small, data-only MuxPoolCloseFixtures;
it proves all transitions rather than importing another acceptance endpoint
solely for its snapshots. Async delivery, buffer/helper masks and custom tracer
normal/exceptional outcomes remain explicit contracts. There is no Haskell mux
replay or new universal shutdown/liveness/source-refinement claim.


Validation for the twelfth increment: twenty-one targeted Agda 2.8.0 endpoint
commands passed serially at `+RTS -M2G -RTS`, without warnings. Final logs have
seventeen own-module Checking lines and four cached successes (group/unwind
properties and group/startup acceptance); those closures had already passed
with the current dependencies. Commands checked
`Properties/{SubsystemSupply,SubsystemReferences,OriginMonitorInvariant,
MuxGroupShutdown,MuxStartupUnwind}` and
`Negative/{MuxGroupShutdown,MuxStoppedTracer,MuxStoppedTracerCancellation,
MuxHandlerExit,MuxHandlerExitOutcomes,MuxHandlerExitCM,MuxExitCancellation,
MuxStartupUnwind,MuxStartupUnwindBranches,MuxStartupUnwindInterleavings,
MuxStartupUnwindCM,MuxStartupUnwindSites,MuxCallbackCancellation,
MuxCallbackCommitted,MuxCallbackCancellationCM,MuxGroupEffects}`.
The changed source runtime/rules and new pool fixture were also checked during
incremental development, directly or transitively. No endpoint is described as
fresh solely from a cached success.

Two initial aggregate callback-cancellation checks exhausted 2 GB while importing
large acceptance modules only for data. The small data-only fixture layer removed
that dependency; the same initialized scenario then passed at 2 GB. No statement
was weakened, scenario removed, safety disabled or heap limit raised. Local
record-field/import scoping repairs were completed before the final checks.
Logs: `/tmp/cm-review-20261028/si4f1-final-*.log`; the two heap failures remain in
`si4f1-tracer-cancellation.log` and
`si4f1-Negative-MuxStoppedTracerCancellation.log`. Static audit of all twenty
pending Agda files found only the same three pre-existing comparison-operator
false positives (≤?/<?) in IGRegistration. No new postulates, holes or unsafe
options were added. Whitespace/EOF checks pass. These changes and the preceding
callback increment remain uncommitted after d47f109. No checker is running.
No source-pin change, Haskell replay, commit or push was performed; `.claude` is untouched.

SI4-F1 is complete within the stated profile. Next: expose the bearer tracer's
TraceEmitDeltaQ callback after clean protocol completion and after Dead on error,
with normal/synchronous/asynchronous outcomes. Preserve prior status/notification
commits and exception replacement; do not infer normal monitor return when that
callback throws. Remaining ignored callbacks, post-close catch cancellation,
earlier allocation/publication and child-finalizer failures, followed by outer
Server/IG/governor composition and admission quiescence, still precede SI5.


## Thirteenth increment: explicit bearer DeltaQ outcomes (29 October 2026)

The overall objective remains the standalone CM/IG/OG/Server model for source
bug-finding at the pinned network revision. This increment extends SI4's physical
handler/mux chain; it does not merge that chain with PeerSupervision/Subsystem or
Server, complete G1/G2, CM-I4c, or derive SI5/full shutdown.

Re-exported exact-pin Mux, JobPool, ConnectionHandler and InboundGovernor source
objects into `/tmp/cm-review-20261029/` before extending claims. Mux.hs:454–464
calls the bearer tracer's TraceEmitDeltaQ after the clean protocol trace, before
another monitor iteration. For a protocol error it first writes Failed and
returns from the exception/Dead tracers, then runs DeltaQ before throwing the
original error. Infrastructure-result branches have no DeltaQ invocation.
The async catch remains outside the real JobPool bracket at Mux.hs:254–279.

`MuxDeltaQ` extends MuxStartupUnwind with tickets taken only from actual successful
typed FIFO consumption. Direction, protocol number, RunId and completion outcome
remain distinct. Entry explicitly requires a monitoring owner and an open
physical pool; a
callback PC cannot adopt partial startup or an already closed bracket. Tracked
IG completion/Dead stages must return at the proper status before entry. Where
the lower component leaves a caller/ignored mux-tracer leg opaque, DeltaQ entry
incorporates that leg's observed normal return; it does not prove tracer totality.
The protocol-error branch reaches DeltaQ only after Dead at the original Failed
value. Normal return invokes the existing exact lower monitor step. Raw clean
branch finish and protocol-error final finish are blocked in the extended
adapter until DeltaQ returns; the intermediate error-trace-to-Dead continuation
is retained. An invoked owner cannot resume its controller, while
other owners, child publication/deregistration and external stop retain their
own guards. The lower MuxResultMonitor is still a component with an observed
successful trace/DeltaQ-return boundary, not a replacement full-source theorem.

A named sync/async exception from an invoked callback selects the actual captured
handler and current-pool route, without changing its held result or already
committed source effects. It retains the complete physical-pool close, buffer
scope, policy and original CM finally/result gates. Sync failure preserves the
existing Ready or original Failed status and replaces the body exception. Async
failure writes the new Failed only after actual pool closure, then invokes a new
Dead callback. Previously committed notifications remain; an earlier protocol
error's Dead notification is not deduplicated or retracted.

`Properties/MuxDeltaQ` projects every successful action and finite execution into
actual shared-source and selected physical-pool histories. Initialized capture,
entry/promise supply and captured-snapshot terminal certificates retain their
existing premises. Fault selection reuses the published-owner/current-pool
certificate; selection/entry do not roll back source effects. The physical CM
wait certificate observes the actual nested dispatcher and physical-result
oracle. `MuxDeltaQCapture.consume-captures-head` exposes the precise original
queue/head, actual pool dequeue, selected monitor state and stored ticket.
The separate `MuxDeltaQPrefix` layer lifts only tagged protocol-only prefixes,
without importing the large source-invariant closure solely for prefix proofs.

Acceptance endpoints:

- `Negative/MuxDeltaQ`: initialized normal clean/error paths in both directions;
  infrastructure exclusion; no skipped, premature, repeated or uninvoked callback;
  actual-head certificates and initialized source/capture/supply facts.
- `MuxDeltaQEffects`: initialized sync and async callback exceptions after clean
  completion and after the error branch's returned Dead. The returned protocol
  can deregister/publish its Async result independently during DeltaQ. All four
  combinations close the real current pool, run the captured CM finally and
  publish the physical parent result. Sync replacement keeps the old mux status;
  async handling retains old notifications and appends the new Dead event.
- `MuxDeltaQCM`: actual initialized CM snapshot, late read, send, DeltaQ delivery
  receipt, collective wait, pool/buffer/CM unwind and physical result publication.
  Receipt, registry closure and cleanup completion cannot shortcut the final wait.
- `MuxDeltaQInterleavings`: infrastructure return/publication and external stop
  during invoked DeltaQ, followed by actual callback return and FIFO consumption.
  The new physical head replaces the old ticket. A queued result outranks shutdown;
  with only that backlog removed, the positive shutdown-selection control passes.
  Forged-PC controls reject partial startup and already closed pools; these
  conditional controls are not initialized reachability claims.

Tracer return, exception class/identity, async receipt, provider behavior and
policy choice remain explicit observed contracts. The pinned optional DeltaQ
transformer (TraceTransformer.hs:42–55) may reset its private statistics and emit
a sample before forwarding TraceEmitDeltaQ. Those statistics/logger resources
are not represented by these CM-source preservation statements. No total-tracer,
full mask, helper-resource cleanup, universal progress, full source refinement or
Haskell mux replay claim follows from these finite executions.

### Conditional source-profile finding, not a confirmed deployment defect

The initialized clean/synchronous case reaches a physically available handler
result after pool and CM cleanup while mux status remains Ready. This strengthens
the earlier conditional tracer-failure boundary with an initialized DeltaQ path;
it refutes any proposed general invariant that every handler exit must write
Failed/Stopped under the admitted tracer inputs. The witness has one protocol
and retains earlier IG events, so it does not establish an IG/PSA deadlock.
Concrete bearer-tracer contracts, multi-protocol/overlapping-key reachability and
implementation replay must be checked before presenting it as a source bug.
Likewise the additional Dead notification after async failure is source-aligned
behavior, not by itself proof of a key-reuse defect.


Validation on 29 October: the current runtime was freshly checked with
`agda ConnectionManagement/MuxDeltaQ.agda +RTS -M2G -RTS`. After making the
monitoring/open-pool guard explicit, all ten final endpoint commands passed
serially without warnings:

```sh
agda ConnectionManagement/MuxDeltaQ.agda +RTS -M2G -RTS
agda ConnectionManagement/Properties/MuxDeltaQPrefix.agda +RTS -M2G -RTS
agda ConnectionManagement/Properties/MuxDeltaQ.agda +RTS -M4G -RTS
agda ConnectionManagement/Properties/MuxDeltaQCapture.agda +RTS -M4G -RTS
agda ConnectionManagement/Negative/MuxDeltaQ.agda +RTS -M4G -RTS
agda ConnectionManagement/Negative/MuxDeltaQEffects.agda +RTS -M4G -RTS
agda ConnectionManagement/Negative/MuxDeltaQCM.agda +RTS -M4G -RTS
agda ConnectionManagement/Negative/MuxDeltaQInterleavings.agda +RTS -M4G -RTS
agda ConnectionManagement/Negative/MuxResultMonitor.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/MuxStoppedTracer.agda +RTS -M4G -RTS
```

Seven final logs contain their own module Checking line; the already rechecked
runtime and two unchanged negative controls were cached confirmations. The fresh
runtime Checking line is in `deltaq-runtime-final.log`. The source-proof closure
initially exhausted 2 GB, including after separating the cheap prefix layer.
With resource availability checked, the source/acceptance closure passed at the
explicit 4 GB heap limit. No proof statement was weakened, scenario removed,
postulate introduced or safety check disabled. The only warning during development
was a constructor-shadowing pattern name in an acceptance helper; renaming it
removed the warning before the final run. Equality-transport, scoping and module
import repairs were also completed before these final checks.

Logs: `/tmp/cm-review-20261029/deltaq-final-*.log`, with the retained 2 GB failure
in `deltaq-properties.log`, the fresh-runtime log above and
`deltaq-proof-audit.log`. Eight-file local proof audit: zero findings; tracked/new
source/documentation whitespace and EOF checks passed. Dependency assumptions
have not been replaced by a term-level external axiom audit. No Haskell replay,
source-pin change, commit, push or unrelated build was performed; `.claude` is
untouched. This increment is uncommitted after 920c16f.

The initiator-direction completion trace also now has explicit invocation,
normal return, sync/async exception and CM-delivery actions. IG ignores these
completion traces, but the caller mux tracer still runs. The initialized clean
and error normal paths use the new actions and reject legacy return/failure
shortcuts before invocation. Generic source/pool projection includes the new
actions. Full initiator-failure cleanup and CM-delivery acceptance witnesses
remain open; the existing complete failure witnesses above concern DeltaQ.

Next executable obligation: initialized initiator-tracer sync/async failure
cleanup, including a live responder in the same physical pool and CM delivery.
Retain the captured completion and already written status without inventing
first-leg return or labeling that failure as DeltaQ.
Then post-close catch cancellation, earlier allocation/publication and additional
child-finalizer/helper scopes remain before outer Server/IG/governor composition
and admission quiescence. Source-contract and stronger reachability/replay checks
for the conditional Ready-after-exit path remain bug-finding follow-ups; no
universal deadlock or full-shutdown claim is made by this increment.


Commit validation on 29 October: after adding the explicit initiator-trace
transitions and normal-path controls, all eight DeltaQ runtime/property/acceptance
modules listed above passed serially with Agda 2.8.0 at a 4 GB heap limit. Six
logs contain Checking lines; runtime and generic source properties were cached
confirmations of their earlier initiator checks. No warnings were reported.
Eight-file static proof audit again found zero findings, and staged whitespace
checks passed. Logs: `/tmp/cm-review-20261029/commit-*.agda.log`. The two unchanged
non-DeltaQ negative controls were not repeated for this commit. No implementation
replay or full initiator-failure cleanup witness was added during commit work.


## Fourteenth increment: ignored initiator completion tracer failures

The caller mux tracer still runs on initiator-direction clean/exception exit,
even though IG's `miniProtocolTerminated` ignores that direction. The unchanged
network pin's Mux.hs:454–464 places the clean trace before bearer DeltaQ; on
protocol error it first writes Failed(original), then calls the exception trace,
Dead, DeltaQ and the original throw. The async-only catch at :275–279 is outside
the physical JobPool bracket (:254–274). JobPool.hs:70–111 closes the captured
registry by sequential uninterruptible cancellation; :147–163 excludes async
exceptions from the job result handler. IG.hs:736–748 recognizes only responder
completion traces. ConnectionHandler.hs:363–365 and :438–440 compose the caller
tracer before IG. The four local exports were compared byte-for-byte with their
pinned Git objects again on 29 October before extending these proofs.

`Properties/MuxInitiatorTrace` adds a selection certificate for the existing
explicit initiator-trace actions: the selected owner/capture, startup PC, callback
and physical parent-registration facts come from the existing fault selector.
`throw-keeps-underlying` proves a local observed throw retains the underlying
source/pool/handler state at selection; cleanup is not manufactured by observation.
The existing generic MuxDeltaQ source/pool/capture/supply statements retain their
types and cover these actions.

`Negative/MuxInitiatorTraceEffects` starts from the actual initializer, admits a
responder, forks an initiator in the same pool, publishes and captures its typed
physical FIFO head, and invokes the initiator trace. While that callback is held,
the already returned initiator deregisters and publishes its physical result.
For each clean/error completion and sync/async tracer exception, the real pool
snapshot contains **the still-running responder, demuxer and muxer**. Every child
is cancelled, unwound, deregistered, physically completed and joined. Snapshot
terminal results follow from `whole-closed-from-initial`; no historical handle
is deleted and no protocol result is fabricated for async cancellation. A join
before the responder's physical result is rejected.

All four finite histories continue through provider/buffer exit, exception policy
where applicable, the original CM finally and physical handler result. Sync
failure retains Ready or Failed(original); async failure closes the pool first,
writes Failed(new), then invokes/samples/commits/returns Dead. This appends the
first new MuxFinished for these initiator branches and clears trace counters.
Previously queued awake/promote events survive. The captured initiator result is
retained as throwing; neither a normal first-leg return nor DeltaQ invocation
is invented. These observations remain conditional tracer/provider/policy inputs.

`Negative/MuxInitiatorTraceCM.Scenario` covers both clean and error origins with
CM snapshot, late read, cancellation request,
actual initiator-trace async receipt/acknowledgment, collective wait, actual pool
close and CM finally/result publication. DeltaQ receipt cannot substitute for
this first-leg receipt. The collective wait is blocked before pool close, after
pool close and after cleanup until the handler's physical result is available.
The final wait is certified by the existing `PhysicalWait` theorem.

The clean synchronous case strengthens the conditional Ready-after-exit finding:
a real live responder in the same pool is physically cancelled/joined while mux
status remains Ready and source trace metadata retains one hot responder and its
running protocol. No new IG completion/Dead notification is emitted on this path;
the earlier awake/promote queue remains. This refutes an unconditional invariant
that physical handler completion always clears responder metadata or changes mux
status under the admitted observations. It is **not a confirmed deployment bug,
a deadlock witness or a full shutdown theorem**. Concrete tracer/policy contracts,
IG/PSA recovery, overlapping-key reachability and implementation replay remain
necessary before claiming a source-code defect. The physical handler adapter
still has not been integrated with whole PeerSupervision/Subsystem/Server history.

Validation on 29 October: Agda 2.8.0 checked the new selection proof and both
acceptance endpoints serially at a 4 GB heap limit. The standalone effects check
passed before adding snapshot-terminal and explicit metadata facts; the later
CM check freshly rechecked that final effects module transitively. The final CM
check then passed for the generic clean/error-origin scenario. Final logs have
Checking lines and no warnings:

```sh
agda ConnectionManagement/Properties/MuxInitiatorTrace.agda +RTS -M4G -RTS
agda ConnectionManagement/Negative/MuxInitiatorTraceEffects.agda +RTS -M4G -RTS
agda ConnectionManagement/Negative/MuxInitiatorTraceCM.agda +RTS -M4G -RTS
```

Evidence: `/tmp/cm-review-20261029/initiator-selection.log`,
`initiator-effects-2.log`, `initiator-CM.log` (includes final effects Checking)
and `initiator-CM-both.log`. An initial fixture-type scoping error was corrected
to the kernel's existing ThreadPhase/ClosePC names before the passing checks.
No proof statement/scenario was weakened, hole/postulate introduced or safety
check disabled. Three-file proof audit found zero findings; source/documentation
whitespace and new-file EOF checks passed. Unchanged baseline endpoints were
not rebuilt separately; imports were checked transitively. No Haskell replay,
source-pin change, commit or push. The work remains uncommitted after 43e0e2b;
`.claude` is untouched.

Next executable obligation: observed cancellation/failure during the post-close
async catch's Failed/Dead actions. Preserve the closed snapshot and any already
written status/committed callback effects; a new exception from that catch exits
to outer cleanup rather than recursively re-entering the same catch or inventing
a returned Dead trace. Earlier allocation/publication, other ignored callbacks
and child-finalizer/helper scopes, then outer Server/IG/governor composition and
admission quiescence still remain. G0–G5, CM-I4c and SI4/SI5 remain open.


## Fifteenth increment: interruption of the post-close async catch

Source rechecking refined this obligation before adding transitions. The local
io-classes 1.8.0.1 archive delegates `MonadCatch IO.catch` to IO.catch. Network-mux
at the unchanged pin requires io-classes `^>=1.8`; ConnectionHandler.hs:378–380
and :450–452 explicitly unmask Mux.run. A catch entered from unmasked IO executes
its handler masked interruptibly. Therefore a new async exception cannot be
freely delivered between the catch's nonblocking Failed/status/read operations.
The actual blocking operation or a tracer unmasking contract must justify receipt.
The current profile covers an observed blocking caller tracer and a full-queue
retry in the IG Dead transaction. It does not claim every custom tracer blocks.

`MuxCatchUnwind` wraps the existing physical DeltaQ/handler chain. It admits
replacement only for an async catch's pending Dead callback with the actual pool
closed, no outer exit frame, and mux status matching the caught async exception.
A blocking caller-tracer observation is before IG's active read (or the opaque
caller trace on a no-IG attachment). The retry site requires captured-active
Dead and failure of the actual bounded `writeMessage`, not an arbitrary pending
STM. Ordinary status steps, a nonfull queue, and returned Dead reject delivery.
Synchronous caller-tracer throwing uses the existing throw-point guard.

The interruption record retains the original caught Fault, actual current Dead
callback, and replacement cause. Selection changes only metadata, keeps the
closed physical pool/source/queue/counters intact, and goes directly to outer
buffer exit. The same catch is not recursively entered: it does not rewrite
Failed(new), invoke another Dead or invent old Dead return. CM receipt executes
the actual acknowledgment operation. The lower legacy sync observation is blocked
in this adapter so it cannot discard the new retained catch evidence.

`Properties/MuxCatchUnwind` projects all actions/executions to existing source and
physical-pool paths, lifts initialized capture/supply, and retains the physical
CM wait certificate. `select-is-local` and `observe-keeps-underlying` establish
metadata-only selection without manufacturing cleanup. The generic CM projection
peels the adapter at an abstract action before specializing the real nested wait,
keeping the full source dispatcher out of normalization.

`Negative/MuxCatchUnwind` lifts the actual initialized initiator clean/error
failure prefixes, closes responder/demuxer/muxer, writes the caught async Failed
status and invokes Dead. A replacement async exception at an observed blocking
caller tracer exits through the real buffer/provider and original CM finally to
physical handler completion. Both origins retain Failed(caught), the pending Dead
callback and old IG queue; the replacement async exception is the handler result.
Controls reject recursive Failed/Dead, fabricated callback return, delivery at an
ordinary STM or after return, and queue delivery with room. An injected full-queue
snapshot proves retry before masked delivery and source retention; that control
is conditional, not an initialized full-queue reachability claim. A synchronous
first-leg replacement control also retains the caught/abandoned metadata.

`Negative/MuxCatchUnwindCM` drives CM snapshot/read/send while that catch tracer
is pending, actual receipt/acknowledgment, outer cleanup and physical result, for
both completion origins. The collective wait is blocked after receipt and after
cleanup until the real result is published. Its final `PhysicalWait` certificate
uses the existing actual coordinator/physical handler boundary.

`SourceReplay/CatchMaskProbe.hs` passed under GHC 9.6.7 / base 4.18.3.0. It checks
pool-close → MaskedInterruptible catch → outer-finally, with replacement
UserInterrupt escaping a blocked catch handler. It is an IO semantics probe,
not a concrete Mux/IOSim replay, source refinement or deadlock witness. See the
SourceReplay README for reproduction and scope. Enclosing mask/provider behavior,
custom tracer operations, admission quiescence and outer composition remain
explicit limitations. This increment adds coverage, not a deployment bug claim.

Validation on 29 October: all four new Agda modules passed serially with Agda
2.8.0. Each final log contains its own Checking line and no warnings:

```sh
agda ConnectionManagement/MuxCatchUnwind.agda +RTS -M2G -RTS
agda ConnectionManagement/Properties/MuxCatchUnwind.agda +RTS -M4G -RTS
agda ConnectionManagement/Negative/MuxCatchUnwind.agda -v tc.decl:10 +RTS -M6G -RTS
agda ConnectionManagement/Negative/MuxCatchUnwindCM.agda +RTS -M6G -RTS
```

The initial aggregate proof check exhausted 4 GB before the abstract CM
projection was factored; equality/case-split repairs then preceded the successful
standalone property check at 4 GB. The initialized acceptance closure exhausted
4 GB in both aggregate and standalone checks. With 21 GB available, the complete
unchanged acceptance histories passed at 6 GB, followed by the CM endpoint.
No scenario or theorem was weakened and no safety option disabled. The failed
logs are retained alongside the passing logs: `catch-runtime.log`,
`catch-properties-3.log`, `catch-acceptance-6g.log`, `catch-CM-6g.log` under
`/tmp/cm-review-20261029/`. Seven-file local proof audit (including the preceding
uncommitted initiator increment) found zero findings; new-file EOF/whitespace
and documentation diff checks passed. Dependency assumptions were not replaced
by a term-level external axiom audit. GHC `-fno-code -Wall` checked the boundary
probe without warnings, and its execution passed. Unchanged baseline endpoints
were not rebuilt separately; imports were checked transitively.

No concrete Mux/IOSim replay, source-pin change, commit or push. These changes
and the preceding initiator-tracer increment remain uncommitted after 43e0e2b.
`.claude` is untouched. Next: source-audit and model pre-publication failures at
returnedSuccess/handleAllocated, retaining the real promise/catch/finally order
and physical handler identity rather than inventing successful publication.
Other ignored callbacks, child finalizer/helper failures and outer Server/IG/
governor composition/admission quiescence remain. G0–G5, CM-I4c and SI4/SI5 remain
open; none of these local paths derives universal/full-system shutdown.


## Sixteenth increment: failures before successful promise publication

**Source-fidelity correction (30 October):** the resolved typed-protocols
1.2.1.0 driver forces handshake results before return. The pinned HandshakeResult
NFData instance forces application WHNF and version data NF inside the narrow
handshake catch; NodeToNodeVersion and NodeToNodeVersionData derive NFData.
The positive strictHandle/handleSync scenario has been removed. That observation
site now rejects both sync and async failures, with an actual initialized
post-allocation prefix retained as a negative control. The four tracer cases
remain. No generic theorem statement was changed. This corrects the model's
source profile; historical five-case checks do not validate the removed case.
See the [forcing contract probe](SourceReplay/HandshakeForcing.hs) and
[reproduction/scope](SourceReplay/README.md#handshake-result-forcing-contract-probe).

**Uncommitted after 9ecdfb8.** The four corrected initialized tracer-failure
histories and the CM endpoint now pass. Real readCounters steps and exact
awaitResult certificates replace the earlier counter-PC refusal control. A
separate raw-dispatcher lemma establishes the empty-promise read retry at that
actual PC; physical result availability at the same waits is also proved.

The source audit at the unchanged pin separates restored handshake execution
from the following masked continuation. ConnectionHandler.hs:337–346 and
:414–423 catch exceptions from **runHandshake** and write HandlerError. They do
not cover the successful continuation. TrHandshakeSuccess (:353/:430), control
TVars/counters, Mux.new (:370/:438), the strict Handle (:371–376/:443–448), and
successful writePromise (:377/:449) occur afterwards. Mux.hs:140–146 emits
TraceNewMux before allocating its protocol map/queue/status. Handle fields are
strict (ConnectionHandler.hs:119–124). The outer classifier (:293–309) traces
and rethrows according to policy, without writing the handshake promise.

Core.hs:584–592 installs the real CM finally around the whole handler. Cleanup
terminates/purges the captured entry and closes the socket, but does not fill the
promise. The fresh inbound and outbound callers readPromise directly at :897
and :1584; those reads do not race the physical Async result or connVar. Exact
Mux, ConnectionHandler and Core Git exports were rechecked before extending
these claims. This source boundary motivates candidate **CM-PUB1** below.

`MuxPublicationUnwind` wraps the current catch/physical-handler chain. It admits
observed sync failures from TrHandshakeSuccess and TraceNewMux at
returnedSuccess. Async receipt is admitted only as an observed blocking operation
in either tracer. The strictHandle site is always rejected: no new payload
evaluation is justified at that later pure constructor. No ordinary masked allocation/status step is
invented as a delivery site. Partial private TVar allocations and opaque tracer
internals are outside this atomic allocation profile.

Selection requires the actual owner/frame, matching current HandlerStart, an
empty promise, no old fault/outer exit, pre-publication startup and no pool
handles. It retains the complete original unpublished frame/site/outcome,
installs the existing outer exit frame, and does not publish success or error,
enter a buffer/pool, close a fictitious pool, create a handler or attach the
post-publication async mux catch. Sync exceptions enter the real classifier;
async exceptions bypass it. The failed owner's old allocation/publication and
controller actions are sealed while other actors and its real outer cleanup
remain executable. Successful lower allocation remains an observed normal
operation, not a theorem that concrete caller tracers cannot throw.

`Properties/MuxPublicationUnwind` projects actions/executions to actual source
and physical-pool paths, lifts initialized capture/supply and certifies the real
CM physical-result wait. `Negative/MuxPublicationUnwind` supplies initialized
outbound histories for both tracer sync/async failures. They use actual
creation/negotiation. A separate initialized allocation prefix proves rejection
of both sync and async strictHandle observations. Each continues through policy where applicable, original CM
finally, socket/map cleanup and physical handler result; no buffer or pool is
entered. Each then executes the actual counter read, reaches awaitResult, and
checks the empty-promise read. The captured unpublished frame survives.
`Negative/MuxPublicationUnwindCM` adds real CM snapshot/read/send, observed
TraceNewMux blocked-tracer receipt/ack, finally and collective physical wait.
The promise wait and Async wait remain distinct. The CM history advances the
caller before final CM completion, rather than inserting a successful API action
after the CM scope closes. Properties/PromiseWait.outbound-read-retries requires
the exact captured awaitResult frame and empty promise, and targets O.advance
directly; the claimed retry is not caused by an adapter's controller guard.
MuxPublicationFixtures contains data only, avoiding imports of large existing
negative-control endpoints; all four tracer cases and their actual birth steps remain.

**CM-PUB1 (conditional source-profile candidate):** a pre-publication failure
outside the handshake catch can leave an empty promise after the real handler
physically completes and CM cleanup removes its entry. A caller reading that
promise still blocks. This is a finite initialized model/source-profile finding,
not a universal deadlock or a confirmed deployment defect. Concrete tracer
fault contracts, production policy, external governor/Server cancellation and
an actual pinned implementation replay remain to be checked. The current
initialized acceptance is outbound; the generic adapter also selects inbound
frames, but no corresponding inbound initialized execution is claimed here.

Additional source audit: CM Types.hs:289–317 implements readPromise with
readTMVar, and writePromise with tryPutTMVar/throwSTM; neither the reviewed
Core finally nor ConnectionHandler uses forcePromise to repair this failure.
PeerStateActions.hs:784–795 directly tries acquireOutboundConnection, and
EstablishedPeers.hs:570–574 directly calls establishPeerConnection with an
explicit timeout TODO. These reviewed functions do not supply an establishment
timeout. This observation does not exclude external scope cancellation or other
runtime recovery; concrete replay and full ownership composition remain needed.

Historical validation on 29 October, before the strictHandle correction: the corrected initialized endpoint passed with Agda
2.8.0 at 6 GB, freshly checking Negative/MuxPublicationUnwind and its new data-only
MuxPublicationFixtures dependency. The corrected CM endpoint then passed at 6 GB,
freshly checking itself and Properties/PromiseWait. Both logs have Checking
lines and no warnings:

```sh
agda ConnectionManagement/Negative/MuxPublicationUnwind.agda +RTS -M6G -RTS
agda ConnectionManagement/Negative/MuxPublicationUnwindCM.agda +RTS -M6G -RTS
```

The unchanged runtime and generic source/pool/capture/supply properties were
previously checked at 4 GB and 6 GB respectively and confirmed through imports
here. Their prior logs are publication-runtime-4g.log and
publication-properties-6g.log. The earlier runtime 2 GB, generic-property 4 GB
and old aggregate acceptance 6 GB heap failures are retained. Earlier syntax and
case-splitting repairs preceded these checks. A standalone PromiseWait check
initially lacked the existing DecEq-Id instance import; after adding that import,
the lemma passed transitively in the corrected CM check. All checks in this
continuation were serial. No generic theorem was weakened, case removed,
postulate/hole added or safety option disabled.

Final evidence is in /tmp/cm-review-20261029/publication-corrected.log,
publication-CM-corrected.log and publication-final-audit.log. Six-file local proof
audit found zero findings; source/documentation whitespace and new-file EOF checks
passed. No unrelated baseline rebuild, concrete implementation replay, full
source refinement, source-pin change, commit or push. The dated presentation
remains an unchanged snapshot of the earlier WIP checkpoint.

Next executable obligation: investigate CM-PUB1 using the actual pinned
ConnectionHandler/CM and concrete tracer/payload/policy contracts; establish a
corresponding inbound witness and account for caller/governor/Server lifetime
and recovery before stronger liveness claims. Private allocation and duplicate
publication failures, other ignored callbacks and child/helper/finalizer scopes
remain, followed by physical/Subsystem/Server composition, admission quiescence
and derived full shutdown. G0–G5, CM-I4c and SI4/SI5 remain open.


30 October handler-body replay: SourceReplay/PublicationHandler.hs passed ten
synchronous cases across real inbound/outbound production makeConnectionHandler
with encoded queue-bearer handshakes. TrHandshakeSuccess, TraceNewMux and lazy
protocol-element allocation faults leave the real promise empty after handler
Async result; early handshake payload failure writes Left, late TraceStarting
failure follows Right. Delegating STM writer observations preserve original
semantics; exact injected fault is checked at the real classifier. This validates
the allocation fault location separately from the rejected strictHandle case.
The allocation fault is not yet a positive Agda scenario. Actual CM finally,
caller/map/socket cleanup, ThreadFinished ordering, async tracer receipt and
outer recovery are not included; no stronger liveness claim follows. Scope and
reproduction: SourceReplay/README.md. Final runghc -Wall exited 0 without warnings.


30 October actual-CM follow-up: SourceReplay/PublicationCM.hs passes 14 IO cases
using the real production handler and both CM entry points. Pre-publication sync
and observed blocked-tracer async faults leave a pending STM caller after actual
GHC handler ThreadFinished, empty full CM map and one synthetic socket close.
Caller counter callbacks (two outbound/one inbound) certify the fresh readPromise
boundary; the earlier counter-PC control is not reused. Early payload Left and
late publication Right controls return, with the late cleanup race permitted.
All writer operations are delegated atomically and force count is zero. Async
receipt is sent by the harness at an actually blocked MaskedInterruptible tracer;
CM's shutdown snapshot/send traversal and outer caller recovery remain open.
Final runghc -Wall exit 0, no warnings. The earlier IOSim attempt exited 1 on the
pure payload's host evaluation after two sync tracer passes; actual IO avoids
altering production evaluation. SourceReplay/README.md records precise scope.

Agda correction acceptance update: the first downstream 6 GB run ended with heap
exhaustion (exit 251), not a type error. Keeping head/frame/action functions split
by the four constructors restores a neutral case index in generic proofs, avoiding
eager normalization of the full source fixture. A fresh corrected initialized
endpoint check is running at 6 GB; final acceptance remains pending until it and
the downstream CM endpoint finish. No generic theorem type was changed.


## Seventeenth increment: allocation failure and initialized inbound history

**30 October, work in progress.** Production-handler and actual-CM IO replays
validated a lazy protocol-element failure *inside* Mux.new after TraceNewMux and
before allocation returns. MuxPublicationUnwind now exposes muxAllocation at
returnedSuccess for sync observations only. It rejects async delivery there and
rejects retroactive allocation failure after handleAllocated. strictHandle remains
rejected for both outcomes. This is a distinct source location, not a renamed
strict-constructor case. Private partial TVar allocation remains abstract.

The outbound acceptance and its CM specialization now range over five cases:
four tracer outcomes plus allocationSync. The new inbound data-only fixtures and
Negative/MuxPublicationInbound build an actual nine-step prefix: seven admission
operations (including fork and real counter read), enterHandshake, and negotiate.
They retain the actual inbound birth and a one-protocol bundle, then describe all
five policy/finally/cleanup/result paths. The intended postconditions include
empty promise, entire map purged, captured socket closed, physical handler result,
retained unpublished capture, and the exact awaitHandshake caller continuation.
Properties/PromiseWait.inbound-read-retries checks the raw Machine.advance read,
without adapter guards. That local retry does not prove permanent blocking.

Validation so far: runtime, new inbound promise lemma and inbound fixtures each
freshly passed serial Agda 2.8.0 checks at 4 GB. Eight-file proof audit has no
findings; whitespace checks pass. The previous two corrected outbound acceptance
runs exhausted 6 GB (both exit 251), not a type diagnostic; preserving neutral
case indices alone did not make 6 GB sufficient. Resource inspection showed
20 GB available. The new full inbound endpoint is RUNNING at 8 GB, session 90172;
/tmp/cm-review-20261029/publication-inbound.log. It rechecks generic properties.
No full endpoint success is claimed yet. Outbound and CM endpoints must then be
rechecked serially against the new allocation-aware runtime. No generic theorem
type was weakened, or axiom/hole/unsafe pragma added. The actual-CM replay remains
14 passing IO cases; no replay was rerun for these Agda-only changes.

After acceptance, continue CM-owned shutdown delivery and caller/governor/Server
recovery/ownership integration. Inbound CM snapshot/wait composition is not proved
by the standalone inbound history. G0–G5, CM-I4c and SI4/SI5 remain open.


30 October acceptance/replay update: the full five-case inbound initialized
endpoint and generic MuxPublicationUnwind properties passed at 8 GB (session
90172 exit 0, own Checking lines, no warnings). Runtime, PromiseWait and inbound
fixtures retain their fresh 4 GB passes. The aggregate outbound+CM endpoint is
now checking serially at 8 GB, session 53625, log publication-allocation-CM.log;
it must finish before claiming those updated endpoints accepted.

PublicationCM.hs now passes **18** actual-CM IO cases. Four new cases cover
CM-owned shutdown at either pre-publication blocked tracer for each provenance.
They require an exact live singleton map, blocked handler and pending caller;
then cancel/join the caller and verify the map/handler unchanged before CM scope
exit. The real Core finally performs snapshot/send/wait. After return, zero
promise writes, one close and GHC handler ThreadFinished are required. Lifecycle
order is observed-open/caller-cancelled/cm-shutdown/socket-close/after-with.
No CM API is used after its scope; no harness throwTo targets the handler in
these four cases. SourceReplay/README.md records the two different observation
phases. Final repository runghc -Wall exits 0 without warnings; log
publication-CM-owned-final.log. This establishes finite profile replays, not a
live escaped caller, permanent stall or full shutdown theorem.

A corresponding inbound CM snapshot/receipt/finally/physical-wait witness is
prepared in Negative/MuxPublicationInboundCM.agda. It has not been checked yet;
queue it after the live outbound/CM check. Its retained caller PC is a logical
capture, not a certificate of a live caller job after CM closure. Outer
caller/governor/Server cancellation/ownership integration remains open.


**New Server fidelity prerequisite (30 October):** source review and actual
Server replay show that its admission workers are raw async children with
ignored handles (Server.hs:239–254), outside its scoped action/IG/accept-loop
join tree. PublicationServer.hs passes six actual Server/IG/CM/handler cases:
five pre-publication faults leave its admission worker blocked after Server.with
returns; early payload Left is the finishing control. Handler completion, empty
CM map, exact caller read boundary and listener closure are checked. The API's
all-server-threads-stop comment (:132–133) has this injected-contract exception.
ThreadId instrumentation can affect GC/deadlocked-STM detection; permanent leak,
production occurrence and universal deadlock are not proved. The harness cleans
up its observed workers. SourceReplay README and SI4 audit contain exact scope.

The 18-case direct-CM replay's caller cancellation is explicitly harness-owned.
It must not be transferred to Server as a source fact. Next Server composition
must model independent raw admission Async actors, their original onException/
Disconnected close branches and missing join, before SI5 can derive completion.
Rules/CallerCancellation currently handles outbound acquisition/release only;
its noCaller branch does not supply physical inbound admission cancellation.
Do not equate a stored logical awaitHandshake PC with a live physical worker.


## Acceptance checkpoint and next Server layer — 30 October

All current pre-publication Agda endpoints now pass with their own Checking lines
and no warnings. Runtime, PromiseWait and new inbound fixtures passed at 4 GB;
full initialized inbound and generic properties passed at 8 GB. Then the aggregate
outbound/CM endpoint freshly checked its five-case outbound endpoint/data fixtures
and passed at 8 GB (session 53625 exit 0). Finally the new inbound CM witness
passed at 8 GB (session 46265 exit 0). Commands:

```sh
agda ConnectionManagement/Negative/MuxPublicationInbound.agda +RTS -M8G -RTS
agda ConnectionManagement/Negative/MuxPublicationUnwindCM.agda +RTS -M8G -RTS
agda ConnectionManagement/Negative/MuxPublicationInboundCM.agda +RTS -M8G -RTS
```

Logs: publication-inbound.log, publication-allocation-CM.log and
publication-inbound-CM.log in /tmp/cm-review-20261029. The two 6 GB heap failures
are historical failed runs; neutral-case indexing alone did not suffice there.
Nine-file local proof audit reports zero findings, and whitespace/EOF checks pass.
Generic theorem types remain unchanged; no new trust assumption/unsafe option.
This is model proof evidence, separate from 18 actual-CM and six actual-Server
IO replay cases. No checker remains running at this checkpoint.

Next SI4 slice must represent Server's **raw admission Async workers**, rather
than importing the chosen caller scope of the direct-CM harness:

- Observe actual accepted-socket handoff/fork before recording a physical worker;
  do not adopt existing admission PCs as physical Async history.
- Keep its includeInbound result/error close branches and physical result separate
  from handler cleanup. A stored awaitHandshake PC is not a live-thread proof.
- Close only the owned Server action/IG/accept-loop scopes at their real boundary.
  The source has no admission registry join; preserve a finite initialized
  counterexample to deriving all-worker completion from those scope certificates.
- Use PublicationServer.hs's finite observation as the source check. External
  cleanup/GC/runtime recovery are separate inputs; production governor/PSA scopes
  still require composition with the physical handler model before SI5.

This priority follows verified source behavior and prevents an incorrect
structured-admission-ownership assumption. G0–G5, CM-I4c and SI4/SI5 remain open.


## Eighteenth increment: raw admission workers and owned Server scope return

**30 October, uncommitted.** [ServerAdmission](ServerAdmission.agda) wraps the
physical publication-unwind chain with actual raw admission-worker history.
`initial` refuses existing admission/socket slots. An observed successful
accepted-socket handoff/fork inserts both the source continuation and physical
worker, checking fresh caller, socket and reserved handler identities. Historical
outbound results and raw-worker identities cannot be recycled as new callers.
No old logical admission is adopted as an Async birth.

The worker's calling, close, body-exit and result-publication phases are distinct.
Normal Connected returns need no worker close; Disconnected invokes its captured
socket close. A later observed exception at awaitHandshake also invokes that
close. A failed Disconnected close enters the original onException cleanup; a
cleanup-close failure replaces the propagated exception. Server close attempts
are counted separately from CM handler cleanup; uncertain close outcomes remain
explicit. Earlier admission/map-lease/fork-failure physical unwinds are not yet
covered by this adapter. Exited workers cannot resume old caller operations or
reuse their identities for outbound calls.

| Source portion | Implemented scope | Still open |
| --- | --- | --- |
| Server raw admission async | Explicit successful handoff/fork and immutable captured request; post-handshake return/exception close and result phases | Accept/getLocalAddr/tracer/fork errors before handoff; earlier admission unwind branches |
| Owned action/accept/IG scopes | One initialized listener, normal action wins; accept receipt, listener close/result/join, stopped trace and returned-action cancel/join | Multiple listeners, other race winners, owned helper/finalizer/tracer failures |
| IG scope cleanup | Actual deactivateIG/flushOnExit shared transitions, exited/inactive checks, empty published registry | IG CM-call cancellation/unwind and nonempty remote-state exit tracing |
| CM outer finally | Actual shutdown snapshot/traversal/delivery/result-wait steps after IG join; real finishClose required | Full PSA/governor/Server composition and admission quiescence |

The owned infrastructure is an explicit **post-setup scenario boundary**. This
is not a whole-node startup/refinement theorem. The first IG-exit profile refuses
receipt with pending inbound-release/remote-call frames; it does not discard an
unfinished CM call. Listener close and trace return are observed successful
operations, with no eventuality claim. Existing raw workers remain independent
after scope return; no admission registry join or global freeze is invented.

`Properties/ServerAdmission` proves that any finite scope-only execution retains
the exact raw-worker table, including when scope plans perform actual IG writes.
Inherited physical steps also retain it; the guarded source path has a checked
roundtrip. A permission-indexed lift reuses lower physical executions rather
than normalizing their whole dispatchers again. These statements do not yet lift
capture/supply/resource invariants through all the new handoff/close writers.

`Negative/ServerAdmission.initialized` performs two explicit handoffs to recreate
the existing two-admission fixture, then lifts the checked NewMux sync-failure
path and executes the owned Server/IG/CM cleanup. It proves handler result
availability and Server return while **worker zero itself** has no result, retains
its actual physical birth and is at its empty-promise awaitHandshake read. The
second accepted worker is not the sole reason for the unfinished-worker result.
`no-universal-all-worker-completion` refutes deriving all raw results from those
scope certificates in this profile. Map purge, listener close and raw read retry
are separate observations. No fake result, unread return, new post-close handoff
or premature Server completion is admitted.

A further checked suffix supplies an observed async exception, closes the raw
worker's socket and publishes its result. Publication before that close and old
caller/identity reuse afterwards are rejected. This represents the replay's
explicit cleanup input and leaves room for runtime recovery; it proves no
permanent leak, universal deadlock or GC behavior.

Validation: initial runtime and generic properties passed at 4 GB. After actor
history/IG-exit guard refinements and recovery controls, the final endpoint freshly
checked all three modules serially at 8 GB, exit 0, no warnings:

```sh
agda ConnectionManagement/Negative/ServerAdmission.agda +RTS -M8G -RTS
```

Log: /tmp/cm-review-20261029/server-admission-negative-final.log. Initial syntax
and missing Bool-import diagnostics were repaired before acceptance. Three-file
local proof audit: zero findings; whitespace checks pass. No postulates, holes,
unsafe options or weakened prior theorem types. The earlier pre-publication
endpoints remain accepted and unchanged. Native CM/Server replay artifacts were
not changed or rerun for this Agda-only increment. No jobs remain running.

The full SI5 claim is **not** replaced by an easier conditional completion
statement. This counterexample is an obstruction to inferring all-worker
completion from owned scopes alone. Extend physical admission failure coverage,
new-writer invariants, IG-call/nonempty cleanup and parent PSA/governor composition;
keep any additional quiescence/fix profile explicit. G0–G5, CM-I4c and SI4/SI5
remain open. No whole-source or whole-node shutdown/refinement is established.


## Nineteenth increment: initialized Server admission prefix exits

Checked 30 October 2026. This completes acceptance of the prefix runtime committed
in `093cbe5`; the earlier increment's validation predates that runtime extension.
No runtime rule or prior theorem statement was changed for this acceptance work.

Pinned source was rechecked in the clean network checkout at
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`: Core.hs:801–891 distinguishes normal
hard-limit return from forbidden selection and handler-fork exceptions;
Core.hs:2366–2380 restores the saved map on exception without undoing committed
entry writes. State.hs:193–200 retains the lazy handler reference for `mfix`.
Server.hs:239–254 closes Disconnected sockets and uses a separate `onException`
cleanup close. Failure of the normal close can therefore cause a second attempt;
failure of the exception-cleanup close replaces the exception and exits.

[Negative/ServerAdmissionPrefix](Negative/ServerAdmissionPrefix.agda) aggregates
three independently checked branches, backed by data-only flat snapshots and
small shared trace combinators. Internal adapter aliases are private, following
the existing fixture convention. Every trace starts from the real wrapper
initializer with empty raw admission/socket tables and two explicit successful
handoffs; no old logical worker is adopted as physical history.

| Branch | Initialized evidence |
| --- | --- |
| `HardLimit.initialized` | Both requests have hardLimit=1 and are handed off before either CM call. The first installs a real unnegotiated handler; the second counts it, restores/publishes the map, closes once and publishes a normal result. The first entry and physical handler remain, with no second handler birth or promise allocation. |
| `ForkFailure.initialized` | The first fresh-entry path fails before handler birth. The saved empty map is restored while entry/promise allocations and supplies remain. One successful close precedes the raised synchronous worker result; handler stores/results and the handshake promise remain empty. |
| `Forbidden.initialized` | Both requests have hardLimit=2 and the same key. The first executes actual modeled negotiation, allocation, publication and caller completion to inboundIdle. The second counts, allocates its promise, rejects selection, restores and closes once before publishing the synchronous exception, preserving the original entry, handler and socket. |

Four additional initialized histories cover a failed hard-limit normal close
followed by cleanup success or failure, and exception-cleanup close failure for
the fork/forbidden branches. They distinguish uncertain socket outcome, attempt
count, body exit and result publication. Cleanup success retains the first close
exception; cleanup failure publishes the replacement without another retry.
Negative controls reject close/return observations before restoration, premature
worker results, the inherited raw lower-close shortcut, and mismatched handoff
limits. Failed closes do not falsely finish the logical admission.

Validation ran serially with Agda 2.8.0 from the standalone library root. All
listed commands exited 0, with their own `Checking` lines and no warnings:

```sh
agda ConnectionManagement/Properties/ServerAdmission.agda +RTS -M4G -RTS
agda ConnectionManagement/Negative/ServerAdmission.agda +RTS -M8G -RTS
agda ConnectionManagement/Negative/ServerAdmissionPrefixHardLimit.agda --profile=definitions +RTS -M8G -RTS
agda ConnectionManagement/Negative/ServerAdmissionPrefixFork.agda +RTS -M8G -RTS
agda ConnectionManagement/Negative/ServerAdmissionPrefixForbidden.agda +RTS -M8G -RTS
agda ConnectionManagement/Negative/ServerAdmissionPrefix.agda +RTS -M8G -RTS
```

Logs are in `/tmp/cm-prefix-20261030/`: `properties.log`, `server-existing.log`,
`hard-limit-private.log`, `fork.log`, `forbidden.log` and `aggregate.log`.
The final aggregate freshly rechecked all three branch modules and Support after
EOF whitespace cleanup; Fixtures had freshly checked in the successful hard-limit
command. Six-file local proof audit: zero holes, postulates or unsafe-option
findings. Tracked and new-file whitespace checks pass. This is a local source
audit, not a term-level audit of all imported assumptions.

Initial syntax/import repairs preceded these successes. An earlier combined
8 GB run exhausted heap (exit 251). Two subsequent slow checks were stopped
(exit 130) while flattening snapshots, splitting branches and making the internal
adapter aliases private. Those runs are not passing evidence; the final split
checks above establish acceptance. No checker remains running.

Limits: the established owned-infrastructure/single-listener profile remains.
The same-key transport input is abstract, without OS tuple-reachability evidence.
Failed-fork unresolved lazy-reference evaluation is outside this profile. Async
close failures are observed interruptible-close outcomes, not an assertion that
every masked region admits cancellation. No native replay was changed or rerun,
and no new prefix replay, production patch, permanent leak or whole-node shutdown
result is claimed. Broader async lease/tracer unwinds and other scope winners
remain open. Next: lift capture/supply/resource invariants through the new handoff
and close writers, then pending IG-call/nonempty-exit handling and shared
Server/PSA/governor composition. G0–G5, CM-I4c and SI4/SI5 remain open.


## Twentieth increment: Server handoff and close invariants

Checked 30 October 2026. No runtime rule, guard or existing theorem statement was
changed. This extends the existing predicates through the Server admission
wrapper's new writers and every implemented scope/worker action.

[Properties/ServerAdmissionInvariant](Properties/ServerAdmissionInvariant.agda)
proves exhaustive step and finite-execution preservation for a source predicate
given preservation of lower steps, accepted handoffs and socket writes. The
generic layer is parameterized over lower preservation. The concrete
[ServerAdmissionInvariants](Properties/ServerAdmissionInvariants.agda) supplies
all three proofs; no new unproved preservation assumption is left in its public
capture/supply/resource endpoints. Inherited effects reuse the existing
publication-to-outbound-machine trace projection; bookkeeping observations keep
the source unchanged, and successful prefix closes use their actual lower step.

| Public statement | Exact scope and premises |
| --- | --- |
| `captures-step`, `captures-exec` | Preserve unchanged `OutboundRuntimeCapture.Captures`, covering all stored pending outbound acquisition captures, from an existing capture certificate. `from-initial-captures` derives it for initialized outbound configurations without a supply premise. |
| `supply-step`, `supply-exec` | Preserve unchanged `OutboundRuntimeSupply.Valid`, including capture validity and entry/promise allocation bounds. `from-initial-supply` requires only initial shared-world `SupplyBounds`, deriving empty-runtime capture validity from `O.initial`. Bounds alone are not claimed sufficient for arbitrary injected acquisition frames. |
| `For q captured.{step,exec}-preserves` | Retain the exact original handler descriptor plus existence of its stored entry/socket records. Public `resources-step`/`resources-exec` use unchanged `Resources`; no supply, uniqueness, ownership or scheduling premise is added. Closed/uncertain socket values still count as stored records, not live ownership. |

Handoffs change only admissions and sockets, so acquisition frames and allocation
bounds are definitionally unchanged. Socket replacement retains stored resource
identities using the existing `HandlerResourceFacts.socket-write` lemma. Source
steps use the established outbound capture/supply/resource preservation proofs.
This includes selected IG deactivation/flush and actual CM shutdown actions; it
does not widen the runtime's pending-IG-call or nonempty-exit guards.

[Negative/ServerAdmissionInvariants](Negative/ServerAdmissionInvariants.agda)
applies the theorem to all seven initialized prefix/close histories, the earlier
initialized Server-return counterexample and its recovery suffix. An additional
initialized caller-cancellation/close/result history closes the same socket as an
existing handler while preserving its historical resource records. An explicitly
conditional fixture carries a nonempty, well-formed outbound acquisition capture
through enabled handoff/close writers, with capture/supply/resource certificates;
no initialized outbound history is fabricated for that fixture. An initializer
with an already unbounded promise list refutes unconditional initial supply,
retaining the real theorem's initial-bounds premise. These are invariant controls,
not source-defect or progress claims.

Validation ran serially with Agda 2.8.0 from the standalone library root. These
commands exited 0 with their own `Checking` lines and no warnings:

```sh
agda ConnectionManagement/Properties/ServerAdmissionInvariant.agda +RTS -M4G -RTS
agda ConnectionManagement/Properties/ServerAdmissionInvariants.agda +RTS -M8G -RTS
agda ConnectionManagement/Negative/ServerAdmissionInvariants.agda +RTS -M8G -RTS
```

Accepted logs: `/tmp/cm-server-invariants-20261030/{lift-cases,invariants-direct-final,negative}.log`.
Existing lower resource components also freshly checked transitively. Existing
`Negative/ServerAdmission.agda` and `Negative/ServerAdmissionPrefix.agda` commands
with `+RTS -M8G -RTS` exited 0 as cached regressions, with no `Checking` lines;
logs are `server-existing.log` and `prefix-existing.log` in the same directory.
Three-file local proof audit: zero holes, postulates or unsafe-option
findings; tracked/new-file whitespace checks pass. Imported assumptions were not
given a new term-level axiom audit.

Preliminary results remain distinct: the first broad generic closure exhausted
its 4 GB heap (exit 251); wildcard rejection proofs produced unsolved constraints
(exit 42) and were replaced by exhaustive constructor cases. A slow broad
publication-proof alias instantiation at 8 GB was stopped (exit 130); direct calls
to the two needed projection/initialization lemmas removed that expansion. One
implicit projection-parameter error (exit 42) was corrected before final success.
No native replay or full baseline suite was rerun. The pinned checkout remains
clean and the source pin unchanged. All checker handles are terminal.

Next: inspect and implement pending IG CM-call cancellation/unwind and nonempty
IG exit, preserving shared continuations and source cleanup order. Then compose
Server/PSA/governor scopes on one shared `O.Configuration`. This increment proves
preservation of stored facts through the implemented adapter; it does not finish
raw workers or establish whole-node shutdown, source refinement or liveness.
G0–G5, CM-I4c and SI4/SI5 remain open.


## Twenty-first increment: pending IG calls and nonempty exit

Checked 30 October 2026. The separate [ServerIGExit](ServerIGExit.agda) adapter
extends the normal-action-winner, single-listener, post-setup Server profile.
`ServerAdmission` and its existing guards/theorem types remain unchanged. This
increment implements selected caller-run CM interruption and the actual nonempty
IG catch path; it does not declare complete exception coverage or whole shutdown.

Source was rechecked in the clean network checkout at
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`:

- InboundGovernor.hs:193–207 catches outside the loop, deactivates in STM, drains
  InfoChannel once, then calls `handleError`. At :225–235 it reads the published
  state, traverses its public remote-state map with final transition tracers, and
  rethrows. It neither unregisters those connections nor joins raw workers.
- InboundGovernor/State.hs:76–82 projects remote states without idle timers.
  ConnectionId.hs:41–44 orders remote address before local address. The adapter
  reuses `ConnectionOrder.keyLess` and its explicit family/host/port abstraction;
  it does not establish OS address-order correspondence.
- Core.hs:1111 masks release, :2066 masks promotion, and :2257 leaves demotion
  unmasked. The initial and counter transactions read the map using `readTMVar`;
  they do not acquire a map lease. Release :1250–1254 and promotion :2233–2247
  separate tracing, counter reads and captured cancellation sends. Prune
  :767–777 performs ordered `throwTo` calls without cleanup joins.
- The real mux tracer samples active before a later queue transaction
  (InboundGovernor.hs:633–725). A callback that sampled True can therefore commit
  after deactivation and the final drain.

| Receipt site | Permission and effect |
| --- | --- |
| IG loop boundary or batch wait | No active CM call; preserve body/registry state for catch handling. |
| Release/promotion initial or counter read | Exact call PC, IG inCM, and map actually taken. Initialized controls use a distinct raw worker and check that the ordinary CM read retries. |
| Release send or promotion pruning send | An observed blocked `throwTo`, before target receipt. A send PC alone is not evidence of blocking or delivery. |
| Demotion transaction/assertion/counters/return boundary | Unmasked caller boundary; no false blocked-map premise. |

Every receipt archives the whole actual frame, including captured targets and
remaining pruning victims, then retires only the local call cursors. Already
committed writes, the shared world and other workers remain unchanged; no map
restoration, synthetic target step, handler result or cleanup join is generated.
Dual active frames and masked nonblocking receipt attempts are rejected. The old
call cannot resume after retirement, while unrelated actors can still progress.

Catch handling performs real IG deactivation/drain before a separate snapshot of
the published registry. Duplicate snapshot keys are refused; final rows are
ordered with the existing key comparison. Each final tracer has distinct
invocation and return observations. Normal body exit requires all callbacks to
return. A synchronous failure, or observed async interruption of a blocked tracer
in the MaskedInterruptible catch handler, replaces the original exception and
leaves the failed row unfinished. Body exit, result publication and IG join stay
separate. Final tracing does not clear the registry, and a late queue write does
not imply another drain or prevent the modeled IG exit.

[Properties/ServerIGExit](Properties/ServerIGExit.agda) proves exact active-frame
capture, exact source change (`clearPending` only), unchanged shared world and
raw worker table for every successful receipt. Its generic preservation lift
covers every adapter action and finite execution. The concrete
[ServerIGExitInvariants](Properties/ServerIGExitInvariants.agda) lifts unchanged
outbound capture, entry/promise supply and original handler/stored-resource facts.
Initial supply bounds and existing resource premises remain explicit. This
does not prove live resource ownership, registry validity or universal progress.

[Negative/ServerIGExit](Negative/ServerIGExit.agda) aggregates the acceptance
modules. All initialized histories begin at the real wrapper initializer with
empty admission/socket tables, two actual handoffs, real first-handler birth,
handshake publication, caller completion and IG registration. Hard limits agree
at 10; no injected queue is used to fake an initialized event history.

- `ServerIGExitRelease` interrupts the post-write counter read while the second
  raw worker holds the CM map. Terminating and that worker's lease survive IG join.
- `ServerIGExitSend` adds initialized release interruption before its first
  transaction and during an observed blocked captured send, without target result.
- `ServerIGExitProtocolPrefix` drives real mux startup/on-demand notifications,
  promotion, responder completion, monitor handling and explicit DeltaQ completion
  to a demotion call. `ServerIGExitCases` interrupts promotion before/after commit
  and unmasked demotion after commit. Final tracing reads published Warm while CM
  already contains Idle. It also checks a real sampled-active callback enqueue
  after the drain and unrelated handler progress while final tracing is pending.
- `ServerIGExitControls` checks initialized synchronous/blocked-tracer async
  replacement outcomes. Pruning-send cursor retention and two-key traversal order
  are explicitly conditional data controls, not initialized pruning/multiconnection
  histories. Premature snapshot/result/join, callback shortcuts and whole-Server
  completion are rejected at their tested frontiers.

Validation used serial Agda 2.8.0 checks from this library root. Runtime passed
initially at 4 GB; properties, invariants, branch endpoints and final aggregate
passed at 8 GB with their own `Checking` lines and no final warnings:

```sh
agda ConnectionManagement/Negative/ServerIGExit.agda +RTS -M8G -RTS
```

Logs: `/tmp/cm-ig-exit-20261030/`. Accepted individual evidence includes
`runtime.log`, `properties-final.log`, `invariants.log`, `release-clean.log`,
`protocol-prefix-check.log`, `cases.log`, `controls-final.log`, `send-final.log`;
`aggregate.log` freshly rechecks the aggregate and affected proof endpoints after
EOF cleanup. Data fixtures and remaining properties freshly checked in the
individual runs. Preliminary missing imports/name clashes and a shadowing warning
were repaired; no accepted run retains them. The 13-file strict local proof audit
reports zero findings, and tracked/new-file whitespace checks pass. This is not
a term-level audit of every imported assumption.

Existing `Negative/{ServerAdmission,ServerAdmissionPrefix,ServerAdmissionInvariants}`
also passed serial `+RTS -M8G -RTS` regression checks, exit 0, using cached
interfaces without `Checking` lines. Logs are `regression-*.log` in the same
directory. All checker processes have exited.

Assertions remain enabled; ordinary CM diagnostic tracers retain their earlier
total/nonblocking profile. Other receipt windows, initialized pruning-send history, arbitrary tracer
or finalizer failures, other Server race winners and multiple listeners remain
open. No native replay, full baseline rebuild, production patch or new deployed
defect is claimed. Next: compose this Server/handler adapter with
`PeerSupervision`/`GovernorPool` on one shared `O.Configuration`, preserving both
adapters' pending calls, actor freshness and scope certificates. G0–G5, CM-I4c and
SI4/SI5 remain open; raw admission workers are still outside owned scope joins.
