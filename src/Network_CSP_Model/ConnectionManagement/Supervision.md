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
| SI4 | CM handler/mux lifetime and cleanup, connection-manager scope, and responder Server scopes, including remaining handler sends and joins. | Active: typed FIFO monitor effects checked; group/whole-pool unwind, buffer/CM cleanup and outer/Server integration still open. |
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
TraceStopped. It does not close the pool or emit IG Dead. Monitor return or
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
