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
| SI1 | Standalone one-owner governor-pool lifecycle: immutable registry snapshot, sequential cancel/wait, queue preservation, and certificates for snapshot Async results. | Standalone implementation complete and checked in this checkpoint. This is not full shutdown. |
| SI2 | CM caller cancellation and governor adapter: executable source-compatible cancellation effects, explicit bracket/handoff context, asynchronous-exception propagation, and job termination only after the modeled local unwind. | Implemented and checked within the stated execution profile: real cleanup, captured-frame/supply induction, initialized runs and pool-close certificate. |
| SI3 | Separate PSA background-thread registry/pool plus provider, churn and governor Async scopes, with their actual ownership and unwinding order. | Remaining obligation. |
| SI4 | CM handler/mux lifetime and cleanup, connection-manager scope, and responder Server scopes, including remaining handler sends and joins. | Remaining obligation. |
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

SI3–SI5 remain open. In particular, the actual background-monitor thread registry
is not `Subsystem.monitors`, which records only currently executing follow-up
operations. No full shutdown action is derived or added by this integration.

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

Next executable obligation: SI3 must record actual background-thread
creation/registration and the outer provider/Async scopes;
`Subsystem.monitors` cannot stand in for that thread registry. SI4 and SI5 remain
outstanding, and no completeShutdown derivation is claimed.

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

SI3 remains open. This subsection is source-verified design guidance, not an
implemented outer registry or a validation claim. The queue-free kernel
prerequisite now exists; actual PSA thread capture and outer-scope integration
still need to be implemented.

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
