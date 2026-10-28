# SI4 shutdown source audit — 27 October 2026

The overall objective is an executable combined CM/IG/OG/Server model that can
expose source bugs. SI4 adds the remaining physical resource and supervision
scopes; SI5 must derive full shutdown from their certificates. This audit records
new implementation obligations, separate from the earlier review corrections.

Authority is network revision `96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`.
Local exports of Core, ConnMap, Server, ConnectionHandler and network-mux's Mux
were compared byte for byte with the pinned Git objects. The checked-out Haskell
worktree is not the source authority. This is a source inspection, with no Haskell
replay or implementation refinement claim.

## CM close is a snapshot of mutable references

[Core:523–550][cm-close] reads the map once, then traverses the captured entry
references. Each entry's state is read later. `getConnThread` returns no thread
for ReservedOutbound or Terminated; all other modeled constructors retain a
handler. Each `throwTo` waits for delivery acknowledgment, then traversal proceeds.
Only after all sends does one STM wait for every collected Async result.
[ConnMap:251–264][traversal] uses nested Map traversals; despite the Core comment,
it does not spawn a cleanup task per entry.

Consequences for the executable coordinator:

- Capture entry references, then read each current heap cell. Do not snapshot
  handler IDs atomically or re-read the map to choose later entries.
- Preserve repeated references and repeated handler identities. Source traversal
  does not deduplicate the collected Async list.
- Separate cancellation request, delivery acknowledgment and collective result
  wait. Reusing JobPool's cancel/join-per-child cursor changes the algorithm.
- A handler removed before the snapshot is outside this wait. A captured entry
  becoming Terminated before its read contributes no handler.
- Collected Async results certify termination observations, not successful socket
  closure, all historical handlers, or absence of future handlers.

The local nested Store is an association list, whereas source Map traversal is
ordered by keys. List order is an abstract enumeration of captured entries;
source-order equivalence is not established by this coordinator.

## Handler completion requires actual local unwind

[Core:585–710][cleanup] installs `finally` around the entire handler. Cleanup
writes the original captured entry and deletes a map binding only if it still
points to that same mutable entry. A stale handler must not purge a replacement.
Socket-close failure can restore the original map while committed entry writes
remain; an available Async result can therefore contain a cleanup exception.
The Terminating branch unmasks only the TIME_WAIT delay, whose finalizer still
performs the captured termination/purge logic after cancellation.

[ConnectionHandler:330–349][handshake] catches asynchronous as well as synchronous
exceptions around the unmasked handshake and writes the failure promise there.
Earlier bearer setup and later successful mux setup are outside this catch.
Cancellation must not universally synthesize a failed handshake promise.
Success promise publication precedes the buffer bracket and mux execution.
Neither promise publication nor the historical `handlers` capture heap is a
physical Async completion registry.

## Mux scope still needs a physical pool

[Mux:256–270][mux-pool] places muxer, demuxer and mini-protocol jobs in the same
WithQueue pool. [Mux:558–572][mux-stop] first cancels the MiniProtocolJob subset,
then allows the egress queue to drain, then returns from the monitor. Only outer
pool close cancels and joins the remaining muxer/demuxer jobs. The subset
[cancelGroup:213–225][group-close] uses interruptible sequential cancellation;
it is not the whole-pool uninterruptible finalizer.

SI4 must bind fresh physical identities to direction, protocol number and run
generation. Current responder counters/result cells and peer protocol `running`
flags cannot certify physical job ownership. Exact generation publication must
not consume an older same-protocol result. Async cancellation must not invent a
normal completion result. `HandlerLifecycle.jobPoolClosed` remains an explicit
local boundary until a physical-pool adapter justifies it; buffer release also
needs its own boundary before CM finalizer entry. No full shutdown follows from
the present CM coordinator alone.

## Server joins do not join accepted admission children

[Server:147–186][server-scopes] nests the action Async and the listener Asyncs
inside the inbound governor/CM scope. Listener finalizers close listening sockets.
But [Server:234–254][server-child] spawns each accepted admission with bare
`async`, discards its handle and resumes accepting. Listener joins therefore do
not join these children. [InboundGovernor:193–235][ig-exit] first disables the
IG tracer and drains its queue before rethrowing; these two commits must precede
IG Async result publication to avoid blocking handler cleanup on the queue.

An admission child can still be pending when CM snapshots an empty map. A later
child can then enter CM and fork a handler after that snapshot has completed.
[Core:870–881][inbound-fork] also forks before map insertion/return; an exception
in the intervening trace can leave a handler outside the restored map. There is
no CM closed flag in the inspected finalizer that rules these executions out.

This identifies a shutdown/quiescence obligation and a potential source race,
not a replay-confirmed deployed bug. A model witness beginning with already
accepted admission children proves only the stated continuation behavior; it
does not derive the entire Server prefix or settle the caller's scope contract.
Do not add a fictitious Server join or forbid new CM work merely to prove an
unconditional global shutdown theorem. Full coverage may need explicit API
quiescence premises or a source change, with their status stated separately.

[cm-close]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L523-L550
[traversal]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/ConnMap.hs#L251-L264
[cleanup]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L585-L710
[handshake]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionHandler.hs#L330-L349
[mux-pool]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/network-mux/src/Network/Mux.hs#L256-L270
[mux-stop]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/network-mux/src/Network/Mux.hs#L558-L572
[group-close]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/network-mux/src/Control/Concurrent/JobPool.hs#L213-L225
[server-scopes]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/Server.hs#L147-L186
[server-child]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/Server.hs#L234-L254
[ig-exit]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor.hs#L193-L235
[inbound-fork]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L870-L881


## Pre-handshake physical completion increment

The next adapter begins before any handler exists and records physical ownership
at the actual inbound `Server.fork` transition. It does not adopt the retained
handler heap or a post-handshake snapshot as a physical registry. This first
profile covers pre-handshake asynchronous cancellation; successful handshake,
outbound physical spawning and mux execution are later obligations.

The pinned exception classifier is especially significant here:
`classifyHandlerError (HandlerError _) = HandshakeProtocolViolation`
([ConnectionHandler:186–200][handler-error-class]). This includes an async
exception caught by the handshake's `SomeException` handler. It differs from
`HandleHandshakeClientError/ServerError (HandshakeProtocolError _)`, which is
classified as `HandshakeFailure`. The consumer therefore uses the existing
`protocolViolation` branch for the caught cancellation result. An interrupted
masked bearer setup is outside that catch and has no such promise publication.
Its cancellation delivery needs an explicit blocked-operation observation;
ordinary delivery at an arbitrary masked setup boundary is not justified.

Physical result publication must follow actual `Machine.handlerExit`, the
existing captured-entry/socket cleanup steps and an observed `cleanupDone`
outcome. A failed socket close replaces the original exception; it can complete
the Async with a close error while retaining socket-close uncertainty and the
restored original map. Delivery acknowledgment and handshake-result publication
are both earlier than this Async result. Cleanup remains uninterruptible except
for the source TIME_WAIT delay. Its interruption must invoke the existing real
finalizer transaction before propagating the replacement error.

These source mappings justify the bounded adapter's transitions. They are not a
proof of complete mask semantics, eventual delivery, successful socket closure,
or coverage of every handler body outcome. Source setup completion and Async
result-publication scheduling remain explicit local observations.

[handler-error-class]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionHandler.hs#L186-L200


## Outbound birth and successful mux startup continuation

[Core:1531–1545][outbound-birth] forks the physical handler before the separate
Connected transaction. The source entry can still be ReservedOutbound while the
child starts its body. Recording physical ownership at `commitConnected`, or
reconstructing it from `getConnThread`, would omit that interval. The adapter
must capture the child's actual HandlerStart at `OutboundAcquire.forkOK` while
preserving the other callers' runtime frames and independent inbound actions.
Old inbound-only proofs do not justify preservation across the new outbound
writes: projection must target OutboundMachine, and supply induction must retain
the existing pending-acquisition capture invariant.

A snapshot read in this interval may skip the reserved entry despite the
physical child. This is a local interleaving observation, not a proof that full
diffusion shutdown reaches that interval: the earlier caller/pool joins and API
scope contracts still matter. It must not be presented as a replay-confirmed bug
or as permission to fabricate a handler reference in ReservedOutbound.

Successful negotiation has a separate source sequence: handle/mux construction,
promise publication, the buffer bracket, bearer construction and unmasked
`Mx.run` ([ConnectionHandler:353–381][successful-handler]). In particular, the
application can observe a successful promise before either mux infrastructure
job is forked. `MuxRuntime.ready` already represents the Mx.new state and is not
proof of either physical startup or shutdown.

[Mux:248–270][physical-startup] traces Starting, allocates the egress queue,
creates one WithQueue JobPool, forks/registers the muxer, then forks/registers
the demuxer, traces Mature and enters the monitor. Both jobs share the same pool
that will later own directional mini-protocol generations. Each
[JobPool:122–145][startup-registration] parent masks its own fork/insertion gap;
a child can act before insertion but its deregistration waits for that insertion.
A standalone startup component can certify these captured fork/register histories;
it cannot certify that a caller actually published a successful handler promise,
released a buffer or joined the pool until the adapter supplies those couplings.

[outbound-birth]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1531-L1545
[successful-handler]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionHandler.hs#L353-L381
[physical-startup]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/network-mux/src/Network/Mux.hs#L248-L270
[startup-registration]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/network-mux/src/Control/Concurrent/JobPool.hs#L122-L145


## Coupling successful publication to per-handler startup

Successful negotiation returns into the masked handler body before handle
allocation and promise publication ([successful-handler]). The handshake-only
catch no longer surrounds this continuation. The coupled prefix must disable
the old unmasked-handshake cancellation route immediately at observed successful
return, rather than keeping it available until the promise is written. Blocking
interruptibility and unwind in later masked setup/startup remain separate future
observations; omission of those branches is not a theorem that cancellation
cannot occur there.

Birth direction determines source allocation policy. Outbound success attaches
an IG tracer only in responder mode with duplex flow (ConnectionHandler:361–370).
Inbound success always constructs the IG tracer (435–443). A current CM entry can
have been overwritten by another incarnation by then, so it cannot determine
which handler function is running. Capture inbound/outbound origin at the actual
fork and retain the original handler key, promise, socket and entry references.

The actual successful `Machine.handlerPublication` and the startup component's
`observePublication` must advance together. Before that event, callers cannot
observe the negotiated promise. After it, callers may consume the result or queue
responder requests while buffer/bearer creation and physical mux jobs remain
pending. Neither handle allocation's M.ready status nor command enqueue proves
that the mux monitor is running. Startup ownership must remain per handler, so
independent handlers and callers can interleave throughout this prefix.

The prefix must also guard inherited entry points: raw handle installation,
publication observation, old handler body/cleanup/result paths and monitor/job
progress cannot bypass the new resource ownership. In particular, successful
startup does not justify `HandlerLifecycle.jobPoolClosed`, buffer release,
CM-finalizer entry or Async result publication. Global physical JobId freshness
across these per-handler pool histories is an explicit adapter check; a per-pool
distinctness theorem alone cannot establish it.


## Protocol jobs in the captured pools — 28 October 2026

At the same network pin, Mux.hs:494–517/600–625 forks mini-protocol jobs into the
very same JobPool that owns muxer/demuxer. Direction and number identify a source
protocol slot; a new completionVar identifies each restart. A physical job capture
therefore needs direction, number and a fresh generation as well as its Async
identity. PeerActions running cells and legacy responder runningJobs lists are
not physical registries.

Mux.hs:333–354 returns from the protocol action, traces Terminating, waits for
that job's Wanton egress to be empty, then atomically sets StatusIdle and writes
its clean completion before returning the JobResult. JobPool.hs:156–164 publishes
that returned result to its queue later. Consequently a clean first generation
can release the protocol slot and be preempted before queue publication; a newer
generation of the same number can publish first. Selecting a pending result by
protocol number would incorrectly publish the older occurrence. The new
publishJobOccurrence operation selects/removes one exact pending occurrence;
legacy number-based publication remains only for compatibility.

A synchronous job exception (Mux.hs:356–364) bypasses the egress wait and attempts
the error completion without writing StatusIdle. Error completion must not enable
a restart. Asynchronous exceptions bypass this jobHandler entirely: no ordinary
error completion or queued JobResult may be fabricated for cancellation. The
present normal/synchronous body profile does not implement group cancellation.
JobPool's masked parent insertion gap remains distinct from child completion:
children may return and publish before insertion, while deregistration retries
until insertion. The monitor cannot process another event while its parent fork
operation is still awaiting that insertion; independent mux parents can proceed.

The new physical queue must carry infrastructure outcomes as well as protocol
outcomes. Its generation-tagged protocol items are bound to their actual physical
jobs. The legacy MuxRuntime.completions list is only a responder-side projection
in this new component: it cannot be treated as the full physical queue or used to
skip a preceding infrastructure/initiator result. Typed-head monitor consumption
and the initiator-to-peer result bridge remain later integration obligations.

Initiator creation is an explicit observed miniProtocolJob-fork boundary. The
adapter checks its captured configured number, slot state, mux readiness and
known pending work; it does not claim that a PeerActions.startProtocol flag is a
fork, nor prove the unmodeled initiator caller/command prefix. Initiator result
cells are captured locally and publish to the authoritative same physical pool.
This extends the modeled runtime; it is not a fabricated old OutboundMachine or
PeerActions write. Responder forks/completion/publication do couple to the actual
existing source dispatcher operations, with exact occurrence selection. No
source-refinement or complete cross-direction command-FIFO theorem follows from
the standalone initiator observation.


## Typed physical result consumption — 28 October 2026

Mux.hs:427–454 dequeues one JobPool result inside STM before entering its
handling branch. The selected value must therefore be held independently of
later queue appends or current protocol slots. The responder legacy list is a
projection; it cannot skip a preceding infrastructure or initiator physical item.

Mux.hs:454–488 orders result handling as follows. Clean protocol completion emits
its direction-specific clean trace and continues. Protocol exception first writes
Failed, then emits the exception trace, Dead and DeltaQ before throwing. Muxer
failure is always Failed followed by Dead. Demuxer handling reads current
JobPool MiniProtocolJob group size in the same STM as its status write; only
BearerClosed with size zero writes Stopped and suppresses propagation. Every
other demuxer outcome writes Failed. Both paths emit Dead afterward.

The group count is read at handling, not at dequeue or body completion. A clean
job whose slot is already Idle but is still registered counts toward that size.
A removed historical error job does not count despite its non-Idle/error slot.
Jobs can deregister between dequeue and handling. A normal demuxer result can
therefore leave later typed results queued; monitor-local normal finish is not a
queue-empty, pool-closed, buffer-released or parent-Async-result certificate.

A responder completion trace uses the actual existing IG monitor/tracer path;
its error trace returns through afterFailure before starting Dead separately.
Initiator completion traces are ignored by the IG responder tracer, but remain
explicit local normal-return observations. Clean completion traces precede DeltaQ
and continuation; an error exception trace precedes Dead, with protocol DeltaQ
after Dead. The local error finish before Dead covers the exception trace, while
its later monitor-finish boundary covers the remaining DeltaQ/throw continuation.
Infrastructure cases have no protocol DeltaQ call. An initiator error writes
Failed before its exception trace and then Dead. The new
source status-only writes and Dead helper preserve those boundaries rather than
using the old fused initiator legacy result branch as a physical consumer.
Custom tracer errors, async interruption and lexical JobPool unwind remain future
branches, not obligations discharged by a callback-returned flag.

The monitor uses a fixed classifier parameter mapping abstract ErrorId values to
the source exception's BearerClosed classification. This contract is explicit;
exception identity alone does not derive dynamic exception type. Parent insertion
must have settled before the same monitor can dequeue; independent child returns,
publication/deregistration and other monitors remain enabled while an item is
held or its tracer blocks. Group cancellation is still a later, distinct scope.

## Interruptible group shutdown and whole-pool unwind — 28 October 2026

Rechecked exact network objects at `96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`:
`network-mux/src/Network/Mux.hs`,
`network-mux/src/Control/Concurrent/JobPool.hs`, and
`ouroboros-network/framework/lib/Ouroboros/Network/ConnectionHandler.hs`.
Their `/tmp/cm-review-20261027` exports match these objects byte for byte.
The checked-out source worktree is not the authority.

Mux.hs:555–570 handles CmdShutdown by tracing Stopping BEFORE its status write,
then cancelGroup MiniProtocolJob, then a two-second bounded egress drain, Stopped
write, TraceStopped and monitor return. TraceStopped is ignored by the IG tracer;
it is not a fabricated Dead callback. Infrastructure jobs are outside the group
snapshot and may independently return/fail while the group is closing or draining.
JobPool.hs:213–225 reads the registry once and traverses matching jobs with ordinary
interruptible cancel (send and wait). It does not close the pool. The separate
bracket release at JobPool.hs:105–109 snapshots ALL currently registered jobs and
sequentially performs uninterruptibleCancel. Neither snapshot includes removed
historical handles or future admissions. A handle deregistered before whole close
may still lack an Async result and is not recaptured by that close.

JobPool.hs:156–164 excludes asynchronous exceptions from jobHandler. Delivery to
an unmasked protocol body therefore enters actual unwind without inventing a
normal/error result or queue entry. In particular, cancellation after the clean
Idle/result commit but before body return retains that committed metadata; the
model removes only the exact unpublishable responder ghost occurrence. The
synchronous error handler and later publication are masked, so their normal
completion may outrun a cancellation request. An explicitly observed synchronous
exception replacing cancellation during an uncommitted protocol unwind may enter
the real error-handler path; cancellation alone cannot create that error result.

Mux.hs:256–279 places the async catch outside withJobPool. Owner cancellation in
the modeled group/drain stages immediately abandons the graceful cursor, but
Failed and Dead occur only AFTER the actual whole-pool close. MuxGroupShutdown
models this observed delivery and ordering. Its normal/failed/async scope outcome
is not a parent handler Async result or a rethrow-policy decision. In particular,
ConnectionHandler.hs:377–380 still has the surrounding buffer scope, and its
non-async classifyExceptions wrapper has separate propagation effects.

The current profile covers post-startup waiting and group/drain cancellation,
with callback returned and no pending parent insertion. Startup/setup failure,
custom tracer failure/interruption, infrastructure unwind replacement and the
post-whole-close return windows are not established by this increment. Drain
readiness, timeout and synchronous-unwind replacement remain explicit observations;
no fairness, source refinement or full-shutdown theorem follows. CM shutdown
send acknowledgement is not yet coupled to this owner-delivery observation.

## Buffer scope, handler outcome and CM finally — 28 October 2026

Rechecked Core.hs and ConnectionHandler.hs exports against the exact network pin
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`; both matched byte for byte.
ConnectionHandler.hs:378–380,450–452 encloses restored Mx.run in withBuffer.
Core.hs:118 supplies withBuffer as a callback: the CM model cannot establish a
concrete provider's memory-release implementation. MuxHandlerExit observes its
scope exit after the actual group/whole-pool runtime reaches ScopeDone. Successful
teardown preserves the pending mux outcome; an observed provider exception may
replace it. Exception preservation and completed provider teardown are explicit
contracts, not a proof that every supplied higher-order callback behaves that way.

ConnectionHandler.hs:294–309 classifies only non-async exceptions AFTER that scope.
It chooses runRethrowPolicy in the original inbound/outbound error context, traces
TrConnectionHandlerError, then either throws ExceptionInHandler to the peer caller
or delivers that wrapper to main and rethrows the original exception. The adapter
retains original versus peer-wrapped synchronous errors and async errors separately.
Policy selection, trace return and main-thread delivery are observations. Main
receipt is neither node exit nor a join. Custom trace exceptions/interruption and
additional cancellation windows in classification remain outside this profile.

Core.hs:584–592 places cleanup outside the handler callback in finally. Its
captured HandlerStart, not a later CM alias, supplies entry, key, socket and promise.
The adapter compares that original capture with the source handler registration
before entering or stepping cleanup, then invokes actual handlerExit/cleanupStep
operations. It preserves the existing map-take, captured entry write, socket-close,
map-publication/restoration, TIME_WAIT finally and counter-read boundaries.

A cleanup exception replaces the body outcome without re-entering the already
exited handler classifier. Shared CleanupOutcome alone does not record its dynamic
exception class. The new frame records the observed throwing operation: this profile interprets
failSocketClose as ordinary synchronous socket-close failure and interruptTimeWait
as delivered asynchronous cancellation. That exception-class contract is explicit;
masking alone is not a dynamic-exception-type theorem. Completion must match the
recorded error identity. It cannot turn
TIME_WAIT cancellation into an invented synchronous error. No additional tracer,
transaction or foreign-call failure coverage follows from those two branches.

CM.shutdown send acknowledgment is coupled to actual group/waiting owner abort,
or to the actual TIME_WAIT interruption. It is still separate from all joins and
parent result publication. The final collective wait reads the new handler result
record for successful mux owners, alongside the existing pre-handshake physical
history. Direct use of the older pre-handshake final-wait oracle is blocked in
this layer. Results become available only after the modeled body outcome, actual
CM cleanup completion and explicit Async-result publication. Remaining buffer/
policy delivery windows, setup/startup failures, custom tracer unwind and outer
Server/IG/governor histories still prevent a full shutdown claim.

## Masked post-mux cancellation windows — 28 October 2026

Core.hs:584–592 and ConnectionHandler.hs:294–309,378–380,450–452 were rechecked
against the pinned network objects; local exports match byte for byte. The
handler is born under mask_, while its supplied unmask restores Mx.run. Returning
from that restored action does not make all later pure policy/rethrow code
arbitrarily interruptible. The new MuxExitCancellation layer requires an observed
interruptible operation in one of three named windows. It is not a theorem about
the concrete mask of a caller-supplied buffer provider or arbitrary tracer.

At a blocked buffer-provider operation, cancellation replaces the pending mux
outcome with an async exception but leaves buffer scope unwind outstanding.
Only a later provider-return/unwind observation permits body exit and CM cleanup.
A synchronous provider-finalizer exception may still replace that cancellation
and enter the outer non-async classifier. A post-Mx.run provider failure does not
retroactively rewrite mux status or invent an IG Dead callback.

The classifier's TrConnectionHandlerError callback precedes either policy branch.
Cancellation at an observed blocking operation in that callback escapes its
catch handler: it does not re-enter classification, peer wrapping or node delivery.
A synchronous exception thrown from that callback also escapes directly as the
new original error. It is not wrapped by the interrupted old policy. This is the
connection-handler error tracer, not the mux/IG tracer; their remaining failure
and callback windows are distinct obligations.

ShutdownNode calls throwTo before rethrowing the original exception. An observed
interruptible blocked send may instead propagate cancellation into CM finally.
The model does not fabricate a successful send-return observation afterward. It
also does not prove retraction of an in-flight exception, main-thread nonreceipt
or node termination. Pure classification, peer rethrow, post-send node rethrow,
body-exit and uninterruptible cleanup stages are not invented delivery points.
Existing explicit TIME_WAIT delivery and already-finished acknowledgment remain
in the underlying handler-exit adapter.

Each CM-coupled delivery reads the actual awaitDelivery target, performs that
same local delivery, then acknowledges the actual coordinator. It does not skip
provider unwind, captured CM cleanup or physical Async-result publication.
New generic proofs preserve actual source/per-pool histories and initialized
capture/supply facts, and expose the exact window, receiver and acknowledgment.
These are bounded model/source contracts; implementation replay and full shutdown
remain open at the unchanged source pin.

## Partial startup and synchronous mux-tracer unwind — 28 October 2026

Verified the exact network pin again: Core.hs, ConnectionHandler.hs, Mux.hs and
JobPool.hs exports match `96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d` byte for
byte. Current implementation reading, not the external worktree checkout, is
the authority for this increment.

ConnectionHandler.hs:377–380,449–452 writes the successful promise before entering
withBuffer, creating the bearer and restoring Mx.run. A failure observed before
provider callback invocation has no modeled buffer-body teardown obligation.
Bearer setup failure inside that callback still requires observed provider unwind.
The provider's allocation, exception preservation and memory-release semantics
remain contracts. Normal return from an arbitrary higher-order provider without
calling its body is not established by this profile.

Mux.hs:248–254 places TraceStarting, egress allocation and labels BEFORE the
withJobPool expression's async catch. Observed cancellation at those pre-call
points must not invent a later Failed/Dead catch. JobPool.hs:71–81 brackets pool
creation before body entry. Synchronous acquisition failure owes no close of an
unacquired pool; once the bracket body is entered even an empty pool owes actual
close. MuxStartupUnwind keeps these cases separate and never changes partial
startup into monitoring or fabricates G.ScopeDone to pass the old exit guard.
Named helper failures are observed throwing-call boundaries; additional internal
allocator/timer/provider scopes are not themselves proved by those observations.

JobPool.hs:122–145 masks creation through insertion. The new profile observes
fork failure BEFORE birth and refuses ordinary async delivery in an existing
fork/insertion gap. Child result publication may outrun insertion, but removal
still waits for it. A child deregistered after insertion and before its Async
result fill is omitted from a later current-registry snapshot. The initialized
removed-history example closes an empty snapshot while that historical result
is still unavailable; it also retains the physical queued infrastructure result.

A synchronous startup or tracer exception runs the actual whole-pool release,
then propagates past Mx.run's ASYNC-only catch. It does not force Failed/Dead or
pretend the failed callback returned. An entered-pool startup cancellation instead
runs that release BEFORE actual Failed, Dead and rethrow. The async catch's own
tracer can throw a new synchronous error which replaces the original async
exception, without re-entering that same catch or overwriting its Failed value.
Observed normal/error provider exit and the real captured CM finally remain
separate prerequisites before parent Async result publication and the CM wait.

ConnectionHandler.hs:363–365,438–440 composes the caller's mux tracer FIRST and
the IG tracer second. A custom exception at the entry of that call is distinct
from a later descriptor exception inside the IG STM leg. The new monitor-trace
fault guard accepts callback entry or actual tracerFailed evidence, not a pending
commitTrace state alone. Existing IG.commitTracer computes the actual failure
with TracerReadiness prefix/retry precedence and missingDescriptor checks. The
conditional successor-registration control executes that interpreter first,
checks no trace publication committed, then enters unwind with tracerFailed
preserved. That view is explicitly conditional; it has no initialized second
handler/registration history and is not a new source-reachability theorem.

Remaining gaps include async delivery during mux/IG callbacks, some ignored and
DeltaQ tracer windows, post-close catch cancellation, pre-publication negotiation/
allocation faults, additional child-finalizer failure classes and outer Server/IG/
governor histories. No source refinement, universal termination, admission
quiescence or full-shutdown theorem is inferred from these finite model paths.
