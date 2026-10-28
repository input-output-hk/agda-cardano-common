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
