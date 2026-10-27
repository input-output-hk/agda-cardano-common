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
