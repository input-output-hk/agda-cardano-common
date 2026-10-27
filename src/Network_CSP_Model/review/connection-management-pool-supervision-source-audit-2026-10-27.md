# Job-pool close and diffusion supervision source audit

Date: 27 October 2026.

This audit reads network Git objects at pin
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`. It identifies an executable first
scope for cancellation and waiting: closing one governor-owned job pool.
Completion of that operation must not be presented as completed diffusion
supervision or node shutdown.

## One immutable snapshot, sequential cancellation and waiting

Both `withJobPool` and `withJobPool_` use a resource bracket whose release is
`closeJobPool`. Release reads `jobsVar` once and traverses the captured map with
`mapM_ uninterruptibleCancel` ([JobPool.hs:70–110][pool-close]). It does not
repeatedly drain the live registry, issue every cancellation before waiting, or
clear the completion queue.

An executable close should retain this snapshot independently of later registry
updates. It should process one snapshot handle at a time: request cancellation,
observe delivery, await the handle's Async result, then advance to the next
handle. An already completed handle can be awaited immediately. Later handles
can execute while an earlier cancellation or wait is blocked. Preserve source
map traversal order, or state explicitly that an abstract traversal order is a
model abstraction. Do not replace this operation with a bulk-send/bulk-wait
algorithm.

The source comments warn that cancellation can block when an exception cannot
be delivered. Neither uninterruptible masking nor finite snapshot size proves
that close eventually completes.

## Registration is not an Async completion certificate

`forkJob'` masks the owner across child creation and registry insertion. A child
runs its action/publication code and then deregisters. On an exception it also
deregisters before propagating the exception. Deregistration retries if the
parent has not inserted the entry yet ([JobPool.hs:122–145][fork]). This supports
the fast-child race: the child may finish its action before registration, but
cannot remove its entry until the parent's insertion exists.

For the concrete governor owner, closing its own scope should not start in the
middle of this masked fork/registration sequence. A first close model should
state an owner-quiescence condition that rules out further own-pool forks and
unregistered children at snapshot acquisition. This condition is scoped to the
owner; the JobPool API itself does not globally prohibit unrelated concurrent
clients from retaining and using a pool handle.

Deregistration is the last operation of the JobPool child body, but the enclosing
Async wrapper still has to record its result. Registry absence therefore does
not itself certify Async completion. In particular:

- An empty registry is not a certificate that every historical child has an
  observable Async result.
- Snapshot members remain valid cancellation/wait targets after deregistration.
- A child removed before snapshot acquisition is outside the captured set.

A close-finished theorem should quantify over snapshot handles and observable
Async results. It should not silently quantify over every child ever created.
Here, waiting for an Async result is the intended completion observation; this
is not a claim about literal OS-thread destruction.

## Outcomes, publication, deregistration and cancellation

The job action runs under a handler which explicitly excludes
`SomeAsyncException`. If the action or its ordinary exception handler returns a
result, a WithQueue pool then writes that result to its queue; a WithoutQueue
pool performs no publication ([JobPool.hs:147–164][outcome]). Normal
deregistration follows that publication because it is outside the `io` call
([JobPool.hs:122–145][fork]).

These are separate boundaries: action result, queued outcome, registry removal,
and Async result availability. An action result alone is not a queued outcome,
and a queued outcome is not a thread-completion certificate. Cancellation that
wins before publication must not fabricate an ordinary failed governor
completion: asynchronous exceptions bypass the ordinary handler. A completion
already published before cancellation remains in the queue; pool close does not
remove it. Source masking and interruptible-operation boundaries constrain
where cancellation can actually arrive, so a model should not claim every
syntactic gap is a freely interruptible point without further evidence.

The existing model's ordinary deregistration guard may require a queued
completion. Cancellation needs its own path, since a cancelled source child can
deregister without publishing any ordinary outcome. A proof that reuses raw
execution erasure must account for any new configuration-changing cancellation
transition; deleting a job is not an underlying stutter.

## Distinct owners and nested diffusion scopes

The governor owns a WithQueue pool around its loop
([Governor.hs:481–489][governor]). Peer-state actions separately own a
WithoutQueue pool ([PeerStateActions.hs:624–638][psa]); that pool receives the
background `peerMonitoringLoop` jobs forked after establishment
([PeerStateActions.hs:836–852][monitor]). These are separate pools with separate
snapshot and cancellation boundaries. A background monitor has no governor
completion-queue publication in that WithoutQueue pool.

Diffusion nests the peer-state-actions scope outside peer-selection providers,
then the governor Async scope, then the churn Async scope. This is visible for
both [initiator-only diffusion:767–786][diffusion-init] and
[responder-capable diffusion:789–826][diffusion-responder]. The provider helper
places its local-root provider Async scope inside its ledger-peer provider
scope ([PeerSelectionActions.hs:84–102][providers]). On exceptional unwinding
of that continuation, the nesting gives this cleanup order:

1. Cancel and await churn.
2. Cancel and await the governor; governor unwinding includes its own job-pool
   close.
3. Unwind local-root and ledger-peer provider scopes.
4. Close the separate peer-state-actions background-monitor pool.

This is an order on the unwinding thread's scope exits. It does not serialize
all concurrent activity: the governor can already be unwinding independently,
and peer-state monitors can continue during governor-pool close. In responder
mode the server additionally owns action, inbound-governor and accept-loop
scopes ([Server.hs:147–175][server]). Remote and local diffusion may themselves
be raced by the thread captured as `mainThreadId`
([Diffusion.hs:253–267][main]). Either pool's completed close is therefore only
one part of supervision. It certifies neither connection-manager/handler
cleanup nor complete diffusion or process shutdown.

## Supplementary dependency evidence

Local cached package archives were available for `io-classes-1.8.0.1` and
`async-2.2.6`; neither package was registered in the queried GHC package database.
These archives were inspected directly. No resolved build configuration tying
these exact dependency versions to the network pin was established, so they are
supplementary evidence, not an audited dependency pin.

In cached `io-classes-1.8.0.1`,
`src/Control/Monad/Class/MonadAsync.hs:257` defines the default
`uninterruptibleCancel = uninterruptibleMask_ . cancel`; lines 384–386 delegate
the IO instance to async. The cached async implementation confirms:

- `Control/Concurrent/Async/Internal.hs:299–300`: `cancel` sends `AsyncCancelled`
  with `throwTo`, then waits with `waitCatch`.
- Lines 329–331: `uninterruptibleCancel` wraps `cancel` in uninterruptible masking.
- Lines 214–224: `withAsync` cancels and waits on both exceptional and normal
  continuation exit. Its fork wrapper records the child result in a TMVar.
- Lines 307–310: `cancelMany` is a different bulk-send then bulk-wait operation;
  pinned JobPool close does not call it.

## Recommended first executable contract

Model one governor-owned WithQueue pool close with explicit owner quiescence,
an immutable registry snapshot, sequential per-handle cancellation and Async
result observation, and completion-queue preservation. Prove that finishing
this close certifies its snapshot members. Retain the independent background
monitor pool and larger diffusion scopes as outstanding obligations.

This report changes no model code. No Agda or source replay was run. The audit
provides source boundaries and limitations, not a cancellation liveness proof or
full-supervisor refinement theorem.

[pool-close]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/network-mux/src/Control/Concurrent/JobPool.hs#L70-L110
[fork]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/network-mux/src/Control/Concurrent/JobPool.hs#L122-L145
[outcome]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/network-mux/src/Control/Concurrent/JobPool.hs#L147-L164
[governor]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/Governor.hs#L481-L489
[psa]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerStateActions.hs#L624-L638
[monitor]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerStateActions.hs#L836-L852
[diffusion-init]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/Diffusion.hs#L767-L786
[diffusion-responder]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/Diffusion.hs#L789-L826
[providers]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerSelectionActions.hs#L84-L102
[server]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/Server.hs#L147-L175
[main]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/Diffusion.hs#L253-L267
