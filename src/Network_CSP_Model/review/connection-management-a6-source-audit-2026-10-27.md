# A6 peer policy and supervision source audit

Date: 27 October 2026.

This audit checks the A6 policy and supervision finding against network pin
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`. The source was read from Git objects
at that revision. It supports retaining the existing open policy model and adding
a separate pinned production peer-policy wrapper. It does **not** support treating
fatal-exception delivery as completed node shutdown.

## Policy configuration and production wiring

`RethrowPolicy` is configurable: its function accepts an `ErrorContext` and
`SomeException` and returns `ShutdownPeer` or `ShutdownNode`.
`ShutdownPeer` is the monoid identity; `ShutdownNode` is absorbing.
See [RethrowPolicy.hs:52–90][policy].

The source has two distinct policy paths:

| Path | Pinned wiring and scope |
| --- | --- |
| Peer-state acquisition | `PeerStateActionsArguments` accepts `spsRethrowPolicy` and `spsMainThreadId` ([PeerStateActions.hs:560–588][arguments]). Diffusion supplies its local base `rethrowPolicy` directly ([Diffusion.hs:582–593][peer-wiring]). |
| Connection handler | Diffusion separately combines the base policy with `daRethrowPolicy` for the remote handler and `daLocalRethrowPolicy` for the local handler ([Diffusion.hs:350–356][local-handler], [525–534][remote-handler]). These extensions are not supplied to `spsRethrowPolicy`. |

The base production policy checks the dynamic outer exception for
`IOManagerError` and selects `ShutdownNode` only in that case. Its `IOException`
branch returns `mempty`, hence `ShutdownPeer`; its outbound
`UnknownMiniProtocol` case also selects `ShutdownPeer`. Other exceptions use the
same default. See [Diffusion.hs:286–322][production-policy].

An arbitrary client of `withPeerStateActions` can supply another policy, so an
open profile permitting `ShutdownNode` for other faults is not inherently wrong.
It must be distinguished from the pinned production wiring.

## Acquisition exceptions and the classifier contract

The acquisition call is caught with `try` and inspected as `SomeException`; the
catch is not restricted to `IOException`. On a node-fatal decision, this branch
sends the **original exception** to the diffusion thread, then locally rethrows
that same exception ([PeerStateActions.hs:784–801][acquire-policy]). This differs
from the connection handler's separate `ExceptionInHandler` wrapping path
([ConnectionHandler.hs:289–306][handler-policy]).

CM throws its own selection errors and allows errors from transport operations
to propagate through acquisition/resource cleanup. Relevant boundaries are
[Core.hs:1422–1525][acquire-io]: selection error propagation, `openToConnect`,
configuration/bind/connect/local-address operations, and rethrow after connect
failure. The concrete socket opening path calls `Socket.socket` and
`associateWithIOManager`; its exception handlers close and rethrow rather than
turning every error into one CM fault ([Snocket.hs:394–407][snocket-open]).
Platform-specific IO-manager behavior is delegated to `System.IOManager` through
the network shim; this audit does not enumerate every platform's possible errors.

Consequently, the abstract model constructor `Cases.ioFailure ErrorId` must not
silently be equated with the Haskell `IOException` class. For an exact production
policy projection, the model needs either:

- An explicit fault distinction that represents a dynamically classified
  IO-manager exception; or
- A supplied classifier with a stated contract tying its answer to the original
  captured source exception.

A classifier based on opaque error IDs is an environment assumption until that
source-to-model relation is established. It must not permit a captured
`ConnectionExists` or ordinary `IOException` to be relabelled as an IO-manager
failure while claiming pinned production correspondence.

## Delivery and cleanup are distinct stages

The source-compatible stages are:

1. CM acquisition raises an exception; the peer action selects its policy.
2. `ShutdownPeer` locally rethrows. `ShutdownNode` first executes blocking
   `throwTo spsMainThreadId e`.
3. The target receives the exception. This acknowledges delivery, not completion
   of the target's unwinding or of any descendant cancellation/join.
4. If the sender continues, it executes the subsequent local `throwIO e`.
   Its outer `bracketOnError` restores `PeerCold`. The governor job handler can
   produce a failed completion, and the job-pool publication is a later step.
   See [PeerStateActions.hs:784–801][acquire-policy],
   [EstablishedPeers.hs:504–520][job-handler], and
   [JobPool.hs:156–164][job-publication].
5. The diffusion thread unwinds its active supervision scopes. Which descendants
   are cancelled and joined depends on the scopes already entered. Completion of
   those scopes is a later boundary, not the delivery event.

Other threads can run between delivery, the sender's local rethrow, completion
publication, and cancellation of that sender or the governor. Cancellation may
win that race, so the model must not require every fatal sender to publish a
failed completion before supervision completes. Conversely, immediate global
termination at delivery would erase these possible interleavings.

The concrete diffusion supervision structure is visible at:

- [Diffusion.hs:253–267][main-thread]: `mainThreadId` is the thread running
  diffusion; remote and local services may be raced. It is not a proof that this
  thread is the process's OS/main entry point.
- [Diffusion.hs:767–786][initiator-supervision] and
  [789–826][duplex-supervision]: nested `Async.withAsync` scopes and `waitAny`
  supervise governor, churn, providers and, when present, inbound governor.
- [Governor.hs:481–489][governor-pool] and
  [PeerStateActions.hs:624–638][peer-pool]: the governor and peer actions own
  separate job-pool brackets.
- [JobPool.hs:70–110][pool-close]: pool scope exit invokes `closeJobPool`, which
  cancels and waits on its recorded jobs. The source comments explicitly discuss
  potentially blocked delivery; there is no unconditional cleanup-liveness proof.
- [Server.hs:147–175][server-supervision]: the responder server races action,
  inbound-governor and accept-loop threads inside its own scopes.
- [Diffusion.hs:903–919][outer-run]: outer diffusion wraps/rethrows a non-ExitCode
  failure after unwinding its `withIOManager` body. Process-level supervision
  outside this module is not established by this audit.

## Recommended model scope

Keep the open executable policy choices, and add a pinned peer-policy wrapper
that explicitly enforces the production classifier contract. Do not reuse the
handler-policy extension as the peer-state policy.

Represent request/delivery and sender continuation separately from completed
supervision. If a wrapper accepts an externally supplied
**completed-supervision boundary**, state its meaning precisely: it marks the
end of the chosen modeled diffusion scope and prevents later ordinary wrapper
steps. That boundary is a scoped assumption, **not implemented cancellation,
resource cleanup, a join certificate, process termination or a liveness theorem**.
The open model remains useful for executions before that boundary and for custom
policies.

No maintained model file was edited for this audit. No Agda or source replay was
run; this is source evidence and a modeling contract, not an implementation
validation result.

[policy]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/RethrowPolicy.hs#L52-L90
[arguments]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerStateActions.hs#L560-L588
[peer-wiring]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/Diffusion.hs#L582-L593
[local-handler]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/Diffusion.hs#L350-L356
[remote-handler]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/Diffusion.hs#L525-L534
[production-policy]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/Diffusion.hs#L286-L322
[acquire-policy]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerStateActions.hs#L784-L801
[handler-policy]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionHandler.hs#L289-L306
[acquire-io]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1422-L1525
[snocket-open]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/Snocket.hs#L394-L407
[job-handler]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/Governor/EstablishedPeers.hs#L504-L520
[job-publication]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/network-mux/src/Control/Concurrent/JobPool.hs#L156-L164
[main-thread]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/Diffusion.hs#L253-L267
[initiator-supervision]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/Diffusion.hs#L767-L786
[duplex-supervision]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/Diffusion.hs#L789-L826
[governor-pool]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/Governor.hs#L481-L489
[peer-pool]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerStateActions.hs#L624-L638
[pool-close]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/network-mux/src/Control/Concurrent/JobPool.hs#L70-L110
[server-supervision]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/Server.hs#L147-L175
[outer-run]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/Diffusion.hs#L903-L919
