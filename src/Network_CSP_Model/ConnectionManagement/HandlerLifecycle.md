# Tracked handler cancellation and CM cleanup

`Rules/HandlerLifecycle.agda` connects the existing release/pruning delivery events
to a post-handshake handler unwind path. Tracking is **opt-in**: the new
`handlerStep worker (attach cancellationError)` action associates an existing
registered handler with its published handle's mux. The original `handlerExit`
boundary remains available for untracked handlers; no claim is made that all
machine cleanup traces are now source-derived.

Source pin: `96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`.

- [ConnectionHandler.hs:434–452](https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionHandler.hs#L434-L452): publish the negotiated handle and enter unmasked mux execution.
- [Mux.hs:254–278](https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/network-mux/src/Network/Mux.hs#L254-L278): close the job-pool bracket before the async catch writes Failed, traces Dead and rethrows.
- [JobPool.hs:70–110](https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/network-mux/src/Control/Concurrent/JobPool.hs#L70-L110): bracket release uses `uninterruptibleCancel` for registered jobs.
- [ConnectionHandler.hs:286–309](https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionHandler.hs#L286-L309): asynchronous exceptions bypass the synchronous rethrow policy.
- [Core.hs:584–713](https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L584-L713): the outer finally enters the existing CM finalizer.

## Attachment and ordering

Attachment requires a handler registration, its negotiated promise result, an
installed handle/mux, no started cleanup, and a ready mux with no callback in
progress. It captures the mux through the original promise, not through a current
connection-map entry. Duplicate tracking and two tracked workers owning one mux
are refused. Attachment marks entry into the modeled running-mux slice; it does
not derive handle allocation, handshake execution or bearer construction.

The supplied error identity represents AsyncCancelled in this profile. It is an
abstract payload, not exception classification or an allocated global identity.

```mermaid
sequenceDiagram
    participant Caller as Release or pruning caller
    participant Handler as Tracked handler
    participant Pool as Job-pool completion boundary
    participant Mux as Mux state and synchronous tracer
    participant CM as CM finalizer
    Caller->>Handler: Cancellation delivery
    Handler-->>Caller: Acknowledgment; caller may continue
    Handler->>Pool: Unwind job-pool bracket
    Pool-->>Handler: jobPoolClosed input
    Handler->>Mux: Write Failed and begin Dead callback
    Mux->>Mux: Sample IG active flag
    Mux->>Mux: Commit MuxFinished and clear counters
    Note over Handler,Mux: Queue backpressure can delay rethrow
    Handler->>Handler: finishRethrow input, including buffer release
    Handler->>CM: handlerExit enters finally
    CM->>CM: Take map, inspect captured entry, close socket
    alt Captured entry is Terminating
        CM->>CM: Restore map, await TIME_WAIT, then purge
    else Captured entry is already Terminated
        CM->>CM: Purge and restore map without TIME_WAIT
    end
```

A successful delivery atomically advances the caller and changes the tracked
handler from `monitoring` to `poolClosing`. It does not fail the mux, enqueue a
notification or enter CM cleanup in that event. The caller may complete its own
assertion/counter/IG-publication continuation before the handler closes its pool.

`jobPoolClosed` is an explicit completion input. It clears modeled running jobs
and on-demand waits, then `publishAsyncFailure` writes Failed and starts the Dead
callback. It does not synthesize normal protocol completions: the source job pool
filters asynchronous exceptions out of the per-job error handler, so canceled
jobs need not publish completion results or reset protocol status to Idle.
Existing `sampleTracer` and `commitTracer` actions preserve the sampled
active flag and information-channel backpressure. `finishRethrow` requires the
callback to have returned; it represents rethrow through the async-transparent
classifier and completion of remaining buffer unwinding. Only then may the
tracked `handlerExit` begin CM cleanup.

The dispatcher disables the abandoned monitor continuation after delivery. Job
outcome/publication actions remain possible during pool closure, but stop after
the close-completion input. During `deadTracing`, only the tracer callback may
execute on that owned mux. IG's independent batch and publication actions remain
available. Runtime frames retain mux identity across changes to CM entries and
IG registrations.

## Supported profile and limits

- This slice handles async cancellation delivered while the tracked mux is
  monitoring. [Normal and selected synchronous exits](HandlerOutcomes.md) are
  now handled separately. Handshake failure, repeated async interruptions and
  all masking windows remain incomplete for tracked handlers.
- Additional delivery is refused during pool closure, Dead tracing, body exit
  and active finalization. A completed finalizer permits a late acknowledgment,
  abstracting the target's final thread exit. Untracked deliveries keep their
  earlier environment-boundary behavior.
- Pool closure is not proved to finish. Its individual job inventory, cancellation
  order, joins, muxer/demuxer termination and blocking foreign calls remain behind
  the completion input. The model must not infer deadlock freedom from that input.
- Buffer-release completion is likewise an input. Source async propagation does
  not execute the synchronous ShutdownPeer/ShutdownNode rethrow-policy branches;
  those branches are modeled separately in [handler outcomes](HandlerOutcomes.md).
- `cleanupDone cleanupNormal` describes successful finalization after cancellation;
  it does not mean the handler body returned normally. The original handler,
  socket and entry identities continue to drive the existing finalizer.
- Ordinary diagnostic tracers remain total/nonblocking, except the modeled IG
  callback whose queue transaction can retry. A full queue can leave Failed
  visible while preventing the handler from entering finally.

## Verification

`CSP/HandlerLifecycle.agda` composes admission, registration, release and tracked
async unwinding into a raw CSP trace, and supplies a hidden unwind trace. Further
witnesses connect that exit to TIME_WAIT cleanup and connect a local self-pruning
fixture to purge-only cleanup. They distinguish source-composed prefixes from
local pruning fixtures and retain explicit environment completion assumptions.

Checks cover delivery-before-join, status-before-notification, blocked old monitor
steps, no premature rethrow/finalizer, full-queue backpressure, caller return
without joining cleanup, and the distinct Terminating/Terminated finalizer paths.
The existing global ownership and allocation-supply theorem statements are
unchanged; new lifecycle actions preserve the world, and guarded entry into the
finalizer reuses the existing cleanup preservation proof.

```sh
agda ConnectionManagement/CSP/HandlerLifecycle.agda +RTS -M2G -RTS
```

Normal and selected synchronous exits are covered by [handler outcomes](HandlerOutcomes.md).
Next strengthen runtime validity and move source-oriented scenarios toward
mandatory tracking before advancing outbound acquisition/OG. This increment proves neither complete source refinement nor
universal cleanup progress.
