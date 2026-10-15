# First IG batch: notification to registration

This increment adds an executable IG prefix to the existing machine and CSP
process. It implements the **first nonempty batch from an empty IG registry**,
with successful responder startup represented by an explicit boundary contract.
It is not the general IG loop or a complete CM/IG/OG/Server lifecycle.

The implementation is [Rules/IGRegistration.agda](Rules/IGRegistration.agda);
[CSP/IGRegistration.agda](CSP/IGRegistration.agda) supplies machine executions,
raw and hidden CSP traces, and negative checks. No historical model is imported.

## Source mapping

All references are to network `96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`.
The relevant source is [InboundGovernor.hs](https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor.hs#L242-L398).

| Model action/state | Source boundary | Scope |
|---|---|---|
| `captureTime` | `getMonotonicTime` | Symbolic timestamp captured before the batch transaction; no elapsed-time theorem |
| `registerInactivity` | `registerDelay inactionTimeout` | Allocate a symbolic timer token; expiry/empty-loop branch is not implemented |
| `drainFirstBatch` | Queued-message alternative, whole-queue flush | Requires empty registry/freshness and a nonempty queue; retains the entire batch atomically |
| `readEvent` | `readTVarIO stateVar`, lookup by connection ID | Re-read published state for each event; retain the captured snapshot across later steps |
| `registerIdleTimer` | `traverse registerDelay idleTimeout` | Profile with idle timeout enabled; allocate a fresh symbolic timer, without registration yet |
| `successfulResponderStart` | Successful `foldM runResponder` plus `writeTVar stateVar` in one STM transaction | Explicit successful-start contract; commit registration and duplex freshness together |
| `commitDuplicate` | Existing-key branch and later `StateWithPeerTransition` publication | Write the captured snapshot, preserving the original handle, timer and freshness |
| `readNext time []` | End of the retained batch | Stop at a scope boundary; do not fabricate another iteration |

At the first batch, the empty registry and fresh-peer map make maturity and
peer-commit candidates absent. With a nonempty queue, the queued-message branch
wins over inactivity regardless of timer readiness. This is a source-derived
specialization of the [general selection kernel](Rules/IGBatch.agda), not an
arbitrary readiness input. It cannot be reused for later batches with live peers.

```mermaid
sequenceDiagram
    participant CM as CM result consumer
    participant Q as Information queue
    participant IG as IG continuation
    participant P as Published IG state
    CM->>Q: Enqueue NewConnectionInfo
    IG->>Q: Atomically flush entire first batch
    Note over IG: Retain batch separately from live queue
    IG->>P: Read state for current event
    alt Key absent
        Note over IG: Allocate idle timer; capture state
        IG->>P: Atomic successful startup + registration + freshness
    else Key already tracked
        IG->>P: Publish captured state unchanged
    end
    Note over IG: Advance retained batch cursor
```

## Representation and contracts

`Configuration.inboundGovernor` contains the IG continuation, published registry,
fresh-peer metadata and timer supply. `State.inboundInfo` remains the shared
notification queue. The authoritative dispatcher commits the updated queue and
IG runtime together. Other machine actions retain the IG runtime. Existing
initial fixtures initialize an empty IG; initiator-only configurations refuse IG
actions. This models post-wiring initialization, not Server supervision.

A `Registration` records notification/handle identity and the idle timer. Its
presence means that every responder was successfully submitted to
`runMiniProtocolSTM` in that transaction; it does **not** mean that protocols have
started executing. The handle's bundle and version data are opaque: freshness
retains a handle reference identifying the source version data, not a new version
value. The protocol map, run statuses, active counters and counter cache are not
represented. The source `RemoteIdle` projection is represented by the idle timer;
no remote-state transitions are implemented yet.

`successfulResponderStart` is an environment boundary analogous to the existing
handler-publication boundary. It assumes all startup calls succeed. The model does
not yet determine that outcome from mux/control state. Partial successful startups
followed by failure, `Mux.stop`, cancellation, tracer effects and exception
unwinding require separate rules. A trace choosing success is conditional on this
contract, even if another model action has closed the socket in the meantime.
Diagnostic logging is assumed total and nonblocking; the queue-writing mux tracer
is a missing behavioral dependency, not logging that may be erased.

The first-batch queue contains only `NewConnectionInfo`. The complete event union,
nonempty-registry readiness, timer expiry, later iterations and interaction with
mux tracing are still outstanding. The `igNextBatch`, `igResponderStartup` and
`igInactivity` diagnostics expose selected limits. They are not process events or
completeness certificates; `igInactivity` marks an omitted alternative even when
the nonempty-queue action is available.

## Evidence and limitations

The main witness composes existing admission and handshake executions with CM
notification and this IG prefix. It reaches registration as both a raw CSP trace
and a trace under the existing hiding policy. Clock capture and the explicit
successful-start boundary remain visible; internal queue/cursor/timer steps are
hidden. API-outcome equivalence is not claimed.

Checks also establish:

- The queue is empty after draining while the retained batch is still unprocessed.
- No registration exists before the atomic successful-start boundary.
- Startup before the event-state read is refused, and its raw CSP trace is excluded.
- A duplicate key with a different supplied handle/capability preserves the prior
  registration, timer and freshness; it does not allocate another idle timer.
- Unidirectional registration does not add duplex freshness.
- A CM enqueue interleaved after drain survives processing of the retained batch.
- Initiator-only mode refuses IG actions, and completed first batches cannot be
  drained again by this prefix rule.

Duplicate and late-enqueue fixtures are local branch/interleaving tests; their
injected initial states are not claimed reachable from source initialization.
The ownership and entry/promise supply proofs now cover **all extended machine
actions**, including IG. They do not establish IG registry/timer validity or full
state validity. No source replay, bounded search, source defect, deadlock or
liveness result is claimed.

## Validation and next work

From the library root, with Agda 2.8.0:

```sh
agda ConnectionManagement/CSP/IGRegistration.agda +RTS -M2G -RTS
```

This endpoint checks the new rules and traces, hiding, correspondence, and the
extended ownership/supply proof endpoints transitively. This endpoint passed with
fresh elaboration of the affected closure. Separate checks of
`Negative/CleanupAtomicity.agda` and `Negative/StaleHandshake.agda` also passed
with the same heap limit. The nine-file local proof audit found no holes or unsafe
markers; documentation links and `git diff --check` passed. These checks are not
an audit of term-level assumptions in external dependencies.

The next behavioral step
is the real IG event union and mux/tracer runtime: determine startup outcomes,
preserve atomic tracer queue/counter effects, and implement subsequent-batch
readiness from state. Add inbound release and OG jobs before claiming the first
combined subsystem lifecycle gate is complete.
