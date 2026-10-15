# IG caller-run inbound release

`Rules/InboundRelease.agda` implements the `CommitRemote` CM call under the existing
machine and CSP renderer. It follows network revision
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`,
[Core.hs:1107–1260](https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1107-L1260)
and [InboundGovernor.hs:529–568](https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor.hs#L529-L568).
Assertions are enabled in this profile. Diagnostic tracers are assumed total and
nonblocking; their counter read remains an explicit transaction.

```mermaid
sequenceDiagram
    participant IG as IG batch continuation
    participant CM as Caller-run CM release
    participant Map as Shared CM map and entry TVars
    participant Env as Cancellation boundary
    IG->>CM: CommitRemote, capture IG state
    CM->>Map: Read current binding and atomically decide/write
    Note over CM,Map: InboundIdle → Terminating; capture worker
    CM->>Map: Separate counter-read transaction
    Note over CM,Map: Blocks while map is taken
    CM->>Env: Request cancellation of captured worker
    Env-->>CM: Delivery acknowledgment (explicit input)
    CM->>CM: Evaluate deferred assertion
    CM-->>IG: CommitTr / KeepTr / UnsupportedState
    IG->>IG: Separate publication of captured-state decision
```

## Branch mapping

The exact-key lookup is performed in the transaction, not when IG captures its
published state. Entry selection and the optional write happen in one machine
transition; `Proposal` is a pure implementation helper, never a suspended commit.

| Observed CM state | Transaction effect | Result or exception |
| --- | --- | --- |
| Missing binding | None | CommitTr |
| Reserved, unnegotiated, outbound uni | None | UnsupportedState |
| Outbound duplex ticking | Write expired, using requested key | KeepTr |
| Outbound duplex expired | None | Inline assertion exception |
| Outbound idle | None | Deferred assertion exception; nominal CommitTr cannot return |
| Inbound idle | Write Terminating; capture worker | CommitTr after delivery |
| Inbound active | Write Terminating; capture worker | Deferred assertion after delivery; nominal unsupported cannot return |
| Duplex active | Write outbound duplex ticking | Deferred assertion; nominal unsupported cannot return |
| Terminating | None | CommitTr |
| Terminated | None | UnsupportedState |

All non-inline branches read counters before cancellation and deferred assertion
handling. Unsupported results still perform that read. A taken map disables the
read without undoing the earlier entry write. Missing heap references are invalid
fixtures, not source STM retries. Only the incoming-count projection is retained;
all bound entries are read, but complete diagnostic counter values are not exposed.

`throwTo` delivery is separated from request. The target stays captured even if a
later action changes the current entry. Delivery does not wait for TIME_WAIT or
handler cleanup. The handler's reception/unwind behavior is not derived from the
mux model yet; the input can also abstract a target that has already exited.
Consequently the trace allowing IG publication before any modeled cleanup is
conditional on this explicit boundary, not a source execution claim.

On return, CommitTr prepares unregister, KeepTr prepares RemoteCold and unsupported
advances the batch cursor without publication. Successful decisions use the
captured IG state and are published by `IG.commitDecision`. During the CM call,
`IG.inCM` prevents the batch from advancing. Existing IG deactivation prevents
subsequent call steps; full asynchronous masking/unwinding remains unmodeled.
An assertion reaches `assertionRaised`, reported by `CSP.Scope.releaseFrontier`;
it cannot return nominally. This is an exception frontier, not a source deadlock.

## Verification and next slice

`CSP/InboundRelease.agda` contains raw/hidden finite trace witnesses, including a
trace composed from accepted-socket admission through registration, idle timeout
and release. Local fixtures cover KeepTr publication, unsupported return, missing
binding, taken-map waits, captured cancellation identity and both assertion
locations. They are branch/interleaving checks, not claims that all fixtures are
source reachable.

The existing machine-wide ownership and allocation-supply theorem statements are
unchanged and now cover `releaseStep`. Entry-only edits preserve lease ownership;
supply preservation uses the existing `overwrite-bound` lemma. Their CSP lifts
continue to apply to arbitrary finite executions of this partial machine.

Check from the library root with Agda 2.8.0:

```sh
agda ConnectionManagement/CSP/InboundRelease.agda +RTS -M2G -RTS
```

[AwakeRemote promotion and WaitIdleRemote demotion](RemoteState.md) now preserve
different assertion/counter ordering: promotion checks deferred assertions before
counting and counts successful results only; demotion checks assertions first and
then counts every returned classification. Promotion may invoke pruning inside
its transaction, so its capacity-exceeded branch needs the actual pruning policy.
Over-limit promotion remains an explicit pruning frontier. Handler
cancellation/unwind integration, OG, bounded exploration and source replay remain
outstanding. No code-defect or liveness claim follows from these witnesses.
