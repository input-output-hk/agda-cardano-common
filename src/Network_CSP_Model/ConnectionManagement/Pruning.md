# Over-limit promotion pruning

The promotion pruning frontier has been replaced by executable policy selection,
atomic entry writes and ordered cancellation delivery. `Rules/Pruning.agda` is the
pure selection/write kernel; `Rules/RemoteState.agda` retains the caller continuation;
`Machine.agda` commits the entire proposal in one event. Neither an intermediate
victim write nor a pending promotion write is observable as a separate step.

The source pin remains `96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`:

- [Core.hs:720–777](https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L720-L777): candidate construction, victim writes and cancellation action.
- [Diffusion/Policies.hs:284–306](https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/Diffusion/Policies.hs#L284-L306): the diffusion pruning policy used here.
- [Types.hs:239–261](https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Types.hs#L239-L261): connection-type ordering.
- [ConnMap.hs:63–83](https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/ConnMap.hs#L63-L83): omission of unknown-local keys.
- [ConnectionId.hs:43–53](https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionId.hs#L43-L53): remote-before-local ordering.

## Policy and transaction

The implemented policy is the diffusion policy, not the source's test-only
`simplePrunePolicy`. Candidate construction reads the current map and entry heap,
excludes unknown-local bindings, and retains inbound unnegotiated, inbound idle,
inbound active and duplex-active entries. It then inserts the prospective promoted
connection by requested key, replacing any same-key candidate.

Candidates are sorted in source connection-key order. Each receives one signed
score in that order. Stable policy sorting compares:

1. Upstream status: downstream first; among eligible candidates only duplex-active
   is upstream. Prospective outbound-duplex promotion is therefore upstream, while
   prospective outbound-idle-duplex promotion is downstream inbound-active.
2. Random score, ascending.
3. Connection type, using the source constructor and data-flow ordering.
4. Original key order, retained by stable sorting when all preceding fields tie.

The model uses stable insertion sort for small carriers; it does not claim the
source's asymptotic complexity. It selects the first `incomingCount + 1 - hardLimit`
keys, with `take` naturally saturating at the candidate count. Restricting the
candidate map to those keys restores connection-key order for cancellation.

All selected entry TVars are written to `Terminated Nothing`. The prospective
promoted state is written only when the requested key was not selected. These
writes and consumption of one random-input generation occur atomically. A malformed
reference or invalid score input returns no proposal; it cannot publish a partial
write list. These malformed-fixture rejections are not source STM waits.

```mermaid
sequenceDiagram
    participant IG as IG caller
    participant CM as CM map and entry TVars
    participant R as Random-score boundary
    participant H as Captured handler targets
    IG->>CM: Over-limit promotion transaction
    CM->>CM: Read current entries, insert prospective candidate
    R-->>CM: Current generation and scores in key order
    CM->>CM: Select victims; write all Terminated states
    CM->>CM: Write promotion only if self survives; consume generation
    Note over CM: One atomic machine transition
    IG->>IG: Check deferred assertion
    loop Selected candidates in connection-key order
        IG->>H: Request cancellation of captured worker
        H-->>IG: Delivery acknowledgment (explicit input)
    end
    IG->>CM: Separate counter-read transaction
    Note over IG,CM: May wait if another operation has taken the map
    CM-->>IG: Successful promotion result, even if self was pruned
    IG->>IG: Prepare and separately publish RemoteWarm
```

The self-pruned connection still produces a successful promotion result and IG's
RemoteWarm decision after the cancellation sequence and counter read. This follows
the source branch; it is not a claim that the peer remains live. Later mux/handler
notifications are separate. The unusual outbound-idle pruning transition trace in
Core.hs is still a diagnostic tracing abstraction; the modeled return retains the
old state used by the source's `fromState` projection.

## Randomness, delivery and ordering assumptions

`transactPruning generation scores` is an explicit input event executing the whole
transaction. Its generation must equal `Configuration.pruningGeneration`; its
score list must have exactly one element per candidate. A successful pruning
transaction increments the generation once. Ordinary `transact` handles branches
that do not prune. A scored action is refused when the current state no longer
needs pruning, without consuming its input.

This represents the occurrence of `stateTVar stdGenVar splitGen` and the ordering
of the policy's random scores. It does **not** implement `StdGen`, `splitGen`,
`randoms`, machine-Int width, a probability distribution, or reproducibility from a
seed. Scores use mathematical integers as order inputs; equal and negative scores
are retained. Generations distinguish draw occurrences, not random independence.
Concrete source replay must supply the scores from the pinned generator and verify
its state evolution. No theorem currently says every supplied sequence is
realizable from a Haskell seed. Score inputs and cancellation delivery remain
visible under the current CSP hiding policy.

Cancellation captures the selected worker IDs at commit. It does not look them up
again after a wait; replacement entries cannot retarget the operation. Delivery
acknowledgment is an environment input, not a derived handler-unwind transition or
a join on cleanup/TIME_WAIT. Full masking and handler supervision remain absent.

`ConnectionOrder.agda` now provides remote-before-local ordering for both pruning
and IG's expired-idle selection. This corrects the previous **model** helper, which
compared local first. The address order itself remains abstract family/host/port;
concrete socket-address ordering must be matched for replay. A regression reverses
local and remote preferences so the old comparison cannot pass accidentally.

## Evidence and remaining scope

`CSP/Pruning.agda` provides raw and hidden multi-victim traces, a self-pruning return
path, and branch checks for both promotion constructors. It checks upstream
priority despite lower upstream scores, score/type/key tie ordering, cancellation
map order, captured targets after replacement, atomic victim/promotion results,
blocked later counter reads, malformed/stale random inputs, generation advancement,
unknown-local exclusion, and delayed IG publication. These are local over-limit
fixtures; outbound acquisition is not implemented, so their reachability from the
accepted-socket initial state is not asserted.

The existing global ownership and allocation-supply theorem statements are
unchanged. Their new helper proves preservation across the pure list of writes;
Machine exposes only its final state. The CSP invariant lifts continue to cover
arbitrary finite executions, including the new pruning actions. No count-reduction,
full-state-validity, source-refinement or universal-liveness theorem is claimed.

```sh
agda ConnectionManagement/CSP/Pruning.agda +RTS -M2G -RTS
```

Next connect cancellation/mux/tracer termination to handler unwind and cleanup,
then continue outbound acquisition and OG. Seeded source replay, stronger runtime
validity and bounded exploration remain separate work.
