# Connection-management progress review

Review date: 15 October 2026. Scope: the current `ConnectionManagement` tree,
including the uncommitted supply-bound work. This review assesses direction and
claim boundaries; it is not an independent proof of Haskell/model correspondence.

## Assessment

**The architecture is appropriate. The next priority should be executable source
coverage and integrated scenarios.** Keep the standalone small-step machine and
its CSP interpretation. Keep the ownership and allocation-bound invariants as
regression checks. Defer another broad invariant campaign until the model executes
a meaningful governor/handler interaction.

The objective remains finding problems in the combined CM/IG/OG/Server source.
The current result is a checked foundation for that investigation. It has not yet
reached the first integrated lifecycle gate in the design, and no source bug has
been demonstrated by the new model.

## What is working

1. **Independence and identities.** The new model imports neither `Cardano_network`
   nor the historical GovernorWedge/HotDemotion models. Mutable entry identity,
   connection key, handler, handle and promise are distinct. Fixed protocol
   configuration does not stand in for dynamic connection use.
2. **One executable authority.** `Machine.advance` dispatches source rule families;
   the `PTree` renderer interprets that same function. The step/trace correspondence
   is meaningful assurance that the CSP layer does not silently change the machine.
3. **Concurrency boundaries.** Admission, result consumption and cleanup distinguish
   the map TMVar from entry TVars. IO take/body/put, map-only restoration, captured
   entries, counter reads and atomic TIME_WAIT finalization remain separate where
   required. These are the sorts of details relevant to race analysis.
4. **Checked structural safety.** Ownership and entry/promise supply bounds are now
   preserved by every action of the current partial machine and by finite execution.
   Raw CSP executions recover endpoints satisfying the corresponding invariant.
   They require only their stated initial predicates; they do not smuggle in a
   global reference-validity or scheduler premise.
5. **Useful negative controls.** Heap rollback, deletion by key alone, split
   finalizer commits, dangling map references and weak freshness assumptions each
   expose a specific modeling mistake. The ownership and future-ID fixtures are
   now excluded from reachability from the accepted-socket start.

These results justify confidence in particular aspects of the model. They do not
validate omitted source behavior or prove eventual release of a held resource.

## Coverage against the intended subsystem

| Area | Implemented evidence | Remaining gap for source investigation |
|---|---|---|
| CM inbound path | Admission, handshake consumer, handler cleanup | Outbound acquire/reuse/release, remote transitions, pruning |
| Server | Admission worker after accepted-socket handoff | Accept/rate-limit loop, handling CM returns, scope supervision |
| Handler/mux | Publication and exit boundaries; explicit cleanup | Negotiation, handle/control allocation, mux run/stop/stopped, tracer blocking |
| IG | CM notification producer; queue/batch kernels added by this review | Event payloads, batch guard computation, frame/cursor, registration, event handling and publication |
| OG | Design and source locations | Decisions, jobs, completions, peer monitors and progress bookkeeping |
| CSP | Productive process, hiding, step/trace correspondence, singleton refusals, invariant transfer | Validated observation contract, hidden divergence analysis, source conformance |
| Exploration | Explicit finite model witnesses | Complete bounded action enumeration, cutoff handling, search/minimization, source replay |

The implementation is partway through the foundation and lifecycle gates, with
some semantic-bridge results already complete. It is not accurate to call G1 or
G2 complete: cancellation and several runtime primitives remain missing.

## Findings and priorities

### High: source coverage is now the limiting factor

The recent invariant work is useful, but does not add governor behavior. At this
review snapshot, before adding the queue/batch kernels, the `Properties` directory
contains 24 Agda modules and 2,430 lines, while the four operational `Rules` modules
contain 448 lines. Those counts
are a snapshot, not a quality score; they illustrate why the next increment should
exercise more source behavior rather than repeat the same progress pattern.

**Decision:** retain the proved properties, but do not require whole-state
uniqueness/reference preservation to be finished before implementing the next
source-backed slice. Discharge concrete fixture validity and any new local
obligations needed by that slice. Full explorer validity remains required before
interpreting search results as source deadlocks.

### High: abstract handler exit cannot expose the intended blocking dependency

A freely supplied publication/exit boundary does not model whether the mux thread
can reach it. In particular, the real tracer runs in the mux/handler context and
can wait on the information queue or an expired-idle condition. This is a missing
producer/governor dependency, not something a stronger allocator proof can repair.

**Decision:** connect the information-channel operations to IG batching and then
to an explicit tracer/mux lifecycle before investigating a wedge. Give each external
boundary a named contract. Do not let the environment force a blocked handler past
its missing source wait.

### High: registration, draining and processing are different operations

The source batch transaction chooses among maturity, the first ready peer commit,
queued messages and inactivity, in that order. It then processes the resulting
list sequentially with a fresh published-state read per event. `NewConnection`
starts responders and publishes the successful registration in one STM transaction;
registration must not be fused with CM notification or split into independently
visible responder-start and registry-publication steps.

**Decision:** implement a batch frame/cursor and the relevant event union next.
Derive readiness from the source state, captured time, timers and ordered peer
fold. Supplied readiness candidates in the new pure kernel are a contract for
future integration, not arbitrary machine actions.

### Medium: model proofs and source evidence need separate reporting

Raw trace correspondence relates two representations of our model. Concrete
`refl` witnesses test its equations. Both are valuable, but neither establishes
that Haskell can execute the same trace. Similarly, a singleton refusal can be
healthy contention, a wrong-phase attempt or a malformed fixture.

**Decision:** for each investigation, record the source path, initial-state
premises, environment assumptions, captured identities, expected invariant and
replay plan. Classify findings as model distortion, abstract candidate or
source-confirmed defect. Continue using negative controls without calling them
source defects.

### Medium: observation and proof maintenance need attention before growth

The visible CM-return label omits its completion payload, so different returns can
have the same observation. The raw machine still records the result. Avoid using
the present hidden alphabet to assert API-outcome equivalence.

The preservation proofs explicitly enumerate many disabled phase/action pairs.
This gives coverage checks, but adds maintenance cost when continuations grow.
Reuse local projection/transaction lemmas when changing those proofs; keep the
operational rules authoritative. A broad proof refactor is not the next priority.

## Source recheck and immediate continuation

The earlier temporary checkout was unavailable, so this review fetched the following
files again at the existing fixed network pin
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`:

- [InformationChannel](https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor/InformationChannel.hs): capacity 100, single read/write and whole-queue flush.
- [InboundGovernor](https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor.hs#L242-L278): batch alternatives, registration and tracer call sites.
- [Synchronisation](https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/monoidal-synchronisation/src/Data/Monoid/Synchronisation.hs): `FirstToFinish` composition through `Alternative`, interpreted here with ordinary left-biased STM alternatives.

This was a focused recheck, not a new audit of every source-ledger branch or a
verification of current upstream branch heads.

The continuation made during this review is deliberately limited:

- `Rules/InformationChannel.agda` implements FIFO read/write, unconditional flush,
  and the queue effect of multiple writes in one STM transaction. A failed burst
  exposes no partially committed successor queue.
- The existing handshake enqueue delegates to `writeMessage`; its capacity and
  FIFO behavior are retained.
- `Rules/IGBatch.agda` implements the ordered selection kernel for already-derived
  readiness candidates. It is not an IG worker and adds no `Machine` action.
- `Scenarios/IGBatch.agda` checks real-capacity backpressure, a three-message burst,
  whole-queue draining, branch priority and the distinction between a retained
  batch and newly queued messages. A two-message prefix fits where the three-message
  transaction retries, exposing the error in splitting that source transaction.

Queue payloads are total Agda values; source payload-evaluation exceptions are
outside this kernel. Tracer counters and all other effects must eventually commit
with their queue writes in the same rule. The current `State.inboundInfo` still
contains only `NewConnectionInfo`; no claim of full IG event coverage is made.

## Next acceptance milestones

1. **IG batching and registration:** replace the notification-only queue with the
   required source event types; derive ordered readiness; retain an IG batch/cursor;
   execute new-connection registration and duplicate notification handling with the
   source atomicity. Deliver a machine/CSP trace from CM notification through IG
   registration, including drain-before-processing behavior.
2. **Handler/tracer interaction and inbound release:** add mux states and commands,
   tracer transaction/counter effects, captured-mux waits and caller-run CM release.
   Revisit GovernorWedge scenarios as tests with the new model's own source pin and
   assumptions; do not import or merge the historical model.
3. **OG plus complete lifecycle:** add outbound acquisition/reuse and selected
   establishment/demotion jobs with completions/monitoring. Deliver one combined
   Server/CM/IG/OG lifecycle before declaring G2 complete. IG work must not become
   a substitute for the explicitly requested OG coverage.
4. **Investigation tooling:** validate finite action enumeration and cutoff handling,
   add targeted search/monitors, minimize candidates and replay the selected source
   operations. Expand structural invariants where required to interpret results.

Do not delay all behavioral investigation until every optional invariant is proved;
do not label an incomplete-model stall a source deadlock. Each milestone needs a
source ledger update, positive path, relevant negative control and scoped claim.

## Validation of this increment

Agda 2.8.0 checks passed for `Scenarios/IGBatch.agda`,
`Scenarios/OwnershipInvariant.agda`, `Scenarios/SupplyInvariant.agda`,
`Negative/CleanupAtomicity.agda` and `Negative/StaleHandshake.agda`, each with
`+RTS -M2G -RTS`. The new kernel endpoint and affected invariant/cleanup closures
were freshly elaborated, as was the stale-handshake endpoint; unchanged dependencies
could use cached interfaces.
The local static audit found only the `?` in the standard `_≤?_` comparison,
not an Agda hole. Local documentation links and `git diff --check` passed.
No bounded search, source replay or complete-subsystem check was performed.

## Subsequent implementation: first IG registration prefix

The [first-batch implementation](../ConnectionManagement/IGRegistration.md) now
provides a dispatcher-integrated notification-to-registration CSP trace, with a
retained batch, per-event state read and duplicate handling. It specializes
readiness to an empty initial registry and uses an explicit successful responder-
startup boundary. This advances milestone 1; the full event union, general
readiness and actual startup/mux/tracer behavior remain outstanding. The coverage
table and earlier kernel discussion above describe the review snapshot before
this subsequent increment.
