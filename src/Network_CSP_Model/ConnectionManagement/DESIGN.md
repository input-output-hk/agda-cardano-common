# Implementation design: CM, IG, OG and Server

**Design baseline: 14 October 2026; implementation update: 15 October 2026.**
The admission prefix, inbound handshake-result consumer, handler cleanup and local map/reference
preservation lemmas are available; see [README.md](README.md) for exact coverage.
A dispatcher for those slices, a productive CSP renderer, hiding and machine/trace
correspondence are also available. The full combined subsystem and source
correspondence remain unimplemented. Schematic declarations below describe the target design.

## 1. Objective and authority

Build a standalone executable model for finding source-code problems in the
combined connection-management subsystem. The first integrated lifecycle slice
must include CM, IG, OG and Server; the implemented admission/handshake slices are foundations
for that slice. The target model includes their shared state, action jobs,
peer monitors, handlers, mux lifecycle, protocol controls/results, and cleanup.

Network baseline: `96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`, pinned by consensus
`585a86117618ff86d7d5b541f9d23b03356d4c3a`. Use [SourceLedger.md](SourceLedger.md)
for exact paths and ranges. Section 5 of the network specification is a separate
comparison specification; implementation rules come from the pinned code.

The executable authority will be a **pure small-step machine with modular rule
families**. A productive `PTree` rendering and finite exploration interpret that
same machine. A separate parallel CSP presentation requires a correspondence
argument; do not implement two independent versions of the transition rules.

No imports from `Cardano_network`, `GovernorWedge` or `HotDemotion`. Selectively
adapt proof techniques and historical test scenarios with their assumptions
recorded. This design supersedes the earlier proposal to integrate connection
management into `Cardano_network`. The node-level picture supplies context, not
new executable semantics.

## 2. First scenario and abstraction manifest

Call the initial profile `LocalLifecycle`. It represents a local node in
initiator-and-responder diffusion mode. Use one listening address and two distinct
remote addresses, with explicit ports and full connection keys. Both remote
addresses can also be outbound targets. A connection may be accepted, acquired,
reused, released, replaced or awaiting cleanup.

| Aspect | Initial decision | Claim boundary |
|---|---|---|
| Server | One accept loop plus independent admission workers | Dual-listener races are a follow-up scenario |
| CM | Source state constructors, reservation/lookup, map ownership, admission/acquisition/release, remote activity, cleanup | No aggregate `connected`/`closed` state replacing source branches |
| IG | Actual event families, bounded queue, batch selection/cursor, publication, timers and exit path | No fused notification/registration operation |
| OG | Source establishment/activation/demotion decisions for a fixed known-peer set; jobs, completions and monitoring | Discovery and Cardano policy hooks are declared inputs or fixed configuration |
| Peer policy | Initially two ordinary known peers, no big-ledger special case; sane target updates via the source target-monitor interface | Guards and in-progress accounting remain source-derived; no arbitrary `demote` command standing in for OG |
| Negotiation | Version/feature profile fixed; either permitted data-flow outcome can be supplied by handshake contract | Not arbitrary renegotiation of an established bearer |
| Protocol layout | Hot: ChainSync, BlockFetch, TxSubmission2, LeiosNotify, LeiosFetch; established: KeepAlive; warm: empty | Peras and PeerSharing disabled in this profile |
| Protocol execution | Lifecycle contracts for each configured initiator/responder, with control-read points, waits, results, errors and cleanup | Not a full payload/codec model or a proof about all Leios behaviors |
| Application | Named ChainDB, mempool, fetch-work and Leios-resource contracts | No assumption that data or remote replies eventually arrive |
| Transport | Accept/connect/reset/read/write outcomes constrained by socket ownership and session identity | Tuple reuse and delayed failure detection explicit; no old-session delivery into a new session |
| Scheduling | Local worker interleaving; source STM alternative ordering | Fairness only in separately stated progress properties |
| Time | Tokenized untimed expirations initially | Race analysis only; no elapsed-time guarantee |
| Assertions | Enabled baseline; disabled variant named separately | Preserve exception/evaluation position, not just a diagnostic flag |
| Egress | Explicit may-block/may-progress send contract initially | Detailed scheduler ordering requires source mapping before scheduler-specific claims |

The protocol layout is fixed configuration; **running protocol instances are
dynamic**. There is no `linkConfig`, and no fixed upstream/downstream partition.
Negotiated duplex capability permits both initiator directions but does not imply
that both are currently used.

Start from initialized listener/governor infrastructure with no connections and
two known peers. Treat this as a post-initialization scenario state: supply a
source-valid setup prefix or explicit reachability premise before reporting a
whole-node counterexample. Initial ordinary-peer targets are known = 2,
established = 2, active = 1; demotion scenarios lower active to 0 through the
target-update interface. Local-root and big-ledger special cases are disabled.
Complete the other target fields and seed consistently with the pinned sanity
predicate during G0; these values do not bypass eligibility/backoff guards.

`LocalLifecycle` is a selected subsystem abstraction, not the full Leios node.
Every protocol contract must list admitted waits, control checks, outcomes and
cleanup dependencies. In particular, BlockFetch/ChainSync registry dependencies
and shared Leios peer-resource lifetime cannot be replaced by independent
instantaneous returns in a scenario that investigates those effects. Until these
contracts are reviewed, use them only for model sanity tests, not source claims.

### Exploration profile

The semantic machine uses fresh natural-number-backed identities. A finite
explorer applies a separate bound manifest. Initial trial limits are six total
socket/mux allocations, six mutable entries, 96 protocol-run allocations, 256
worker allocations, 256 timer allocations, 128 queued OG completions, and a
2,000-step search-depth cutoff. These are tunable search parameters, not proven
sufficient limits or bounds imposed on the Haskell implementation. Adjust them
after measuring actual lifecycle resource usage.

These are total allocations in the first explorer: no recycling, so old references
cannot alias new identities. Ordinary traces must fit before race exploration.
At least one scenario must admit three overlapping incarnations of a key while
another key is present. Semantic queues corresponding to unbounded source queues
remain unbounded; hitting an explorer limit reports `cutoff`, not `retry` or
`STOP`. The IG information queue retains the source capacity **100**.

## 3. Domain and state design

The following declarations are schematic design notation, not compilable Agda.
Implement small wrapper datatypes with decidable equality; do not use aliases that
make different identities definitionally interchangeable.

```text
PeerAddr           = address family + address + port
ConnectionKey      = local PeerAddr × remote PeerAddr
LocalKey           = unknownLocal | knownLocal PeerAddr
EntryId, WorkerId, SocketId, MuxId, PromiseId, RunId, TimerId, JobId
                   = distinct wrappers around fresh identifiers
ProtocolKey        = protocol number × initiator/responder role
ProtocolRun        = mux identity × protocol key × run identity
```

The CM map is structurally `remoteAddr ↦ localKey ↦ EntryId`, with separate
operations for exact-key lookup and source remote-address selection. Preserve
ordering and randomized selection semantics of the selected path: choosing any
matching entry is not automatically an exact abstraction of the source PRNG.
The first scenario may fix a seed; broader choices require explicit justification.

Use records and algebraic datatypes rather than a universal untyped heap:

| State record | Contents |
|---|---|
| `CMStore` | Global map TMVar state, entry heap, identity supplies, selection/random state |
| `Entry` | Source CM constructor and associated key, handler, handle, data-flow/timeout/error fields |
| `IGStore` | Published connections, fresh/mature duplex peers, counters, active flag, information queue |
| `IGFrame` | Batch, cursor, captured published state, event continuation and pending decision |
| `OGFrame` | Known/established/active state, targets, in-progress sets, captured timed decision, pending job launches |
| `JobStore` | Separate pool registries, OG completion queue, captured job arguments |
| `PeerStore` | Peer connection handles, status, temperature controls and protocol-result mappings |
| `ExecutionStore` | Handshake promises, mux states/commands, protocol runs and application-resource references |
| `TransportStore` | Sockets, owner/cleanup obligations, endpoints, failure visibility and pending IO |
| `TimerStore` | Fresh timer tokens, owner, purpose, armed/expired/cancelled state |
| `ThreadTable` | Worker kind, continuation, masking state, pending exception and completion state |
| `SupervisorState` | Scope relationships, failure propagation, cancellation/join continuations |

Source entry variants to retain: `ReservedOutboundState`, `UnnegotiatedState`,
`OutboundUniState`, `OutboundDupState` with its timeout flag, `OutboundIdleState`,
`InboundIdleState`, `InboundState`, `DuplexState`, `TerminatingState`, and
`TerminatedState`. Map absence is separate from `TerminatedState`.

The map TMVar has `full map` or `taken owner` state. A worker owning it keeps its
saved map and working map in its continuation. Restoring the saved map on exception
does not restore entry-TVar contents: those remain in the heap. A worker with a
captured entry reference can access it even while another worker owns the map,
where its source operation permits this.

Do not identify mutable entry identity with mux identity. Reserved/unnegotiated
overwrite can retain the entry while changing handler references. Old handlers,
jobs, timers, queue payloads and results remain until their actual lifetime ends.
Use ghost origin metadata for diagnosis only; do not add an identity check to a
source operation that receives only a key.

## 4. Worker continuations and execution ownership

CM is an API over shared state, not an actor. Represent a CM call by a typed
operation frame attached to its caller and a return continuation. No extra CM
request queue or service thread exists in the model.

| Worker family | Representative continuation phases |
|---|---|
| Accept loop | read limits → delay/wait → accept → capture socket → get local address → fork admission → next accept |
| Admission worker | include operation → take map → choose/admit entry → fork handler → put map → await promise → negotiated update → notify → return/close |
| OG loop | sample inputs/time → guarded STM decision → apply timed decision → publish view → launch jobs → next loop |
| OG action job | captured peer/handle → establish/activate/deactivate/close call → success or error handler → completion publication → deregister |
| Peer monitor | await first result/status → branch-specific action → wait for outbound demotion when required → status publication/loop |
| IG loop | select/flush batch → read published state → handle one event → execute CM/mux calls → publish decision → next event |
| Handler/mux | negotiate → allocate handle → publish promise → run mux → stop/fail → notification/cleanup phases |
| Protocol run | lifecycle-specific control/read/write/application wait → body return/error → bracket cleanup → observable result |
| Scope cleanup | initiate cancellation → await delivery/termination → restore/release resources → propagate outcome |

These are phase inventories, not permission to fuse neighboring phases. A frame
retains exactly the values already read by the source. For example, IG's
`MuxFinished` captures the mux found while handling that event; it must not perform
a fresh lookup every time its wait is evaluated. Similarly, `CommitRemote` retains
the IG snapshot across its caller-run CM operation and later publication.

Use explicit finite frame constructors for selected operation paths. Avoid an
arbitrary Haskell-like function closure in state, because it prevents equality and
finite exploration. An OG completion is a tagged captured-data record interpreted
against **current** OG state and time; it is not a replacement state snapshot.

## 5. Transition interface and atomicity

Proposed executable interface:

```text
Actor   = worker WorkerId | environment | runtime
Attempt = actor × rule identifier × explicit outcome/choice
advance : Scenario → State → Attempt → Maybe State

Step cfg s a s' = advance cfg s a ≡ just s'
```

`advance` is deterministic for a fully specified attempt. Nondeterminism is the
set of enabled attempts. An outcome field must be validated by the rule; it is not
permission to choose a forbidden result. Distinct diagnostic attempts may project
to the same external event. Keep them distinct until the semantic rendering
accounts for all successors.

`environment` identifies external inputs; `runtime` identifies modeled timer or
exception-delivery effects where no application worker performs the step. These
tags record provenance, not additional threads or a scheduler process. Runtime
effects must still satisfy the source-specific readiness and masking conditions.

`nothing` means the rule cannot complete now. A separate explanation function may
return a wait reason for diagnostics; it must agree with enabledness and must not
become another scheduler rule. A blocked STM transaction does not consume a step.

Rule families inspect one authoritative state. No field-by-field store processes
may interleave inside a transaction. Ordinary IO boundaries and actual source
locks retain their interleavings:

- Commit every STM read/guard/write group atomically. STM failure rolls back its
  writes; exception handling runs subsequently in the worker continuation.
- IO `modifyTMVar`: take → body → put, with saved-map restoration on exception.
  STM `modifyTMVarSTM`: take/body/put commit as one transaction.
- Preserve `orElse`/`FirstToFinish` branch ordering; do not replace it with an
  unconstrained choice among simultaneously ready alternatives.
- Fork makes a child runnable at the source fork point. Parent registration can
  follow later; job deregistration may wait for that registration.
- Queue flush removes a complete snapshot into a batch. Event processing is later.
  An atomic producer burst requires space for the whole burst.
- Cancellation request, blocking sender, delivery, unwind and final completion
  are distinct. Model unmasked, masked-interruptible and masked-uninterruptible
  execution, with delivery allowed only at justified points.
- An untimed timer can expire only after arming; firing, cancellation and stale
  references use the captured token. It supplies no deadline or fairness theorem.
- Keep protocol body return, cleanup completion, result publication and mux
  terminal status distinct whenever the source separates them.

### Expanded example: IO map update

```text
mapTake:
  guard: caller at TakeMap, map full
  effect: map becomes taken(caller), caller saves map and enters body

bodyCommit:
  guard/effect: exact source transaction over the entry heap
  interleaving: other workers can act; map readers cannot complete

mapPut:
  guard: caller owns map, body returned
  effect: publish returned map, continue caller

mapRestore:
  guard: caller owns map, exception reached the helper's handler
  effect: publish saved map, retain current entry heap and IO effects,
          continue exception propagation under the source masking rules
```

Each of these is a rule family further specialized by caller/phase. The ledger
contains expanded admission and release cases, including assertion ordering.

## 6. Events, process rendering and outcomes

Separate actual source effects from diagnostic labels. A transition label adds no
extra handshake or blocking tracer. The real inbound mux tracer is an exception:
its queue/counter operations are actual source effects and remain executable.

Use an event family compatible with existing `PTree` conventions:

```text
DiagnosticEv : Set → Set
  execute : DiagnosticEv Attempt

Diagnostic cfg s : PTree DiagnosticEv (ExtI DiagnosticEv) Outcome
```

An enabled `execute a` continues at `advance cfg s a`; disabled attempts are absent
from the offer map. Define this productively using the existing `.force`/`react`
pattern and `{-# OPTIONS --guardedness #-}`. This is a proposed shape, not a
typechecked declaration. Resolve precise universe levels and equality instances
when implementing `Events.agda`.

`Observation` classifies attempts as internal or externally meaningful (transport,
policy/application input, selected lifecycle outcomes). First retain full labels
for diagnostic traces. Hide internal execution labels to obtain the behavioral
process. When projecting multiple labels to one observation, preserve all
successors using the library's renaming/branching semantics; do not arbitrarily
pick a successor in an offer map.

The running node does not terminate merely because it has no current connections.
Use successful process termination only when a modeled scope has actually exited
and its required cleanup has completed. Fatal errors are explicit observed
outcomes followed by source supervision/cleanup, not immediate silent `STOP`.
Healthy idle service can offer only environmental events and need not be an error.

Keep explorer cutoff outside the source transition relation. Reports distinguish
successful termination, source error, genuine blocked state, divergence and
bounded-search cutoff. Internal self-loops for blocked waits are forbidden.

## 7. Modules and dependency order

```text
Domain → Scenario → State → Events
                       ↓       ↓
                     Rules/*
                       ↓
                    Machine
                       ↓
                    Process
                       ↓
                 Correspondence
                       ↓
             Scenarios / Properties
```

`Domain` owns finite enums and distinct identity wrappers. `Scenario` owns immutable
configuration and declared environmental contracts. `State` owns records/frames;
do not make it import executable rules. `Events` owns attempts and observations.
`Rules/*` returns proposed successor states; `Machine` dispatches by rule family
without duplicating behavior. Rule helpers must not create import cycles.

Rule modules: `Server`, `CM`, `IG`, `OG`, `PeerActions`, `HandlerMux`,
`ProtocolLifecycle`, and `Supervision`. Add small generic memory/timer helpers only
where they actually reduce duplication. `Finite`/`Export` follows a stable machine
interface and is not a prerequisite for initial Agda witness proofs.

There is no new Agda library configuration: this namespace lives in the existing
standalone `cardano-network-csp` library and uses only its generic dependencies.
Do not create empty module scaffolding before the type boundary is settled.

## 8. Proof obligations and initial properties

Prove the cheap structural layer first:

1. `advance`/`Step` agreement by construction and deterministic successor for a
   fully specified attempt.
2. Machine step ↔ diagnostic process transition, and pure runs ↔ traces.
3. Reference validity and map-ownership preservation, allowing old-but-live
   references and the source's temporary mismatches.
4. Enabledness agreement for bounded enumeration on non-cutoff states.
5. Appropriate stable-offer/refusal and divergence correspondence before exporting
   those claims between renderings. Trace equality alone is insufficient.

Then define source-sensitive monitors:

| Monitor | Intended evidence |
|---|---|
| Socket obligation | Accepted socket remains attributable to handoff, handler or cleanup until closed |
| Map ownership | Put/restore belongs to the taking worker; saved map restoration does not roll back the heap |
| Identity-sensitive cleanup | Source identity-checked deletion does not delete a different entry |
| IG obstruction | A specified pending event cannot be serviced while the IG waits on another key's target |
| Completion correctness | Successful action completion has the required results and current-status checks |
| OG bookkeeping | In-progress sets/jobs/completions agree at the source-defined milestones |
| Session separation | Old results/traffic cannot be attributed to a new run without a permitted source mechanism |

Monitors observe transitions or ghost state; they never veto a bad transition.
Not every stale reference or transient mismatch violates a property. State the
precise obligation and its start/end milestones. An IG wedge witness must include
a reachable wait and explain why permitted future events cannot discharge it under
the scenario, rather than just exhibit a finite prefix without progress.

Add positive lifecycle traces and intentional negative controls. Example negative
controls: remove an identity check; fuse map restoration with heap rollback;
pretend mux stop is immediate; shrink the IG queue below the maximum atomic burst.
Each control should demonstrate the particular property/distortion intended, not
be advertised as a real-source defect.

## 9. Implementation gates and validation

| Gate | Work | Acceptance evidence |
|---|---|---|
| G0 | Domain, scenario and source ledger | Identity distinctions, profile assumptions, first-path branch coverage reviewed |
| G1 | State and primitive semantics | Map take/restore, STM retry/rollback, fork, promise, queue and cancellation examples |
| G2 | First combined lifecycle | Server admission, OG jobs, IG handling, handler/protocol lifecycle and clean release all run from initial state |
| G3 | Concurrency | Two peers, duplex reuse, delayed cleanup, same-key overlap and job/monitor interleavings |
| G4 | Semantic bridge | Machine/process transition and trace correspondence; monitors and negative controls |
| G5 | Exploration/replay | Bounded enumeration/export checks, minimized candidates, source-operation replay |

Develop G2 in small paths, but do not declare the subsystem modeled after only a
CM or IG path. First witnesses: inbound clean lifecycle; outbound clean lifecycle;
duplex reuse; handshake failure and socket cleanup; successful hot demotion;
timeout-driven cooling with delayed cleanup. Some profiles may not admit a desired
trace; diagnose the source guards rather than weakening them to force success.

Run Agda 2.8.0 from this library root, one process at a time. Typecheck each actual
new module, its downstream correspondence/scenario endpoint, and the relevant
negative controls. Preserve guardedness; no postulates, holes, unsafe termination
pragmas or weakened goals. No heavy `Cardano_network` proof rebuild is needed for
this independent namespace. Reusing a generic law requires checking its premises.

The design and ledger are documentation-only and need no Agda check. Future
reports must distinguish cached checks, fresh elaboration, bounded searches,
proved statements and source replay. Do not call a candidate a code defect solely
because the abstract model admits it.

## 10. Remaining implementation decisions

These are concrete work items, not permission gates:

- Expand every selected source branch listed as a family in the ledger before
  implementing it; record exact reads/writes and masked/interruptible points.
- Complete lifecycle contracts from the pinned protocol/registry sources. Keep
  detailed pipeline contents deferred until they influence the target scenario.
- Resolve timeout/promise/cancellation helper behavior from the pinned dependency
  versions; use `IOSim` behavior for replay and state any GHC-specific assumptions.
- Fix the initial policy seed/targets and generate ordinary source-valid traces.
- Review the egress boundary before any claim about scheduling-induced stalls.
- Select an exporter only after confirming tool availability and the intended CSP
  semantic model. No exporter or FDR run is assumed to exist today.

The immediate coding entry point is `Domain.agda` and `State.agda`, followed by
the primitive rules and admission path in the ledger. G0/G1 provide the small
reviewable foundation before the combined model grows.
