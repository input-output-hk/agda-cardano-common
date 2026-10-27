# Connection management source fidelity correction plan

Date: 27 October 2026.

Correct the verified model/source differences before extending proofs that depend
on those behaviors. The goal remains the executable CM/IG/OG/Server model and
its design gates; these corrections do not establish full source refinement.
The [review](connection-management-source-spec-review-2026-10-27.md) and
[assessment](connection-management-source-spec-review-summary-2026-10-27.md)
provide the findings and their qualifications.

Source authority remains network pin
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`. Part B concerns upstream specification
errata. Part C concerns a later snapshot and does not authorize moving the pin.

## Workstreams and dependencies

| ID | Findings | Action and acceptance condition | Status |
| --- | --- | --- | --- |
| CM-SF1 | A1 | Use one direction-tagged JobPool completion FIFO, preserving separate job outcome and queue publication transactions. Gate monitor consumption by handler phase. Check FIFO priority, initiator clean/error handling, restart before publication, and exactly-once consumption. | Implemented and checked for the current responder-capable profile; broader lifetime limits below remain open. |
| CM-SF2 | A2 | Represent actual IG tracer attachment. Inbound handlers attach it regardless of flow; outbound handlers require responder mode plus duplex. An absent tracer must emit no IG events or queue backpressure, including mux stop. Keep attachment distinct from counters becoming inactive. | Design and migration inventory complete; next semantic wave. |
| CM-SF3 | A3 | Restore source retry precedence before missing-descriptor failure for started traces: expired idle first, and initial AwakeRemote queue write before descriptor forcing. Preserve transaction atomicity and test expired/full/available cases. Treat completed traces separately according to their source evaluation order. | Integrated after SF1; helper and actual dispatcher controls pass. |
| CM-SF4 | A4 | Separate the model's target ordering predicate from production bounds and explicitly document invalid-input filtering. A source-faithful input profile would permit arbitrary overwrites and check the current value at selection. | Differences documented; executable target/input correction remains open. |
| CM-SF5 | A5 | State model/replay clearing delay 60 versus pinned production 120, and retries 5 in both. Keep this profile's historical witnesses rather than silently changing their policy. | Documentation corrected; no default change. |
| CM-SF6 | A6 | Distinguish abstract policy choices from production fault classification. Keep delivery acknowledgment separate from supervisor termination. A concrete policy/supervision profile needs explicit fault classes and delivery/cancellation behavior. | Differences documented; concrete production profile remains open. |
| CM-SF7 | A7 | State that STM retry rolls back generator splitting and preserves selection on unchanged inputs, while other threads can alter the generator. Preserve abstract admissible selection without claiming a concrete PRNG implementation. | Documentation corrected; concrete PRNG correspondence remains outside scope. |
| CM-SF8 | A8 | Correct API names and stale comments, while keeping Store admissibility/sampling and inbound/outbound origin-proof scopes distinct. | Documentation/comment corrections implemented; coordinator review completed. |
| CM-SF9 | A9 | Verify and repair source spans, adding distinct wiring/registry-cleanup references instead of overstating short ranges. | Citation corrections implemented; coordinator review completed. |

## Parallel execution rules

Three workstreams can proceed safely:

1. The completion-FIFO workstream owns shared mux, IG, subsystem semantics and
   their affected Agda proofs/scenarios. It integrates CM-SF1 as one coherent
   change; incompatible intermediate snapshots are not acceptance evidence.
2. The citation/comment workstream owns the assigned documentation and
   comment-only Store/Handshake edits. It then inventories CM-SF2 without editing
   shared semantic files.
3. The profile-documentation workstream owns Outbound.md and documents CM-SF4–7.
   It then designs CM-SF3 without editing the shared IG rules.

CM-SF2 and CM-SF3 are serialized with CM-SF1 because they edit the same mux/tracer
constructors, branches and exhaustive proof cases. Design and source inspection
can run concurrently; semantic mutations cannot. The coordinator owns integration,
acceptance review, this plan and PROJECT_STATE.md.

**Run one Agda process at a time across all workstreams.** Validation requires an
explicit coordinator handoff. Agents may search, edit disjoint files and perform
static audits concurrently. Preserve the original review/assessment, user edits,
configuration symlinks and source pin. No commits are implied by this plan.

## Completion FIFO design requirements

- Initiator and responder results share one queue, including their direction and
  protocol number; equal protocol numbers in opposite directions must not alias.
- A protocol result becoming visible to peer-state readers is distinct from its
  later JobPool queue publication. Capture pending outcomes independently of the
  mutable current protocol run so restart cannot erase an old result.
- Publication removes one pending result and appends it once. Consumption acts on
  the head only. Commands and on-demand starts cannot overtake queued results.
- Initiator clean results do not fabricate responder termination/counter events.
  Initiator errors fail the mux through the same monitor order and final tracing
  boundary as other fatal job results.
- The old direct failure action must not scan peer-state errors and bypass the
  queue. A compatibility action, if retained, can consume only a matching queued
  head under the normal monitor phase gate.

## Tracer corrections after FIFO integration

CM-SF2 needs an immutable per-mux tracer-attachment marker distinct from optional
responder counters. Attached tracers can clear their counters after deregistration
and still emit MuxFinished; absent tracers must skip sampling, descriptor lookup
and queue writes altogether. Keep the inbound install boundary attached even for
unidirectional flow, and add an explicit outbound allocation boundary deriving
attachment from mode and flow. Migrate actual outbound fixtures to that boundary.

Full initiator-only mode also requires separating shared mux-engine actions from
IG governor actions: the current noResponderMode rejects both. Whitelist actual
engine actions rather than enabling IG registration/batch operations. Update
allocation-monitor classifications explicitly; a new outbound boundary must not
silently bypass origin/admissibility monitoring. Acceptance includes full IG
queue controls for absent/attached tracers, inbound unidirectional tracing,
cleared counters on attached tracers, allocation freshness and noResponder IG
registration refusal. This is a separate wave, not a completed A2 fix.

CM-SF3 adds a pure preflight for started traces only. With a registered view and
active counters, expired RemoteIdle retries first; otherwise zero counters require
capacity for the initial AwakeRemote before forcing a missing descriptor. The
preflight never publishes its proposed queue: the existing final burst/counter
transaction must remain atomic. Completed traces do not use this gate because
source strict event construction forces their descriptor before queue capacity.
Test missing-descriptor starts with expired timers, full/99-element queues and
zero/nonzero counters; test a valid two-event hot start at capacity99 retries with
no partial event; retain completed-descriptor faults even when idle/full.

## Validation and integration gates

For each semantic correction:

1. Verify the affected branch at the exact source pin and record its observable
   transactions and event direction. Do not substitute a later main snapshot.
2. Typecheck the edited leaf, then the relevant subsystem endpoint, with Agda
   2.8.0 and the existing guardedness/options. Use the 2 GB heap limit where viable;
   avoid unconstrained elaboration before increasing resource limits.
3. Add focused positive and refusal controls. Distinguish injected fixtures from
   execution paths derived from initialization. Existing equations encoding the
   incorrect behavior must change; preservation theorem statements must not be
   weakened to accommodate the correction.
4. Repair affected inbound and combined capture/supply/ownership/map/reference
   proof closures. Validate handler-origin and lifecycle/failure witnesses where
   affected. Keep one Agda process globally and use incremental checks.
5. Run local hole/trust and whitespace audits. Report fresh Checking output versus
   reused interfaces, warnings/failures and any checks left unperformed.
6. Reconcile scope documentation and the checkpoint only after the corresponding
   acceptance evidence passes. Applicability of replay patches is not replay
   execution, and neither is a source-refinement theorem.

## Additional fidelity limits found during integration

The A1 acceptance claims concern FIFO consumption and phase gating in the current
responder-capable execution profile. They are not a full arbitrary-job-lifetime
refinement. Responder finishedJobs still publishes by protocol number, so delayed
repeated responder runs cannot choose their publication occurrence as freely as
the new initiator ordinal boundary. Shutdown completion also abstracts group
cancellation/join: without tracked lifecycle frames, stored pending results can
outlive a normal stopped snapshot. Source completed group shutdown excludes such
late publication. Keep these as explicit follow-ups rather than claiming global
queue/lifetime fidelity.

The current noResponderMode does not drive the shared IG mux-monitor actions.
Initiator-only consumption remains part of CM-SF2's engine/governor separation.
Do not add a FIFO-empty condition to the asynchronous handler-cancellation path:
source asynchronous teardown may legitimately leave queued job results unread.
Exactly-once publication means removal of one selected pending occurrence; it
does not mean an ordinal-labelled action is idempotent after indices shift.

## First execution wave results

CM-SF1 and CM-SF3 are integrated; CM-SF8/9 and profile documentation corrections
are complete in the worktree. Three delegated workstreams performed FIFO code/
proof migration, citation/comment fixes, and profile/tracer design and tests.
Shared semantic edits were sequenced and all Agda checks ran one process at a
time. This checkpoint covers the first wave; A2 remains the next semantic change.

The A1 leaf and proof checks passed Agda 2.8.0 at `+RTS -M2G -RTS`:
PeerActions, IGRegistration, Subsystem, MuxRetention, both subsystem invariant
lifts, and the revised combined-reference control. The focused
`Negative/InitiatorCompletionFIFO.agda` endpoint passed its ordering, event/counter,
direction-collision, phase, restart and ordinal-publication controls.

After A3 integration, the following endpoints also passed sequentially at the
same heap limit:

```sh
agda ConnectionManagement/Negative/TracerReadinessIntegration.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/TracerReadiness.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/InitiatorCompletionFIFO.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/SubsystemReferences.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/SubsystemSupply.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/SubsystemOwnership.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/SubsystemMapUnique.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/SubsystemMapReferences.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/SubsystemResources.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerIGMux.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerOrigin.agda +RTS -M2G -RTS
agda ConnectionManagement/CSP/IGRuntime.agda +RTS -M2G -RTS
agda ConnectionManagement/CSP/HandlerOutcomes.agda +RTS -M2G -RTS
```

The integrated acceptance and regression endpoints emitted Checking output,
except the last IGRuntime invocation reused its already checked interface.
Incremental checks reuse unchanged dependency interfaces; this is not a whole-cache
fresh build. Logs for the twelve-command batch are under
`/tmp/cm-review-20261027/combined-checks/`. The seventeen-file local proof audit
found fourteen inspected comparison operators and no new holes, postulates or
unsafe flags. Whitespace checks passed. Existing generic preservation theorem
statements were retained; scenario equations encoding the incorrect direct
failure transition were replaced with publication/consumption steps.

These are Agda model checks, not Haskell replay or source refinement. No replay,
upstream spec edit, source-pin migration or unrelated heavy network build was run.
CM-SF2 is the next semantic workstream; it must retain the no-tracer/cleared-counter
distinction and address initiator-only engine driving before claiming mode coverage.

## Remaining scope

A4 executable input semantics and A6 production-policy/supervision execution are
separate extensions after the mux corrections; documenting their current profile
is not equivalent to implementing them. Full concrete PRNG correspondence is not
needed for the present abstract profile. Upstream Part B errata can be drafted
later, with B12's conditional status and unverified PDF details retained. Part C
changes remain deferred until an explicit source-pin migration.
