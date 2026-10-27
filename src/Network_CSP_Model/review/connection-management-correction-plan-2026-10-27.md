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
| CM-SF2 | A2 | Represent actual IG tracer attachment. Inbound handlers attach it regardless of flow; outbound handlers require responder mode plus duplex. An absent tracer must emit no IG events or queue backpressure, including mux stop. Keep attachment distinct from counters becoming inactive. | Committed as `4268692`; 44 acceptance equations and 18 final regression endpoints pass. See the A2 execution results below. |
| CM-SF3 | A3 | Restore source retry precedence before missing-descriptor failure for started traces: expired idle first, and initial AwakeRemote queue write before descriptor forcing. Preserve transaction atomicity and test expired/full/available cases. Treat completed traces separately according to their source evaluation order. | Integrated after SF1; helper and actual dispatcher controls pass. |
| CM-SF4 | A4 | Enforce ordinary target bounds and select changed sane values from an overwritable input. Invalid raw writes must not block policy/wakeup; captured selections survive later writes. | Committed as `67a3c69`; checked in the nonnegative ordinary profile. |
| CM-SF5 | A5 | State model/replay clearing delay 60 versus pinned production 120, and retries 5 in both. Keep this profile's historical witnesses rather than silently changing their policy. | Documentation corrected; no default change. |
| CM-SF6 | A6 | Distinguish abstract policy choices from production fault classification. Keep delivery acknowledgment separate from supervisor termination. A concrete policy/supervision profile needs explicit fault classes and delivery/cancellation behavior. | Scoped peer-policy wrapper and delivery/local-rethrow boundaries checked; 32 acceptance equations and 16 regressions pass. Full cancellation/join remains open. |
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
registration refusal. This second-wave design is now implemented and checked; see the A2 execution results below.

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

The first wave did not drive shared mux monitors in noResponderMode. A2 now
separates shared engine actions from governor/responder operations and validates
initiator-only consumption; the earlier mode gap is resolved in the A2 scope.
Do not add a FIFO-empty condition to the asynchronous handler-cancellation path:
source asynchronous teardown may legitimately leave queued job results unread.
Exactly-once publication means removal of one selected pending occurrence; it
does not mean an ordinal-labelled action is idempotent after indices shift.

## First execution wave results

CM-SF1 and CM-SF3 are integrated; CM-SF8/9 and profile documentation corrections
are complete in the worktree. Three delegated workstreams performed FIFO code/
proof migration, citation/comment fixes, and profile/tracer design and tests.
Shared semantic edits were sequenced and all Agda checks ran one process at a
time. The first wave is committed as `b8d0081`; A2 was subsequently committed
as `4268692`.

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
CM-SF2 was the next semantic workstream after this checkpoint. Its implemented
no-tracer/cleared-counter distinction and initiator-only engine checks are recorded
in the second-wave results below.

## A2 execution results

First-wave corrections were committed as `b8d0081` before starting A2. The A2
worktree now adds a separate `TracerAttachment` marker, inbound/outbound allocation
boundaries, attachment-aware callbacks and direction-sensitive initiator-only
engine dispatch. Actual outbound witnesses use `installOutboundHandle`. Existing
origin/attribution/registry profiles explicitly refuse the new outbound boundary,
including unrelated IDs and empty registries, without asserting outbound origin.
The open machine still accepts the corresponding allocation.

Agda 2.8.0 checks ran sequentially with `+RTS -M2G -RTS`. The core/ordinary closure
passed `Rules/IGRegistration`, `Properties/HandlerIG`, and combined references;
the monitor closure passed `Properties/OriginMonitorInvariant` and the three
origin-profile negative endpoints. The final
`Negative/TracerAttachment.agda` check passed all 44 acceptance equations,
including actual initiator-only Machine allocation and Subsystem FIFO consumption
against a full IG queue. These fixtures remain conditional model controls.

The final regression batch also passed all eighteen endpoints:

- `Negative/{InitiatorCompletionFIFO,TracerReadinessIntegration,SubsystemReferences}`.
- `Negative/{SubsystemSupply,SubsystemOwnership,SubsystemMapUnique,SubsystemMapReferences,SubsystemResources}`.
- `Negative/{HandlerOrigin,OriginMonitor,AttributedOrigin,OriginRegistry,HandlerIGMux,RegistryProducer}`.
- `CSP/{HandlerOutcomes,IGRuntime,OutboundAdmission,GovernorLifecycle}`.

New/affected modules emitted Checking output during incremental validation;
repeated endpoints reused cached interfaces. In the final batch, SubsystemReferences,
HandlerOrigin, the three origin-profile controls, HandlerOutcomes, IGRuntime,
OutboundAdmission and GovernorLifecycle reused their already checked interfaces.
Other batch endpoints rechecked affected closures. Logs are in
`/tmp/cm-review-20261027/a2-checks/`. This was not a whole-cache fresh build.

The twenty-nine-file local proof audit found four inspected comparison operators,
not holes. No new axioms, unsafe flags or weakened existing theorem statements
were introduced. Whitespace checks passed. The first acceptance compile exposed
two fixture naming/import errors; those were corrected and all final checks
exited 0. No Haskell replay, upstream spec edit or source-pin migration was run.
A2 and its documentation were validated on top of `b8d0081`.

CM-SF4 followed this checkpoint; its ordinary-target bounds and overwritable-input
correction are implemented in the A4 execution results below. The fixed-profile
policy values remain unchanged; CM-SF6 production fault classification/supervision
is separate.
Broader responder publication ordering, shutdown/job lifetime and handler validity
limits remain open as stated above.

## A4 execution results

A2 was committed as `4268692` before implementing A4. The worktree now checks
`active ≤ established ≤ known` plus ordinary ceilings of 100/1000/10000. Environment
`setTargets` writes always overwrite, while target selection reads the latest
changed sane value. An invalid input disables only the target alternative and
leaves otherwise-ready policy and wakeup choices available. Selected target
values remain captured through a later overwrite and wakeup cancellation;
`applyAt` does not reread or revalidate the external input.

Pinned source verification covers Governor/Types.hs:265–283, Monitor.hs:55–95,
Diffusion.hs:631 and
the Governor STM-selection/timed-decision boundary. This is the default-target,
nonnegative ordinary profile, fixing omitted root/big-ledger targets and root
sets to zero/empty. Source negative Int values, root clamping and custom target
hooks are not represented. No global private-target-sanity theorem is asserted
for arbitrary injected initial states or forged pending decisions.

Agda 2.8.0 checks ran sequentially at `+RTS -M2G -RTS`. The core/world invariant
check passed. `Negative/TargetInputs.agda` passed 31 concrete equations and two
finite write traces for upper bounds, ordering, overwrites, ready alternatives,
priority and captured application/cancellation. The first test compile exposed
a missing product-constructor import, which was corrected; final checks exited 0.

Fourteen regression endpoints then passed:

- `Negative/{OutboundGovernor,Subsystem,GovernorOpenFailure,GovernorFailureLimit}`.
- `Negative/{SubsystemSupply,SubsystemOwnership,SubsystemMapUnique,SubsystemMapReferences,SubsystemResources,SubsystemReferences}`.
- `Negative/{TracerAttachment,InitiatorCompletionFIFO,TracerReadinessIntegration}`.
- `CSP/GovernorLifecycle`.

All batch endpoints rechecked affected modules except the final readiness and
lifecycle calls, which reused already checked interfaces. Logs are under
`/tmp/cm-review-20261027/a4-checks/`. The five-file local proof audit found 21
inspected comparison operators; no holes, postulates, unsafe flags or changed
preservation theorem types. Whitespace checks passed. No Haskell replay, upstream
spec edit or source-pin change was performed. A4 was validated on top of `4268692`.

CM-SF4 was committed as `67a3c69` before starting CM-SF6. Its source audit and
scoped executable correction are recorded below. Do not equate throwTo acknowledgment with completed
node shutdown. The fixed replay-policy values and abstract PRNG profile stay as
already documented.

## A6 executable peer-policy correction

A4 was committed first as `67a3c69`. The
[A6 source audit](connection-management-a6-source-audit-2026-10-27.md) checks the
policy and supervision finding against Git objects at the unchanged network pin.
It distinguishes the base policy supplied to peer-state actions from the
configurable handler extensions. The broad acquisition `SomeException` boundary
supports an explicit exception-class input; it does not justify assuming every
`ioFailure` is an ordinary `IOException`.

`Rules/PeerJobs` now retains the acquired `Fault` in `acquirePolicy`,
`nodeDelivery` and `nodeRethrow`. Delivery acknowledgment and the sender's local
rethrow/failed-establishment cleanup are separate actions. The exhaustive generic
peer-job and subsystem preservation layers cover the added PC/action without
changing their public preservation statements. Existing failure scenario
snapshots now name the captured fault.

`Rules/ProductionPolicy.Profile` is an explicit wrapper over the open subsystem.
Its immutable `ErrorId → Bool` classifier must agree with the original source
exception. Named CM faults are always peer-only; broad `ioFailure` consults the
classifier. Both governor-job and background-monitor dispatch enforce the same
policy, delivery and local-rethrow guards. The first successful fatal delivery
records its actor and fault. Ordinary interleavings remain possible afterward,
including before the sender's local rethrow.

A separate `completeShutdown` marks an externally supplied completed-supervision
boundary and freezes further wrapper actions. It is enabled only after a
recorded fatal peer-job delivery. It is not a cancellation implementation, a
resource-cleanup or join certificate, a process-termination result, or an
eventual-shutdown theorem. Handler-originated fatal exceptions remain outside
this wrapper's supervision claim. `step-projects` and `exec-projects` retain
ordinary subsystem actions and erase only the shutdown boundary; `Profile.Lift`
transfers existing subsystem safety invariants through that projection.

Validation passed sequentially with Agda 2.8.0 and `+RTS -M2G -RTS`:

- `Properties/SubsystemWorldInvariant` rechecked the new local-rethrow cases.
- `Rules/ProductionPolicy` rechecked the wrapper, projection and generic lift.
- `Negative/ProductionPolicy` rechecked 32 equations, universal stopped-action
  refusal, a three-step finite wrapper execution, its raw projection, and an
  application of the existing map-uniqueness invariant lift. These are conditional
  model controls, not initial-state source-reachability witnesses.
- Sixteen final regressions passed: `Properties/SubsystemInvariant`,
  `Negative/{SubsystemSupply,SubsystemOwnership,SubsystemMapUnique,
  SubsystemMapReferences,SubsystemResources,SubsystemReferences,TargetInputs,
  TracerAttachment,InitiatorCompletionFIFO,TracerReadinessIntegration,Subsystem,
  OutboundGovernor,GovernorOpenFailure,GovernorFailureLimit}` and
  `CSP/GovernorLifecycle`.

The three core/new endpoint checks emitted Checking output. Twelve final
regression invocations emitted Checking output; the readiness, subsystem,
outbound-governor and final lifecycle invocations reused checked interfaces.
Batch logs and the wrapper log are under `/tmp/cm-review-20261027/a6-checks/`.
During development, a preservation branch still used the old combined
failure-cleanup law after delivery was split; the final branch preserves the
unchanged world, and the separate local-rethrow branch uses the cleanup law.
Initial wrapper name-shadowing warnings were removed; final checks had no
warnings. The nine-file local proof audit found six inspected `≤?` comparison
tokens and no holes, new axioms or unsafe flags. Existing preservation statement
types are unchanged. Whitespace checks passed. No Haskell replay, upstream spec
edit, source-pin migration or unrelated heavy build was run.

The scoped peer-policy correction is implemented and checked, but full
cancellation/join correspondence remains an open part of CM-SF6. The next
supervision increment must represent scope-owned cancellation and joins before
replacing the external completed-supervision boundary with a derived one.
A6 validation was completed on top of `67a3c69`; this checkpoint includes the
scoped correction and its source/validation reports.

## Remaining scope

A4 is implemented for the documented ordinary target profile. Root/big-ledger,
negative-input and custom-target extensions remain separate. A6 now has a scoped
executable peer-policy profile; full production cancellation/join and supervision
correspondence remain open. Full concrete PRNG correspondence is not needed for the present abstract profile. Upstream Part B errata can be drafted
later, with B12's conditional status and unverified PDF details retained. Part C
changes remain deferred until an explicit source-pin migration.
