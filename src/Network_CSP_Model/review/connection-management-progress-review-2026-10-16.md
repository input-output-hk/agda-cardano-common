# Connection-management progress review — 16 October 2026

Reviewed after commits `99e6b41`, `540496b`, and `2ae7cb6`. This is a review
of current model definitions, theorem statements, source ledger and recent
witnesses. It is not a fresh audit of every proof or a source-refinement proof.
The earlier progress review remains a historical snapshot.

## Assessment

The architecture remains appropriate, and the inbound implementation has made
substantial progress. The next priority should shift from extending identity
certificates to executable source coverage and counterexample discovery. No
source defect is established by the recent registry witnesses.

The standalone dispatcher and its CSP process should remain. The registry is a
useful success-profile contract, but must not become the only system searched
for defects. Retain the open machine as the operational authority and make
contract violations observable during future exploration.

## Evidence now available

| Area | Current evidence | What it does not establish |
|---|---|---|
| Inbound lifecycle | Allocation-first admission, publication, CM result consumption, IG registration, release, handler unwind and cleanup in a 45-action registry trace | General source reachability, Server accept loop or outbound lifecycle |
| Early release return | 48-action trace separates caller return, IG unregistration, pool closure and socket cleanup | Eventual cancellation or cleanup under every schedule |
| Subsequent IG batch | 54-action trace drains and skips a late mux-finished notification after unregistration | Universal IG progress or readiness of another batch |
| Registered notification | Three-action local traces for stopped and failed muxes; ready/stopping and premature-commit refusals | Admission-derived notification production or replacement-mux reachability |
| Identity | Supported publication and attachment retain exact descriptor/mux identity through arbitrary accepted finite continuations | Live resources, source attribution of observer tags, or identity recycling |
| CSP | Productive process trees, machine/trace correspondence, projection and concrete non-traces | Full subsystem failures refinement, hidden divergence freedom or source deadlock |

The generic preservation results are stronger than individual examples. The
examples add concrete reachability evidence, but trace length is not a coverage
measure. A snapshot equality outside an execution path is only a fixture fact.

## Findings affecting direction

### 1. OG and outbound CM remain the largest functional gap

`Machine.Action` has admission, handshake, cleanup, handler, IG, remote-state and
inbound-release actions. It has no OG action family. The source ledger still
lists OG decisions, launch/completion handling and peer monitoring as outstanding
families. Outbound acquisition/reuse/release is also incomplete.

The original goal covers CM, IG, OG and Server together. Another series of
registry-only lemmas would not close that gap. G2's combined lifecycle remains
incomplete; G1 is also not declared complete by the implementation design.

### 2. A restricting monitor can hide the behavior being investigated

`Rules/OriginRegistry.step` accepts only when allocation/publication checks,
`Open.advance`, and all invocation monitors accept. Its projection proves that
accepted registry behavior is open-machine behavior. It does not prove the
reverse inclusion or that source executions always satisfy the monitor.

Consequently, a registry non-trace can demonstrate a contract check without
showing a source impossibility. A future explorer should distinguish an open
machine refusal from a monitor rejection and retain the latter as a candidate
contract violation. Do not report a monitor-induced block as a source deadlock.

### 3. The newest registered-event test is deliberately conditional

`RegistryRegisteredFinish.input` seeds an already-selected notification and
varies mux status independently. This is useful guard coverage, particularly
for current-registration lookup, but it does not close the producer path.
The ready/stopping cases are not proved reachable for the originating invocation.

The next bounded task should connect a real modeled producer to this branch.
Use responder startup and failure/stop actions, preserve the preceding startup
notifications, and execute their required CM calls. Do not delete earlier queue
messages or replace the IG continuation simply to reach the desired event.

### 4. Proof assurance currently exceeds exploration capability

The recent work checks selected schedules and generic finite safety properties.
The inspected implementation supplies no complete bounded action enumerator,
cutoff classification, counterexample minimization or source replay pipeline.
Singleton event refusals do not establish a state with no enabled actions.

Before using the model for bug discovery, define the supported finite scenario,
state the completeness obligation for its action enumeration, distinguish
bounds from semantic blocking, and preserve identities in exported traces.
Candidate failures then need validation against the pinned source and its
concurrency assumptions, preferably through a corresponding replay.

## Recommended sequence

1. Close the registered-notification producer path from accepted-socket admission.
   Acceptance: one checked trace through startup, actual notification production,
   IG selection, mux polling and removal, plus a targeted negative control.
2. Implement a minimal outbound CM/OG lifecycle for a fixed known peer. Include
   source guards, captured job arguments, in-progress bookkeeping, completion
   against current governor state, and release/cleanup boundaries. Avoid another
   broad invariant campaign before this lifecycle executes.
3. Combine inbound and outbound work on the same connection key. Exercise duplex
   reuse, delayed cleanup, current versus captured identity, and queued callbacks.
4. Add bounded exploration and replay for that declared scenario. Validate
   enumeration and cutoffs before interpreting blocking as deadlock.

Keep current invariants as regression checks. Add new general proofs when they
protect a changed rule or discharge a concrete scenario obligation. Keep timer,
exception-delivery, pool-join and policy-input assumptions explicit.

## Validation and scope of this review

The two newly committed increments previously passed Agda 2.8.0 checks of
`Negative/RegistryBatch.agda` and `Negative/RegistryRegisteredFinish.agda`, each
with `+RTS -M2G -RTS`, and targeted proof audits. This review does not claim a
fresh whole-library rebuild, term-level dependency axiom audit, current-upstream
source refresh, or implementation defect. Documentation whitespace is checked
with `git diff --check`.
