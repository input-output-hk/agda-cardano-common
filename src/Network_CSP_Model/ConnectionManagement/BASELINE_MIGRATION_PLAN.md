# Model and proof migration plan

Status: M0 contract fixed; M1 runtime/proof integration in progress (kernel component invariants closed 7 November: per-key conservation, lane exclusivity, routing provenance, write enabledness), M2 in progress (7 November: configured startup kernel and invariant, configured egress installation, configured-role protocol/group/monitor selectors and lane routing; shared counter registry with pre-pool register, scopeDone retire and exit gating; M1+M2 batch strict acceptance passed 8 November at 16bec87); M5 synchronous LeiosDB waits and M3 scheduled-egress handler setup stages/unwind sites with outer-scope owner mapping (pool-relays cancel/join an explicit gap); M3+M5 batch strict acceptance passed 9 November; M4a lane waits/write lock/shared-bucket grants (e5699f2) and M4b governor tenure observations implemented 9 November; M4 strict acceptance pending. Migration started at the user's request
on `kangfeng/connection_management_new_source`, based on accepted `daf111d`.
Task Monitor goal `g-f038d197e9fe` tracks M0–M6. The [M0 profile](MigrationProfile.md)
fixes source units, state ownership and the first-batch compatibility interface. Authority: [source audit](../review/connection-management-source-baseline-audit-2026-11-06.md),
[design and G0–G5](DESIGN.md#9-implementation-gates-and-validation), and actual
maintained theorem types. Preserve accepted model commit `daf111d`.

Target exact consensus `2e44d98a843168ba3b189e305820b79943ac7d1e` and network
`2f1c154f248659b89523d5679ca532f442e7ed2a`; these are the audited pair, not a
moving branch designation. Existing model authority remains consensus585a861 /
network96ee6e until the final promotion gate. Record module-level migration
status explicitly while work is in progress.

## M0 unit correction (source inspection)

The source name `laneHeld` denotes one shared `Int` TVar for a mux run, not a
counter per lane. It counts outstanding batches. `esHeld` counts distinct batch
memberships for each `(MiniProtocolNum, Dir)` key, once per key per batch;
`esSent` counts bytes including SDU headers. Earlier audit wording saying
"held bytes" is corrected: zero-readiness conclusions remain, but the state
interface must preserve these distinct units. Key counters persist across protocol
generations; mux-held counts belong to a mux run, so any generation ledger must
project to the actual shared source keys.

Held release and `esSent` update follow normal `writeMany` return. Scheduled grant/
charge and Slice reservation can commit before the write; queued cancellation
and after-grant failure must not be given an invented refund. Direct credit
accounting occurs after the write. Source comment/code terminology about charging
needs explicit reconciliation; this is an open ambiguity, not a proved bug.

The empty-lanes/shared-held-zero predicate guards successful drain only. Timeout2
can also lead to Stopped/TraceStopped; never prove that every Stopped state has
zero held batches. Protocol clean completion has further source action/tracer/
result-cell guards beyond its empty/held data predicate. The [M0 profile](MigrationProfile.md) fixes these distinctions and controls;
actual kernel declarations are checked incrementally in M1–M2. The first frozen
accounting kernel passed its focused check/source review; integration, component
invariants/controls and composed acceptance are still in progress.

## Order and completion gates

| ID | Work and likely code surfaces | Required completion evidence |
| --- | --- | --- |
| M0 | Freeze source-to-model contracts and configuration. Expand changed source branches in SourceLedger: plain/scheduled mux, optional slice lane/counters, protocol DB waits, and included outer workers. Fix lifecycle state/event interfaces before large proof edits. | Every selected operation has an exact source anchor, owner, mask/wait/error behavior, and classification: implemented, explicit observation contract, justified exclusion, or remaining gap. No relevant changed operation is silently excluded. |
| M1 | Model outstanding egress ownership and readiness around `MuxProtocolJobs.cleanCommit` and `MuxGroupShutdown.drainEmpty`. Use lane-indexed queues, one mux-wide held-batch count, and per-(protocol number,direction) batch-membership counts. A batch containing several SDUs for one key contributes once. Keep any generation ownership ledger separate from the source counter keys and byte accounting. | Conservation/ownership and no-double-release properties; clean completion requires queue-empty and per-key held-zero; drain requires every lane empty and the shared mux-wide held-batch count zero. Queue-empty/held-positive controls reject both transitions. Partial/failed writes are not completed writes; cancellation alone does not invent zero held state. |
| M2 | Generalize mux infrastructure identity and pool closure: `Rules/MuxJobTypes`, startup, `MuxHandlerSupervision`, `MuxProtocolJobs`, `MuxGroupShutdown`. Represent the configured lane muxers and demuxer; incorporate byte-cell register/retire scope. Reuse unchanged generic JobPool laws. | Actual fork/register/result/removal/join histories for every configured worker, complete captured pool membership, no ID reuse/cross-lane confusion, counter retirement distinct from Async publication. Preserve timeout2 versus successful drain and independent caller receipt/return. |
| M3 | Extend pre-publication handler setup and owned outer scopes. Cover optional egress rule/rank-source/charge-sink installation, STM/rank tracing, counter attachment and their exceptional exits. Map countersLoop race, pool relays and included watchers to their actual owners. | Initialized setup-success and failure/cancellation paths with no fabricated handshake Left result or premature publication. New finalizers execute exactly once. Counter-loop/tracer failure can end the selected diffusion scope; excluded scopes must remain outside any all-worker claim. |
| M4 | Add selected scheduling waits and policy observations. Model Direct/Scheduled/optional Slice readiness, grants, writability, write-lock/write and cancellation cleanup. Extend included OG tenure/public-root observations and current-state result races. | Waiting/granted/cancelled states remain distinct; no double grant/accounting, stale waiter or timer leak in selected paths. Include post-grant cancellation and blocked write controls. Actual local-root/hot/tenure inputs are read at the correct source boundary. No fairness or universal progress claim without additional proof. |
| M5 | Update protocol-body completion contracts for synchronous DB writes. Use a small owned-wait interface at `executing`/body-return boundaries; distinguish the protocol collector, independent DB writer, queued job, completed promise and sealed failure. | A pending write prevents body return/clean completion; successful/error completion enables the matching result; cancelling the collector does not retract an already queued DB job or imply DB quiescence. Preserve actual ambient masking. Codec/payload abstractions remain explicit; no DB durability theorem is claimed. |
| M6 | Compose the migrated profile, update affected invariants/correspondence, run source validation, then promote the source baseline. | Strict maintained initialized acceptance plus affected source replays/build checks, reviewed dependency/profile manifest, and reconciled source ledger/docs. Only then switch global source authority to the audited pair. Preserve old results under their original pins. |

M1 precedes M2/M4. M3 uses the frozen configuration/job interface from M0/M2.
M5 can progress independently after M0, then joins the same composed runtime.
M6 depends on every contract included in the selected profile; an intentionally
smaller profile must be named and cannot be advertised as full prototype coverage.

## First implementation batch: readiness and pool ownership

Combine M1 and M2 as one acceptance batch, with focused checks during editing.
This avoids repeatedly rebuilding the large concrete regression suite for each
new shared field or role constructor. The first task is M0's precise state/lens
and event contract, followed by a small egress-accounting layer and its component
proofs before editing the full frontend closure.

Include these source-distinguishing scenarios:

- Queue empty, one batch held: refuse protocol clean completion and drain.
- Write completion releases the actual owner's held batch exactly once; then
  enable the corresponding clean completion/drain.
- One nonempty lane or any shared held batch blocks global drain; another lane's
  completion does not discharge unrelated outstanding batches. Exercise timeout
  separately.
- Cancellation during reservation/grant/write follows the selected source
  cleanup path; it neither manufactures successful write accounting nor skips
  physical pool cancellation/join/publication.
- Plain mux still enforces held-zero. Existing initialized inbound/outbound
  traces use explicit source-valid empty/zero initial egress state.

Keep the original birth/resources, captured release target/reply, caller guards,
raw-ack refusal, physical result publication and final CM wait. Do not replace
these statements with weaker readiness or quiescence claims to retain old traces.

## Proof migration

Carry forward unchanged CM/IG/Server/JobPool source-text evidence, while reviewing
changed callers/enclosing scopes. Existing theorems remain results about their
old definitions; source equivalence is a separate obligation.

For each runtime batch:

1. Prove new local state/accounting laws and component preservation facts first.
2. Extend existing origin, capture, supply, backing and collected-result proofs
   across every new writer. Do not omit a new action from an old universal claim.
3. Reuse generic pool/trace laws and opaque original histories. Adapt witnesses
   through proved constructors and endpoint equalities; keep actual events,
   chronological order, initialization and resource identities.
4. Check affected raw machine/process correspondence and projections. G4 model
   correspondence is not Haskell refinement.
5. Add focused positive and discriminating negative controls, then exercise the
   initialized release/cleanup/result/wait endpoint.

If a current proof statement is insufficient for a new claim, retain it and add
an explicitly stronger or separate theorem. Any necessary specification change
must be visible and justified, not hidden in extra premises or relaxed guards.

## Four concurrent roles, one checker

| Role | Ownership |
| --- | --- |
| Runtime/interfaces | Shared state/rules and component runtime edits; publish and freeze the batch interface before proof consumers edit. |
| Proofs/controls | Disjoint existing property/acceptance modules; local invariants, endpoint adapters and negative controls. |
| Independent source/review | Exact source branches, wait/mask/error contracts, ownership matrix and semantic review; documentation reconciliation after acceptance. |
| Integrator/checker | Compose changes, own the single Agda queue, record resource/check outcomes and run final acceptance. |

M3's source/setup work and M5's DB-wait contract/proof preparation can overlap
M1/M2 after their shared interface is fixed. Detailed scheduler policy work can
be prepared independently, but must consume the same held/lane ownership layer.
Assign file ownership explicitly; simultaneous edits to shared runtime types are
not parallel work. Consolidate acceptance in the existing endpoint rather than
proliferating fixture files.

## Validation and runtime budget

Use Agda2.8.0, guardedness and the standalone library setup. No new axioms, holes,
unsafe options or weakened goals. Run one bounded CM checker at a time; explicit
user authorization permits it alongside external project checks. Check available
RAM and keep the host-memory guard where workloads overlap.

During editing, check the changed small module and affected component/control
endpoint. At a ready batch boundary run the affected existing regression import
closure and a fresh strict
`Negative/ServerPeersOrigins.agda` check: own Checking line, checked:true,
DoneExiting, empty visible/invisible goals/warnings/errors, successful exit and
unchanged source hash. Confirm the final ordinary cached CLI separately. Invalidate
only the endpoint's own interface for an explicitly fresh check; keep other caches.

Use narrow imports, direct references to large concrete modules, opaque histories
and typed variable-endpoint adapters. Specify concrete successors and trace
indices. If elaboration stalls/exhausts its heap, locate the smallest failing
prefix and inspect conversion before another full run or heap increase. Reuse
successful component evidence; do not repeat unchanged expensive failures.

Static integrity audit, local-link checks, original diagram preservation and
accurate logs accompany each boundary. Source-only documentation needs no heavy
proof rebuild. Run native scenarios against the exact new pair when their
contracts change; record unperformed builds/backend checks explicitly.

## Baseline promotion and deferred work

M6 must report which new-source configurations are covered and which remain
explicit contracts. Preserve old replay seeds, scopes and assumptions. Build or
replay failures remain gates; a successful Agda load alone cannot promote source
correspondence or claim universal delivery/shutdown.

After promotion, resume caller-specific TIME_WAIT/post-mux delivery coverage on
the selected baseline. CM-I4c, admission/API quiescence, SI4/SI5, remaining G0–G5
work and bounded exploration/replay remain independently tracked; this migration
plan does not mark them complete. No proof implementation, source repin or commit
was performed when writing this plan.
