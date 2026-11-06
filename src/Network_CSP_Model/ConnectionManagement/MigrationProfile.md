# Migration profile and interface contract — M0

6 November 2026, branch `kangfeng/connection_management_new_source`.
This fixes the first M1–M2 batch's interface and source interpretation. It is not
an implementation, source-refinement theorem, global repin or completed G0 gate.
[Plan](BASELINE_MIGRATION_PLAN.md) and [audit](../review/connection-management-source-baseline-audit-2026-11-06.md)
retain the overall scope and original proof authority.

Target: consensus `2e44d98a843168ba3b189e305820b79943ac7d1e` / network
`2f1c154f248659b89523d5679ca532f442e7ed2a`. Preserve `daf111d` and its old-pin
acceptance. Each changed module must distinguish target-source operations from
legacy plain compatibility behavior until M6 promotion.

## First-batch configuration and units

| Interface | Frozen meaning |
| --- | --- |
| Plain | One Scheduled-labelled source queue, Unscheduled behavior, one muxer then demuxer. No grants are implied by that lane label. |
| Scheduled | Actual Direct, Scheduled and optionally Slice queues/muxers, then demuxer. No slice bucket means Slice routing falls back to Direct; no phantom worker. |
| Persistent key | `(protocol number, direction)`, registered at mux creation. Counters survive protocol generations; unknown keys are not automatically ready. |
| Wanton identity | A particular protocol-job send buffer, separate from its persistent key and generation/history identity. Empty means taken, not sent. |
| Held ownership | One shared signed batch count per mux run; each distinct key in a batch has one signed membership count. Repeated same-key SDUs do not add memberships. Global count is not the sum of key counts. |
| Bytes | Per-key successful sent bytes include headers. Keep them distinct from held counts, queue entries and scheduling charges. |
| Batch witness | Internal identity/owner/lane, distinct member keys and wire contributions. At most one actively constructed/written batch per lane muxer; a failed lane does not start another batch without a real lifecycle transition. Witness IDs are not source allocations/threads. |
| Arithmetic | Unbounded signed held counts require reachable non-underflow proofs; unbounded byte totals use an explicit non-overflow execution profile. No claim that source Int/Word64 have these unbounded types. Never use saturating subtraction to hide duplicate release. |

Authoritative queues/key cells/run accounting live once in the existing source
Mux under IG execution. A small key/equality-parameterized `Rules/MuxEgress`
component supplies lane/configuration and accounting types without importing
MuxRuntime back into itself. MuxRuntime instantiates it using its actual key.
Protocol/Group/frontend layers only query or invoke real IG → Machine → O.advance
writers. No duplicate independently writable readiness state or metadata-stutter
claim for a source update.

## Transition boundaries and source anchors

All network paths below are under `network-mux/src/` at the target pin.

| Operation | Atomicity, guard and accounting contract | Source |
| --- | --- | --- |
| Open batch | First dequeue/fragment take plus first key membership and global held acquisition commit together. No queue-empty/held-zero gap. | Egress243–247 |
| Extend batch | Subsequent queue try-read and fragment take are separate STM operations. Deduplicate key membership within the existing held batch; do not increment global held again. | Egress340–402 |
| Grant/wait | Scheduled sink/budget and Slice reservation may commit before write. Queued waiter cancellation does not refund a granted request or release a held batch. Detailed grant algorithms and their actual charge/refund controls remain explicit M4 gaps. | Egress263–289; Bucket674–888,1070–1088 |
| Write/account success | Actual writeMany return followed by one STM held release, per-key sent credit and Direct post-write credit. Masking permits blocking-write interruption, not a free async gap after successful return before nonblocking accounting. | Egress298–309 |
| Failure/cancellation | Before accounting commit, no successful held release/esSent update. Already granted Scheduled/Slice charges persist. Preserve failed/unreleased batch ownership; do not manufacture drain success on exception. | Egress263–309 |
| Protocol clean completion | Actual body/tracer/result-cell path plus empty want and persistent key-held zero; data readiness alone is not complete event enabledness. | Mux528–553 |
| Successful drain | Every configured lane queue empty AND shared run-held zero. | Mux763–776 |
| Timeout | Preserve distinct timeout2 elapsed observation; Stopped/TraceStopped may follow expiry without successful drain. No eventual-delivery assumption. | Mux763–776 |
| Pool/retirement | Register counter cells before pool entry. After entry, real pool bracket close and, on async owner failure, the inner Failed/Dead/rethrow catch continuation precede retirement; acquisition failure before entry retires via the actual outer-finalizer failure path without fabricating a closed pool. Retirement transfers byte totals/removes registry row; it is not held release, physical Async result or handler completion. | Mux408–434; Counters221–239 |

The source comment that a throwing write is neither counted nor charged is
ambiguous against committed pre-write Scheduled/Slice effects. Follow actual
code timing and retain this documentation ambiguity; do not claim an unintended
Haskell defect or invent a universal refund.

Traffic ingestion must match the source send path: append to an existing Wanton
and enqueue its demand only when the old payload was empty (Mux918–941). Do not
invent independent duplicate queue entries for each send. No generic positive
payload guard follows from takeSingleWanton or raw send: even empty fragments
have an SDU header. Any nonempty encoding restriction must be a named source
profile assumption, not silently built into the kernel.

## Infrastructure and proof compatibility

Keep `TypedResult` unchanged: all configured lane muxer errors map to the same
existing `infraMuxer` tag; source MuxerException has no lane payload. Extend
physical role/binding identity for actual lane workers, not the result tag.

Keep existing plain Startup.PC/State constructor arities and actions. Add one
configured continuation/frame and configured action family sharing the SAME
Startup.pool. Freeze immutable ordered role plan, actual historical Role→JobId
bindings and fork/register cursor. Bind only after real fork, enforce global
freshness, preserve the masked parent insertion gap and fast child cases.
Monitoring needs the actual configured births/registrations. Whole-close and
infrastructure membership query the complete actual bindings, never a synthesized
old two-job alias. Preserve removed historical workers separately from captured
current registry membership and physical result availability.

Optional counter references point to one shared execution-heap registry, not a
copy per mux. Register/retire must be real source transitions. Pre-pool acquisition failure
uses its actual failure/outer-finalizer path, not a fabricated pool-close
certificate. Counter threads,
relay scopes and pre-publication rank-rule execution remain M3 gaps; M2 records
only the included pool/register/retire boundary, not whole-diffusion completion.

Preserve existing theorem types, source projections and actual O traces across
every new writer. Stronger readiness/all-role/retirement statements are additions.
Any compatibility constructor must initialize an explicit source-valid plain
empty/zero profile and preserve definitional equality; verify consumers before
changing a record constructor.

The old-arity `MuxRuntime.muxState` selects an explicit bidirectional plain
profile for its listed protocol numbers. Source `WithInitiatorResponderMode`
supports that profile; it is not a claim that every mux has both directions.
The configured constructor supplies exact registered keys, and outbound
`noResponderMode` allocation must register initiator keys only. Tracer attachment
and negotiated data flow do not determine protocol direction support
(`ouroboros-network-framework/src/Ouroboros/Network/Mux.hs`:254–275,297–309 at
the target network revision).

Wanton allocation is a separate actual child-entry operation after the physical
fork, permitted before or after parent registry insertion. The source job starts
with `newWanton` (`network-mux/src/Network/Mux.hs`:527–528); JobPool's child starts
independently of the parent's registration (`JobPool.hs`:122–164). Cancellation
may arrive before entry. Neither sending nor clean completion may treat an absent
Wanton as ready, and unsupported direction keys must be refused at the fork.

**Open migration decision:** explicit child entry changes the full source state.
The old `initiator-publication-source-stutters` and
`initiator-clean-keeps-IG-source` fixture equalities span these new allocations;
their old-pin results cannot be carried over with the same endpoints. The staged
correction compares post-allocation states and adds real entry edges, preserving
the original event order and final receipt guarantees. That concrete statement
change awaits explicit approval; it is not an equality transport or an accepted
replacement theorem. The proposal and exact old/new types are recorded in
`/tmp/cm-migration-m1-20261106/fixture-specification-delta.md`.

M1's component does not implement the grant/credit ledger: its failure controls
establish unchanged held/sent accounting only. Actual pre-grant versus granted
charge tests belong to M4; record them as deferred rather than claiming a vacuous
refund result. The first batch does not establish full scheduled-source
correspondence merely by adding lane/readiness state.

## Acceptance and later gaps

M1–M2 acceptance must include multi-key batch global1/keyA1/keyB1, same-key SDU
deduplication, persistence across generations, wrong/duplicate release refusal,
held-positive readiness refusal, pre-grant versus granted failure, distinct
successful-drain/timeout paths, real2/3/4 infrastructure jobs and registration
gaps, one-shot retirement after pool close, and unchanged captured release/origin/
result/final-wait histories. Altered-state guard controls are not automatically
initialized reachability witnesses.

Reuse unchanged generic JobPool laws and opaque traces. Use typed variable-endpoint
lift/trace/frame/observation adapters, explicit successors and runtime indices.
Focused checks precede a single ready-batch strict maintained endpoint check;
no new axioms, holes, unsafe options or weaker old statements. M1–M2 remains open
until that acceptance passes; no module-wide source promotion follows merely
from checking the new component.

M3 handler rule/tracer/outer-worker contracts, M4 detailed tokens/policy/fairness,
M5 collector-owned DB waits, exact dependency/backend validation and M6 source
replays remain explicit gaps. Scheduling disablement does not remove held guards.
Cancelling a DB collector does not retract its queued writer job. No universal
quiescence, progress or current-source refinement is asserted here.

Detailed independent M0 source/acceptance/interface reports and49 reproducible
source anchors: `/tmp/cm-migration-m0-20261106/`. The source-contract report is
complete; kernel API declarations will be checked incrementally during M1–M2.
