# Documentation index

Start with the [library overview and setup](../README.md). For the active goal,
acceptance evidence and next task, use [PROJECT_STATE.md](../PROJECT_STATE.md).
Topic pages below carry the maintained explanations; dated audits preserve the
investigation history.

## Connection management

| Topic | Maintained page and evidence |
| --- | --- |
| Combined CM/IG/OG/Server scope and completion gates | [Design](../ConnectionManagement/DESIGN.md); [remaining work and parallel execution](../ConnectionManagement/Supervision.md#remaining-work-and-parallel-execution) |
| Source authority and operation mapping | [Source ledger](../ConnectionManagement/SourceLedger.md); its coverage snapshots are historical, not a complete current inventory |
| Cancellation, monitor histories and shutdown certificates | [Current supervision findings](../ConnectionManagement/Supervision.md#current-composed-lifecycle-certificates); [remaining obligations](../ConnectionManagement/Supervision.md#open-questions-and-reconciled-status) |
| Initialized handler resources and birth backing | [Collected inbound origins](../ConnectionManagement/Supervision.md#sixty-first-increment-collected-inbound-resource-origins); [profiled outbound origins](../ConnectionManagement/Supervision.md#sixty-second-increment-automatic-outbound-collected-resource-origins); [physical birth backing](../ConnectionManagement/Supervision.md#fifty-seventh-increment-initialized-physical-handler-birth-backing); [collected-worker backing](../ConnectionManagement/Supervision.md#fifty-eighth-increment-acknowledged-collected-handler-birth-backing) |
| Finished-target CM acknowledgement | [Increment 63](../ConnectionManagement/Supervision.md#sixty-third-increment-initialized-finished-target-acknowledgement): independently completed target, late-read skip and actual receipt-derived origins and retained resource packets |
| Outbound negotiated-mux CM receipt and wait | [Increment 64](../ConnectionManagement/Supervision.md#sixty-fourth-increment-outbound-negotiated-mux-receipt-and-final-wait): accepted actual outer closure and inactive-IG unwind through publication/final wait. [Pinned source evidence](../review/connection-management-si4-source-audit-2026-10-27.md#increment-64-outbound-mux-receipt-and-inactive-ig-6-november-2026) |
| Initialized TIME_WAIT receipt/finalizer routes | [Increment 65 contract](../ConnectionManagement/Supervision.md#sixty-fifth-increment-initialized-time_wait-receipt-and-finalizer-routes): accepted initialized elapsed/interrupted finally routes and CM waits; [pinned entry/finalizer audit](../review/connection-management-si4-source-audit-2026-10-27.md#increment-65-time_wait-entry-and-finalizer-audit-6-november-2026) |
| Independent outbound-release receipt/return | [Accepted increment 66](../ConnectionManagement/Supervision.md#sixty-sixth-increment-framed-mux-outbound-release-receipt-and-return), committed in `daf111d`: finite initialized live/available-result routes, actual source return and same-origin final wait; [generic receipt properties](../ConnectionManagement/Properties/ServerPeersReleaseReceipt.agda). |
| Source-baseline assessment | [Verified current-pair audit](../review/connection-management-source-baseline-audit-2026-11-06.md): exact source objects retrieved, changed lifecycle/readiness contracts identified; migrated and promoted on 9 November 2026 ([migration plan](../ConnectionManagement/BASELINE_MIGRATION_PLAN.md)). |
| Acquisition, release and peer-state behavior | [Outbound](../ConnectionManagement/Outbound.md), [inbound release](../ConnectionManagement/InboundRelease.md), [remote state](../ConnectionManagement/RemoteState.md), [pruning](../ConnectionManagement/Pruning.md) |
| Handler and IG behavior | [Handler lifecycle](../ConnectionManagement/HandlerLifecycle.md), [handler outcomes](../ConnectionManagement/HandlerOutcomes.md), [IG registration](../ConnectionManagement/IGRegistration.md) |
| Implementation experiments and reproduction | [Source replays](../ConnectionManagement/SourceReplay/README.md), including the [actual Server admission-worker replay](../ConnectionManagement/SourceReplay/README.md#actual-server-admission-worker-lifetime-replay) |
| Model semantics and module navigation | [CSP interpretation](../ConnectionManagement/CSP/README.md), [module overview](../ConnectionManagement/README.md) |

ConnectionManagement uses network revision
`2f1c154f248659b89523d5679ca532f442e7ed2a` and consensus revision
`2e44d98a843168ba3b189e305820b79943ac7d1e` (since 9 November 2026; earlier
results keep `96ee6e0…` / `585a861…`). The
[dated SI4 audit](../review/connection-management-si4-source-audit-2026-10-27.md)
records source obligations and subsequent model/replay followups. Model proofs,
source inspection and finite implementation replays supply different evidence;
none substitutes for the others.

## Network processes and liveness

| Topic | Reading entry point |
| --- | --- |
| Network assembly and mini-protocol coverage | [Module map](../Cardano_network/README.md), [protocol scope and claims](../Cardano_network/mini-protocols.md) |
| Medium refinement, equivalence and sanity probes | [Network verification](../Cardano_network/NetworkVerification/README.md) |
| Four-node liveness routes | [Liveness overview](../Cardano_network/FourNode/Liveness/README.md); separate [LTL assumptions/status](../Cardano_network/FourNode/Liveness/LTL/BLOCKLIVENESS_STATUS.md) and [CSP-refinement assumptions/status](../Cardano_network/FourNode/Liveness/CSP_Refinement/STABR_STATUS.md) |
| Parametric Leios systems and proof boundaries | [Leios overview](../Cardano_network/Parametric/Leios/README.md) |
| Send priority | [Priority model](../Cardano_network/Priority/README.md) |

Use each area's own baseline and theorem premises. In particular, local
postulate freedom, imported assumptions, no livelock and possible delivery
traces are distinct claims.

## Focused investigations and open questions

- [GovernorWedge](../GovernorWedge/README.md) has its own network pin,
  `4b3ab7664f609a1aee0f0c24dcfcfd0ab899fc42`, overlapping-incarnation model,
  atomic release and untimed timeout. Its
  [missing design artifacts](../GovernorWedge/README.md#design-artifact-provenance)
  are an open provenance gap; their paths have been retained.
- [Hot demotion](../HotDemotion/README.md) records its own source baseline,
  [assumptions](../HotDemotion/README.md#2-assumptions) and theorem scope.
- [Supervision open questions](../ConnectionManagement/Supervision.md#open-questions-and-reconciled-status)
  distinguish the confirmed finite certificates from handler provenance,
  admission quiescence and derived whole-supervision completion still required.

**Evidence labels:** a *confirmed finding* is supported under its cited
revision/profile; an *inference* adds an explicitly stated interpretation; an
*open question* names missing evidence and the check needed to settle it.
Dated “next” and “uncommitted” statements describe their checkpoints; use the
current topic overview and project state for continuation.

- [Prototype source-baseline audit, 6 November](../review/connection-management-source-baseline-audit-2026-11-06.md): verified current pin pair, changed lifecycle/readiness contracts and the decision to retain model pins pending migration.

- [Model and proof migration plan](../ConnectionManagement/BASELINE_MIGRATION_PLAN.md): dependency order, first readiness/pool batch, parallel roles and baseline-promotion gates.

- [M0 migration profile](../ConnectionManagement/MigrationProfile.md): exact batch units, source transition boundaries, lane/job identity and first-batch acceptance contract.
