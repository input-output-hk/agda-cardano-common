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
| Acquisition, release and peer-state behavior | [Outbound](../ConnectionManagement/Outbound.md), [inbound release](../ConnectionManagement/InboundRelease.md), [remote state](../ConnectionManagement/RemoteState.md), [pruning](../ConnectionManagement/Pruning.md) |
| Handler and IG behavior | [Handler lifecycle](../ConnectionManagement/HandlerLifecycle.md), [handler outcomes](../ConnectionManagement/HandlerOutcomes.md), [IG registration](../ConnectionManagement/IGRegistration.md) |
| Implementation experiments and reproduction | [Source replays](../ConnectionManagement/SourceReplay/README.md), including the [actual Server admission-worker replay](../ConnectionManagement/SourceReplay/README.md#actual-server-admission-worker-lifetime-replay) |
| Model semantics and module navigation | [CSP interpretation](../ConnectionManagement/CSP/README.md), [module overview](../ConnectionManagement/README.md) |

ConnectionManagement uses network revision
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d` and consensus revision
`585a86117618ff86d7d5b541f9d23b03356d4c3a`. The
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
