Companion: [Verified properties summary](connection-management-verified-properties-summary.md).

# Identified Haskell and connection-management issues

Summary reconciled 17 November 2026 against model commit `687463c`, the pinned
source and the recorded replays through increment 100.
[Branch disparity review and validation](connection-management-architecture-review-2026-11.md#11-model-source-and-proof-disparities).

## Findings and evidence

| Issue | What was observed | Evidence |
| --- | --- | --- |
| **Socket-open failure leaves a reservation** | Established at `96ee6e`; **re-tested at `2f1c154` in M6**. Actual CM/IOSim replay shows `openToConnect` throwing while `ReservedOutbound` remains. Subsequent acquisitions get `ConnectionExists`; the integrated governor eventually forgets the peer while CM retains the reservation. | [Socket-open and governor replay](../ConnectionManagement/SourceReplay/README.md#socket-open-reservation-replay); [M6 revalidation](../ConnectionManagement/SourceReplay/README.md#m6-revalidation-at-network-2f1c154-9-november-2026) |
| **Over-limit release reports success without completing the state transition** | Established at `96ee6e`; **re-tested at `2f1c154` in M6**. When pruning selects another connection, the surviving released connection remains `OutboundDup Ticking` rather than becoming inbound-idle. Reproduced through actual CM APIs. | [Outbound-release replay](../ConnectionManagement/SourceReplay/README.md#verified-over-limit-outbound-release-replay); [M6 revalidation](../ConnectionManagement/SourceReplay/README.md#m6-revalidation-at-network-2f1c154-9-november-2026) |
| **Unpublished handshake result can strand a caller** | Established at `96ee6e`; **CM and Server probes re-tested at `2f1c154` in M6**, using plain mux. Injected failures after negotiation but before promise publication leave a caller waiting after handler completion and map cleanup. Actual Server replay observes admission workers blocked after `Server.with` returns. Deployment relevance remains conditional on the injected faults. | [CM caller and cleanup replay](../ConnectionManagement/SourceReplay/README.md#actual-cm-caller-and-cleanup-replay-for-cm-pub1); [Server admission-worker replay](../ConnectionManagement/SourceReplay/README.md#actual-server-admission-worker-lifetime-replay); [M6 revalidation](../ConnectionManagement/SourceReplay/README.md#m6-revalidation-at-network-2f1c154-9-november-2026) |
| **Inbound-governor wedge from overlapping connection incarnations** | Established by the separate study at `4b3ab76`; **not re-tested at `2f1c154`**. A stale mux callback can identify a newer, live mux and make IG wait for it. Evidence combines field observations, source analysis and machine-checked model witnesses, rather than an M6 native replay. | [GovernorWedge study and limits](../GovernorWedge/README.md#1-what-this-is) |
| **Self-purged handler outlives CM shutdown** | **Replay-confirmed at `2f1c154`**. Increments 78/99 observe a pending physical result after direct CM return while the masked cleanup-counter tracer is paused. The increment 100 pristine full-Server control observes that Server did not wait while the same gate was closed. It opens the gate before sampling the result after return. Both findings are scoped to their supplied inputs. | [Direct-CM replay](../ConnectionManagement/SourceReplay/README.md#handler-self-purge-before-the-cm-returns-12-november-2026); [reduced replay](../ConnectionManagement/SourceReplay/README.md#reduced-cleanup-candidates-increment-99); [full-Server control](../ConnectionManagement/SourceReplay/README.md#controls-and-physical-observations) |
| **Late admission after CM shutdown** | **Separate halves replayed at `2f1c154`; combined Server race unconfirmed**, increments 73 and 99. POR finds Server/CM return with an admission worker not yet started; direct API tests show post-finally include can fork a handler. No single source trace combines that Server worker, return and its late include. | [Late-admission replay and bounds](../ConnectionManagement/SourceReplay/README.md#late-admission-after-the-cm-shutdown-10-november-2026); [increment 73](../ConnectionManagement/Supervision.md#seventy-third-increment-late-admission-after-the-cm-shutdown); [increment 99 classification](../ConnectionManagement/SourceReplay/README.md#reduced-cleanup-candidates-increment-99) |
| **Foreign CM callers survive shutdown** | **Model artefact, not a source defect**. Increments 75–77 identify residual frames as foreign callers and exclude them in the owned-callers variant. Increment 99's `2f1c154` replay deliberately forks an external caller; its survival does not show a library-owned-worker defect. | [Increments 75–77](../ConnectionManagement/Supervision.md#seventy-fifth-increment-outbound-caller-frames-at-shutdown-residue-c2); [source-operation classification](../ConnectionManagement/SourceReplay/README.md#reduced-cleanup-candidates-increment-99) |

## Source revisions and limits

The historical CM baseline is network
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`; GovernorWedge uses
`4b3ab7664f609a1aee0f0c24dcfcfd0ab899fc42`. The promoted network authority is
`2f1c154f248659b89523d5679ca532f442e7ed2a`, dependency of consensus
`2e44d98a843168ba3b189e305820b79943ac7d1e`. The
[migration plan (M6)](../ConnectionManagement/BASELINE_MIGRATION_PLAN.md) and
[source ledger](../ConnectionManagement/SourceLedger.md) distinguish historical
results from revalidation. CM Core, IG, Server and JobPool are byte-identical
between the two CM pins; that comparison alone is not a replay.

These are fixed revisions, not today's upstream status. Finite fault-injection
and synthetic-transport results do not establish permanent leaks, production
deadlock, deployment frequency or universal shutdown. The Server report records
instrumentation and garbage-collection limits. Bounded POR negatives do not
prove unreachability, and model witnesses are not full Haskell trace refinement.

## Recommended design

Follow the [design contract](../ConnectionManagement/DesignContract.md): owned CM
callers, retained Server admission workers joined without cancellation before CM
shutdown, and a historical handler registry independent of the live map, swept
for cancellation/results before closure. The
[quiescent-shutdown prototype](../ConnectionManagement/SourceReplay/QuiescentShutdownPrototype.patch)
adds implementation evidence at `2f1c154` ([increment 100](../ConnectionManagement/Supervision.md#one-hundredth-increment-quiescent-shutdown-haskell-prototype)).
The prototype's join and sweep order differ from the Agda variant. The patch
relies on caller ownership, and its escaped-API control still admits a late
include. Progress cases remain open for blocked cleanup, missing promise
publication and late producers filling the stopped IG's bounded queue.
[Model and prototype ordering](../ConnectionManagement/DesignContract.md#model-and-prototype-ordering).

## Distinguish source findings from model corrections

Source findings are the reservation, over-limit release, publication/blocked
Server worker and historical IG wedge above, now supplemented by replay-confirmed
self-purge. Late admission remains a source candidate with separately replayed
halves. Recent work therefore does identify additional source shutdown behavior;
it cannot be summarised as finding no other Haskell defect.

Model corrections include A1–A9 and SI4-F1 source-mapping limitations
([review summary](connection-management-source-spec-review-summary-2026-10-27.md)),
foreign-caller ownership (increments 75–77), the five
[primitive-rule corrections, increment 80](../ConnectionManagement/Supervision.md#eightieth-increment-g1-primitive-runtime-closure),
[inbound physical release receipt, increment 82](../ConnectionManagement/Supervision.md#eighty-second-increment-inbound-physical-release-receipt-and-clean-lifecycle),
and [StartOnDemandAny support, increment 92](../ConnectionManagement/Supervision.md#ninety-second-increment-startondemandany-and-the-full-configured-outbound-witness).
Correcting these rules or extending provenance proofs is not itself a Haskell
bug fix; source findings, model fidelity and proposed design changes remain
separate claims.
