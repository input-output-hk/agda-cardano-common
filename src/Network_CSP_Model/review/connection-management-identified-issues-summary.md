# Identified Haskell and connection-management issues

Summary prepared 4 November 2026 from the repository's recorded source audits
and replay results. No source replay or upstream-status check was rerun for this
summary.

## Findings and evidence

| Issue | What was observed | Evidence |
| --- | --- | --- |
| **Socket-open failure leaves a reservation** | Actual CM/IOSim replay shows `openToConnect` throwing while `ReservedOutbound` remains. Subsequent acquisitions get `ConnectionExists`; the integrated governor eventually forgets the peer while CM retains the reservation. | [Socket-open and governor replay](../ConnectionManagement/SourceReplay/README.md#socket-open-reservation-replay) |
| **Over-limit release reports success without completing the state transition** | When pruning selects another connection, the surviving released connection remains `OutboundDup Ticking` rather than becoming inbound-idle. Reproduced through actual CM APIs. | [Outbound-release replay](../ConnectionManagement/SourceReplay/README.md#verified-over-limit-outbound-release-replay) |
| **Unpublished handshake result can strand a caller** | Injected failures after successful negotiation but before promise publication leave the caller waiting, although the handler has finished and CM cleanup emptied the map. Actual Server replay also observes admission workers still blocked after `Server.with` returns. Deployment relevance remains conditional on the injected tracer/payload faults occurring. | [CM caller and cleanup replay](../ConnectionManagement/SourceReplay/README.md#actual-cm-caller-and-cleanup-replay-for-cm-pub1); [Server admission-worker replay](../ConnectionManagement/SourceReplay/README.md#actual-server-admission-worker-lifetime-replay) |
| **Inbound-governor wedge from overlapping connection incarnations** | A stale mux callback can identify a newer, live mux and make IG wait for it. The separate GovernorWedge study connects this mechanism to field observations and machine-checked witnesses. | [GovernorWedge study](../GovernorWedge/README.md#1-what-this-is) |

## Source revisions and limits

The first three findings concern network revision
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`. GovernorWedge studies the distinct
revision `4b3ab7664f609a1aee0f0c24dcfcfd0ab899fc42`. These historical findings
do not establish that today's upstream still has every issue; the supporting
reports describe their tested configurations and fix analyses.

The promise/publication and Server observations are finite fault-injection
results. They do not establish a universal or permanent thread leak, a production
deadlock, or deployment exposure to the injected faults. The Server report also
records instrumentation and garbage-collection limitations.

## Distinguish source findings from model corrections

A1–A9 and SI4-F1 largely concern errors or limitations in the Agda model and its
source mapping. Correcting them should not be counted as fixing Haskell bugs.
See the [source/specification review summary](connection-management-source-spec-review-summary-2026-10-27.md)
and [supervision development record](../ConnectionManagement/Supervision.md).

The recent provenance proofs strengthen the model's evidence. They have not
themselves identified another Haskell defect.
