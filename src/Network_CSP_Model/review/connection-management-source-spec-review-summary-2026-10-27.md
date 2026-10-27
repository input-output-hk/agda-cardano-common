# Connection management source and specification review summary

Date: 27 October 2026.

Implementation status is tracked separately in the
[correction plan](connection-management-correction-plan-2026-10-27.md); the
assessment below records the review baseline before those corrections.

The [original review](connection-management-source-spec-review-2026-10-27.md)
is mostly supported by the current model and pinned source. **A1 is a confirmed
source-fidelity bug and should be corrected before extending proofs affected by
mux-monitor ordering.** Several proposed fixes need qualification. Existing
Agda invariants remain statements about the model; they do not establish that
its traces faithfully represent the source.

The assessment used Git objects at network pin
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`, avoiding the stale checkout.
Comparison with `main` concerns the fixed snapshot
`4646039f05eb809bd5252af17121644ec1dc0c2c`, not the current remote branch.

## Model findings

| Finding | Assessment and required qualification |
| --- | --- |
| A1: initiator failure ordering | Confirmed. `Subsystem.observeInitiatorFailure` bypasses pending responder completions and tracked-handler phase gating. The source mux consumes one FIFO of job results. |
| A2: unconditional IG tracer | Confirmed. Outbound requires responder mode and duplex flow; inbound attaches its IG tracer regardless of flow. Represent tracer attachment explicitly: setting counters to `nothing` alone does not suppress the unconditional `muxStopped` event. |
| A3: missing-descriptor precedence | Confirmed. Expired idle state can cause source retry before descriptor evaluation. The source's initial `AwakeRemote` queue write can also retry on a full queue before forcing that descriptor. |
| A4: target sanity and updates | Confirmed profile differences. The model omits source target bounds and rejects invalid input updates rather than storing them for the governor to ignore. |
| A5: failure-clearing delay | Confirmed: model/replay uses 60; pinned production policy uses 120. Document the configuration provenance or align the default. `maxRetries = 5` matches production; its cautious model-setting disclaimer is not itself false. |
| A6: ShutdownNode | A production-policy and supervision abstraction, already partly documented. The model permits broader policy choices and lacks full node shutdown. Immediate termination after delivery would erase the source's delivery and cancellation window. |
| A7: reuse selection | Correct abstraction limitation. Retrying unchanged STM inputs preserves the source selection; another thread changing the generator can change it. Qualify the existing PRNG abstraction rather than treating nondeterminism alone as a new algorithmic defect. |
| A8: stale descriptions | Mostly confirmed: API names and the handshake-consumption comment need updating. However, `validSelection` checks admissibility, not concrete ordered/random sampling. HandlerOrigin documentation must not imply that outbound origin preservation has been proved. |
| A9: source citations | Corrections are supported. Several ranges omit relevant context or extend beyond the file; these are documentation fixes rather than independent executable-model defects. |

A10's blanket consistency statement is too broad. In particular, its mux-priority
claim must exclude A1's combined-dispatcher bypass. Branch checks, patch
applicability and model proofs do not establish source refinement.

## Correction priority

1. **Correct A1 with a shared, direction-tagged completion FIFO and the appropriate
   monitor phase gate.** An empty-responder-queue guard alone does not represent a
   queued initiator failure or prevent commands/on-demand starts overtaking it.
   Check FIFO delivery of an earlier responder clean result, failure ordering,
   command/start priority and tracked pool-closing behavior.
2. Fix A8/A9 documentation and citation drift without expanding theorem claims.
3. Correct or explicitly document A2–A7, preserving inbound/outbound tracer
   asymmetry, source retry precedence, policy provenance and supervision limits.
4. Resume affected structural-proof extensions after the semantic correction and
   relevant regressions. Keep historical reference coherence separate from live
   source ownership, object lifetime and phase/cleanup validity.

## Specification errata and source drift

Part B's principal API, blocking, initiator-mode and transition corrections are
supported by the pinned source and TeX. B12 remains conditional: exact lookup
explains why an initial unknown-local reservation is missed, but does not settle
all `Overwritten` behavior after local-address promotion and possible socket
interleavings. The assessment did not independently audit every table cell, PDF
page number or the latest-published-PDF claim. Upstream errata should retain
these limits.

Part C's stale-`MuxFinished` handling, provenance/flow filtering and assertion
trace changes are confirmed for snapshot `4646039f`. `docs/network-spec` has no
diff between that snapshot and the pin; the CM chapter's last change there is
`c9e803664`, dated 16 June 2025. These drift findings do not authorize changing the
model's source pin.

## Validation and scope

- A scratch Agda probe passed with Agda 2.8.0 and `+RTS -M2G -RTS`. Injected
  fixtures show that pending responder completions do not prevent the direct
  failure transition, and that `poolClosing` gates `IG.monitorCompletion` while
  allowing that direct transition. The probe also checks acceptance of targets
  exceeding source bounds. These are enabled model-step controls, not new
  source-reachable witnesses.
- `SocketOpenFailure.patch`, `GovernorCMReplay.patch` and
  `OverLimitReleaseReplay.patch` each passed `git apply --check` against isolated
  pinned file exports, excluding `*.cabal`. Combined application and replay
  execution were not tested by this assessment.
- No maintained Agda module or executable transition was changed during the
  review. No broad regression build or new source-refinement proof was performed.

The scratch check was run from the library root:

```sh
agda -i /tmp/cm-review-20261027 /tmp/cm-review-20261027/ReviewProbe.agda +RTS -M2G -RTS
```

The probe is a temporary verification artifact; the durable correction criteria
are recorded above. The original review remains unchanged.
