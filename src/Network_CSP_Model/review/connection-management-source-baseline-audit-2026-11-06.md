# Prototype source-baseline audit — 6 November 2026

**Decision: retain the model's existing source pins.** The current prototype pair
is now available and reviewed at the boundaries below, but a pin-only update would
hide changed readiness, ownership and blocking contracts. Accepted model proofs
through `daf111d` remain evidence about their original definitions and profile.
This audit neither refutes those proofs nor establishes refinement to the new code.

## Verified authority

| Role | Immutable revision |
| --- | --- |
| Existing model consensus | `585a86117618ff86d7d5b541f9d23b03356d4c3a` |
| Existing model network | `96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d` |
| Observed prototype consensus | `2e44d98a843168ba3b189e305820b79943ac7d1e` |
| Its declared network dependency | `2f1c154f248659b89523d5679ca532f442e7ed2a` |

Live `ls-remote` observations at 16:39 UTC on 6 November identified those
consensus/network branch heads. The fetched consensus `cabal.project` selects
exactly that network revision. These are timestamped observations, not permanent
claims about moving branches. Local consensus `2416493bfdbe…` is an intermediate
1 November revision, 44 reachable commits beyond the old consensus pin.

The earlier local-only audit could not find the network object in 37 databases.
A sandbox fetch failed DNS; an authorized retry retrieved the exact revision into
an isolated temporary repository. That resolves source availability. Existing
checkouts, configuration, model pins and proof files were not changed.

The [evidence manifest](source-baseline-2026-11-06.json) retains revisions, remote
observations and source blob/hash inventories. Detailed commands, extracted source,
diffs and independent reports are under `/tmp/cm-baseline-wave-20261106/`.
Historical [source mappings](../ConnectionManagement/SourceLedger.md) retain their
original revision authority.

## M0 clarification: counter units

Subsequent exact source inspection clarified the earlier held-byte terminology:
`laneHeld` is a single mux-wide shared batch count, not a per-lane byte counter.
`esHeld` counts distinct per-key batch memberships; several SDUs for the same key
in one batch increment once. `esSent` measures bytes including headers. Preserve
these distinct units when implementing the readiness/accounting model.

## Confirmed findings

The selected network inventory covers 101 library, API, tracing, test and package
files: 51 unchanged, 40 changed and 10 added. This is selected coverage, not an
all-source semantic audit. CM Core/Types/State/ConnMap, IG framework and channel,
Server, JobPool and the framework mux wrapper are byte-identical. The handler's
classification/peer-node rethrow body and mux async catch body also match.
Changed callers and surrounding scopes prevent an unchanged-file claim from
establishing unchanged composed behavior.

| Changed boundary | Confirmed source contract | Consequence for the model |
| --- | --- | --- |
| Handler setup | `ConnectionHandler.hs` installs optional shared egress, dynamic rank/charge rules and counters; rank STM/tracing precedes promise publication inside the existing classifier. | Recheck setup allocation, blocking and exceptional paths. New rule/tracer work needs an explicit profile, rather than an assumed total diagnostic. |
| Mux completion/drain | `Network/Mux.hs` requires an empty send queue **and zero held batches** before normal completion; shutdown requires all lane queues empty **and zero shared mux-held batches**, retaining timeout 2. This also applies without scheduled egress. | `cleanCommit` and `drainEmpty` are abstract observations. Applying them to this source needs the stronger readiness mapping; detailed byte/stall claims need held/in-flight state. |
| Egress and ownership | Multiple lane muxers, grant/writability waits, masked write/accounting, waiter/timer cancellation and counter register/retire brackets surround the unchanged JobPool. | Recheck actual job sets, interruption windows and enclosing cleanup. Registry removal, held release, protocol completion and Async result remain distinct. |
| Diffusion lifetime | A counters loop races diffusion; its failure/tracer failure can end diffusion. Pool-relay infrastructure participates in async ownership/waiting. | Treat these as owned lifecycle participants, not inert telemetry. No all-worker shutdown result follows from existing certificates. |
| Outbound governor | Four supporting modules change tenure/public hot-upstream/local-root state and peer-share failure backoff; main Governor is unchanged. | Recheck new public observations and result races. The upstream peer-share fix is not a bug discovered by this audit. |
| Consensus integration | Fresh-byte/capacity feedback, tier RNG and live local-root membership feed scheduling/fetch policy. LeiosFetch replies and transaction encoding change. | Preserve codec/payload exclusions, but assess feedback and protocol-worker contracts separately. |
| Latest consensus delta | `2416493…` to `2e44d98…` replaces linked asynchronous durability completions with synchronous waits for EB-point/body/transaction writes. | Body return, cancellation, error and publication boundaries must account for DB completion waits. No new local mask establishes an unmasked invariant. |

These are source findings. They do not demonstrate a new implementation defect,
universal progress, a unique backend dependency solve or build compatibility.

## Migration gate and next action

**Inference:** completion/drain readiness and newly owned setup/wait operations are
the first supervision contracts to reconcile. Disabling scheduled egress alone
is insufficient because held-batch guards also affect the plain path.

Before changing pins:

1. Define the target profile and map held/in-flight readiness, lane/pool ownership,
   counter cleanup, pre-publication rule/tracer work and synchronous DB waits.
2. Justify unchanged abstractions explicitly; implement only demonstrated model
   gaps. Preserve theorem statements, controls and old-pin evidence.
3. For runtime edits, use focused component checks followed by the maintained
   strict initialized acceptance endpoint, one bounded checker and integrity audit.
4. Revalidate affected source replays/build scenarios against the exact new pair;
   keep unperformed backend/build/refinement obligations explicit.

No repin, proof implementation, Agda check, Haskell build or native replay was
performed for this audit. Current model G0–G5, CM-I4c, SI4/SI5 and quiescence
obligations remain open. Caller-specific TIME_WAIT expansion remains deferred
while this source-contract migration is scoped.
