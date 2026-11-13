# G0–G5 gate audit

13 November 2026 (G1 implementation follow-up). Documentation audit of [DESIGN §§1, 9–11](DESIGN.md),
[project state](../PROJECT_STATE.md), the area indexes and evidence below.
**All six gates are partly met; none is closed.** A gate requires every acceptance
item, not merely a strong result in one component.

The source baseline is network `2f1c154f248659b89523d5679ca532f442e7ed2a`,
pinned by consensus `2e44d98a843168ba3b189e305820b79943ac7d1e`.
[SourceLedger](SourceLedger.md) records the promotion and unchanged CM/IG/Server/
JobPool files. Earlier results retain their original `96ee6e0…` / `585a861…`
pins. The [15 October progress review](../review/connection-management-progress-review.md)
is historical: its missing OG, IG and supervision coverage has since advanced.
Likewise, early “open” entries in [Supervision](Supervision.md) must be read with
increments 68–80: SI5a/b are proved for the one-listener scope, and CM-I4c is
complete for the explicit `O.initial` profile. Neither closes these project gates.

“Proved” below means a model theorem with its stated premises. A finite witness
proves an enabled path exists; a mutated fixture tests a branch; a bounded search
covers only its bounds; a source replay executes selected pinned implementation
operations. These are separate evidence classes. The original gate snapshot ran no Agda checks,
source replays or git commands. The 12 November G1 inventory added seven fixture checks and a dependency audit;
[13 November increment 80](Supervision.md#eightieth-increment-g1-primitive-runtime-closure)
adds five primitive corrections and records fresh checks and capped regressions.
Other check/replay results retain their historical scope. Transient logs are identified in the linked records.

## G0 — domain, scenario and source ledger: partly met

Acceptance: identity distinctions, profile assumptions and first-path branch
coverage reviewed.

| Evidence item | Status | Evidence and exact gap |
| --- | --- | --- |
| Identity distinctions | **met** | [Domain](Domain.agda) indexes identities by kind and separates full connection keys, addresses/ports and local-key alternatives. [DESIGN §§2–3](DESIGN.md) and [README](README.md) distinguish entry, worker, socket, mux, promise, handle and protocol-run lifetimes. This is a model representation decision, not source conformance. |
| Profile assumptions reviewed | **partly met** | [DESIGN §2](DESIGN.md), [MigrationProfile](MigrationProfile.md) and [Outbound profile differences](Outbound.md#profile-differences-from-pinned-production) state the one-listener, ordinary-peer, untimed and IO/policy contracts. Missing: one reconciled executable LocalLifecycle setup matching the two-peer targets and configured protocol bundles, a concrete source PRNG seed/selection contract, and completed per-protocol wait/control/registry/cleanup contracts. The one-peer reduced-bundle witnesses do not discharge these choices. |
| First-path branch coverage reviewed | **partly met (matrix complete)** | [BranchMatrix](BranchMatrix.md) reconciles all 49 original ledger families and later branches in 99 rows: 66 implemented, 11 contracted, 14 excluded and 8 missing. It names actual initialized targets/bundles/selection inputs, corrects stale source ranges, separates accept-loop exits from the newly implemented handoff/worker exception edges, and lists the incomplete protocol/registry/resource contracts. The review artifact closes plan step 1; the 8 missing rows and incomplete source contracts still need implementation, reviewed contracts or justified exclusions. The executable profile also remains unresolved, so G0/G2 stay partly met. Plan step 2 now supplies the [primitive matrix](PrimitiveMatrix.md); its five primitive runtime findings are implemented, with capped regression acceptance pending. |

## G1 — state and primitive semantics: partly met

Acceptance: map take/restore, STM retry/rollback, fork, promise, queue and
cancellation examples.

| Evidence item | Status | Evidence and exact gap |
| --- | --- | --- |
| Map take/restore | **met** | [PrimitiveMatrix P01–P02](PrimitiveMatrix.md#shared-storage-concurrency-and-synchronization): [PrimitiveMap](Negative/PrimitiveMap.agda) adds enabled take/put/restore and empty-cell, foreign-owner and full-cell refusals. [HeapRollback](Negative/HeapRollback.agda) distinguishes saved-map restoration from committed heap rollback. [PrimitiveIncludeRestoration](Negative/PrimitiveIncludeRestoration.agda) now exercises X01: actual captured-body fault, saved-map-only restoration, retained heap/promise/child and separate close/result. |
| STM retry/rollback | **met** | Matrix P03–P04; [Scenarios/IGBatch](Scenarios/IGBatch.agda) `burst-fits`, `burst-retries-as-a-whole`, `split-prefix-would-fit`, ordered alternative/timeout controls; [Negative/Outbound](Negative/Outbound.agda) `full-queue-refuses-entire-commit`. The dependency contracts now cite the resolved STM implementations, not only API expectations. |
| Fork | **met for selected success/registration/failure contract** | Matrix P05; [ConcurrentPool](Negative/ConcurrentPool.agda) `fast-second-child-returns`, `fast-child-dereg-retries`, and masked parent insertion controls. J07 now has separate pre-birth failure, accepted-socket reservation, close and propagation controls in [PrimitiveAdmissionFork](Negative/PrimitiveAdmissionFork.agda). |
| Promise | **met** | Matrix P06–P07: [CM Types at the pin](PrimitiveMatrix.md#resolved-dependency-evidence), ordinary first write/duplicate exception, retained blocking read; [Scenarios/Handshake](Scenarios/Handshake.agda) `early-publication-is-readable`, `promise-survives-read`, `empty-promise-waits`, `duplicate-publication-throws`. `forcePromise` is unused by the selected model/handlers. Historical forcing probes retain their IO/IOSim limitations. |
| Queue and result synchronization | **met** | Matrix P08–P11: bounded IG bursts/flush versus source-unbounded completion/command queues; [PrimitiveResults](Negative/PrimitiveResults.agda) adds ordered first-result, empty/all-returned/error and pending-result controls. No queue/result observation implies physical termination. |
| Cancellation, mask/delivery, cancel/wait/waitCatch | **met for selected contracts; regression acceptance pending** | Matrix P12–P15, C01–C18, H01–H02, S01–S14, U01–U06, K01–K07, I01–I10 and J01–J07 enumerates selected sites with named enabled/refusal controls, explicitly labelling permission equations and supplied blocking observations. IO/IOSim catch/mask/throwTo and waitCatch differences are source-backed. Configured startup delivery **S10/F2**, include-body restoration **X01/F1** and raw admission fork failure **J07/F5** are now implemented with paired controls; see [increment 80](Supervision.md#eightieth-increment-g1-primitive-runtime-closure). |
| Timeout winners and modeled delays | **met for supplied observations; regression acceptance pending** | Matrix T01–T10 separates ordered idle/IG STM winners, exception-based PSA/Cold/drain timeouts, grant timer cancellation, TIME_WAIT and failure sleep. [PrimitiveTimers](Negative/PrimitiveTimers.agda) adds winner/readiness/duplicate-expiry and wrong-wait controls. [PrimitiveHandshakeContinuation](Negative/PrimitiveHandshakeContinuation.agda) covers distinct protocol-limit/bearer-timeout/query-delay continuations **T09/F4**; [PrimitiveGrantRefresh](Negative/PrimitiveGrantRefresh.agda) covers expiry/rearm **T10/F3** and grant/cancel controls. Untimed elapsed/expiry observations are not deadline guarantees. |
| Resolved dependency and runtime distinction audit | **met for the recorded Linux replay plan** | [PrimitiveMatrix dependency evidence](PrimitiveMatrix.md#resolved-dependency-evidence): GHC 9.6.7, base 4.18.3.0, stm 2.5.1.0, async 2.2.6, io-classes/io-sim 1.8.0.1, with plan SHA256, installed units, archive hashes and pinned helper sources. No new Haskell replay or universal IO/IOSim equivalence was established. |

**Plan step 2 runtime coverage is now 90 met / 0 missing** (original inventory
40/50; 12 November fixture checkpoint 85/5). All five findings are fixed rather
than excluded, with source-backed masking and explicit timer/blocking inputs.
**G1 remains partly met pending capped regression acceptance**: the affected
SourceKeys/OwnedFrames/OwnedCallers and heavy initialized concrete endpoints must
pass the [increment 80 check list](Supervision.md#eightieth-increment-g1-primitive-runtime-closure).
Existing theorem statements are unchanged. Focused passing examples do not replace
those checks, and this does not close G0/G2–G5 or assert Haskell refinement.

## G2 — first combined lifecycle: partly met

Acceptance: Server admission, OG jobs, IG handling, handler/protocol lifecycle
and clean release all run from initial state. The six first witnesses are
additional explicit obligations, assessed separately below.

| Evidence item | Status | Evidence and exact gap |
| --- | --- | --- |
| Server admission from initialization | **met** | [ServerAdmissionPrefix](Negative/ServerAdmissionPrefix.agda) and [ServerPeers](Negative/ServerPeers.agda) provide initialized handoffs, admission and selected failure exits. This starts at declared post-setup infrastructure, not a proof of whole-node boot. |
| OG jobs from initialization | **met** | [GovernorLifecycle](CSP/GovernorLifecycle.agda), `path`, executes establish/activate/deactivate/close. [ServerPeers.Protocols](Negative/ServerPeers.agda) connects jobs and physical initiators on shared state. The ordinary-peer restrictions remain explicit. |
| IG handling from initialization | **met** | [RegistryProducer](CSP/RegistryProducer.agda) composes admission, startup, CM promotion and failure-event consumption/removal. [ServerPeers](Negative/ServerPeers.agda) adds initialized registration and nonempty exit. These are finite witnesses, not delivery guarantees. |
| Handler/protocol lifecycle | **partly met** | [Supervision increments 23–31](Supervision.md#twenty-third-increment-peer-initiator-starts-and-physical-results) cover actual initiator starts, results, restart and shutdown races. [LiveTrackerInitialized](Properties/LiveTrackerInitialized.agda), `Frontend.from-initial`, proves `FullValidity` for every finite run from successful `initialize (O.initial c₀) g`. Missing: the complete selected protocol contracts and ordinary clean lifecycle witnesses for the configured bundles; validity does not establish execution coverage or eventual completion. |
| Clean release in the combined initialized profile | **partly met** | [GovernorLifecycle](CSP/GovernorLifecycle.agda) closes the outbound peer role; [Negative/Subsystem](Negative/Subsystem.agda), `final-inbound-retained` and `final-socket-retained`, explicitly retain the duplex inbound bearer. That can be correct reuse behavior. [ServerPeersClose](Properties/ServerPeersClose.agda) proves success histories; `ServerPeers.Protocols.CloseOriginChecks` includes initialized clean wait/release/Cold paths. Missing: the remaining clean inbound/outbound paths below with exact role-release, protocol, socket and physical-result endpoints, without injected midpoint states. Exceptional Server-return traces are not clean connection lifecycles. |

| First witness required by DESIGN §9 | Status | Concrete evidence and exact gap |
| --- | --- | --- |
| Inbound clean lifecycle | **partly met** | [RegistryProducer](CSP/RegistryProducer.agda) reaches registered removal via synchronous failure; [HandlerOutcomes](CSP/HandlerOutcomes.agda) supplies finite normal-exit paths with pool/buffer completion inputs. Missing: one initialized supervised admission → registration → normal protocol/mux exit → clean release/cleanup/result path, with those contracts named and endpoint resources checked. |
| Outbound clean lifecycle | **partly met** | [GovernorLifecycle](CSP/GovernorLifecycle.agda) is the 146-action logical lifecycle, with empty warm/established bundles and one hot protocol ([scope](Outbound.md#checked-witnesses-and-their-limits)). Missing: the configured, physically coupled clean path through release and results; preserve any legitimately retained inbound bearer rather than requiring every role-release to close it. |
| Duplex reuse | **met** | [ServerPeers.Protocols](Negative/ServerPeers.agda), `initialized-to-start`, includes actual inbound admission/publication/registration and startup, then outbound `Acquire.select (just (ident 0))` and return on the existing bearer. The header comments specify that only CM-free metadata is reused. This is an initialized finite model witness under `canInitiate`, not exhaustive reuse-branch or source replay coverage. |
| Handshake failure and socket cleanup | **partly met** | [Scenarios/Handshake](Scenarios/Handshake.agda) and [Scenarios/Cleanup](Scenarios/Cleanup.agda) compose negotiation failure with close/TIME_WAIT using abstract publication/exit boundaries; [HandlerSupervision](Negative/HandlerSupervision.agda) instead covers actual pre-handshake cancellation. [PublicationServer.hs](SourceReplay/PublicationServer.hs) has an actual early-handshake-error/finished-worker control ([record](SourceReplay/README.md#actual-server-admission-worker-lifetime-replay)). Missing: one current supervised initialized negotiation-failure witness joining the consumer, physical cleanup, admission result and socket outcome, rather than combining these separate kinds of evidence. |
| Successful hot demotion | **met** | [GovernorLifecycle](CSP/GovernorLifecycle.agda), `path`, includes clean hot-result publication and successful deactivation. [ServerPeersDeactivation](Properties/ServerPeersDeactivation.agda), `origin-success`, distinguishes already-Warm entry from an actual clean hot wait. This meets finite-path evidence for the reduced profile; it proves no universal demotion progress. |
| Timeout-driven cooling with delayed cleanup | **partly met** | [Negative/OutboundGovernor](Negative/OutboundGovernor.agda) checks timeout/cooling branches locally; `ServerPeers.Protocols.CloseOriginChecks.Proofs.initialized-timeout` ([fixture](Negative/ServerPeers.agda), [scope](Supervision.md#forty-third-increment-initialized-close-and-release-success-histories)) reaches the timeout route with an independent CM release caller. [ServerPeersOrigins](Negative/ServerPeersOrigins.agda) and [ServerPeersReleaseTimeWait](Negative/ServerPeersReleaseTimeWait.agda) provide initialized release/handler TIME_WAIT histories. Missing: one initialized PSA operation-timeout → Cooling → delayed physical cleanup → outbound-demoted observation → Cold path with the relevant job/monitor interleaving. Handler TIME_WAIT and governor demotion timeout are different boundaries. |

## G3 — concurrency: partly met

Acceptance: two peers, duplex reuse, delayed cleanup, same-key overlap and
job/monitor interleavings.

| Evidence item | Status | Evidence and exact gap |
| --- | --- | --- |
| Two peers | **partly met** | [ServerPeers.Interleaving](Negative/ServerPeers.agda) combines two admission handoffs, a held map and outbound caller cleanup; [Negative/Outbound](Negative/Outbound.agda) also has a conditional two-entry pruning fixture. Missing: an initialized two-ordinary-peer lifecycle with both peers executing, not just a second pending handoff or injected competitor. |
| Duplex reuse | **met** | The initialized `ServerPeers.Protocols.initialized-to-start` witness described under G2 exercises shared-bearer reuse. |
| Delayed cleanup | **met** | [ServerPeersOrigins](Negative/ServerPeersOrigins.agda) retains actual birth/resources through elapsed/interrupted TIME_WAIT and final CM waits; [release-caller delivery](Negative/ServerPeersReleaseTimeWait.agda) enters that delay through a real receipt. These are finite initialized schedules, not a deadline theorem. |
| Same-key overlap | **partly met** | [StaleHandshake](Negative/StaleHandshake.agda), [CleanupAtomicity](Negative/CleanupAtomicity.agda) and [IGRuntime](CSP/IGRuntime.agda) test captured identities, replacement and overlapping mux effects. Missing: an initialized witness of the DESIGN §2 requirement—three overlapping incarnations of one key while another key is present—with real allocation, replacement and delayed cleanup. Local replacement fixtures do not establish that history. |
| Job/monitor interleavings | **met** | [Negative/Subsystem](Negative/Subsystem.agda) checks child-before-registration; [ServerPeers](Negative/ServerPeers.agda) includes initialized restart/publication/cancellation races. [ServerPeersMonitorJoins](Properties/ServerPeersMonitorJoins.agda) proves ordered snapshot/join histories. Coverage is selected interleavings, not exhaustive schedule exploration. |

## G4 — semantic bridge: partly met

Acceptance: machine/process transition and trace correspondence, monitors and
negative controls.

| Evidence item | Status | Evidence and exact gap |
| --- | --- | --- |
| Machine/process transition correspondence | **partly met** | [Correspondence](CSP/Correspondence.agda), [Outbound](CSP/Outbound.agda) and [Subsystem](CSP/Subsystem.agda) prove `step-intro`/`step-inv` for their renderings of the same dispatcher. Missing: equivalent coverage, or a documented sufficient projection, for the expanded `ServerPeers.Protocols`/outer supervised runtime and its physical events. These results do not cover a separately composed parallel architecture or Haskell. |
| Finite run/trace correspondence | **partly met** | Those modules prove `exec-intro`/`exec-inv`, `trace-intro`/`trace-inv` and refused extensions; [Hiding](CSP/Hiding.agda) relates projected traces for the earlier machine. Missing: the expanded-runtime lift and a reviewed observation contract where required API outcomes are retained. [CSP README](CSP/README.md#observation-policy) records result-omitting labels; no hidden divergence or failures-divergences refinement follows. |
| Monitors | **partly met** | [OriginMonitorInvariant](Properties/OriginMonitorInvariant.agda) and [OriginMonitorWitness](CSP/OriginMonitorWitness.agda) supply selected origin diagnostics; [Scope](CSP/Scope.agda) explicitly disclaims completeness. [HandlerValidity](HandlerValidity.md) explains why legacy tracking is empty in the supervised stack and supplies the replacement live-tracker theorem. Missing: current-runtime monitor/frontier coverage distinguishing malformed input, incomplete modeling, ordinary blocking and explorer cutoff; legacy diagnostic absence cannot certify completeness. |
| Negative controls | **met** | [Negative/HeapRollback](Negative/HeapRollback.agda), [CleanupAtomicity](Negative/CleanupAtomicity.agda), [CounterValidity](Negative/CounterValidity.agda) and [LiveTrackerReferencesCounterexample](Properties/LiveTrackerReferencesCounterexample.agda) refute specific shortcuts or overbroad premises. [OwnedCallersFixture](Negative/OwnedCallersFixture.agda) and [ServerOwnedHandlersFixture](Negative/ServerOwnedHandlersFixture.agda) add variant refusals. These are intentional typechecking counterexamples, not automatically source defects. |

## G5 — exploration and replay: partly met

Acceptance: bounded enumeration/export checks, minimized candidates and
source-operation replay.

| Evidence item | Status | Evidence and exact gap |
| --- | --- | --- |
| Bounded enumeration and export checks | **not met** | [DESIGN §2](DESIGN.md) supplies trial allocation/depth limits; [Supervision’s remaining order](Supervision.md#remaining-dependency-order) still requires enabledness-complete enumeration, explicit cutoffs and export. Missing: an executable bounded action enumerator with completeness evidence for the declared carrier, distinct cutoff outcomes, and checked trace export/reimport. Raw Agda path proofs are not search runs. No exporter or FDR run is assumed. |
| Minimized candidates | **not met** | [SourceReplay](SourceReplay/README.md) contains focused fault scenarios, but no recorded model-search candidate minimizer. Missing: reproducible reduction preserving initialization, enabled replay and the monitored violation, with original/reduced traces and bounds. A short handwritten fixture is not evidence of minimization. |
| Source-operation replay | **met** | [Replay record](SourceReplay/README.md) and retained artifacts cover socket-open reservation, OG/PSA/CM failure/backoff (seeds 0, 1, 42), over-limit release, publication faults, Server worker lifetime, scheduled setup and DB waits. M6 records reruns at the promoted pins. Later [late-admission](SourceReplay/README.md#late-admission-after-the-cm-shutdown-10-november-2026) and [self-purge](SourceReplay/README.md#handler-self-purge-before-the-cm-returns-12-november-2026) records add scoped source observations. This meets selected replay evidence, not full source refinement or replay of every proposed race. |

The late-admission IOSimPOR run exhausted **628 schedules within its declared
20,000 schedule / 20 branching bounds**: it found a not-yet-started admission
worker after return, but no single trace with that worker's include after return.
The direct API replay separately executes a late include. Keep the combined
late-fork claim a candidate; the bounded negative is not unreachability.
The self-purge replay confirms a handler result unavailable after CM return,
using synthetic transport/handler inputs and a gated cleanup tracer; it does not
run full `Server.with`. The primitive cancel/join probe is not a CM replay.

Historical validation also differs by artifact. [Supervision increment 52](Supervision.md#fifty-second-increment-cache-aware-race-lifecycle-certificates)
records fresh interaction loads followed by a cached final CLI success.
[Round six](Supervision.md#round-six-full-initialized-cm-i4c-reference-validity)
records 18 fresh endpoint checks with each endpoint's own `Checking` line,
reusing dependency interfaces, exit 0 and no warnings. [Increment 78](Supervision.md#seventy-eighth-increment-admission-quiescence-step-2-design-exploration)
records fresh variant/fixture checks. M6's native results are actual replay runs,
not Agda checks. Earlier broad generated socket tests had a pruning coverage
warning; repeated deterministic tests and three fixed seeds add no exhaustive
schedule coverage. This audit does not upgrade any of these records.

## Second objective — a correct design

[DESIGN §1](DESIGN.md#1-objective-and-authority) gives this equal standing with
source-problem finding. There is already substantive proved design exploration:

- [OwnedCallers](Variants/OwnedCallers.agda) guards the existing rules to remove
  foreign CM begins. [Properties/OwnedCallers](Properties/OwnedCallers.agda),
  `Protocols.no-frames`, proves no acquire/release frames remain at finished
  relays for initialized variant runs. Restriction/erasure theorems relate these
  runs to the source model. The source-model theorem only limits residual
  frames to foreign callers; the stronger result depends on this policy.
- [ServerOwnedWorkers](Variants/ServerOwnedWorkers.agda) owns and joins admission
  workers without cancelling them and transports SI5, but is insufficient:
  [failed-handshake](Negative/ServerOwnedWorkersCounterexample.agda) and
  [self-purge](Negative/ServerOwnedWorkersSelfPurge.agda) witnesses leave a
  handler without its physical result. Cancel-and-join was rejected because
  pre-publication map restoration can lose a forked child's binding.
- [ServerOwnedHandlers](Variants/ServerOwnedHandlers.agda) adds a historical
  physical-birth registry and result sweep to worker ownership and owned
  callers. [Properties/ServerOwnedHandlers](Properties/ServerOwnedHandlers.agda)
  proves `registry-si5`, `no-late-admission`, `quiescence` and
  `quiescent-covered`: at finished relays, workers are joined and registered/
  physical handlers have results. This is an accepted model design proposal,
  not a change implemented in the pinned Haskell.

Remaining design questions: can the no-cancel worker joins and registry sweep
always finish, and under which scheduler, transport, protocol and tracer progress
assumptions? How should a real implementation register births, retain detached
handlers and prevent late callers across rollback/overwrite/pruning windows?
What is the required policy for foreign callers and preloaded continuations?
How far should guarantees extend beyond one listener and the selected outer
scopes? The current `FullValidity` theorem covers `initialize (O.initial c₀) g`;
the unrestricted initializer is refuted. Quiescence is safety at a reached
endpoint; finite progress examples do not prove eventual shutdown. A source fix
needs its own implementation/replay and correspondence evidence.

## Ordered gap-closing plan

Sizes are relative: S = focused audit/fixture, M = a component or composed path,
L = tooling or broad integration. Reuse existing proofs; a new general invariant
campaign is not a prerequisite for ordinary behavioral witnesses.

| Order | Size | Deliverable and acceptance |
| --- | --- | --- |
| 1 | S | **Done — [BranchMatrix](BranchMatrix.md), 12 November 2026.** All original ledger families and later branches classified, with executable fixture targets/bundles/selection policy, source ranges and evidence. Protocol contracts and handoff/worker errors remain explicit gaps. This completes the G0/G2 checklist review without changing gate criteria or closing the gates. |
| 2 | M | **Runtime work implemented; capped regression acceptance pending**, 13 November 2026. [PrimitiveMatrix](PrimitiveMatrix.md): 90 rows, original 40/50 → inventory checkpoint 85/5 → current 90/0 met/missing. F1–F5 now have source-backed rules and paired fixtures. [Increment 80](Supervision.md#eightieth-increment-g1-primitive-runtime-closure) records the checks and remaining capped endpoints. **G1 remains partly met until those checks pass.** |
| 3 | M | Add an initialized supervised inbound clean lifecycle: admission, IG registration, actual protocol/mux normal exit, role release, socket cleanup and physical result. State contracts and check exact endpoints without injected midpoint states. |
| 4 | M | Add the configured outbound clean lifecycle and supervised negotiation-failure/cleanup witness. Reuse the proved duplex prefix; distinguish outbound role release from retained inbound bearer ownership. Deliver two named initialized paths and premature-result controls. |
| 5 | M | Add one initialized operation-timeout/Cooling/delayed-cleanup/Cold history with actual job and monitor steps. Check that Cold and job return cannot precede their required observations; keep demotion timeout and TIME_WAIT separate. Reassess all six G2 witnesses. |
| 6 | M | Deliver a design-variant acceptance contract for worker joins and the historical handler registry, with explicit progress assumptions and a pinned implementation replay/prototype plan covering detached handlers. Retain the rejected variants and counterexamples; do not infer eventual shutdown from quiescence. |
| 7 | M | Add initialized two-peer and three-same-key-incarnation histories with another key present, preserving captured identities and delayed cleanup. Include branch/refusal controls and an allocation-bound budget. This supplies missing G3 evidence. |
| 8 | M | Extend or explicitly project the semantic bridge to the supervised/outer runtime; prove step/run/trace correspondence and review result-bearing observations. Update monitors/frontiers for current events and retain negative controls. This supplies missing G4 evidence without asserting hidden divergence freedom. |
| 9 | L | Implement enabledness-complete bounded enumeration and checked export/reimport over a declared finite carrier, with explicit allocation/depth cutoffs. First replay all ordinary initialized witnesses within bounds; then record targeted race searches with exact bounds and outcomes. |
| 10 | M | Add candidate minimization with replay/violation preservation, retain original and reduced traces, and replay selected reduced source operations at the pinned revisions with controls. Classify each result as model distortion, unconfirmed candidate or replay-confirmed source behavior; close G5 only when every item is evidenced. |
