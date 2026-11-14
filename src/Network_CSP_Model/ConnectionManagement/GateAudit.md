# G0–G5 gate audit

14 November 2026 (increment 92 start-mode and configured outbound acceptance). Documentation audit of [DESIGN §§1, 9–11](DESIGN.md),
[project state](../PROJECT_STATE.md), the area indexes and evidence below.
**G1 is met for the selected contracts, G3 for the initialized finite profiles, and G4 for the full raw supervised rendering; G0/G2/G5 remain partly met.** A gate
requires every acceptance item, not merely a strong result in one component.

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

**Increment 92 acceptance:** the user approved replacing exactly six obsolete
installation-refusal diagnostics. [Plan 2](../plan2.md) is implemented: eager
initiators, grouped Any responder starts, captured contract coupling, physical
pool-exit guards, and the 381/322-event configured outbound witness with endpoint
controls and executable OwnedCallers proof. [The increment record](Supervision.md#ninety-second-increment-startondemandany-and-the-full-configured-outbound-witness)
records 785 accepted non-heavy affected modules and the 79-module deferred heavy
closure. Seed/selection/numerical-version instantiation and configured initialized
inbound coverage remain separate obligations.

## G0 — domain, scenario and source ledger: partly met

Acceptance: identity distinctions, profile assumptions and first-path branch
coverage reviewed.

| Evidence item | Status | Evidence and exact gap |
| --- | --- | --- |
| Identity distinctions | **met** | [Domain](Domain.agda) indexes identities by kind and separates full connection keys, addresses/ports and local-key alternatives. [DESIGN §§2–3](DESIGN.md) and [README](README.md) distinguish entry, worker, socket, mux, promise, handle and protocol-run lifetimes. This is a model representation decision, not source conformance. |
| Profile assumptions reviewed | **partly met; discrepancy reconciled** | [Pinned profile](BranchMatrix.md#pinned-locallifecycle-profile--increment-91) and [FullConfiguredProfile](Negative/FullConfiguredProfile.agda) now specify/check two ordinary peers, sane targets **2/2/1**, five hot protocols, **empty warm**, and established KeepAlive **8 / StartOnDemandAny**. Source directions, reduced 0/0/0 and 1/1/0 fixtures, 60 versus 120 clearing delay, feature/version abstraction and unseeded policy inputs are explicit. Increment 92 implements grouped responder startup and couples all three contract batches in the full configured outbound initialized witness. Missing: concrete source RNG/selection/numerical-version instantiation and configured initialized inbound coverage. All eight protocol/resource rows remain contracted observations, not source refinements. |
| First-path branch coverage reviewed | **partly met (matrix complete)** | [BranchMatrix](BranchMatrix.md) reconciles all 49 original ledger families and later branches in 99 rows: 67 implemented, 19 contracted, 13 excluded and 0 missing. It names actual initialized targets/bundles/selection inputs, corrects stale source ranges, separates accept-loop exits from the newly implemented handoff/worker exception edges, and records the reviewed protocol/registry/resource contracts. The review artifact closes plan step 1; no missing rows remain after [increment 90](Supervision.md#ninetieth-increment-g0-leios-protocol-and-shared-resource-contracts). Source execution of contracted inputs remains an instantiation obligation. Increment 92 resolves increment 91’s installer refusal: StartOnDemandAny is implemented with paired scheduler controls. G0/G2 stay partly met; zero missing rows does not establish source conformance or complete gate acceptance. Plan step 2 now supplies the [primitive matrix](PrimitiveMatrix.md); its five primitive runtime findings are implemented and accepted by capped regression. |

**Historical increment 91 outcome:** G0 was **not met**. Configuration discrepancies are
now concrete, with checked target initialization and exact source start modes;
the full profile still cannot execute and no fixture has a certified source
PRNG/selection/version instantiation. The [reconciliation](BranchMatrix.md#pinned-locallifecycle-profile--increment-91)
records omissions and deliberate abstractions. No remaining obligation is
removed by relabeling a row.

## G1 — state and primitive semantics: met

Acceptance: map take/restore, STM retry/rollback, fork, promise, queue and
cancellation examples.

| Evidence item | Status | Evidence and exact gap |
| --- | --- | --- |
| Map take/restore | **met** | [PrimitiveMatrix P01–P02](PrimitiveMatrix.md#shared-storage-concurrency-and-synchronization): [PrimitiveMap](Negative/PrimitiveMap.agda) adds enabled take/put/restore and empty-cell, foreign-owner and full-cell refusals. [HeapRollback](Negative/HeapRollback.agda) distinguishes saved-map restoration from committed heap rollback. [PrimitiveIncludeRestoration](Negative/PrimitiveIncludeRestoration.agda) now exercises X01: actual captured-body fault, saved-map-only restoration, retained heap/promise/child and separate close/result. |
| STM retry/rollback | **met** | Matrix P03–P04; [Scenarios/IGBatch](Scenarios/IGBatch.agda) `burst-fits`, `burst-retries-as-a-whole`, `split-prefix-would-fit`, ordered alternative/timeout controls; [Negative/Outbound](Negative/Outbound.agda) `full-queue-refuses-entire-commit`. The dependency contracts now cite the resolved STM implementations, not only API expectations. |
| Fork | **met for selected success/registration/failure contract** | Matrix P05; [ConcurrentPool](Negative/ConcurrentPool.agda) `fast-second-child-returns`, `fast-child-dereg-retries`, and masked parent insertion controls. J07 now has separate pre-birth failure, accepted-socket reservation, close and propagation controls in [PrimitiveAdmissionFork](Negative/PrimitiveAdmissionFork.agda). |
| Promise | **met** | Matrix P06–P07: [CM Types at the pin](PrimitiveMatrix.md#resolved-dependency-evidence), ordinary first write/duplicate exception, retained blocking read; [Scenarios/Handshake](Scenarios/Handshake.agda) `early-publication-is-readable`, `promise-survives-read`, `empty-promise-waits`, `duplicate-publication-throws`. `forcePromise` is unused by the selected model/handlers. Historical forcing probes retain their IO/IOSim limitations. |
| Queue and result synchronization | **met** | Matrix P08–P11: bounded IG bursts/flush versus source-unbounded completion/command queues; [PrimitiveResults](Negative/PrimitiveResults.agda) adds ordered first-result, empty/all-returned/error and pending-result controls. No queue/result observation implies physical termination. |
| Cancellation, mask/delivery, cancel/wait/waitCatch | **met for selected contracts** | Matrix P12–P15, C01–C18, H01–H02, S01–S14, U01–U06, K01–K07, I01–I10 and J01–J07 enumerates selected sites with named enabled/refusal controls, explicitly labelling permission equations and supplied blocking observations. IO/IOSim catch/mask/throwTo and waitCatch differences are source-backed. Configured startup delivery **S10/F2**, include-body restoration **X01/F1** and raw admission fork failure **J07/F5** are now implemented with paired controls; see [increment 80](Supervision.md#eightieth-increment-g1-primitive-runtime-closure). |
| Timeout winners and modeled delays | **met for supplied observations** | Matrix T01–T10 separates ordered idle/IG STM winners, exception-based PSA/Cold/drain timeouts, grant timer cancellation, TIME_WAIT and failure sleep. [PrimitiveTimers](Negative/PrimitiveTimers.agda) adds winner/readiness/duplicate-expiry and wrong-wait controls. [PrimitiveHandshakeContinuation](Negative/PrimitiveHandshakeContinuation.agda) covers distinct protocol-limit/bearer-timeout/query-delay continuations **T09/F4**; [PrimitiveGrantRefresh](Negative/PrimitiveGrantRefresh.agda) covers expiry/rearm **T10/F3** and grant/cancel controls. Untimed elapsed/expiry observations are not deadline guarantees. |
| Resolved dependency and runtime distinction audit | **met for the recorded Linux replay plan** | [PrimitiveMatrix dependency evidence](PrimitiveMatrix.md#resolved-dependency-evidence): GHC 9.6.7, base 4.18.3.0, stm 2.5.1.0, async 2.2.6, io-classes/io-sim 1.8.0.1, with plan SHA256, installed units, archive hashes and pinned helper sources. No new Haskell replay or universal IO/IOSim equivalence was established. |

**Plan step 2 runtime coverage is now 90 met / 0 missing** (original inventory
40/50; 12 November fixture checkpoint 85/5). All five findings are fixed rather
than excluded, with source-backed masking and explicit timer/blocking inputs.
**G1 is met** (13 November 2026): the affected SourceKeys/OwnedFrames/OwnedCallers
and heavy initialized concrete endpoints passed the capped regression of the [increment 80 check list](Supervision.md#eightieth-increment-g1-primitive-runtime-closure).
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
| Handler/protocol lifecycle | **partly met overall; outbound configured witness supplied** | [FullConfiguredWitness](Negative/FullConfiguredWitness.agda) couples all three reviewed contract batches to actual captured physical jobs, with eager initiators and nonempty established KeepAlive. [FullConfiguredFacts](Negative/FullConfiguredFacts.agda) separates clean local results, Async availability, shared cleanup, Cold and premature-step controls; [FullConfiguredCallers](Negative/FullConfiguredCallers.agda) certifies the whole initialized frontend schedule. Grouped responder startup has separate enabled/refusal controls. Missing: configured initialized inbound coverage and concrete source instantiation; validity and finite existence do not imply eventual completion. |
| Clean release in the combined initialized profile | **partly met overall; outbound configured witness supplied** | The reduced [InboundCleanLifecycle](Negative/InboundCleanLifecycle.agda) (109 events) and [OutboundCleanLifecycle](Negative/OutboundCleanLifecycle.agda) (156 events) keep their scopes. Increment 92 adds 322 full-bundle initialized outbound frontend events through clean deactivation/close, mux/pool exit, release TIME_WAIT receipt, socket/entry cleanup, physical handler result and Cold. The second selected peer's unentered job remains pending. Configured inbound coverage is still open; finite boundary-observation runs are not universal completion guarantees. |

| First witness required by DESIGN §9 | Status | Concrete evidence and exact gap |
| --- | --- | --- |
| Inbound clean lifecycle | **met for the reduced initialized profile** | [InboundCleanLifecycle](Negative/InboundCleanLifecycle.agda), `initialized-to-completion`, checks **109 actual events** from `V.initialize (O.initial c₀) settings`: Server admission, IG registration, clean responder result, normal mux/pool exit, inbound release, normal handler body exit, socket close, physical inbound receipt at unmasked TIME_WAIT, separate release return/IG commit, cleanup finally and Async publication. Endpoint: Terminated captured entry, empty live map, closed socket, no IG connection or pending inbound call, completed cleanup and available asynchronous result (cancellation interrupts TIME_WAIT after normal mux return). Existing premature/raw/outbound controls remain; new controls refuse missing-pending, premature and duplicate inbound receipt and premature result. [Increment 82](Supervision.md#eighty-second-increment-inbound-physical-release-receipt-and-clean-lifecycle) records the adapter/source contract and local validation; broad capped regression acceptance is separate. This finite boundary-observation profile does not establish universal liveness or source refinement. |
| Outbound clean lifecycle | **met for the full configured normal outbound profile** | [FullConfiguredWitness](Negative/FullConfiguredWitness.agda) has 381 contract-wrapper inputs and 322 real frontend events from the usual initializer. All six initiators complete their normal contracts; full hot promotion, target-driven clean demotion/close, physical results, release, handler cleanup, Cold and OwnedCallers are certified. The reduced 156-event witness remains unchanged. Source readiness and operation results are explicit contracts, and the second selected establishment job stays at its registered unentered boundary. |
| Duplex reuse | **met** | [ServerPeers.Protocols](Negative/ServerPeers.agda), `initialized-to-start`, includes actual inbound admission/publication/registration and startup, then outbound `Acquire.select (just (ident 0))` and return on the existing bearer. The header comments specify that only CM-free metadata is reused. This is an initialized finite model witness under `canInitiate`, not exhaustive reuse-branch or source replay coverage. |
| Handshake failure and socket cleanup | **met for the supervised initialized outbound failure profile** | [SupervisedHandshakeFailure](Negative/SupervisedHandshakeFailure.agda), `initialized-to-cleanup`: **40 real frontend events**, sharing the actual peer-job acquire/connect/fork prefix, then observed handshake deadline failure, real promise publication, caller disconnected return and peer-job failure observation, helper/body exit, physical socket/map cleanup and available handler result. Endpoint: closed socket, Terminated entry retaining error 7, empty live map, cleanupNormal, no allocated handle and physical `returned` (the helper handles the limit failure). Premature consumer/job/exit/finalizer/result, duplicate publication and success-after-failure controls pass. This covers the outbound caller/worker, not an inbound admission-worker failure history. [Increment 83](Supervision.md#eighty-third-increment-g2-outbound-clean-lifecycle-and-supervised-handshake-failure) distinguishes this from asynchronous cancellation and the older abstract scenario boundaries. |
| Successful hot demotion | **met** | [GovernorLifecycle](CSP/GovernorLifecycle.agda), `path`, includes clean hot-result publication and successful deactivation. [ServerPeersDeactivation](Properties/ServerPeersDeactivation.agda), `origin-success`, distinguishes already-Warm entry from an actual clean hot wait. This meets finite-path evidence for the reduced profile; it proves no universal demotion progress. |
| Timeout-driven cooling with delayed cleanup | **met for the reduced production-caller profile** | [TimeoutCoolingOwned](Negative/TimeoutCoolingOwned.agda), `initialized-to-completion`, checks 145 initialized events: established outbound peer → PSA operation timeout/Cooling → queued mux shutdown and pool exit → handler CM finally closing the socket and directly terminating/purging the entry → monitor Cold and normal job/monitor results. Every real frontend edge is `refl`. [TimeoutCoolingOwnedCallers](Negative/TimeoutCoolingOwnedCallers.agda) proves `every-owned`, `production-policy : Owned.Allowed initialized-outer` and `production-run : Owned.OuterRuns′ …` for the full schedule. No raw core begin, CM release or TIME_WAIT occurs. Controls retain required observations and distinguish demotion timeout from cleanup. The [increment 84 source audit](Supervision.md#pinned-source-audit-who-cleans-up-after-the-psa-timeout) explains why this outbound source branch has direct cleanup rather than TIME_WAIT. The existing 158-event [TimeoutCooling](Negative/TimeoutCooling.agda) remains foreign-caller delayed-cleanup evidence. Full application coverage, universal progress and implementation refinement are not established. |

**Reassessment of all six first witnesses (increment 84):** inbound clean is met
for its reduced initialized responder profile (109 events); outbound clean is met
for its reduced configured initiator profile (156); duplex reuse remains met for
the existing initialized shared-bearer history; handshake failure/cleanup is met
for its supervised outbound failure profile (40); successful hot demotion remains
met for the existing reduced finite path. Timeout/Cooling/cleanup/Cold is now met
for the reduced production-caller profile (145 events), with an executable
OwnedCallers certificate on the entire initialized history. The separate
158-event foreign-caller history retains TIME_WAIT evidence; the ordinary source
timeout branch uses direct handler cleanup. The older duplex/hot-demotion checks
were reviewed, not rebuilt here. **G2 overall remains partly met** because configured initialized inbound
coverage remains open. Batch 1 completes the three reviewed ChainSync/BlockFetch/registry
contracts; batch 2 completes TxSubmission2 and KeepAlive, and batch 3 completes
LeiosNotify, LeiosFetch and shared Leios resource contracts (zero missing rows). Increment 92 now couples these contracts to the full selected outbound bundle;
the kernels and generic adapters retain their separate scopes. These histories do not establish universal lifecycle, shutdown,
deadline or implementation-refinement theorems.

**Increment 92:** the full configured outbound obligation is implemented in
[FullConfiguredWitness](Negative/FullConfiguredWitness.agda), with a coupled
contract run, exact frontend projection, endpoint/refusal facts and full-prefix
[OwnedCallers](Negative/FullConfiguredCallers.agda) execution. Hot 2/3/4/18/19,
empty warm and established 8 run through their normal lifecycles; selected
protocol, handler, governor-job and monitor results are separately available at
Cold. The second selected establishment job remains registered and unentered;
this does not certify all-worker/node shutdown. Increment 91’s refusal diagnostics
are historical and replaced under the user’s narrow exception.

**G2 overall remains partly met:** full configured initialized inbound coverage
remains open; concrete source policy/selection/version instantiation remains a
G0/G2 boundary. Source readiness, pipeline/driver/DB and private-registry effects
are contracted inputs. This finite outbound run does not establish universal
progress, deadlines, cancellation joins for all node workers or Haskell refinement.
The other reduced-profile witnesses retain their accepted scopes.

## G3 — concurrency: met

Acceptance: two peers, duplex reuse, delayed cleanup, same-key overlap and
job/monitor interleavings.

| Evidence item | Status | Evidence and exact gap |
| --- | --- | --- |
| Two peers | **met for the reduced initialized profile** | [ConcurrentLifecycles](Negative/ConcurrentLifecycles.agda), `initialized-to-completion`: **294 actual events**, two distinct ordinary outbound peers both acquiring, negotiating, running clean configured initiators, closing mux pools, releasing, cleaning up and reaching Cold with handler/close-job/monitor physical results. [Facts](Negative/ConcurrentLifecycleFacts.agda) check distinct captures, endpoints, premature/raw/duplicate refusals and exact allocation counts. The [entire run executes in OwnedCallers](Negative/ConcurrentLifecycleOwnedCallers.agda); no raw core begin or injected competitor occurs. |
| Duplex reuse | **met** | The initialized `ServerPeers.Protocols.initialized-to-start` witness described under G2 exercises shared-bearer reuse. |
| Delayed cleanup | **met** | [ServerPeersOrigins](Negative/ServerPeersOrigins.agda) retains actual birth/resources through elapsed/interrupted TIME_WAIT and final CM waits; [release-caller delivery](Negative/ServerPeersReleaseTimeWait.agda) enters that delay through a real receipt. These are finite initialized schedules, not a deadline theorem. |
| Same-key overlap | **met for the initialized overlap profile** | [OverlapInitialized](Negative/OverlapInitialized.agda), `initialized-to-overlap`: **303 actual events**, same-key captured entries 0 → 2 → 3 while genuinely allocated other-key entry 1 is present. The first two execute clean responder/mux/release paths and defer their captured TIME_WAIT finalizers until the third is admitted, published, registered and starts its mux. [Facts](Negative/OverlapInitializedFacts.agda) prove both old finalizers actually execute without changing the new/other map entries, preserve all four captures, refuse premature/duplicate steps and count allocations. [OwnedCallers](Negative/OverlapInitializedOwnedCallers.agda) certifies the whole initialized schedule. New and other handlers intentionally remain live; this is not all-connection completion or a GovernorWedge source replay. |
| Job/monitor interleavings | **met** | [Negative/Subsystem](Negative/Subsystem.agda) checks child-before-registration; [ServerPeers](Negative/ServerPeers.agda) includes initialized restart/publication/cancellation races. [ServerPeersMonitorJoins](Properties/ServerPeersMonitorJoins.agda) proves ordered snapshot/join histories. Coverage is selected interleavings, not exhaustive schedule exploration. The new [294-event two-peer run](Negative/ConcurrentLifecycles.agda) adds both establishment children entering before registration, alternating protocol/mux work and independent Cold/close-job/physical-monitor results, with [controls](Negative/ConcurrentLifecycleFacts.agda) and a full OwnedCallers certificate. |

[Increment 85](Supervision.md#eighty-fifth-increment-g3-initialized-concurrency-histories) records the new initialized histories and allocation budgets. **G3 is met at these finite-profile scopes**; this does not close G0/G2/G4/G5, prove exhaustive interleavings or establish universal delivery/shutdown progress.

## G4 — semantic bridge: met for the full raw supervised rendering

Acceptance: machine/process transition and trace correspondence, monitors and
negative controls.

| Evidence item | Status | Evidence and exact gap |
| --- | --- | --- |
| Machine/process transition correspondence | **met for the full raw supervised runtime** | [Supervised](CSP/Supervised.agda) and [SupervisedInner](CSP/SupervisedInner.agda) instantiate [Dispatcher](CSP/Dispatcher.agda), the existing productive `react` rendering pattern, with `outerStep` and `T.advance`. `step-intro`/`step-inv` retain exact successor states for every `OuterAction`/`T.Event`, including physical and relays events. No execution rules or existing Agda modules are changed. This is a representation theorem, not separate parallel composition or Haskell refinement. |
| Finite run/trace correspondence | **met for raw traces and the lossless trace object** | Both bridges prove native `exec-intro`/`exec-inv`, `trace-intro`/`trace-inv` and arbitrary `all-trace-inv`; outer `all-exec-inv` also retains the process endpoint. [ResultTrace](CSP/ResultTrace.agda) renders exact `(before, action, after)` observations, proves `record-run`/`erase`, `recorded-trace`/`all-trace-recorded` and uniqueness for a fixed start/action list. [SupervisedWitness](CSP/SupervisedWitness.agda) maps the committed 109-event initialized inbound G2 history to inner/outer traces, result snapshots and replay acceptance, with a refused-result extension. The old action-only hiding policy remains result-omitting; no value-bearing API-only PTree, expanded hiding correspondence, hidden divergence or failures-divergences refinement is claimed. |
| Refusal explanations | **met over every state and the full raw alphabet** | [Dispatcher](CSP/Dispatcher.agda), `refusal-exact`, proves arbitrary-set stable refusal iff every corresponding machine action is disabled. `singleton-refusal`/`singleton-refusal-inv` give the individual-event form. `failure-intro`/`failure-inv` and `all-failure-inv` characterize stable failures by actual machine runs ending in disabled sets; both supervised bridges expose native run adapters. Tick is always refused and has no machine action. No reachable-state or finite-carrier premise is needed. |
| Decoder and coverage | **met for the full typed inner/outer alphabets** | `decode-event`, `alphabet-complete`, `action-covered`, `encode-decode`, `decode-label`, `decode-sound` and `label-injective` prove a bijection between visible raw labels and the complete action type, including disabled actions and all nested payloads. Both renderers publicly instantiate these facts. Ambient tick is explicitly rejected; `SupervisedControls.tick-not-covered` checks the stronger all-`Event√` surjectivity claim is false. This is a typed-alphabet contract, not a byte/log parser or source-coverage claim. |
| Monitors | **met for typed rendered input and machine refusal explanations** | [RuntimeMonitor](CSP/RuntimeMonitor.agda), `decode-input-label`, `visible-input-covered`, `decode-schedule` and `replay-rendered-run`, supplies the verified rendering adapter and run acceptance. `refusal-rendering`/`rendering-refusal` connect disabled replay edges with stable refusals in both directions. Malformed/unsupported external declarations, fuel cutoff and optional ordinary-wait/model-gap causes remain distinct; classifying all disabled actions into such causes is not asserted. Legacy origin diagnostics and live-tracker invariants remain unchanged. |
| Negative controls | **met** | Existing [HeapRollback](Negative/HeapRollback.agda), [CleanupAtomicity](Negative/CleanupAtomicity.agda), [CounterValidity](Negative/CounterValidity.agda), [LiveTrackerReferencesCounterexample](Properties/LiveTrackerReferencesCounterexample.agda) and [OriginMonitor](Negative/OriginMonitor.agda) are unchanged and pass selected regression checks. `SupervisedWitness.premature-result-refused` excludes physical result publication before TIME_WAIT finally after a genuine initialized prefix. New controls separate unequal physical-result observations, refuse premature outer cancellation, and distinguish replay frontiers. Increment 87 adds the initialized pre-result stable failure, a genuinely enabled next step at that same state, refusal/monitor round trips, disabled-action decoding and tick exclusions. Variant controls remain unchanged; they were not rebuilt here. |

[Increment 86](Supervision.md#eighty-sixth-increment-g4-supervised-runtime-semantic-bridge)
records exact signatures, observation contract, validation and exclusions.
**G4 is met for the full raw supervised rendering**, with the lossless result-trace contract from increment 86. [Increment 87](Supervision.md#eighty-seventh-increment-g4-refusal-and-decoder-completeness) closes both remaining typed semantic obligations. External byte/log parsing, completeness against pinned source operations, a compact value-bearing API-only PTree/hiding abstraction, hidden divergence and independent parallel composition remain outside this acceptance. No such implementation/refinement claim follows.

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

[DesignContract](DesignContract.md) completes plan step 6: source patch outline,
proved safety scope, explicit progress assumptions, rejected variants and pinned
replay acceptance for late admission, self-purge and all phase C detachments.
Implementation and progress validation remain open.

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
| 2 | M | **Done**, 13 November 2026. [PrimitiveMatrix](PrimitiveMatrix.md): 90 rows, original 40/50 → inventory checkpoint 85/5 → current 90/0 met/missing. F1–F5 now have source-backed rules and paired fixtures. [Increment 80](Supervision.md#eightieth-increment-g1-primitive-runtime-closure) records the checks and remaining capped endpoints. **G1 is met.** |
| 3 | M | **Done for the reduced initialized inbound profile, 13 November 2026.** [InboundCleanLifecycle](Negative/InboundCleanLifecycle.agda), `initialized-to-completion`: 109 actual frontend events through normal responder/mux exit, inbound physical release receipt, socket/entry cleanup, IG unregistration and handler result. The separately authorized source review confirmed masked inbound `throwTo` and the handler’s unmasked TIME_WAIT; [increment 82](Supervision.md#eighty-second-increment-inbound-physical-release-receipt-and-clean-lifecycle) records the new adapter, controls and validation. Existing statements/raw guards are unchanged. Capped broad regression endpoints remain user-run acceptance. |
| 4 | M | **Done for the explicit reduced configured profiles, 13 November 2026.** [OutboundCleanLifecycle](Negative/OutboundCleanLifecycle.agda), `initialized-to-completion` (156 events), and [SupervisedHandshakeFailure](Negative/SupervisedHandshakeFailure.agda), `initialized-to-cleanup` (40 events), start at the supervised initializer, check every real step by `refl`, and join caller/job observations to socket/entry cleanup and handler physical results. The outbound path uses increment-66-family physical release receipt and separately preserves the duplex retained-inbound distinction. Endpoint facts/premature controls and eight fresh checks pass; [increment 83](Supervision.md#eighty-third-increment-g2-outbound-clean-lifecycle-and-supervised-handshake-failure) records the one-protocol scope. Full application coverage remains open; step 5 is assessed below and G2 overall stays partly met. |
| 5 | M | **Done for the reduced production-caller profile, 13 November 2026.** [TimeoutCoolingOwned](Negative/TimeoutCoolingOwned.agda), `initialized-to-completion` (145 events), checks the source timeout → mux/handler exit → direct CM cleanup → monitor Cold and physical job/monitor results. [TimeoutCoolingOwnedCallers](Negative/TimeoutCoolingOwnedCallers.agda) proves the entire initialized schedule is allowed and executes in OwnedCallers: no raw begin, CM release or TIME_WAIT. The [increment 84 audit and production witness](Supervision.md#production-only-timeout-cooling-witness) distinguish this source path from the retained 158-event foreign-caller TIME_WAIT history. Endpoint facts, premature controls and both fresh checks pass. Full application contracts/bundles remain open; G2 stays partly met. |
| 6 | M | **Done — [DesignContract](DesignContract.md), 13 November 2026.** Documents worker joins and the historical handler registry, exact model guarantees/premises, open progress assumptions, rejected variants/counterexamples and a pinned prototype/IOSim plan covering phase C detached handlers. Documentation acceptance only: implementation/replay and eventual-shutdown obligations remain open; quiescence is endpoint safety. |
| 7 | M | **Done for the initialized finite profiles, 13 November 2026.** [ConcurrentLifecycles](Negative/ConcurrentLifecycles.agda) (294 events) and [OverlapInitialized](Negative/OverlapInitialized.agda) (303) supply both executing ordinary peers and three overlapping same-key incarnations with another real key present. All real edges are checked by `refl`; endpoint/captured-identity facts, delayed-finalizer preservation, refusal controls, exact allocation budgets and full executable OwnedCallers certificates pass. [Increment 85](Supervision.md#eighty-fifth-increment-g3-initialized-concurrency-histories) records scope and serial checks. **G3 is met**; no universal progress, full application coverage or source refinement follows. |
| 8 | M | **Done for the full raw supervised rendering, 13 November 2026.** [Increment 86](Supervision.md#eighty-sixth-increment-g4-supervised-runtime-semantic-bridge) supplies step/run/arbitrary-trace correspondence, lossless result traces and initialized controls. [Increment 87](Supervision.md#eighty-seventh-increment-g4-refusal-and-decoder-completeness) adds arbitrary-set refusal/stable-failure correspondence, complete unique typed decoding and action coverage, verified monitor input and committed-state refusal/non-deadlock controls. **G4 is met at this scope.** No existing theorem statement or machine rule changes; no source-parser, compact API/hiding, hidden-divergence or parallel-architecture claim. |
| 9 | L | Implement enabledness-complete bounded enumeration and checked export/reimport over a declared finite carrier, with explicit allocation/depth cutoffs. First replay all ordinary initialized witnesses within bounds; then record targeted race searches with exact bounds and outcomes. |
| 10 | M | Add candidate minimization with replay/violation preservation, retain original and reduced traces, and replay selected reduced source operations at the pinned revisions with controls. Classify each result as model distortion, unconfirmed candidate or replay-confirmed source behavior; close G5 only when every item is evidenced. |
