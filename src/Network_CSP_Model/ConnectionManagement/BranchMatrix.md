# Pinned branch and fixture matrix

13 November 2026 (increment 91 configuration reconciliation). The 12 November audit completed [GateAudit plan step 1](GateAudit.md#ordered-gap-closing-plan): an inventory review, not implementation or gate closure. It reconciles [SourceLedger](SourceLedger.md), [DESIGN §§1–2, 9–11](DESIGN.md), [Supervision](Supervision.md) through increment 82, the [migration profile](MigrationProfile.md) and [migration acceptance](BASELINE_MIGRATION_PLAN.md). The original inventory used declarations and topic records. The G1 follow-up implements two previously missing branches below; [increment 80](Supervision.md#eightieth-increment-g1-primitive-runtime-closure) records the accepted G1 checks. The inbound receipt follow-up in [increment 82](Supervision.md#eighty-second-increment-inbound-physical-release-receipt-and-clean-lifecycle) completes the reduced initialized inbound witness; its broad capped regression remains separate.

## The profile actually exercised

Authority is network **`2f1c154f248659b89523d5679ca532f442e7ed2a`**, pinned by consensus **`2e44d98a843168ba3b189e305820b79943ac7d1e`**. Earlier evidence keeps network `96ee6e0…` / consensus `585a861…`. The [baseline manifest](../review/source-baseline-2026-11-06.json) records unchanged CM/IG/Server/JobPool files and changed mux, handler and diffusion files. Retained network source copies were matched against its promoted blob inventory before locating the changed ranges below. Consensus bundle, fetch and logic copies match the manifest's applicable content hashes. This does not establish source refinement. The original inventory audit did not inspect model Git metadata; increment 91 separately inspected model HEAD `5a6f9ef633e909577be20842a236d076d4affcc9`.

There is **no successful executable fixture matching all of DESIGN's LocalLifecycle choices**. Increment 91 adds the exact descriptor/target profile and an initialized allocation-refusal diagnostic below. In particular, two accepted sockets do not mean two executing ordinary peers, and protocol number 1 below is a synthetic descriptor, not the configured six-protocol application.

| Fixture and initializer | Actual initial configuration and bundle |
| --- | --- |
| [CSP/GovernorLifecycle](CSP/GovernorLifecycle.agda), `settings`, `c₀ = Subsystem.initial (OutboundMachine.initial CSP.Fixtures.start) settings` | One known ordinary peer, `remote Scenarios.Admission.key₀`; targets **known 1, established 1, active 1**. No established/active peers or jobs initially. The 146-action `path` uses one hot `protocol 1 hot onDemand`, empty warm and established groups, then lowers active to 0. `CSP.Fixtures.start` already contains two accepted admission callers/sockets; it is not a Server boot trace. |
| [Negative/ServerPeers](Negative/ServerPeers.agda), `Fixtures.settings`, `Interleaving.initializer` | `ServerPeers.initial (O.initial (Machine.initial responderMode ServerAdmissionPrefixFixtures.empty)) Fixtures.settings`. One known peer at `remote key₁`, targets **1/1/1**. Starts with an empty CM and no raw workers; the path performs two `acceptedFork` handoffs. The second handoff is not a second completed OG lifecycle. |
| Same module, `Protocols.initializer`, `Protocols.initial`, `Protocols.capability` | `ServerPeers.Protocols.initialize (O.initial (Machine.initial responderMode F.empty)) GovernorLifecycle.settings`. Targets **1/1/1**, known peer `remote key₀`. Actual admission, duplex publication, IG registration and outbound reuse precede physical initiator work. The admitted bundle from [MuxPublicationInboundFixtures](Negative/MuxPublicationInboundFixtures.agda), `ps`, is the same single hot/on-demand protocol 1. `capability` admits only handle 0 / protocol 1. Empty warm/established bundles remain. [Negative/LiveTrackerInitialized](Negative/LiveTrackerInitialized.agda), `scheduled-full-validity`, applies the general validity theorem to this initialized scheduled-close history; it adds no protocol-body coverage. |
| [Negative/ServerAdmissionPrefixFixtures](Negative/ServerAdmissionPrefixFixtures.agda), `start`, instantiated by [ServerIGExitFixtures](Negative/ServerIGExitFixtures.agda) as `F = Prefix 10 key₁` | One live listener and IG, no connections/workers initially. Admission hard limit **10**, matching `Machine.initial`'s promotion hard limit. `ServerAdmission.acceptedFork` supplies each accepted socket and its worker. [Negative/ServerAdmission](Negative/ServerAdmission.agda), `start`, uses the same empty post-setup shape without an OG. |
| [Negative/MuxConfiguredTraffic](Negative/MuxConfiguredTraffic.agda), `plan`, `keys`, `initialized-configured-traffic` | A separate initialized physical-birth/mux fixture, not a two-peer LocalLifecycle run. `scheduledLayout false`: Direct and Scheduled muxers plus demuxer, no Slice worker; protocol 1 initiator routes to Scheduled, responder to Direct. `configureMux owner plan 16 1000 keys` fixes its limits. Handler setup precedes publication; a real Direct write precedes clean completion. Plain compatibility fixtures use one Unscheduled muxer plus demuxer. |

Common executable policy values are in [Subsystem.initial](Subsystem.agda): maximum retries **5**, failure clearing **60** time units, time and allocation counters initially zero. The source production clearing default is **120 seconds** ([Outbound policy comparison](Outbound.md#retry-policy-values)); the model/replay choice is deliberate. Ordinary target sanity is `active ≤ established ≤ known`, with ceilings 100/1000/10000; omitted root and big-ledger targets embed as zero, root sets empty. Sane target changes pass through `setTargets` and governor selection, not direct state edits.

**There is no model PRNG seed.** `OutboundMachine.initial.randomGeneration` and `Machine.initial.pruningGeneration` start at 0; these are draw markers. Acquisition accepts an eligible bucket member; pruning accepts generation-tagged integer scores; governor selection accepts eligible peers and establishment jitter 0–4. These are the [Outbound selection](Outbound.md#acquisition) and [Pruning score](Pruning.md#randomness-delivery-and-ordering-assumptions) contracts, not `StdGen` state. In particular, retry may choose a different member without a changed input map, whereas the source STM split rolls back. Replay seeds **0, 1, 42** in [SourceReplay](SourceReplay/README.md) are separate source experiments, not seeds of these Agda fixtures.

The physical fixture's exception projections are explicit: `MuxPublicationInboundFixtures.bearerClosed` recognizes error 999; `Negative/GovernorPool.classify` recognizes error 7 as IO-manager error. `ServerPeers.Fixtures.classify` is instead constantly false for its local interleaving fixture. They must match represented source exceptions before making source claims. Negotiation supplies a fixed bundle and permitted flow; duplex capability permits reuse but does not require both roles to run.

All fixtures start after listener/governor infrastructure setup. Assumptions are one listener, ordinary fixed-known peers, enabled assertions, untimed token expiry, nondecreasing sampled time, explicit transport/buffer/policy outcomes and successful observed diagnostic traces. The IG queue has capacity 100; source unbounded queues remain unbounded. Address order is abstract remote-before-local; signed counters and byte arithmetic require their stated non-overflow profiles. There is no fairness, eventual reply/write/cleanup or whole-node-boot premise. Increment 91 below reconciles DESIGN's **2/2/1** targets and exact descriptors; execution is blocked by KeepAlive's start mode. The full contracts are reviewed, but their runtime coupling and a concrete seed-to-selection relation remain obligations. Peras, PeerSharing, local roots, big-ledger policy and discovery are excluded.

## Pinned LocalLifecycle profile — increment 91

**Reconciliation result: targets are expressible; the source bundle is
representable as data but is rejected by executable installation.** Phase 2 is
stopped at this guard. No start mode, existing statement or runtime rule is
changed. [FullConfiguredProfile](Negative/FullConfiguredProfile.agda) gives the
usual `V.initialize (O.initial c₀) settings` equality with empty CM/physical jobs,
one post-setup listener and two known ordinary peers. Initial targets are
known **2**, established **2**, active **1**. `key₀`/`key₁` use local IPv4 host 0,
port 3001 and remote hosts 1/2, port 3001. Both known records have failures and
connectAt 0, clearFailuresAt Nothing, tepid/successful false; all established,
active, in-progress, cooling and tenure collections are empty. `targets-sane`
checks the model projection. Embedding root and all big-ledger targets as 0
satisfies [GTypes] 270–290 with empty root sets. These are selected scenario
values, **not production default targets**. No target is lowered in this blocked
prefix; a future demotion must use `setTargets`/the target monitor.

### Bundle and directions

Authority: [wire bundle][Wire] 250–325, 475–494 (blob
`ec3a1f45ba0116bc9fa0e90e45ab2acad1176014`) and [Bundle] 1963–2100
(blob `b2f3e96e8458592e2eee7dd4fd33174b4d6c63c3`). Both were read at the
pins above. PerasUnsupported and PeerSharingDisabled select this layout:

| Group | Protocols, in source group order | Descriptor start mode | Directions in initiator-and-responder application |
| --- | --- | --- | --- |
| Hot | ChainSync **2**, BlockFetch **3**, TxSubmission2 **4**, LeiosNotify **18**, LeiosFetch **19** | `StartOnDemand` for all five | Each has initiator and responder callbacks |
| Warm | **empty** | None | Neither direction has a warm protocol |
| Established | KeepAlive **8** | **`StartOnDemandAny`** | Initiator and responder callbacks |

The initiator-only projection has the same descriptor groups/modes with only
initiator callbacks. **Effective start policy differs by direction:** [Actions]
1180–1198 starts initiators with `StartEagerly`, overriding descriptor start mode;
[IG] 777–795 passes the descriptor mode to responder starts. Establishment starts
warm then established initiators, activation starts hot initiators. IG installs
all three responder groups for eligible inbound/duplex registrations. Thus
KeepAlive's grouped-readiness behavior belongs to responder scheduling, while
this model rejects its descriptor even for outbound unidirectional or
initiator-only installation before that distinction can be used. Negotiated unidirectional flow does not start a local responder just
because the node uses initiator-and-responder diffusion. Duplex permits reuse;
it does not imply all callbacks run. The diagnostic selects outbound
unidirectional flow, full six-number initiator capability on handle 0 and a plain
mux. It reaches no started callbacks. Requiring a nonempty warm protocol would
change this selected source configuration; the reduced warm protocol 1 cannot
be added to fill that group.

The Agda list is globally sorted `2,3,4,8,18,19` because `IG.ordered` requires
strict number order; filtering by temperature retains the source group orders.
`Protocol` records number, temperature and start mode; it carries no codec,
network magic, numerical version or feature-flag value. Source layout selection
ignores the version argument here. Supported [source versions][WireVersion] 14/15/16 with
PerasUnsupported and PeerSharingDisabled share this descriptor layout; no
specific numerical version is recoverable from a model handle. Fixing one for
codec/source replay remains an instantiation obligation. Tx responder V1/V2 is
selected separately by `txSubmissionLogicVersion` ([Bundle] 551–578), not a
second protocol 4 or a wire-version inference. Neither responder variant is
instantiated in this blocked outbound diagnostic. Payload/codec, peer trust,
limits, private resources and remote operation outcomes retain the explicit
[protocol contracts](ProtocolContracts.md); no unsupported numerical/version
claim is inferred from descriptor equality.

### Exact execution gap and initialized diagnosis

[IGRegistration](Rules/IGRegistration.agda), `supported`, returns false as soon
as it sees `onDemandAny`; both `installWith` and `installInitiatorWith` require
true. `MuxHandlerSupervision.allocate` calls the corresponding real install
operation through `O.advance`. Merely having `MuxRuntime.demandAny` as a status
constructor supplies no grouped-readiness monitor. [Mux] 745–761, 797–802 waits
for demand on any mini-protocol to start these responders. Replacing KeepAlive
with independent on-demand or eager startup would change that semantics.
This is an executable gap for **both** source directions and for initiator-only
installation, not a missing descriptor constructor, ordering failure, occupied
handle or protocol-contract completion refusal.

`FullConfiguredProfile` checks the sane initializer, ordered six-number bundle,
unsupported full bundle and singleton KeepAlive, and real inbound/outbound/
initiator-only installation refusals. [FullConfiguredAcquire](Negative/FullConfiguredAcquire.agda)
uses 23 real frontend edges: select both eligible peers at time 0, apply/trace,
fork/register the first establishment job, owned acquire/reserve/socket connect,
physical handler fork/handoff/commit and enter handshake. The second peer stays
known with its establishment launch pending. [FullConfiguredBlocked](Negative/FullConfiguredBlocked.agda)
adds the actual full-bundle negotiation-return edge: **24 initialized events**,
every edge `refl`, no injected midpoint. `allocation-refused` is the next real
frontend step. Controls refuse premature publication, body exit and handler
result; endpoint facts show two known peers, no installed handles/muxes, no
physical protocol jobs and no handler result. [FullConfiguredBlockedCallers](Negative/FullConfiguredBlockedCallers.agda)
proves the **prefix's** `every-owned`, `Owned.Allowed` and executable
`Owned.OuterRuns′` inside the relays scope. It proves no hot promotion, protocol
lifecycle, Cold endpoint or available final job/handler result. The increments
88–90 adapters stay conditional and unwired: wiring them alone cannot pass the
installation guard. Per the task's stop condition, phase 2 is not attempted.

### Policy seed and selected inputs

There is **no executable Agda seed** and no source seed certified for these
fixtures. Source [Diffusion] 301–308 splits externally supplied `diRng` into
ledger, churn, fuzz, local CM, remote CM1/CM2, egress and peer-selection-actions
generators; the IO entry uses `newStdGen` (1062). [Policies] 150–270 ranks peers
using atomic `StdGen` splits and Word32 draws, with tepid/failure/metric weights;
[Established] 521 uses `randomR (-2,2 :: Double)` for establishment fuzz.
CM bucket choice/splitting is atomic with retry rollback ([Core] 1276–1279,
1379–1388). Model generation counters start at **0**, not `mkStdGen 0`.
`selectPolicy` supplies an eligible distinct list up to quota; `Acquire.select`
supplies a bucket member or absent choice; pruning supplies generation-tagged
scores; establishment jitter uses integral codes **0..4** for -2..2. These
abstractions bound eligibility and permit finite scheduling studies without
implementing PRNG/distribution/continuous time. They do **not** certify source
ranking, full requested pick cardinality or deterministic retry selection.

For the new diagnostic the initial source-style establishment pick cardinality
is two: both eligible peers are explicitly selected; the first source-address-
ordered job acquires an absent bucket (`Acquire.select nothing`). No pruning,
fuzz or metric-based choice is reached. In `OutboundCleanLifecycle` and
`TimeoutCoolingOwned`, the shared prefix selects only the sole eligible peer,
absent acquisition, targets **1/1/0**, and one warm/on-demand initiator 1;
there are no hot/established protocol bodies or KeepAlive registry work.
`InboundCleanLifecycle` has targets **0/0/0**, no known peers or OG job and only
one hot/on-demand responder 1. The 1/1/1 hot-protocol fixtures in the earlier
table omit the other named hot protocols and all established work as well.
All begin with draw counters 0; none runs a seeded source peer policy.
Common retry maximum **5** matches source; clearing delay **60** versus source
**120 seconds** is an existing discrete-time model/replay parameter, not a
reconciled deployment default. All timers are untimed observations.

The concrete seed/selection obligation is still open: fix the source `diRng`
and split consumption, policy metrics and peer order, project actual selected
sets/bucket choices/pruning scores/fuzz at each transaction, and preserve retry
rollback. Existing replay seeds 0/1/42 do not instantiate this schedule.
Accordingly **G0 remains partly met** despite completing this discrepancy
reconciliation, and **G2 remains partly met**. Their remaining work includes
source-faithful grouped readiness, seed/selection/version instantiation and full
configured initialized contract/job/handler execution, including clean
inbound/outbound coverage. No missing matrix row is concealed: the existing
StartOnDemandAny **excluded** row is a blocker to the intended full profile.

## Reading the matrix

**Counts: 66 implemented, 19 contracted, 14 excluded, 0 missing (99 rows).** All 49 original ledger family IDs occur below; split and additional rows expose different statuses.

Each row has one status: **implemented** means the named selected rule has a fixture or theorem; **contracted** means the cited abstract operation/input stands in for source execution; **excluded** names an intentional scope omission; **missing** has neither adequate implementation nor a completed contract. Implemented does not mean every branch has an initialized whole-system witness. Local controls, initialized finite paths and invariants retain their different strengths. G0 applies to every row; the gate column lists the other gates served.

Source aliases below link to full files at the promoted pins. Ranges are source lines, not Agda lines. Model paths are relative to this directory; `R/` in prose means `Rules/`. Broad operation ranges cover the case alternatives named in the row. The original ledger family IDs are retained, with separate rows where statuses differ.

### Primitives and helpers

| Family / selected branches | Pinned source | Model rule and evidence / contract | Status | Gates |
| --- | --- | --- | --- | --- |
| `CM.MAP.TAKE/BODY/PUT/RESTORE`: success and exception restoration | [Core] 2364–2400 | [R/CM](Rules/CM.agda), `takeMap`, `putMap`, `restoreMap`; [Scenarios/MapOwnership](Scenarios/MapOwnership.agda), [Negative/HeapRollback](Negative/HeapRollback.agda). Restore map, retain committed heap writes. | **implemented** | G1, G2 |
| `CM.MAP.STM`: atomic commit/retry | [Core] 2384–2400 | [R/CM](Rules/CM.agda) STM entry updates; [Negative/CleanupAtomicity](Negative/CleanupAtomicity.agda), [Negative/Outbound](Negative/Outbound.agda) refusal/rollback controls. | **implemented** | G1, G2 |
| `SYNC.FIRST`: ordered alternatives at selected sites | [Sync] 41–69; [Actions] 361–381; [IG] 242–278; [Mux] 628–646 | [R/PeerActions](Rules/PeerActions.agda), `first`; [R/IGBatch](Rules/IGBatch.agda), `selectBatch`; [MuxResultMonitor](MuxResultMonitor.agda), `consume`; [CSP/IGRuntime](CSP/IGRuntime.agda), [Negative/MuxResultMonitor](Negative/MuxResultMonitor.agda). | **implemented** | G1, G2 |
| `SYNC.ALL`: empty groups, errors, all started results | [Sync] 74–129; [Actions] 383–435 | [R/PeerActions](Rules/PeerActions.agda), `all`; physical read coupling in [ServerPeers.Protocols](ServerPeers.agda); [Negative/ServerPeers](Negative/ServerPeers.agda), `Protocols`, and [ServerPeersDeactivation](Properties/ServerPeersDeactivation.agda). | **implemented** | G1, G2 |
| `JOB.FORK/REGISTER`: child before masked parent insertion | [JobPool] 113–177 | [R/JobPoolKernel](Rules/JobPoolKernel.agda), fork/register; [Negative/Subsystem](Negative/Subsystem.agda), `racePath`, `registration-required`; [Negative/ConcurrentPool](Negative/ConcurrentPool.agda). | **implemented** | G1, G3 |
| `JOB.COMPLETE/DEREGISTER`: queued/unqueued, sync/async outcomes | [JobPool] 113–177 | Same kernel and [JobPoolLifecycle](Rules/JobPoolLifecycle.agda); [Negative/JobPoolLifecycle](Negative/JobPoolLifecycle.agda). Completion, removal and Async result are separate. | **implemented** | G1, G2 |
| `JOB.WAIT/CANCEL`: FIFO wait, captured registry cancel/join | [JobPool] 70–110, 179–225 | [GovernorPool](GovernorPool.agda), [MuxGroupShutdown](MuxGroupShutdown.agda); [Properties/GovernorPool](Properties/GovernorPool.agda), [Negative/MuxGroupShutdown](Negative/MuxGroupShutdown.agda). | **implemented** | G1, G2, G3 |
| `IG.QUEUE`: FIFO, full retry, whole flush and bursts | [Info] 35–54 | [R/InformationChannel](Rules/InformationChannel.agda), burst/flush; [Scenarios/IGBatch](Scenarios/IGBatch.agda), `burst-retries-as-a-whole`. | **implemented** | G1, G2 |
| `MUX.STOP/STOPPED`: command enqueue and status wait | [Mux] 214–221, 326–328 | [R/IGRegistration](Rules/IGRegistration.agda), `enqueueMuxStop`, `pollStopped`; [CSP/IGRuntime](CSP/IGRuntime.agda). A request is not drain, cancellation or join. | **implemented** | G1, G2 |
| `EXN.DELIVER`: selected request/receipt/unwind sites | [Core] 523–550, 1254, 2032; [JobPool] 105–109 | [Supervision cancellation matrices](Supervision.md#acquisition-cancellation-matrix), [CallerCancellation](Rules/CallerCancellation.agda), [MuxExitCancellation](MuxExitCancellation.agda), [MuxCatchUnwind](MuxCatchUnwind.agda). Receipts and blocked-operation observations stand in for full IO/IOSim mask semantics. | **contracted** | G1, G2 |
| `TIMER/PROMISE`: allocation/read/write, readiness and winner inputs | [CMTypes] 266–322; [Handler] 392–442, 474–518; [Governor] 657–665; [Actions] 986–1107 | [R/Handshake](Rules/Handshake.agda), [R/OutboundRelease](Rules/OutboundRelease.agda) and [forcing/mask probes](SourceReplay/README.md). Token expiry, fresh-promise and observed helper-return contracts remain; resolved dependency versions and all winner/delivery sites await plan step 2. | **contracted** | G1, G2 |

### Server, outer scopes and admission

| Family / selected branches | Pinned source | Model rule and evidence / contract | Status | Gates |
| --- | --- | --- | --- | --- |
| `WIRE.START/SUPERVISE`: initial wiring/setup | [Diffusion] 632–698, 860–950; [Server] 147–180 | [ServerPeers.initial / Protocols.initialize](ServerPeers.agda) and [MigrationProfile](MigrationProfile.md): post-setup infrastructure and external policy/IO parameters. No whole-node setup execution. | **contracted** | G2 |
| Provider/governor/churn failure, IG failure observed by action `waitAny` | [Diffusion] 930–950 | [R/AsyncScope](Rules/AsyncScope.agda), `beginUnwind`, then [PeerSupervision](PeerSupervision.agda); abstract cause/receipt contract in [Supervision](Supervision.md#current-executable-integration), not provider bodies. | **contracted** | G2, G3 |
| Server action exit: normal test callback or production exception | [Server] 165–180; [Diffusion] 946–950 | [ServerAdmission](ServerAdmission.agda), `returnAction` → result/winner → scope unwind; [Negative/ServerPeers](Negative/ServerPeers.agda), `Protocols.StartTrace.ScopedCM.Completion`. [SI4 reinterpretation](SourceLedger.md#audit-finding-the-modelled-server-exit-has-no-production-instance) merges error tracing and omits the final rethrow value. | **implemented** | G2 |
| IG wins first | [IG] 194–235; [Server] 165–175 | [ServerIGExit](ServerIGExit.agda), `fail`; [ServerAdmission](ServerAdmission.agda), `failIGBody`, `igWins`; [Negative/ServerIGFirst](Negative/ServerIGFirst.agda). | **implemented** | G2, G3 |
| Accept loop wins: fatal accept; getLocalAddr/accept-trace error closes accepted socket | [Server] 218–252 | [ServerAdmission](ServerAdmission.agda), `acceptFails`, `closeListener`; [Negative/ServerPeers](Negative/ServerPeers.agda), `Interleaving.initialized-accept-failure`. Socket before handoff is outside the heap; both triggers share this observed step. | **implemented** | G2, G3 |
| External cancellation of Server owner | [Server] 165–175; [Diffusion] 281–296 | [ServerAdmission](ServerAdmission.agda), `interruptServer`; [ServerPeers](ServerPeers.agda), `peerOpen`/join guards; [Negative/ServerPeers](Negative/ServerPeers.agda), `Interleaving.initialized-interrupt`. | **implemented** | G2, G3 |
| `SERVER.RATE.READ` before accept | [Rate] 67–137; [Server] 211–215 | No accept-rate actor/read rule. Explicit timing/policy exclusion in [README limits](README.md) and [SI4 audit](SourceLedger.md#serverwith-and-the-accept-loop-serverhs-147254). Admission's later `countLimit` is a different read and is not its implementation. | **excluded** | G2 |
| `SERVER.RATE.WAIT`: soft/hard/minimum delays | [Rate] 99–137 | Same exclusion: no elapsed-time or rate guarantee; the hard-wait guard is also omitted, so this permits earlier handoffs. | **excluded** | G2 |
| `SERVER.ACCEPT`: successful accept | [Server] 211–238 | [ServerAdmission](ServerAdmission.agda), `acceptedFork`, takes an already accepted socket/key. [ServerAdmissionPrefixFixtures](Negative/ServerAdmissionPrefixFixtures.agda) and [Supervision increment 18](Supervision.md#eighteenth-increment-raw-admission-workers-and-owned-server-scope-return) state the transport boundary. | **contracted** | G2 |
| Aborted accept, ECONNABORTED delay/retry | [Server] 218–228 | No allocation/state change represented; explicitly omitted untimed retry/delay in [SI4 audit](SourceLedger.md#serverwith-and-the-accept-loop-serverhs-147254). | **excluded** | G2 |
| `SERVER.HANDOFF`: successful bare async, independent parent; worker result/close | [Server] 233–254 | [ServerAdmission](ServerAdmission.agda), `acceptedFork`, `workerReturned`, `workerClose`, `workerResult`; [Negative/ServerAdmission](Negative/ServerAdmission.agda), initialized two-handoff history. | **implemented** | G1, G2, G3 |
| Failure of admission `async` fork before `acceptedFork` | [Server] 239–252 | [ServerAdmission](ServerAdmission.agda), `forkFailure` → reserved acceptPending socket → `closeForkFailure` → `finishForkFailure`; [PrimitiveAdmissionFork](Negative/PrimitiveAdmissionFork.agda) covers initialized failure, replacement close error, no fabricated child and no pending-token reuse. | **implemented** | G1, G2 |
| General worker exception between include map take, handler fork and map publication | [Core] 801–880, 2373–2379; [Server] 249–250 | [ServerAdmission](ServerAdmission.agda), `workerException` → `workerRestore` → separate socket close/result; [PrimitiveIncludeRestoration](Negative/PrimitiveIncludeRestoration.agda) restores saved map only, retaining committed heap/promise/physical child. [Increment 80](Supervision.md#eightieth-increment-g1-primitive-runtime-closure) supersedes increment 78's missing-rule snapshot; lazy-reference forcing remains an evaluation abstraction. | **implemented** | G1, G2 |
| Multiple listeners and cross-loop cancellation | [Server] 147–180 | One-listener profile; `withAsyncAll` order for several loops excluded. | **excluded** | G2, G3 |
| Stopped/error diagnostic tracer failure and final rethrow observation | [Server] 174–180 | [SI4 trace/exit contract](SourceLedger.md#audit-finding-the-modelled-server-exit-has-no-production-instance): observed successful trace; merged `TrServerError`; rethrow not model state. | **contracted** | G2, G4 |
| CM outer finally: locked snapshot, per-handler throwTo, all results | [Core] 523–550 | [R/CMShutdown](Rules/CMShutdown.agda), `captureSnapshot`, request/acknowledge/finish; [Properties/ServerShutdownCoordinator](Properties/ServerShutdownCoordinator.agda) and [Negative/ServerPeersOrigins](Negative/ServerPeersOrigins.agda). Exceptional entry uses the same body. | **implemented** | G2, G3 |
| Late raw worker/handler after the CM snapshot | [Server] 239–254; [Core] 523–550, 780–880 | [ServerAdmission](ServerAdmission.agda), no global freeze; [Negative/ServerLateAdmission](Negative/ServerLateAdmission.agda) initializes then forks after return. This fixture is at the admission layer, not an outer-composition late-fork proof. | **implemented** | G2, G3, G5 |
| Initiator-only diffusion and node-to-client Server | [Diffusion] 399–466, 888–915 | Separate modes/CM instances excluded from this combined responder profile; shared outbound kernels may still support initiator-only mode. | **excluded** | G2 |
| Counters loop / local diffusion race bodies | [Diffusion] 281–296 | Outside selected actors; failure is an abstract external-unwind cause above, not an all-worker claim. | **excluded** | G2 |
| Pool-relays scope presence, cancellation and join | [Diffusion] 699–722, 888, 946–950 | [R/PoolRelays](Rules/PoolRelays.agda), `initial`, `requestCancel`, `join`, `finish`; [ServerPeersRelays](ServerPeersRelays.agda); [Properties/PoolRelays](Properties/PoolRelays.agda), [Negative/PoolRelays](Negative/PoolRelays.agda). | **implemented** | G2 |
| Pool-relays DNS/semaphore/ledger body; intervening socket scope closes | [Diffusion] 699–722, 860–950 | Body and socket-close interval outside the relays wrapper; no claim that all diffusion resources are modeled. Its owner cancel/join is included in the preceding row. | **excluded** | G2 |

### CM operation families

| Family / selected branches | Pinned source | Model rule and evidence / contract | Status | Gates |
| --- | --- | --- | --- | --- |
| `CM.INCLUDE`: absent/reserved/unnegotiated/terminal entry; hard limit; forbidden/fork failure | [Core] 780–896 | [R/Server](Rules/Server.agda), `chooseEntry`, `fork`, restoration/close; [Negative/ServerAdmissionPrefix](Negative/ServerAdmissionPrefix.agda), initialized prefix exits. Failed-fork lazy-reference forcing is not certified. | **implemented** | G1, G2 |
| `CM.INCLUDE.RESULT`: success, error/query and changed entry | [Core] 897–1101 | [R/Handshake](Rules/Handshake.agda), read/commit/count/notify/return; [Scenarios/Handshake](Scenarios/Handshake.agda), [Negative/StaleHandshake](Negative/StaleHandshake.agda), [ServerAdmissionPrefix](Negative/ServerAdmissionPrefix.agda). | **implemented** | G2, G3 |
| `CM.ACQUIRE.SELECT`: reservation preference, eligible entry, retry/error | [Core] 1273–1391 | [R/OutboundAcquire](Rules/OutboundAcquire.agda), `select`; [Negative/Outbound](Negative/Outbound.agda), reservation/replaced-entry controls. Member admissibility implemented; concrete selection remains the separate seed contract above. | **implemented** | G2, G3 |
| `CM.ACQUIRE.CONNECT`: reserve/open/configure/bind/connect/local-key/fork; failure/query | [Core] 1392–1832 | [R/OutboundAcquire](Rules/OutboundAcquire.agda), socket/fork/result PCs; [CSP/OutboundAdmission](CSP/OutboundAdmission.agda), [CSP/OutboundOpenFailure](CSP/OutboundOpenFailure.agda), [Negative/Outbound](Negative/Outbound.agda). | **implemented** | G2, G5 |
| `CM.ACQUIRE.REUSE`: duplex reuse, captured inbound wait, forbidden uni and terminal cases | [Core] 1284–1391, 1558–1769 | [R/OutboundCases](Rules/OutboundCases.agda), [R/OutboundAcquire](Rules/OutboundAcquire.agda); [Negative/Outbound](Negative/Outbound.agda); initialized reuse in [Negative/ServerPeers](Negative/ServerPeers.agda), `Protocols.initialized-to-start`. Not every reuse branch is initialized. | **implemented** | G2, G3 |
| `CM.RELEASE.IN`: missing/unsupported, KeepTr/CommitTr, inline/deferred assertions, cancel | [Core] 1107–1260 | [R/InboundRelease](Rules/InboundRelease.agda), transaction/counters/delivery/return; [CSP/InboundRelease](CSP/InboundRelease.agda), [InboundRelease branch table](InboundRelease.md#branch-mapping). [MuxHandlerExit](MuxHandlerExit.agda) couples inbound mux/TIME_WAIT/finished receipt to the captured call; [InboundCleanLifecycle](Negative/InboundCleanLifecycle.agda) extends the initialized normal-exit run through cleanup/result (increment 82; local acceptance in progress). | **implemented** | G2 |
| `CM.RELEASE.OUT`: unsupported/forbidden/no-op, idle timer/change, capacity/pruning, cancellation | [Core] 1834–2060 | [R/OutboundRelease](Rules/OutboundRelease.agda); [CSP/OutboundReleaseScenarios](CSP/OutboundReleaseScenarios.agda), [Negative/Outbound](Negative/Outbound.agda). Timeout selection and later write remain separate. | **implemented** | G2, G3, G5 |
| `CM.REMOTE.WARM`: capacity/no-capacity, supported/unsupported/assertion | [Core] 2061–2252 | [R/RemoteState](Rules/RemoteState.agda), promotion transaction; [CSP/RemoteState](CSP/RemoteState.agda), [CSP/Pruning](CSP/Pruning.agda); [RemoteState table](RemoteState.md#mapping). | **implemented** | G2 |
| `CM.REMOTE.COLD`: supported/unchanged/terminal/unknown, assertion and counter order | [Core] 2253–2355 | Same rule module, demotion; [CSP/RemoteState](CSP/RemoteState.agda), separate idle timer/publication. | **implemented** | G2 |
| `CM.PRUNE`: candidate types, unknown-local omission, score/type/key order, self/survivor | [Core] 720–777; [Policies] 284–306 | [R/Pruning](Rules/Pruning.agda), scored transaction and ordered captured deliveries; [CSP/Pruning](CSP/Pruning.agda), [Negative/Outbound](Negative/Outbound.agda), surviving-self control. Score realizability is contracted above. | **implemented** | G2, G3 |
| `HANDLER.PUBLISH/RUN`: handshake receipt/error publication, success allocation/publication/start | [Handler] 307–339, 379–518 | [HandlerSupervision](HandlerSupervision.agda), caught result/Async result; [MuxHandlerSupervision](MuxHandlerSupervision.agda), `negotiate`, `allocateHandle`, `publishSuccess`; [Negative/MuxPublicationInbound](Negative/MuxPublicationInbound.agda), [Negative/HandlerSupervision](Negative/HandlerSupervision.agda). Actual wire negotiation remains input. | **implemented** | G1, G2 |
| `HANDLER.CLEANUP`: map lease, captured worker/entry, close failure/restore, Terminated vs Terminating/TIME_WAIT | [Core] 570–719 | [R/Cleanup](Rules/Cleanup.agda), close/map publish/timewait/final STM; [Scenarios/Cleanup](Scenarios/Cleanup.agda), [Negative/CleanupAtomicity](Negative/CleanupAtomicity.agda), [Negative/ServerPeersOrigins](Negative/ServerPeersOrigins.agda). | **implemented** | G1, G2, G3 |
| Release/CM shutdown receipts at live mux, finished target or unmasked TIME_WAIT (increments 63–67) | [Core] 523–550, 666–709, 1254, 2032 | [MuxHandlerExit](MuxHandlerExit.agda), `acknowledgeFinished`, `deliverShutdownMux/TimeWait`, `deliverReleaseMux/TimeWait`; [Negative/ServerPeersOrigins](Negative/ServerPeersOrigins.agda), [Negative/ServerPeersReleaseTimeWait](Negative/ServerPeersReleaseTimeWait.agda). Receipt is not join. | **implemented** | G1, G2, G3 |

### IG families

| Family / selected branches | Pinned source | Model rule and evidence / contract | Status | Gates |
| --- | --- | --- | --- | --- |
| `IG.BATCH`: maturity, first idle commit, queue, inactivity; captured time/order | [IG] 242–278, 796–804, 945–955 | [R/IGBatch](Rules/IGBatch.agda), `selectBatch`; [R/IGRegistration](Rules/IGRegistration.agda), derived candidates; [Scenarios/IGBatch](Scenarios/IGBatch.agda), [CSP/IGRuntime](CSP/IGRuntime.agda). | **implemented** | G1, G2 |
| `IG.NEW`: duplicate/new, partial startup success/failure, registered state | [IG] 280–398; [Mux] 966–1069 | [R/IGRegistration](Rules/IGRegistration.agda), `runResponders`; [CSP/IGRegistration](CSP/IGRegistration.agda), [CSP/IGRuntime](CSP/IGRuntime.agda). Installation's source contract is in [HandlerOrigin](HandlerOrigin.md). | **implemented** | G2 |
| `IG.FINISHED`: absent key or capture current mux, wait then remove | [IG] 400–415 | Same runtime, `pollStopped`; [CSP/RegistryProducer](CSP/RegistryProducer.agda), [Negative/RegistryProducer](Negative/RegistryProducer.agda). Event key is not old mux identity. | **implemented** | G2, G3 |
| `IG.PROTOCOL.END`: clean/error, registration and restart | [IG] 417–461 | Same runtime, `restart`; [CSP/IGRuntime](CSP/IGRuntime.agda). Selected eager/independent on-demand bundles only. | **implemented** | G2 |
| `IG.REMOTE`: awake/idle/hot/warm, maturity/inactivity | [IG] 463–528, 574–612 | Same runtime and [R/RemoteState](Rules/RemoteState.agda); [CSP/RemoteState](CSP/RemoteState.agda), [CSP/IGRuntime](CSP/IGRuntime.agda). | **implemented** | G2 |
| `IG.COMMIT`: caller-run release, CommitTr/KeepTr/unsupported | [IG] 529–572; [Core] 1107–1260 | [R/IGRegistration](Rules/IGRegistration.agda), `inCM`, return continuation; [CSP/InboundRelease](CSP/InboundRelease.agda). No independent CM worker. | **implemented** | G2 |
| `IG.PUBLISH`: captured decision, separate masked commit | [IG] 280–379, 574–598 | Same runtime, `commitDecision`; [CSP/IGRegistration](CSP/IGRegistration.agda), [CSP/InboundRelease](CSP/InboundRelease.agda), [CSP/RemoteState](CSP/RemoteState.agda) specialize new/remove/remote decisions. | **implemented** | G2, G3 |
| `IG.TRACER`: active sample, readiness/descriptor order, signed counters and atomic bursts | [IG] 625–735 | [R/MuxRuntime](Rules/MuxRuntime.agda), [R/TracerReadiness](Rules/TracerReadiness.agda), sample/commit; [Negative/TracerReadinessIntegration](Negative/TracerReadinessIntegration.agda), [CSP/IGRuntime](CSP/IGRuntime.agda). | **implemented** | G1, G2, G3 |
| `IG.EXIT`: own failure/cancellation, retire pending call, deactivate/drain/trace/rethrow/result | [IG] 194–235 | [ServerIGExit](ServerIGExit.agda), `receive`, `fail`, `captureSnapshot`, final trace actions; [Negative/ServerIGExit](Negative/ServerIGExit.agda), [Negative/ServerIGFirst](Negative/ServerIGFirst.agda). A sampled producer may enqueue after drain. | **implemented** | G2, G3 |

### OG and peer actions

| Family / selected branches | Pinned source | Model rule and evidence / contract | Status | Gates |
| --- | --- | --- | --- | --- |
| `OG.DECIDE`: ordered monitor/completion/targets/policy/wakeup, captured decision | [Governor] 588–729; [Monitor] 55–112 | [Subsystem](Subsystem.agda), selection/apply PCs; [CSP/GovernorLifecycle](CSP/GovernorLifecycle.agda), [Negative/TargetInputs](Negative/TargetInputs.agda). Ordinary eligible-peer choices only. | **implemented** | G2, G3 |
| `OG.LAUNCH`: public view/counters/traces, each fork then register | [Governor] 588–641 | [Subsystem](Subsystem.agda), `publishPublicState`, `forkJob`, `registerJob`; [Negative/Subsystem](Negative/Subsystem.agda), child-before-registration control. | **implemented** | G1, G2, G3 |
| `OG.COMPLETE`: FIFO pop and current-state timed completion/assertion | [Monitor] 100–112; [Governor] 609–616 | [Subsystem](Subsystem.agda), completion selection/application; [Properties/ServerPeersCompletions](Properties/ServerPeersCompletions.agda), [Negative/Subsystem](Negative/Subsystem.agda). | **implemented** | G2, G3 |
| `OG.ESTABLISH/CLOSE`: ordinary quota/eligibility/in-progress, failures/backoff/forget | [Established] 241–341, 470–643, 670–779, 884–1013; [Known] 452–507 | [R/OutboundGovernor](Rules/OutboundGovernor.agda), `complete`; [CSP/GovernorLifecycle](CSP/GovernorLifecycle.agda), [CSP/GovernorFailureLimit](CSP/GovernorFailureLimit.agda), [Negative/GovernorFailureLimit](Negative/GovernorFailureLimit.agda). | **implemented** | G2, G5 |
| `OG.ACTIVATE/DEMOTE`: ordinary guards, late/aborted/timeout completion | [Active] 326–626, 862–1086 | Same governor rules, mark/complete; [Negative/OutboundGovernor](Negative/OutboundGovernor.agda), [CSP/GovernorLifecycle](CSP/GovernorLifecycle.agda). | **implemented** | G2, G3 |
| `ACTION.ESTABLISH`: actual acquire, warm/established starts, results, Warm/monitor fork | [Actions] 777–903, 1149–1242 | [R/PeerJobs](Rules/PeerJobs.agda), establishment PCs; [R/PeerActions](Rules/PeerActions.agda), start/publish; [Negative/ServerPeers](Negative/ServerPeers.agda), `Protocols`. Physical result cells are distinct from body/Async exit. | **implemented** | G2 |
| `ACTION.ACTIVATE`: controls, sequential hot starts, status/promotion time | [Actions] 951–984 | Same rules; [CSP/GovernorLifecycle](CSP/GovernorLifecycle.agda), [Negative/ServerPeers](Negative/ServerPeers.agda), initialized second activation. | **implemented** | G2, G3 |
| `ACTION.DEACTIVATE`: PeerWarm shortcut, all-hot clean/error, concurrent status, operation timeout | [Actions] 986–1046 | Same rules; [Properties/ServerPeersDeactivation](Properties/ServerPeersDeactivation.agda), `origin-success`; [Negative/OutboundGovernor](Negative/OutboundGovernor.agda). Timeout stop/Cooling does not finish physical cleanup. | **implemented** | G2 |
| `ACTION.CLOSE`: all-temperature terminate/results; success/error/timeout and real release | [Actions] 1048–1107 | Same rules and [R/OutboundRelease](Rules/OutboundRelease.agda); [Properties/ServerPeersClose](Properties/ServerPeersClose.agda), [Negative/ServerPeers](Negative/ServerPeers.agda), `Protocols.CloseOriginChecks`. | **implemented** | G2 |
| `PEER.MONITOR`: ordered first results, background demotion/close, CM Cold observation | [Actions] 640–775, 904–949; [Monitor] 114–320 | [R/PeerActions](Rules/PeerActions.agda), `first`; [PeerSupervision](PeerSupervision.agda) physical monitors; [Properties/ServerPeersMonitorJoins](Properties/ServerPeersMonitorJoins.agda), [Negative/ServerPeers](Negative/ServerPeers.agda). | **implemented** | G2, G3 |
| `OG.DEMOTE.ERROR`: separate Cold-wait timeout and completion membership | [Active] 963–1086 | [R/PeerJobs](Rules/PeerJobs.agda), demotion-error wait/timeout; [Negative/OutboundGovernor](Negative/OutboundGovernor.agda). Distinct from PSA operation timeout and handler TIME_WAIT. | **implemented** | G2 |
| Ordinary peer/node exception policy, blocking main-thread delivery and local rethrow | [Actions] 784–805; [Diffusion] 337–373, 676–698 | [R/ProductionPolicy](Rules/ProductionPolicy.agda), immutable exception-class projection; [Outbound policy contract](Outbound.md#exception-policy-and-node-delivery). `completeShutdown` remains a standalone external boundary; SI5 outer theorems have separate scope. | **contracted** | G2, G5 |

### Protocol contracts still required

| Family / selected branches | Pinned source | Model rule and evidence / contract | Status | Gates |
| --- | --- | --- | --- | --- |
| `PROTOCOL.CONTRACT`: generic control/start/return/error/result lifecycle | [Actions] 361–435, 1149–1242; [Mux] 491–572 | [R/PeerActions](Rules/PeerActions.agda), [MuxProtocolJobs](MuxProtocolJobs.agda) and [Supervision increment 23](Supervision.md#twenty-third-increment-peer-initiator-starts-and-physical-results): body return, selected control behavior and supplied outcomes stand in for protocol execution. | **contracted** | G2 |
| ChainSync control reads, ChainDB waits and bracket cleanup | [Bundle] 1438–1524; [ProtocolContracts sources](ProtocolContracts.md#chainsync) | Reviewed per-direction wait/control/result/mask and cleanup contract; executable candidate/start/drain/resource guards in [ProtocolContracts](ProtocolContracts.agda), enabled/refusal [controls](Negative/ProtocolContracts.agda); conditional typed job adapter [ProtocolContractJobs](ProtocolContractJobs.agda). Payload/ChainDB readiness and complete inner unwinds are explicit observations. | **contracted** | G2 |
| BlockFetch work/control waits and client cleanup | [Bundle] 1526–1574; [Registry] 75–207; [contract sources](ProtocolContracts.md#blockfetch) | Reviewed initiator/responder lifecycle; work/control priority, outstanding drain and cleanup obligations; executable waits/cleanup/error/cancellation guards and [controls](Negative/ProtocolContracts.agda). Actual STM/work/driver/registry return observations remain contracted; no initialized full-bundle run. | **contracted** | G2 |
| ChainSync/BlockFetch registration synchronization | [Registry] 75–207, 217–257 | [Reviewed shared contract](ProtocolContracts.md#shared-registration-synchronization): context/KeepAlive/absence prerequisites, start-before-candidate, done-before-fetch-removal, acquisition failure and cleanup cancellation. [Kernel](ProtocolContracts.agda) implements captured-pair ordering; multi-incarnation registry and KeepAlive bodies remain explicit contracts. Responders have private registries. | **contracted** | G2 |
| TxSubmission2 mempool/work/control/result lifecycle | [Bundle] 539–578, 1576–1635; [reviewed sources](ProtocolContracts.md#txsubmission2) | Per-direction blocking-request/control priority, mempool/driver waits, V1/V2 selection, pipelined zero-depth Done and V2 scrub/retire-before-tier cleanup contract. [Kernel](ProtocolContracts2.agda), [enabled/refusal controls](Negative/ProtocolContracts2.agda), [typed 4/8 adapter](ProtocolContractJobs2.agda). Real work, registry identity, masking and readiness remain certified inputs; no configured initialized bundle witness. | **contracted** | G2 |
| KeepAlive established-group control/wait/result lifecycle | [Bundle] 1727–1773; [reviewed sources](ProtocolContracts.md#keepalive) | Initiator/responder contract: first ping before control, response/delay priority, dq registration, uninterruptible captured-fetch cancel/done before removal, independent responder result. [Kernel and controls](Negative/ProtocolContracts2.agda); [job controls](Negative/ProtocolContractJobs2.agda). Shared registry coupling is contracted; existing initialized lifecycle witnesses still have empty established groups. | **contracted** | G2 |
| LeiosNotify pending/pipelined work, control checks and termination | [Bundle] 1866–1909; [Notify] 529–723 | [Reviewed per-direction contract](ProtocolContracts.md#leiosnotify): forecast/control and arrived gating, Quit-before-drain-before-Done, responder Quit-first sender flush and linked-pump finalizer/join. [Kernel](ProtocolContracts3.agda), [enabled/refusal controls](Negative/ProtocolContracts3.agda) and [typed 18/19 adapter](ProtocolContractJobs3.agda). Actual STM/depth/credit/driver/pump operations remain certified inputs. | **contracted** | G2 |
| LeiosFetch pending/pipelined work, control checks and termination | [Bundle] 1911–1961; [Fetch] 587–687 | [Reviewed per-direction contract](ProtocolContracts.md#leiosfetch): stop-first command selection, nonzero-depth collection before recheck, drain-before-Done, nested writer/reader cleanup. [Kernel and controls](Negative/ProtocolContracts3.agda), [job controls](Negative/ProtocolContractJobs3.agda). Actual work/depth/DB operations and projection to existing writer waits remain contracted; no full-bundle initialized run. | **contracted** | G2 |
| Shared Leios peer-resource allocation/removal/outstanding cleanup | [Bundle] 1836–1864 | [Reviewed shared contract](ProtocolContracts.md#shared-leios-peer-resources): CS/Notify/Fetch initiators get-or-create, no refcount, first exit deletes then refunds under outstanding MVar; sibling cleanup is idempotent and stragglers may reallocate. [Kernel/controls](Negative/ProtocolContracts3.agda) retain cleanup-failure residue. Actual cell identity, accounting and decision-loop lock discipline remain contracts; responders have separate resources. | **contracted** | G2 |
| Peras, PeerSharing, discovery/local-root/big-ledger branches | [Bundle] 1637–1725, 1775–1834, 1963–2100; [Governor] 671–729 | Explicit ordinary-peer/application configuration exclusion in [DESIGN §2](DESIGN.md#2-first-scenario-and-abstraction-manifest), [Outbound](Outbound.md). These protocols must be disabled in a source instantiation. | **excluded** | G2, G3 |

### Later handler, mux and migration branches

These expand `HANDLER.PUBLISH/RUN`, `MUX.STOP/STOPPED`, `JOB.*` and the ledger's M3/M4 tables. The DB and fine-grained physical lifecycle rows were not separately indexed in the original family list.

| Family / selected branches | Pinned source | Model rule and evidence / contract | Status | Gates |
| --- | --- | --- | --- | --- |
| Plain/scheduled mux allocation, pre-publication failure sites | [Handler] 307–339, 428–436, 498–510 | [MuxHandlerSupervision](MuxHandlerSupervision.agda), `configureMux`; [MuxPublicationUnwind](MuxPublicationUnwind.agda), `observeFailure`; [Negative/MuxConfiguredHandler](Negative/MuxConfiguredHandler.agda), [Negative/MuxPublicationUnwind](Negative/MuxPublicationUnwind.agda). No invented handshake error after the handshake catch. | **implemented** | G2 |
| Egress rule wait, atomic rank/sink install, rank trace; sync/async failure | [Handler] 329–335 | Same modules, three `egressSetup` stages and failure sites; [Negative/MuxEgressSetupUnwind](Negative/MuxEgressSetupUnwind.agda). Rank values/order are abstract below. | **implemented** | G1, G2 |
| Pure `withCounters` field attachment | [Handler] 337–339; [Mux] 209–211 | No separate transition/exception: pure record update. Actual counter registration/retirement is in the next row. | **excluded** | G2 |
| Configured 2/3/4-worker startup, shared pool, counter registration/retirement | [Mux] 399–483; [Counters] 221–239 | [R/MuxStartup](Rules/MuxStartup.agda), `forkConfigured`/`registerConfigured`; [R/IGRegistration](Rules/IGRegistration.agda), `registerCells`/`retireCells`; [Negative/MuxStartup](Negative/MuxStartup.agda), [Negative/MuxConfiguredCounters](Negative/MuxConfiguredCounters.agda), [Negative/MuxConfiguredWholeClose](Negative/MuxConfiguredWholeClose.agda). | **implemented** | G1, G2 |
| Physical protocol generations, child Wanton entry, typed FIFO results and restart | [Mux] 491–572, 628–646, 704–833; [JobPool] 113–177 | [MuxProtocolJobs](MuxProtocolJobs.agda), fork/`enterProtocolBody`/publish/remove; [MuxResultMonitor](MuxResultMonitor.agda), `consume`; [Negative/MuxProtocolJobs](Negative/MuxProtocolJobs.agda), [Negative/ServerPeers](Negative/ServerPeers.agda), `Protocols`. | **implemented** | G1, G2, G3 |
| Graceful group cancel, successful drain vs timeout2, whole-pool close | [Mux] 411–434, 763–778; [JobPool] 105–109, 213–225 | [MuxGroupShutdown](MuxGroupShutdown.agda), group/whole close and stopped tracer; [Negative/MuxStoppedTracer](Negative/MuxStoppedTracer.agda), [Negative/MuxConfiguredWholeClose](Negative/MuxConfiguredWholeClose.agda). Stopped need not imply drained. | **implemented** | G2 |
| Buffer acquisition/release and possible replacement exception | [Handler] 437–439, 511–513 | [MuxHandlerExit](MuxHandlerExit.agda), `observeBufferReturn`, `observeBufferException`; [Supervision increment 8](Supervision.md#si4-eighth-increment-buffer-scope-captured-cm-finally-and-parent-results). Provider return/throw is an input; provider body is not modeled. | **contracted** | G2 |
| Synchronous handler policy, trace return, node delivery | [Handler] 342–373 | [MuxHandlerExit](MuxHandlerExit.agda), `choosePolicy`, `observeErrorTrace`, `observeNodeDelivery`; [HandlerOutcomes](HandlerOutcomes.md#rules-and-boundaries). Configurable policy and tracer/delivery inputs stand in; no fixed deployment policy is reconstructed. | **contracted** | G2 |
| Post-publication setup faults, partial pool startup and sync tracer unwind | [Handler] 437–439, 511–513; [Mux] 398–434, 704–778 | [MuxStartupUnwind](MuxStartupUnwind.agda), site/route-sensitive unwind; [Negative/MuxStartupUnwindBranches](Negative/MuxStartupUnwindBranches.agda), [Negative/MuxStartupUnwindSites](Negative/MuxStartupUnwindSites.agda). No pool close before pool entry. | **implemented** | G1, G2 |
| Async callback interruption and post-close async catch replacement | [Mux] 428–434, 655–664, 704–778 | [MuxExitCancellation](MuxExitCancellation.agda), [MuxCatchUnwind](MuxCatchUnwind.agda), selected blocking sites; [Negative/MuxCallbackCancellation](Negative/MuxCallbackCancellation.agda), [Negative/MuxCatchUnwind](Negative/MuxCatchUnwind.agda). General mask semantics remain contracted above. | **implemented** | G1, G2 |
| Bearer DeltaQ callback return/sync/async failure | [Mux] 655–664 | [MuxDeltaQ](MuxDeltaQ.agda), ticketed invocation/outcome; [Negative/MuxDeltaQ](Negative/MuxDeltaQ.agda). Outcome availability is observed, not guaranteed. | **implemented** | G2 |
| Initiator completion callback ignored by IG: caller trace return/sync/async failure | [Mux] 655–664; [IG] 736–748 | [MuxDeltaQ](MuxDeltaQ.agda), `beginInitiatorTrace`, `observeInitiatorReturn`, `observeInitiatorException`; [Negative/MuxInitiatorTraceCM](Negative/MuxInitiatorTraceCM.agda). | **implemented** | G2, G3 |
| Leios collector synchronous DB waits: queued, completed, failed/sealed; cancellation retains write | [Logic] 1006–1007, 1455 | [R/IGRegistration](Rules/IGRegistration.agda), `stepDb`; [MuxProtocolJobs](MuxProtocolJobs.agda), `submitDbWrite`, `awaitDbWrite`, `writerComplete`, `writerSeal`; [Negative/MuxLeiosDbWait](Negative/MuxLeiosDbWait.agda), [SourceReplay/LeiosDbWaits](SourceReplay/LeiosDbWaits.hs). Writer completion/error is supplied; replay is SQLite/serial-blockio only. | **implemented** | G2, G5 |
| Demand append/take, batch memberships, held/sent accounting and completion guards | [Mux] 528–553, 763–776, 918–941; [Egress] 243–247, 298–309, 340–402 | [R/MuxEgress](Rules/MuxEgress.agda) via shared [R/MuxRuntime](Rules/MuxRuntime.agda); [Negative/MuxEgressReadiness](Negative/MuxEgressReadiness.agda), [Negative/MuxConfiguredTraffic](Negative/MuxConfiguredTraffic.agda). Wanton empty is not successful send. | **implemented** | G1, G2 |
| Unscheduled/Direct/Slice/Scheduled modes; gate, fast/queued grant, arm/disarm, cancellation cleanup | [Mux] 442–483; [Egress] 263–333; [Bucket] 674–888, 1070–1088 | [R/MuxEgress](Rules/MuxEgress.agda), `modeOf`, `openGate`, `grantFast`, `queueRequest`, `armTimer`, `grantQueued`, `disarmTimer`, `writeFailed`; [Negative/MuxEgressScheduling](Negative/MuxEgressScheduling.agda). Granted charges persist on cancellation. | **implemented** | G1, G2, G3 |
| Shared scheduled write lock, blocking write failure, masked post-return accounting/Direct credit | [Mux] 455–458; [Egress] 298–309; [Bucket] 608–621 | Same rules, `takeLock`, `returnWrite`, `writeAccount`; [Negative/MuxEgress](Negative/MuxEgress.agda), [Negative/MuxConfiguredTraffic](Negative/MuxConfiguredTraffic.agda). No extra async gap between return and accounting. | **implemented** | G1, G2 |
| Token availability, rank/ticket/floor choice and refresh/standing reads | [Bucket] 674–888, 1070–1088; [Diffusion] 519–545 | [M4a/M4b contract](SourceLedger.md#m4a-lane-waits-and-shared-buckets-network-2f1c154), [MigrationProfile](MigrationProfile.md#acceptance-and-later-gaps): abstract grant order/tokens; no `standingOf` read state; timer refresh is now explicit in [PrimitiveGrantRefresh](Negative/PrimitiveGrantRefresh.agda). No scheduling-order/fairness claim. | **contracted** | G2, G3 |
| Egress interval/burst statistics, detector, rotation and gate-timeout counter | [Egress] 263–333; [Bucket] 190–239, 356–371, 535–563, 649–888 | Excluded policy observations in the M4a ledger; they do not supply progress or timeout guarantees. | **excluded** | G2 |
| Active tenure insert/restrict/assert/publication | [Active] 594–595, 1041–1042, 1079–1080; [Monitor] 234–235; [Governor] 591; [GTypes] 883–890, 1399 | [R/OutboundGovernor](Rules/OutboundGovernor.agda), `complete`/`applyMonitor`; [Subsystem](Subsystem.agda), `publishPublicState`; [Properties/ActiveTenure](Properties/ActiveTenure.agda), `Tenure`, `Coordinator.tenure-runs`; [Negative/OutboundGovernor](Negative/OutboundGovernor.agda). | **implemented** | G2, G3 |
| Local-root public addresses/provider restart and PeerShare failure backoff | [GTypes] 883–890; [LocalRoots] 62–260; [GKnown] 250–410 | No local roots or peer sharing; M4b ordinary-profile exclusion. Public whole-state copying over-approximates the three source public fields. | **excluded** | G2 |
| StartOnDemandAny grouped readiness | [Mux] 745–761, 797–802 | [IGRegistration profile](IGRegistration.md#profile-and-remaining-abstractions) excludes this bundle; `installHandle` refuses it. Eager and independent on-demand remain supported. Increment 91 confirms that this exclusion blocks the full source KeepAlive profile, including allocation before initiators can start eagerly. | **excluded** | G2 |

### Later design variants and proof-only additions

| Family / selected branches | Pinned source | Model rule and evidence / contract | Status | Gates |
| --- | --- | --- | --- | --- |
| Owned-only CM callers (increment 77) | Comparison: [Actions] 777–1107; [Core] 1264–2060 | [Variants/OwnedCallers](Variants/OwnedCallers.agda) restricts foreign begin actions; [Negative/OwnedCallersFixture](Negative/OwnedCallersFixture.agda). Excluded from the unrestricted source profile; it is a separately named design restriction. | **excluded** | G2, G3 |
| Server-owned worker joins and historical handler sweep (increment 78) | Comparison: [Server] 239–254; [Core] 523–550, 652–713 | [Variants/ServerOwnedWorkers](Variants/ServerOwnedWorkers.agda), [Variants/ServerOwnedHandlers](Variants/ServerOwnedHandlers.agda); [Negative/ServerOwnedHandlersFixture](Negative/ServerOwnedHandlersFixture.agda). No corresponding ownership registry/join branch in pinned production. | **excluded** | G2, G3, G5 |

Increments 32–62 and 71–76/79 mainly add provenance, initializer restrictions, shutdown and validity theorems for the rows above, not new Haskell branches. In particular [LiveTrackerInitialized](Properties/LiveTrackerInitialized.agda), `Frontend.from-initial`, proves validity along `Runs` from successful `initialize (O.initial c₀) g`; it neither validates an unrestricted preloaded acquisition nor closes protocol contracts. [ServerShutdownComplete](Properties/ServerShutdownComplete.agda) and [ServerShutdownCoordinator](Properties/ServerShutdownCoordinator.agda) establish reached-endpoint safety for the one-listener outer run, not eventual shutdown or admission quiescence. Origin/capture/reference topics ([HandlerOrigin](HandlerOrigin.md), [HandlerCapture](HandlerCapture.md), [HandlerReferences](HandlerReferences.md), [HandlerUniqueOwnership](HandlerUniqueOwnership.md), [HandlerValidity](HandlerValidity.md), [AttributedOrigin](AttributedOrigin.md), [OriginRegistry](OriginRegistry.md), [OriginMonitor](OriginMonitor.md)) remain supporting model evidence, not independent source branches.

## Discrepancies and gate consequences

1. **Profile mismatch — blocks G0 and configured G2.** Increment 91 supplies a checked two-ordinary-peer 2/2/1 initializer and exact descriptors, but the pinned KeepAlive `StartOnDemandAny` is rejected at installation, including after a 24-event initialized prefix. The seed-to-selection and numerical version instantiation remain absent. Reduced fixtures and replay seeds do not fill these gaps.
2. **Protocol lifecycle reviews — complete as contracts.** Batch 1 contracts ChainSync, BlockFetch and their shared registry ([increment 88](Supervision.md#eighty-eighth-increment-g0-chainsync-blockfetch-and-registry-contracts)); batch 2 contracts TxSubmission2 and KeepAlive ([increment 89](Supervision.md#eighty-ninth-increment-g0-txsubmission2-and-keepalive-contracts)); batch 3 contracts LeiosNotify, LeiosFetch and shared peer resources ([increment 90](Supervision.md#ninetieth-increment-g0-leios-protocol-and-shared-resource-contracts)). No missing matrix rows remain; configuration/selection reconciliation and full configured initialized coverage remain open. `SERVER.RATE.READ/WAIT` have no model counterpart and are deliberately excluded here; admission `countLimit` cannot be cited as the rate read. Selected exception/promise/timer contracts remain abstract under the accepted G1 primitive matrix; contracted inputs still require source-backed instantiation for G2.
3. **Newer model coverage absent from, or stale in, the initial family cells — reconciled here.** Physical initiator/result/restart and typed mux lifecycle, DB waits, release TIME_WAIT receipts, late admission, SI5 and initializer validity have later evidence. `CM.INCLUDE.RESULT`'s “handler execution pending,” `IG.EXIT`'s “rethrow pending” and blanket missing accept/supervision statements describe earlier checkpoints. The SI4 table's “raw admission worker errors before handoff” conflates loop `accept/getLocalAddr/trace` failures (now the implemented `acceptFails` outcome) with the async-fork/worker-unwind edges now implemented in increment 80. M3's pool-body exclusion says “together with its owner,” although the owner cancel/join is implemented. These indexing discrepancies no longer block inventory review; they do not upgrade G2 witnesses. Ownership variants have no production counterparts and stay separate.
4. **Stale source anchors — corrected in this matrix.** Ledger `[mux-api]` 121–180 now misses `stopped` 214–221 and `stop` 326–328. `[handler]` 324–455 misses inbound publication 510 and the current catch/run boundaries; use 307–518, with publication 436/510. Old mux monitor/cleanup anchors 254–278, 424–618 and 554–570 must be replaced by pool/catch 411–434, monitor 605–833 and shutdown 763–778. Diffusion wiring 539–600 / 625–825 becomes 632–698 / 728–950; the peer policy is now 337–373. Demotion-job start is 963 rather than 961, ending at 1086. The consensus bundle reference had no range; current constructors are 1963–2100 and shared Leios bracket 1836–1864. Fetch's pipelined declaration begins at 587, not the old 591 anchor. These are source-location corrections, not new semantic claims. Unchanged Core/IG/Server/JobPool ranges retain the ledger's authority. No blocking unresolved anchor is being silently treated as implementation.

**G0 remains partly met.** The branch inventory has now been reviewed, with zero missing rows and explicit contracted inputs. Closing G0 still requires execution support for the reconciled LocalLifecycle bundle (KeepAlive grouped readiness is currently rejected), source seed/selection/version instantiation, and full configured-bundle initialized execution demonstrating that profile. All per-protocol/resource lifecycle reviews are now contracted by batches 1–3. Increment 80 records accepted primitive/worker regression; no new existing Agda dependency is changed by batch 3. Lazy-reference forcing is a separate evaluation abstraction. G2 still needs full configured-bundle initialized clean inbound/outbound coverage; the reduced clean, supervised negotiation-failure/cleanup and production-caller timeout witnesses have the accepted scopes specified in [GateAudit](GateAudit.md#g2--first-combined-lifecycle-partly-met). Existing reduced-profile hot demotion and initialized duplex reuse remain evidence within their stated scope.

[Core]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs
[CMTypes]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Types.hs
[Sync]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/monoidal-synchronisation/src/Data/Monoid/Synchronisation.hs
[JobPool]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/network-mux/src/Control/Concurrent/JobPool.hs
[Info]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor/InformationChannel.hs
[Mux]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/network-mux/src/Network/Mux.hs
[Handler]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionHandler.hs
[IG]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor.hs
[Server]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/Server.hs
[Rate]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/Server/RateLimiting.hs
[Diffusion]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/lib/Ouroboros/Network/Diffusion.hs
[Policies]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/lib/Ouroboros/Network/Diffusion/Policies.hs
[Governor]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/lib/Ouroboros/Network/PeerSelection/Governor.hs
[Monitor]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/lib/Ouroboros/Network/PeerSelection/Governor/Monitor.hs
[Established]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/lib/Ouroboros/Network/PeerSelection/Governor/EstablishedPeers.hs
[Active]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/lib/Ouroboros/Network/PeerSelection/Governor/ActivePeers.hs
[Known]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/lib/Ouroboros/Network/PeerSelection/State/KnownPeers.hs
[Actions]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerStateActions.hs
[Registry]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/lib/Ouroboros/Network/BlockFetch/ClientRegistry.hs
[Counters]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/network-mux/src/Network/Mux/Counters.hs
[Egress]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/network-mux/src/Network/Mux/Egress.hs
[Bucket]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/network-mux/src/Network/Mux/Egress/Bucket.hs
[Bundle]: https://github.com/IntersectMBO/ouroboros-consensus/blob/2e44d98a843168ba3b189e305820b79943ac7d1e/ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/Network/NodeToNode.hs
[Notify]: https://github.com/IntersectMBO/ouroboros-consensus/blob/2e44d98a843168ba3b189e305820b79943ac7d1e/ouroboros-consensus/src/ouroboros-consensus/LeiosDemoOnlyTestNotify.hs
[Fetch]: https://github.com/IntersectMBO/ouroboros-consensus/blob/2e44d98a843168ba3b189e305820b79943ac7d1e/ouroboros-consensus/src/ouroboros-consensus/LeiosDemoOnlyTestFetch.hs
[Logic]: https://github.com/IntersectMBO/ouroboros-consensus/blob/2e44d98a843168ba3b189e305820b79943ac7d1e/ouroboros-consensus/src/ouroboros-consensus/LeiosDemoLogic.hs

[GTypes]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/lib/Ouroboros/Network/PeerSelection/Governor/Types.hs
[LocalRoots]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/lib/Ouroboros/Network/PeerSelection/RootPeersDNS/LocalRootPeers.hs
[GKnown]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/lib/Ouroboros/Network/PeerSelection/Governor/KnownPeers.hs

[Wire]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/cardano-diffusion/lib/Cardano/Network/NodeToNode.hs
[WireVersion]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/cardano-diffusion/api/lib/Cardano/Network/NodeToNode/Version.hs
