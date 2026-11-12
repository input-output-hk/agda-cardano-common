# Supervision integration workstream

The objective is to connect cancellation and joining to actual CM effects and
the remaining diffusion scopes, then derive completed shutdown from the required
certificates. A completed governor job-pool close alone does not establish full
shutdown.

Source authority remains network pin
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`. This work does not change that pin,
resolve a new dependency version, or promote conditional snapshots into source
reachability witnesses. The detailed source evidence is in
[the pool audit](../review/connection-management-pool-supervision-source-audit-2026-10-27.md)
and [the peer-policy audit](../review/connection-management-a6-source-audit-2026-10-27.md).

## Current composed lifecycle certificates

**Confirmed finding — model scope, 4 November 2026.** Model commit `6878713`
contains increments 45–52, extending the initialized Server/peer frontend to
ordered monitor histories and actual CM handler-result waits. The upstream
network pin above is unchanged; this implementation commit is not a new source
revision or a Haskell refinement result.

**Accepted extensions, committed in `1e332cd`:** increments 53–57 add initialized inbound
and outbound handler resource origins, deriving primitive steps from actual
frontend events and retaining histories through publication and CM waits.
These extend implementation `6878713` and documentation `c1b631b`; see
[increment 53](#fifty-third-increment-initialized-handler-resource-origins),
[increment 54](#fifty-fourth-increment-primitive-admission-steps-from-frontend-events),
[increment 55](#fifty-fifth-increment-initialized-outbound-handler-resource-origins)
and [increment 56](#fifty-sixth-increment-outbound-origins-through-frontend-interference)
for their distinct inbound and pre-handshake outbound profiles. The broader
outbound constructor permits arbitrary enabled frontend histories before birth.
[Increment 57](#fifty-seventh-increment-initialized-physical-handler-birth-backing)
now discovers the physical fork from current handler membership and retains it
through CM acknowledgement, handler result publication and the final CM wait.
[Increment 58](#fifty-eighth-increment-acknowledged-collected-handler-birth-backing), committed in `3822a47`, supplies that physical membership from acknowledged
CM collection without a caller lookup. Committed in `db743c2`,
[increment 59](#fifty-ninth-increment-initializer-boundary-and-gap-aware-resource-histories) adds witnessed inbound resource histories with enabled allocation/selection/fork
gaps and checks the initializer boundary. Also committed in `db743c2`,
[increment 60](#sixtieth-increment-automatic-inbound-occurrence-reconstruction) reconstructs those inbound occurrences from an actual enabled fork,
without supplied continuation or resource certificates. Committed in `898a02d`,
[increment 61](#sixty-first-increment-collected-inbound-resource-origins) now connects discovered collected births to that
inbound evidence, returning actual outbound births as an explicit alternative.
Committed in `8636e88`, [increment 62](#sixty-second-increment-automatic-outbound-collected-resource-origins)
now derives the outbound branch under an explicit `O.initial core` profile;
its validation record below includes fresh full acceptance.
[Increment 63](#sixty-third-increment-initialized-finished-target-acknowledgement)
derives the finished-target receipt path and is committed in `8dd2452`; fresh full
acceptance is recorded below. [Increment 64](#sixty-fourth-increment-outbound-negotiated-mux-receipt-and-final-wait)
is committed in `eef9971`, with fresh full acceptance recorded below.
[Increment 65](#sixty-fifth-increment-initialized-time_wait-receipt-and-finalizer-routes)
is committed in `a54d4fd`, with fresh full acceptance recorded below.
[Increment 66](#sixty-sixth-increment-framed-mux-outbound-release-receipt-and-return)
is accepted and committed in `daf111d`.
[Increment 67](#sixty-seventh-increment-release-caller-delivery-at-time_wait)
adds the release caller's delivery into TIME_WAIT, with an initialized run
that retains the birth packet to the final CM wait. The
[source-baseline assessment](#next-task-source-baseline-audit) records changed
source contracts to reconcile before any repin or further proof expansion.

| Boundary | Derived evidence and premises |
| --- | --- |
| Terminal monitor handle | [Handle backing](Properties/ServerPeersMonitorBacking.agda) and [stage histories](Properties/ServerPeersMonitorStages.agda) use initialization, finite enabled execution and the terminal lookup. The return, removal and result-available phases yield successively longer prefixes of the physical exit/removal/Async-publication history. Normal/handled-error and cancelled-unwind causes remain distinct. |
| Join and closed snapshot | [Monitor joins](Properties/ServerPeersMonitorJoins.agda) derives prior lifecycle events from an actual inherited join. `initialized-closed` derives the empty cursor, exact snapshot/joined-list equality and histories in that order. [Join-order laws](Properties/JobPoolJoinOrder.agda) supply the snapshot decomposition. |
| Callback return and CM entry | `initialized-callback` uses the actual enabled return and its closure guard. `initialized-cm-entry-run` carries those certificates through enabled `ServerRuns` to `beginCM`; preservation follows from these steps. |
| Physical handler publication and CM wait | `physical-publication` and `physical-wait` lower actual guarded frontend events to physical operations. `initialized-cm-result-wait` derives the wait certificate, including the exact pre-wait result oracle, through the inherited Server suffix. Cancellation acknowledgement alone supplies no handler result. |
| Independent release receipt | [Release receipt properties](Properties/ServerPeersReleaseReceipt.agda) invert the actual live/available-result frontend events: captured caller frame, actual target operation, actual source acknowledgement, outer caller permission and unchanged CM coordinator. Separate canonical request/return steps use `FramedRuns.frameRelease`; finite initialized histories retain birth/resources through the final CM wait. |
| Cache-writing race suffix | `initialized-framed-result-wait` allows classified inherited/completion plans over Server actions. It preserves the governor pool, monitor pool and scope state; it permits peer-cache changes and does not assert whole-context equality. |
| Initialized handler resources | [Handler resource origins](Properties/ServerPeersHandlerResources.agda) derives primitive allocation/selection/fork steps from their actual frontend events, tying the occurrence to a fixed descriptor, allocated promise and stored entry/socket identities. It retains them through arbitrary enabled frontend suffixes; `AtPublication` and `AtWait` derive the inbound physical certificates. `OutboundOrigin` additionally derives resources from initialized acquisition prefixes; `OutboundFrontend.History` admits arbitrary enabled frontend prefixes/routes through the capture-only lift. The pre-handshake publication and guarded outer CM wait retain that descriptor, without claiming admission quiescence. |
| Inbound histories with enabled gaps | [HandlerOriginHistory](Properties/HandlerOriginHistory.agda) links actual allocation, positive selection and fork across two arbitrary enabled gaps, with explicit matching operational PCs. Entry presence follows from selection and [retention](Properties/HandlerOriginRetention.agda); existing resource retention handles post-birth suffixes. Empty gaps recover the old adjacent `Origin`. This constructor takes occurrence witnesses, not just collected membership. |
| Automatic inbound origins | [InboundOriginResources](Properties/InboundOriginResources.agda), `Frontend.initialize-origin`, takes successful initialization, the actual enabled prefix, a canonical/core inbound-fork label and its enabled step, and a suffix. It reconstructs allocation/positive selection with exact original labels and gaps, derives all matching PCs, the descriptor, historical promise allocation and stored resource facts. `extend-origin` copies the same packet through later runs. It is an inbound-fork result; the collected adapter below derives the physical occurrence itself. |
| Physical handler birth backing | [HandlerBirthBacking](Properties/HandlerBirthBacking.agda) derives an earlier actual inbound/outbound physical fork, its captured descriptor and the frontend prefix/event/suffix from successful initialization, an enabled finite frontend run and current physical-thread lookup. It takes no supplied birth or resource-validity certificate. |
| Acknowledged collected workers | [Membership](Properties/HandlerAuxFrontend.agda) and the thin [birth corollary](Properties/CollectedHandlerBirth.agda) derive a physical lookup and actual earlier fork from successful initialization, enabled finite frontend execution and current `Close.collected` membership. No supplied lookup or empty-CM premise; entry/snapshot targets and live resource ownership remain separate. |
| Collected inbound resource origins | [CollectedInboundOrigin](Properties/CollectedInboundOrigin.agda), `Frontend.initialize-origin`, takes successful initialization, enabled frontend execution and queried `Close.collected` membership. It returns the discovered descriptor/backing and either its automatic inbound allocation/selection/resource history or the actual outbound birth. The inbound branch preserves original labels and derives historical promise membership and stored handler/entry/socket facts; `extend-inbound` retains the same occurrence. No supplied physical lookup, PC or resource facts. |
| Profiled outbound collected resources | [CollectedOutboundOrigin](Properties/CollectedOutboundOrigin.agda), `Frontend.initialize-origin`, takes successful initialization from `O.initial core`, an enabled frontend run and queried collection membership. It returns the same discovered descriptor/backing with either the existing inbound origin or automatic outbound reservation/allocation history and stored resource facts. The actual labels and original event-list decomposition remain intact; `extend-outbound` copies the immutable birth packet. Fresh full acceptance is recorded in [increment 62](#sixty-second-increment-automatic-outbound-collected-resource-origins). |
| Finished-target receipt | [ServerPeersFinishedReceipt](Properties/ServerPeersFinishedReceipt.agda) derives the actual awaited entry/worker and physical Async-result branch from the enabled acknowledgement. [Profiled discovery](Properties/CollectedOutboundOrigin.agda), `initialize-finished`, additionally derives collected membership and the birth/resource sum from initialization, the original prefix and that event. Fresh full acceptance is recorded in [increment 63](#sixty-third-increment-initialized-finished-target-acknowledgement). |
| TIME_WAIT receipt and finalizer | [ServerPeersTimeWaitReceipt](Properties/ServerPeersTimeWaitReceipt.agda) derives the actual interrupted cleanup and acknowledged identity. `CollectedOutboundOrigin.initialize-timewait` derives membership and birth/resource discovery internally; [increment 65](#sixty-fifth-increment-initialized-time_wait-receipt-and-finalizer-routes) checks initialized elapsed/interrupted routes through both final CM waits. |

These are conditional finite-execution certificates, not guarantees that any
boundary will eventually be reached. The initialized examples and negative
controls use [ServerPeers.agda](Negative/ServerPeers.agda) and its dependent [origin endpoint](Negative/ServerPeersOrigins.agda), including
`CMResultLifecycleChecks` and `RaceLifecycleChecks`. Both race paths retain the
original monitor causes through CM's wait and Server return; raw admission
workers can remain incomplete. The current-clean path also refutes preservation
of the whole peer context while preserving the three certified components.

Detailed statements and historical validation are retained in
[increments 45–52](#forty-fifth-increment-initialized-terminal-monitor-handle-backing).
For increment 52, the generic module and full ServerPeers endpoint passed fresh
Agda 2.8.0 interaction loads on 4 November; the final strict batch
`agda ConnectionManagement/Negative/ServerPeers.agda +RTS -M11G -RTS`
passed cached. The [acceptance record](#fifty-second-increment-cache-aware-race-lifecycle-certificates)
preserves resource limits, the repaired initial diagnostic and transient log
identity `/tmp/cm-race-certificates-20261104/`. Documentation maintenance did
not rerun Agda, native replays or a term-level imported-assumption audit.

## Open questions and reconciled status

- **Confirmed finding:** the early ledger's statement that accepted-child and
  supervision behavior were unimplemented describes the initial admission
  slice. [ServerAdmission](ServerAdmission.agda) now supplies `acceptedFork` and
  selected raw-worker phases, and the certificates above cover selected
  initialized paths. This supersedes that blanket coverage statement; it does
  not supply the entire accept/getLocalAddr/failure loop.
- **Confirmed finding:** [the actual Server replay](SourceReplay/README.md#actual-server-admission-worker-lifetime-replay)
  observes blocked admission workers after `Server.with` returns in five
  injected-fault cases, with an early-handshake-error control. This is finite
  source execution at the pinned revision with synthetic listeners/bearers,
  not evidence of deployment frequency or universal shutdown failure.
- **Inference:** the source's discarded admission Async handles, that replay
  and the initialized model counterexamples expose a quiescence obligation
  outside listener joins. They do not establish every proposed late-admission
  race. Preserve the [source audit's scope](../review/connection-management-si4-source-audit-2026-10-27.md#server-joins-do-not-join-accepted-admission-children)
  rather than treating “Server returned” as “all raw workers completed.”
- **Confirmed finding — increment 53:** the initialized inbound occurrence now
  retains its original handler descriptor and entry/socket/promise references
  through physical publication, CM's wait and the selected race paths. A closed
  socket still has a stored identity; historical presence supplies no live owner.
- **Confirmed finding — increment 54:** the preferred frontend-only constructor
  now derives the primitive allocation/selection/fork equations, retaining both
  checked views in the origin record. The earlier paired-view statement remains
  available with its original type.
- **Confirmed finding — increment 55:** outbound resources now follow from
  initialized common-route acquisition histories and survive arbitrary enabled
  suffixes through pre-handshake publication and the owned CM wait. The
  acceptance reaches `closingCM`; no universal Server-return or quiescence
  certificate follows.
- **Confirmed finding — increment 56:** the capture-only frontend invariant
  now removes the acquisition-only prefix restriction from the broader outbound
  history constructor. The old constructor remains available unchanged.
- **Confirmed finding — increment 57:** current physical handler membership now
  yields an earlier enabled physical fork and its real frontend location.
  [The backing theorem](#fifty-seventh-increment-initialized-physical-handler-birth-backing)
  does not turn a CM entry naming a worker into physical registry membership.
- **Confirmed finding — increment 58:** acknowledged collected workers now
  have physical membership and earlier actual fork histories under the existing
  successful-initialization contract. The initialized same-entry failed-fork
  control confirms why an arbitrary entry reference is weaker than collection.
- **Confirmed finding — increment 59:** a real initialized preloaded acquisition
  can fork a descriptor whose captured entry and promise are absent; the paired
  `O.initial core` immediate fork is refused. Witnessed inbound histories now
  allow enabled gaps and retain their descriptor through publication and final
  CM wait. These model findings establish no new Haskell defect.
- **Confirmed finding — increment 60:** actual inbound forks now yield their
  earlier allocation and positive selection automatically, retaining the original
  labels and enabled gaps. The closed resource API derives operational PCs and
  stored resource facts internally. The same packet is checked through actual
  publication and final CM wait; historical presence remains distinct from ownership.
- **Confirmed finding — increment 61:** collected membership now supplies the
  discovered birth internally. Its inbound branch derives resource origins through
  the actual wrapper, preserving the event, descriptor and enabled gaps. The
  alternative retains an actual outbound birth without asserting its resources.
  See the [accepted contract](#sixty-first-increment-collected-inbound-resource-origins).
- **Confirmed model finding — increment 62:** the explicit `O.initial core`
  profile now supplies outbound reservation/promise history and stored resource
  facts from discovered collected births, with the existing inbound branch retained.
  The [milestone record](#sixty-second-increment-automatic-outbound-collected-resource-origins)
  records fresh full acceptance. The permissive
  preloaded-acquisition counterexample remains outside that profile.
- **Open question — remaining shutdown routes:** the accepted
  [finished-target route](#sixty-third-increment-initialized-finished-target-acknowledgement)
  covers independent cancellation before CM request. The outbound negotiated-mux
  route is accepted in increment 64. The
  [initialized TIME_WAIT route](#sixty-fifth-increment-initialized-time_wait-receipt-and-finalizer-routes)
  is accepted in increment 65, through real `Terminating`/`cleanupWaiting`,
  elapsed/interrupted finally, publication and CM waits. Its independent
  release caller remains pending; the [next contract](#next-batch-framed-mux-outbound-release-receipt-and-return-candidate-increment-66)
  addresses the missing coupled framed-mux release receipt and return.
  Resource origins outside the justified profile, receipt/birth multiplicity,
  global freshness and live ownership are not established. The malformed preloaded
  fork has no collected suffix; it does not refute every possible stronger
  theorem about collected workers.
- **Open question — SI4/SI5:** identify and discharge remaining admission,
  handler and outer-scope obligations before deriving whole-supervision
  completion. The [SI4 source-coverage audit](SourceLedger.md#si4-source-coverage-audit-10-november-2026)
  finds that both production `Server.with` callbacks can exit only by an
  exception. The existing Server exit chain follows that exit step for step and
  is now read as it (increment 1, documentation only). External cancellation,
  the ordinary node-shutdown path, is implemented in
  [increment 68](#sixty-eighth-increment-external-server-interruption), and the
  IG thread as race winner in
  [increment 69](#sixty-ninth-increment-the-inbound-governor-fails-first), and
  the accept loop failing first in
  [increment 70](#seventieth-increment-the-accept-loop-fails-first). All
  missing `Server.with` exit branches of the audit are now modelled for one
  listener. [Increment 71](#seventy-first-increment-derived-shutdown-certificate-for-the-outer-composition-si5a)
  (SI5a) derives the Server return, peer closure with its component
  certificates, and the relays join from one initialized outer history.
  [Increment 72](#seventy-second-increment-the-closed-cm-coordinator-at-the-final-state-si5b)
  (SI5b) adds the closed, drained CM coordinator and its physical final wait.
  [ProductionPolicy](Rules/ProductionPolicy.agda)
  still accepts an explicitly delivered completion boundary as a standalone
  wrapper. Any API-quiescence premise or source change needs its own
  evidence. G0–G5 and CM-I4c remain open.

## Milestones and completion criteria

Keep these IDs stable when recording progress or changing implementation scope.
The acceptance criteria originate in the 27 October 2026 plan; positions below
are reconciled through model commit `eef9971` (accepted increment 64), with
accepted, uncommitted increment 65 TIME_WAIT integration on 6 November. Later work must
recheck the actual theorem types and worktree.

| ID | Scope and required result | Current workstream position |
| --- | --- | --- |
| SI1 | Standalone one-owner governor-pool lifecycle: immutable registry snapshot, sequential cancel/wait, queue preservation, and certificates for snapshot Async results. | Committed in `8c79b9a`; checked within the snapshot contract. This is not full shutdown. |
| SI2 | CM caller cancellation and governor adapter: executable source-compatible cancellation effects, explicit bracket/handoff context, asynchronous-exception propagation, and job termination only after the modeled local unwind. | Committed in `8c79b9a`; real cleanup, capture/supply induction, initialized runs and pool-close certificate checked within the stated profile. |
| SI3 | Separate PSA background-thread registry/pool plus provider, churn and governor Async scopes, with their actual ownership and unwinding order. | Committed in `bb11970`. Initialized nonempty close, component certificates and capture/supply preservation pass. |
| SI4 | CM handler/mux lifetime and cleanup, connection-manager scope, and responder Server scopes, including remaining handler sends and joins. | Active. SI4-F1 (graceful TraceStopped/IG callback) is corrected in `920c16f`. Selected initialized callback/CM/Server paths, physical birth backing and handshake shutdown certificates are committed through `1e332cd`; collected-worker physical/birth backing is committed in `3822a47`; witnessed gap-aware histories and automatic inbound origins are committed in `db743c2`; collected inbound resource origins are committed in `898a02d`. Increment 62 is committed in `8636e88`, with outbound resource proofs under `O.initial core` and fresh full acceptance. Increment 63 finished-target integration is committed in `8dd2452`, with fresh full acceptance recorded below. Increment 64 outbound mux integration is committed in `eef9971`, with fresh full acceptance recorded below. Increment 65 TIME_WAIT integration is accepted and uncommitted, with fresh full acceptance recorded below. Remaining shutdown routes and full scope/quiescence obligations remain open. |
| SI5 | Derive `completeShutdown` only from all required scope certificates; remove dependence on an externally asserted whole-supervision completion boundary. | SI5a (increment 71): Server return, peer closure and component certificates, and relays join, derived for every initialized outer run reaching the finished relays state. SI5b (increment 72): at that state the CM coordinator is closed, has no unread snapshot entry, and was closed by an actual physical result wait. Raw admission workers stay outside (admission quiescence). |

The current production-policy wrapper's explicit completed-supervision boundary
remains a scoped assumption until SI5. No theorem about a smaller component may
be substituted for those remaining obligations.

## Remaining work and parallel execution

**Implementation checkpoint — 6 November 2026, HEAD `eef9971`.** Increments 59–60
are committed in `db743c2`, 61 in `898a02d`, 62 in `8636e88`, 63 in `8dd2452`
and 64 in `eef9971`. Increment 65 is accepted and uncommitted. The
increment-64 exact contract remains
in the [milestone entry](#sixty-fourth-increment-outbound-negotiated-mux-receipt-and-final-wait). The [G0–G5 acceptance criteria](DESIGN.md#9-implementation-gates-and-validation)
and overall objective remain unchanged.

### Next batch: origin profile and resource histories (increment 59)

**Completed.** The [acceptance record](#fifty-ninth-increment-initializer-boundary-and-gap-aware-resource-histories)
contains the formal initializer control/profile pair, entry retention and positive
selection helper, gap-aware inbound history, empty-gap adapter, alignment controls,
and nonempty-history publication/final-wait applications. Existing outbound
mixed-route and collected-birth applications passed in the full acceptance.
The planned unconditional selection packet was corrected: enabled `chooseEntry`
may return denial, so the positive post-PC is an explicit branch premise.
No existing statement or runtime guard was weakened.

### Next batch: reconstruct inbound occurrence histories (increment 60)

**Completed.** The [acceptance record](#sixtieth-increment-automatic-inbound-occurrence-reconstruction)
contains the closed inbound-fork resource API, exact original-label decomposition,
nonempty/empty and mixed-label controls, same-entry interference, and retention
of the same automatic packet through publication/final wait. Old witnessed and
outbound APIs remain available. No canonical-event restriction was added to the
observed prefix; only the final fork is classified by its two supported label forms.

### Next batch: connect discovered inbound births to automatic origins (increment 61)

**Completed.** The [acceptance record](#sixty-first-increment-collected-inbound-resource-origins)
contains exact-event birth decomposition, the closed collected adapter with an
explicit outbound alternative, and four same-occurrence lifecycle controls.
The source proof covers all certified selected wrappers directly; it neither
assumes two-label exhaustiveness nor claims a newly found enabled label.

### Next batch: outbound origin profile and history (increment 62)

**Completed and committed in `8636e88`.** The
[profiled collected adapter](#sixty-second-increment-automatic-outbound-collected-resource-origins)
recovers actual reservation and promise-allocation history from the discovered
outbound birth under `O.initial core`. Existing capture/resource lifts supply
stored facts; generic prefix observation remains independent of birth inversion.
The ordinary lifecycle and interference-only birth cases retain their distinct
scope. No runtime initializer or preloaded-acquisition control was changed.

### Next batch: already-finished target acknowledgement (increment 63)

**Completed, accepted and committed in `8dd2452`.** The
[authoritative increment 63 record](#sixty-third-increment-initialized-finished-target-acknowledgement)
distinguishes a live target captured before independently cancelled completion
from a late read of its terminated entry. The actual receipt derives collection
membership and preserves the same origin packet through the final CM wait.

### Next batch: outbound mux receipt and final wait (increment 64)

**Completed, accepted and committed in `eef9971`.** The initialized inbound
mux route already has acceptance in `CMResultLifecycleChecks` and increment 61.
The new outbound path executes acquisition, handoff, negotiation, mux startup,
real peer/Server/nonempty-IG closure and coupled CM receipt before the interrupted
group's whole-pool unwind, handler publication and final wait. See the
[authoritative contract](#sixty-fourth-increment-outbound-negotiated-mux-receipt-and-final-wait)
for the corrected initial profile, inactive tracer effects and controls.

### Next batch: TIME_WAIT receipt and finalizer route (candidate increment 65)

**Completed, accepted and committed in `a54d4fd`.** The
[source audit](../review/connection-management-si4-source-audit-2026-10-27.md#increment-65-time_wait-entry-and-finalizer-audit-6-november-2026)
supports real IG idle expiry, outbound release timeout and genuine cleanup entry.
The [milestone contract](#sixty-fifth-increment-initialized-time_wait-receipt-and-finalizer-routes)
now supplies initialized `Terminating` → `cleanupWaiting`, elapsed and CM-interrupted
finally routes, the same birth/resource packet through publication/final wait,
premature/duplicate controls and fresh full acceptance. No state is installed to
bypass those operations; pending release-caller completion remains explicit.

### Next batch: framed-mux outbound release receipt and return (candidate increment 66)

**Completed and accepted; uncommitted over `a54d4fd`.** The
[authoritative milestone record](#sixty-sixth-increment-framed-mux-outbound-release-receipt-and-return)
connects the genuine pending caller to a coupled mux receipt or available-result
acknowledgement, then its separate source return. It retains original
birth/resources and the actual final CM wait, with raw bypass, premature,
duplicate and local permission/target controls. Global API quiescence and the
remaining delivery windows are not established.

### Next task: source-baseline audit

**Audit completed; model pins retained.** The
[current-source audit](../review/connection-management-source-baseline-audit-2026-11-06.md)
verified the timestamped consensus/network pair `2e44d98…` / `2f1c154…`, obtained
the previously missing objects and compared the relevant lifecycle contracts.
CM/IG/Server/JobPool code is identical; changed mux held-batch readiness, handler
setup, egress ownership and synchronous DB waits require explicit mapping.
The linked report and [ledger](SourceLedger.md#latest-prototype-audit-6-november-2026)
record the decision and migration gates. Existing proofs retain their old-pin
scope. Caller-specific TIME_WAIT/post-mux expansion remains deferred; no guard,
statement or acceptance requirement may be relaxed during migration.

### Remaining dependency order

| Work | Dependency and completion evidence |
| --- | --- |
| Remaining collected-worker shutdown routes | After the profiled origin layer, integrate mux, cleanup/TIME_WAIT and already-finished paths. Preserve the same actual fork through acknowledgement, publication and the final pre-wait oracle; keep premature-wait/duplicate-publication controls. |
| CM-I4c tracked validity | Can proceed independently in separate component properties. Review initialized reference, phase and cleanup preservation across combined writers. [HandlerValidity](Properties/HandlerValidity.agda) is a diagnostic, not a proved global invariant or a filter for enabled transitions. Its legacy lifecycle store stays empty in the supervised stack ([LegacyLifecycleEmpty](Properties/LegacyLifecycleEmpty.agda), proved through `HandlerSupervision` and `OutboundHandlerSupervision`, audited above them; see [scope](HandlerValidity.md#scope-in-the-current-supervised-stack-10-november-2026)). Phase/cleanup validity for `HandlerSupervision` threads is proved through `OutboundHandlerSupervision` ([HandlerPhaseCleanup](Properties/HandlerPhaseCleanup.agda), over the cleanup-writer lemmas in [CleanupWriters](Properties/CleanupWriters.agda)), and with `MuxHandlerExit` exit frames and startup faults up to the top-level runtime ([MuxPhaseCleanup](Properties/MuxPhaseCleanup.agda), [FrontendPhaseCleanup](Properties/FrontendPhaseCleanup.agda), with peer actions by [CleanupPeers](Properties/CleanupPeers.agda)). The remaining CM-I4c obligation is reference validity of the live trackers, which these theorems do not state. |
| SI4 executable/source coverage | Audit now in parallel. For each selected Server/handler/provider/tracer/finalizer outcome, record implemented behavior, explicit contract, justified profile exclusion or missing branch using the [ledger checklist](SourceLedger.md#9-source-expansion-and-implementation-checklist). Implement missing branches only after pinned source/masking review and reachable controls. |
| Admission/API quiescence | In progress (increment 73: late-admission witness and replay; increment 74: residue c1, no pending inbound-governor CM call at the finished state; increment 75: c2 as first stated is false, since a foreign CM caller's frame survives shutdown; increment 76: restated c2 proved, every frame left at shutdown belongs to a foreign caller with no result yet; increment 77: in the owned-callers design variant the original c2 holds, no frame is left; increment 78: step 2 design exploration, Server-owned workers plus a CM handler registry are quiescent at shutdown; source candidate: a self-purged handler outlives `Server.with`). Investigate in parallel with SI4. Preserve the [finite Server replay](SourceReplay/README.md#actual-server-admission-worker-lifetime-replay) and model counterexamples: listener and CM completion do not imply raw-admission completion. Resolve the intended claim by source evidence, a justified profile, or a separately reviewed fix. Do not prove an unconditional claim contradicted by retained examples. |
| SI5 derived completion | SI5a is done in [ServerShutdownComplete](Properties/ServerShutdownComplete.agda) and SI5b in [ServerShutdownCoordinator](Properties/ServerShutdownCoordinator.agda), for the one-listener profile, from one initialized outer history. Raw admission workers stay outside (quiescence resolution). No eventual-completion claim follows without separate progress assumptions. |
| G0–G5 beyond supervision | Close the selected profile's branch/primitive matrix and initialized G2 lifecycles; extend G3 interference and audit G4 correspondence for the expanded dispatcher. G5 still needs enabledness-complete bounded enumeration, explicit cutoffs, trace export/minimization and source-operation replay. Existing raw trace proofs and finite native replays remain useful partial evidence. |

Explorer work can start with its interface and bound manifest while proofs run.
Keep limits outside semantic `advance`; distinguish cutoff, unavailable attempts,
malformed states, termination and actual blocking. Ordinary initialized paths
must fit the bounds before race searches. Exporter/tool selection follows the
intended semantic model and available tools; no FDR run is assumed. Extend
[existing replay artifacts](SourceReplay/README.md) selectively, preserving source
pins, injected contracts, IO/IOSim distinctions and their finite evidence limits.

### Four-agent execution protocol used for increment 62

| Owner | Completed increment 62 work and handoff |
| --- | --- |
| Agent A — acquisition profile | Audit initialized outbound acquisition profiles/writers and expose a small actual-event origin interface; keep prefix/effect proofs independent of birth inversion. |
| Agent B — thin composition | Compose the justified outbound branch with automatic reconstruction, retaining the actual prefix, fork and suffix and the explicit profile boundary. |
| Agent C — controls/evidence | Prepare concrete outbound/interference controls under `/tmp`; preserve the preloaded acquisition control and scope source claims to their pinned evidence. |
| Coordinator — integration/checks | Own shared APIs, the dependent `Negative/ServerPeersOrigins.agda` endpoint, docs/index and `PROJECT_STATE.md`; serialize checks and integrate the batch. |

Parallelize disjoint proof editing, source reading and lightweight evidence work.
**Run one Agda process at a time** from this library root with bounded heap/cgroup
memory and a resource check before heavy endpoints. Freeze each checked import
closure. Scope-only preflight can catch integration names cheaply; it does not
replace strict typechecking. Reuse opaque runs and narrow aliases, check focused
layers while editing, then full affected acceptance. Update docs/state at the
boundary and leave changes uncommitted until requested.

## Current executable integration

This section begins the historical implementation record, starting with SI1/SI2.
Dated “next,” “current” and “uncommitted” statements below retain their original
checkpoint meaning. Increments 45–52 were subsequently committed in `6878713`;
use the [current overview](#current-composed-lifecycle-certificates) for reconciled
claims and [PROJECT_STATE.md](../PROJECT_STATE.md) for continuation.

`GovernorPool` couples the ordinary `Subsystem` and production peer-policy stage
to `JobPoolLifecycle Body`. Successful raw fork/register, body-return, queue and
deregistration transitions drive the pool metadata; independent pool inputs
cannot fabricate a body result. Publication checks the exact job identity,
arguments and outcome, while retry-delay input remains checked by the original
subsystem. Once a body has returned, the adapter permits masked publication and
normal deregistration but refuses a new cancellation delivery in that gap.

`Rules/CallerCancellation` detaches the cancelled caller's acquisition/release
continuation into an explicit unwind frame. It preserves the entire `CM.core`
at detachment; subsequent close/remove/counter steps invoke the real
`OutboundAcquire.step` writer. The adapter blocks only that caller's old CM and
job continuations, retains the historical job, and permits unrelated work.
Cancelled deregistration removes the actual source pool entry without fabricating
a governor completion. Lease ownership and nested-map uniqueness are preserved
by detachment and every caller cleanup step, reusing existing writer theorems.

`Properties/GovernorPool` projects coupled executions into actual executions of
the separate pool component. Its `from-initial` theorem derives observable Async
results for the captured governor-pool snapshot when a finite coupled execution
reaches closedPool. This projection does not erase CM writes into raw subsystem
stutters. The source configuration actually retains their effects.

A failed socket close is significant: the source cleanup exception replaces the
original AsyncCancelled. `recoverCloseFailure` restores the raised close exception
to the awaiting peer job and resumes the ordinary peer-policy path. Depending on
the fixed classifier, it can produce a normal failed completion or attempt fatal
node delivery. Pool recovery from bodyUnwinding is exposed only at this adapter
boundary, not as a way to undo an observed terminal result.

The adapter records protected cleanup regions across counter PCs and splits
handler fork from successful bracket handoff. `deliverOpenCancellation` explicitly
acknowledges an interruptible blocked socket-acquire operation. These source
boundary inputs do not establish complete exception-mask semantics or source
reachability for arbitrary injected snapshots. `Properties/CallerCancellationCapture` retains the detached EntryId certificate,
and `Properties/GovernorPoolSupply` proves a combined invariant over ordinary
runtime captures, all detached cleanup captures, and shared supply bounds.
Deleting a caller slot therefore does not lose the premise needed by later
cleanup writes. The real initializer discharges both capture runtimes; initial
shared entry/promise bounds remain explicit. Existing raw Subsystem theorem
statements have not been changed or silently generalized.

SI3 now supplies the separate actual background-thread registry described below.
It is not `Subsystem.monitors`, which records only followup operations. SI4/SI5
remain open; no full shutdown action is derived or added by this integration.

## SI2 validation checkpoint (27 October 2026)

This SI1/SI2 implementation checkpoint was validated on top of `4f3b159`. These changes are
new implementation work, rather than required review corrections. All checks ran
sequentially with Agda 2.8.0 and `+RTS -M2G -RTS`:

- `Rules/CallerCancellation.agda` and `Properties/CallerCancellation.agda`.
- `GovernorPool.agda` and `Properties/GovernorPool.agda`.
- `Negative/GovernorPool.agda`.
- Amended `Rules/JobPoolLifecycle.agda`, `Properties/JobPoolClose.agda` and
  `Negative/JobPoolLifecycle.agda`.

All exited 0 with Checking output across the incremental checks. The final
GovernorPool projection was rechecked after tightening the owned-caller begin
guard. The final acceptance endpoint checks **118 equations**, including two
initialized close executions: a 21-action pre-resource cancellation retains the
reservation, while a 25-action socket-open/cancel/cleanup/deregister/Async-result/
join run closes the socket, removes the map alias, terminates the captured entry
and publishes no ordinary failed completion. Both instantiate the generic coupled
close certificate. Handoff, release/pruning, close-error recovery, exact normal
outcomes, masking and independent progress controls also pass; the later
injected snapshots remain conditional controls, not source-reachability proofs.

The amended pool primitive adds `resumeAfterUnwindError`, permitted only from
bodyUnwinding. This models a finalizer exception replacing cancellation; the
coupled adapter gates it on a recorded socket-close failure. Existing pool-close
certificate types remain unchanged. The prior 65-equation, three-execution
standalone acceptance endpoint also passes.

Four unchanged regression endpoints passed using cached interfaces:
`Negative/{ProductionPolicy,SubsystemSupply,SubsystemOwnership,SubsystemMapUnique}`.
The local proof audit of eight implementation/proof/acceptance files found zero
holes, postulates or unsafe flags. Whitespace checks passed. Initial elaboration
failures concerned imports, Maybe coverage, projection transports and explicit
impossible-constructor cases; all were resolved without weakening statements or
introducing trust assumptions. Final checks had no warnings. Independent source
and proof reviews found no substantive defect.

No Haskell replay, source-pin migration, dependency-version resolution or
unrelated heavy build was run. The
old Subsystem proofs retain their original scope. The new caller writer has
map-uniqueness and lease-ownership preservation, while `GovernorPool.from-initial`
certifies only its pool's captured Async handles after an actual finite run.

The subsequent capture/supply increment also passed: the induction predicate
is `SubsystemSupply.Valid (machine s)` paired with `All` detached cleaning-frame
capture validity. `from-initial` proves entry/promise bounds after every finite
coupled execution from `GovernorPool.initial (CM.initial c) g`, requiring only
the initial shared supply bounds. Real raw steps retain all pending detached
references; cancellation transfers the capture; cleanup advances it and preserves
both ordinary and detached runtimes. Acceptance applies this theorem while the
original caller slot is already absent and again after each initialized close.

The pool engine is now factored into `JobPoolKernel Result queued` and
`JobPoolCloseKernel`, with the original public modules retaining their queued
specialization. In queue-free mode, body return proceeds directly to normal
deregistration and `publishCompletion` is unavailable. The new
`Negative/WithoutQueuePool` endpoint checks normal and cancelled initialized
executions and applies queue-free close certificates. This is a prerequisite,
not a background-thread registry or SI3 completion claim.

The two new capture/supply modules, queue-mode kernel/certificate, the amended
queued acceptance endpoint, and the queue-free endpoint all passed sequential
Agda checks with Checking output. The final governor acceptance rechecked under
the factored kernel and includes the new capture/supply applications. A final
local audit covers thirteen files with zero findings. Queue-mode matching used
explicit helper functions after Agda rejected matching on a module parameter;
no check was disabled and no theorem weakened.

That SI2 checkpoint was committed as `8c79b9a` before starting SI3 below.
`Subsystem.monitors` cannot stand in for the actual thread registry. SI4 and SI5
remain outstanding, and no completeShutdown derivation is claimed.

## Acquisition cancellation matrix

CM acquisition has no outer `mask` ([Core.hs:1273–1276][acquire-start]); its public
API is a projection ([Types.hs:577–596][api]). JobPool restores the job action,
and the peer-state-actions bracket restores its body, so the ordinary caller
path is unmasked. Nested resource acquisition, fork and cleanup regions have
their own masking rules.

| Acquisition context / modeled PC | Cancellation effect and guard |
| --- | --- |
| `selecting`, before initial STM commits | An interrupted transaction rolls back. Do not fabricate a new reservation. |
| `count (allocatePromise ...)`, `allocatePromise`, before socket acquisition | Reservation insertion already committed, but the socket bracket is not installed. Cancellation can retain `ReservedOutbound`; no CM reservation cleanup is automatically available. |
| `openSocket`, executing bracket resource acquisition | `bracketOnError` masks resource acquisition. Delivery is possible at an interruptible operation, not at every abstract boundary. If acquisition does not return a resource, its release handler does not run. |
| `configureSocket`, `bindSocket`, `connectSocket`, `localAddress`, `updateAddress`, before handler fork | These belong to the restored bracket body. Cancellation invokes its error cleanup: close the socket first, then delete this captured entry's aliases and write `Terminated Nothing`. |
| Handler exists, but bracket body has not returned | Still inside the parent's error bracket. Parent cleanup may run while the handler also exists. This needs a separate explicit pre-handoff boundary. |
| `connectedCommit`, `count (awaitResult ...)`, `awaitResult` | Successful bracket return has transferred cleanup ownership to the handler. Caller cancellation abandons the call; it does not automatically cancel or join that handler. |
| `commitResult`, before/after handshake transaction | Cancellation of a blocked transaction rolls back its state writes and IG enqueue together. Already committed changes remain. There is no socket-bracket rollback after handoff. |
| `waitingInbound` | Abandon the captured inbound wait; do not clean up the borrowed inbound connection. |
| Error cleanup `closeError`, `removeError`, its counter trace | Cleanup is uninterruptible. Reject a second cancellation delivery in this region. Close failure prevents subsequent map cleanup and may replace the original exception. |

The initial reservation is inserted at [Core.hs:1399–1431][reservation]. The
socket bracket, cleanup and restored body are at
[1451–1535][socket-bracket]. The handler fork and successful body return are
separate source boundaries at [1531–1537][handoff]. Connected commit and promise
wait are at [1537–1584][await-result]; the handshake write and optional bounded IG
enqueue share STM at [1600–1664][handshake]. The borrowed inbound wait is at
[1666–1755][inbound-wait].

A model that jumps directly from `forkHandler` to `connectedCommit` omits the
forked-but-pre-handoff cancellation window. Fork itself uses `mask_`
([Core.hs:579–592][handler-fork]); that does not mask the whole surrounding
acquisition body or the later connected commit.

`count` wrappers cannot determine cancellation permission from their shape or
final fault alone. Preserve the inherited region. The cleanup's counter trace
at [1469][socket-bracket] is uninterruptible; ordinary acquisition traces at
1423, 1582, 1661 and 1754 inherit the caller context. In particular, a cleanup
`count (complete (raised ...))` must not be mistaken for an ordinary cancellable
return with the same result constructor.

The concrete socket implementation documents a blocking IO-manager association
inside opening ([Snocket.hs:394–407][socket-open]). Its lower-level exception
handling is not a general proof that every possible opening failure closes every
OS resource. Keep acquisition failure and returned-resource cleanup distinct.

## Exception propagation through the caller

Peer-state actions catch acquisition with `try` as `SomeException`, including
asynchronous exceptions ([PeerStateActions.hs:784–801][psa-catch]). Under the
pinned base policy an ordinary cancellation selects `ShutdownPeer` and is
re-thrown as the same asynchronous exception. The peer-state bracket restores
`PeerCold`. The outer JobPool handler excludes `SomeAsyncException`
([JobPool.hs:147–164][job-exceptions]), so this path must not manufacture an
ordinary failed governor completion.

Keep cancellation distinct from the coarse abstract `ioFailure ErrorId` used by
normal policy examples. Do not allow an opaque classifier to turn a known
cancellation exception into a production IO-manager fatal error. Custom open
policies remain a separate profile.

## Release cancellation matrix

Outbound release has no outer mask or rollback handler
([Core.hs:1840–1844][release-start]); its PSA caller also has no enclosing mask
or release-on-cancel bracket ([PeerStateActions.hs:1050–1105][psa-close]).

| Release context / modeled PC | Cancellation effect |
| --- | --- |
| `transaction`, before STM commit | Roll back the transaction. |
| After demotion commit: `count`, `armTimer`, `waitIdle` | Abandon the timer wait with committed `OutboundIdle` retained. Do not invent handler cancellation or state rollback. |
| `timeoutWrite`, before its STM commit | Preserve the prior state; after commit, preserve `Terminating`. |
| `count (cancel ...)`, `cancel`, `delivering` | Cancellation may interrupt the sender before or while sending. Delivery acknowledgment is not handler termination. Already delivered target effects remain possible. |
| `prune` | All selected victim writes committed before the sequential send phase. Cancellation can leave a pending send tail; do not undo writes or acknowledge undelivered sends. |

Demotion, timer registration, ordered STM wakeup and handler send are at
[Core.hs:1875–2034][release-wait]. Release intentionally uses `throwTo` without
waiting for handler time-wait completion. Pruning atomically writes victim states
then performs later sequential sends ([Core.hs:762–777][prune]); release runs
that action at [2042–2046][release-prune].

## Remaining supervision boundaries

Handler `finally` cleanup is independent of caller cancellation. Its map/socket
work is uninterruptible; its time-wait delay explicitly unmasks, with a final
state/map update even if interrupted ([Core.hs:595–710][handler-cleanup]). A
caller-pool join is therefore not a handler-cleanup certificate.

The governor WithQueue pool and PSA WithoutQueue background-monitor pool are
separate. Diffusion nests PSA, providers, governor Async, then churn Async. Scope
unwinding cancels/waits churn before governor, then unwinds provider scopes and
PSA, while other threads may continue concurrently
([Diffusion.hs:767–826][diffusion-scopes]). Server adds independent action,
inbound-governor and accept-loop scopes ([Server.hs:147–175][server]). SI3 and
SI4 must account for these before SI5 derives full completion.

This checkpoint records source evidence and implementation obligations. It makes
no new validation, source-refinement, cleanup-liveness or full-shutdown claim.

[acquire-start]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1273-L1276
[api]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Types.hs#L577-L596
[reservation]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1399-L1431
[socket-bracket]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1451-L1535
[handoff]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1531-L1537
[await-result]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1537-L1584
[handshake]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1600-L1664
[inbound-wait]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1666-L1755
[handler-fork]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L579-L592
[socket-open]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/Snocket.hs#L394-L407
[psa-catch]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerStateActions.hs#L784-L801
[job-exceptions]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/network-mux/src/Control/Concurrent/JobPool.hs#L147-L164
[release-start]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1840-L1844
[psa-close]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerStateActions.hs#L1050-L1105
[release-wait]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1875-L2034
[prune]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L762-L777
[release-prune]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L2042-L2046
[handler-cleanup]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L595-L710
[diffusion-scopes]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/Diffusion.hs#L767-L826
[server]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/framework/lib/Ouroboros/Network/Server.hs#L147-L175


## SI3 source-derived integration checklist

This source-verified checklist guided the SI3 implementation and remains the
source-to-model scope contract. The executable implementation and validation
checkpoint follow it; the remaining CM/handler/server scopes are SI4.

- Split background creation, registration and successful establishment return.
  [PSA:836–852][si3-spawn] calls `JobPool.forkJob` before returning the peer
  handle. [JobPool:122–145][si3-register] masks each spawning parent across fork
  and registry insertion; the child can act before insertion, but deregistration
  waits for its entry. Do not interpret atomic `J.launchMonitor`/job completion
  as all three boundaries. Keep the pre-registration mask and the subsequent
  in-bracket establishment-return window explicit: cancellation after
  registration but before successful establishment return restores `PeerCold`
  while the already spawned monitor remains independently owned.
- Model multiple spawning parents. The PSA pool is shared by concurrent
  establishment jobs, unlike the governor's single spawning loop. Each parent
  has its own masked fork/registration gap. A single `parentFork : Maybe ...`
  kernel must not be presented as preserving all concurrent parent gaps. Use
  multiple-parent tracking, or an explicit source-adapter certificate with a
  clearly limited serialization/coverage claim. Queue-free operation alone does
  not solve this ownership issue.
- Keep a physical background-thread registry with a captured peer reference and
  fresh thread identity. `Sub.monitors` contains only a temporary followup
  operation; its absence is not physical thread termination. `monitorStarted`
  is not registry or join evidence. Bind each `pollPeer`/followup caller to its
  captured physical worker, so a detached, cancelled or completed thread cannot
  resume through an independently supplied caller ID.
- Distinguish monitor outcomes. Normal waiting observes `PeerCold` directly or
  waits for CM demotion and atomically writes `PeerCold`
  ([PSA:673–695][si3-wait]); normal exit traces hot duration, clearing its saved
  promotion time ([PSA:651–660][si3-duration], [773–775][si3-loop]). Protocol-error
  result branches update cooling and recurse; they do not by themselves throw
  an ordinary exception. Clean hot results invoke deactivation and recurse;
  clean warm/established results invoke close and recurse
  ([PSA:709–767][si3-loop]).
- Represent the synchronous-error handler separately. It waits for outbound
  demotion, writes `PeerCold`, traces hot duration/error, then rethrows; the
  outer Job handler returns `Just exception`. The inner handler explicitly
  excludes asynchronous exceptions ([PSA:836–849][si3-spawn]). Cancellation can
  interrupt its demotion wait: do not write cold unless that transaction has
  committed. The ordinary error identity must remain captured if a conditional
  source-projection claim depends on it.
- On asynchronous cancellation, retain already committed controls, status,
  partial starts, promotion time and CM release effects. There is no monitor
  cancellation finalizer that forces `PeerCold` or runs the ordinary error
  handler. If an active followup owns a CM release, detach/unwind that captured
  caller and retain its pending send tail. Then distinguish local unwind,
  deregistration and Async result availability. Do not fabricate a governor
  completion or any WithoutQueue result publication.
- Begin outer PSA pool close only after governor Async completion/join and the
  intervening provider scope joins. A governor-pool `closedPool` certificate is
  a prerequisite inside governor unwinding, not the governor Async result.
  Diffusion nesting requires churn, governor, local-root provider, ledger-peer
  provider, then PSA pool scope exit
  ([Diffusion:767–826][si3-order],
  [PeerSelectionActions:84–102][si3-providers]). Other monitor and handler
  activity can continue during these waits. SI4 handler/CM/server certificates
  and SI5 derived shutdown remain separate obligations.

[si3-spawn]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerStateActions.hs#L836-L852
[si3-register]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/network-mux/src/Control/Concurrent/JobPool.hs#L122-L145
[si3-wait]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerStateActions.hs#L673-L695
[si3-duration]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerStateActions.hs#L651-L660
[si3-loop]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerStateActions.hs#L709-L775
[si3-order]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/Diffusion.hs#L767-L826
[si3-providers]: https://github.com/IntersectMBO/ouroboros-network/blob/96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d/ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerSelectionActions.hs#L84-L102


## SI3 executable integration and validation (27 October 2026)

Commit `8c79b9a` contains SI1/SI2. This SI3 checkpoint was validated on top of it.
`PeerSupervision` now owns a physical monitor-thread registry, a separate
WithoutQueue pool, and the outer Async scope coordinator. It routes followups
through each captured worker and refuses untracked launch, caller substitution,
or resumption after cancellation. It refines the original atomic launch into
fork, parent registration, PSA return and governor-job return. A spawning parent's
own masked gap blocks its cancellation delivery while other parents/children
continue. Cancellation after insertion but before PSA return restores Cold;
after successful PSA return it preserves the peer, independently of job return.

`JobPoolKernel` admits concurrent fork/register only in queue-free mode and
requires every outstanding insertion to settle before the outer snapshot. The
queued governor specialization keeps its previous single-owner behavior.
Historical removed children are not re-registered or mistaken for live gaps.
A child can return before its own insertion, but cannot deregister before it.

Normal monitor exit and its duration-variable clear are distinct from a followup
operation finishing. An active followup must complete before the physical loop
exits. Ordinary thrown errors enter a captured demotion wait and write Cold only
when that wait commits; exit tracing then clears promotion time. Asynchronous
cancellation bypasses that handler, retains committed peer/control/release effects
and promotion time, and produces no governor completion. Blocking interruptibility
in a masked error handler is an explicit observation. `monitorException` is an
observed synchronous throw, not a proof that every supplied error is reachable.

`Rules/AsyncScope` models churn, governor, local-root provider and ledger-peer
provider. Its join cursor follows that nesting order, while independent thread
completion can occur earlier. Governor pool close requires delivered cancellation
or an explicit independent exception-entry observation. Governor Async body exit
requires its own pool closed; the outer monitor snapshot requires the Async scope
joins completed. Thread local-body exit remains an explicit component boundary;
provider/churn internals and startup before those scopes are entered are outside
this ordinary-profile coordinator. The pool relays thread is not a fifth actor:
it encloses the whole remote callback, so `Rules/PoolRelays` wraps the Server
composition instead and is joined only after `serverReturned`. No eventuality or
full Haskell refinement is claimed. The four scope statuses are stored as finite fields, avoiding nested
callback histories while preserving the getter/snapshot-builder interfaces.

`Properties/PeerSupervision` projects every coupled step and finite execution to
three actual operational traces: the governor pool, physical monitor pool and
Async scope coordinator. From the real initializer and the three observed closed
states, its certificate gives terminal Async results for both captured snapshots
and all four scope joins. Real CM/peer writes remain in the source execution;
only the separate metadata components are projected. `PeerSupervisionSupply`
preserves ordinary and detached captures plus shared entry/promise bounds across
all coupled actions/interleavings, requiring only initial shared bounds.

Validation used Agda 2.8.0 and `+RTS -M2G -RTS`, one process at a time. The new
rules, component/capture-supply proofs and all acceptance layers passed. The
maintained endpoint is `Negative/PeerSupervision.agda`, which publicly reexports
three checked layers: `PeerSupervisionScenarios`, `PeerSupervisionGovernorClose`
and `PeerSupervisionClosing`. They retain **144 named reflexivity equations**,
an initialized 44-action monitor spawn, a 26-action empty-scope close and an
initialized **81-action nonempty close**. The latter actually queues the normal
governor result while the owner is unwinding, joins that job, joins the provider
scopes, and cancels/deregisters/joins the captured monitor. It instantiates both
pool/scope certificates and the capture/supply theorem. A concrete handler remains
present afterward, an explicit control against calling this full shutdown.
`Negative/ConcurrentPool` adds 17 equations and an initialized seven-action
registration-race execution. Conditional snapshot controls remain distinguished
from initialized model executions and from implementation reachability.

The initial monolithic acceptance check exhausted its 2 GB heap. Explicit
component snapshots, finite scope fields, and separate checked scenario/governor/
closing proof layers resolved it without increasing the heap limit, deleting
cases, changing theorem statements or adding axioms. Earlier elaboration fixes
covered inaccessible private module aliases, constructor names and store order.
Final checks produced no warnings. Logs are under
`/tmp/cm-review-20261027/si3-*.log`; generic component proof logs are also under
`a6-checks/` at that location. The queued-pool compatibility check passed with
Checking output. Final regression checks of `Negative/WithoutQueuePool` rechecked;
`Negative/{GovernorPool,SubsystemSupply,SubsystemOwnership,SubsystemMapUnique}`
passed with cached interfaces. The twelve-file local proof audit found zero
findings. Whitespace checks passed. No replay, upstream source/spec edit,
dependency upgrade or unrelated heavy proof build was run.

Next is SI4: audit and connect actual handler creation and post-handshake mux
job ownership, callback/pool/buffer unwind, CM finalizers and responder-server
scope joins. Existing `HandlerLifecycle.jobPoolClosed` and other local completion
inputs must not be promoted to a whole-scope certificate without their own
captured job/cleanup evidence. The initialized remaining handler is the concrete
starting fixture. SI5 will consume the resulting certificates; no full shutdown
transition has been derived here.


## SI4 first increment: CM scope traversal

SI3 is committed as `bb11970`. The first SI4 increment adds
`Rules/CMShutdown`, `Properties/CMShutdown` and `Negative/CMShutdown`.
The [source audit](../review/connection-management-si4-source-audit-2026-10-27.md)
records why the CM algorithm differs from JobPool close and why Server listener
joins cannot establish admission quiescence.

The coordinator snapshots current map entry references once, reads their heap
cells later, sends cancellations with separate delivery acknowledgments, then
waits collectively for the collected Async results. Repeated references are
preserved. Store enumeration abstracts source Map key order; no ordering
refinement is claimed. Arbitrary shared-store and result-observation inputs may
interleave with coordinator steps, without a fictitious global closed flag.
`closed-from-initial` certifies an exhausted traversal and a witness of the actual
successful final wait, with the exact observation oracle used at that boundary.
It does not assume future oracle values or certify uncollected handlers.

Physical Async-result observations remain explicit adapter obligations. They
must ultimately follow actual mux-pool, buffer, CM finalizer and result-publication
steps; neither delivery acknowledgment nor a historical handler capture suffices.
This increment does not connect those physical lifetimes or derive full shutdown.
The source audit describes the remaining mux startup/generation/group-cancel and
Server/IG scope obligations. SI4 and SI5 remain open.


Validation on 27 October 2026: all three new Agda modules passed with fresh
Checking output, Agda 2.8.0, `+RTS -M2G -RTS`, sequentially and without warnings.
Acceptance contains 32 named reflexivity controls, a nine-action bulk traversal,
the generic final-wait certificate application, and a ten-action product
execution: empty CM capture/traverse/close followed by the seven real inbound
admission actions from `CSP.Fixtures.start` to `waiting`. A handler and its owned
socket then exist while the coordinator remains closed with an empty snapshot.
The fixture starts after accepted-child handoff; this is not a derivation of the
full Server prefix or a Haskell replay. Other controls cover delayed entry reads,
Terminated skipping, duplicate references, missing historical handlers,
map-lock blocking and refusal to finish with only some results available.

The acceptance check initially reported two implicit inference metas in its
path-lifting helper; explicit source/target/action arguments resolved them.
The final three-file local proof audit found zero holes, postulates or unsafe
flags; whitespace passed. Existing theorem files were not modified. No broad
unrelated proof rebuild, source change or replay was run. Logs are
`/tmp/cm-review-20261027/si4-cmshutdown-{rules,negative}.log` and
`/tmp/si4-cmshutdown-properties.log`. This CM traversal increment is committed
as `2c39700`.

Next executable obligation: track physical handler identity from the real fork
and bind pre-handshake cancellation, promise catch regions and CM finalizer
completion to Async result publication. Then build the physical mux startup and
per-direction/per-generation job pool, with its separate interruptible group
close and buffer boundary, before supplying post-handshake observations to the
CM coordinator. Server listener/action/IG ordering and admission quiescence must
remain explicit before SI5 consumes a whole-scope certificate.


## SI4 second increment: pre-handshake handler completion

`HandlerSupervision` is a bounded inbound pre-handshake adapter over the actual
`Machine` dispatcher and `CMShutdown` coordinator. It initializes only without
pre-existing handlers/cleanups/lifecycle frames/publication faults and captures
the physical child's original `HandlerStart` at the successful admission fork.
No later key lookup changes that child's captured entry, socket or promise.
The historical handler heap is not adopted as an active Async registry.

Setup return and blocked-setup interruptibility are explicit local observations.
Ordinary async delivery is allowed in the unmasked handshake; its catch must
publish the real `handlerError protocolViolation` promise, rethrow, then enter
the actual CM finalizer. Observed blocked cancellation in masked setup bypasses
that promise because setup is outside the catch. This first profile supplies no
successful-handshake/mux completion shortcut.

All finalizer transitions invoke existing cleanup writers. Completion retains
both the original cancellation error and actual cleanup outcome. A close error
replaces the effective exception and can leave socket-close uncertainty.
`cleanupDone`, finalizer return and Async result publication are separate
boundaries. The last publication checks the real cleanup outcome again. The CM
coordinator receives only the registry's `resultReady`; callers cannot inject an
oracle or acknowledge a cancellation without coupled delivery/finished-target
evidence. During TIME_WAIT a coupled delivery invokes the real interruption
step, whose termination/purge continuation still must run before result return.

Raw handler publication/exit/lifecycle/cleanup and release/pruning cancellation
acknowledgments are refused by this adapter. Ordinary independent source actions
retain the original guards. Delivery coupling for release/pruning senders, outer
peer supervision, outbound physical fork, normal/synchronous handler outcomes,
mux jobs and Server scopes remain later integration work. No global closed flag
freezes later admissions; a closed snapshot is not whole-node shutdown.


`Properties/HandlerSupervision` projects every successful wrapper step and every
finite interleaving into actual `Machine.Executes` and `CMShutdown.Executes`
paths. Its `closed-from-initial` certificate retains a drained traversal and a
`PhysicalWait` with the actual wrapper finish transition and its registry-derived
oracle. The checkpoint remains meaningful after independent source actions;
it does not assert the same oracle at every later state. Existing Machine supply,
map-uniqueness and lease-ownership theorems lift through the projected real source
execution, with their original initial premises and no new runtime validity gate.

Integration must eventually start at the real outer initializer so all physical
forks are tracked. The SI3 endpoint's retained post-handshake handler cannot simply
be adopted into this empty-registry initializer. Outbound birth and successful
handshake/mux startup must be coupled before replaying that entire outer history.


Validation on 27 October 2026: `HandlerSupervision.agda`,
`Properties/HandlerSupervision.agda` and `Negative/HandlerSupervision.agda` all
passed with fresh Checking output, sequentially in Agda 2.8.0 with
`+RTS -M2G -RTS`, without warnings. The final acceptance check includes the
initialized 24-action fork/cancel/promise/finalizer/result/CM-close execution,
73 named reflexivity controls, and the initialized ten-action empty-close then
late-admission execution. It instantiates the generic physical-wait certificate,
actual Machine trace projection, supply preservation and both successful and
failed-cleanup result-publication checkpoints. The latter checkpoints retain the
original captured thread and the real cleanupDone observation at publication.
The generic map and lease-ownership corollaries preserve their explicit initial
premises; no whole-state validity is assumed by execution guards.

Controls additionally cover masked setup without a promise, refusal of raw
handler and cancellation-acknowledgment bypasses, wrong workers, failed socket
close/map restoration/exception replacement, and a child finalizer blocked by
its parent's outstanding map lease. A two-action consumer suffix from the
reachable caught publication checks protocolViolation's actual Terminated/purge
effect. TIME_WAIT interruption controls are conditional snapshots, not initialized
source reachability witnesses. The source exports and exception classifier were
checked at the existing network pin; no pin change or Haskell replay was run.

Initial checker failures were nested-with clause association, a fixture argument
name collision, and implicit inference of trace inputs erased by reduction.
Explicit clauses/arguments resolved them without modifying existing semantics,
weakening theorem statements, raising the heap limit or adding trust assumptions.
The final three-file proof audit had zero findings; whitespace checks passed.
Logs: `/tmp/cm-review-20261027/si4-handler-{rules,properties,negative-final}.log`.
No unrelated proof rebuild was run. This second SI4 increment is uncommitted.

Next is outbound physical birth and successful-handshake/mux ownership, including
fresh directional run identities, real pool startup, the separate interruptible
mini-protocol group close, final pool joins and buffer release. Couple these from
the true outer initializer, retaining the earlier peer supervision proofs and
late-admission behavior. Release/pruning sender acknowledgments and Server/IG
scope completion still need integration before SI5 can derive full shutdown.


## SI4 third increment: outbound physical birth and mux-startup prerequisite

`OutboundHandlerSupervision` extends the pre-handshake physical registry across
actual outbound acquisition/release and inbound interleavings. `O.core` is the
only stored dispatcher configuration; the inherited handler state is a view,
so handler writes replace that core without losing pending callers, operation
results or the random-generation field. Outbound `forkOK` captures the actual
new HandlerStart immediately, before `commitConnected`. Physical child freshness
also excludes active admission/outbound caller identifiers and retained physical
history. This is a symbolic worker-identity profile, not an implementation
ThreadId ordering theorem.

Raw `O.inbound` cannot bypass handler gates; raw outbound release delivery is
also refused until a coupled delivery adapter exists. The real source operation
still has its original guard for every enabled step. The initializer refuses
existing handler captures while retaining any supplied caller runtime; arbitrary
such runtimes require the existing capture/supply premises. The ordinary
`O.initial` corollaries derive empty-runtime capture validity and require only
the shared world's initial allocation bounds.

`Properties/OutboundHandlerSupervision` projects every step and finite execution
to actual `OutboundMachine.Executes` and `CMShutdown.Executes`. New outbound
writers remain real source steps, rather than stutters justified by an old
inbound invariant. Its capture and combined runtime/supply corollaries reuse the
actual outbound proof endpoints. The closed certificate retains the exhausted
snapshot and inherited physical wait at the actual handler-view boundary, with
no claim about all historical or later handlers.

The standalone `Rules/MuxStartup Result` is the next prerequisite, with a generic
result type so mux infrastructure and later mini-protocol actors can share one
WithQueue pool. It separates observed success publication, buffer acquisition,
bearer construction, run/Starting/egress/pool setup, each infrastructure fork and
registry insertion, Mature and monitor entry. Its startup phases retain the
muxer/demuxer physical identities; child completion can run between parent steps.
Neither `MuxRuntime.ready` nor an existing pool snapshot initializes ownership.

Success publication remains an explicit observed boundary in this component:
no theorem yet couples it to a successful handler promise in the physical
outbound adapter. It supplies no buffer-release, shutdown, group-cancel or join
action, and no successful/mux handler result can be published through the bounded
pre-handshake adapter. The next integration must couple that boundary and actual
startup to each captured handler before deriving post-handshake completion.


Validation on 27 October 2026: all six new modules passed with Agda 2.8.0,
`+RTS -M2G -RTS`, one process at a time, without final warnings. The outbound
adapter, its property endpoint and its acceptance endpoint had fresh Checking
output. MuxStartup rules checked transitively during the first property check;
the subsequent explicit rule command passed using that cached interface. Final
MuxStartup property and acceptance commands had fresh Checking output. The first
transitive rule output remains in the tool transcript rather than a preserved
log; the explicit rule log is empty because that check was cached.

Outbound acceptance has 54 named reflexivity controls, an initialized 28-action
acquisition/child-before-Connected/cancellation/cleanup/result/CM-close execution,
and applications of the actual source/coordinator projections, physical-wait,
capture and combined runtime/supply certificates. Initialized inbound/outbound
interleavings preserve pending callers, and empty-close/later-admission still
captures new physical children. An initialized 14-action local run closes a CM
snapshot that skipped the ReservedOutbound entry while the already forked child
remains alive. This does not derive the full diffusion prefix: outer caller joins
and scoped API use still need integration before claiming a source shutdown race.

Mux-startup acceptance includes 15 named reflexivity controls, a 13-action
initialized startup, actual same-pool fork/register projections, distinct physical
capture certificates, refusal of out-of-order/reused identities and early monitor
entry, plus a fast-child interleaving. The child returns and publishes to the
queue before insertion, cannot deregister early, then inserts/deregisters and
publishes its Async result before the demuxer fork. A final initialized run still
reaches monitor entry with that first child already unregistered; the historical
capture certificate and actual pool trace both apply. These remain standalone
component executions with observed body/publication boundaries, not successful
handler-source refinement or completed mux shutdown.

Proof-checker repairs concerned names colliding with existing constructors,
implicit argument inference, with-abstraction equality transport and an explicit
All constructor for initial bounds. All were resolved in the new files without
modifying the old rules or weakening statements. The final six-file local proof
audit found zero holes, postulates or unsafe flags; whitespace passed. Source
exports for Core, ConnectionHandler, Mux and JobPool were compared again against
the pinned Git objects. No replay, pin change or unrelated proof rebuild was run.
Logs: `/tmp/cm-review-20261027/si4-outbound-handler-{rules,properties,negative}.log`
and `si4-mux-startup-{rules,properties,negative}.log` in the same directory.
All work after `2c39700`, including the prior pre-handshake increment, remains
uncommitted. The pre-existing `.claude` symlink is untouched.

Next executable action: couple successful handshake/handle allocation and actual
promise publication to each captured handler's mux-startup instance, including
the masked post-handshake/buffer/bearer interval. Do not leave the old handshaking
cancellation path enabled after success or infer physical startup from M.ready.
Then add fresh directional/generation mini-protocol ownership in the same pool,
exact result publication, separate interruptible group cancellation, final pool
joins and buffer release before enabling post-handshake CM finalization. Reconnect
the outer peer-supervision history from its true initializer and finish Server/IG
scopes with admission quiescence explicit. SI4/SI5 and full shutdown remain open.


## SI4 fourth increment: successful handler to mux-startup coupling

`MuxHandlerSupervision Result` is an additive wrapper over
OutboundHandlerSupervision. It retains one shared outbound source, records
inbound/outbound birth provenance only at successful real fork transitions, and
keeps a separate startup frame for each observed successful handler. Its
initializer rejects pre-existing physical handlers and pre-existing IG
handles/muxes rather than adopting their ownership.

`negotiate` is the explicit restored-handshake-success observation. It captures
the registered handler's original references, protocol bundle and flow, and
immediately disables that handler's old handshaking/cancellation/body/cleanup/
result paths. Birth provenance selects actual `installHandle` for inbound or
mode/flow-sensitive `installOutboundHandle` for outbound, using the captured key;
mutable CM entry provenance is never consulted for this decision.

`publishSuccess` invokes the real `OutboundMachine.inbound` handler-publication
writer and the selected `MuxStartup.observePublication` in the same transition.
Handle allocation alone does not publish a promise. After publication, independent
callers may consume the result and enqueue requests while the buffer, bearer and
physical infrastructure startup remain pending. Each handler then advances its
own startup instance through the same queued-pool fork/register transitions.
Infrastructure JobIds must be fresh across all captured mux pool histories,
including deregistered children; the per-pool certificate alone is not described
as a proof of global uniqueness.

Raw handle installation and independent publication observations are blocked.
Inherited old handler and CM-delivery actions cannot bypass a captured success
frame. Monitor/tracer/job actions for its allocated mux are also parked until a
physical protocol/monitor adapter extends this startup prefix; ordinary command
enqueue and unrelated actors retain their original guards. There is no successful
body-exit, pool-close, buffer-release, CM-finalizer or Async-result shortcut.
Masked setup failures, blocking interruption and startup unwind remain future
branches, not a theorem that those interruptions cannot happen.


`Properties/MuxHandlerSupervision` projects every step and finite execution to
actual OutboundMachine and CMShutdown executions, retaining the physical final
wait, and to a separate startup execution for every selected handler. Its
initialized monitoring certificate gives that handler's distinct captured
infrastructure identities and actual same-pool history. The source projection
lifts existing capture/runtime-supply theorems with their original premises;
new allocation and publication writes are not erased into old-wrapper stutters.
A local `Publication` witness retains the actual source promise write and matching
startup observation. `startup-parent-registry` proves every startup-only step
leaves the physical parent handler table unchanged; a child Async result does
not fabricate the parent handler's result.

Validation on 27 October 2026: the new model, property and acceptance modules all
passed with fresh Checking output, sequentially at Agda 2.8.0 with
`+RTS -M2G -RTS`, without final warnings. The maintained endpoint is
`Negative/MuxHandlerSupervision.agda`. It contains 104 named reflexivity controls,
an initialized 27-action outbound fork/success/publication/monitor-entry run,
actual inbound second-handler birth and independent per-handler startup histories,
and an actual CM-consumer/IG request-enqueue suffix before buffer/job startup.
Generic source/coordinator/selected-handler projections, monitoring/pool-history,
publication, capture/supply and parent-registry certificates are instantiated.
A three-action initialized empty CM close also instantiates the inherited
physical-wait certificate; it does not assert future quiescence.

Controls cover publication before buffer/physical jobs, refusal of independent
publication observation and raw install/cleanup/exit/cancellation bypasses,
mode/flow-sensitive outbound tracer selection versus inbound tracer selection,
foreign-pool body results, globally fresh captured mux-job identities even after
deregistration, and another pool forking during the first parent's insertion gap.
The birth-policy control with an overwritten mutable CM entry is a conditional
snapshot; the real initialized paths are labeled separately. Negotiation return,
local buffer/bearer/setup boundaries and child body outcomes remain explicit
component observations, not implementation refinement or eventuality claims.

Checker repairs concerned local names colliding with existing constructors;
there was no old-rule change, theorem weakening, heap increase or new trust
assumption. Final three-file local proof audit: zero findings. Tracked diffs and
new-file whitespace checks passed. ConnectionHandler, Mux and JobPool exports
were compared again with the pinned Git objects. No Haskell replay, source-pin
migration, unrelated proof build or commit was performed. Logs are
`/tmp/cm-review-20261027/si4-mux-handler-{rules,properties,negative,negative-final}.log`.
All work after `2c39700` remains uncommitted; `.claude` remains untouched.

Next executable obligation: extend each captured startup's SAME physical pool
with directional/generation mini-protocol jobs and an exact result sum that can
also represent muxer/demuxer outcomes. Bind protocol fork/start, body result,
queue publication and deregistration to actual source operations without using
legacy runningJobs/finishedJobs cells as physical identities. Then permit mux
monitor processing through that adapter, including interruptible MiniProtocolJob
group cancellation, final pool close/joins, async-vs-normal tracer ordering and
buffer release before CM finalizer entry. Masked setup/startup failure and
interruption branches need their real unwind, too. Preserve independent actors,
per-parent insertion masks and late admissions while integrating outer scopes.
SI4/SI5 and full shutdown remain open.


## SI4 fifth increment: physical protocol generations in the same pools

`MuxProtocolJobs` instantiates the existing handler/startup wrapper with
`MuxJobTypes.TypedResult`: muxer and demuxer outcomes plus protocol direction,
number, generation and outcome. Protocol forks extend each captured frame's
existing `Startup.pool` through real JobPoolKernel transitions. They do not
initialize a second pool or reconstruct physical threads from running flags.
Captured protocol metadata binds JobId to owner handler, mux, direction, number
and fresh generation. Clean slot completion permits a new generation; error
completion leaves that slot busy, even after publication/deregistration.

Responder creation requires the actual selected forkPending callback and couples
`IG.forkResponder` with the physical Pool.fork. Parent insertion is a separate
step. Initiator creation is an explicit observed source miniProtocolJob fork:
known configured number, readiness, slot and pending-work guards are checked,
but the legacy PeerActions running flag is not used as evidence. Initiator
command selection, directional capability and peer result-action integration are
still boundary contracts rather than proven frontend histories.

`protocolReturned` records return from the protocol action; `commitClean` is the
explicit Wanton-drained readiness observation and actual responder completion/
status commit. The egress byte queue itself is not modeled by that observation.
Synchronous errors bypass the wait and preserve non-Idle status. Local completion
commit leaves the physical bodyRunning. `returnProtocol` separately records the
JobResult return to JobPool, and only then can `publishProtocol` queue its exact
typed result. Deregistration and Async result publication remain separate. This
exposes the post-completion unmasked body window for future cancellation; it does
not assume every committed completion will eventually be queued.

New `IG.publishJobOccurrence mid index` removes one exact finished occurrence.
The old number-based action remains unchanged for old profiles. The adapter
tracks responder pending JobIds in append order, locates the selected physical
job, checks its source number/outcome and typed direction/generation/outcome,
then couples source occurrence publication with that job's Pool publication.
A newer run can therefore publish before an older preempted run of the same
number. Initiator outcomes publish to the authoritative physical pool and local
completion metadata; they do not fabricate a PeerActions or OutboundMachine
initiator writer. The legacy mux completion list is only the responder projection
here, not the complete shared queue.

Infrastructure results also use the same typed pool, including inside their
parent insertion gaps. Arbitrary inherited child-result input and raw monitor/job
bypasses are blocked. Typed controls allow command selection, on-demand start and
tracer continuation only after physical startup, respecting the selected owner's
parent insertion gap and physical result priority. A previously selected start
may finish tracing/forking after a result arrives. There is no result-consumption,
group-cancel, cancellation/unwind, pool-join or handler-finalization shortcut.

`Properties/MuxProtocolJobs` projects every successful step and finite execution
to actual OutboundMachine executions and actual selected-handler Pool executions.
New protocol forks cannot be projected through the older startup-only grammar;
the proof uses JobPoolKernel directly. The selected pool starts empty at the real
initializer. Existing pending-capture and combined runtime/supply facts lift
through the actual source trace with their original premises.


Local checked observations additionally retain the physical fork metadata/source
callback (or explicit initiator-fork contract), completion commit and unchanged
pool/bodyRunning window, actual body return, exact typed publication, and selected
responder ordinal/source occurrence. They are instantiated in the acceptance
endpoint together with source/pool execution and capture/supply certificates.

Validation on 28 October 2026 used Agda 2.8.0 and `+RTS -M2G -RTS`, sequentially,
with no final warnings. The two new runtime/type modules, final property endpoint,
new occurrence controls and final protocol-job acceptance all had fresh Checking
output. The modified old proof statements were retained and checked through
Properties/{HandlerIG,IGRetention,OriginMonitorInvariant}; existing
Negative/TracerAttachment also passed. It initially failed only because the
sandbox could not refresh an external csp-ptree interface; an explicitly escalated
retry succeeded without dependency source edits.

The new Negative/MuxProtocolJobs endpoint contains 142 named reflexivity controls.
Its initialized 38-action physical birth/publication/caller/IG-queue/startup prefix
feeds a 13-action fast responder run that commits, returns and queues before
parent insertion, then inserts/deregisters/publishes its Async result. Other
initialized model executions cover same-number opposite directions, a clean
initiator restart before the older body return with newer error publication first,
mixed infrastructure/protocol outcomes, early infrastructure publication before
insertion and completion of an already selected start after a result arrives.
The responder same-number ordinal-overtaking suffix uses an explicitly
conditional frontend request after a genuine older clean commit; it is not an
initialized ordinary-IG restart witness. Source IG normally restarts from the mux
completion trace. Five separate ProtocolJobOccurrence controls check indexed
publication, retained older data, legacy compatibility and refusal cases.

The first acceptance import closure exhausted 2 GB in CSP/InboundRelease before
reaching the new scenarios. New data-only Negative/MuxProtocolFixtures removed
the heavy CSP/old-negative dependency while preserving actual initialized steps
and all intended controls; no heap increase or case deletion was used. The older
CSP/InboundRelease endpoint was subsequently checked **in isolation**, freshly at
the same 2 GB limit, and passed. Final test imports therefore remain cheap rather
than relying on that whole expensive closure. Compiler repairs were local names,
nested-with scope and equality transport, not weakened statements or disabled
checks. The source audit also prompted the clean commit/body-return split before
final checking, preserving the future cancellation window.

The final thirteen-file local proof audit found three heuristic question-mark
hits, all inspected pre-existing natural-number decision operators in
IGRegistration (two ≤? and one <?), and no actual holes or unsafe additions.
Tracked and all six new files' whitespace checks passed. Mux/JobPool exports were
compared against the unchanged pin. No Haskell replay, source-pin migration or
commit was performed. Logs are under `/tmp/cm-review-20261028/`:
`protocol-occurrence-{handler,retention,origin,negative,tracer}.log`,
`protocol-jobs-{types,rules,properties,negative,negative-final}.log`, and
`protocol-jobs-inbound-release-isolated.log`. Earlier failed attempts were
reported; successful retry logs contain final results. All changes after
`77cc590` remain uncommitted and `.claude` is untouched.

Next: consume the typed physical FIFO head through a verified mux-monitor bridge,
including infrastructure failures and the responder projection/initiator result
bridge. Do not let the legacy responder-only list skip a preceding physical
infrastructure or initiator item. Group decisions must count the current physical
registered MiniProtocolJob subset, not historical metadata or protocol slot
activity. Then implement distinct interruptible group cancel/join, full pool
shutdown, buffer release and captured CM finalization. Cancellation after clean
completion but before body return must retain the committed completion/status
while producing no queued normal/error JobResult; exact pending-occurrence
bookkeeping must remain aligned. Synchronous exception-handler and post-return
masked publication regions also need their correct delivery guards. SI4/SI5,
outer scope integration and full shutdown remain open.


## SI4 sixth increment: typed FIFO monitor handling

The preceding protocol-job increment is committed as `a641636`. The requested
commit-first phase completed before this new work; its only amendment removed an
extra blank EOF line and final staged whitespace passed. Prior Agda evidence was
not rerun solely for that commit.

`JobPoolKernel.consumeCompletion` now removes one actual WithQueue head while
the pool is open. Empty, queue-free and closing pools refuse it. Existing generic
close statements are unchanged: queue removal preserves captured-handle and
closed-registry facts. `IGRegistration` adds status-only failure/stopped writes
and a separate Dead trace; lifecycle/retention coverage includes those operations
in both appropriate runtime modes. Old legacy completion actions are unchanged.

`MuxResultMonitor isBearerClosed` consumes the authoritative physical FIFO head
into a per-handler held state, then handles it in a separate event. The selected
responder generation/outcome is matched against its captured job and legacy
responder head before invoking the real source monitor action. While held, that
responder item remains in the legacy projection until handling; the representation
relation includes the held item as well as the remaining physical FIFO. Initiator
and infrastructure heads never consume an unrelated responder projection item.

Status writes precede error/Dead tracing. Responder errors complete their actual
exception-tracer callback and afterFailure continuation before the separate Dead
trace. Initiator completion traces ignored by IG are explicit local observations;
clean traces include DeltaQ before continuation, while error DeltaQ follows Dead.
Muxer errors always fail. Demux BearerClosed stops normally only when the CURRENT
registered MiniProtocolJob count is zero at handling. Counting ignores historical
removed jobs and slot activity; it includes completed/published jobs still in the
physical registry. The classifier parameter is an explicit source-exception
contract, not derived from the numeric ErrorId.

The owning monitor cannot resume commands/forks or select another item while
handling/tracing/finished. Independent child return, publication, insertion and
removal and other actors retain their original guards. Handling has no queue-empty
precondition: new results can arrive while the selected item is held. Normal or
failed monitor finish requires actual Dead callback return and matching mux
status, and changes only its local PC. It does not certify an empty queue, closed
pool, released buffer or parent handler Async result.

`Properties/MuxResultMonitor` projects every step/finite execution to real
OutboundMachine and selected-handler JobPool executions; initialized pool,
capture and runtime/supply corollaries retain their original premises. Local
Dequeue evidence retains the exact original head/tail, actual kernel removal and
stored selected value. Handle evidence retains captured generation matching,
actual source effects, the current registry/job captures and group count at that
step, and the classifier/count choice. Finished evidence retains actual callback
return, matching status and an unchanged underlying runtime.

Validation on 28 October 2026: the new model, property and final acceptance
endpoints passed with fresh Checking output in Agda 2.8.0, with
`+RTS -M2G -RTS` and no final warnings. Helper/kernel checks and regressions passed:
Properties/{JobPoolCloseKernel,HandlerIG,IGRetention,OriginMonitorInvariant},
new Negative/MuxMonitorEffects (13 named controls and two old close-certificate
applications), and existing Negative/{JobPoolLifecycle,WithoutQueuePool,
ConcurrentPool,TracerAttachment}. Kernel/source rule changes were checked
transitively; the final property/acceptance checks were fresh. One consume test
attempt was interrupted after process overlap was noticed; the final consume
check and remaining regressions ran individually and passed. No concurrent Agda
process remained afterward.

Negative/MuxResultMonitor contains 145 named reflexivity controls and initialized
main paths for clean/error results in both directions, infrastructure results,
current-registered count versus inactive/removed history, and the dequeue/count
race: mini count one at dequeue, child publication/deregistration, count zero at
handling, normal Stopped/Dead finish with a protocol tail still queued. A new child
publication during a blocked callback is also an actual initialized execution.
Wrong projection/generation fixtures are conditional controls. Unrelated-owner
controls check delegation guards, not successful execution of a nonexistent
second owner. Six local certificate applications and generic source/pool/capture/
supply applications passed against those paths.

An initial acceptance check exhausted 2 GB while expanding chained computed
snapshots. Flat explicit snapshots resolved it without raising the heap limit or
removing any case. Remaining checker repairs concerned local names, fixture
parentheses, exhaustive patterns and equality transport, not weakened statements
or altered model guards. The final thirteen-file local audit had only the three
known pre-existing Nat ≤?/<? operator false positives in IGRegistration, no actual
holes or unsafe additions. Tracked and four new files' whitespace checks passed,
including exactly one EOF newline. Pinned Mux/JobPool exports were verified.
No replay, source-pin change, unrelated build or second commit was performed.
Logs: `/tmp/cm-review-20261028/typed-monitor-{close,retention,source-retention,origin,
consume,queued,queuefree,concurrent,tracer,rules,properties,negative,negative-final}.log`.
The first chained-fixture failure is historical; final logs retain passing runs.
New work after `a641636` is uncommitted; `.claude` remains untouched.

Next is the distinct interruptible MiniProtocolJob group cancel/join operation,
using a one-shot snapshot of CURRENT registered protocol handles. Keep muxer and
demuxer alive during graceful egress drain, then perform the outer whole-pool
snapshot/cancel/join before buffer release and captured CM finalization. Async
cancellation of the owner during group cancellation/drain must abandon that
cursor and enter whole-pool unwind, immediately disabling its normal continuation
before the later async Failed write. Preserve committed clean completion without
fabricating a queue result if delivery precedes body return. Old normal/sync
masked publication can outrun cancellation. Monitor-local finished remains only
a prerequisite: actual pool/buffer/body outcome and rethrow-policy effects still
need coupling before parent Async results, outer scopes and SI5 full shutdown.

## SI4 seventh increment: group shutdown and distinct whole-pool close

`MuxGroupShutdown isBearerClosed` layers over the same captured physical pools
and typed monitor. Actual stop callers append CmdShutdown without a status or
tracer-return guard; enqueue remains available before physical startup, while a
callback is pending, and after monitor return. Selection still requires settled
parent insertion and the monitor's physical result priority. Stopping trace,
status write and current-registered MiniProtocolJob snapshot are separate steps.
The group cursor requests, delivers and joins sequentially while the underlying
pool remains open. It targets captured protocol jobs only; slot activity and
historical job tables do not define membership.

Unmasked body cancellation uses a real kernel interruptJob step and actual child
unwind, deregistration and Async-result boundaries. A clean commit before body
return can be cancelled without any typed queue result; exact ghost occurrence
removal preserves the source Idle/result commit. Synchronous jobHandler capture
refuses ordinary async delivery, allowing normal masked publication to win.
Explicit observed synchronous unwind replacement can instead enter the actual
protocol error path before an ordinary result is queued. Delegation guards prevent
an interrupted body from resuming its old return/commit continuation. Independent
children, other owners and ordinary source actors keep their existing guards.

Group completion permits observed empty egress or timeout, then Stopped and
TraceStopped. **Correction, 28 October (SI4-F1):** the pinned IG tracer handles
TraceStopped by publishing MuxFinished and clearing counters. The original
adapter omitted that callback; the twelfth increment below corrects it and
updates these initialized graceful witnesses. TraceStopped does not close the pool or emit
a TraceState Dead event. Monitor return or
observed owner abort enables a separate actual Kernel.beginClose snapshot of all
CURRENT registered jobs, including infrastructure, followed by sequential
uninterruptible cancellation/joins and actual finishClose. Owner abort seals the
normal cursor immediately; its Failed write and Dead trace wait for whole-pool
closure. An abandoned group cursor is not silently completed by that operation.
Removed history is outside the whole snapshot even when its Async result has not
arrived. ScopeDone records only this local outcome and pool closure.

`Properties/MuxGroupShutdown` projects every step and finite execution to actual
OutboundMachine and each selected physical JobPool execution. It lifts initial
pool, capture and supply facts with unchanged premises. The initialized
whole-closed-from-initial theorem certifies result availability for precisely the
actual whole-pool snapshot. Local observation records expose exact group capture,
eligible delivery, available-result join, actual unwind intermediate, owner-abort
stuttering, and actual whole-pool begin/finish steps. They do not yet establish a
separate global all-group-snapshot terminal invariant.

Source mapping and limitations are recorded in the SI4 source audit's
“Interruptible group shutdown and whole-pool unwind” section. Buffer release,
captured CM cleanup, proper handler body outcomes/rethrow policy and parent Async
completion remain the next integration obligations. Startup/tracer interruption
and remaining Server/IG/outer scope histories remain open. SI4/SI5, CM-I4c and the
overall G0–G5 objective are still in progress.

Validation on 28 October 2026: the new model and full properties endpoint passed
fresh Agda 2.8.0 checks using `+RTS -M2G -RTS`, exit zero without warnings. The
property check includes the appended delivery, join, abort and whole-close local
observations (`group-shutdown-properties-final.log`). The initial and extended
flat acceptance matrix and final theorem applications passed fresh at 2 GB
(`group-shutdown-negative.log`, `group-shutdown-negative-final.log`). No heap
increase or case deletion was used.

Shared helper changes passed the close/retention/origin endpoints and existing
Negative/{JobPoolLifecycle,WithoutQueuePool,ConcurrentPool,TracerAttachment}
regressions. New Negative/MuxGroupEffects has 19 conditional helper controls;
these require the adapter to supply ordering. External enqueue additions were
rechecked through affected retention/origin/effects/tracer endpoints. Logs are
`/tmp/cm-review-20261028/group-shutdown-{rules,properties,properties-final,close,
retention,igretention,origin,effects,queued,queuefree,concurrent,tracer}.log` and
`group-shutdown-enqueue-{retention,igretention,origin,effects,tracer}.log`.
Checks ran one Agda process at a time. No Haskell replay, source-pin change or
unrelated proof build was performed. All new work after `a641636` remains
uncommitted; `.claude` is untouched.


Negative/MuxGroupShutdown composes actual initialized paths for the 30-step
normal group/drain/whole-close suffix, committed clean cancellation with timeout,
masked error publication winning cancellation, explicit synchronous unwind
replacement, independent infrastructure publication, 25-step group-abort and
20-step removed-history-abort suffixes, and drain interruption. It checks physical
FIFO priority, actual stop enqueue before startup and the masked insertion gap.
The main paths use no injected conditional source worlds; unwind, drain and trace
observations remain explicit contracts. Generic source/pool/capture/supply results,
three initialized whole-snapshot terminal certificates and the local observation
records are applied to these paths. The removed-history example deliberately
retains a deregistered handle without an Async result after whole close.

Final audit scanned all seventeen pending Agda files: only three inspected
pre-existing Nat decision operators in IGRegistration were reported, with no
actual holes or unsafe additions. Tracked/new-file whitespace checks passed,
including exactly one EOF newline. These are local proof/source checks, not a
term-level audit of all dependency assumptions or implementation replay.

## SI4 eighth increment: buffer scope, captured CM finally and parent results

`MuxHandlerExit isBearerClosed` extends the same group/monitor/protocol/startup
state without creating another pool or adopting existing handler records. A
successful mux owner's physical history stays in the original registry; a new
exit record carries typed outcomes that the earlier ErrorId-only pre-handshake
phases cannot represent. Normal return, async exception, original synchronous
exception and peer-wrapped exception remain distinct.

Exit starts only after actual mux ScopeDone and closedPool, using the original
startup frame's HandlerStart and matching source registration. Observed buffer
scope return preserves that mux outcome. An observed provider exception can
replace it, and cannot be used to turn an exception into normal success. Since
withBuffer is a supplied callback, these observations are provider contracts,
not a proof of concrete memory release. Synchronous failures then enter the
captured-context rethrow-policy boundary and require the error trace to return.
ShutdownPeer rethrows ExceptionInHandler; ShutdownNode requires observed main
receipt before rethrowing the original error. Async failures bypass this classifier.

The adapter invokes actual OutboundMachine handlerExit and cleanupStep actions,
retaining map acquisition, captured entry selection, socket close, prospective
map publication/restoration, TIME_WAIT finally and counter reads. Each cleanup
operation checks the original HandlerStart against the source registration.
Cleanup failure overrides the body outcome outside the already-exited classifier.
The local frame records whether the actual failure operation was synchronous
socket close or asynchronous TIME_WAIT interruption, and matches its ErrorId at
completion. Shared CleanupOutcome alone cannot establish that exception class.
Parent result availability requires actual cleanupDone, the matching local
cleanup-completion stage and explicit Async-result publication. resultOf exposes
the typed value only after that publication.

CM snapshot capture/read/send/collective wait use the same coordinator in the
physical-handler state. Delivery to a waiting/group/draining mux is coupled to
actual owner abort before acknowledging throwTo; TIME_WAIT delivery executes the
actual cleanup interruption before acknowledgment. The result oracle combines
the new successful-mux exit records with the old pre-handshake physical history.
The old pre-handshake final-wait bypass is disabled in this adapter. A completed
pool, send acknowledgment, cleanupDone or removed map entry alone cannot satisfy
the successful owner's result observation. Independent admissions, source actors,
children and other owners remain enabled under their existing guards.

`Properties/MuxHandlerExit` projects all steps and finite executions to actual
OutboundMachine and selected physical JobPool histories, retaining initialized
capture and supply premises and whole-snapshot terminal certificates. Publication
observations retain the actual cleanupDone result and local predecessor. Its
PhysicalWait retains the actual wrapper finishClose call, exact combined result
oracle and primitive final-wait observations. These local certificates do not
assert global all-history termination or eventual progress.

The remaining profile gaps include CM delivery in buffer/policy/trace windows,
setup/startup and custom tracer failure/unwind, plus outer Server/IG/governor
histories and admission quiescence. Normal error-trace return and node delivery
are still observations, not a node-exit theorem. SI4/SI5, CM-I4c and G0–G5 remain
open. Source mapping: the SI4 audit's “Buffer scope, handler outcome and CM finally”
section. All work after `a641636` remains uncommitted.

Validation on 28 October 2026: Agda 2.8.0 checks passed at `+RTS -M2G -RTS`,
exit zero without warnings, for the new runtime, Properties/MuxHandlerExit,
Negative/MuxHandlerExitFixtures and all three acceptance endpoints:
Negative/{MuxHandlerExit,MuxHandlerExitOutcomes,MuxHandlerExitCM}. The final
property and acceptance checks have fresh Checking output. The runtime was also explicitly freshly checked after invalidating only its own
interface (`handler-exit-rules-final.log`);
source comments and documentation were not used as a reason for unrelated builds.
No old theorem type, transition or build setting was changed in this increment.

Initialized paths cover normal and async mux outcomes through actual CM cleanup
and parent Async publication; both peer/node rethrows after an observed buffer
exception; socket-close failure with map restoration before publication; and the
combined CM snapshot/read/send/owner-abort/whole-pool-close/CM-finalizer/result-wait
path. It refuses collective close before result publication, early finalizer or
result shortcuts, async classification and node rethrow before delivery. Generic
source/pool/capture/supply results and actual Publication/PhysicalWait certificates
are applied. The separate TIME_WAIT delivery/finally/counter/result fixture is
explicitly conditional on an already-entered finalizer, not an initialized trace.
Buffer, policy, trace-return and node-delivery observations remain contracts.

Several initial checks exhausted the 2 GB heap while elaborating helpers and
re-exported controller aliases at the concrete classifier. Generic lift helpers,
shared-state snapshot builders and private internal module aliases resolved that
cost; acceptance was split by responsibility. No case was removed and no heap or
safety setting was relaxed. Final logs are in `/tmp/cm-review-20261028/`:
`handler-exit-{rules-final,properties-final,fixtures,negative-final,outcomes,cm}.log`.
Scratch probes and earlier checks are historical diagnostic evidence, not final
acceptance. The final runtime log retains its fresh Checking line.

The final pending-worktree audit scanned 23 Agda files: only the three previously
inspected Nat decision-operator false positives in IGRegistration were reported;
all six new exit-layer files had zero findings. No holes or unsafe additions.
Tracked/new-file whitespace and exactly-one-EOF-newline checks passed. Pinned
source objects were compared locally; no Haskell replay, source-pin change,
commit, push or unrelated heavy proof build was performed. `.claude` is unchanged.

## SI4 ninth increment: observed post-mux cancellation windows

Commit-first completed as `a173dd0` (26 files), bundling typed FIFO monitoring,
group/whole-pool shutdown and handler exit. Prior successful checks were not
rerun solely for that commit; staged whitespace passed. `.claude` was excluded.
The following cancellation-window work is uncommitted after that anchor.

`MuxExitCancellation` shares MuxHandlerExit.State directly. It adds observed
interruptible buffer-provider, classifier error-trace and node-send delivery;
there is no second registry, JobPool or source configuration. Buffer delivery
retains the provider-unwind boundary with an async outcome. Classifier-trace/send
cancellation seals that continuation and exits the handler with the new async
exception. A separately observed synchronous error-trace exception escapes as
the new original synchronous error, without reclassification or the old peer
wrapper. Provider teardown can still replace pending cancellation with a new
synchronous error. No post-Mx.run cancellation invents a mux Failed/Dead write.

Pure masked policy selection/rethrow and uninterruptible finalizer stages are
not generalized delivery points. Named windows are operation/mask contracts;
provider/tracer implementation masks are not derived from a numeric ErrorId or
from the phase alone. Interrupted node send does not certify main nonreceipt,
exception retraction or node exit. The old explicit TIME_WAIT interruption and
finished-target acknowledgment keep their separate source guards.

CM delivery takes the actual awaitDelivery target, records the same observed
operation delivery, then performs actual coordinator acknowledgment. The sender
still cannot finish the collective wait until the provider/body/CM finally and
explicit parent Async-result publication settle. `Properties/MuxExitCancellation`
projects all steps and finite executions to actual OutboundMachine and selected
JobPool traces; initialized capture/supply and whole-snapshot facts retain their
old premises. Delivery and ShutdownDelivery records retain exact predecessor,
window, receiver, intermediate and acknowledgment. The final wait reuses the
checked physical-result oracle and its actual wrapper call.

Validation on 28 October 2026: Agda 2.8.0 runtime, properties and acceptance checks
passed at `+RTS -M2G -RTS`; the final property and expanded acceptance checks were
fresh, exit zero without warnings. The runtime was also checked transitively
after its explicit helper type declarations. Logs:
`/tmp/cm-review-20261028/exit-cancellation-{rules,properties,negative,negative-final}.log`.
Private internal module aliases keep the concrete proof layer small. No heap or
safety setting was changed, and no previous theorem statement was weakened.

Negative/MuxExitCancellation has actual initialized paths for buffer cancellation
through provider return, CM cleanup, Async result and collective close; classifier
trace and blocked node-send cancellation through actual cleanup/result publication;
and a synchronous error-tracer exception through cleanup/result publication.
Actual CM snapshot/read/send/delivery/ack prefixes are also checked for the tracer
and node-send windows. Refusals cover pure masked stages, wrong windows, stale
tracer/policy/send continuation, premature finalizer and premature collective wait.
Generic source/pool/capture/supply, exact delivery and physical-wait certificates
are applied. A provider-finalizer replacement step uses the initialized buffer
prefix. Source callbacks and exception-delivery observations remain contracts.

All three new Agda files passed the scoped proof audit with zero findings.
Tracked/new-file whitespace and exactly one EOF newline passed. Pinned Core and
ConnectionHandler exports were compared locally. No Haskell replay, source-pin
change, unrelated proof build, push or second commit was performed.

Next: post-publication setup/startup and mux/IG-tracer failure/unwind, before
outer Server/IG/governor histories. Keep actual fork/insertion gaps and current
whole-pool snapshots; no fabricated successful startup or pool/body result may
bridge a setup failure. Admission quiescence and full shutdown remain separate.
SI4/SI5, CM-I4c and overall G0–G5 remain open.

## SI4 tenth increment: partial startup and synchronous mux-tracer unwind

`MuxStartupUnwind` layers over the same cancellation/handler state, physical
handler history and queued pools. It records the original published handler,
mux identity, partial startup PC, callback at failure, exception class and lexical
scope route. Its exception type has only synchronous/asynchronous failures;
there is no fabricated successful-body outcome. The three routes distinguish
failure before provider callback invocation, failure inside its buffer scope
before pool acquisition, and failure inside an acquired JobPool bracket.

Named setup sites cover buffer/bearer setup, TraceStarting, egress/label setup,
pool acquisition, infrastructure forks before birth, Mature and timeout setup.
The model refuses ordinary async delivery in existing fork/insertion gaps. A
selected fault immediately seals that owner's startup/monitor controller while
independent children, other owners and ordinary source actors keep their guards.
The partial startup PC is retained even after physical parent result publication;
it is not rewritten into monitoring or G.ScopeDone to reuse an exit gate.

An entered pool closes through actual current-registry beginClose, sequential
cancellation, child unwind/removal, Async-result joins and finishClose. Synchronous
failure then leaves the mux's prior status/callback intact and hands a failed
body to the buffer scope. It does not invent Failed/Dead. Startup async delivery
inside that bracket instead closes the pool BEFORE actual Failed/Dead/rethrow;
pre-catch delivery does not enter that later catch. A synchronous exception from
the catch's own tracer replaces the original async outcome without re-entering
the catch or rewriting its Failed value. Before buffer callback invocation the
handoff goes directly to body classification; otherwise provider unwind remains
outstanding. The existing typed policy/CM-finalizer/parent-result sequence is
reused, including the actual CM send acknowledgment and collective result wait.

For monitor tracing, caller mux-tracer entry is distinct from IG STM failure.
The new guard permits the first custom tracer leg or actual tracerFailed evidence,
plus the existing explicit initiator trace observation. A pending commitTrace
alone is not an exception certificate. The conditional successor-registration
control executes real IG.commitTracer, including prefix/retry precedence, before
observing the descriptor exception. Callback failure is retained rather than
changed into a successful return. Source audit details are in the SI4 audit's
“Partial startup and synchronous mux-tracer unwind” section.

`Properties/MuxStartupUnwind` projects every plan, successful action and finite
execution to actual OutboundMachine and each selected physical JobPool history.
Initial capture/supply and current whole-snapshot terminal facts keep their
premises. Selection retains the real owner lookup, settled parent insertion,
successful publication, exact mux lookup, scope route and original callback.
PhysicalWait retains the actual nested wrapper finishClose call and the combined
physical-result oracle. These are operational/source-contract certificates, not
universal progress or implementation refinement.

Acceptance is split into data-only Fixtures and five acceptance endpoints:
Negative/MuxStartupUnwind, Branches, Interleavings, CM and Sites. Initialized
paths cover two-engine Mature failure through actual close, provider exit,
peer rethrow, CM finally and parent result; pre-buffer and bearer failure;
zero-engine startup async close/Failed/Dead/finally/result; pre-catch cancellation;
all named setup and graceful stopping/stopped trace sites; and custom monitor
tracer failure through the actual pool close. The masked-gap path publishes an
infrastructure result before insertion, waits to remove it, then closes an empty
current snapshot while its removed historical Async result is still unavailable.
A separate initialized CM path captures/reads/sends, acknowledges startup delivery,
then waits through pool/provider/finalizer/result before collective close. The
successor-registration descriptor control is conditional, not an initialized
second-handler history. An initialized exception from async-catch Dead tracing
retains the original Failed status and hands off the replacement sync error.

Next remains async mux/IG callback delivery, some ignored/DeltaQ tracer windows,
post-close catch cancellation, earlier allocation/publication gaps and additional
child-finalizer failure classes, followed by outer Server/IG/governor histories.
Named helper/provider/trace faults are observations; their unmodeled internal
resources and mask implementations are not proved by the fault label. Admission
quiescence, full shutdown, SI4/SI5, CM-I4c and overall G0–G5 remain open.

Validation on 28 October 2026: all eight new modules passed Agda 2.8.0 with
`+RTS -M2G -RTS`, one process at a time, exit zero without warnings. The runtime
was freshly rechecked through the tightened-tracer interleavings closure; the
final properties, fixture and acceptance closures have Checking output. Final
commands used Properties/MuxStartupUnwind and
Negative/{MuxStartupUnwind,MuxStartupUnwindBranches,MuxStartupUnwindInterleavings,
MuxStartupUnwindCM,MuxStartupUnwindSites}. Imports checked the runtime and generic
fixture transitively. One larger property recheck initially exhausted 2 GB while
freshly checking the changed runtime; the subsequent serial interleavings check
completed that runtime/property/fixture/main closure at the same limit. No heap
increase, scenario removal or safety relaxation was used. Checker repairs were
local scoping/equality transport and exact wrapper projection, not weakened goals.
No old model or theorem statement was changed in this increment.

Logs are in `/tmp/cm-review-20261028/`:
`startup-unwind-{rules,properties,properties-final,fixtures,negative,branches,
interleavings,interleavings-final,cm,cm-final,sites,sites-final}.log`.
Earlier logs are historical where a later final log supersedes them. Eight-file
local proof audit: zero findings. Tracked/new-file whitespace and exactly one EOF
newline passed. Exact pinned source objects were compared locally; there was no
Haskell replay, upstream/pin change, unrelated build, commit or push. This and the
preceding cancellation-window increment remain uncommitted after `a173dd0`;
`.claude` is untouched. Source-fidelity and finite model evidence remain separate
from implementation replay and a term-level audit of dependency assumptions.


## Eleventh increment: async mux/IG callback interruption (28 October 2026)

`MuxStartupUnwind.unmaskedMuxCallback` observes async delivery at a published,
monitoring owner with a settled fork/registration gap. Callback read/STM and
post-commit continuations retain their exact source snapshot. Selection changes
only fault metadata; `Properties/MuxStartupUnwind.cancellation-keeps-base` proves
that the source, pool and held monitor state are unchanged. Existing controllers
are sealed for that owner while physical children and other actors can proceed.
The original callback is not cleared to Returned to satisfy an exit guard.

The real current-pool snapshot must close before the catch writes Failed.
Separate `recordInterruptedMuxFailure` and `traceInterruptedMuxDead` operations
preserve the old successful-return guards. The status write leaves the abandoned
callback intact; the subsequent operation invokes a new Dead callback, retaining
the original callback in the fault record. Its queue/counter transaction can retry.
Provider unwind, the captured CM finally and physical Async-result publication
remain required. The existing source/pool execution projections, initialized
capture/supply and snapshot-terminal certificates cover the new actions.

Initialized acceptance paths cover a held responder completion at its pending
IG STM transaction, and a start tracer after its atomic counter/event burst has
committed but before a protocol fork. The former does not commit the interrupted
transaction; the latter does not roll back the already committed burst. Both
close the actual infrastructure snapshot and invoke Failed/Dead in order.
`Negative/MuxCallbackCancellationCM` additionally drives the CM snapshot/read/send,
actual callback delivery acknowledgment, collective wait, buffer exit, original
CM cleanup and physical parent result. Delivery and pool close cannot shortcut
the remaining cleanup/result obligations. Queue-full Dead retry controls are
conditional snapshots, not initialized queue-saturation witnesses.

The exact pinned Mux, JobPool, ConnectionHandler and InboundGovernor source
objects were byte-compared with the local audit exports. Mux.hs:254–279 places
the async catch after the pool bracket; InboundGovernor.hs:635–720 uses an active
read followed by atomic event/counter effects. Delivery observations and provider/
mask contracts remain explicit. No implementation replay or full-shutdown claim
follows from these finite model executions.

### Newly verified source-fidelity issue SI4-F1

The earlier audit incorrectly called TraceStopped ignored by IG. At this pin,
Mux.hs:565 emits TraceStopped; InboundGovernor.hs:719–728 routes it to the same
MuxFinished/counter-clear STM branch as TraceState Dead. The current
`MuxGroupShutdown.observeTraceStopped` is only a local phase change and skips
that effect, retry and interruption boundary. Its initialized graceful examples
therefore cannot be presented as complete source-faithful graceful shutdown.
The correction is required before extending those graceful claims: model the
actual callback invocation, active sample, atomic commit/retry, and return before
monitor return/whole-pool close. Preserve existing Failed/Dead distinctions.
This finding changes the next task's priority; the current async-callback paths
start from non-graceful initialized monitor histories.


Validation for the eleventh increment: Agda 2.8.0 checked thirteen targeted
endpoints serially with `+RTS -M2G -RTS`, all exit zero without warnings:
`Properties/{SubsystemSupply,SubsystemReferences,OriginMonitorInvariant}`,
`MuxStartupUnwind`, `Properties/MuxStartupUnwind`,
`Negative/{MuxCallbackCancellation,MuxCallbackCommitted,MuxCallbackCancellationCM,
MuxStartupUnwindBranches,MuxStartupUnwindInterleavings,MuxStartupUnwindCM,
MuxStartupUnwindSites,MuxGroupEffects}`. Each final log contains its Checking
line. Two aggregate fresh-dependency/property attempts exhausted 2 GB; checking
the runtime separately and then its property closure succeeded at the same limit.
No scenario was removed, statement weakened, heap increased or safety disabled.

The thirteen-file static audit flags three existing question-mark comparison
operators in IGRegistration (≤? and <?), verified unchanged from HEAD, rather
than proof holes. No new holes, postulates or checker bypasses were introduced.
Whitespace and one-EOF checks pass for all sixteen changed/new source and
documentation files. Final logs are `/tmp/cm-review-20261028/callback-final-*.log`;
`callback-properties-cold-heap.log` preserves the final aggregate heap failure,
and `callback-proof-audit.log` records the heuristic audit. No checker remains
running. These changes are uncommitted after `d47f109`; `.claude` is untouched.
No Haskell replay, source-pin change, full-system shutdown proof, commit or push
was performed. Next: correct SI4-F1, then resume the remaining callback/failure
windows and outer Server/IG/governor composition.


## Twelfth increment: SI4-F1 graceful TraceStopped correction (28 October 2026)

Rechecked exact pinned Mux.hs and InboundGovernor.hs against the audit exports.
Mux.hs:555–570 writes Stopped before TraceStopped; InboundGovernor.hs:719–728
recognizes TraceStopped and TraceState Dead with the same active-gated,
atomic MuxFinished/counter-clear transaction. This fixes the source-fidelity
issue identified in the eleventh increment; the network pin is unchanged.

`Rules/IGRegistration.traceGracefulMuxStopped` identifies the real graceful
source event separately from `traceMuxDead`. `MuxGroupShutdown` now enters
`stoppedTracing`, samples active, attempts the real tracer transaction, and
requires its returned callback at Stopped before `finishStoppedTrace` permits
monitor return. Only then may whole-pool closure start. A full queue retries;
no callback return, counter clear, notification or normal pool exit is invented.
The callback itself does not join or close the still-live infrastructure pool.
No-IG attachment and an attached inactive tracer remain distinct branches.

`Properties/MuxGroupShutdown.StoppedReturn` and `finish-stopped-observation`
expose the exact owner/mux lookups, Stopped status, returned callback, and next
phase of every successful graceful return. Generic source/pool execution
projections cover each new action; initialized capture/supply and snapshot-result
certificates retain their original statements. Mux retention, handler chains,
subsystem references and origin classification cover the new source operation.

Initialized normal, clean-cancellation, error-publication-race and unwind-error
witnesses now include the callback's invocation, active sample, commit and
return. Their post-callback snapshots retain the notification and cleared
counters through whole-pool close and downstream CM cleanup. The old acceptance
claim that source state was unchanged by TraceStopped was false at the pin; it
is replaced by explicit Stopped-status and MuxFinished-publication checks.

`Negative/MuxStoppedTracer` checks blocked return/closure at each boundary,
100-slot retry versus 99-slot atomic success, captured-active semantics,
inactive/no-IG behavior, and the return certificate. Full/inactive/no-IG controls
are explicitly conditional snapshots, not initialized saturation or attachment
reachability claims. `MuxStoppedTracerCancellation` supplies an initialized
history through real graceful group cancellation and pending TraceStopped
callback, then observed async delivery, actual whole-pool close, Failed/Dead
and provider handoff. The abandoned graceful notification is not committed;
the new Dead invocation publishes once. The old callback remains in the fault
record and its old controllers cannot resume. Returned-callback cancellation
uses the existing ordinary abort guard and retains already committed effects.

The new cancellation endpoint imports small, data-only MuxPoolCloseFixtures;
it proves all transitions rather than importing another acceptance endpoint
solely for its snapshots. Async delivery, buffer/helper masks and custom tracer
normal/exceptional outcomes remain explicit contracts. There is no Haskell mux
replay or new universal shutdown/liveness/source-refinement claim.


Validation for the twelfth increment: twenty-one targeted Agda 2.8.0 endpoint
commands passed serially at `+RTS -M2G -RTS`, without warnings. Final logs have
seventeen own-module Checking lines and four cached successes (group/unwind
properties and group/startup acceptance); those closures had already passed
with the current dependencies. Commands checked
`Properties/{SubsystemSupply,SubsystemReferences,OriginMonitorInvariant,
MuxGroupShutdown,MuxStartupUnwind}` and
`Negative/{MuxGroupShutdown,MuxStoppedTracer,MuxStoppedTracerCancellation,
MuxHandlerExit,MuxHandlerExitOutcomes,MuxHandlerExitCM,MuxExitCancellation,
MuxStartupUnwind,MuxStartupUnwindBranches,MuxStartupUnwindInterleavings,
MuxStartupUnwindCM,MuxStartupUnwindSites,MuxCallbackCancellation,
MuxCallbackCommitted,MuxCallbackCancellationCM,MuxGroupEffects}`.
The changed source runtime/rules and new pool fixture were also checked during
incremental development, directly or transitively. No endpoint is described as
fresh solely from a cached success.

Two initial aggregate callback-cancellation checks exhausted 2 GB while importing
large acceptance modules only for data. The small data-only fixture layer removed
that dependency; the same initialized scenario then passed at 2 GB. No statement
was weakened, scenario removed, safety disabled or heap limit raised. Local
record-field/import scoping repairs were completed before the final checks.
Logs: `/tmp/cm-review-20261028/si4f1-final-*.log`; the two heap failures remain in
`si4f1-tracer-cancellation.log` and
`si4f1-Negative-MuxStoppedTracerCancellation.log`. Static audit of all twenty
pending Agda files found only the same three pre-existing comparison-operator
false positives (≤?/<?) in IGRegistration. No new postulates, holes or unsafe
options were added. Whitespace/EOF checks pass. These changes and the preceding
callback increment remain uncommitted after d47f109. No checker is running.
No source-pin change, Haskell replay, commit or push was performed; `.claude` is untouched.

SI4-F1 is complete within the stated profile. Next: expose the bearer tracer's
TraceEmitDeltaQ callback after clean protocol completion and after Dead on error,
with normal/synchronous/asynchronous outcomes. Preserve prior status/notification
commits and exception replacement; do not infer normal monitor return when that
callback throws. Remaining ignored callbacks, post-close catch cancellation,
earlier allocation/publication and child-finalizer failures, followed by outer
Server/IG/governor composition and admission quiescence, still precede SI5.


## Thirteenth increment: explicit bearer DeltaQ outcomes (29 October 2026)

The overall objective remains the standalone CM/IG/OG/Server model for source
bug-finding at the pinned network revision. This increment extends SI4's physical
handler/mux chain; it does not merge that chain with PeerSupervision/Subsystem or
Server, complete G1/G2, CM-I4c, or derive SI5/full shutdown.

Re-exported exact-pin Mux, JobPool, ConnectionHandler and InboundGovernor source
objects into `/tmp/cm-review-20261029/` before extending claims. Mux.hs:454–464
calls the bearer tracer's TraceEmitDeltaQ after the clean protocol trace, before
another monitor iteration. For a protocol error it first writes Failed and
returns from the exception/Dead tracers, then runs DeltaQ before throwing the
original error. Infrastructure-result branches have no DeltaQ invocation.
The async catch remains outside the real JobPool bracket at Mux.hs:254–279.

`MuxDeltaQ` extends MuxStartupUnwind with tickets taken only from actual successful
typed FIFO consumption. Direction, protocol number, RunId and completion outcome
remain distinct. Entry explicitly requires a monitoring owner and an open
physical pool; a
callback PC cannot adopt partial startup or an already closed bracket. Tracked
IG completion/Dead stages must return at the proper status before entry. Where
the lower component leaves a caller/ignored mux-tracer leg opaque, DeltaQ entry
incorporates that leg's observed normal return; it does not prove tracer totality.
The protocol-error branch reaches DeltaQ only after Dead at the original Failed
value. Normal return invokes the existing exact lower monitor step. Raw clean
branch finish and protocol-error final finish are blocked in the extended
adapter until DeltaQ returns; the intermediate error-trace-to-Dead continuation
is retained. An invoked owner cannot resume its controller, while
other owners, child publication/deregistration and external stop retain their
own guards. The lower MuxResultMonitor is still a component with an observed
successful trace/DeltaQ-return boundary, not a replacement full-source theorem.

A named sync/async exception from an invoked callback selects the actual captured
handler and current-pool route, without changing its held result or already
committed source effects. It retains the complete physical-pool close, buffer
scope, policy and original CM finally/result gates. Sync failure preserves the
existing Ready or original Failed status and replaces the body exception. Async
failure writes the new Failed only after actual pool closure, then invokes a new
Dead callback. Previously committed notifications remain; an earlier protocol
error's Dead notification is not deduplicated or retracted.

`Properties/MuxDeltaQ` projects every successful action and finite execution into
actual shared-source and selected physical-pool histories. Initialized capture,
entry/promise supply and captured-snapshot terminal certificates retain their
existing premises. Fault selection reuses the published-owner/current-pool
certificate; selection/entry do not roll back source effects. The physical CM
wait certificate observes the actual nested dispatcher and physical-result
oracle. `MuxDeltaQCapture.consume-captures-head` exposes the precise original
queue/head, actual pool dequeue, selected monitor state and stored ticket.
The separate `MuxDeltaQPrefix` layer lifts only tagged protocol-only prefixes,
without importing the large source-invariant closure solely for prefix proofs.

Acceptance endpoints:

- `Negative/MuxDeltaQ`: initialized normal clean/error paths in both directions;
  infrastructure exclusion; no skipped, premature, repeated or uninvoked callback;
  actual-head certificates and initialized source/capture/supply facts.
- `MuxDeltaQEffects`: initialized sync and async callback exceptions after clean
  completion and after the error branch's returned Dead. The returned protocol
  can deregister/publish its Async result independently during DeltaQ. All four
  combinations close the real current pool, run the captured CM finally and
  publish the physical parent result. Sync replacement keeps the old mux status;
  async handling retains old notifications and appends the new Dead event.
- `MuxDeltaQCM`: actual initialized CM snapshot, late read, send, DeltaQ delivery
  receipt, collective wait, pool/buffer/CM unwind and physical result publication.
  Receipt, registry closure and cleanup completion cannot shortcut the final wait.
- `MuxDeltaQInterleavings`: infrastructure return/publication and external stop
  during invoked DeltaQ, followed by actual callback return and FIFO consumption.
  The new physical head replaces the old ticket. A queued result outranks shutdown;
  with only that backlog removed, the positive shutdown-selection control passes.
  Forged-PC controls reject partial startup and already closed pools; these
  conditional controls are not initialized reachability claims.

Tracer return, exception class/identity, async receipt, provider behavior and
policy choice remain explicit observed contracts. The pinned optional DeltaQ
transformer (TraceTransformer.hs:42–55) may reset its private statistics and emit
a sample before forwarding TraceEmitDeltaQ. Those statistics/logger resources
are not represented by these CM-source preservation statements. No total-tracer,
full mask, helper-resource cleanup, universal progress, full source refinement or
Haskell mux replay claim follows from these finite executions.

### Conditional source-profile finding, not a confirmed deployment defect

The initialized clean/synchronous case reaches a physically available handler
result after pool and CM cleanup while mux status remains Ready. This strengthens
the earlier conditional tracer-failure boundary with an initialized DeltaQ path;
it refutes any proposed general invariant that every handler exit must write
Failed/Stopped under the admitted tracer inputs. The witness has one protocol
and retains earlier IG events, so it does not establish an IG/PSA deadlock.
Concrete bearer-tracer contracts, multi-protocol/overlapping-key reachability and
implementation replay must be checked before presenting it as a source bug.
Likewise the additional Dead notification after async failure is source-aligned
behavior, not by itself proof of a key-reuse defect.


Validation on 29 October: the current runtime was freshly checked with
`agda ConnectionManagement/MuxDeltaQ.agda +RTS -M2G -RTS`. After making the
monitoring/open-pool guard explicit, all ten final endpoint commands passed
serially without warnings:

```sh
agda ConnectionManagement/MuxDeltaQ.agda +RTS -M2G -RTS
agda ConnectionManagement/Properties/MuxDeltaQPrefix.agda +RTS -M2G -RTS
agda ConnectionManagement/Properties/MuxDeltaQ.agda +RTS -M4G -RTS
agda ConnectionManagement/Properties/MuxDeltaQCapture.agda +RTS -M4G -RTS
agda ConnectionManagement/Negative/MuxDeltaQ.agda +RTS -M4G -RTS
agda ConnectionManagement/Negative/MuxDeltaQEffects.agda +RTS -M4G -RTS
agda ConnectionManagement/Negative/MuxDeltaQCM.agda +RTS -M4G -RTS
agda ConnectionManagement/Negative/MuxDeltaQInterleavings.agda +RTS -M4G -RTS
agda ConnectionManagement/Negative/MuxResultMonitor.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/MuxStoppedTracer.agda +RTS -M4G -RTS
```

Seven final logs contain their own module Checking line; the already rechecked
runtime and two unchanged negative controls were cached confirmations. The fresh
runtime Checking line is in `deltaq-runtime-final.log`. The source-proof closure
initially exhausted 2 GB, including after separating the cheap prefix layer.
With resource availability checked, the source/acceptance closure passed at the
explicit 4 GB heap limit. No proof statement was weakened, scenario removed,
postulate introduced or safety check disabled. The only warning during development
was a constructor-shadowing pattern name in an acceptance helper; renaming it
removed the warning before the final run. Equality-transport, scoping and module
import repairs were also completed before these final checks.

Logs: `/tmp/cm-review-20261029/deltaq-final-*.log`, with the retained 2 GB failure
in `deltaq-properties.log`, the fresh-runtime log above and
`deltaq-proof-audit.log`. Eight-file local proof audit: zero findings; tracked/new
source/documentation whitespace and EOF checks passed. Dependency assumptions
have not been replaced by a term-level external axiom audit. No Haskell replay,
source-pin change, commit, push or unrelated build was performed; `.claude` is
untouched. This increment is uncommitted after 920c16f.

The initiator-direction completion trace also now has explicit invocation,
normal return, sync/async exception and CM-delivery actions. IG ignores these
completion traces, but the caller mux tracer still runs. The initialized clean
and error normal paths use the new actions and reject legacy return/failure
shortcuts before invocation. Generic source/pool projection includes the new
actions. Full initiator-failure cleanup and CM-delivery acceptance witnesses
remain open; the existing complete failure witnesses above concern DeltaQ.

Next executable obligation: initialized initiator-tracer sync/async failure
cleanup, including a live responder in the same physical pool and CM delivery.
Retain the captured completion and already written status without inventing
first-leg return or labeling that failure as DeltaQ.
Then post-close catch cancellation, earlier allocation/publication and additional
child-finalizer/helper scopes remain before outer Server/IG/governor composition
and admission quiescence. Source-contract and stronger reachability/replay checks
for the conditional Ready-after-exit path remain bug-finding follow-ups; no
universal deadlock or full-shutdown claim is made by this increment.


Commit validation on 29 October: after adding the explicit initiator-trace
transitions and normal-path controls, all eight DeltaQ runtime/property/acceptance
modules listed above passed serially with Agda 2.8.0 at a 4 GB heap limit. Six
logs contain Checking lines; runtime and generic source properties were cached
confirmations of their earlier initiator checks. No warnings were reported.
Eight-file static proof audit again found zero findings, and staged whitespace
checks passed. Logs: `/tmp/cm-review-20261029/commit-*.agda.log`. The two unchanged
non-DeltaQ negative controls were not repeated for this commit. No implementation
replay or full initiator-failure cleanup witness was added during commit work.


## Fourteenth increment: ignored initiator completion tracer failures

The caller mux tracer still runs on initiator-direction clean/exception exit,
even though IG's `miniProtocolTerminated` ignores that direction. The unchanged
network pin's Mux.hs:454–464 places the clean trace before bearer DeltaQ; on
protocol error it first writes Failed(original), then calls the exception trace,
Dead, DeltaQ and the original throw. The async-only catch at :275–279 is outside
the physical JobPool bracket (:254–274). JobPool.hs:70–111 closes the captured
registry by sequential uninterruptible cancellation; :147–163 excludes async
exceptions from the job result handler. IG.hs:736–748 recognizes only responder
completion traces. ConnectionHandler.hs:363–365 and :438–440 compose the caller
tracer before IG. The four local exports were compared byte-for-byte with their
pinned Git objects again on 29 October before extending these proofs.

`Properties/MuxInitiatorTrace` adds a selection certificate for the existing
explicit initiator-trace actions: the selected owner/capture, startup PC, callback
and physical parent-registration facts come from the existing fault selector.
`throw-keeps-underlying` proves a local observed throw retains the underlying
source/pool/handler state at selection; cleanup is not manufactured by observation.
The existing generic MuxDeltaQ source/pool/capture/supply statements retain their
types and cover these actions.

`Negative/MuxInitiatorTraceEffects` starts from the actual initializer, admits a
responder, forks an initiator in the same pool, publishes and captures its typed
physical FIFO head, and invokes the initiator trace. While that callback is held,
the already returned initiator deregisters and publishes its physical result.
For each clean/error completion and sync/async tracer exception, the real pool
snapshot contains **the still-running responder, demuxer and muxer**. Every child
is cancelled, unwound, deregistered, physically completed and joined. Snapshot
terminal results follow from `whole-closed-from-initial`; no historical handle
is deleted and no protocol result is fabricated for async cancellation. A join
before the responder's physical result is rejected.

All four finite histories continue through provider/buffer exit, exception policy
where applicable, the original CM finally and physical handler result. Sync
failure retains Ready or Failed(original); async failure closes the pool first,
writes Failed(new), then invokes/samples/commits/returns Dead. This appends the
first new MuxFinished for these initiator branches and clears trace counters.
Previously queued awake/promote events survive. The captured initiator result is
retained as throwing; neither a normal first-leg return nor DeltaQ invocation
is invented. These observations remain conditional tracer/provider/policy inputs.

`Negative/MuxInitiatorTraceCM.Scenario` covers both clean and error origins with
CM snapshot, late read, cancellation request,
actual initiator-trace async receipt/acknowledgment, collective wait, actual pool
close and CM finally/result publication. DeltaQ receipt cannot substitute for
this first-leg receipt. The collective wait is blocked before pool close, after
pool close and after cleanup until the handler's physical result is available.
The final wait is certified by the existing `PhysicalWait` theorem.

The clean synchronous case strengthens the conditional Ready-after-exit finding:
a real live responder in the same pool is physically cancelled/joined while mux
status remains Ready and source trace metadata retains one hot responder and its
running protocol. No new IG completion/Dead notification is emitted on this path;
the earlier awake/promote queue remains. This refutes an unconditional invariant
that physical handler completion always clears responder metadata or changes mux
status under the admitted observations. It is **not a confirmed deployment bug,
a deadlock witness or a full shutdown theorem**. Concrete tracer/policy contracts,
IG/PSA recovery, overlapping-key reachability and implementation replay remain
necessary before claiming a source-code defect. The physical handler adapter
still has not been integrated with whole PeerSupervision/Subsystem/Server history.

Validation on 29 October: Agda 2.8.0 checked the new selection proof and both
acceptance endpoints serially at a 4 GB heap limit. The standalone effects check
passed before adding snapshot-terminal and explicit metadata facts; the later
CM check freshly rechecked that final effects module transitively. The final CM
check then passed for the generic clean/error-origin scenario. Final logs have
Checking lines and no warnings:

```sh
agda ConnectionManagement/Properties/MuxInitiatorTrace.agda +RTS -M4G -RTS
agda ConnectionManagement/Negative/MuxInitiatorTraceEffects.agda +RTS -M4G -RTS
agda ConnectionManagement/Negative/MuxInitiatorTraceCM.agda +RTS -M4G -RTS
```

Evidence: `/tmp/cm-review-20261029/initiator-selection.log`,
`initiator-effects-2.log`, `initiator-CM.log` (includes final effects Checking)
and `initiator-CM-both.log`. An initial fixture-type scoping error was corrected
to the kernel's existing ThreadPhase/ClosePC names before the passing checks.
No proof statement/scenario was weakened, hole/postulate introduced or safety
check disabled. Three-file proof audit found zero findings; source/documentation
whitespace and new-file EOF checks passed. Unchanged baseline endpoints were
not rebuilt separately; imports were checked transitively. No Haskell replay,
source-pin change, commit or push. The work remains uncommitted after 43e0e2b;
`.claude` is untouched.

Next executable obligation: observed cancellation/failure during the post-close
async catch's Failed/Dead actions. Preserve the closed snapshot and any already
written status/committed callback effects; a new exception from that catch exits
to outer cleanup rather than recursively re-entering the same catch or inventing
a returned Dead trace. Earlier allocation/publication, other ignored callbacks
and child-finalizer/helper scopes, then outer Server/IG/governor composition and
admission quiescence still remain. G0–G5, CM-I4c and SI4/SI5 remain open.


## Fifteenth increment: interruption of the post-close async catch

Source rechecking refined this obligation before adding transitions. The local
io-classes 1.8.0.1 archive delegates `MonadCatch IO.catch` to IO.catch. Network-mux
at the unchanged pin requires io-classes `^>=1.8`; ConnectionHandler.hs:378–380
and :450–452 explicitly unmask Mux.run. A catch entered from unmasked IO executes
its handler masked interruptibly. Therefore a new async exception cannot be
freely delivered between the catch's nonblocking Failed/status/read operations.
The actual blocking operation or a tracer unmasking contract must justify receipt.
The current profile covers an observed blocking caller tracer and a full-queue
retry in the IG Dead transaction. It does not claim every custom tracer blocks.

`MuxCatchUnwind` wraps the existing physical DeltaQ/handler chain. It admits
replacement only for an async catch's pending Dead callback with the actual pool
closed, no outer exit frame, and mux status matching the caught async exception.
A blocking caller-tracer observation is before IG's active read (or the opaque
caller trace on a no-IG attachment). The retry site requires captured-active
Dead and failure of the actual bounded `writeMessage`, not an arbitrary pending
STM. Ordinary status steps, a nonfull queue, and returned Dead reject delivery.
Synchronous caller-tracer throwing uses the existing throw-point guard.

The interruption record retains the original caught Fault, actual current Dead
callback, and replacement cause. Selection changes only metadata, keeps the
closed physical pool/source/queue/counters intact, and goes directly to outer
buffer exit. The same catch is not recursively entered: it does not rewrite
Failed(new), invoke another Dead or invent old Dead return. CM receipt executes
the actual acknowledgment operation. The lower legacy sync observation is blocked
in this adapter so it cannot discard the new retained catch evidence.

`Properties/MuxCatchUnwind` projects all actions/executions to existing source and
physical-pool paths, lifts initialized capture/supply, and retains the physical
CM wait certificate. `select-is-local` and `observe-keeps-underlying` establish
metadata-only selection without manufacturing cleanup. The generic CM projection
peels the adapter at an abstract action before specializing the real nested wait,
keeping the full source dispatcher out of normalization.

`Negative/MuxCatchUnwind` lifts the actual initialized initiator clean/error
failure prefixes, closes responder/demuxer/muxer, writes the caught async Failed
status and invokes Dead. A replacement async exception at an observed blocking
caller tracer exits through the real buffer/provider and original CM finally to
physical handler completion. Both origins retain Failed(caught), the pending Dead
callback and old IG queue; the replacement async exception is the handler result.
Controls reject recursive Failed/Dead, fabricated callback return, delivery at an
ordinary STM or after return, and queue delivery with room. An injected full-queue
snapshot proves retry before masked delivery and source retention; that control
is conditional, not an initialized full-queue reachability claim. A synchronous
first-leg replacement control also retains the caught/abandoned metadata.

`Negative/MuxCatchUnwindCM` drives CM snapshot/read/send while that catch tracer
is pending, actual receipt/acknowledgment, outer cleanup and physical result, for
both completion origins. The collective wait is blocked after receipt and after
cleanup until the real result is published. Its final `PhysicalWait` certificate
uses the existing actual coordinator/physical handler boundary.

`SourceReplay/CatchMaskProbe.hs` passed under GHC 9.6.7 / base 4.18.3.0. It checks
pool-close → MaskedInterruptible catch → outer-finally, with replacement
UserInterrupt escaping a blocked catch handler. It is an IO semantics probe,
not a concrete Mux/IOSim replay, source refinement or deadlock witness. See the
SourceReplay README for reproduction and scope. Enclosing mask/provider behavior,
custom tracer operations, admission quiescence and outer composition remain
explicit limitations. This increment adds coverage, not a deployment bug claim.

Validation on 29 October: all four new Agda modules passed serially with Agda
2.8.0. Each final log contains its own Checking line and no warnings:

```sh
agda ConnectionManagement/MuxCatchUnwind.agda +RTS -M2G -RTS
agda ConnectionManagement/Properties/MuxCatchUnwind.agda +RTS -M4G -RTS
agda ConnectionManagement/Negative/MuxCatchUnwind.agda -v tc.decl:10 +RTS -M6G -RTS
agda ConnectionManagement/Negative/MuxCatchUnwindCM.agda +RTS -M6G -RTS
```

The initial aggregate proof check exhausted 4 GB before the abstract CM
projection was factored; equality/case-split repairs then preceded the successful
standalone property check at 4 GB. The initialized acceptance closure exhausted
4 GB in both aggregate and standalone checks. With 21 GB available, the complete
unchanged acceptance histories passed at 6 GB, followed by the CM endpoint.
No scenario or theorem was weakened and no safety option disabled. The failed
logs are retained alongside the passing logs: `catch-runtime.log`,
`catch-properties-3.log`, `catch-acceptance-6g.log`, `catch-CM-6g.log` under
`/tmp/cm-review-20261029/`. Seven-file local proof audit (including the preceding
uncommitted initiator increment) found zero findings; new-file EOF/whitespace
and documentation diff checks passed. Dependency assumptions were not replaced
by a term-level external axiom audit. GHC `-fno-code -Wall` checked the boundary
probe without warnings, and its execution passed. Unchanged baseline endpoints
were not rebuilt separately; imports were checked transitively.

No concrete Mux/IOSim replay, source-pin change, commit or push. These changes
and the preceding initiator-tracer increment remain uncommitted after 43e0e2b.
`.claude` is untouched. Next: source-audit and model pre-publication failures at
returnedSuccess/handleAllocated, retaining the real promise/catch/finally order
and physical handler identity rather than inventing successful publication.
Other ignored callbacks, child finalizer/helper failures and outer Server/IG/
governor composition/admission quiescence remain. G0–G5, CM-I4c and SI4/SI5 remain
open; none of these local paths derives universal/full-system shutdown.


## Sixteenth increment: failures before successful promise publication

**Source-fidelity correction (30 October):** the resolved typed-protocols
1.2.1.0 driver forces handshake results before return. The pinned HandshakeResult
NFData instance forces application WHNF and version data NF inside the narrow
handshake catch; NodeToNodeVersion and NodeToNodeVersionData derive NFData.
The positive strictHandle/handleSync scenario has been removed. That observation
site now rejects both sync and async failures, with an actual initialized
post-allocation prefix retained as a negative control. The four tracer cases
remain. No generic theorem statement was changed. This corrects the model's
source profile; historical five-case checks do not validate the removed case.
See the [forcing contract probe](SourceReplay/HandshakeForcing.hs) and
[reproduction/scope](SourceReplay/README.md#handshake-result-forcing-contract-probe).

**Uncommitted after 9ecdfb8.** The four corrected initialized tracer-failure
histories and the CM endpoint now pass. Real readCounters steps and exact
awaitResult certificates replace the earlier counter-PC refusal control. A
separate raw-dispatcher lemma establishes the empty-promise read retry at that
actual PC; physical result availability at the same waits is also proved.

The source audit at the unchanged pin separates restored handshake execution
from the following masked continuation. ConnectionHandler.hs:337–346 and
:414–423 catch exceptions from **runHandshake** and write HandlerError. They do
not cover the successful continuation. TrHandshakeSuccess (:353/:430), control
TVars/counters, Mux.new (:370/:438), the strict Handle (:371–376/:443–448), and
successful writePromise (:377/:449) occur afterwards. Mux.hs:140–146 emits
TraceNewMux before allocating its protocol map/queue/status. Handle fields are
strict (ConnectionHandler.hs:119–124). The outer classifier (:293–309) traces
and rethrows according to policy, without writing the handshake promise.

Core.hs:584–592 installs the real CM finally around the whole handler. Cleanup
terminates/purges the captured entry and closes the socket, but does not fill the
promise. The fresh inbound and outbound callers readPromise directly at :897
and :1584; those reads do not race the physical Async result or connVar. Exact
Mux, ConnectionHandler and Core Git exports were rechecked before extending
these claims. This source boundary motivates candidate **CM-PUB1** below.

`MuxPublicationUnwind` wraps the current catch/physical-handler chain. It admits
observed sync failures from TrHandshakeSuccess and TraceNewMux at
returnedSuccess. Async receipt is admitted only as an observed blocking operation
in either tracer. The strictHandle site is always rejected: no new payload
evaluation is justified at that later pure constructor. No ordinary masked allocation/status step is
invented as a delivery site. Partial private TVar allocations and opaque tracer
internals are outside this atomic allocation profile.

Selection requires the actual owner/frame, matching current HandlerStart, an
empty promise, no old fault/outer exit, pre-publication startup and no pool
handles. It retains the complete original unpublished frame/site/outcome,
installs the existing outer exit frame, and does not publish success or error,
enter a buffer/pool, close a fictitious pool, create a handler or attach the
post-publication async mux catch. Sync exceptions enter the real classifier;
async exceptions bypass it. The failed owner's old allocation/publication and
controller actions are sealed while other actors and its real outer cleanup
remain executable. Successful lower allocation remains an observed normal
operation, not a theorem that concrete caller tracers cannot throw.

`Properties/MuxPublicationUnwind` projects actions/executions to actual source
and physical-pool paths, lifts initialized capture/supply and certifies the real
CM physical-result wait. `Negative/MuxPublicationUnwind` supplies initialized
outbound histories for both tracer sync/async failures. They use actual
creation/negotiation. A separate initialized allocation prefix proves rejection
of both sync and async strictHandle observations. Each continues through policy where applicable, original CM
finally, socket/map cleanup and physical handler result; no buffer or pool is
entered. Each then executes the actual counter read, reaches awaitResult, and
checks the empty-promise read. The captured unpublished frame survives.
`Negative/MuxPublicationUnwindCM` adds real CM snapshot/read/send, observed
TraceNewMux blocked-tracer receipt/ack, finally and collective physical wait.
The promise wait and Async wait remain distinct. The CM history advances the
caller before final CM completion, rather than inserting a successful API action
after the CM scope closes. Properties/PromiseWait.outbound-read-retries requires
the exact captured awaitResult frame and empty promise, and targets O.advance
directly; the claimed retry is not caused by an adapter's controller guard.
MuxPublicationFixtures contains data only, avoiding imports of large existing
negative-control endpoints; all four tracer cases and their actual birth steps remain.

**CM-PUB1 (conditional source-profile candidate):** a pre-publication failure
outside the handshake catch can leave an empty promise after the real handler
physically completes and CM cleanup removes its entry. A caller reading that
promise still blocks. This is a finite initialized model/source-profile finding,
not a universal deadlock or a confirmed deployment defect. Concrete tracer
fault contracts, production policy, external governor/Server cancellation and
an actual pinned implementation replay remain to be checked. The current
initialized acceptance is outbound; the generic adapter also selects inbound
frames, but no corresponding inbound initialized execution is claimed here.

Additional source audit: CM Types.hs:289–317 implements readPromise with
readTMVar, and writePromise with tryPutTMVar/throwSTM; neither the reviewed
Core finally nor ConnectionHandler uses forcePromise to repair this failure.
PeerStateActions.hs:784–795 directly tries acquireOutboundConnection, and
EstablishedPeers.hs:570–574 directly calls establishPeerConnection with an
explicit timeout TODO. These reviewed functions do not supply an establishment
timeout. This observation does not exclude external scope cancellation or other
runtime recovery; concrete replay and full ownership composition remain needed.

Historical validation on 29 October, before the strictHandle correction: the corrected initialized endpoint passed with Agda
2.8.0 at 6 GB, freshly checking Negative/MuxPublicationUnwind and its new data-only
MuxPublicationFixtures dependency. The corrected CM endpoint then passed at 6 GB,
freshly checking itself and Properties/PromiseWait. Both logs have Checking
lines and no warnings:

```sh
agda ConnectionManagement/Negative/MuxPublicationUnwind.agda +RTS -M6G -RTS
agda ConnectionManagement/Negative/MuxPublicationUnwindCM.agda +RTS -M6G -RTS
```

The unchanged runtime and generic source/pool/capture/supply properties were
previously checked at 4 GB and 6 GB respectively and confirmed through imports
here. Their prior logs are publication-runtime-4g.log and
publication-properties-6g.log. The earlier runtime 2 GB, generic-property 4 GB
and old aggregate acceptance 6 GB heap failures are retained. Earlier syntax and
case-splitting repairs preceded these checks. A standalone PromiseWait check
initially lacked the existing DecEq-Id instance import; after adding that import,
the lemma passed transitively in the corrected CM check. All checks in this
continuation were serial. No generic theorem was weakened, case removed,
postulate/hole added or safety option disabled.

Final evidence is in /tmp/cm-review-20261029/publication-corrected.log,
publication-CM-corrected.log and publication-final-audit.log. Six-file local proof
audit found zero findings; source/documentation whitespace and new-file EOF checks
passed. No unrelated baseline rebuild, concrete implementation replay, full
source refinement, source-pin change, commit or push. The dated presentation
remains an unchanged snapshot of the earlier WIP checkpoint.

Next executable obligation: investigate CM-PUB1 using the actual pinned
ConnectionHandler/CM and concrete tracer/payload/policy contracts; establish a
corresponding inbound witness and account for caller/governor/Server lifetime
and recovery before stronger liveness claims. Private allocation and duplicate
publication failures, other ignored callbacks and child/helper/finalizer scopes
remain, followed by physical/Subsystem/Server composition, admission quiescence
and derived full shutdown. G0–G5, CM-I4c and SI4/SI5 remain open.


30 October handler-body replay: SourceReplay/PublicationHandler.hs passed ten
synchronous cases across real inbound/outbound production makeConnectionHandler
with encoded queue-bearer handshakes. TrHandshakeSuccess, TraceNewMux and lazy
protocol-element allocation faults leave the real promise empty after handler
Async result; early handshake payload failure writes Left, late TraceStarting
failure follows Right. Delegating STM writer observations preserve original
semantics; exact injected fault is checked at the real classifier. This validates
the allocation fault location separately from the rejected strictHandle case.
The allocation fault is not yet a positive Agda scenario. Actual CM finally,
caller/map/socket cleanup, ThreadFinished ordering, async tracer receipt and
outer recovery are not included; no stronger liveness claim follows. Scope and
reproduction: SourceReplay/README.md. Final runghc -Wall exited 0 without warnings.


30 October actual-CM follow-up: SourceReplay/PublicationCM.hs passes 14 IO cases
using the real production handler and both CM entry points. Pre-publication sync
and observed blocked-tracer async faults leave a pending STM caller after actual
GHC handler ThreadFinished, empty full CM map and one synthetic socket close.
Caller counter callbacks (two outbound/one inbound) certify the fresh readPromise
boundary; the earlier counter-PC control is not reused. Early payload Left and
late publication Right controls return, with the late cleanup race permitted.
All writer operations are delegated atomically and force count is zero. Async
receipt is sent by the harness at an actually blocked MaskedInterruptible tracer;
CM's shutdown snapshot/send traversal and outer caller recovery remain open.
Final runghc -Wall exit 0, no warnings. The earlier IOSim attempt exited 1 on the
pure payload's host evaluation after two sync tracer passes; actual IO avoids
altering production evaluation. SourceReplay/README.md records precise scope.

Agda correction acceptance update: the first downstream 6 GB run ended with heap
exhaustion (exit 251), not a type error. Keeping head/frame/action functions split
by the four constructors restores a neutral case index in generic proofs, avoiding
eager normalization of the full source fixture. A fresh corrected initialized
endpoint check is running at 6 GB; final acceptance remains pending until it and
the downstream CM endpoint finish. No generic theorem type was changed.


## Seventeenth increment: allocation failure and initialized inbound history

**30 October, work in progress.** Production-handler and actual-CM IO replays
validated a lazy protocol-element failure *inside* Mux.new after TraceNewMux and
before allocation returns. MuxPublicationUnwind now exposes muxAllocation at
returnedSuccess for sync observations only. It rejects async delivery there and
rejects retroactive allocation failure after handleAllocated. strictHandle remains
rejected for both outcomes. This is a distinct source location, not a renamed
strict-constructor case. Private partial TVar allocation remains abstract.

The outbound acceptance and its CM specialization now range over five cases:
four tracer outcomes plus allocationSync. The new inbound data-only fixtures and
Negative/MuxPublicationInbound build an actual nine-step prefix: seven admission
operations (including fork and real counter read), enterHandshake, and negotiate.
They retain the actual inbound birth and a one-protocol bundle, then describe all
five policy/finally/cleanup/result paths. The intended postconditions include
empty promise, entire map purged, captured socket closed, physical handler result,
retained unpublished capture, and the exact awaitHandshake caller continuation.
Properties/PromiseWait.inbound-read-retries checks the raw Machine.advance read,
without adapter guards. That local retry does not prove permanent blocking.

Validation so far: runtime, new inbound promise lemma and inbound fixtures each
freshly passed serial Agda 2.8.0 checks at 4 GB. Eight-file proof audit has no
findings; whitespace checks pass. The previous two corrected outbound acceptance
runs exhausted 6 GB (both exit 251), not a type diagnostic; preserving neutral
case indices alone did not make 6 GB sufficient. Resource inspection showed
20 GB available. The new full inbound endpoint is RUNNING at 8 GB, session 90172;
/tmp/cm-review-20261029/publication-inbound.log. It rechecks generic properties.
No full endpoint success is claimed yet. Outbound and CM endpoints must then be
rechecked serially against the new allocation-aware runtime. No generic theorem
type was weakened, or axiom/hole/unsafe pragma added. The actual-CM replay remains
14 passing IO cases; no replay was rerun for these Agda-only changes.

After acceptance, continue CM-owned shutdown delivery and caller/governor/Server
recovery/ownership integration. Inbound CM snapshot/wait composition is not proved
by the standalone inbound history. G0–G5, CM-I4c and SI4/SI5 remain open.


30 October acceptance/replay update: the full five-case inbound initialized
endpoint and generic MuxPublicationUnwind properties passed at 8 GB (session
90172 exit 0, own Checking lines, no warnings). Runtime, PromiseWait and inbound
fixtures retain their fresh 4 GB passes. The aggregate outbound+CM endpoint is
now checking serially at 8 GB, session 53625, log publication-allocation-CM.log;
it must finish before claiming those updated endpoints accepted.

PublicationCM.hs now passes **18** actual-CM IO cases. Four new cases cover
CM-owned shutdown at either pre-publication blocked tracer for each provenance.
They require an exact live singleton map, blocked handler and pending caller;
then cancel/join the caller and verify the map/handler unchanged before CM scope
exit. The real Core finally performs snapshot/send/wait. After return, zero
promise writes, one close and GHC handler ThreadFinished are required. Lifecycle
order is observed-open/caller-cancelled/cm-shutdown/socket-close/after-with.
No CM API is used after its scope; no harness throwTo targets the handler in
these four cases. SourceReplay/README.md records the two different observation
phases. Final repository runghc -Wall exits 0 without warnings; log
publication-CM-owned-final.log. This establishes finite profile replays, not a
live escaped caller, permanent stall or full shutdown theorem.

A corresponding inbound CM snapshot/receipt/finally/physical-wait witness is
prepared in Negative/MuxPublicationInboundCM.agda. It has not been checked yet;
queue it after the live outbound/CM check. Its retained caller PC is a logical
capture, not a certificate of a live caller job after CM closure. Outer
caller/governor/Server cancellation/ownership integration remains open.


**New Server fidelity prerequisite (30 October):** source review and actual
Server replay show that its admission workers are raw async children with
ignored handles (Server.hs:239–254), outside its scoped action/IG/accept-loop
join tree. PublicationServer.hs passes six actual Server/IG/CM/handler cases:
five pre-publication faults leave its admission worker blocked after Server.with
returns; early payload Left is the finishing control. Handler completion, empty
CM map, exact caller read boundary and listener closure are checked. The API's
all-server-threads-stop comment (:132–133) has this injected-contract exception.
ThreadId instrumentation can affect GC/deadlocked-STM detection; permanent leak,
production occurrence and universal deadlock are not proved. The harness cleans
up its observed workers. SourceReplay README and SI4 audit contain exact scope.

The 18-case direct-CM replay's caller cancellation is explicitly harness-owned.
It must not be transferred to Server as a source fact. Next Server composition
must model independent raw admission Async actors, their original onException/
Disconnected close branches and missing join, before SI5 can derive completion.
Rules/CallerCancellation currently handles outbound acquisition/release only;
its noCaller branch does not supply physical inbound admission cancellation.
Do not equate a stored logical awaitHandshake PC with a live physical worker.


## Acceptance checkpoint and next Server layer — 30 October

All current pre-publication Agda endpoints now pass with their own Checking lines
and no warnings. Runtime, PromiseWait and new inbound fixtures passed at 4 GB;
full initialized inbound and generic properties passed at 8 GB. Then the aggregate
outbound/CM endpoint freshly checked its five-case outbound endpoint/data fixtures
and passed at 8 GB (session 53625 exit 0). Finally the new inbound CM witness
passed at 8 GB (session 46265 exit 0). Commands:

```sh
agda ConnectionManagement/Negative/MuxPublicationInbound.agda +RTS -M8G -RTS
agda ConnectionManagement/Negative/MuxPublicationUnwindCM.agda +RTS -M8G -RTS
agda ConnectionManagement/Negative/MuxPublicationInboundCM.agda +RTS -M8G -RTS
```

Logs: publication-inbound.log, publication-allocation-CM.log and
publication-inbound-CM.log in /tmp/cm-review-20261029. The two 6 GB heap failures
are historical failed runs; neutral-case indexing alone did not suffice there.
Nine-file local proof audit reports zero findings, and whitespace/EOF checks pass.
Generic theorem types remain unchanged; no new trust assumption/unsafe option.
This is model proof evidence, separate from 18 actual-CM and six actual-Server
IO replay cases. No checker remains running at this checkpoint.

Next SI4 slice must represent Server's **raw admission Async workers**, rather
than importing the chosen caller scope of the direct-CM harness:

- Observe actual accepted-socket handoff/fork before recording a physical worker;
  do not adopt existing admission PCs as physical Async history.
- Keep its includeInbound result/error close branches and physical result separate
  from handler cleanup. A stored awaitHandshake PC is not a live-thread proof.
- Close only the owned Server action/IG/accept-loop scopes at their real boundary.
  The source has no admission registry join; preserve a finite initialized
  counterexample to deriving all-worker completion from those scope certificates.
- Use PublicationServer.hs's finite observation as the source check. External
  cleanup/GC/runtime recovery are separate inputs; production governor/PSA scopes
  still require composition with the physical handler model before SI5.

This priority follows verified source behavior and prevents an incorrect
structured-admission-ownership assumption. G0–G5, CM-I4c and SI4/SI5 remain open.


## Eighteenth increment: raw admission workers and owned Server scope return

**30 October, uncommitted.** [ServerAdmission](ServerAdmission.agda) wraps the
physical publication-unwind chain with actual raw admission-worker history.
`initial` refuses existing admission/socket slots. An observed successful
accepted-socket handoff/fork inserts both the source continuation and physical
worker, checking fresh caller, socket and reserved handler identities. Historical
outbound results and raw-worker identities cannot be recycled as new callers.
No old logical admission is adopted as an Async birth.

The worker's calling, close, body-exit and result-publication phases are distinct.
Normal Connected returns need no worker close; Disconnected invokes its captured
socket close. A later observed exception at awaitHandshake also invokes that
close. A failed Disconnected close enters the original onException cleanup; a
cleanup-close failure replaces the propagated exception. Server close attempts
are counted separately from CM handler cleanup; uncertain close outcomes remain
explicit. Earlier admission/map-lease/fork-failure physical unwinds are not yet
covered by this adapter. Exited workers cannot resume old caller operations or
reuse their identities for outbound calls.

| Source portion | Implemented scope | Still open |
| --- | --- | --- |
| Server raw admission async | Explicit successful handoff/fork and immutable captured request; post-handshake return/exception close and result phases | Accept/getLocalAddr/tracer/fork errors before handoff; earlier admission unwind branches |
| Owned action/accept/IG scopes | One initialized listener, normal action wins; accept receipt, listener close/result/join, stopped trace and returned-action cancel/join | Multiple listeners, other race winners, owned helper/finalizer/tracer failures |
| IG scope cleanup | Actual deactivateIG/flushOnExit shared transitions, exited/inactive checks, empty published registry | IG CM-call cancellation/unwind and nonempty remote-state exit tracing |
| CM outer finally | Actual shutdown snapshot/traversal/delivery/result-wait steps after IG join; real finishClose required | Full PSA/governor/Server composition and admission quiescence |

The owned infrastructure is an explicit **post-setup scenario boundary**. This
is not a whole-node startup/refinement theorem. The first IG-exit profile refuses
receipt with pending inbound-release/remote-call frames; it does not discard an
unfinished CM call. Listener close and trace return are observed successful
operations, with no eventuality claim. Existing raw workers remain independent
after scope return; no admission registry join or global freeze is invented.

`Properties/ServerAdmission` proves that any finite scope-only execution retains
the exact raw-worker table, including when scope plans perform actual IG writes.
Inherited physical steps also retain it; the guarded source path has a checked
roundtrip. A permission-indexed lift reuses lower physical executions rather
than normalizing their whole dispatchers again. These statements do not yet lift
capture/supply/resource invariants through all the new handoff/close writers.

`Negative/ServerAdmission.initialized` performs two explicit handoffs to recreate
the existing two-admission fixture, then lifts the checked NewMux sync-failure
path and executes the owned Server/IG/CM cleanup. It proves handler result
availability and Server return while **worker zero itself** has no result, retains
its actual physical birth and is at its empty-promise awaitHandshake read. The
second accepted worker is not the sole reason for the unfinished-worker result.
`no-universal-all-worker-completion` refutes deriving all raw results from those
scope certificates in this profile. Map purge, listener close and raw read retry
are separate observations. No fake result, unread return, new post-close handoff
or premature Server completion is admitted.

A further checked suffix supplies an observed async exception, closes the raw
worker's socket and publishes its result. Publication before that close and old
caller/identity reuse afterwards are rejected. This represents the replay's
explicit cleanup input and leaves room for runtime recovery; it proves no
permanent leak, universal deadlock or GC behavior.

Validation: initial runtime and generic properties passed at 4 GB. After actor
history/IG-exit guard refinements and recovery controls, the final endpoint freshly
checked all three modules serially at 8 GB, exit 0, no warnings:

```sh
agda ConnectionManagement/Negative/ServerAdmission.agda +RTS -M8G -RTS
```

Log: /tmp/cm-review-20261029/server-admission-negative-final.log. Initial syntax
and missing Bool-import diagnostics were repaired before acceptance. Three-file
local proof audit: zero findings; whitespace checks pass. No postulates, holes,
unsafe options or weakened prior theorem types. The earlier pre-publication
endpoints remain accepted and unchanged. Native CM/Server replay artifacts were
not changed or rerun for this Agda-only increment. No jobs remain running.

The full SI5 claim is **not** replaced by an easier conditional completion
statement. This counterexample is an obstruction to inferring all-worker
completion from owned scopes alone. Extend physical admission failure coverage,
new-writer invariants, IG-call/nonempty cleanup and parent PSA/governor composition;
keep any additional quiescence/fix profile explicit. G0–G5, CM-I4c and SI4/SI5
remain open. No whole-source or whole-node shutdown/refinement is established.


## Nineteenth increment: initialized Server admission prefix exits

Checked 30 October 2026. This completes acceptance of the prefix runtime committed
in `093cbe5`; the earlier increment's validation predates that runtime extension.
No runtime rule or prior theorem statement was changed for this acceptance work.

Pinned source was rechecked in the clean network checkout at
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`: Core.hs:801–891 distinguishes normal
hard-limit return from forbidden selection and handler-fork exceptions;
Core.hs:2366–2380 restores the saved map on exception without undoing committed
entry writes. State.hs:193–200 retains the lazy handler reference for `mfix`.
Server.hs:239–254 closes Disconnected sockets and uses a separate `onException`
cleanup close. Failure of the normal close can therefore cause a second attempt;
failure of the exception-cleanup close replaces the exception and exits.

[Negative/ServerAdmissionPrefix](Negative/ServerAdmissionPrefix.agda) aggregates
three independently checked branches, backed by data-only flat snapshots and
small shared trace combinators. Internal adapter aliases are private, following
the existing fixture convention. Every trace starts from the real wrapper
initializer with empty raw admission/socket tables and two explicit successful
handoffs; no old logical worker is adopted as physical history.

| Branch | Initialized evidence |
| --- | --- |
| `HardLimit.initialized` | Both requests have hardLimit=1 and are handed off before either CM call. The first installs a real unnegotiated handler; the second counts it, restores/publishes the map, closes once and publishes a normal result. The first entry and physical handler remain, with no second handler birth or promise allocation. |
| `ForkFailure.initialized` | The first fresh-entry path fails before handler birth. The saved empty map is restored while entry/promise allocations and supplies remain. One successful close precedes the raised synchronous worker result; handler stores/results and the handshake promise remain empty. |
| `Forbidden.initialized` | Both requests have hardLimit=2 and the same key. The first executes actual modeled negotiation, allocation, publication and caller completion to inboundIdle. The second counts, allocates its promise, rejects selection, restores and closes once before publishing the synchronous exception, preserving the original entry, handler and socket. |

Four additional initialized histories cover a failed hard-limit normal close
followed by cleanup success or failure, and exception-cleanup close failure for
the fork/forbidden branches. They distinguish uncertain socket outcome, attempt
count, body exit and result publication. Cleanup success retains the first close
exception; cleanup failure publishes the replacement without another retry.
Negative controls reject close/return observations before restoration, premature
worker results, the inherited raw lower-close shortcut, and mismatched handoff
limits. Failed closes do not falsely finish the logical admission.

Validation ran serially with Agda 2.8.0 from the standalone library root. All
listed commands exited 0, with their own `Checking` lines and no warnings:

```sh
agda ConnectionManagement/Properties/ServerAdmission.agda +RTS -M4G -RTS
agda ConnectionManagement/Negative/ServerAdmission.agda +RTS -M8G -RTS
agda ConnectionManagement/Negative/ServerAdmissionPrefixHardLimit.agda --profile=definitions +RTS -M8G -RTS
agda ConnectionManagement/Negative/ServerAdmissionPrefixFork.agda +RTS -M8G -RTS
agda ConnectionManagement/Negative/ServerAdmissionPrefixForbidden.agda +RTS -M8G -RTS
agda ConnectionManagement/Negative/ServerAdmissionPrefix.agda +RTS -M8G -RTS
```

Logs are in `/tmp/cm-prefix-20261030/`: `properties.log`, `server-existing.log`,
`hard-limit-private.log`, `fork.log`, `forbidden.log` and `aggregate.log`.
The final aggregate freshly rechecked all three branch modules and Support after
EOF whitespace cleanup; Fixtures had freshly checked in the successful hard-limit
command. Six-file local proof audit: zero holes, postulates or unsafe-option
findings. Tracked and new-file whitespace checks pass. This is a local source
audit, not a term-level audit of all imported assumptions.

Initial syntax/import repairs preceded these successes. An earlier combined
8 GB run exhausted heap (exit 251). Two subsequent slow checks were stopped
(exit 130) while flattening snapshots, splitting branches and making the internal
adapter aliases private. Those runs are not passing evidence; the final split
checks above establish acceptance. No checker remains running.

Limits: the established owned-infrastructure/single-listener profile remains.
The same-key transport input is abstract, without OS tuple-reachability evidence.
Failed-fork unresolved lazy-reference evaluation is outside this profile. Async
close failures are observed interruptible-close outcomes, not an assertion that
every masked region admits cancellation. No native replay was changed or rerun,
and no new prefix replay, production patch, permanent leak or whole-node shutdown
result is claimed. Broader async lease/tracer unwinds and other scope winners
remain open. Next: lift capture/supply/resource invariants through the new handoff
and close writers, then pending IG-call/nonempty-exit handling and shared
Server/PSA/governor composition. G0–G5, CM-I4c and SI4/SI5 remain open.


## Twentieth increment: Server handoff and close invariants

Checked 30 October 2026. No runtime rule, guard or existing theorem statement was
changed. This extends the existing predicates through the Server admission
wrapper's new writers and every implemented scope/worker action.

[Properties/ServerAdmissionInvariant](Properties/ServerAdmissionInvariant.agda)
proves exhaustive step and finite-execution preservation for a source predicate
given preservation of lower steps, accepted handoffs and socket writes. The
generic layer is parameterized over lower preservation. The concrete
[ServerAdmissionInvariants](Properties/ServerAdmissionInvariants.agda) supplies
all three proofs; no new unproved preservation assumption is left in its public
capture/supply/resource endpoints. Inherited effects reuse the existing
publication-to-outbound-machine trace projection; bookkeeping observations keep
the source unchanged, and successful prefix closes use their actual lower step.

| Public statement | Exact scope and premises |
| --- | --- |
| `captures-step`, `captures-exec` | Preserve unchanged `OutboundRuntimeCapture.Captures`, covering all stored pending outbound acquisition captures, from an existing capture certificate. `from-initial-captures` derives it for initialized outbound configurations without a supply premise. |
| `supply-step`, `supply-exec` | Preserve unchanged `OutboundRuntimeSupply.Valid`, including capture validity and entry/promise allocation bounds. `from-initial-supply` requires only initial shared-world `SupplyBounds`, deriving empty-runtime capture validity from `O.initial`. Bounds alone are not claimed sufficient for arbitrary injected acquisition frames. |
| `For q captured.{step,exec}-preserves` | Retain the exact original handler descriptor plus existence of its stored entry/socket records. Public `resources-step`/`resources-exec` use unchanged `Resources`; no supply, uniqueness, ownership or scheduling premise is added. Closed/uncertain socket values still count as stored records, not live ownership. |

Handoffs change only admissions and sockets, so acquisition frames and allocation
bounds are definitionally unchanged. Socket replacement retains stored resource
identities using the existing `HandlerResourceFacts.socket-write` lemma. Source
steps use the established outbound capture/supply/resource preservation proofs.
This includes selected IG deactivation/flush and actual CM shutdown actions; it
does not widen the runtime's pending-IG-call or nonempty-exit guards.

[Negative/ServerAdmissionInvariants](Negative/ServerAdmissionInvariants.agda)
applies the theorem to all seven initialized prefix/close histories, the earlier
initialized Server-return counterexample and its recovery suffix. An additional
initialized caller-cancellation/close/result history closes the same socket as an
existing handler while preserving its historical resource records. An explicitly
conditional fixture carries a nonempty, well-formed outbound acquisition capture
through enabled handoff/close writers, with capture/supply/resource certificates;
no initialized outbound history is fabricated for that fixture. An initializer
with an already unbounded promise list refutes unconditional initial supply,
retaining the real theorem's initial-bounds premise. These are invariant controls,
not source-defect or progress claims.

Validation ran serially with Agda 2.8.0 from the standalone library root. These
commands exited 0 with their own `Checking` lines and no warnings:

```sh
agda ConnectionManagement/Properties/ServerAdmissionInvariant.agda +RTS -M4G -RTS
agda ConnectionManagement/Properties/ServerAdmissionInvariants.agda +RTS -M8G -RTS
agda ConnectionManagement/Negative/ServerAdmissionInvariants.agda +RTS -M8G -RTS
```

Accepted logs: `/tmp/cm-server-invariants-20261030/{lift-cases,invariants-direct-final,negative}.log`.
Existing lower resource components also freshly checked transitively. Existing
`Negative/ServerAdmission.agda` and `Negative/ServerAdmissionPrefix.agda` commands
with `+RTS -M8G -RTS` exited 0 as cached regressions, with no `Checking` lines;
logs are `server-existing.log` and `prefix-existing.log` in the same directory.
Three-file local proof audit: zero holes, postulates or unsafe-option
findings; tracked/new-file whitespace checks pass. Imported assumptions were not
given a new term-level axiom audit.

Preliminary results remain distinct: the first broad generic closure exhausted
its 4 GB heap (exit 251); wildcard rejection proofs produced unsolved constraints
(exit 42) and were replaced by exhaustive constructor cases. A slow broad
publication-proof alias instantiation at 8 GB was stopped (exit 130); direct calls
to the two needed projection/initialization lemmas removed that expansion. One
implicit projection-parameter error (exit 42) was corrected before final success.
No native replay or full baseline suite was rerun. The pinned checkout remains
clean and the source pin unchanged. All checker handles are terminal.

Next: inspect and implement pending IG CM-call cancellation/unwind and nonempty
IG exit, preserving shared continuations and source cleanup order. Then compose
Server/PSA/governor scopes on one shared `O.Configuration`. This increment proves
preservation of stored facts through the implemented adapter; it does not finish
raw workers or establish whole-node shutdown, source refinement or liveness.
G0–G5, CM-I4c and SI4/SI5 remain open.


## Twenty-first increment: pending IG calls and nonempty exit

Checked 30 October 2026. The separate [ServerIGExit](ServerIGExit.agda) adapter
extends the normal-action-winner, single-listener, post-setup Server profile.
`ServerAdmission` and its existing guards/theorem types remain unchanged. This
increment implements selected caller-run CM interruption and the actual nonempty
IG catch path; it does not declare complete exception coverage or whole shutdown.

Source was rechecked in the clean network checkout at
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`:

- InboundGovernor.hs:193–207 catches outside the loop, deactivates in STM, drains
  InfoChannel once, then calls `handleError`. At :225–235 it reads the published
  state, traverses its public remote-state map with final transition tracers, and
  rethrows. It neither unregisters those connections nor joins raw workers.
- InboundGovernor/State.hs:76–82 projects remote states without idle timers.
  ConnectionId.hs:41–44 orders remote address before local address. The adapter
  reuses `ConnectionOrder.keyLess` and its explicit family/host/port abstraction;
  it does not establish OS address-order correspondence.
- Core.hs:1111 masks release, :2066 masks promotion, and :2257 leaves demotion
  unmasked. The initial and counter transactions read the map using `readTMVar`;
  they do not acquire a map lease. Release :1250–1254 and promotion :2233–2247
  separate tracing, counter reads and captured cancellation sends. Prune
  :767–777 performs ordered `throwTo` calls without cleanup joins.
- The real mux tracer samples active before a later queue transaction
  (InboundGovernor.hs:633–725). A callback that sampled True can therefore commit
  after deactivation and the final drain.

| Receipt site | Permission and effect |
| --- | --- |
| IG loop boundary or batch wait | No active CM call; preserve body/registry state for catch handling. |
| Release/promotion initial or counter read | Exact call PC, IG inCM, and map actually taken. Initialized controls use a distinct raw worker and check that the ordinary CM read retries. |
| Release send or promotion pruning send | An observed blocked `throwTo`, before target receipt. A send PC alone is not evidence of blocking or delivery. |
| Demotion transaction/assertion/counters/return boundary | Unmasked caller boundary; no false blocked-map premise. |

Every receipt archives the whole actual frame, including captured targets and
remaining pruning victims, then retires only the local call cursors. Already
committed writes, the shared world and other workers remain unchanged; no map
restoration, synthetic target step, handler result or cleanup join is generated.
Dual active frames and masked nonblocking receipt attempts are rejected. The old
call cannot resume after retirement, while unrelated actors can still progress.

Catch handling performs real IG deactivation/drain before a separate snapshot of
the published registry. Duplicate snapshot keys are refused; final rows are
ordered with the existing key comparison. Each final tracer has distinct
invocation and return observations. Normal body exit requires all callbacks to
return. A synchronous failure, or observed async interruption of a blocked tracer
in the MaskedInterruptible catch handler, replaces the original exception and
leaves the failed row unfinished. Body exit, result publication and IG join stay
separate. Final tracing does not clear the registry, and a late queue write does
not imply another drain or prevent the modeled IG exit.

[Properties/ServerIGExit](Properties/ServerIGExit.agda) proves exact active-frame
capture, exact source change (`clearPending` only), unchanged shared world and
raw worker table for every successful receipt. Its generic preservation lift
covers every adapter action and finite execution. The concrete
[ServerIGExitInvariants](Properties/ServerIGExitInvariants.agda) lifts unchanged
outbound capture, entry/promise supply and original handler/stored-resource facts.
Initial supply bounds and existing resource premises remain explicit. This
does not prove live resource ownership, registry validity or universal progress.

[Negative/ServerIGExit](Negative/ServerIGExit.agda) aggregates the acceptance
modules. All initialized histories begin at the real wrapper initializer with
empty admission/socket tables, two actual handoffs, real first-handler birth,
handshake publication, caller completion and IG registration. Hard limits agree
at 10; no injected queue is used to fake an initialized event history.

- `ServerIGExitRelease` interrupts the post-write counter read while the second
  raw worker holds the CM map. Terminating and that worker's lease survive IG join.
- `ServerIGExitSend` adds initialized release interruption before its first
  transaction and during an observed blocked captured send, without target result.
- `ServerIGExitProtocolPrefix` drives real mux startup/on-demand notifications,
  promotion, responder completion, monitor handling and explicit DeltaQ completion
  to a demotion call. `ServerIGExitCases` interrupts promotion before/after commit
  and unmasked demotion after commit. Final tracing reads published Warm while CM
  already contains Idle. It also checks a real sampled-active callback enqueue
  after the drain and unrelated handler progress while final tracing is pending.
- `ServerIGExitControls` checks initialized synchronous/blocked-tracer async
  replacement outcomes. Pruning-send cursor retention and two-key traversal order
  are explicitly conditional data controls, not initialized pruning/multiconnection
  histories. Premature snapshot/result/join, callback shortcuts and whole-Server
  completion are rejected at their tested frontiers.

Validation used serial Agda 2.8.0 checks from this library root. Runtime passed
initially at 4 GB; properties, invariants, branch endpoints and final aggregate
passed at 8 GB with their own `Checking` lines and no final warnings:

```sh
agda ConnectionManagement/Negative/ServerIGExit.agda +RTS -M8G -RTS
```

Logs: `/tmp/cm-ig-exit-20261030/`. Accepted individual evidence includes
`runtime.log`, `properties-final.log`, `invariants.log`, `release-clean.log`,
`protocol-prefix-check.log`, `cases.log`, `controls-final.log`, `send-final.log`;
`aggregate.log` freshly rechecks the aggregate and affected proof endpoints after
EOF cleanup. Data fixtures and remaining properties freshly checked in the
individual runs. Preliminary missing imports/name clashes and a shadowing warning
were repaired; no accepted run retains them. The 13-file strict local proof audit
reports zero findings, and tracked/new-file whitespace checks pass. This is not
a term-level audit of every imported assumption.

Existing `Negative/{ServerAdmission,ServerAdmissionPrefix,ServerAdmissionInvariants}`
also passed serial `+RTS -M8G -RTS` regression checks, exit 0, using cached
interfaces without `Checking` lines. Logs are `regression-*.log` in the same
directory. All checker processes have exited.

Assertions remain enabled; ordinary CM diagnostic tracers retain their earlier
total/nonblocking profile. Other receipt windows, initialized pruning-send history, arbitrary tracer
or finalizer failures, other Server race winners and multiple listeners remain
open. No native replay, full baseline rebuild, production patch or new deployed
defect is claimed. Next: compose this Server/handler adapter with
`PeerSupervision`/`GovernorPool` on one shared `O.Configuration`, preserving both
adapters' pending calls, actor freshness and scope certificates. G0–G5, CM-I4c and
SI4/SI5 remain open; raw admission workers are still outside owned scope joins.


## Twenty-second increment: shared Server and peer supervision

Checked 30 October 2026, after `16bf47c`. This is the first shared runtime for
the selected Server/handler/IG adapter and PSA/governor supervision. It preserves
the earlier modules and theorem types. Physical peer bundle start/result coupling,
other Server outcomes and whole shutdown remain open.

The clean network checkout remains at
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`. Source ownership was rechecked:
Diffusion.hs:739–759 supplies the combined CM/IG to Server; :800–826 puts
`withPeerStateActions` inside its callback, around the peer-selection providers,
governor and churn Async scopes. PeerStateActions.hs:620–638 supplies the outer
queue-free monitor JobPool. PeerSelectionActions.hs:84–102 encloses local-root
provider lifetime inside ledger-provider lifetime. Server.hs:147–186 separately
owns its callback, accept loops and IG race, with the IG/CM nesting already mapped
in increment 21. Thus peer scopes must finish before that callback body exits;
their completion cannot certify the raw admission Asyncs created by acceptLoop.

The retained profile starts after scope setup and follows the existing normal
callback-return Server branch. The production Diffusion `waitAny` failure/IG
winner outcomes are not silently treated as normal returns. Their exceptions,
other Server race winners, setup failures and multiple listeners remain separate
integration obligations. Scope-body exits and cancellation receipt still use
the existing observed-operation contracts, without eventuality assumptions.

[PeerContext](PeerContext.agda) contains every peer-side subsystem/policy field,
pool, physical monitor, region, detached cleanup frame and scope state, but no
`O.Configuration`. Its reconstruction function takes the current Server source.
`source-exact`, both round-trip laws and `rebase` hold for arbitrary contexts
without a synchronization premise. [ServerPeers](ServerPeers.agda) stores this
context alongside one `ServerIGExit.State`, which contains the sole CM copy.
Peer writes replace that authoritative source while preserving Server physical
metadata; Server writes keep the peer context and become immediately visible
through reconstruction. No step restores a saved peer-side world.

Common CM actions execute through the existing physical Server adapter, with
PSA/governor caller-running, ownership and region permissions checked as well.
Acquisition region bookkeeping advances with the actual resulting source.
The separate raw peer-core and Server-outbound aliases are refused. New caller,
child, monitor and admission identities are checked against both sides' history,
including requested children and sockets reserved before resource allocation.
New unowned CM calls and peer-owner actions cannot start after callback exit.
Unrelated already-running source actors retain their lower permissions.

Protocol starts with nonempty bundles and independent logical protocol-result
publication cannot stand in for the physical mux/controller lifecycle. The raw
peer shortcuts for those operations are excluded until their actual coupling is
implemented. Empty bundle traversal, policy, caller work, control changes and
the implemented peer cleanup/scope operations retain their existing semantics.
This selected action profile is explicit; there is no enabled-step completeness
or full peer-lifecycle claim.

[Properties/ServerPeers](Properties/ServerPeers.agda) establishes exact shared
source and successful-step observations. Each shared finite execution projects
to real governor-pool, monitor-pool and inner-scope metadata executions, retaining
real CM writes in the combined source. This is not a projection to a raw full
peer execution that pretends Server interference is a source stutter.
`callback-from-initial` derives terminal results for every handle in the two
captured pool snapshots, plus all four inner-scope joins, from an initialized
execution and an actual successful callback-return step. It requires no separate
externally asserted pool/scope-closure arguments. Those three components alone
still do not certify admission workers, handlers or whole Server shutdown.

[ServerPeersSupply](Properties/ServerPeersSupply.agda) proves preservation through
every implemented shared action and arbitrary finite execution of unchanged
outbound capture/supply validity paired with detached governor-capture validity.
Initialization requires only the original shared entry/promise supply bounds.
The new [ServerIGExitEntries](Properties/ServerIGExitEntries.agda) proof retains
any existing entry through Server interference, using actual lower source traces
and unchanged handoff/socket effects. This supplies the detached cleanup premise
without strengthening transition guards to assert capture validity. Broader
resource/reference/ownership invariants remain distinct CM-I4c obligations.

[Negative/ServerPeers](Negative/ServerPeers.agda) contains the fixtures and two
initialized histories as nested modules, plus the initialized freshness control:

- `ServerPeers.Interleaving.initialized` has 58 actions. Two actual accepted
  handoffs precede a real policy-selected establishing job, reservation/promise
  allocation and socket open through the common CM route. Governor cancellation
  detaches the exact cleanup frame. A raw admission worker captures the shared
  map; detached cleanup closes its socket but its removal read genuinely retries.
  The admission's failed fork restores the map without undoing its entry write.
  Cleanup then removes its captured reservation and counts before body unwind,
  deregistration, Async result and join. Peer/provider/monitor scopes finish
  before callback return. The nonempty governor snapshot has its derived result
  certificate; both raw admissions remain incomplete. Capture/supply is also
  instantiated while a detached capture survives the admission's entry write.
- `ServerPeers.IGExit.initialized` has 81 actions. It reuses the checked real admission,
  handshake, IG registration and release prefix. Empty peer pools/scopes close
  while the release's entire pending frame and another worker's map lease remain
  unchanged. Only afterwards does the Server callback return, followed by the
  checked selected receipt, deactivation/drain, nonempty final tracing, result
  publication and IG join. This does not infer CM or whole Server completion.
- A separate three-action initialized unowned CM request reserves its future
  child/socket. Controls reject their reuse, peer/raw identity collisions, old
  caller resumption after detachment, early results/callbacks, both core aliases,
  logical result publication and a new caller after callback exit.

Validation ran serially with Agda 2.8.0 from the standalone library root. Context
and initial runtime checks passed at 4 GB. Entry retention, shared supply,
projection/callback certificates and branch/aggregate checks passed at 8 GB,
with own `Checking` lines and no final warnings. Final acceptance command:

```sh
agda ConnectionManagement/Negative/ServerPeers.agda +RTS -M8G -RTS
```

Logs are in `/tmp/cm-server-peers-20261030/`: `context.log`, `runtime.log`,
`supply.log`, `properties-final.log`, `interleaving-check.log`, `ig.log`,
`aggregate.log` and `aggregate-final.log`. The last aggregate freshly rechecks
the callback certificate and both branch modules after their final edits; the
earlier aggregate freshly checked the final runtime, supply and fixtures.
Preliminary import/name-clash errors, one missing random-generation update in an
expected snapshot, a projection-equality proof error and an implicit-state meta
were repaired before acceptance. An early fixture import warning was also fixed.
No old theorem was weakened, no hole or trust assumption introduced, and no
termination/safety check disabled. The six-file strict local proof audit reports
zero findings; tracked/new-file whitespace checks pass. This local scan does not
audit every transitive dependency at term level.

The acceptance fixtures and both histories were subsequently consolidated into
`Negative/ServerPeers.agda`, under `Fixtures`, `Interleaving` and `IGExit`.
Their definitions/proofs are unchanged apart from module boundaries and fixture
aliases. A fresh check of that single file passed at 8 GB, exit 0, no warnings;
log: `consolidated.log` in the same directory. The six-file audit above covers
the consolidated layout; the individual/aggregate logs retain the earlier split
layout's evidence. Runtime and reusable property modules remain separate.

Existing `Negative/PeerSupervision.agda` and `Negative/ServerIGExit.agda` also
passed serial `+RTS -M8G -RTS` regression checks, exit 0, no warnings. The peer
endpoint and its affected dependency closure had fresh `Checking` lines; the IG
endpoint used cached interfaces. Logs: `regression-PeerSupervision.log` and
`regression-ServerIGExit.log` in the same directory. All checker processes exited.

No native replay, full baseline rebuild, production patch or new deployed source
finding is claimed. Next: couple peer bundle starts and result observations to
the actual physical mux/job/controller path on this shared source, then exercise
nonempty PSA monitor integration and widen callback/race outcomes with their
exact exception semantics. G0–G5, CM-I4c and SI4/SI5 remain open.

## Twenty-third increment: peer initiator starts and physical results

Checked 30 October 2026, after commit `82f6435`. The selected
`ServerPeers.Protocols` extension now joins actual PSA bundle calls to the
physical mux/controller/job lifecycle on the existing single CM source. Runtime,
properties and supply proofs remain in their existing modules; fixtures and all
new histories are nested in `Negative/ServerPeers.Protocols` in the existing
[acceptance file](Negative/ServerPeers.agda). No additional fixture files.

The clean network checkout remains pinned at
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`. The following branches were
rechecked in that local checkout:

- PeerStateActions.hs:1149–1195 traverses the requested temperature bundle with
  eager initiators, then separately publishes the map of completion actions.
- network-mux Mux.hs:737–809 resolves the protocol and direction, checks mux and
  per-direction status, marks Running, allocates an empty completion cell and
  queues the start in one caller transaction. A read retries while Ready; after
  Stopping/Stopped/Failed, a filled local cell takes precedence over Shutdown.
- Mux.hs:415–445 selects typed JobPool results before control commands, and
  commands before on-demand readiness. :491–519 traces an already selected eager
  command and then physically forks it. Later queue arrivals do not undo selection.
- Mux.hs:295–361 separates protocol return/egress drain, clean Idle/cell commit,
  body return and JobPool publication. Its synchronous error handler fills the
  error cell without resetting Idle; asynchronous cancellation is a separate path.
  InboundGovernor.hs:633–725 ignores initiator start/completion traces for responder
  counters and notifications, though the real tracer reads its active variable.

`canInitiate handle protocol` is an immutable initiator-direction capability
contract. A responder descriptor alone does not establish that capability.
Each successful caller step advances the real PSA job and allocates a fresh
RunId/cell plus queued command; it does not invent a physical JobId. Commands
retain how many legacy commands precede them, preserving their relative FIFO
order across later appends and successful legacy pops. Selection checks the real
typed FIFO, current owner/controller permissions and registration gap. Explicit
normal start-trace invocation/return precedes actual Pool.fork and separate
registration. Selected starts retain their place while unrelated child results
or later stop commands arrive.

Every physical job captures direction, owner, mux, protocol number and generation.
Local completion delegates to the existing physical clean/error transition.
Only the matching current generation may update the PSA cache; old completion
cells remain independently readable. Fresh generations are inserted first, so
lookup cannot mistake an old clean cell for the current running generation.
The conditional real restart-step control covers this ordering, old-result
retention and stale-cache rejection. A synchronous-error slot stays busy.
Legacy independent logical publication and observed raw initiator-fork aliases
remain refused; initiator results do not enter the old responder pending table.

[Properties/ServerPeers](Properties/ServerPeers.agda) proves actual physical
fork/job evidence and projects every implemented protocol execution to the real
peer pool/scope metadata paths. `callback-from-protocols` derives the unchanged
component certificates from initialization and actual callback return, with no
externally supplied closure gates. [ServerPeersSupply](Properties/ServerPeersSupply.agda)
preserves the original outbound capture/supply and detached governor-capture
predicate through all new steps and finite executions, retaining only the
original initial supply bounds. These proofs do not assert a new full runtime
resource invariant or enabled-step completeness.

Acceptance evidence in the nested `Protocols` module:

- An 85-action initialized prefix performs actual accepted handoffs, handshake,
  IG registration and physical mux startup. A real governor establishment job
  selects the existing inbound duplex handle through the common CM route,
  completes its empty warm/established traversal, and physically forks/registers
  PSA monitor 50. Policy then selects activation and reaches the hot bundle.
  Governor samples are 10/11/12, after IG registration at 10; absolute activation
  and promotion metadata are shifted consistently.
- A 25-action suffix requests protocol 1, processes the older responder command,
  selects/traces/forks initiator 20, and commits a clean result before parent
  registration and bundle publication. It then completes the governor job,
  physical body/FIFO/deregistration/Async result and ignored initiator completion
  trace/DeltaQ. Assertions distinguish local cell, published peer observation,
  physical body and Async result, and check no initiator IG counter events.
- A further 33 actions close the actual inner scopes and governor pool, then
  capture the nonempty PSA monitor snapshot [50], cancel/unwind/deregister it,
  publish its Async result and join it before callback return. The complete
  initialized history has 143 actions and an instantiated monitor certificate.
  Raw admissions remain incomplete and the physical handler pool remains open.
- Initialized branches cover a selected start forking after a later shutdown
  command and infrastructure result (95 actions); mux failure waking an empty
  queued cell through Shutdown before any job birth (92); a synchronous protocol
  error retaining its busy slot (94); real same-number initiator/responder
  coexistence, including actual responder notifications (100); and a committed
  local clean result winning after later mux failure (99).
- Controls reject priority violations, uninvoked tracer return, raw physical
  fork/commit aliases and premature observations. Restart ordering is checked
  from an explicitly conditional second-activation PC; no second initialized
  policy cycle is claimed.

Validation ran serially with Agda 2.8.0 from this library root. Runtime initially
passed at 4 GB; supply/properties and acceptance passed at 8 GB. After generation
ordering was corrected, `acceptance-generation-order.log` freshly checked the
runtime, both property modules and acceptance endpoint, exit 0. The extended
direction/result-priority/restart acceptance also freshly passed at 8 GB, exit 0,
with its own Checking line and no warnings (`acceptance-directions.log`).
The final EOF-clean acceptance also freshly passed, exit 0, own Checking line,
no warnings (`acceptance-final.log`). The command for these acceptance checks was:

```sh
agda ConnectionManagement/Negative/ServerPeers.agda +RTS -M8G -RTS
```

Serial regressions for `Negative/PeerSupervision.agda`, `Negative/ServerIGExit.agda`,
`Negative/MuxProtocolJobs.agda` and `Negative/MuxInitiatorTraceCM.agda`, each with
`+RTS -M8G -RTS`, passed from cached interfaces, exit 0, no warnings.
Logs are under `/tmp/cm-peer-protocols-20261030/`, including
`regression-<endpoint>.log`. All checker processes exited. The four-file strict
local proof audit reports zero findings and `git diff --check` passes. This is
a local scan, not a term-level audit of every imported dependency. No full
baseline rebuild was run.

Preliminary parse/name-clash errors, two shadow warnings, a case-reduction
proof error and a fork-step equality witness were repaired before acceptance.
Source review corrected clock alignment and the fresh-generation insertion
order; both now have executable controls. No old theorem type was weakened,
no trust assumption or hole introduced, and no safety/termination check disabled.

The start-tracer profile currently admits normal return only; tracer failure/
cancellation unwind remains open. Caller start failures are observable source
error frontiers, not executed exception-policy continuations or deadlock claims.
The Shutdown completion-action observation is modeled, but the old PSA waiters
still need explicit coupling of that observation to their policy continuation.
A fully initialized restart, wider Server callback/race outcomes, CM-I4c,
SI4/SI5 and the overall G0–G5 gates remain open. No native replay, production
source patch, new deployed defect, source refinement, fairness/delivery theorem
or whole-shutdown result is claimed by this increment.

## Twenty-fourth increment: physical completion reads in peer waiters

Checked 30 October 2026, on the uncommitted increment 23 work after
`82f6435`. `ServerPeers.Protocols` now connects the physical completion-action
observations to the selected PSA monitor/deactivation/close continuations.
All new runtime/proofs remain in their existing files; new acceptance is nested
under `Protocols.Waiters` in [Negative/ServerPeers](Negative/ServerPeers.agda).

The network pin remains
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`, with its local checkout clean.
The following source branches were rechecked:

- PeerStateActions.hs:255–278 distinguishes returned/error, NotRunning and
  NotStarted. :361–423 first reads the published result-action map. First-to-finish
  folds ascending protocol numbers with orElse, then retries if the selected
  action returns NotStarted/NotRunning. A live action that retries permits trying
  later actions. All-to-finish sequences every action before collecting outcomes;
  an available error cannot bypass another action's retry.
- PeerStateActions.hs:664–768 checks Cold/Cooling before established, warm and
  hot first-result alternatives. An error cools the peer; a hot success invokes
  deactivation and a warm/established success invokes close.
- PeerStateActions.hs:986–1105 waits for all hot results during deactivation,
  and all three bundles during close. Clean deactivation retires its result map.
  Errors take the operation's failure path; close errors do not release outbound
  ownership.
- Governor/ActivePeers.hs:979–1045 waits for PeerCold (or its own demotion timeout)
  in the deactivation job's exception handler, before returning a governor
  completion. Mux.hs:795–809 still gives a filled local cell priority over
  Shutdown for Stopping/Stopped/Failed.

The new published-cell view preserves unpublished cells, frozen NotRunning/old
published values and exact captured peer/handle/mux identities. Reads retain
`localResult` versus `shutdownResult status`; no synthetic ErrorId or physical
protocol result is used for Shutdown. First/all views preserve map ordering and
bundle precedence. The result-action observation remains live rather than being
memoized into a local completion cell.

`pollResults`, `waitJobResults` and `waitMonitorResults` use the actual physical
monitor ownership, queued-job flag, governor body-running/parent-gap checks,
policy stage and callback permissions. Cached logical poll/wait aliases are
refused in this extension. Successful local-result and Cold/demotion paths reuse
the original lower steps, retaining their physical body-return bookkeeping.
Selected error reads update peer status and/or the captured job/followup PC to
the existing failed-operation boundary. They preserve the authoritative CM,
mux state, physical protocol cells/jobs/FIFO and all Async pools; they do not
make a peer Cold or publish a governor completion.

`Properties/ServerPeers.Protocols.reading-source` and `reading-physical` prove
those source/physical/frontend equalities for the read-update constructor.
The existing execution projections, callback component certificates and
capture/supply preservation now cover the new events without new initial
premises. Their theorem types, and all earlier theorem types, remain unchanged.

Acceptance includes three new initialized histories:

- `initialized-monitor-shutdown` (94 actions): a queued protocol has no physical
  body when an actual infrastructure result fails its mux. The new read is
  blocked before bundle publication; after publication it cools the real peer
  through its actual monitor. No protocol result or FIFO entry is manufactured,
  and Cold still waits for CM demotion.
- `initialized-local-continuation` (103): a committed local clean result wins
  after later mux failure. The real monitor creates a deactivation followup,
  waits for all hot results, retires the hot result and reaches successful
  deactivation while the physical protocol Async body is still running.
- `initialized-job-shutdown` (126): activation returns with its eager command
  still queued. Actual completion/target/policy steps at times 13/14/15 launch
  and register governor deactivation job 2. Mux failure then wakes its all-hot
  wait through Shutdown. The job remains bodyRunning at awaitCold failed,
  without a governor completion or outbound release; protocol 20 never had
  a physical body.

Conditional controls cover multi-protocol retry/error combinations, inactive
first-action behavior, established-before-hot priority and close-all failure
without release. They also reject reads by a different monitor, interrupted
monitor/job, completed policy profile, raw logical aliases and a pending close.
These additional protocol/close snapshots are not claimed to have initialized
physical histories.

Validation ran serially with Agda 2.8.0 from the standalone library root.
Runtime passed at 4 GB (`runtime.log`); the initial supply lift passed at 6 GB
(`supply.log`). The basic aggregate freshly checked runtime, both property
modules and the acceptance file at 6 GB, exit 0, no warnings
(`acceptance-basic.log`). The final aggregate with all policy/conditional controls
freshly checked the acceptance file at 6 GB, exit 0, no warnings
(`acceptance-clock.log`), retaining the checked dependency interfaces:

```sh
agda ConnectionManagement/Negative/ServerPeers.agda +RTS -M6G -RTS
```

Logs are in `/tmp/cm-peer-waiters-20261030/`. An intermediate
`acceptance-policy.log` failed at an expected-snapshot clock mismatch, after
freshly checking the final runtime and both property modules: activation at
13 schedules failure clearing at 73, rather than the reused snapshot's 63.
The metadata clock conversion now shifts that absolute deadline as well as
promotion/activation times; the final aggregate checks the corrected history.
The static audit initially mistook qualified infix `Nat.<?` for a hole; using
the equivalent qualified prefix spelling makes the scan unambiguous. No proof
hole was involved. EOF whitespace was also repaired.

The four-file strict local proof audit reports zero findings; `git diff --check`
passes. Serial `Negative/PeerSupervision.agda` and `Negative/MuxProtocolJobs.agda`
regressions with `+RTS -M6G -RTS` passed from cached interfaces, exit 0, no warnings;
logs are `regression-PeerSupervision.log` and `regression-MuxProtocolJobs.log`
in the same directory. All checker processes exited. No old
theorem type was weakened, no postulate/trust assumption introduced, and no
safety or termination check disabled. This local scan does not audit every
imported dependency at term level.

The selected read/continuation granularity retains the existing normal PSA
tracer profile. Monitor followup failures still use the existing separately
observed synchronous exception handler; this increment does not derive a
concrete `MiniProtocolExceptions` identity or implement its tracer faults.
Additional close/multi-protocol controls remain conditional, not new initialized
end-to-end close histories. No native replay, full baseline rebuild, new deployed
defect, source refinement, fairness/liveness or whole-shutdown theorem is claimed.
Next: source-check and implement synchronous/asynchronous initiator start-tracer
failure/unwind at the selected command, retaining its empty completion cell and
joining actual physical children. A full initialized restart, broader callback/
race outcomes, CM-I4c, SI4/SI5 and G0–G5 remain open.

## Twenty-fifth increment: selected initiator start-tracer faults

Checked 30 October 2026, on uncommitted increments 23–24 after `82f6435`.
`ServerPeers.Protocols` now couples observed synchronous/asynchronous exceptions
from an invoked eager initiator start tracer to the existing physical unwind
machinery. All acceptance remains in the existing
[Negative/ServerPeers](Negative/ServerPeers.agda), nested under `Protocols.StartTrace`.

Source was rechecked at network pin
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`:

- ConnectionHandler.hs:329–380,408–452 explicitly unmasks Mux.run. Mux.hs:242–278
  runs its monitor in the JobPool body and catches SomeAsyncException outside
  that pool bracket. Pool closure precedes the asynchronous Failed/Dead catch.
- Mux.hs:491–519 calls TraceStartEagerly before entering forkJob/forkJobOn.
  JobPool.hs:70–80,105–137,153–172 supplies the bracket, cancellation snapshot,
  masked parent birth/registration and restored child bodies. An exception
  inside the invoked tracer is distinct from the later masked insertion gap.
- InboundGovernor.hs:633–758 samples its active variable but ignores initiator
  start traces for responder counters/notifications. The sync throwing input
  here concerns a supplied custom tracer, not an invented failure of that normal
  ignored IG branch.
- The Mux catch handles asynchronous exceptions only. A synchronous start-tracer
  exception closes the entered pool and propagates without writing Failed;
  overwriting it with an asynchronous-style status would change the source.

`startTraceSelection` requires an invoked tracer cursor, actual monitoring
owner/mux, matching captured call, empty cell and no physical thread for that
call, plus the existing controller/unwind guards. It calls the existing
`MuxStartupUnwind.start` with the actual frame and pool-body route.
`failedC` retains the generation and exception, preventing normal tracer return,
late fork or duplicate receipt. The raw group-abort shortcut is also refused
while this start owns the controller. Independent children retain their lower
return/publication/removal guards.

Fault capture changes only the selected unwind record and frontend cursor;
`start-fault-source` and `start-fault-physical` prove exact preservation of CM,
physical protocol state and caller cells. The acceptance instantiates the
existing `MuxStartupUnwind.Selection` certificate from the actual pre-state.
Generic supply/capture preservation, peer-pool/scope projections and callback
component certificates cover all added events without new initial premises.
Earlier theorem types and lower failure-site guards remain unchanged.

`deliverStartTraceShutdown` separately requires the Server's actual closingCM
stage and the coordinator's pending target. It then uses the guarded
`W.control acknowledgeDelivery` result after selecting the same actual async
fault. The raw shutdownStep acknowledgement remains refused; ordinary async
observation does not acknowledge an unrelated pending CM sender. This receipt
updates the coordinator and fault metadata, without certifying a handler result.

Initialized acceptance shares the real 90-action prefix through admission,
handshake, IG/startup, peer activation request, controller selection and actual
start-tracer invocation:

- A generic 14-action unwind cancels both actual infrastructure handles,
  observes their body unwind, deregisters/publishes Async results and joins
  snapshot [1,0]. Closure retains the empty initiator cell and proves that
  protocol 20 never acquired a physical body or typed completion.
- `StartTrace.Sync.initialized-outcome` reaches the buffer-unwind boundary in
  106 actions. Mux status remains Ready and the empty completion action still
  retries. An explicit subsequent bundle-publication step also leaves the
  published waiter retrying. This finite boundary is not a universal deadlock
  or implementation defect claim.
- `StartTrace.Async.initialized-outcome` has 110 actions: only after pool closure
  does the real catch write Failed, invoke/sample/commit Dead and finish that
  callback. The actual IG tracer emits MuxFinished. Two further real peer steps
  publish the bundle and consume Shutdown to cool the peer (112 actions).

Conditional CM component controls exercise snapshot/read/send, exact receipt,
the same physical cleanup and catch, and the continuing handler-result wait.
They assume a closingCM pre-state; neither initialized reachability nor whole
peer/IG-scope validity of that component snapshot is claimed. The existing
Server guard prevents starting CM shutdown during the live callback. A complete
initialized peer/IG scope-exit prefix with this start still pending remains open.
In particular its real inactive-IG Dead branch must not be replaced by the
active-IG callback used in the conditional component control.

Other controls reject faults before invocation or in the masked registration
gap, late fork/return, duplicate receipts, raw acknowledgement/abort, receipt
during the callback, early join/pool close and early asynchronous Failed writes.
Receipt and pool closure remain distinct from the handler's Async result.

Validation ran serially with Agda 2.8.0 from this library root. Initial runtime
and supply checks passed at 4 GB and 6 GB. The final runtime, generic properties
and supply lift were freshly checked transitively at 6 GB during the guarded
aggregate attempt; the final acceptance file then freshly passed at 6 GB,
exit 0, own Checking line and no warnings:

```sh
agda ConnectionManagement/Negative/ServerPeers.agda +RTS -M6G -RTS
```

Logs are under `/tmp/cm-start-trace-20261030/`; final success is
`acceptance-final.log`. Preliminary logs record a repaired parenthesis/coverage
error and nested acceptance-name clashes. Source review also corrected an
unusable raw-acknowledgement delegation and retained the Server CM-stage guard;
the CM component controls are explicitly conditional, rather than asserting an
unproved initialized scope-exit path. Existing theorem types and guards were not
weakened. No postulate, proof hole, unsafe option or termination bypass was added.
Serial `Negative/MuxStartupUnwind.agda` and `Negative/MuxInitiatorTraceCM.agda`
regressions with `+RTS -M6G -RTS` passed from cached interfaces, exit 0, no
warnings. Logs are `regression-MuxStartupUnwind.log` and
`regression-MuxInitiatorTraceCM.log` in the same directory. All checker processes
exited. The four-file strict local proof audit has zero findings and
`git diff --check` passes. This is a local scan, not a term-level audit of every
imported dependency.

No native replay, production patch, deployed finding, source refinement or
universal progress/shutdown result is claimed. The sync Ready/empty-cell boundary
is finite model evidence under the supplied tracer contract, not a permanent
blocking conclusion. Buffer-provider unwind/handler cleanup and concrete tracer
failures in later callbacks retain their existing explicit boundaries.
Next: build the actual peer-pool/provider/IG scope-exit prefix while retaining
this pending start, then check CM-owned receipt and the inactive-IG catch through
that initialized history. A full initialized restart, wider callback/race
outcomes, CM-I4c, SI4/SI5 and overall G0–G5 remain open.

## Twenty-sixth increment: initialized scope exit and CM start cancellation

Checked 31 October 2026, after `82f6435`, with increments 23–25 still
uncommitted. The new `Protocols.StartTrace.ScopedCM` acceptance in the existing
[Negative/ServerPeers](Negative/ServerPeers.agda) reaches CM-owned start-tracer
cancellation through actual peer/Server/IG scope exit. It uses the existing
runtime and proof modules; no runtime guard or theorem type changed.

The source pin remains
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`. Diffusion.hs:804–826 and
PeerStateActions.hs:620–638 locate the nested peer/provider/governor/churn scopes
inside the Server callback. Server.hs:147–186 orders callback/accept/IG scope
exit; Core.hs:523–550 supplies CM's snapshot, late read, sequential delivery
acknowledgement and collective handler-result wait. InboundGovernor.hs:633–728
makes the later Dead callback conditional on the active variable: after IG
deactivation it neither enqueues MuxFinished nor clears the counters. The local
checkout remains clean; no production replay was rerun.

The 173-action initialized history is assembled from independently checked
finite paths, with shallow expected snapshots and explicit `V.advance` proofs:

- The existing 90-action prefix reaches the real invoked initiator start tracer.
  Its caller has allocated an empty result cell, advanced to publishBundle, and
  selected the command, but protocol 20 has no physical body.
- Thirty-nine actions cancel/join the real inner scopes, nonempty governor pool
  [1], and PSA monitor pool [50], then return the callback. Governor job 1 is
  cancelled while its hot-bundle publication is pending. Its actual no-CM-caller
  unwind, deregistration, Async result and join are separate steps. Monitor 50
  is likewise cancelled, unwound, deregistered, published and joined.
- The successful callback step derives both nonempty pool terminal certificates
  and all four inner joins through `callback-from-protocols`. The abandoned
  publisher's original PC and the handler's invoked tracer cursor remain stored.
- Twenty actions publish/join the Server callback/accept scope, receive the real
  IG loop-boundary cancellation, deactivate/drain IG, snapshot its nonempty
  published row, invoke/return final tracing, publish/join the IG result and
  enter closingCM. The pending start survives all these steps.
- Five actual CM snapshot/read/send/receipt/traversal actions acknowledge delivery
  to that same handler. No stage assignment from the earlier conditional
  `CM.withCoordinator` fixture is used as initialization evidence.
- Fourteen actions cancel, unwind, deregister, publish Async results and join the
  actual infrastructure handles [1,0]. Only then do five catch actions write
  Failed and invoke/sample/commit/finish Dead. Sampling observes IG inactive,
  so the queue stays empty and the old responder counters remain present.

`initialized-scoped-catch` is the complete initialized endpoint;
`initialized-peer-exit`, `initialized-cm-entry`,
`initialized-receipt-scoped` and `initialized-physical-close` expose its actual
intermediate milestones. Generic supply/capture validity is instantiated at the
milestones and final state, with only the existing initial supply bounds.
`scope-certificates`, `governor-terminal` and `monitor-terminal` derive
certificates for the actual nonempty captured snapshots.

Controls reject early callback return or CM entry, publisher resumption after
cancellation, a PSA poll after exit and late tracer return. Assertions preserve
the exact empty cell, absence of an initiator job, nonempty IG snapshot and real
physical joins. Reading the completion action after the catch returns the actual
Shutdown observation. The handler result is still unavailable, and CM's
finishClose still refuses: physical pool closure does not complete the buffer/
handler finalizer or its Async result. The active-IG catch in increment 25's
conditional component control remains distinct; this initialized history
supplies the missing inactive-IG branch.

Validation used Agda 2.8.0 serially from this library root. The complete
acceptance file freshly passed twice with its own Checking line, exit 0 and no
Agda warnings (`scoped-6g.log`, then EOF-clean `final.log`). All new milestones,
certificates, source/supply instances and existing acceptance are checked together.
Logs are in `/tmp/cm-scoped-start-20261030/`; work and final checking crossed
into 31 October. Earlier checks exhausted 2 GB, 2800 MB and 4 GB heaps without
reporting a proof error. The sandbox also blocked the user scope bus, so bounded
scope execution required escalation.

The first successful scope used 5 GB RAM / 2 GB swap with a 6 GB heap. That
placed the heap above the RAM cap, contrary to the repository's resource
guidance. Final verification corrects this to a 6 GB heap below a 7 GB RAM cap,
with swap disabled:

```sh
systemd-run --user --scope -p MemoryMax=7G -p MemorySwapMax=0 -- \
  agda ConnectionManagement/Negative/ServerPeers.agda +RTS -M6G -RTS
```

Final serial verification passed under that corrected scope, exit 0: acceptance
and the two regressions `Negative/ServerIGExit.agda` and
`Negative/MuxInitiatorTraceCM.agda` all used cached, current interfaces and emitted
no warnings. The scope ran `/tmp/cm-scoped-start-20261030/verify.sh`, which stops
on any failed command. Logs: `accepted-final.log`,
`regression-ServerIGExit-final.log`, `regression-MuxInitiatorTraceCM-final.log`
and `final-scope.log`. The 2 GB regression attempts had exhausted their heaps
while loading cached interfaces; their earlier logs are retained. All checker
processes exited. The redundant parenthesis and EOF whitespace were repaired before
acceptance. No runtime, previous theorem type, transition guard or initial
premise was weakened. The four-file strict local proof audit has zero findings;
no new postulate, proof hole, unsafe option or termination bypass was added.
This is a local scan, not a term-level audit of every imported dependency.

This remains the existing selected normal callback-return/observed-cleanup
profile. Production Diffusion failure/other race outcomes and provider/tracer
behavior retain their explicit boundaries. No native replay, full baseline
rebuild, new deployed defect, source refinement or universal shutdown/progress
theorem is claimed.

Next: continue from `scopedReady` through the real buffer-provider outcome,
captured handler finalizer/cleanup and Async result publication. Then let CM's
actual collective result wait finish and check Server return, keeping the raw
admission-worker obstruction explicit. A full initialized restart, broader
failure/race profiles, CM-I4c, SI4/SI5 and overall G0–G5 remain open.

## Twenty-seventh increment: initialized handler result, CM wait and Server return

`Negative/ServerPeers.Protocols.StartTrace.ScopedCM.Completion` continues the
previous initialized history through twelve actual transitions, reaching Server
return after 185 actions. All acceptance remains in `Negative/ServerPeers.agda`.
No runtime, prior theorem statement, initializer premise or guard changes in
this increment.

The source mapping was rechecked at the unchanged clean network pin
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`.
Core.hs:584–713 places handler cleanup inside `finally`: its OutboundDup branch
writes Terminated Nothing and purges only the matching map identity, closes the
captured socket while holding the map, publishes the map, then reads counters.
This branch has no TIME_WAIT delay. Core.hs:523–550 captures handler Asyncs
through sequential exception-delivery acknowledgements, then collectively waits
for their results. Map removal and delivery receipt do not discharge that wait.

The continuation starts at `scopedReady`, after the physical pool and inactive-IG
Dead callback have actually finished. It hands off the original async outcome,
observes normal buffer-provider return and the handler body exit, enters its
captured finalizer, then takes/selects/updates/closes/publishes/counts through the
actual cleanup rules. Cleanup completion and handler Async result publication
are separate steps. Only then do actual CM finishClose and Server finishServer
steps succeed. The published body outcome remains the original async trace
exception 181. The terminated entry remains in the heap, the map is empty and
the captured socket is closed; no protocol body is invented for the empty cell.

`initialized-server-finish` composes the complete initialized execution rather
than installing a terminal stage. `server-finish-supply` instantiates the existing
generic supply/capture theorem with the original initial bounds.
`physical-final-wait` retains the actual lower handler result table, captured
coordinator and successful physical wait observation. Controls reject CM closure
before result publication, result publication before cleanup completion, a
TIME_WAIT action on this branch, late tracer return and cancelled peer publication.
Neither body exit nor cleanup completion alone makes the Async result available.

The final raw-worker table still contains the second admission worker at its
calling PC. `no-universal-raw-worker-completion` uses this initialized history to
refute the implication that Server return entails all raw-worker results. This
preserves the SI5 obstruction already documented by the earlier standalone model
and native replay; it adds integrated initialized evidence, not a new deployed
defect or a proof of permanent blocking. SI5 is not weakened to owned-scope
completion.

The selected normal callback-return, buffer-provider return and cleanup
observations remain explicit contracts. This finite history does not establish
universal delivery, shutdown, liveness or source refinement. No native replay,
full baseline rebuild or term-level dependency audit is part of this increment.

Validation on 31 October used Agda 2.8.0 serially from this library root, with
a 6 GB heap under a 7 GB RAM / zero-swap scope. The first check produced a new
interface without diagnostics, but its terminal tool status was lost across
context compaction. To retain explicit exit evidence, only this endpoint's
interface was invalidated and the final acceptance freshly checked again:

```sh
systemd-run --user --scope -p MemoryMax=7G -p MemorySwapMax=0 -- \
  sh /tmp/cm-handler-finish-20261031/verify.sh
```

The script stops on any failure and runs these commands, each with
`+RTS -M6G -RTS`:

- `agda ConnectionManagement/Negative/ServerPeers.agda`: fresh own Checking
  line, exit 0, no warnings (`acceptance-final.log`).
- `agda ConnectionManagement/Negative/MuxHandlerExit.agda`: cached regression,
  exit 0, no warnings (`regression-MuxHandlerExit.log`).
- `agda ConnectionManagement/Negative/MuxInitiatorTraceCM.agda`: cached
  regression, exit 0, no warnings (`regression-MuxInitiatorTraceCM.log`).

All logs and recorded command exits are under
`/tmp/cm-handler-finish-20261031/`; `verification-scope.log` records the scope and
`results.log` its three successful checker exits. All processes are terminal.
The four-file strict local proof audit has zero findings and `git diff --check`
passes. No new postulate, hole, unsafe option or termination bypass was added;
this scan does not audit every imported term. The source pin, handovers,
presentation, `.claude` and output remain unchanged. No commit was made.

Next: build a fully initialized second hot activation/protocol generation from
the serving branch, using actual governor/PSA transitions and the existing
per-generation physical result cells. Preserve old-result readability and reject
stale bundle reuse. This is protocol restart while Server is serving; the returned
Server is not restarted by assigning a new stage. Broader failure/race profiles,
CM-I4c, SI4/SI5 and the overall G0–G5 objective remain open.

## Twenty-eighth increment: initialized second hot activation

`Negative/ServerPeers.Protocols.Reactivation` adds the previously missing
initialized second activation in the same acceptance file. No runtime, prior
theorem type, transition guard or initializer premise changes. The complete
`initialized-reactivation` history has 188 actions; its supply/capture instance
uses the existing generic theorem and original initial bounds.

The source branches were read directly from Git objects at network pin
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`, using the existing local network
repository without changing its checkout. PeerStateActions.hs:951–1025 orders
HotToWarm controls, awaitAllResults, retirement to constant NotRunning actions,
and warm-to-hot activation. Its startProtocols traversal at :1165–1195 allocates
the mux result actions before publishing their bundle. ActivePeers.hs:563–596,
1045–1078 provides the promotion/demotion completion updates. Network Mux.hs
:307–355 writes StatusIdle and the clean cell before the physical job returns;
:749–807 requires idle, allocates a fresh cell and queues the next eager start.
These are source mappings, not a new trace-refinement or native replay result.

The first 100 initialized actions reach the original clean cell and completed
activation job, keeping that protocol's physical job at the pre-publication
boundary. Twenty-eight actual governor steps apply the first activation
completion, consume the lower active target and select/fork/register/enter the
deactivation job. Thirty-two steps read the real clean result, retire the hot
action, publish/deregister/publish the deactivation Async, apply its completion,
consume the restored target and select/fork/register/enter a second activation.
Only then is the new caller allowed to allocate RunId 21.

The last twenty-eight steps allocate that cell, finish the start traversal,
select/invoke/return its tracer, fork/register physical job 21, publish the new
bundle and finish the actual activation job's body/queue/Async sequence. The old
physical job 20 then returns, publishes, deregisters and publishes its Async
result. The mux consumes that exact typed generation-20 completion through the
initiator tracer and DeltaQ return. Generation 21 remains physically running
with an empty result cell throughout. Its later local error 177, physical return,
typed publication, deregistration and Async result remain separate. A final
actual PSA poll reads the new published error and cools the peer.

Controls on these initialized-path states check both generations' cells and
physical identities. The original clean result stays readable at the second
call and after the new error. The old retired action blocks before new bundle
publication, and the new published action retries while its cell is empty,
including after the late old completion. Stale cache writes, repeated old-cell
commits, RunId reuse and physical JobId reuse are rejected. The old Async result
is available while the new physical body is still running. The new published
action reads error 177 rather than the old clean result. The exact new typed
completion stays queued; initiator completions do not fabricate IG notifications.
Server remains serving throughout this branch.

The existing selected capability, normal tracer/provider observations and
abstract body outcomes remain explicit. The endpoint covers one hot protocol
and one selected interleaving; it does not prove arbitrary restarts, universal
progress or source refinement. The final queued new error has not been processed
by the mux failure monitor; the second governor completion also remains queued
for its later application. Earlier shutdown acceptance remains a separate
initialized branch, with the raw admission-worker obstruction preserved. No
native replay or full baseline rebuild is part of this increment.

Validation on 2 November used Agda 2.8.0 serially from this library root.
The initialized history first freshly passed at a 6 GB heap, exit 0, without
diagnostics (`acceptance.log`, `result.log`). After adding the generation controls,
the final file freshly passed again, with its own Checking line, exit 0 and no
warnings (`acceptance-final.log`). Serial cached regressions
`Negative/MuxProtocolJobs.agda` and `Negative/PeerSupervision.agda` then passed,
exit 0 without warnings. Each command used `+RTS -M6G -RTS` under a 7 GB RAM,
zero-swap scope:

```sh
systemd-run --user --scope -p MemoryMax=7G -p MemorySwapMax=0 -- \
  sh /tmp/cm-reactivation-20261102/verify.sh
```

The script stops on a failure; logs, script and the three recorded final checker
exits are in `/tmp/cm-reactivation-20261102/`. All checker processes exited.
The strict local proof audit of the changed acceptance file has zero findings;
`git diff --check` passes. No new postulate, proof hole, unsafe option or
termination bypass was added, and no prior statement was weakened. This scan
is not a term-level audit of all dependencies. The handovers, presentation,
`.claude`, output and external checkouts are preserved. No commit or push.

Next: combine a live restarted initiator and the delayed old-generation
publication with actual peer/IG scope exit and CM-owned shutdown. Retain both
generation cells and captured physical handles through cancellation, handler
cleanup, collective CM wait and Server return. Broader failure/race profiles,
CM-I4c, SI4/SI5 and overall G0–G5 remain open.

## Twenty-ninth increment: initialized restarted initiator shutdown

`Protocols.Reactivation.Shutdown` remains in `Negative/ServerPeers.agda`.
`initialized-restarted-server-return` proves the complete 273-action history:
172 actions initialize the live restart; 33 close the actual peer scopes and
monitor; 20 exit Server/accept/IG and enter CM; five capture/read/send/receive/
finish the CM traversal; 26 cancel/unwind/deregister/publish/join the physical
snapshot [21,20,1,0]; five perform the inactive-IG async catch; twelve finish the
buffer/handler cleanup, actual Async result, collective CM wait and Server return.
The callback prefix is explicitly typed and abstract to limit inference cost.

The governor snapshot is empty because jobs 0–3 have already published their
actual Async results; its queued activation completion remains stored. The PSA
snapshot [50] is cancelled and joined. Callback certificates are derived from
the initialized execution. Both protocol bodies are still physically running
when CM receives cancellation: generation 20 has a committed clean cell but no
physical publication, and generation 21 has an empty cell. Normal-monitor
receipt changes group control, without creating a selected-tracer fault.

Each captured physical handle has a separately checked cancellation receipt,
body unwind, deregistration, Async publication and join. `four-actual-results`
certifies the actual nonempty physical snapshot. Cancellation enqueues no typed
completion and does not overwrite either cell. The old clean result remains
readable; the current cell stays empty and observes the actual Failed status.
That observation can wake before the handler result exists. Early Failed writes,
joins, handler publication and CM completion, plus cancelled-body resumption and
old publication, are rejected. The physical CM wait certificate retains the
actual captured handler and result table. Captured cleanup terminates entry 0,
purges the matching map and closes its socket. The raw admission-worker
counterexample remains explicit; Server return does not establish SI5.

The source was re-read directly from Git objects at unchanged network pin
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`: Server.hs:147–186;
Core.hs:523–550,584–676; ConnectionHandler.hs:286–309;
network-mux Mux.hs:256–279; JobPool.hs:105–109; and
InboundGovernor.hs:665–728. Pool close precedes async Failed/Dead; inactive IG
neither enqueues MuxFinished nor clears old counters. Explicit body-unwind,
provider/tracer-return and selected normal scope contracts remain in force.
No runtime, prior theorem statement, guard or source pin changed. No native
replay, full baseline rebuild, deployed finding, source refinement or universal
progress/shutdown theorem is claimed.

Agda 2.8.0 freshly accepted the entire final file, own Checking line, exit 0,
without warnings, with a 12 GB heap below a 15 GB RAM / zero-swap scope:

```sh
systemd-run --user --scope -p MemoryMax=15G -p MemorySwapMax=0 -- \
  sh /tmp/cm-restarted-shutdown-20261102/final-check.sh
```

Logs/scripts are under `/tmp/cm-restarted-shutdown-20261102/`;
`final.log` and `final-result.log` record acceptance. Initial scope-entry-only
checks exhausted 6 GB and 8 GB heaps, exit 251, without proof diagnostics.
The changed-file strict local audit has zero findings and whitespace checks pass;
no new postulate, hole, unsafe option, termination bypass or weakened old theorem.
This is not a term-level audit of every dependency. Serial cached Negative/MuxGroupShutdown.agda and Negative/MuxHandlerExit.agda
regressions passed at an 8 GB heap under a 10 GB RAM / zero-swap scope, exit 0
without warnings (regression-results.log and individual regression logs).
All checker processes are terminal. Handovers, presentation, .claude, output and external
checkouts are preserved; no commit or push.

Next: exercise normal old-generation publication racing the captured CM pool
close. Preserve the exact typed FIFO/result and distinguish joining an already
completed Async from delivering cancellation. Retain the live current generation,
actual handler wait and raw-worker obstruction. Broader race/failure profiles,
CM-I4c, SI4/SI5 and overall G0–G5 remain open.

## Thirtieth increment: old publication racing captured pool close

`Protocols.Reactivation.Shutdown.PublicationRace` stays in
`Negative/ServerPeers.agda`. `initialized-publication-race-return` proves a
273-action initialized history using the real restart/peer/IG/CM prefix and
physical capture [21,20,1,0]. Only after capture does generation 20 return,
publish its exact typed completion, deregister and publish its normal Async
result. Generation 21 remains physically live with an empty cell throughout
those four steps. It is then cancelled and joined; the old captured handle is
joined without cancellation delivery, followed by both infrastructure handles.

The mixed-result certificate records normal exit for generation 20 and cancelled
exit for the other three handles. Removal from the registry leaves the old
snapshot membership intact. Controls reject delivery to the finished old child,
popping the result during close or after return, and premature CM completion.
Catch, handler cleanup, actual Async result, physical CM wait and Server return
all retain the exact old typed FIFO. The old cell stays clean; the current cell
stays empty and observes actual Shutdown. The raw-worker counterexample still
refutes Server return implying all worker results; SI5 is unchanged.

Pinned JobPool.hs:105–109,123–164 was re-read directly from Git objects at
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`: close retains a handle snapshot;
normal queued publication precedes deregistration and actual Async completion.
No runtime, prior theorem, guard or source pin changed. Existing normal scope,
body/provider/tracer observations remain explicit. This is a selected finite
race, not universal shutdown, source refinement or a new deployed finding.
No native replay, full baseline rebuild or term-level dependency audit was run.

Validation used Agda 2.8.0 serially. The original fresh check emitted its own
Checking line and produced the updated interface, but its terminal session status
and exit record were lost across the continuation. Its scope was confirmed ended
before retrying. The retry accepted the current cached interface, exit 0 without
warnings. Both used a 12 GB heap under 15 GB RAM, swap disabled. Evidence:
`/tmp/cm-publication-race-20261102/interrupted.log`, `acceptance.log`,
`result.log`, `scope.log` and `retry-scope.log`; script `check.sh`.
Do not describe the cached retry as a fresh check or the original as a recorded
exit-0 run. Final strict local audit has zero findings; whitespace checks pass.
No postulate, hole, unsafe option, termination bypass or weakened old theorem.
Cached Negative/MuxProtocolJobs.agda and Negative/MuxGroupShutdown.agda
regressions passed serially at 8 GB heap under 10 GB RAM / zero swap, exit 0
without warnings (regression-results.log and individual logs). All processes
are terminal. No commit or push; handovers,
presentation, .claude, output and external checkouts remain preserved.

Next: let the current generation commit a clean local result while CM cancellation
is pending, before its physical cancellation receipt. Check local-result priority
over later Failed/Shutdown without fabricating a physical publication or handler
result. Broader races/failures, CM-I4c, SI4/SI5 and overall G0–G5 remain open.

## Thirty-first increment: current clean completion before child cancellation

`Protocols.Reactivation.Shutdown.CurrentClean` adds the initialized 275-action
`initialized-current-clean-return` in `Negative/ServerPeers.agda`. It reuses the
actual CM normal-monitor receipt, captures the pool and requests cancellation
of generation 21. Before delivery to that child, separate actual body-return
and clean-commit steps fill its local cell. The remaining real cancellation,
unwind, deregistration, Async publication and joins precede Failed/Dead,
captured handler cleanup/result, collective CM wait and Server return.

Expected snapshots update only the current physical job, cell and matching peer
cache. Each successor is checked by an actual V.advance equality; no generic
commutation assumption or terminal-stage assignment is used. The existing
capture/supply lift uses the original initial bounds. All four captured physical
results are cancelled, while both generation cells remain locally clean. No
typed protocol completion is invented. The physical handler wait certificate
retains the actual result table and captured handler. The initialized raw-worker
counterexample preserves the SI5 obstruction.

Controls distinguish a clean cell from a physical publication, child Async
result or handler result. They reject premature publication, a repeated cell
write and premature CM completion. The current cell reads clean before child
delivery, after actual mux Failed and after Server return. The mux really is
Failed, and the child Async really is cancelled. The handler outcome is still
the original async exception, independent of the clean protocol result.

Pinned network-mux Mux.hs:332–373,799–816 was re-read directly from Git objects
at `96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`: the clean STM transaction
waits for egress, marks the protocol idle and fills its cell before physical
return/publication. The completion action prefers that cell to Shutdown;
AsyncCancelled bypasses the synchronous job handler. This is one selected
finite interleaving under existing body/egress/provider/tracer and normal scope
contracts, not universal progress or source refinement. No runtime, prior
theorem, transition guard or initializer premise changed. No native replay,
full baseline, new deployed finding or term-level dependency audit.

Agda 2.8.0 freshly checked the complete final file, own Checking line, exit 0,
without warnings, at 12 GB heap below 15 GB RAM / zero swap:

```sh
systemd-run --user --scope -p MemoryMax=15G -p MemorySwapMax=0 -- \
  sh /tmp/cm-current-clean-20261102/check.sh
```

Evidence/scripts are under `/tmp/cm-current-clean-20261102/`; acceptance.log
and result.log record the fresh check. Strict local changed-file audit has zero
findings; whitespace checks pass. No new postulate, hole, unsafe option,
termination bypass or weakened old statement. Cached Negative/MuxProtocolJobs.agda
and Negative/MuxHandlerExit.agda regressions passed serially at 8 GB heap under
10 GB RAM / zero swap, exit 0 without warnings (regression-results.log and
individual logs). All checker processes are terminal.
Handovers, presentation, .claude, output and external checkouts are preserved;
no commit or push.

Next: generalize committed per-generation cell preservation to every enabled
Protocols event and finite initialized execution. Retain fresh allocation and
existing completion guards; do not infer physical Async or shutdown completion
from that monotonicity property. Broader races, CM-I4c, SI4/SI5 and G0–G5 remain
open.

## Thirty-second increment: generic committed-generation cell preservation

`Properties/ServerPeers.Protocols.CommittedCells` strengthens the invariant
layer beyond the selected race histories. `advance-keeps` preserves the complete
Call record once its local result is committed, for every enabled Protocols event
on a unique generation table. `run-keeps` lifts this to arbitrary finite Runs.
`initial-unique` and `run-unique` derive that representation premise from the
actual initializer and enabled prefix. Consequently `from-initial-keeps` and
`from-initial-observe` require only initialization, prefix/suffix executions and
the observed committed binding/value; they add no initial supply or uniqueness
assumption. Both clean and error outcomes are covered. Local observation remains
that committed result regardless of later mux status.

The proof reuses Properties/Stores lookup/put and UniqueKeys lemmas. A byThread
search on a unique table is related to the actual generation-key lookup. The
three permitted table changes are unchanged calls, a fresh cons allocation and
a write to a previously empty call. Every successful executable selector is
checked, including dispatch/FIFO bookkeeping, starts/tracing/fork/registration,
completion, PSA reads/waits and tracer/CM receipt faults. Rejected constructor
cases are explicit. Arbitrary injected Plan values are not assumed enabled.
No runtime, existing theorem statement, guard or initializer premise changed.

`Negative/ServerPeers.CellPreservationChecks` instantiates the generic theorem
on the initialized clean-before-cancellation history and an initialized error
followed by physical body return. It also constructs a deliberately malformed
duplicate-key table: byThread can find a later empty binding behind a committed
first binding, and a real commit overwrites that first binding. This refutes
omitting uniqueness from the arbitrary-state step theorem. The same table is
proved nonunique and cannot occur in the initialized executions covered above.
It is a representation-premise control, not a new deployed source defect.

Pinned network-mux Mux.hs:774–789,799–816 was re-read from Git objects at
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`: each run allocates a fresh cell,
and its completion action prefers that cell to Shutdown. This source mapping
is separate from the generic model theorem; no source-refinement, delivery,
physical child/handler completion or universal-progress conclusion follows.
CM-I4c, SI4/SI5 and overall G0–G5 remain open. No native replay, full baseline
rebuild or term-level dependency audit was run.

Agda 2.8.0 freshly accepted the generic properties module at 8 GB heap below
10 GB RAM / zero swap, exit 0, own Checking line, no warnings. The complete
downstream Negative/ServerPeers.agda acceptance freshly passed
at 12 GB heap below 15 GB RAM / zero swap, exit 0, own Checking line and no
warnings, covering every existing history plus the new generic instances and
malformed-table control.
Logs/scripts: `/tmp/cm-cell-preservation-20261102/`;
`properties-accepted.log` and `result.log` record the generic acceptance.
Preliminary proof development repaired explicit imports, dependent guard
equations, rejected-case coverage and suffix/event inference. No new postulate,
hole, unsafe option, termination bypass or weakened old statement was added.
The strict local two-file audit has zero findings and whitespace checks pass.
`acceptance.log` and `acceptance-result.log` record the final downstream success;
`acceptance-inference.log` retains the repaired one-step test inference diagnostic.
All checker processes are terminal. Only this acceptance module directly imports
the changed proof module in ConnectionManagement; no unrelated lower rebuild was
needed after these proof-only edits. Handovers, presentation,
.claude, output and external checkouts are preserved; no commit or push.

Next: prove that initialized call-thread references retain matching historical
physical job captures (owner, mux, protocol direction/number and generation).
Keep historical presence distinct from a live thread, current CM map ownership,
local completion or Async-result availability.

## Thirty-third increment: initialized call-thread capture soundness

`Properties.ServerPeers.CaptureIdentity.Frontend.initialized-soundness` derives
capture soundness from `Protocols.initialize` and every finite enabled `Runs`.
A call with `thread = just j` has a historical physical `ProtocolJob` row at j
whose owner, mux, initiator direction, protocol number and generation match the
call and its RunId. The theorem adds no initial supply or uniqueness premise:
call-table uniqueness is derived along the same initialized execution.

`Properties.MuxProtocolJobs.CaptureIdentity` proves immutable capture retention
for every physical action and finite execution. Separate proof layers carry that
fact through result monitoring, group/whole-pool close, handler exit, cancellation,
startup unwind, DeltaQ, catch/publication unwind, Server admission, IG exit and
shared ServerPeers actions. Existing source/pool projection theorem types and
runtime definitions/guards remain unchanged. Fresh job insertion and phase-only
updates preserve older identities. The frontend proof checks its actual guarded
fork, fresh caller allocation, result commits, legacy dispatch, PSA reads/waits
and tracer/shutdown events. A small indexed Effect record retains selector-plan
identity during elaboration.

Historical row presence does not establish a live physical child, current CM map
binding, local cell completion, Async availability or universal progress. This
increment is a model invariant; no source-refinement or new deployed defect is
claimed. Network/consensus pins are unchanged. No native replay, full baseline
rebuild or term-level dependency audit was run; CM-I4c, SI4/SI5 and G0–G5 remain open.

Generic Agda 2.8.0 acceptance: fresh own Checking line, exit 0, 10 GB heap with
12 GB virtual-memory limit (`indexed.log`/`indexed-result.log` under
`/tmp/cm-thread-capture-20261102/`). Earlier all-event attempt exhausted its 8 GB
heap, exit 251; a naming clash and selector evidence representation were repaired.
One PatternShadowsConstructor warning concerns the unused `frame` birth pattern.
The full downstream acceptance freshly passed at 12 GB heap under a 15 GB RAM /
zero-swap scope, exit 0, own Checking line (acceptance.log/acceptance-result.log).
Its new `ThreadCaptureChecks` covers initialized clean shutdown, error, restart
and a fabricated-reference negative control. The constructor-shadowing warning
was also reported through the import; there were no proof errors. All checkers
are terminal. Strict local audit of all 13 edited proof
and acceptance modules found zero issues; whitespace clean. All changes remain
uncommitted; handovers, presentation and unrelated user files are preserved.

Next: strengthen the initialized invariant so a committed local cell is backed
by a physical capture of the same generation with the same committed result.
Keep physical result capture, body return, publication and Async availability
separate; do not infer any later phase from the local cell alone.


## Thirty-fourth increment: initialized local-result agreement

`Properties.ServerPeersResults.Frontend.initialized-agreement` proves that each
committed local cell in an initialized finite execution has a real thread handle
and a current historical physical `ProtocolJob` row with the same captured result.
That row also matches the call's owner, mux, initiator direction, protocol number
and RunId. `initialized-soundness` supplies the result component; the public
agreement theorem joins it with increment 33's capture-identity invariant.
Initializer and enabled prefix derive call-table uniqueness, so the initialized
statement adds no supply or representation premise.

`Properties.MuxProtocolJobs.CommittedRows` proves exact retention of already
resultCaptured rows through physical steps and finite executions. Separate
projections carry this fact through monitoring, shutdown, handler/cancellation/
unwind layers, Server admission, IG exit and shared ServerPeers. Fresh forks
cannot reuse an existing row; body-return preparation starts at executing, and
actual completion input excludes a previously captured result. Frontend writer
proofs use the actual guarded physical step and capture operation, not an assumed
successful commit. Allocation/fork, dispatch, reads/waits and tracer/shutdown
cases preserve the invariant, which is then lifted through finite Runs.

The focused result-proof module keeps repeated checks small; all acceptance
fixtures remain in the existing `Negative/ServerPeers.agda`. Recursive adapter
implementation aliases are private, and `MuxPublicationUnwind.retained-jobs`
provides the needed projection without exposing the nested alias tree. Direct
inherited-observation calls avoid instantiating complete lower proof modules.
Old theorem statements, runtime definitions, transition guards and initializers
are unchanged. This is a model invariant, not implementation refinement.

`Protocols.LocalResultChecks` instantiates initialized clean shutdown, error and
restart histories and extracts the current generation's clean physical capture.
Negative controls reject a committed cell with no physical row and an error cell
backed only by a clean physical row. The theorem concerns captured results. It
does not identify the local result with a physical body's final Async outcome,
infer body return/publication/Async availability, prove progress or close SI4/SI5.
The clean-before-cancellation history deliberately retains those distinctions.
CM-I4c and overall G0–G5 remain open; network/consensus source pins are unchanged.
No new source defect, native replay, full baseline or term-level axiom audit is
claimed.

Agda 2.8.0 freshly accepted the generic result module and the complete downstream
acceptance file, each with its own Checking line, exit 0, no warnings, 12 GB heap
under a 15 GB RAM / zero-swap user service. The final acceptance also checks the
existing earlier witnesses and negative controls. Logs, explicit exits and
scripts: `/tmp/cm-result-soundness-20261102/` results.log/results-result.log,
acceptance.log/acceptance-result.log, check-results-generic.sh and check-results.sh.
All checker processes are terminal. Strict local audit of 14 edited/new proof and
acceptance modules: zero findings; whitespace clean. No new postulate/hole/unsafe
option, termination bypass or weakened old statement was introduced. This local
scan is not a transitive term-level dependency audit. All changes are uncommitted;
handovers, presentation, .claude, output and external checkouts remain preserved.

Development diagnostics are retained separately: returned-phase/state inference,
a module-name clash, a with-equation proof term and the final explicit action
argument were repaired. Earlier long-running namespace-instantiation probes were
interrupted or terminated and are not reported as successful checks. Profiling
identified most time outside individual theorem checking; direct lemma calls
reduced the subsequent generic retry to about three minutes (a measurement, not
a runtime guarantee).

Next: derive generic PSA poll/wait observation soundness. Any selected localResult
should belong to the selected call generation and match its captured physical
result; the Shutdown branch must retain its actual mux-state fallback semantics.
Reuse initialized-agreement, latest/byThread and existing read-selector evidence.

## Thirty-fifth increment: PSA observation provenance

Increment 35 extends the existing
[result proof module](Properties/ServerPeersResults.agda) with `Observations`.
The public `initialized-poll`, `initialized-job-wait` and
`initialized-monitor-wait` statements start with the executable initializer, a
finite enabled prefix and the actual successful read event. They return the
before-state peer/frame lookups, read permission and selected-result provenance.
No uniqueness, supply or physical-result premise is added to those initialized
statements. Cold/Cooling polls and existing monitor followups are classified
separately because they do not select a new result.

`initialized-readable` reuses increment 34's exact physical agreement and
increment 32's call-table uniqueness. `latest-info` connects the owner/number
search to lookup by RunId in that unique table. A live selection certifies the
published running action, matching controller, latest generation and captured
peer/handle/mux/protocol number. Its local result carries the actual historical
physical row, matching owner/mux/initiator direction/number/RunId and
`resultCaptured result`. A Shutdown selection instead carries an empty local
cell, the actual mux lookup and its Stopping/Stopped/Failed status. A filled local
cell retains priority even after mux failure.

The theorem deliberately distinguishes constant published actions. `returned`
and `notRunning` store results which can survive later starts; they do not read
the latest local cell. `Origin.cached` and `Origin.retired` certify those exact
published constants. An arbitrary supplied peer can have a constant result with
no local or physical row at all. Attributing that constant to a newer live
generation would be false. A separate invariant relating initialized peer-cache
constants to their historical publications remains the next obligation; it is
not assumed here.

`first-proof`, `all-proof`, `peer-proof` and `wait-proof` follow the actual
ordered first/all combinators, temperature precedence and wait PCs. Certificates
include membership in the original peer's runs, preserved through the existing
insertion sort. Never-started/retired actions still block the first-result choice;
all-result waits ignore never-started actions and include retired constants.
Blocked live actions can be skipped by first-result reads and cannot be skipped
by all-result waits. No runtime, old theorem statement, selector guard or
initializer is changed.

`Protocols.ObservationChecks` in the existing
[acceptance file](Negative/ServerPeers.agda) instantiates initialized Shutdown
polling, the clean monitor wait after mux failure, and the failed deactivation
job wait. Clean/error/restarted observations instantiate physical certificates.
Controls distinguish arbitrary constants with no calls, retired all/first
behavior, wrong-peer live selection and impossibility of Ready as Shutdown.
The earlier ordered multi-protocol and publication controls remain in the same
file. No separate fixture module was added.

Agda 2.8.0 accepted the final complete endpoint with fresh Checking lines for
both the reader proof module and `Negative/ServerPeers.agda`, exit 0 without
warnings. The command was `agda --profile=definitions
ConnectionManagement/Negative/ServerPeers.agda +RTS -M12G -RTS`, under a 15 GB
RAM / zero-swap user service. Only the reader module's own generated interface
was invalidated for that final run. Scripts, profiles and explicit exits are
under `/tmp/cm-observation-soundness-20261102/`: check-acceptance.sh,
acceptance.log and acceptance-result.log. The earlier direct generic check also
passed; its logs are properties-second.log/properties-second-result.log.
No checker process remains running. The final two-file local proof-integrity
scan found zero holes/trust bypasses; `git diff --check` passed. This is a local
scan, not a term-level audit of external assumptions.

The preliminary all-cells proof needed the saved tail-selection equation after
dependent case splitting; it was repaired before acceptance. That diagnostic is
retained in properties-first-error.log. One acceptance attempt was stopped to
refresh the final reader interface after a small proof cleanup landed during
checking; acceptance-pre-refresh.log and acceptance-pre-refresh-result.log record
that interruption, not a successful check. No new postulate, unsafe option, checker bypass or weakened
previous statement was introduced. All changes remain uncommitted; presentation,
Makefile/PDF, .claude and external work are preserved.

This is a model provenance theorem, not source refinement, body/Async completion,
delivery progress or universal shutdown. No new native replay, unrelated full
baseline or source-pin change is included. CM-I4c, SI4/SI5 and G0–G5 remain open.

Next: prove historical backing of cached/retired results on actual initialized
peers. Derive that cache/publication invariant from the real writers and retain
old-generation witnesses across restart; do not equate a stored constant with
the latest call or add cache coherence as an initializer premise.

## Thirty-sixth increment: initialized peer-cache provenance

Increment 36 closes the cached-constant obligation left by increment 35.
[ServerPeersCache](Properties/ServerPeersCache.agda) proves `initialized-cache`
for every enabled finite execution from the unchanged frontend initializer.
Every returned/notRunning value in either an actual or published peer cell has
a retained committed call matching the peer reference, handle, mux, protocol
number and result. The witness can name an older generation; it is not defined
by the latest call.

`initialized-actual` and `initialized-published` join that call witness to
increment 34's exact physical agreement: a real thread and historical physical
row matching the original call owner, mux, initiator direction, protocol number,
RunId and `resultCaptured result`. `initialized-pick-local` then discharges the
live, cached and retired branches of increment 35's reader provenance. Its
supplied peer must be the peer actually looked up in the before-state. Arbitrary
supplied snapshots still cannot justify physical backing.

The reusable [PeerCache](Properties/PeerCache.agda) layer tracks both actual and
published cells. Restart can freeze the old observed value; retirement copies
that observed result into a notRunning constant; publication replaces an action
without inventing a result. The proof covers peer jobs, subsystem dispatch,
policy filtering, governor cleanup/cancellation, monitor faults, normal/async
exit and scope bookkeeping. A raw logical result write has no unconditional
preservation rule. The shared runtime's existing gate rejects it, while a real
frontend completion supplies its new committed-call witness before caching.
Existing committed-call retention transports all earlier witnesses to the final
table. Initialization derives uniqueness and the empty cache, without adding a
supply or cache-coherence premise. Runtime transitions, guards, initialization
and previous theorem statements are unchanged.

All new acceptance is consolidated in `Protocols.CacheChecks` in the existing
[ServerPeers acceptance file](Negative/ServerPeers.agda). A checked initialized
prefix reaches the second start: generation 21 is allocated but empty, while
the published retired clean constant still has historical physical backing.
A control proves that backing cannot be generation 21. The all-results reader
certificate is joined to this historical witness while the first-results reader
still blocks on retirement. Further checks cover the live error read, actual
error cache, clean shutdown, and a fabricated constant with an empty call table.
The invariant refutes reaching that fabricated cache from initialization.

Agda 2.8.0 freshly accepted the final complete endpoint on 3 November 2026,
exit 0 without warnings, including its own Checking line and a fresh shared
cache-proof rebuild. Command: `agda --profile=definitions
ConnectionManagement/Negative/ServerPeers.agda +RTS -M12G -RTS`, run by
check-acceptance.sh with `ulimit -v 15728640` (15 GB virtual memory). The generic
PeerCache layer also passed freshly; the earlier direct shared pass used a
15 GB RAM / zero-swap service and had one constructor-shadowing warning, renamed
before final acceptance. All checker processes for this task are terminal.
Logs/scripts/explicit exits: `/tmp/cm-peer-cache-20261102/` pure.log,
pure-result.log, shared.log/shared-result.log and acceptance.log/
acceptance-result.log. The initial endpoint fixture-name clash is retained in
acceptance-first-error.log and acceptance-first-error-result.log; two service
restart requests interrupted before launch are not counted as checks.

The final local three-file integrity scan found no substantive issues: its
three possible-hole flags at PeerCache.agda:707,847,854 are the standard `≤?`
operator, inspected individually. `git diff --check` passed. No new postulate,
unsafe option, checker bypass or weakened previous statement was introduced;
this is a local scan, not a term-level audit of external assumptions.

These are model provenance theorems. They do not identify a local/cached result
with final body/Async outcome or availability, establish delivery/progress or
universal shutdown, close SI4/SI5/CM-I4c, or declare G0–G5 complete. No native
replay, unrelated full baseline, source-pin change or new source finding is
claimed. Presentation/Makefile/PDF and unrelated external work are preserved.

Next: package the historical local-result witnesses and actual Shutdown fallback
into full physical observation certificates for initialized poll/job-wait/
monitor-wait events, retaining all existing read gates and no-read poll branches.

## Thirty-seventh increment: physical certificates for initialized result reads

Increment 37 extends the existing
[ServerPeersCache](Properties/ServerPeersCache.agda) proof layer with
`PhysicalObservation`, `PhysicalPoll`, `PhysicalJobWait` and
`PhysicalMonitorWait`. The public `initialized-physical-poll`,
`initialized-physical-job-wait` and `initialized-physical-monitor-wait` theorems
take the unchanged initializer, an enabled finite prefix and the actual successful
read event. They derive the full certificate without adding supply, uniqueness,
cache-coherence or physical-result premises.

Each wrapper retains increment 35's original reader certificate: actual peer/
frame lookups, permissions, selected results and original-run provenance. Every
local result now carries increment 36's historical committed-call and exact
physical-capture witness, including cached/retired values from older generations.
Every Shutdown result retains the selected published running action, current
owner/latest-call selection, original run membership and number, empty local
cell, actual mux lookup and non-ready status. Shutdown supplies no fabricated
protocol result or thread completion. Wait certificates cover every pair in the
actual result list, preserving all temperature bundles and ordering. Cold/Cooling
and existing-followup polls require no invented result certificate.

All new acceptance is in `Protocols.PhysicalReadChecks` in the existing
[ServerPeers file](Negative/ServerPeers.agda). The wrappers are instantiated on
the actual initialized Shutdown poll, clean monitor wait after mux failure and
failed job wait. Further certificates cover the live error read, retired clean
read after restart and Shutdown before any protocol body exists. Controls reject
Ready as a certified Shutdown and prove that the retired physical witness cannot
be attributed to the new empty generation 21.

Agda 2.8.0 freshly accepted the final full endpoint on 3 November 2026, with
own Checking lines for the shared cache proof module and Negative/ServerPeers,
exit 0 without warnings. Command: `agda --profile=definitions
ConnectionManagement/Negative/ServerPeers.agda +RTS -M12G -RTS`, run by
check-acceptance.sh with `ulimit -v 15728640` (15 GB virtual memory). The final
two-file local integrity scan found zero findings; whitespace checks passed.
This scan is not a term-level audit of external assumptions. No checker for this
increment remains running. Logs/scripts/explicit exits are under
`/tmp/cm-physical-observations-20261103/`: acceptance.log,
acceptance-result.log and check-acceptance.sh.

A preliminary list-helper inference failure was repaired with its explicit
result-list type. A fixture pattern that Agda resolved as a constructor, and a
constructor-shadowing parameter, were renamed before final acceptance. The
initial diagnostics remain in shared-inference-error.log,
acceptance-name-error.log and acceptance-name-error-result.log. No new postulate,
hole, unsafe option, checker bypass or weakened previous theorem was introduced.

No runtime, previous theorem, transition guard or initializer changed. These are
finite model observation certificates, not body/Async completion or availability,
delivery/progress, implementation refinement or universal shutdown. No native
replay, unrelated baseline, source-pin change or new source finding is included.
CM-I4c, SI4/SI5 and G0–G5 remain open. Increments 35–36 are committed in `55ac872`;
this increment remains uncommitted, with presentation/Makefile/PDF preserved.

Next: prove generic read-to-continuation agreement. Relate certified observations
to the actual resulting peer status and job/monitor PC, distinguishing clean
continuations from failed-operation/demotion waits and retaining the separate
governor/protocol body, publication and Async boundaries.

## Thirty-eighth increment: read-to-continuation safety

[ServerPeersContinuations](Properties/ServerPeersContinuations.agda) connects the
physical observation certificates to actual resulting continuations. Public
`initialized-poll-agreement`, `initialized-job-agreement` and
`initialized-monitor-agreement` take the unchanged initializer, finite enabled
prefix and successful read event. They retain increment 37's physical evidence
and derive postconditions without new initializer or cache-coherence premises.

The safety statement is one-way. `job-success-clean` and `monitor-success-clean`
prove that a successful hot-wait continuation or an all-bundle release
continuation requires clean certified observations. The corresponding
`*-success-captures` theorems attach matching historical physical captures to
every observed result. `*-success-peer` derives the actual resulting peer:
successful hot waits retire the hot bundle and clear promotion time, changing
Hot to Warm while preserving other starting statuses; successful all-bundle
waits retain the peer and proceed to callRelease. This does not assert CM release
completion, protocol body termination or Async availability.

An inherited clean branch retains both the actual guarded shared step and its
logical `J.step`. The logical continuation is classified as hot success, release
continuation or failed demotion. Clean observations alone are not stated as
sufficient for success, and no equation between arbitrary logical cache snapshots
and latest physical cells is assumed. The proof uses existing component-step
projections and exact returned job/monitor rows rather than constructing a
desired post-state.

Non-clean waits write the exact captured frame at `awaitCold failed`. Hot-wait
failures use `Peer.cool`; all-bundle failures retain the peer. Active non-clean
polls cool their actual looked-up peer and create neither a followup nor a job.
`FailureEffects` retains the source, full Server state, physical protocol/mux
state, frontend, physical monitor-thread table, governor/monitor pools and scopes.
These observations do not fabricate protocol results or physical completions.
Cold/Cooling/existing-followup polls retain their actual guarded inherited step.

All acceptance remains in `Protocols.ContinuationChecks` in the existing
[ServerPeers file](Negative/ServerPeers.agda): initialized Shutdown polling,
clean monitor deactivation after mux failure, failed job waiting, clean physical
captures and exact peer updates, failure resource preservation, and rejection
of success from the failed continuation. An existing conditional close/followup
snapshot checks the failed all-bundle boundary separately; it is not asserted
to be a new initialized close history.

Final Agda 2.8.0 acceptance passed on 3 November 2026, exit 0 without warnings:
`agda --profile=definitions ConnectionManagement/Negative/ServerPeers.agda
+RTS -M12G -RTS`, with `ulimit -v 15728640` (15 GB virtual memory).
Both the final generic proof and complete dependent acceptance have their own
fresh `Checking` lines. Only the generic proof's own interface was invalidated
for this final run. The check includes strengthened resource fields, actual
inherited shared-step witnesses and the conditional close control. Script,
log and explicit exit: `/tmp/cm-read-continuations-20261103/check-acceptance.sh`,
`acceptance.log` and `acceptance-result.log`. Earlier passing versions are saved
separately there. All checker runs for this task are terminal. Early
with-equation, queued-frame, lookup inference and fixture-scope diagnostics were
repaired. The three-file local proof audit and whitespace checks passed with
zero findings; this is not a term-level dependency audit. No runtime, previous
theorem, guard or initializer is changed; no new postulate, unsafe option,
checker bypass or weakened previous statement is introduced.

No native replay, unrelated full baseline, source-pin change, new source finding,
implementation refinement, progress or universal shutdown claim is included.
CM-I4c, SI4/SI5 and G0–G5 remain open. This increment and 37 remain uncommitted
after `55ac872`; presentation/Makefile/PDF and unrelated work remain preserved.

Next: connect certified successful operation continuations to the real governor/
monitor body-return and completion-publication bookkeeping, retaining the
separate protocol-result, caller-body, queued-completion and Async boundaries.

## Thirty-ninth increment: continuation return and completion publication

The continuation layer now connects certified successful governor waits to the
real `GovernorPool.noteReturn` boundary. `job-success-return` derives the exact
pool update to `bodyReturned` with the job's captured work and successful outcome.
The completion queue, registry, close cursor and other pool fields are retained;
the job remains unqueued. This return belongs to the governor operation and does
not return the physical mini-protocol whose local result was read.

`publish-completion` derives its postconditions from the actual enabled shared
publication step and its original body-agreement and delay guards.
`CompletionPublication` records the
selected already-returned body, logical queued job row, exact source-completion
FIFO append and separate pool FIFO append. The resulting handle is still
`deregisterPending normalExit`; deregistration and Async publication require
later events. `job-published-body` joins the immediate publication to the
certified successful wait and identifies its exact returned body;
`publication-handle` exposes the pending-deregistration phase. These are model
theorems about the existing operations, without runtime or initialization changes.

`monitor-wait-preserves` proves that either result of a certified monitor wait
retains the physical monitor-thread table, monitor pool and governor pool.
Logical followup completion does not complete the physical loop. The distinct
`finish-monitor-body` theorem extracts the real looked-up thread at
`normalFinishing`, its actual WithoutQueue body-return step, exited thread row,
and exact pending-deregistration pool update. It creates no completion queue
entry or Async result. This theorem is conditional on an enabled normal finish
action; this increment adds no new initialized normal physical monitor-exit
history. Its initialized monitor checks end with a cleared logical followup
and the physical loop still running.

Acceptance is consolidated in `Protocols.CompletionChecks` in the existing
ServerPeers.agda. It uses the initialized target-selected deactivation prefix,
separate actual publication/deregistration/Async steps, and the initialized clean
monitor followup followed by its real removal. Controls reject publication
before body return or from the failed wait, duplicate publication, early
registry removal, early Async results and physical monitor return/Async inferred
from the completed or cleared followup.

Final Agda 2.8.0 acceptance freshly passed on 3 November 2026, exit 0 without
warnings: `agda --profile=definitions
ConnectionManagement/Negative/ServerPeers.agda +RTS -M12G -RTS`, with
`ulimit -v 15728640` (15 GB virtual memory). Both the final generic proof and
complete dependent acceptance have their own `Checking` lines. No interface
invalidation was needed for the final edited sources. Script, log and explicit
exit: `/tmp/cm-continuation-bookkeeping-20261103/check-acceptance.sh`,
`acceptance.log`, `acceptance-result.log`. All task checker runs are terminal.
The three-file local proof audit has zero findings; whitespace checks passed,
including the new untracked generic proof file. This is not a term-level
imported-assumption audit. Incremental checks repaired saved with-equations,
explicit action/state inference, a grouped-prefix application and a local
constructor-shadowing name. The earlier full failure and generic core pass are
saved separately in the same directory.

Previous theorem statements, runtime, guards and initializers remain unchanged.
No new axiom, hole, unsafe option or checker bypass was introduced. Presentation
artifacts and unrelated work remain untouched. This increment and 37–38 are
uncommitted after `55ac872`. No native replay, source-pin change, new source
finding, source refinement or progress claim is included. CM-I4c, SI4/SI5 and G0–G5 remain
open.


Next: certify actual governor completion selection and application, including
branch priority, time and completion-assertion guards and private/public-state
boundaries. `Sub.completions` is the consumed source queue;
`GP.Pool.completions` currently retains the body ledger. Audit their intended
source mapping before claiming live queue equality or changing either model.

## Fortieth increment: governor completion selection and application

The existing continuation proof layer now certifies actual owner steps through
the shared frontend. `selected-completion` retains the source selecting PC,
no-monitor-change guard, exact FIFO head/tail and entire resulting source state.
`completion-priority` excludes target, policy and wakeup alternatives while that
completion is ready. This concerns the existing ordinary-peer profile and its
explicit source permissions, rather than all production extension hooks.

`applied-completion` checks the actual application PC and monotone time.
`CompletionApplication` keeps both source assertion outcomes. A passing assertion
applies `G.complete` to the actual current private state and parameters; a failed
assertion enters `completionAssertionFailed` and retains private state. Both
outcomes retain public state. `cancelled-completion-timer` proves the separate
cancellation boundary for a selected live timer. `public-governor-state` certifies
the actual next-loop write of private state into the model's public state.
These exact source-state equations retain every other subsystem field.

`OwnerEffects` also retains the full governor pool, physical monitor threads and
pool, and physical protocol-job table. Source queue consumption does not consume
the pool component's retained body ledger. It does not expose a child Async
result or imply physical protocol completion. Pinned `JobPool.hs:208–209`,
`Governor/Monitor.hs:98–109`, `Governor.hs:588–641,675–678` and
`Governor/ActivePeers.hs:1043–1079` were re-read using `git show` at the unchanged
network pin. Production has a destructive completion TQueue, completion
functions supplied with selected current state, a later time argument, a
successful hot-demotion assertion and next-loop public-state publication. The
integration ledger is an observer component; no equality of two live queues or
new source-refinement theorem is asserted.

`Protocols.GovernorCompletionChecks` stays in existing ServerPeers.agda. The
initialized deactivation lifecycle now extends through actual completion
selection/application, counters, tracing, launch completion and public-state
publication. Checks show the exact selected completion, consumed source queue,
retained ledger, current private-state update and public active membership
remaining until the later write. Guard controls reject backwards application
time, early public publication, and lower-priority branches. Separate conditional
snapshots check monitor priority, timer cancellation ordering and assertion
failure without claiming new initialized histories for those branches.

Final Agda 2.8.0 generic and full downstream acceptance checks passed serially
on 3 November 2026, exit 0 without warnings. Commands:
`agda --profile=definitions ConnectionManagement/Properties/ServerPeersContinuations.agda
+RTS -M12G -RTS` and
`agda --profile=definitions ConnectionManagement/Negative/ServerPeers.agda
+RTS -M12G -RTS`, each with `ulimit -v 15728640` (15 GB virtual memory).
Each target has its own fresh `Checking` line in its respective log. The final
downstream run reused the already-checked, unchanged generic interface; no
interface invalidation was needed. Component lemmas were also checked in scratch
modules outside the maintained import closure. Logs/scripts/explicit exits are
in `/tmp/cm-governor-completions-20261103/`: `generic.log`, `generic-result.log`,
`check-generic.sh`, `acceptance.log`, `acceptance-result.log` and
`check-acceptance.sh`. All task checker runs are terminal. The first downstream
attempt caught a local module-alias collision; it was renamed, and the diagnostic
is retained separately in `acceptance-scope-acceptance.log` and its result file.

The local three-file proof audit found no substantive issue: its one inspected
possible-hole report is the standard natural-number `≤?` decision operator at
the application-time comparison. Whitespace checks passed, including the
untracked proof file. Runtime, guards, initializers and previous theorem
statements are unchanged; no new axiom, hole, unsafe option or checker bypass was
introduced. Presentation artifacts and unrelated work remain untouched. No
native replay, source-pin change, deployed defect, term-level imported-assumption
audit or progress/refinement claim is included.
CM-I4c, SI4/SI5 and G0–G5 remain open; increments 37–40 remain uncommitted after
`55ac872`.


Next: derive initialized provenance for source completion-queue entries and
actual consumed heads from real governor body returns and publications, retaining
historical job identity and work/outcome agreement through interleavings. Use
the retained ledger as evidence rather than equating it with the live source
queue; derive the invariant from the initializer without new coherence premises.

## Forty-first increment: initialized completion provenance

[ServerPeersCompletions](Properties/ServerPeersCompletions.agda) derives backing
for every pending completion and every actually selected queue head after an
unchanged initializer and finite enabled frontend execution. `initialized-backed`,
`initialized-pending` and `initialized-consumed` add no coherence, supply,
uniqueness or returned-body premise to initialization.

Each `Origin` keeps a historical frontend state pair, its actual enabled event,
a prefix from the initializer and a suffix to the queried state. The actual
source FIFO append and primitive pool publication step are attached to that
same state pair. The original source job frame and complete PC, captured body,
returned-handle lookup and original publication guard remain explicit.
`origin-agreement` reflects that guard into exact job identity, captured work
(including its optional peer-incarnation field) and outcome equality. The original completion
value, including its delay input, is retained; the pool body carries no invented
delay field. `extend-through` keeps the publication history after consumption
and through later application/public-state updates.

The proof uses two dependency layers. [GovernorCompletions](Properties/GovernorCompletions.agda)
classifies every enabled subsystem, governor and physical-monitor operation as
retaining, consuming or publishing to the source queue. Actual publication is
coupled to the returned-body guard and exact primitive pool step. It covers the
original interleavings and exception/cleanup paths without introducing an actor
whitelist. [JobPoolReturnHistory](Properties/JobPoolReturnHistory.agda) is a generic
WithQueue proof: a returned handle reached from the empty pool has an actual
`bodyReturnedWith` step in a primitive execution prefix, with the same handle
and payload. Its historical handle survives later lifecycle operations.

`origin-returned` joins the publication's returned-cell lookup to that theorem
through the existing actual shared pool projection. `origin-returned-current`
then extends the history to the queried state. These establish a historical
modeled body return, without requiring the current handle still to be in the
returned phase or asserting an Async result is available. The consumed source
queue and retained pool body ledger remain distinct; no live queue equality,
protocol completion, delivery liveness or implementation refinement follows.

All acceptance stays in `Protocols.CompletionProvenanceChecks` in existing
ServerPeers.agda. The initialized deactivation publication, consumed head and
later public-state endpoint instantiate exact work/outcome/identity agreement,
primitive return history and historical handle retention. A wrong-outcome
control is refuted. Another control erases the pool while retaining a readable
completion queue: selection is executable on that arbitrary snapshot, but the
initialized provenance theorem proves the snapshot unreachable. This is a
representation control, not a new deployed failure finding.

Semantic Agda 2.8.0 checks passed for all three new generic layers and full
ServerPeers acceptance, exit 0 without warnings. The shared check freshly checked
its lower dependency as well. Logs/scripts and explicit exits are under
`/tmp/cm-completion-provenance-20261103/`; passing semantic logs are preserved as
`*-semantic-pass.log` and `*-semantic-pass-result.log`. A single trailing-space
blank line was then removed from the lower proof. The final lower recheck and
complete dependent endpoint both passed, exit 0 without warnings; the endpoint
freshly checked ServerPeersCompletions and Negative/ServerPeers. No cache purge
or interface invalidation was used. The first full endpoint alias collision was
renamed and saved as `acceptance-scope-acceptance.log` with its result file.
Scratch import/constructor names and index/inference diagnostics were repaired;
scratch files remain outside maintained import closures.

Final commands, all from the standalone library root: `agda
ConnectionManagement/Properties/JobPoolReturnHistory.agda +RTS -M6G -RTS`,
`agda ConnectionManagement/Properties/GovernorCompletions.agda +RTS -M8G -RTS`,
`agda ConnectionManagement/Properties/ServerPeersCompletions.agda +RTS -M12G -RTS`
and `agda --profile=definitions ConnectionManagement/Negative/ServerPeers.agda
+RTS -M12G -RTS`. Scripts set `ulimit -v 15728640` (15 GB virtual memory).
Corresponding scripts are `check-returns.sh`, `check-lower.sh`, `check-shared.sh`
and `check-acceptance.sh`, with logs and explicit `*-result.log` files alongside.
All task checker runs are terminal. Final whitespace checks passed for tracked
changes and all three new proof files.

The four-file local proof audit has no substantive finding. Its three inspected
possible-hole reports are standard `≤?` operators at sample-time, application-
time and wakeup-deadline decisions. This is not a term-level imported-assumption
audit. No new axiom, hole, unsafe option or checker bypass, weakened previous
statement, runtime/guard/initializer change, native replay or source-pin change
is included. Presentation artifacts and unrelated work remain untouched.
CM-I4c, SI4/SI5 and G0–G5 remain open. Increments 37–41 remain uncommitted after
`55ac872`.

Next: connect a successfully consumed deactivation completion to its specific
job continuation and certified clean protocol-result wait. Keep operation
failure, demotion timeout, protocol return, publication and Async availability
separate when composing those existing proof layers.

## Forty-second increment: initialized deactivation success origins

A successfully consumed deactivation completion now retains its original job's
actual success continuation. The source-correct split is **already Warm at
entry**, or **an actual clean hot-result wait**. `Rules.PeerJobs.enter` contains
that early Warm return, matching the race comment and `PeerWarm` branch in
`PeerStateActions.hs` at the unchanged network pin. A theorem requiring a fresh
wait for every successful deactivation would exclude a legitimate source branch.

[ServerPeersDeactivation](Properties/ServerPeersDeactivation.agda) derives
`initialized-valid` from the unchanged initializer and finite enabled frontend
runs. Each stored deactivation frame has its own control invariant and every
successful row has a `History` with the exact job ID and captured work, actual
frontend event/selected plan, initialized prefix and continuation suffix.
`origin-success` joins this invariant to increment 41's precise historical
publication frame; `consumed-success` applies it to the actually selected source
head. History remains available after consumption and later state updates.
There is no added coherence, supply, uniqueness, initially-Hot or body-return
premise. The result is historical; it does not assert a peer is still Warm later.

The `alreadyWarm` cause retains the actual entry transition, before-frame and
Warm peer lookup, completed after-row and unchanged work. `cleanWait` retains
the same job's before-frame at `awaitHot`, actual `waitJobResults` event,
initialized `JobAgreement`, exact completed after-row and `CleanReads`. The last
contains the historical physical capture for every clean observation, retaining
peer, handle, mux and protocol identity. This is a certificate of the observed
results; it does not assert physical protocol-body return or Async availability.

The proof's dependency layers are [PeerJobControl](Properties/PeerJobControl.agda),
which preserves captured work and classifies deactivation control transitions;
[PeerJobFrames](Properties/PeerJobFrames.agda), which classifies every enabled
subsystem/governor/physical-monitor frame write; and
[ServerPeersJobFrames](Properties/ServerPeersJobFrames.agda), which derives frame
write/read permissions from actual frontend selectors. A forged arbitrary
`reading` plan is not assumed safe. Monitor birth restores its original parent
execution; cancellation flags preserve execution; establishment return and
failed-read resets are handled explicitly. Failure and timeout cannot supply a
successful deactivation continuation. No actor whitelist or runtime restriction
is introduced.

Acceptance remains in `Protocols.DeactivationOriginChecks` in the existing
ServerPeers.agda. It covers initialized returned, consumed and retained success;
the actual clean selector and clean-wait cause; and an initialized race where a
monitor completes deactivation before the already-registered governor job enters.
The target job then succeeds at Warm entry without a result wait of its own.
A control mixes a deactivation job with an activation PC: it can execute an
arbitrary success-shaped return, but `initialized-valid` proves that snapshot
unreachable. This is a representation control, not a deployed defect finding.

Agda 2.8.0 checked all four new generic layers during development, including
fresh checks after moving them to maintained paths. The final full endpoint
`agda --profile=definitions ConnectionManagement/Negative/ServerPeers.agda
+RTS -M12G -RTS` freshly checked ServerPeers, exit 0 without warnings; its generic
dependencies were cached on that final run. No interface purge was used. The
serial `check-acceptance.sh` sets `ulimit -v 15728640` (15 GB virtual memory).
Final log and explicit exit are `acceptance.log` and `acceptance-result.log` under
`/tmp/cm-deactivation-origins-20261103/`. Scratch import/index inference and
acceptance scope/name errors were repaired before success; the last scope
failure is retained as `acceptance-scope-fix.log`.

The five-file local proof audit has three inspected possible-hole reports, all
standard `≤?` decisions in PeerJobFrames (sample time, application time and wakeup
deadline). No substantive local audit finding, new axiom, hole, unsafe option,
checker bypass or weakened earlier statement is present. This is not a term-level
imported-assumption audit. Tracked and new-file whitespace/EOF checks pass.
Runtime rules, guards, initializers, source pin and presentation artifacts are
unchanged. No native replay, source-refinement, delivery-liveness or full-shutdown
claim is added. Increments 37–42 remain uncommitted after `55ac872`.
G0–G5, CM-I4c and SI4/SI5 remain open.

Next: develop the initialized close/release success route, retaining the
Cold/Cooling entry paths directly to a Cold wait and distinguishing clean
all-bundle results, CM release, Cold observation, publication and physical
thread/Async completion.

## Forty-third increment: initialized close and release success histories

Close success is now tracked through its actual job stages, rather than inferred
from a completed row. `Properties.ServerPeersClose.initialized-valid` derives
`Progress` for every stored close frame from the unchanged initializer and finite
enabled frontend runs. `origin-success` joins the exact historical publication
frame to that progress; `consumed-success` applies it to the actually selected
source queue head. Job identity and the full captured work remain explicit,
without added coherence, supply, uniqueness or initially-Warm assumptions.

A successful `History` ends in an actual `J.observeCold` with a matching peer
lookup at `peerCold`. Its `Route` to the successful Cold wait has three cases:

- Cold/Cooling entry through the actual close operation, skipping all-bundle wait
  and release by this job.
- An actual operation timeout while awaiting all results. The timeout's guarded
  stop/cooling step is retained; a later Cold observation can still return
  `G.succeeded`.
- A certified clean all-temperature wait, followed by this job's actual release
  request and collection of a non-asserting CM result. Success and unsupported
  results remain distinct. The actual released-cell lookup, caller, peer/key,
  guarded CM request and shared before-world remain attached to their steps.

The last route carries `Waited`, `Requested` and `Released` histories. Every step
has an actual enabled frontend event and selected plan, before/after frame,
initialized prefix and suffix to the queried state. Earlier stages' suffixes end
at the next stage's before-state. The all-bundle `JobAgreement` and `CleanReads`
retain physical capture certificates for every actual clean observation. Clean
results alone do not prove release, Cold observation or successful publication.
Operation timeout is not relabeled as a clean wait or a release; demotion timeout
keeps its own outcome. Failed reads and release assertion failure cannot supply
the successful-Cold route.

`Properties.PeerJobCloseControl` classifies every enabled action on the close
control PCs. The existing frame-effect layer now also retains the actual CM
before-world. `ServerPeersJobFrames` derives `observeAll` event authorization
from the physical job-wait selector, alongside the existing hot-read permission.
The earlier deactivation theorem retains its statement and passes with the
stronger evidence. No runtime, guard, initializer or actor restriction changes.

The pinned `PeerStateActions.closePeerConnection` was re-read locally at network
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`: Cold/Cooling entry, timeout stop,
all-temperature results, error throw and clean release remain separate. The
source discards the release return value. This model theorem does not establish
implementation refinement or a term-level dependency axiom audit.

Acceptance is consolidated in `Protocols.CloseOriginChecks` in existing
ServerPeers.agda. Direct expected snapshots, with separately named actual
guarded-step equalities, follow the existing acceptance style. The cases exercise
initialized clean wait/request/collection/Cold,
publication/consumption and retained history; consumption before Async
publication; protocol-body/Async separation; premature publication rejection;
initialized timeout and Cold-entry routes where an independent caller releases
CM; and the distinct demotion-timeout outcome. Cooling entry remains covered by
the generic control proof; no separate initialized Cooling-entry trace is claimed.

`Snapshots` and `Proofs` are sibling modules inside this same acceptance file.
Snapshot bodies and actual edge/lookup facts are checked together; abstract
history proofs use those facts without unfolding the sibling's large runtime
representations. Prefixes are shared and intermediate states, events and generic
instantiation parameters are explicit. This follows Agda's
[scope of abstraction](https://agda.readthedocs.io/en/v2.8.0/language/abstract-definitions.html#scope-of-abstraction),
without adding a postulate or changing a statement.

Agda 2.8.0 freshly checked the full Negative/ServerPeers endpoint through
`agda --interaction-json --profile=definitions +RTS -M9G -RTS`, loading the exact
file through `interaction-input.txt`. Process exit was 0 and final `checked` was
true; errors, visible/invisible goals and warnings were all empty. The final
normal CLI confirmation, `agda ConnectionManagement/Negative/ServerPeers.agda
+RTS -M9G -RTS`, passed with exit 0 and empty output; that confirmation was cached.
The generic layers were checked earlier, including the prior deactivation proof
with its stronger shared-world evidence. No interface purge was used.

The fresh check ran in transient unit `cm-close-origins-20261103.service`: 9 GB
RTS heap, 11 GB cgroup limit, zero swap and 15 GB virtual-memory limit. For this
run systemd reported 6min49.885s CPU, 7min27.792s wall and 6.7G peak memory.
Earlier computed/transparent fixture attempts hit memory limits; one run was
killed by systemd-oomd. Diagnostic highlighting exhausted filesystem quota and
was replaced by compact progress output; only this task's generated diagnostic
logs were trimmed, retaining diagnostic sections. Scope/index fixes and the two
sealed branch-start equalities preceded the successful run. An initial CLI
result-log write also hit quota; generated diagnostic trimming and the final
CLI repeat completed the record.

Logs/scripts/results are under `/tmp/cm-close-origins-20261103/`, notably
`check-interaction.py`, `interaction-compact.log`, `interaction-result.json`,
`final-cli.log`, `final-cli-result.log` and `audit.log`. The six-file local proof
audit has no substantive finding: three inspected reports are standard `≤?`
decisions in PeerJobFrames. Tracked and new-file whitespace/EOF checks pass.
No new axiom, hole, unsafe option, checker bypass or weakened previous statement
is added. This is not a term-level imported-assumption audit.

Increment 43 is accepted and uncommitted with 37–42 after `55ac872`. Runtime,
guards, initializers, source pin and presentation artifacts remain unchanged.
No native replay, implementation-refinement, delivery-liveness or full-shutdown
claim is added. G0–G5, CM-I4c and SI4/SI5 remain open.

Next: increment 44, initialized physical-monitor return provenance. Reuse the
normal/error finishing states reached by these Cold paths, then retain actual
monitor body return through registry removal and Async publication. Preserve
thread/peer identity and cancellation distinctions; a finishing PC alone is not
a return or Async-availability certificate.

## Forty-fourth increment: initialized physical monitor exit histories

The overall CM/IG/OG/Server model and G0–G5 gates remain in progress. Increment
44 connects an actual physical monitor exit occurring in an initialized finite
frontend trace to separate registry-removal and Async-publication events. The
new proof layer is `Properties/ServerPeersMonitorReturns.agda`; all acceptance
stays in `Negative/ServerPeers.agda`.

### Statement and limits

`BodyExit` retains the exact thread row at the enabled exit: peer incarnation,
worker, spawning parent, parent PC and interrupted/followup frames. `Cause`
distinguishes `normalFinishing`, `errorFinishing err`, and cancellation with its
actual abandoned unwind frame. The primitive operation is respectively
`bodyReturnedWith tid nothing`, `bodyReturnedWith tid (just err)`, or
`bodyUnwound tid`. The actual error comes from the thread PC, rather than a
supplied event parameter. Both handled-error and normal returns enter normal
pending deregistration in the queue-free pool; cancellation uses cancelled exit.
The historical cause therefore carries information that the terminal handle
phase deliberately discards.

`physical-exit` derives this certificate from each enabled physical-supervision
exit. Frontend `finish` lowers the actual dispatch through the unchanged shared
runtime guards. `initialized-exit` and `initialized-occurrence` retain the exact
initializer, executed prefix, actual exit and continuing suffix. The latter
accepts any initialized finite trace containing that exit event. `extend` keeps
the same historical captured thread through arbitrary later enabled events.

`Removed` and `Published` each retain their own enabled frontend event and actual
primitive pool step, nested over the earlier history. `initialized-lifecycle`
derives the three stages from an initialized trace containing consecutive exit,
deregistration and publication events, with arbitrary prefix and suffix.
`extend-published` carries the resulting history through later execution.
These are finite event-occurrence theorems. They do not invert an arbitrary
terminal handle lookup to discover an exit, prove eventual publication or join,
relate the captured thread to an independently supplied identity, or claim
whole-system shutdown. In particular, a finishing PC alone is no return witness.

### Acceptance and source boundary

The existing `CloseOriginChecks.Snapshots`/`Proofs` sibling boundary is retained.
Normal monitor return starts at the initialized clean-close state after the
close result has been consumed and the governor's public established set has
been cleared. The physical monitor is still running at that point. A separate
normal return, registry removal and Async publication are checked, with
initialized origins and retained history. The Cold-entry error path supplies a
second initialized lifecycle: the actual error payload is preserved in the
body operation, although its pool exit phase is normal.

Controls reject early deregistration/publication on both finishing paths,
publication between body return and removal, duplicate normal return, normal
versus error dispatch, and either return substituted for cancellation unwind.
The returned/removed/published phases and pre-/post-removal registries are
checked separately. `MonitorCancellationChecks` reuses the earlier initialized
`Reactivation.Shutdown` cancellation run, deriving its complete publication
history through the later callback exit; no additional maintained fixture file
or executable driver is introduced.

Re-read at the unchanged network pin:
`network-mux/src/Control/Concurrent/JobPool.hs:122–164` and
`PeerStateActions.hs:836–851`. The queue-free body result is discarded before
child deregistration, asynchronous exceptions bypass the synchronous handlers,
and the PSA monitor's handled error returns a `Just` payload through the job
handler. The local model records symbolic errors and explicit primitive
boundaries; these proofs do not establish implementation refinement or a new
replay result. Fetched source snapshots are under the validation folder.

### Validation and continuation

Checked 3 November 2026 with Agda 2.8.0. The generic command
`agda ConnectionManagement/Properties/ServerPeersMonitorReturns.agda +RTS -M4G -RTS`
freshly passed, exit 0 with no warnings. An initial generic check's constructor
shadowing warnings were repaired by renaming pattern variables. The full
`ConnectionManagement/Negative/ServerPeers.agda` interaction load freshly passed:
process exit 0, checked=true, errors/goals/warnings empty. Final normal CLI
`agda ConnectionManagement/Negative/ServerPeers.agda +RTS -M9G -RTS` passed
cached, exit 0 with empty output. No cache purge. Only one checker was started
at a time. The compact runner used a 9 GB heap, 11 GB cgroup memory, zero swap
and 15 GB virtual limit; systemd reported 6.7G peak for this run.

Logs, runner, fetched source snapshots and results are under
`/tmp/cm-monitor-returns-20261103/`: `generic.log`, `interaction-compact.log`,
`interaction-result.json`, `final-cli.log`, `final-cli-result.log` and
`audit.log`. The two-file local proof audit reports zero findings; tracked and
new-file whitespace/EOF checks pass. No new axiom, hole, unsafe option, proof
bypass or weakened old statement is added. This is not a term-level audit of
imported assumptions. No additional native replay was run.

Increment 44 is accepted and uncommitted with 37–43 after `55ac872`.

No runtime, guard, initializer, source pin, presentation or commit is changed.
After acceptance, the next obligation is initialized terminal-handle backing:
derive an earlier physical exit from a queried terminal pool phase, retaining
normal/error/cancellation histories without an extra history/coherence premise.
That inversion is deliberately separate from this increment's event-occurrence
statement. CM-I4c and SI4/SI5 remain open alongside G0–G5.

## Forty-fifth increment: initialized terminal monitor handle backing

The overall CM/IG/OG/Server objective and G0–G5 remain in progress. Increments
37–44 are committed in `29e5607`; this increment extends the physical-monitor
exit histories from event occurrences to queries of initialized terminal handles.
Presentation sources, their Makefile and generated output remain uncommitted.

### Statement and proof layers

`Properties/MonitorPoolEffects.agda` classifies every primitive queue-free pool
transition and every enabled physical-supervision action. A handle write is
unchanged, active, a terminal-stage transition preserving its exit, or an actual
new return/unwind. The classifier retains the old lookup on terminal-stage
transitions and exact writes on every changed key. Its tagged source reflection
admits a fresh exit only from `finishMonitor`, `finishMonitorError` or
`monitorBodyUnwound`. `PhysicalExit` records that actual enabled source step and
the earlier `BodyExit` certificate, including the captured thread and actual
error/unwind cause. Existing metadata projections discharge governor, CM and
outer-scope bookkeeping; no runtime rule or guard changes.

`Properties/ServerPeersMonitorBacking.agda` lifts this complete classifier through
shared Server/CM steps and every frontend plan. Protocol result caching preserves
the entire monitor pool. `History` retains initialization, the executed prefix,
actual frontend event and selected plan, its enabled transition, the physical
source exit, the exact new handle write and the continuing suffix. `SelectedExit`
explicitly identifies the inherited/caller/completion plan executing that exact
physical action; `located-change` retains its source-action equality. The lower
physical state is retained explicitly because later frontend caching can change
peer cells without changing physical handles.

`initialized-backed` derives a history for every pending-deregistration,
deregistered or result-available handle after any initialized finite enabled
`Runs`. `initialized-pending`, `initialized-removed` and
`initialized-published` require only the initializer, execution and queried
current lookup. No prior return history, supply, coherence, uniqueness or
current registry-membership premise is added. Induction transports old histories
for unrelated keys, rejects active phases at a terminal query, retains the exit
across deregistration/publication, and creates fresh histories only at the
source-certified exit. Empty initial handles are derived from the initializer.

A normal pool exit returns an existential normal-or-handled-error cause, with
its actual error available in the captured source certificate. The result-erased
handle alone cannot select between those causes. `cancelled-history` eliminates
the normal alternatives and retains the actual cancellation unwind. This is a
finite initialized safety/provenance theorem. It does not prove eventual exit,
publication, join, delivery, source refinement or whole-system shutdown, nor
creation-to-exit identity invariance. In particular, querying a published handle
supplies an earlier exit history here; independently recovering its intervening
removal/publication event histories is the next obligation.

### Acceptance and representation control

All acceptance remains in `Negative/ServerPeers.agda`. The existing opaque
snapshot/proof siblings are retained. Six direct terminal queries cover all
three phases on the initialized normal and handled-error paths, using only
initializer, enabled execution and the already checked current phase lookup.
The existing initialized cancellation run is queried after publication, join
and callback exit; its normal alternatives are eliminated to obtain the exact
cancelled history.

Thirteen existing long shutdown/restart witnesses now supply explicit source,
intermediate, target and event arguments on their 289 `V.more` steps. Every
original theorem signature, edge proof and edge order is preserved. This avoids
repeated inference of large concrete states during memory-limited validation;
the change is proof elaboration only. The annotation script and manifest are in
the validation folder.

An arbitrary forged snapshot marks the still-finishing monitor as deregistered
and can execute Async publication. Its thread PC remains finishing. The control
proves this snapshot cannot be the endpoint of the fixed initialized clean-close
prefix, using execution determinism and its actual running-handle lookup. It is
an executable representation control, not a claim that the snapshot is
unreachable under every conceivable event schedule or a deployed defect.

### Validation and continuation

Accepted 4 November 2026 with Agda 2.8.0 (threaded GHC 9.6.7). The final generic
command `agda ConnectionManagement/Properties/ServerPeersMonitorBacking.agda
+RTS -M4G -RTS` freshly checked both new proof layers, exit 0 without warnings.
The full `ConnectionManagement/Negative/ServerPeers.agda` interaction load
freshly passed: process exit 0, checked=true, errors/goals/warnings empty.
It used normal declaration caching and the default collector, 9 GB heap,
11 GB cgroup, zero swap and a 15 GB virtual limit; systemd reported 7G peak
for this run. Final strict batch `agda ConnectionManagement/Negative/ServerPeers.agda
+RTS -M9G -RTS` passed cached, exit 0 with empty output.

The three-file local proof audit reports zero findings. Tracked and new-file
whitespace/EOF checks pass. No new axiom, hole, unsafe option or weakened old
statement is added. This is not a term-level imported-assumption audit. No
native replay was rerun. Evidence is under `/tmp/cm-monitor-backing-20261103/`:
`backing-final-generic.log`, `generic-result.log`, `interaction-compact.log`,
`interaction-result.json`, `final-cli.log`, `final-cli-result.log`, `audit.log`,
`annotation-manifest.json` and `service-journal.log`. The work began on
3 November and resumed on 4 November.

Earlier type/scope diagnostics and pattern-shadowing warnings were repaired
before the successful generic checks. A first full check exhausted a
5 GB heap while rebuilding a dependent module. A second used an incorrectly
ordered 9 GB heap/7 GB cgroup configuration and was killed for memory after
reaching later acceptance; the attempted stop found the unit already gone.
A subsequent run corrected this to 6 GB heap below a 7 GB cgroup cap, zero swap,
15 GB virtual limit and disabled Agda's in-memory declaration cache. That run was
deliberately stopped while strengthening `History` with the explicit selected
plan/source-action link; the strengthened generic check freshly passed with no
warnings. The strengthened unannotated run then exhausted its 6 GB heap in the existing
72-step restart witness after 27 minutes (4G reported physical peak). Its stop
request found the unit already terminated. The thirteen witness annotations
address that inference cost. Both generic layers freshly passed again with no
warnings. The annotated 6 GB copying-collector run still exhausted its heap
before the long witness. Non-moving-collector experiments at 4 and 5 GB also
exhausted their heaps. They changed RTS memory management only; Agda 2.8.0 and
its threaded GHC 9.6.7 runtime were checked. The relevant official references
are the [GHC RTS options](https://downloads.haskell.org/ghc/9.6.7/docs/users_guide/runtime_control.html)
and [memory guide](https://downloads.haskell.org/ghc/9.6.7/docs/users_guide/hints.html#understanding-how-os-memory-usage-corresponds-to-live-data).

Available memory later rose from about 4 GB to 17 GB after other work released
shared memory, allowing the successful standard-memory check recorded above.
Earlier failure/interruption logs remain separately named in the evidence
folder. No disk interface purge, explicit `-c`, or proof-check bypass was used.

Increment 45 is accepted and uncommitted after `29e5607`. No runtime, guard,
initializer, source pin, presentation or replay is changed. G0–G5, CM-I4c and
SI4/SI5 remain open. Next: increment 46, derive the actual
intervening registry-removal and Async-publication histories directly from
initialized terminal-phase queries, allowing interleaved events and requiring
no supplied lifecycle history.

## Forty-sixth increment: initialized terminal stage event histories

The overall CM/IG/OG/Server objective and G0–G5 remain in progress. Increment 46
extends terminal exit backing to the actual intervening registry removal and
Async publication. Increment 45 remains uncommitted after `29e5607`.

### Statement and proof layers

`MonitorPoolEffects.Detailed` retains the movement label and its witness on
terminal-stage transitions. The primitive and supervision classifiers are shared
with the earlier API; `forget` projects the detailed classifier into the original
`Change`, `Raw`, `source-change` and `located-change` interfaces. Their theorem
statements remain intact. Tags now retain removal/publication identities.
`PhysicalMove` supplies the actual enabled supervision action, primitive pool
step and registry effect. Deregistration removes that captured ID from the
registry; Async publication preserves the registry. No runtime rule changes.

`Properties/ServerPeersMonitorStages.agda` lifts both exits and movements through
the shared runtime and every frontend plan. `SelectedMove` identifies the exact
inherited/caller/completion plan executing the source operation. `realized-pool`
connects the source result to the whole actual frontend pool, explicitly using
cache preservation on completion plans. The registry equations therefore concern
the recorded runtime before/after states, not an assumed source snapshot.

`Removal` retains an earlier increment-45 exit history ending at the removal's
actual before state, together with its event/plan, enabled source/primitive
steps, actual old lookup, handle write, registry deletion and continuing suffix.
`Publication` retains an earlier `Removal` ending at the publication's before
state, plus the corresponding actual event, source/primitive steps, old lookup,
write, registry preservation and suffix. The same job ID and normal/error/
cancellation cause index the whole chain. Historical thread/peer/parent/error
information is retained in the original exit witness.

`initialized-backed`, `initialized-pending`, `initialized-removed` and
`initialized-published` derive these ledgers from an initializer, finite enabled
`Runs` and the current terminal lookup. No supplied lifecycle history, extra
coherence/supply/uniqueness or current registry-membership premise is added.
One induction creates fresh records at the actual transitions, transports old
records across unrelated writes and retains the exit classification across
stages. `extend-removal` and `extend-publication` preserve arbitrary intervening
suffixes; `removal-exit`/`publication-exit` recover the earlier exit history at
the queried current state. `cancelled-publication` excludes normal-return causes.

These are finite initialized safety/provenance statements. They do not establish
eventual return/publication/join, native implementation refinement, permanent
absence from a whole registry or whole-system shutdown. Registry equations are
historical effects at the recorded step; later unrelated registrations remain
possible. The original captured thread is not recomputed from a current peer.

### Acceptance and validation

All acceptance remains in `Negative/ServerPeers.agda`. Six direct queries cover
pending, removed and result-available phases on the initialized normal and
handled-error paths. The existing initialized cancellation run supplies the
complete ordered history after publication, join and callback exit. A further
initialized path performs real target-input writes before removal, between
removal/publication and after publication, then queries the published handle.
Every edge is checked against the actual frontend transition. The earlier
premature-publication and forged-prefix controls are retained.

Accepted 4 November 2026 with Agda 2.8.0. The generic command
`agda ConnectionManagement/Properties/ServerPeersMonitorStages.agda +RTS -M4G -RTS`
freshly passed, exit 0 without warnings. The refined classifier and unchanged
increment-45 consumer also checked. The full maintained ServerPeers interaction
load freshly passed: process exit 0, checked=true, errors/goals/warnings empty.
It used normal caching/default GC, 9 GB heap below 11 GB cgroup, zero swap and
15 GB virtual limit; systemd reported 6.7G peak for this run. Final strict batch
`agda ConnectionManagement/Negative/ServerPeers.agda +RTS -M9G -RTS` passed
cached, exit 0 with empty output. No interface purge or collector experiment.

The local three-file proof scan reports zero findings; tracked/new-file
whitespace and EOF checks pass. No new axiom, hole, unsafe option or weakened
old statement. This is not a term-level imported-assumption audit. Earlier local
diagnostics involved nested-module name clashes, a saved with-expression
equality, a nested with-clause and explicit implicit-argument inference/order;
these were repaired before acceptance. Evidence, scripts, logs, results and
audit are under `/tmp/cm-monitor-stages-20261104/`, notably `stages.log`,
`generic-result.log`, `interaction-compact.log`, `interaction-result.json`,
`final-cli.log`, `final-cli-result.log`, `audit.log` and `service-journal.log`.

Increment 46 is accepted and uncommitted alongside 45 after `29e5607`.
No runtime, guard, initializer, source pin, presentation or native replay changes.
Next: increment 47, connect initialized monitor joins to these
full exit/removal/publication histories and their captured close-snapshot IDs.
Keep enabled-join safety separate from eventual closure and the still-unmodeled
remaining CM/handler/server completion obligations. G0–G5, CM-I4c and SI4/SI5
remain open.

## Forty-seventh increment: initialized monitor join provenance

The overall CM/IG/OG/Server objective and G0–G5 remain in progress. Increment 47
connects an actual inherited monitor join to its initialized snapshot and the
exit/removal/publication chain derived in increments 45–46.

### Statement and proof layers

`Properties/JobPoolJoinOrder.agda` proves the exact invariant
`snapshot = joined ++ remaining` for every enabled primitive execution from the
empty initializer, for either queue policy. Beginning close establishes the cut;
joining consumes its head and appends that ID to the joined prefix. Other actions
preserve the cut. `inspect-join` extracts the current ID, either `cancelPending`
or `joinPending`, its terminal lookup, remaining head/tail and exact resulting
state from the actual enabled primitive join. `captured` derives membership in
the snapshot from the invariant and that inspected head. No membership or order
premise is supplied by the client.

`Properties/ServerPeersMonitorJoins.agda` lowers the real frontend event
`dispatch (peerStep joinMonitor)` through the shared and physical-supervision
guards to the actual primitive join. The existing background-pool projection
provides an execution from the empty pool initializer, yielding the invariant.
`initialized-join` requires only initialization, finite enabled `Runs` and this
actual join. Its `Joined` record retains the prefix, source/primitive steps,
inspected shape, derived snapshot membership and earlier `Publication`. The
terminal lookup needed by increment 46 is extracted from the join guard; it is
an output rather than an added hypothesis. Publication retains its earlier
Removal and physical exit, including the original thread, peer, parent and
normal/handled-error/cancellation cause. `ordered-snapshot` exposes the exact
joined-prefix/current-ID/tail cut. The inspected state fixes the append, tail,
closing phase and unchanged snapshot. `publication-after` and `exit-after` extend
the histories through the actual join. Observation helpers name its derived
ID and recover the cause-indexed publication without recomputing the history.

The theorem concerns this inherited frontend event; it does not add a classifier
for arbitrary raw plan aliases. Generic histories retain all three exit causes;
a normal terminal pool phase alone still cannot distinguish an ordinary return
from a handled monitor error. No runtime, guard, initializer or source-pin change.
No new coherence, supply, uniqueness, registry absence, terminal-result or prior
lifecycle premise. The claim is finite enabled-join safety/provenance, with no
eventual join/closure, native refinement or whole-system shutdown conclusion.

### Acceptance and validation

All acceptance remains in `Negative/ServerPeers.agda`. `MonitorJoinChecks`
reuses the actual initialized cancelled shutdown prefix ending immediately before
join, derives the captured ID 50 and cancelled publication history, and checks
snapshot retention, joined order, consumed remaining cursor and premature join
rejections before removal and before publication. The prefix uses the original
30 checked edges, with explicit intermediate states to bound elaboration.
`MonitorJoinRace` has actual empty-initializer primitive executions for a normal
or handled-error payload returning after a cancellation request, before delivery.
Both pending cancellation and already-available-result waiting phases join only
a published Async result. Running, pending-removal and removed-only handles do
not join; return prevents cancellation delivery; a wrong head does not join.
These primitive cases do not claim additional full frontend normal/error
shutdown witnesses.

Accepted 4 November 2026 with Agda 2.8.0. Both generic commands freshly
passed with exit 0 and no warnings:
`agda ConnectionManagement/Properties/JobPoolJoinOrder.agda +RTS -M4G -RTS`
and `agda ConnectionManagement/Properties/ServerPeersMonitorJoins.agda +RTS -M4G -RTS`.
The fresh full maintained ServerPeers interaction load passed: process exit 0,
checked=true, errors/goals/warnings empty. It used normal caching/default GC,
9 GB heap below an 11 GB cgroup, zero swap and a 15 GB virtual limit; systemd
reported 6.9G peak. Final strict batch
`agda ConnectionManagement/Negative/ServerPeers.agda +RTS -M9G -RTS` passed
cached, exit 0 with empty output. No interface purge or collector experiment.

The three-file local proof scan reports zero findings; whitespace/EOF checks
pass. No new axiom, hole, unsafe option or weakened old statement. This is not a
term-level imported-assumption audit. Local typing/scope diagnostics were repaired;
the first two full loads rejected a fixture name collision and incorrect named
primitive-trace constructor arguments. Neither failed load counts as acceptance.
Evidence: `/tmp/cm-monitor-joins-20261104/`, including generic logs, the successful
interaction log/result, final batch log/result, audit and service journal.

Increment 47 is accepted and uncommitted alongside 45–46 after `29e5607`.
No commit, presentation or native replay change. G0–G5, CM-I4c and SI4/SI5 remain
open. Next: increment 48, an initialized closed-monitor-snapshot certificate,
combining exact joined order with per-handle lifecycle histories, while keeping
the remaining CM/handler/server completion obligations explicit. This next
certificate must derive its premises from initialization, finite enabled Runs
and the closed-pool observation; it must not assume earlier lifecycle histories
or assert eventual closure.

## Forty-eighth increment: initialized closed-monitor snapshot certificates

The overall CM/IG/OG/Server objective and G0–G5 remain in progress. Increment 48
combines initialized snapshot order, closed-pool terminal coverage and actual
lifecycle histories in the existing `ServerPeersMonitorJoins` proof module.
Acceptance remains consolidated in `Negative/ServerPeers.agda`.

### Statement and proof layers

`Frontend.SnapshotLifecycle` retains a cause-indexed terminal lookup and an
actual earlier `Publication`, whose `Removal` retains the physical body exit.
The captured thread, peer, parent and error/unwind information stays in that
historical chain. A normal terminal phase still permits either an ordinary
return or a handled-error cause; cancellation requires actual unwind.

`Frontend.ClosedSnapshot` records initialization, the finite enabled prefix,
the actual closed-pool observation, an empty remaining cursor, exact equality
of snapshot and joined lists, and `All SnapshotLifecycle snapshot`. The `All`
witness follows the captured list order. `initialized-closed` derives the entire
record from just initialization, finite enabled `Runs` and the closed phase.
It reuses the actual background-pool projection, `JobPoolCloseKernel.exec-empty`
and `from-initial`, the increment-47 partition invariant and increment-46 stage
histories. No per-handle terminal lookup, history, snapshot membership, supplied
order, registry absence or extra coherence/supply/uniqueness premise is added.
The existing join theorem and runtime interfaces retain their types.

`captured-lifecycle` retrieves a member's derived history;
`histories-in-join-order` transports the ordered histories to the equal joined
list, and `joined-lifecycle` retrieves a joined member. `lifecycle-exit` retains
the earlier physical exit at the current query state. `cancelled-lifecycle`
uses a concrete cancelled lookup only to specialize an already-derived history;
that lookup is not a premise of `initialized-closed`.

This is a finite certificate conditional on an actual closed observation. The
order field identifies the model's joined list; it does not add a frontend event
history for every join or claim a concrete source ThreadId ordering. Histories
cover captured handles; excluded historical handles receive no new certificate.
No eventual closure, native refinement, whole-system shutdown or current whole
registry-absence claim. No runtime, guard, initializer or source-pin change.

### Acceptance and validation

`MonitorClosedSnapshotChecks` derives the actual initialized nonempty closed
frontend snapshot before the callback exits and again after its actual exit.
It retrieves histories through both captured and joined membership, checks their
order and derives cancelled publication and the original exit for ID 50. ID 51
is excluded. A published-but-unjoined head still prevents finishing the close;
the callback remains at the serving stage when the monitor pool closes.

The existing normal/error primitive race modules now execute join and finish
from their empty initializer, derive exact snapshot/joined equality and terminal
coverage, and reject premature finish. `MonitorClosedEmptyAndForgedChecks`
checks an actual empty primitive close. Its forged closed state deliberately
lacks both order equality and a terminal result, showing why a bare closed bit
cannot replace initialized execution. These are primitive controls, not new
full frontend normal/error or empty shutdown witnesses.

Accepted 4 November 2026 with Agda 2.8.0. The generic command
`agda ConnectionManagement/Properties/ServerPeersMonitorJoins.agda +RTS -M4G -RTS`
freshly passed, exit 0 without warnings. The fresh full maintained ServerPeers
interaction load passed: process exit 0, checked=true, errors/goals/warnings
empty. It used normal caching/default GC, 9 GB heap below an 11 GB cgroup,
zero swap and a 15 GB virtual limit; systemd reported 6.9G peak. Final strict
batch `agda ConnectionManagement/Negative/ServerPeers.agda +RTS -M9G -RTS`
passed cached, exit 0 with empty output. No interface purge or collector change.

The two-file local proof scan reports zero findings; whitespace/EOF checks pass.
No new axiom, hole, unsafe option, weakened old statement or added history premise.
This is not a term-level imported-assumption audit. Evidence:
`/tmp/cm-monitor-closed-20261104/`, including the generic log/result, fresh full
interaction log/result, final batch log/result, local audit and service journal.
Increment 48 is accepted and uncommitted alongside 45–47 after `29e5607`.
Presentations and native replays are untouched.

Next: increment 49, integrate the closed-snapshot lifecycle certificate with an
actual initialized callback exit and its existing governor/scope certificates,
deriving the closed observation from the enabled callback guard. Keep this
separate from remaining CM/handler/server completion and eventual progress.
G0–G5, CM-I4c and SI4/SI5 remain open.

## Forty-ninth increment: initialized callback-exit lifecycle integration

The overall CM/IG/OG/Server objective and G0–G5 remain in progress. Increment 49
integrates the initialized monitor lifecycle certificate with the actual Server
callback return and the existing governor/scope certificates, in the existing
`Properties/ServerPeersMonitorJoins.agda` module.

### Statement and proof layers

`Frontend.CallbackExit` retains initialization, the finite enabled prefix, the
actual inherited callback event, its real shared step, unchanged peer context,
callback closure guard, the existing `Shared.Certificates` and the new
`ClosedSnapshot`. `initialized-callback` requires only initialization, enabled
`Runs` and the actual `dispatch (serverStep (run (scope returnAction)))` step.
It lowers that event using the existing dispatch observation and real server
step. `callback-gate` and `closure-observation` derive governor-pool closure,
monitor-pool closure and the finished scope. Existing initialized component
proofs yield governor/scope terminal/join certificates; increment 48 yields the
ordered monitor histories. The caller supplies no closed-phase observation,
component certificate, terminal lookup or lifecycle history. No additional
coherence, supply, uniqueness or registry-absence premise.

`extend-lifecycle` retains the original cause and earlier publication/removal/
exit history while extending its actual suffix across a run with the same whole
monitor pool. `extend-closed` applies this to the ordered histories and extends
the initialized prefix, retaining closure, empty cursor and snapshot/joined
order. These helpers have explicit run/pool-equality premises; the main callback
theorem derives those facts from the actual event rather than requiring them.
`callback-monitors-after` uses that extension on the recorded pre-return
certificate, preserving its histories instead of making independent post-return
cause choices. `callback-pool-same` follows from the actual unchanged peer
context. `callback-components-after` transports the existing certificates across
that same context equality; those certificates concern its pools/scope, not a
claim that the whole CM source is unchanged.

This concerns the inherited callback return event. It adds no classifier for
arbitrary raw plan aliases. The result is finite conditional provenance, without
an eventual callback/shutdown theorem. Captured pool results and scope joins do
not establish completion of raw admissions, physical handlers, CM or Server.
No runtime, guard, initializer, source-pin or previous theorem-type change.

### Acceptance and validation

`Negative/ServerPeers.agda.CallbackLifecycleChecks` derives both the initialized
first-activation and restarted callback exits. It retrieves all component
certificates before/after return, nonempty captured monitor histories and actual
cancelled publication chains after return. The restarted case checks the real
shared step, retained snapshot/joined lists and the cause-preserving history
extension. Early return is rejected before peer closure, before monitor join
and before monitor finish; repeated return is rejected. The actual post-state is
`actionBodyExited`, not full Server return. The existing open physical-handler
pool and incomplete raw-admission facts remain explicit acceptance boundaries.
No new lifecycle driver or split fixture file.

Accepted 4 November 2026 with Agda 2.8.0. The generic command
`agda ConnectionManagement/Properties/ServerPeersMonitorJoins.agda +RTS -M4G -RTS`
freshly passed, exit 0 without warnings. An unresolved state-inference meta in
component transport was repaired with explicit state arguments before acceptance.
The fresh full maintained endpoint interaction load passed: process exit 0,
checked=true, errors/goals/warnings empty. It used normal caching/default GC,
9 GB heap below an 11 GB cgroup, zero swap and a 15 GB virtual limit; systemd reported 6.8G peak. Final
strict batch `agda ConnectionManagement/Negative/ServerPeers.agda +RTS -M9G -RTS`
passed cached, exit 0 with empty output. No interface purge or collector change.

The two-file local proof scan reports zero findings; whitespace/EOF checks pass.
No new axiom, hole, unsafe option, weakened old statement or supplied closure/
history premise. This is not a term-level imported-assumption audit. Evidence:
`/tmp/cm-callback-lifecycle-20261104/`, including generic log/result, full
interaction log/result, final batch log/result, local audit and service journal.
Increment 49 is accepted and uncommitted alongside 45–48 after `29e5607`;
presentations and native replays are untouched.

Next: increment 50, propagate these lifecycle certificates through the existing
initialized Server/IG shutdown prefix into actual CM entry. Retain the captured
handles and distinguish CM entry from CM completion. Remaining handler/admission
completion and eventual shutdown stay separate; G0–G5, CM-I4c and SI4/SI5 remain
open.

## Fiftieth increment: Server/IG-to-CM-entry lifecycle propagation

The overall CM/IG/OG/Server objective and G0–G5 remain in progress. Increment 50
carries the callback's component and captured-monitor lifecycle certificates
through the existing Server/IG shutdown prefix into the actual `beginCM` event.
The proof extends `Properties/ServerPeersMonitorJoins.agda`; acceptance stays in
`Negative/ServerPeers.agda`.

### Statement and proof layers

`Frontend.ServerRuns` records finite enabled inherited Server/IG actions. Every
edge uses the real frontend `advance (dispatch (serverStep action))` and retains
its original guards. `server-runs` exposes the ordinary runtime trace;
`server-runs-from` reuses an existing trace whose events are those actions.
`server-step-context` lowers each actual event through the shared dispatcher and
server rule; `server-context` derives equality of the peer contexts across the
whole suffix. No pool/context-preservation equation is supplied as a premise.
These steps can change the real CM/IG source; equality of peer metadata does not
erase those effects or assert that the whole source is unchanged.

The CM-entry action is the actual inherited `run (scope beginCM)`. The stage
lemmas inspect the real admission/IG/shared/frontend steps and derive its
`closingCM` result. No stage observation is supplied. `CMEntry` retains the
callback before/after states and derived `CallbackExit`, the actual Server/IG
cleanup suffix and its last pre-entry state, enabled entry event and resulting
stage. `initialized-cm-entry` requires initialization, enabled execution to the
callback, the callback return, that guarded suffix and the actual entry event.
`initialized-cm-entry-run` accepts the suffix ending in `beginCM` and extracts
its actual final predecessor/step. Neither requires a prior lifecycle/component
certificate, terminal lookup or additional preservation/coherence/supply premise.
The suffix restriction is explicit; this is not a theorem for arbitrary frontend events after the
callback or raw plan aliases.

`cm-cleanup` includes the final entry event. `cm-context-same` derives its context
preservation. `cm-monitors` extends the callback's original ordered lifecycle
histories and causes across this actual trace; it does not reclassify later
terminal cells. `cm-components` transports the existing governor/scope
certificates across the same context equality. Previous theorem interfaces and
runtime rules retain their types and definitions.

### Acceptance and validation

`ServerCMEntryLifecycleChecks` reuses the existing initialized restarted shutdown
and its 20 actual Server/IG edges, covering action-result publication, accept
cancellation/join, TraceStopped, callback join, IG cancellation, deactivation,
flush, final traversal, result publication/join and `beginCM`. It derives the
entry certificate without a supplied lifecycle or context-equality premise,
checks the concrete and recorded context equations, all component certificates,
ordered monitor histories and the original cancelled exit for ID 50. The
history-extension control retains the same cause through the concrete suffix.

Entry before the callback, immediately after it, or before the IG join is
rejected, as is repeated entry. Server finish at CM entry is rejected. In this
actual witness the CM coordinator has not yet captured its snapshot and both
current and older physical bodies remain running/unpublished. The certificate
therefore does not assert CM/handler/raw-admission/Server completion or eventual
shutdown. It adds no native replay or source-refinement claim and changes no
runtime, guard, initializer or source pin.

Accepted 4 November 2026 with Agda 2.8.0. The generic command
`agda ConnectionManagement/Properties/ServerPeersMonitorJoins.agda +RTS -M4G -RTS`
freshly passed, exit 0 without warnings. The fresh full maintained endpoint
interaction load passed: process exit 0, checked=true, errors/goals/warnings
empty. It used normal caching/default GC, 9 GB heap below an 11 GB cgroup,
zero swap and a 15 GB virtual limit; systemd reported 6.9G peak. Final strict batch
`agda ConnectionManagement/Negative/ServerPeers.agda +RTS -M9G -RTS` passed
cached, exit 0 with empty output. No interface purge or collector change.

The two-file local proof scan reports zero findings; whitespace/EOF checks pass.
No new axiom, hole, unsafe option, weakened old statement or supplied lifecycle/
preservation premise. This is not a term-level imported-assumption audit. Local
typing diagnostics were repaired by directly reducing specialized wrapper
guards. An initial full run was deliberately stopped to correct an opaque-record
fixture query before acceptance; it does not count as a successful check.
Evidence: `/tmp/cm-entry-lifecycle-20261104/`, including generic log/result,
successful interaction log/result, final batch log/result, local audit, stopped
attempt and service journal. Increment 50 is accepted and uncommitted alongside
45–49 after `29e5607`; presentations and native replays are untouched.

Next: increment 51, carry these certificates through the existing actual CM
cancellation-acknowledgement and physical-handler/CM-result-wait path. Retain the
captured identities and distinguish delivery acknowledgement, physical result
publication and the collective CM wait. Remaining admission/quiescence and
eventual-shutdown obligations stay explicit; G0–G5, CM-I4c and SI4/SI5 remain open.

## Fifty-first increment: CM cancellation receipts and physical handler results

The overall CM/IG/OG/Server objective and G0–G5 remain in progress. Increment 51
carries the captured monitor and governor/scope certificates through the actual
restarted CM acknowledgement, physical-handler finalizer and CM result wait.
The proof remains in `Properties/ServerPeersMonitorJoins.agda` and all acceptance
remains in `Negative/ServerPeers.agda`.

### Statement and proof layers

`handler-action`/`handler-event` name the inherited physical-handler operation
through the real publication/catch/DeltaQ/startup wrappers. `physical-lower`
lowers its enabled frontend event through the dispatch, shared Server, IG and
admission guards, then reuses each existing wrapper observation lemma to reach
the actual `MuxHandlerExit.step`. Individual lemma calls and selected record
exports avoid instantiating the wrappers' unrelated proof APIs. No alias bypass,
new runtime permission or guessed physical successor is introduced.

`MuxReceipt` retains the captured entry and worker from `awaitDelivery`, the
actual owner-abort step and CM acknowledgement against its real intermediate
state. `physical-receipt` derives it from an enabled frontend mux-delivery event.
It does not manufacture an Async result. `physical-publication` derives the
existing physical publication certificate from the actual frontend result
publication, retaining the body outcome, observed cleanup and completion guard.
`physical-wait` derives `Handler.PhysicalWait` from the actual frontend
`finishClose`. That certificate retains the real physical step, primitive wait,
the exact pre-wait result function and observed results for the collected handles;
a later closed flag or cleanup heap is not substituted for its oracle.

`follow-monitors` and `follow-components` extend the CM-entry certificates across
actual guarded inherited Server actions, deriving context preservation from
those steps. `CMResultWait` retains the earlier CM-entry certificate, exact
cleanup suffix, enabled frontend wait and derived physical wait. The initializer
`initialized-cm-result-wait` builds the entire chain from initialization, enabled
execution to the callback, actual callback return, checked Server/IG entry
suffix, checked CM/handler suffix and actual successful wait. It requires no
supplied receipt/publication/wait/lifecycle certificate, terminal lookup or
preservation equation. `wait-monitors-before/after` and
`wait-components-after` retain the ordered monitor histories/causes and existing
governor/scope certificates at the real wait. The suffix restriction to inherited
Server actions remains explicit; arbitrary frontend cache-writing plans are not
silently treated as context-preserving.

### Acceptance and validation

`CMResultLifecycleChecks` reuses the existing restarted receipt, 26-edge physical
pool close, catch and finalizer paths. A ten-edge prefix reuses the original
checked finalizer edges with explicit intermediate states, ending immediately
before the wait. Actual CM receipt, physical result publication and collective
wait each produce their own derived certificate. The captured receipt worker
is the original child; the wait oracle is exactly `resultReady` at `handler10`.
The original monitor cancellation history and all component certificates survive
the wait and the actual subsequent Server return.

Negative controls reject CM completion at receipt, physical-pool close, after
catch and before physical publication. Receipt and cleanup completion still
have no handler result. The actual published handler result retains its async
exception; the collected CM worker is unchanged. CM closes and Server returns
in this finite profile, while raw admission results remain incomplete. These
certificates therefore do not establish universal admission quiescence, eventual
shutdown or source refinement. No runtime, guard, initializer or source-pin change.

Accepted 4 November 2026 with Agda 2.8.0. The generic proof freshly passed
an interaction load with 9 GB heap under an 11 GB cap: process exit 0,
checked=true, errors/goals/warnings empty. Its selected exports and direct lemma
calls reported 3.7G peak. The fresh full maintained endpoint load also passed:
process exit 0, checked=true, errors/goals/warnings empty. The generic check
used a 15 GB virtual limit. The full check used an 11 GB heap below a 13 GB
cap and 17 GB virtual limit; it reported 8G peak. Both used normal
caching/default GC and zero swap. Final strict batch
`agda ConnectionManagement/Negative/ServerPeers.agda +RTS -M11G -RTS` passed
cached, exit 0 with empty output. No interface purge or collector change.

The two-file local proof scan reports zero findings; whitespace/EOF checks pass.
No new axiom, hole, unsafe option, weakened old statement or supplied physical
certificate/history/preservation premise. This is not a term-level imported-
assumption audit. Earlier generic 4 GB and full endpoint 9 GB runs exhausted
their heaps; a broad alias run was
stopped before replacing whole proof-module instantiations with direct lemma
calls. A local equality proof and a fixture alias collision were repaired before
acceptance. Diagnostic/failed/stopped runs do not count as acceptance.
Evidence: `/tmp/cm-result-lifecycle-20261104/`, including the separate generic
check log/result/journal, full endpoint log/result, final batch log/result,
audit and service journal. Increment 51 is accepted and uncommitted alongside
45–50 after `29e5607`; presentations and native replays are untouched.

Next: increment 52, apply the composed certificates to the existing
publication/cancellation and current-clean-commit race paths. Account explicitly
for frontend cache writes rather than assuming whole-context equality. Keep
initialized ownership, admission/quiescence and eventual-shutdown boundaries
explicit; G0–G5, CM-I4c and SI4/SI5 remain open.

## Fifty-second increment: cache-aware race lifecycle certificates

The overall CM/IG/OG/Server objective and G0–G5 remain in progress. Increment 52
extends the composed lifecycle certificates to the existing initialized
publication/cancellation and current-clean-commit races. The proof remains in
`Properties/ServerPeersMonitorJoins.agda`; acceptance remains consolidated in
`Negative/ServerPeers.agda`.

### Statement and proof layers

`frame-view` is the existing three-component peer-supervision view: governor
pool, monitor pool and scope state. `server-plan` recognizes inherited and
completion plans over actual Server actions. `framed` inspects the real frontend
`choose`, and `advance-frame` uses the actual selected plan and enabled enactment
to derive equality of those three components. A completion's physical Server
step retains its context; its later cache write uses the existing total
`Shared.Protocols.cache-view` lemma. Whole-context equality is not assumed and
is not concluded for completion plans.

`FramedRuns` records each actual event, its computed plan-classification proof
and enabled `advance`. `framed-runs` exposes the ordinary runtime trace;
`framed-view` derives preservation over the whole suffix. `framed-server`
embeds the earlier `ServerRuns` without changing their statements. The explicit
selected-plan restriction excludes arbitrary peer/caller/core/local/birth plans;
this is not a frame claim for every frontend event. No coherence, supply,
terminal-result, lifecycle-history or preservation equation is added as a premise.

`framed-monitors` extends the original ordered monitor lifecycle histories using
the derived monitor-pool equation. `framed-components` transports the existing
governor/scope certificates through the three component equations. These are
facts about the actual components, not an erasure of source/peer-cache changes.
`FramedCMResultWait` and `initialized-framed-result-wait` retain initialization,
actual callback/CM entry, the classified enabled suffix, actual final wait and
its derived physical certificate. The exact physical oracle remains the real
pre-wait `resultReady` function. Existing theorem/runtime interfaces are intact.

### Acceptance and validation

The race witnesses reuse original edge facts and exact source/event order, with
explicit intermediate states. The publication race retains the old normal
physical publication while current cancellation proceeds. The current-clean
race contains its actual `commitClean` completion and cache write after the
cancellation request. `RaceLifecycleChecks` derives both initialized final-wait
certificates, physical waits, governor/scope certificates and the original
cancelled monitor history; component certificates continue through actual
Server return.

The current commit preserves the three-component view, while a separate
counterexample requires its peer-cache lookup and whole context to differ.
Existing controls retain the current local clean result even when its physical
Async result is cancelled; local clean still does not supply a handler result
or finish CM before physical publication. Raw admissions remain incomplete.
The result is finite model provenance on these classified executions, without
universal quiescence, eventual shutdown, native refinement or a new source
finding. No runtime, guard, initializer or source-pin change.

Accepted 4 November 2026 with Agda 2.8.0. The generic interaction load
freshly passed: process exit 0, checked=true, errors/goals/warnings empty,
9 GB heap below an 11 GB cap, zero swap and 15 GB virtual limit; reported
3.9G peak. The full maintained endpoint interaction load freshly passed with
process exit 0, checked=true and errors/goals/warnings empty, using 11 GB heap
below a 13 GB cap, zero swap and 17 GB virtual limit; reported 8G peak.
Normal caching/default GC.
Final strict batch `agda ConnectionManagement/Negative/ServerPeers.agda +RTS -M11G -RTS`
passed cached, exit 0 with empty output. No interface purge or collector change.

The two-file local scan reports zero findings; whitespace/EOF checks pass.
No new axiom, hole, unsafe option, weakened old statement or supplied frame/
lifecycle/physical certificate. This is not a term-level imported-assumption
audit. A misplaced fixture import was repaired after an initial failed full
load; that diagnostic does not count as acceptance. Evidence:
`/tmp/cm-race-certificates-20261104/`, including generic check log/result/journal,
full endpoint log/result, final batch log/result, audit and service journal.
Increment 52 is accepted and uncommitted alongside 45–51 after `29e5607`;
presentations and native replays are untouched.

Next: increment 53, initialized handler resource provenance at physical result
publication and CM's wait. Connect the retained handler descriptor and its
entry/socket/promise references to their actual initialized fork/publication
history, reusing existing resource/capture invariants. Keep historical presence
separate from live ownership and admission quiescence. G0–G5, CM-I4c and SI4/SI5
remain open.

## Fifty-third increment: initialized handler resource origins

**Confirmed finding — model scope, accepted 4 November 2026.** This worktree
extension after `c1b631b` connects an initialized inbound handler's original
resources to physical publication and CM's actual wait. Network/consensus pins,
runtime rules, guards, initializers and earlier theorem statements are unchanged.

[ServerPeersHandlerResources](Properties/ServerPeersHandlerResources.agda)
fixes the complete `HandlerStart` throughout preservation. Existing subsystem,
acquisition-writer and Server/IG resource laws carry its handler lookup and
entry/socket presence through governor cancellation/cleanup and every frontend
plan, including completion cache writes. `PeerSupervisionSupply.Lift` factors
its existing observer-preservation proof; the original supply API is recovered
by the original predicate and writer law, with unchanged premises.

`Frontend.initialized-inbound-origin` takes initialization, an enabled prefix,
the actual prepared admission lookup, promise-allocation/selection/fork events,
and primitive source equations at those same states. Allocation derives the
new promise's membership and selected PC. Selection/fork derives the exact
original descriptor and entry/socket presence without a supplied resource,
coherence, supply or ownership certificate. The origin retains both checked
views of those events and an arbitrary enabled suffix. Its promise allocation
is historical; no claim about a current promise value or unique allocation is
added. This is an occurrence theorem, not inversion of arbitrary later lookups.

`extend` preserves that same history and descriptor. `publication-origin` derives
`AtPublication` from the actual guarded physical publication event; `wait-origin`
derives `AtWait` from the actual final CM wait and membership of this worker in
its collected list. The physical certificates, including the exact pre-wait
result oracle, are outputs. These statements neither establish origins for all
possible collected handlers nor prove universal completion or admission
quiescence.

[ServerPeers.HandlerResourceOriginChecks](Negative/ServerPeers.agda) reuses the
original initialized admission prefix and existing cleanup/race edge facts.
It applies the certificates at physical publication, CM wait and Server return,
and at both old-publication and current-clean race waits. Explicit projections
retain the original descriptor's resources. Controls reject a wrong worker and
forged entry reference, show the socket already closed before publication, and
retain premature-wait refusal and incomplete raw admissions.

Validation ran sequentially with Agda 2.8.0:

- `agda ConnectionManagement/Properties/PeerSupervisionSupply.agda +RTS -M7G -RTS`
  freshly passed, exit 0, under a 9 GB user-scope cap with swap disabled.
- `agda ConnectionManagement/Properties/ServerPeersHandlerResources.agda +RTS -M9G -RTS`
  freshly passed, exit 0, under an 11 GB cap with swap disabled.
- `agda ConnectionManagement/Negative/ServerPeers.agda +RTS -M11G -s -RTS`
  freshly passed, exit 0, under a 13 GB cap with swap disabled. Its own Checking
  line is present; no warnings, goals or errors. RTS reported 8249 MiB total
  memory in use, not an RSS measurement.

Normal caching/default GC; no interface purge. The three-file static audit has
zero findings; it is not a term-level imported-assumption audit. Preliminary
checks exposed a dependent-rewrite diagnostic, constructor-shadow warnings,
missing event arguments and a fixture-name collision; all were repaired before
acceptance. The sandbox initially refused the user bus; checks then used the
approved bounded user scopes. Logs: `/tmp/cm-handler-resources-20261104/`
(`peer-lift.log`, `origins-fourth.log`, `acceptance-second.log`, `audit.log`).
No native replay, new source finding, presentation refresh or commit.

**Next: increment 54, derive the primitive admission steps from actual frontend
events**, removing the duplicated source-step inputs from the initialized
inbound origin API while retaining all its guards and original resource/history
outputs. Wider outbound origins, CM-I4c, SI4/SI5 and G0–G5 remain open.

## Fifty-fourth increment: primitive admission steps from frontend events

**Confirmed finding — model scope, accepted 4 November 2026.** This uncommitted
extension after `c1b631b` removes the duplicated primitive-step inputs from the
preferred initialized inbound origin constructor. The existing paired-view
statement, `Origin` record, resource predicates and physical publication/wait
statements are retained unchanged. Runtime rules, guards, initializers and source
pins are unchanged.

[ServerPeersHandlerResources](Properties/ServerPeersHandlerResources.agda)
now proves `allocation-lower`, `selection-lower` and `fork-lower` from the actual
enabled frontend events. The proof reuses the outer dispatch/Server/IG and
exception-wrapper lowering, then retains every handler-exit, group, monitor,
protocol-job, mux-startup and outbound-wrapper permission. Promise allocation
and entry selection expose their actual dispatcher step. Fork separately retains
its physical thread-registration guards and a `ForkObservation` containing the
actual primitive computation and exact resulting source projection. Registry
metadata is not substituted for that source step.

`initialized-inbound-origin-from-frontend` derives all three primitive equations
and applies the existing origin theorem. Its inputs are initialization, the
enabled prefix, the actual prepared admission lookup, the three enabled
frontend events and the enabled suffix. It takes no primitive-step or resource
certificate. The returned record still contains both checked event/source views,
original descriptor, historical promise allocation and retained entry/socket
identities. This remains an initialized inbound occurrence result, not inversion
of arbitrary collected handlers or a live-ownership/quiescence theorem.

[HandlerResourceOriginChecks](Negative/ServerPeers.agda) now constructs the
origin without the former three source-equation arguments. Named checks expose
each derived primitive step; new controls reject allocation before admission,
selection before promise allocation and fork before entry selection. The prior
publication, CM wait, Server-return and both race applications remain, alongside
the closed-socket, forged-descriptor and premature-wait controls.

Validation ran sequentially with Agda 2.8.0:

- `agda ConnectionManagement/Properties/ServerPeersHandlerResources.agda +RTS -M9G -s -RTS`
  freshly passed, exit 0, with its own Checking line and no warnings, under an
  11 GB user-scope cap with swap disabled. RTS reported 3241 MiB total memory
  in use, not RSS.
- `agda ConnectionManagement/Negative/ServerPeers.agda +RTS -M11G -s -RTS`
  freshly passed, exit 0, with its own Checking line and no warnings, under a
  13 GB cap with swap disabled. RTS reported 8224 MiB total memory in use,
  not RSS. The existing descriptor `refl` checks still pass.

Normal caching/default GC; no interface purge. The three-file local static
scan has zero findings, not a term-level imported-assumption audit. Preliminary
checks exposed branch-equality and dependent fork-transport diagnostics;
`ForkObservation` resolves the latter without changing premises or semantics.
Logs: `/tmp/cm-handler-frontend-20261104/` (`properties-fifth.log`,
`acceptance-first.log`, `audit.log`). No native replay, new source finding,
presentation change or commit.

**Next: increment 55, initialized outbound handler resource origins.** Extend the
origin construction to the actual outbound promise/fork route, deriving the
captured entry/socket/promise references from its initialized execution and
existing acquisition-capture laws. Reuse resource retention and physical-boundary
certificates; do not assume resource validity or live ownership. Arbitrary
collected-handler inversion, CM-I4c, SI4/SI5 and G0–G5 remain open.

## Fifty-fifth increment: initialized outbound handler resource origins

**Confirmed finding — model scope, accepted 4 November 2026.** The uncommitted
[resource-origin module](Properties/ServerPeersHandlerResources.agda) now derives
outbound promise/fork histories from the actual common frontend. The existing
inbound statements remain unchanged. Runtime semantics, guards, initializers and
the source pin above are unchanged.

`initialized-outbound-origin` starts with an empty acquisition runtime supplied
by `CM.initial` and a successful frontend initializer. Its pre-birth
`AcquisitionRuns` contains enabled common-route begin/acquire calls, potentially
from multiple callers; it does not yet permit arbitrary frontend interference
before birth. Lowering retains the frontend permissions and physical fork
registration, yielding the actual outbound-machine steps. Existing
`OutboundRuntimeCapture` laws derive the selected entry's historical allocation
from this initialized execution. No resource-validity, supply or live-owner
certificate is supplied by the caller.

The resulting `OutboundOrigin` records the original initializer, prefix,
promise-allocation event, acquisition route, exact fork lookup/event, primitive
source equations and fixed descriptor. `extend-outbound` retains that descriptor
with its entry/socket/promise/key references and the stored entry/socket facts
through every enabled frontend suffix. Promise membership is recorded at
allocation, not asserted at every later state.
`outbound-publication-origin` and `outbound-wait-origin` derive the existing
physical raw-handler publication and outer CM final-wait certificates from
their actual frontend events, including the combined physical result oracle
used by that wait. The acceptance uses the owned Server shutdown route; the
nested raw-handler coordinator alias is refused. They establish neither
universal Server return nor admission quiescence, eventual progress, source
refinement or arbitrary collected-handler origin inversion. Historical socket presence remains compatible with closure.

[OutboundHandlerResourceOriginChecks](Negative/ServerPeers.agda) stays in the
single acceptance file. It adapts the prior outbound scenario's expected states
by removing unused inbound actors, then independently checks every edge from a
successful full frontend initializer. The path allocates promise 0, forks the
captured child, enters its handshake before Connected, performs the mandatory
parent handoff, closes the empty peer pools and four lexical scopes, and
executes the actual Server callback/listener/IG shutdown sequence into CM. It
then proceeds through cancellation, cleanup, physical publication and the
outer coordinator's result wait. The descriptor is definitionally unchanged;
the final socket is closed. Controls refuse early fork/publication/wait,
duplicate publication, a parent Connected commit before handoff, the nested
coordinator alias and outer CM capture before Server scope closure. The final
state remains `closingCM`, distinct from Server return.

Validation on 4 November used Agda 2.8.0 sequentially:

- `agda ConnectionManagement/Properties/ServerPeersHandlerResources.agda +RTS -M9G -RTS`
  freshly passed, exit 0, own Checking line and no warnings, under an 11 GB
  user-scope memory cap with swap disabled.
- `agda ConnectionManagement/Negative/ServerPeers.agda +RTS -M11G -RTS`
  freshly passed, exit 0, own Checking line and no warnings, under a 13 GB cap
  with swap disabled.

Normal caching/default GC; no interface purge. The local three-file static scan
has zero findings; it is not a term-level imported-assumption audit. All accepted
increment-54 definitions are retained verbatim apart from adding `map` to an
import. Development checks exposed and repaired a shadowed constructor name and
acceptance-local name/qualification collisions. Inspection of the model
`MuxHandlerExit.delegateAllowed` caught the refused nested coordinator route;
superseded checks were stopped and the acceptance was replaced by the owned
outer shutdown history. The owned-route check also rejected a raw IG-delivery
shortcut; the final history retains the actual receipt and empty callback
snapshot. Handler cleanup uses `H.cleanup` rather than the refused raw
dispatcher alias. Final logs: `origin-owned.log`, `acceptance-owned-third.log`
and `audit-owned.log` in `/tmp/cm-outbound-origins-20261104/`.
Local-link checks covered the four affected Markdown pages: 348 local targets,
zero errors or fragment/URI review notes. Both Mermaid blocks are unchanged;
no diagram rendering was needed. Tracked diff and new-module whitespace checks
passed. No native replay, source revalidation, presentation change or commit.

**Next: increment 56, broader initialized pre-birth frontend histories.** Lift
acquisition-capture validity through the actual combined frontend, so the
outbound origin constructor can admit interference before birth rather than
only `AcquisitionRuns`. Preserve the present constructor and statements, derive
validity from initialization, and add an enabled interfering-history acceptance
with refusal controls. Arbitrary collected-handler inversion remains separate;
CM-I4c, SI4/SI5 and G0–G5 remain open.

## Fifty-sixth increment: outbound origins through frontend interference

**Confirmed finding — model scope, accepted 4 November 2026.** The uncommitted
[resource-origin module](Properties/ServerPeersHandlerResources.agda) now derives
active acquisition-capture validity through every enabled combined frontend
plan. The original inbound and acquisition-only outbound occurrence records,
constructors, extension and boundary definitions remain verbatim. Runtime rules,
guards, initializers and the upstream source pin are unchanged.

`Observer` factors the existing resource-preservation implementation over the
active acquisition runtime and shared world. It reuses actual subsystem,
cancellation and Server writer laws, then transports the predicate through
physical governor/peer bookkeeping and all frontend plans, including result-cache
writes. The old `For` API specializes it to fixed resource facts; `Captures`
specializes it to `OutboundRuntimeCapture.RuntimeValid`. Cancellation start
removes the selected caller while retaining the remaining captures. Detached
cleanup retains that active runtime without requiring a validity or supply
certificate for its detached frame.

`initialized-frontend-captures` starts from `CM.initial` and a successful
frontend initializer, then follows arbitrary finite `T.Runs`. The new
`OutboundFrontend.initialize-history` uses this result for both the prefix
before promise allocation and the route between allocation and fork. These
histories may contain any enabled frontend events. The caller supplies neither
resource validity nor supply/ownership premises. The returned `History` keeps
the actual primitive allocation/fork equations, fixed descriptor, historical
promise allocation and stored entry/socket facts. `extend-history`,
`publication-history` and `wait-history` retain this history through actual
suffixes and derive the physical publication and guarded outer CM-wait
certificates. Promise membership remains an allocation-time fact; live ownership,
universal progress/return, admission quiescence and arbitrary handler-origin
inversion do not follow.

[ServerPeers acceptance](Negative/ServerPeers.agda) keeps the new checks in
`OutboundHandlerResourceOriginChecks.Interference`. Its initialized prefix
publishes the peer view, begins outbound acquisition, admits an independent
Server worker and advances IG's clock between outbound socket actions. The
actual fork retains the original descriptor while the independent admission,
peer PC and IG continuation remain visible. This mixed path continues through
child handshake entry. Controls refuse duplicate admission/clock progress,
a raw acquisition alias and premature fork. A separate application of the
broader constructor follows the existing owned shutdown history through
physical publication and CM wait.

Validation used Agda 2.8.0 sequentially:

- `agda ConnectionManagement/Properties/ServerPeersHandlerResources.agda +RTS -M9G -RTS`
  freshly passed, exit 0, own Checking line and no warnings, under an 11 GB
  user-scope memory cap with swap disabled.
- `agda ConnectionManagement/Negative/ServerPeers.agda +RTS -M11G -RTS`
  freshly passed, exit 0, own Checking line and no warnings, under a 13 GB cap
  with swap disabled. Existing descriptor `refl` checks still pass.

Normal caching/default GC; no interface purge. The local three-file static scan
has zero findings, not a term-level imported-assumption audit. An initial
acceptance-local helper-name collision and IG test-event wrapper diagnostic
were repaired. Final logs: `history-first.log`, `acceptance-third.log` and
`audit.log` in `/tmp/cm-prebirth-captures-20261104/`.
Local links: four affected Markdown pages, 354 local targets, zero errors or
fragment/URI review notes. Both Mermaid blocks remain verbatim; they were not
re-rendered. Tracked diff and new-module whitespace checks passed. No native
replay, new upstream source validation, presentation change or commit.

**Next: increment 57, initialized handler birth backing.** Begin arbitrary
collected-handler origin inversion by deriving the prior enabled physical fork
from an initialized frontend history and a current physical handler-registry
lookup.
Retain the actual inbound/outbound route and original descriptor; do not accept
a caller-supplied birth event or resource certificate. This is a prerequisite
for arbitrary collected-handler origins, not a shutdown-completeness claim.
CM-I4c, SI4/SI5 and G0–G5 remain open.


## Fifty-seventh increment: initialized physical handler birth backing

**Confirmed finding — model scope, accepted 4 November 2026.**
[HandlerBirthBacking.Frontend.initialized-birth](Properties/HandlerBirthBacking.agda)
takes successful `ServerPeers.Protocols.initialize`, a finite enabled `Runs`
history and a current lookup in the actual `B.threads` registry. It derives
`Backing`: the earlier frontend prefix/event/suffix, enabled event and selected
nested plan, an enabled inbound or outbound physical fork at that event's
physical input, and the same original captured descriptor at the fork and now.
The caller supplies no birth occurrence, supply/coherence invariant or
resource-validity certificate. `selected-operation` equates the returned physical
operation with inversion of the stored actual selected call; a compatible
source-only transition is insufficient. Wrapper bookkeeping after the fork is
related by capture-map equality; it is not claimed to leave the entire physical state equal.

[HandlerBirthEffects](Properties/HandlerBirthEffects.agda) proves the guarded
physical capture-map effects, preservation and first-appearance search. Only the
two real physical fork routes add a capture; phase changes and other operations
preserve it. The effects module covers actual enabled fault, Server, IG and
shared-peer steps. The backing module handles frontend plans and inverts the selected
nested operation. Successful initialization supplies an empty physical registry.
Source-only updates are separate from physical birth, and frontend protocol-job
birth is separate from parent-handler birth. Existing resource-occurrence APIs
remain available unchanged. `follow` preserves the same discovered fork through
opaque enabled suffixes; `follow-operation` states exact operation retention.
`current-thread` recovers a current physical lookup from the retained capture.

The [resource integration](Properties/ServerPeersHandlerResources.agda), in
`BackedShutdown`, derives one `InitializedShutdown` certificate across the
pre-handshake cancellation route. It starts from initialization, an enabled
prefix and the physical lookup before delivery. Actual acknowledgement,
cleanup, result publication, traversal and wait edges then retain the same birth,
without new physical lookup or resource-validity premises at later boundaries.
The awaited CM recipient must match the worker, and final snapshot membership
remains explicit. `HandshakeReceipt.primitive-ack` exposes the actual CM
acknowledgement; `RawFacts.ResultPublication` observes real cleanup/result
publication; `PhysicalWait` retains the exact **pre-wait** result oracle.
`same-birth-command` and `result-at-final-wait` connect the common birth and
collected worker to those observations. This is a handshake-cancellation
integration, not coverage of every handler/mux shutdown route.

[ServerPeers acceptance](Negative/ServerPeers.agda), in
`Protocols.HandlerBirthBackingChecks`, applies the public theorem to the
initialized inbound fork and an initialized outbound history continuing through
peer/scope closure and physical handler cleanup. Its `ShutdownBatch` reuses
opaque runs and the existing deterministic prefix-removal lemma, then reaches
CM acknowledgement, handler result publication and final CM wait as one
milestone. It checks current physical membership, the same discovered fork and
the final pre-wait result. Controls show acknowledgement supplies no result,
publication is still required, duplicate publication is refused, and CM wait
leaves Server at `closingCM`. Repeated fork, child freshness and initial-adoption
refusal and existing descriptor `refl` checks remain in the same endpoint.

Validation used Agda 2.8.0 sequentially on 4 November 2026:

- `agda --profile=definitions ConnectionManagement/Properties/HandlerBirthEffects.agda +RTS -M11G -RTS`
- `agda --profile=definitions ConnectionManagement/Properties/HandlerBirthBacking.agda +RTS -M11G -RTS`
- `agda --profile=definitions ConnectionManagement/Properties/ServerPeersHandlerResources.agda +RTS -M11G -RTS`
- `agda ConnectionManagement/Negative/ServerPeers.agda +RTS -M11G -RTS`

All four freshly passed with their own Checking lines, exit 0 and no warnings,
under a 13 GiB user-scope cap and with swap disabled. Normal caching/default GC;
no interface purge. Focused prefix checks guided editing; full acceptance ran
when the batch was ready. The first full run exposed a projection hidden by an
opaque certificate; an explicit projection equality repaired the concrete
pre-wait check without weakening it or unfolding its trace.

Earlier diagnostic checks included an 11 GiB heap exhaustion and stopped runs.
Narrow runtime/proof interfaces and flat component references reduced the
focused prefix from about 343 seconds to 51 seconds. Local guard, layout, name
and implicit-argument diagnostics were repaired. Final logs in
`/tmp/cm-handler-backing-20261104/`: `effects-flat-full.log`,
`backing-batch-third.log`, `shutdown-third.log`, `acceptance-second.log`,
`audit-final.log`. The four-file static proof scan found zero findings; this is
not a term-level imported-assumption audit. No new source replay, upstream
revalidation, presentation change or commit. Four-page local-link check: 364
targets, zero errors or fragment/URI review notes. Both Mermaid blocks remain
verbatim; unchanged diagrams were not rendered. External URLs were not fetched.
Whitespace checks passed.

**Open question — next increment:** connect arbitrary collected CM workers to
actual physical membership under the intended initialized profile and combine
the discovered fork with resource-origin evidence. A CM entry naming a worker
is not itself a physical lookup. This increment proves finite birth backing;
it adds no live-ownership, universal delivery/return, admission-quiescence or
whole-system shutdown theorem. G0–G5, CM-I4c and SI4/SI5 remain open. Upstream
network pin `96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d` and consensus pin
`585a86117618ff86d7d5b541f9d23b03356d4c3a` remain unchanged; no new source
conformance or replay result is inferred from these model checks.

The physical-membership part of that dated next step is established by increment
58 below; the generalized resource-origin obligation remains open.

## Fifty-eighth increment: acknowledged collected-handler birth backing

**Accepted model result, 5 November 2026.**
[Physical membership](Properties/HandlerAuxFrontend.agda), in
`Frontend.initialized-member`, takes successful initialization, an enabled
finite frontend run and membership in the current `Close.collected` list. It
returns a real physical `H.Thread` lookup. The thin
[birth corollary](Properties/CollectedHandlerBirth.agda),
`Frontend.initialized-birth`, uses that lookup internally and returns the
original descriptor and existing `HandlerBirthBacking.Frontend.Backing`: an
actual selected inbound/outbound fork with its enabled operation and frontend
location. Neither API takes a supplied physical lookup, birth/resource oracle,
empty-CM or admission-quiescence premise.

[Auxiliary backing](Properties/HandlerAuxBacking.agda) tracks presence for mux
frames, saved unwind faults and exit frames; it requires no descriptor-coherence
invariant. [Collection backing](Properties/CollectedHandlerBacking.agda) covers
all guarded lower acknowledgements. One upper induction preserves both facts,
including DeltaQ, catch/publication unwind and the frontend start-tracer receipt.
Plan safety comes from actual `choose`; arbitrary manually constructed plans
are not assumed safe. The separate birth corollary keeps the birth-inversion
closure out of the larger membership induction.

[Acceptance](Negative/ServerPeers.agda), in
`Protocols.InitializedCollectedExamples`, applies both closed APIs to existing
opaque initialized inbound/outbound shutdown runs through the final CM wait.
`SameEntryFailedForkControl` forks the first handler, reuses its exact entry for
a second admission, then fails that second fork and restores the map. Its
initialized prefix retains the overwritten entry naming the absent new child
and the old physical handler. Its subsequent snapshot/read/request checks are
**raw coordinator** steps, not an initialized frontend shutdown suffix; Server
is still serving. `PreloadedEntryCountercontrol` separately checks accepted
initialization with an unbacked entry and an empty collected list. These close
the earlier fresh-entry versus same-entry witness gap. Existing premature-wait,
acknowledgement-without-result and duplicate-publication controls remain.

Entry/snapshot targets and acknowledged workers remain distinct; collection
retains duplicates and acknowledgement supplies no Async result. The
[source/evidence audit](../review/connection-management-increment58-coverage-2026-11-05.md)
retains the network/consensus pins and the unresolved concrete `mfix`/socket
scenario questions. Runtime rules, initializers and guards are unchanged. This
is no new Haskell defect, replay or source-conformance result.

Validation used Agda 2.8.0, one process at a time:

- `agda ConnectionManagement/Properties/HandlerAuxBacking.agda +RTS -M11G -RTS`
- `agda ConnectionManagement/Properties/CollectedHandlerBacking.agda +RTS -M11G -RTS`
- `agda --profile=definitions ConnectionManagement/Properties/HandlerAuxFrontend.agda +RTS -M11G -RTS`
- `agda --profile=definitions ConnectionManagement/Properties/CollectedHandlerBirth.agda +RTS -M11G -RTS`
- `agda --profile=definitions ConnectionManagement/Negative/ServerPeers.agda +RTS -M11G -RTS`

All five passed fresh with their own Checking lines, exit 0 and no warnings;
11 GiB heap / 13 GiB user-scope cap, swap disabled, normal caching/default GC,
no interface purge. Focused prefix checks guided editing, followed by full
acceptance. Four concurrent roles handled auxiliary proofs, collection proofs,
evidence/controls and integration; compiler checks stayed sequential.
Two earlier frontend checks were deliberately interrupted (exit 130) as memory
rose; they were not successful checks or heap-exhaustion results. Flat narrow
aliases and the dependency split made the final frontend check tractable
(profile total 35,076 ms; thin corollary 22,316 ms). These are measurements of
this batch, not general runtime guarantees. Name, inference, branch-refinement,
case-coverage and constructor-shadow diagnostics were repaired without changing
the statements.

Final logs: `/tmp/cm-collected-backing-20261105/{aux-12,collected-06,upper-07,birth-01,acceptance-04}.log`.
The five-file local proof audit found zero findings; it is not a term-level
imported-assumption audit. Five Markdown pages passed 399 local link/anchor
checks with no errors or fragment/URI review notes; whitespace passed. Both
existing Mermaid blocks are unchanged and were not re-rendered. External
URLs were not fetched. No native replay or presentation refresh was performed during validation.

Resource-origin reconstruction remains a separate obligation. Arbitrary
initialization can retain preloaded acquisition frames and resource heaps;
[the next premise audit](../review/connection-management-increment58-coverage-2026-11-05.md#increment-59-premise-audit)
therefore calls for a formal control and justified origin profile before a
generalized history theorem. Keep intervening enabled events explicit rather
than imposing adjacency from an older occurrence record. Live ownership,
admission quiescence, a census of every handler, eventual completion and whole
shutdown remain open, as do G0–G5, CM-I4c and SI4/SI5.


## Fifty-ninth increment: initializer boundary and gap-aware resource histories

**Accepted model result, 5 November 2026; uncommitted over `3822a47`.**
[HandlerOriginRetention](Properties/HandlerOriginRetention.agda) derives stored
entry presence from an actual positive selection and preserves it through enabled
frontend gaps. Selection can also return denial: `selected-entry-present` takes
the positive post-PC rather than asserting that every enabled choose succeeds.
The pre/post-PC equalities are operational branch/alignment premises.

[HandlerOriginHistory](Properties/HandlerOriginHistory.agda), in
`Frontend.initialize-history`, records actual allocation, selection and fork
with two enabled gaps, the same parent/request/lease/promise/entry, primitive
source equations derived from frontend events, and the exact captured descriptor.
Entry presence follows from positive selection and retention; the actual fork
establishes stored handler/socket facts. No supplied resource-validity or physical
thread lookup is an input. Matching admission PCs before selection, after positive
selection and before fork remain explicit; initialization and `Runs` alone do
not discover these occurrences. `extend-history` retains the original evidence
through arbitrary enabled suffixes; `events`/`execution` include both gaps.
`empty-gaps-origin` and `empty-gaps-captured` recover the existing adjacent API
and exact descriptor without changing that API.

**Confirmed initializer boundary:**
`Negative/ServerPeers.Protocols.PreloadedAcquisitionForkControl` checks successful
initialization with a preloaded outbound `forkHandler entry99 promise88 key` frame.
A different entry names the fresh child. The real guarded frontend `forkOK` creates
the physical handler with that exact descriptor and a socket, while the captured
entry/promise remain absent. `preloadedResourcesImpossible` refutes stored resource
facts for this descriptor. The paired `initialize (O.initial core)` succeeds but
refuses the immediate fork. `O.initial` clears acquisition bookkeeping; it does
not establish empty core promise/result heaps or global identity freshness.
This is a model initializer boundary, not a new source defect or replay.
No malformed collected suffix is claimed: the missing entry also blocks the
checked connected commit and can prevent captured-entry cleanup.

**Confirmed applications:** `Protocols.InboundTwoGapOriginChecks` uses real
IG time capture between allocation and selection, then inactivity-timer
registration between selection and fork. Both gaps are nonempty. The same
history is retained through actual handler result publication and the final CM
wait, preserving both gaps and `I.captured`. A 13-edge bridge moves those genuine
timer effects earlier while preserving later allocated engine handles/muxes;
then it rejoins the existing opaque suffix. Empty-gap compatibility and forged
promise/entry descriptor and PC contradictions are checked. These contradictions
refute certificates; the runtime actions do not accept forged descriptor arguments.
The new gapped final execution also feeds increment 58's closed membership/birth
APIs; its discovered original descriptor equals `I.captured`. Existing outbound
mixed-route, publication/wait and negative controls remain in full acceptance.

Allocation records historical promise membership and equality with the allocator's
input counter. It supplies no current promise-retention, global freshness or
uniqueness theorem. Stored entry/socket presence is not live ownership. Automatic
history discovery from arbitrary collected membership, broader shutdown packets,
admission quiescence, eventual completion and full shutdown remain open.

Validation on 5 November used Agda 2.8.0, one process at a time:

- `agda --profile=definitions ConnectionManagement/Properties/HandlerOriginRetention.agda +RTS -M11G -RTS`
- `agda --profile=definitions ConnectionManagement/Properties/HandlerOriginHistory.agda +RTS -M11G -RTS`
- `agda --profile=definitions ConnectionManagement/Negative/ServerPeers.agda +RTS -M12G -RTS`

All three passed fresh, own Checking lines, exit 0 and no warnings. Focused checks
used 11 GiB heap / 13 GiB user scopes; full acceptance used 12 GiB heap / 14 GiB
scope after the prior 11 GiB attempt exhausted its heap (exit 251). Swap was
disabled in every scope; normal cache/default GC, no interface purge.
Retention/history profile totals were 23,551/24,249 ms;
full acceptance was 260,478 ms. Isolated initializer and two-gap applications
also passed fresh before consolidation (12,255/36,919 ms). An initial indentation
parse error, missing scratch harness import and integrated `subst` import were
repaired; failed attempts are not successful checks. No proof statements, runtime
rules, initialization contracts or guards were weakened.

Final logs: `/tmp/cm-origin-history-20261105/{retention-02,history-01,control-02,gaps-03,acceptance-03}.log`;
`verification.json` records the batch. The three-file local static proof audit
found zero findings; it is not an imported term-level axiom audit. Affected topic,
README, index, audit and state links/anchors passed: five pages, 405 local targets,
zero errors or fragment/URI review notes. Whitespace passed. Both
existing Mermaid blocks are unchanged and were not re-rendered; external URLs
were not fetched. The upstream network pin
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d` and consensus pin
`585a86117618ff86d7d5b541f9d23b03356d4c3a` are unchanged. No native replay,
source revalidation, presentation refresh or commit was performed for this batch.


## Sixtieth increment: automatic inbound occurrence reconstruction

**Accepted model result, 5 November 2026; uncommitted over `3822a47`.**
[InboundOriginResources](Properties/InboundOriginResources.agda), in
`Frontend.initialize-origin`, takes successful initialization, an actual enabled
frontend prefix, a classified canonical/core inbound-fork label and its enabled
step, and an enabled suffix. It derives all allocation/selection/fork PC matches,
the same request/lease/promise/entry, the actual captured descriptor, historical
promise membership at allocation, and stored handler/entry/socket facts at birth
and the current state. No caller-supplied PC, primitive computation, physical
lookup or resource-validity certificate is an input to this closed endpoint.

**Confirmed reconstruction:**
[the generic search](Properties/InboundOriginFrontend.agda) locates the actual
positive selection behind the terminal fork continuation, then searches its
strict prefix for allocation. [The initializer adapter](Properties/InboundOriginReconstruction.agda)
derives the empty admissions table from the existing successful Server guard;
its primitive-fork inversion derives the request and continuation fields.
Each occurrence retains its actual event, enabled prefix/gaps and an equality
decomposing the original observed list. Core-dispatch and Server-wrapped labels
remain distinct; no observed run is relabeled. The resource layer's synthetic
canonical transition only inverts the same delegated core operation.

[Core](Properties/InboundOriginCore.agda) and
[effect](Properties/InboundOriginEffect.agda) proofs classify one admission update
per enabled event: unchanged table, non-origin continuation, allocation or positive
selection, with the exact primitive cause. The effect relation has no arbitrary
sequential-composition constructor. [Quiet component proofs](Properties/InboundOriginQuiet.agda)
and [raw](Properties/InboundOriginRaw.agda), [lower](Properties/InboundOriginLower.agda),
[upper](Properties/InboundOriginUpper.agda) wrappers cover actual guarded steps.
[Peer preservation](Properties/InboundOriginPeers.agda) uses the shared dispatcher's
refusal of raw peer-core aliases. [Selector safety](Properties/InboundOriginPlanSafety.agda)
identifies the one eager-start caller plan; [the full runtime observer](Properties/InboundOriginRuntime.agda)
therefore requires no caller-supplied effect or permission oracle.

The existing peer-job, subsystem and peer-supervision observer proofs now expose
narrower reusable interfaces while retaining their original unrestricted public
types and premises. The resource layer reuses the positive-selection proof through
an additive `HandlerOriginRetention.selected-entry-from-source` export and the
existing exact-descriptor fork/retention laws. Heavy birth inversion stays outside
the full-event observer/search import closure. `canonical-history` maps the located
packet to the unchanged increment-59 History when its three operation labels are
canonical; it does not relabel mixed histories. `extend-origin` copies the same
reconstructed packet, descriptor, birth facts and allocation witness while appending
the actual suffix; `events`/`execution` retain the original observed list.

**Confirmed acceptance:** `Negative/ServerPeers.AutomaticInboundChecks` applies
the closed API to canonical empty/nonempty gaps, mixed core/Server labels,
unrelated-parent admission interference, and a second successful fork reusing the
same CM entry. It checks exact observed lists, recovered descriptors and derived
resource facts, plus forged-descriptor, denied-selection, failed-fork, caller-reuse,
cancellation/restart and forbidden-alias controls. Same-entry overwrite changes
the mutable value while both original physical captures remain; identity presence
does not assert current map ownership.
`Protocols.AutomaticInboundWaitChecks` reconstructs the exact increment-59 nonempty
gap path automatically, then extends that same packet via existing opaque runs
through actual result publication and the final CM wait. It preserves the packet,
original decomposition and descriptor, and feeds its exact execution into the
existing closed collected-birth theorem. Existing inbound/outbound, publication/
wait and initialized malformed-control regressions remain in full acceptance.

The endpoint covers an actual enabled inbound fork in either supported label form,
with an unrestricted enabled prefix/suffix. It is not yet automatic resource
reconstruction for every CM-collected worker. The outbound preloaded-acquisition
countercontrol remains; no global promise freshness/uniqueness, live ownership,
admission quiescence, eventual completion or whole shutdown is established.

Validation on 5 November used Agda 2.8.0, sequential bounded processes. Focused
checks included Core, Quiet, PlanSafety, Peers, Reconstruction and Resources;
the latter checked the final Runtime/Upper closure transitively. The generic
Effect/search and raw/lower proofs were also checked transitively. Commands used
`agda --profile=definitions <module>.agda +RTS -M11G -RTS` inside 13 GiB user scopes
with swap disabled. Final focused logs include `core-07`, `quiet-01`, `observer-06`,
`plan-01`, `peers-03`, `reconstruction-02`, `resources-05` and `narrow-02`.
Resources passed fresh without warnings (28,579 ms profile total); independent
five-case automatic acceptance also passed fresh without warnings (29,823 ms).
Scratch initializer, source projections and short controls were checked during
editing. Initial name, implicit-argument, with-abstraction and instance diagnostics,
and constructor-shadow warnings, were repaired without weakening statements.

The first full acceptance attempt found an ill-typed comparison between dependent
decomposition proofs in the new wait example. Explicit transport across the
proved packet equality repaired it; the corresponding generic transport passed
a focused fresh check (`transport-01.log`, 17,885 ms). This failed full attempt
is recorded in `acceptance-01.log`, not counted as success.
A subsequent full run exhausted its 12 GiB heap (`acceptance-02.log`, exit 251).
The wait example now keeps the recovered origin opaque and transports the
proved packet/capture equalities explicitly, preserving its original statements.
The next 12 GiB run also exhausted its heap (`acceptance-03.log`). Flat,
narrow aliases now avoid repeated copies of the closed history/runtime namespaces;
the resource API and unchanged control matrix were focus-checked again. This
Agda release omits per-declaration debug output, so the attempted verbosity flag
provided no per-definition progress. No interfaces or verification gates were purged.
After scope-only integration preflight, the final strict full command was:
`agda --profile=definitions ConnectionManagement/Negative/ServerPeers.agda +RTS -M12G -RTS`
inside a 14 GiB user scope, swap disabled. It passed fresh, own Checking line,
exit 0 and no warnings; full profile total 423,612 ms. Normal cache/default GC,
no interface purge. Four roles worked concurrently; all compiler checks stayed
sequential. Logs and reviewed audit detail: `/tmp/cm-inbound-reconstruction-20261105/`,
including acceptance-04.log, `verification.json`, `audit-final.log` and `audit-review.json`.
After acceptance, spaces on 19 otherwise blank Core lines were removed; all
tokens and line numbers are unchanged, with checked and final hashes retained.
The static scan's six possible-hole findings were inspected: all are the ordinary
`≤?` decision operator, not holes. No actual holes, added axioms or disabled safety
checks were found; an imported term-level axiom audit was not performed.

Affected topic/README/index/audit/state local links and whitespace passed; both
existing Mermaid blocks are unchanged and were not re-rendered. External URLs
were not fetched. Runtime rules and guards, source pins, presentation files and
unrelated edits remain unchanged. Network pin
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d` and consensus pin
`585a86117618ff86d7d5b541f9d23b03356d4c3a` are retained. No native replay, new source
revalidation, Haskell-defect claim or commit was performed. G0–G5, CM-I4c and
SI4/SI5 remain open.

## Sixty-first increment: collected inbound resource origins

**Accepted model result, 5 November 2026; initially uncommitted over `db743c2`,
subsequently committed in `898a02d`.**
[CollectedInboundOrigin](Properties/CollectedInboundOrigin.agda),
`Frontend.initialize-origin`, takes successful initialization, an actual enabled
frontend run and queried CM-collected membership. It derives the physical birth
internally, returning its descriptor/backing and an explicit alternative: automatic
inbound resource history, or the actual enabled outbound birth. No caller-supplied
physical lookup, fork PC, primitive equation or resource certificate is required.
This is per queried worker, not a bijection or uniqueness theorem for collected
list positions.

**Confirmed model evidence:** [InboundBirthLabels](Properties/InboundBirthLabels.agda)
copies the discovered occurrence's original label, prefix/suffix and actual runs.
Its internal `SourceFork` packages the enabled nested operation with exact source
and capture projections through every certified selected wrapper, including
acknowledgement and frontend completion/cache bookkeeping. Raw inbound fork
inversion identifies the queried child and captured descriptor from physical
absence/presence. The proof does not assume canonical/core labels are exhaustive;
no concrete additional enabled label is claimed.

The thin adapter feeds the derived source equation into the existing closed
observer/search and aligns its recovered terminal row with that same birth.
Private consequence helpers in the thin adapter derive historical promise
allocation and stored handler/entry/socket facts from the reconstructed occurrence.
Both existing resource and acceptance modules are byte-for-byte at `db743c2`;
the new helpers do not extend the old resource module namespace. Existing
APIs/statements and runtime guards are unchanged. Birth
inversion remains outside the generic observer/search import closure.
`extend-inbound` copies the same reconstructed packet and descriptor while
appending actual suffixes; `execution` retains the original event list.

**Confirmed acceptance:** `Negative/ServerPeersOrigins.CollectedInboundOriginChecks`
checks canonical/core × empty/nonempty gaps through acknowledgement, publication
and final CM wait. Closed discovery retains its explicit sum and exact descriptor
at all twelve checkpoints. Explicit backing of each same actual fork demonstrates
the positive inbound branch without searching opaque prefixes; it is extended
through the existing opaque lifecycle traces with reconstruction/label/prefix
identity and retained resource facts. The initialized preloaded acquisition is
classified outbound, while its missing resources and uncollected status remain
proved. Premature waits and duplicate receipt/publication controls are retained.
No malformed collected suffix is fabricated.

Four roles worked concurrently; Agda checks stayed sequential. Agda 2.8.0 final
focused checks passed fresh without warnings: `labels-06` (30,007 ms) and
`collected-04` (26,178 ms), using 11 GiB heaps/13 GiB scopes, swap disabled.
The full unchanged suite passed a fresh strict `Cmd_load_no_metas` load
(296,079 ms); the dependent endpoint also passed fresh (36,760 ms).
Both returned exit0, checked:true, DoneExiting and empty goals/warnings/errors.
These final loads used 13 GiB heaps/15 GiB scopes, swap disabled. Ordinary CLI
confirmations were cached successes:
`agda ConnectionManagement/Negative/ServerPeersOrigins.agda +RTS -M13G -RTS`
and the corresponding `ServerPeers.agda` command. Normal cache/default GC;
no interfaces or verification gates were purged.

Earlier attempts exposed an ill-typed homogeneous dependent equality and repeated
12 GiB heap exhaustion. Uniform packets retain all indices and reconstruction;
generic copy laws compose existing equalities. Named child-module abstraction
provides the actual boundary described by [Agda 2.8](https://agda.readthedocs.io/en/v2.8.0/language/abstract-definitions.html#scope-of-abstraction).
All assertion types and old/new coverage are retained. The dependent endpoint
reuses the complete old suite through its validated interface; private helper
placement restores the old dependency namespace exactly. A long incomplete
baseline was interrupted for that isolation, and one diagnostic run hit a disk
quota; neither counts as acceptance. Bounded logging now omits only bulky UI
highlight payloads, retaining diagnostics, status, goals and current ranges.
Exact commands, successful results, all failed/incomplete attempts and their
limits are recorded under `/tmp/cm-collected-origins-20261105/`:
`verification.json`, `baseline-result-04.json`, `acceptance-result-02.json`,
CLI logs, `audit-final.log` and `links-final.log`.

Affected local links and whitespace passed; both existing Mermaid blocks are
unchanged and were not re-rendered. No new holes, axioms or disabled safety checks
were found by the targeted static review; no imported term-level axiom audit was
performed. Existing source pins remain network
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d` and consensus
`585a86117618ff86d7d5b541f9d23b03356d4c3a`. No new pinned networking-source revalidation, native replay,
Haskell-defect claim, presentation edit or commit was performed for this wave.
General outbound resources, global freshness, live ownership, admission/API
quiescence, progress and full shutdown remain open. The overall G0–G5 program,
CM-I4c and SI4/SI5 remain in progress.


## Sixty-second increment: automatic outbound collected resource origins

**Accepted model result, 5 November 2026; initially uncommitted over `898a02d`,
subsequently committed in `8636e88`.**
[CollectedOutboundOrigin](Properties/CollectedOutboundOrigin.agda),
`Frontend.initialize-origin`, takes successful initialization from `O.initial core`,
an actual enabled frontend run and queried `Close.collected` membership. It derives
physical membership and the actual earlier fork internally. The result retains
that descriptor/backing and returns either the existing inbound resource origin
or automatic outbound acquisition history and resource facts. No caller supplies
a physical lookup, fork PC, primitive equation or resource certificate. The
existing arbitrary-initializer inbound API is unchanged; its small appended
`from-inbound-occurrence` wrapper reuses the same private recovery proof.

**Confirmed proof scope:** `O.initial core` is a sufficient, explicit profile,
not a new runtime guard. It clears outbound acquisition/release and returned-result
tables, preserving the supplied core. The generic history engine needs only an
empty initial acquisition store; no empty CM map, entry/promise heap or global
identity-freshness premise is added. Arbitrary preloaded acquisition frames are
not covered by this new outbound conclusion.

[OutboundOriginCore](Properties/OutboundOriginCore.agda) classifies actual active
acquisition writes. Its promise/entry marks follow pre-fork continuations through
counter wrappers. Marks range over **all stored rows**, not merely the visible
lookup, so deleting the first duplicate key cannot silently expose an untracked
row. The noncreator `Backwards` relation composes through permitted peer and
cancellation bookkeeping without creating either mark; an actual acquisition
source step must account for each creator.
[OutboundOriginHistory](Properties/OutboundOriginHistory.agda) then locates the
positive `select nothing` reservation before `newPromise`, retaining matching
requests, entry/promise IDs, primitive source evidence, original outer labels,
enabled gaps and exact event-list decomposition. Its final fork PC is derived
from the selected physical birth, not supplied to the closed API.

[OutboundOriginFrontend](Properties/OutboundOriginFrontend.agda) closes this search
over actual frontend events and proves the initializer projection. Its generic
observer/search closure excludes physical birth inversion.
[OutboundBirthResources](Properties/OutboundBirthResources.agda) derives the queried
child and descriptor from the real physical fork and absent-before capture; the
existing initialized acquisition-capture invariant supplies entry presence.
The thin adapter reuses the increment 55/56 resource-retention lifts. Historical
promise membership is proved at the actual allocating write; it is not a claim
of global promise freshness or current ownership.

`OutboundOrigin` separates an immutable `BirthPacket` from its later suffix.
`extend-outbound` copies that exact packet while appending enabled runs and
retaining fixed-worker/fixed-descriptor facts. `extend-packet` is a uniform copy
law, and `execution` recovers the exact original event list. Neither this API nor
collection establishes uniqueness, a receipt/birth bijection or an eventual exit.

**Confirmed acceptance scope:**
`Negative/ServerPeersOrigins.CollectedOutboundOriginChecks` contains an ordinary
outbound route through acknowledgement, physical publication and final CM wait.
It also contains genuine peer/Server interference and an alternate core-dispatch
IG clock gap, checked as birth/restored-handshake routes. Their independent state
changes do not rejoin the ordinary shutdown suffix; no such suffix is asserted.
Explicit genuine backing exposes each positive outbound branch without forcing
an opaque prefix to normalize. Closed collected discovery retains its full sum
at the ordinary checkpoints, with exact descriptors and same-packet/resource
checks. Premature/duplicate controls remain. The permissive preloaded malformed
fork, missing-resource and uncollected controls are retained; `preloadedExcluded`
separately refutes its membership in any `O.initial core` profile, with the
same-core immediate-fork refusal. No malformed collected suffix is fabricated.

Agda 2.8.0 focused checks passed fresh without warnings, using 11 GiB heaps and
13 GiB scopes with swap disabled. The final logs in
`/tmp/cm-outbound-collected-origins-20261105/` are `core-07`, `history-01`,
`quiet-01`, `peers-01`, `birth-02`, `inbound-bridge-01`, `upper-01`, `frontend-02`
and `collected-01` (all `.log`). Upper checked its effect/lower imports
transitively; its profile total was 11,960 ms, frontend 16,237 ms and the thin
collected endpoint 27,666 ms. Representative command:
`agda --profile=definitions ConnectionManagement/Properties/CollectedOutboundOrigin.agda +RTS -M11G -RTS`.
`b-verification.json` and `audit-b-final.log` retain the focused command/result,
source hashes and six-file zero-finding static scan. This is not an imported
term-level axiom audit.

Fresh full acceptance of `ConnectionManagement/Negative/ServerPeersOrigins.agda`
passed under the strict JSON driver with a 13 GiB RTS heap, 15 GiB scope and swap
disabled, using the normal cache and default GC without an interface purge. The
endpoint emitted its own `Checking` entry and 6,463 declaration entries; exit 0,
`checked: true`, `DoneExiting`, and empty error, warning and goal reports were all
confirmed. The profile total was 39,641 ms (40.354 s elapsed). Evidence is in
`acceptance-03.log` and `acceptance-result-03.json` in the same scratch directory.
A subsequent ordinary CLI check,
`agda ConnectionManagement/Negative/ServerPeersOrigins.agda +RTS -M13G -RTS`,
passed from cache with exit 0 (`acceptance-cli-01.log`); it is not another fresh check.

Two integration diagnostics were repaired before that pass without weakening any
assertion. The first attempt compared an opaque packet's birth-state facts with
the known current state; using its retained-facts projection supplies the original
assertion type. The second reached EOF with an unsolved event implicit in the
restored-packet application; both applications now specify
`V.more {a = childEvent}`. Neither failure involved heap exhaustion or changed
cache/GC settings.

The final targeted proof audit covered all ten new layers, the appended inbound
wrapper and acceptance endpoint: 12 files, zero findings. The old proof bodies
remain exact prefixes; existing resource proofs and `Negative/ServerPeers` are
unchanged. `verification.json` and `audit-final-review.md` retain final hashes,
commands, reviewed dependency boundaries and failed attempts. Affected topic,
README, index, review and state links passed: five pages, 444 local targets,
zero errors or fragment/URI review notes. Whitespace passed; both existing Mermaid
blocks and nine unrelated presentation/output/issue-summary hashes are unchanged.
External URLs were not fetched and unchanged diagrams were not re-rendered.

The [source ledger](SourceLedger.md) retains network pin
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d` and consensus pin
`585a86117618ff86d7d5b541f9d23b03356d4c3a`. These are model proofs, not a new
pinned-source audit, native replay, Haskell-defect or implementation-refinement
claim. Remaining mux/TIME_WAIT/already-finished shutdown routes, CM-I4c tracked
validity, admission/API quiescence, SI4/SI5 completion and G0–G5 remain open.


## Sixty-third increment: initialized finished-target acknowledgement

**Accepted model result, 5 November 2026; uncommitted over `8636e88`.**
The actual initialized outbound path captures a live worker at CM `readEntry`,
then holds the coordinator at `sendReady` while an **independent handshake
cancellation** runs through caught-error publication, rethrow, outer finalizer,
real cleanup and physical Async-result publication. CM only then requests
cancellation, takes the guarded `acknowledgeFinished` branch, completes traversal
and performs its collective result wait. The independent delivery is neither
this CM receipt nor normal handler return.

[ServerPeersFinishedReceipt](Properties/ServerPeersFinishedReceipt.agda) is a small
observer of the actual physical acknowledgement. `Receipt` retains the awaited
entry/worker, real enabled step, ready result branch and coordinator control
certificate; collection appends that worker. The result branch distinguishes a
mux exit frame from the physical handshake fallback, including its no-mux-frame
guard. This local observer alone supplies no initialized history or final wait.

The appended [CollectedOutboundOrigin](Properties/CollectedOutboundOrigin.agda)
`Frontend.initialize-finished` takes successful `O.initial core` initialization,
the original enabled prefix and the actual acknowledgement. It derives the
worker and collection membership internally, then returns `FinishedDiscovery`
with the existing full inbound/outbound resource sum for exactly
`prefix ++ [acknowledgement]`. No caller supplies a worker, membership, physical
lookup, fork PC or result/resource oracle. The existing APIs and runtime guards
are unchanged.

`Negative/ServerPeersOrigins.FinishedTargetChecks` retains the same increment-62
immutable resource packet and increment-58 physical birth command through the
new receipt and final wait. Descriptor equalities, retained resources, exact
execution and the physical pre-wait result oracle are checked separately. Its
companion late-read path holds the captured snapshot in `reading` while the
same independent completion runs: `getConnThread` then skips the terminated
entry and collects nothing. Refusals cover acknowledgement before request or
Async publication, cleanup-only readiness, direct raw receipt, premature and
duplicate publication/receipt/wait. No phase or result is injected.

**Confirmed source boundary.** The
[dated addendum](../review/connection-management-si4-source-audit-2026-10-27.md#increment-63-captured-before-completion-versus-late-read-5-november-2026)
records the pinned Core/traversal/wait source and separately versioned backend
inspection. `resultReady` means **Async result available**, not a literal
scheduler `ThreadFinished` observation. Masking the sender does not freeze the
target or guarantee prompt receipt. Source pins are unchanged; no GHC RTS
dead-target audit or new native replay was performed.

Focused Agda 2.8.0 checks passed fresh without warnings: `receipt-04.log`
(19,916 ms), the exact trace harness `trace-01.log` (42,053 ms) and appended
collected API `collected-02.log` (28,007 ms), under the coordinator's serialized
queue. Earlier receipt parse/with-abstraction diagnostics
and a constructor-shadow warning were repaired before the final focused check.
The first collected-API attempt found a missing `[]` import, repaired before
its focused pass.

Fresh full strict interaction acceptance of
`ConnectionManagement/Negative/ServerPeersOrigins.agda` passed on its first
attempt: own `Checking` entry, 9,748 typechecking entries, exit 0, `checked: true`,
`DoneExiting`, and empty error, goal and warning reports. The profile total was
40,973 ms (41.965 s elapsed), with a 13 GiB RTS heap, 15 GiB scope and swap
disabled; normal cache/default GC, no interface purge. `acceptance-01.log` and
`acceptance-result-01.json` retain that fresh result. The subsequent ordinary CLI
`agda ConnectionManagement/Negative/ServerPeersOrigins.agda +RTS -M13G -RTS`
passed from cache, exit 0 (`acceptance-cli-01.log`); this is not another fresh
check. The three-file targeted scan found no new holes, postulates or unsafe
pragmas; an imported term-level axiom audit was not performed. Evidence, focused logs,
pinned source excerpts and package/blob hashes are in
`/tmp/cm-finished-target-20261105/`.

Final local checks covered five affected pages and 482 local targets, with zero
errors or fragment/URI review notes. Whitespace passed; both Mermaid blocks and
nine unrelated presentation/output/issue-summary hashes are unchanged. External
URLs were not fetched and unchanged diagrams were not re-rendered. Exact commands,
final source hashes, audits and check identities are retained in
`/tmp/cm-finished-target-20261105/verification.json`.

This finite independently cancelled path proves no normal-return route, whole
thread census, API/admission quiescence, eventual completion, RTS correspondence
or implementation refinement. Remaining mux/TIME_WAIT routes, CM-I4c validity,
SI4/SI5 and G0–G5 obligations remain separate.

## Sixty-fourth increment: outbound negotiated-mux receipt and final wait

**Accepted model result, 6 November 2026; uncommitted over `8dd2452`.
Fresh full affected acceptance passed.** Increment 63 is now committed in that
revision; its earlier uncommitted label above preserves its acceptance checkpoint.
This increment extends the initialized outbound route to negotiated mux execution.
The existing inbound mux route remains a separate accepted witness.

[ServerPeersMuxEmbedding](Properties/ServerPeersMuxEmbedding.agda) lifts actual
physical transitions through the combined wrappers, keeping each permission
explicit. [ServerPeersMuxReceipt](Properties/ServerPeersMuxReceipt.agda) observes
the actual coupled `deliverShutdownMux`: owner interruption and acknowledgement
derive the captured entry/worker and appended collection membership. The appended
[CollectedOutboundOrigin](Properties/CollectedOutboundOrigin.agda)
`Frontend.initialize-mux` takes genuine `O.initial core` initialization, the actual
enabled prefix and receipt. It derives the worker and resource/birth discovery
internally; it does not take a supplied physical lookup or resource certificate.

**Profile correction.** The reused `Negative/MuxProtocolFixtures.F.start` contains
unrelated admissions and sockets 0/1, so the genuine outer initializer rejects
that raw fixture. The supported core input removes those unused rows before
initialization while retaining the actual outbound socket 10. Every affected
physical/combined transition has a freshly checked guarded equation, reusing component
operation order and data rather than applying old transition proofs after erasure.
The raw component initializer remains valid at its own layer; the unchanged
outer initializer's refusal is retained as a negative control. This corrects the
initial inspection's mistaken empty-table assumption, without changing the
initializer or runtime permissions.

The accepted `Negative/ServerPeersOrigins.OutboundMuxChecks` executes the real
outbound acquisition and physical fork, governor handoff, negotiation, handle
publication and mux startup. Legacy selector bookkeeping retains its real
frontend owner row. Canonical CM operations require Server `closingCM`, so the
prefix first closes the empty peer pools and four lexical scopes, returns the
Server action, closes the listener, and runs the genuine nonempty IG exit before
entering CM. It never adopts a closing-stage snapshot. `IG.finishBatch` reaches
the actual loop cancellation boundary. Deactivation, queue flush and final
transition callbacks preserve the published registration and CM entry.

CM capture/read/request then precede coupled delivery while the mini-protocol
group's graceful cancellation is in progress. That interruption abandons its
cursor and graceful drain/`TraceStopped` continuation. The actual whole-pool
bracket close still runs; the async mux catch writes `Failed`, traces `Dead` and
rethrows the original async error. Because IG has exited, its inactive callback
skips the queue/counter transaction: the existing `(+1, 0)` counters remain and
no new `MuxFinished` message is queued. These are stored historical counters,
not evidence of live responders.

The milestone contract retains the same immutable outbound resource packet and
birth command through actual buffer return, finalizer/cleanup, Async publication
and the exact final pre-wait oracle. CM-entry and result-wait component
certificates `cmEntry` and `cmResultWait` are derived from the real outer steps.
Receipt, pool close and cleanup alone cannot satisfy the result wait. Controls cover premature and
duplicate receipt/publication/wait, framed raw-handshake bypasses, raw coordinator
acknowledgement and canonical CM operations before scope closure. Generic
standalone `G.abortOwner` may remain enabled; it leaves CM acknowledgement and
collection unchanged.

**Confirmed source finding.** The
[increment 64 audit](../review/connection-management-si4-source-audit-2026-10-27.md#increment-64-outbound-mux-receipt-and-inactive-ig-6-november-2026)
records exact pinned operations and the separate backend contract. No new native
replay, GHC RTS audit, imported term-level axiom audit, implementation refinement,
admission/API quiescence, universal progress or whole-shutdown claim is made.

Agda 2.8.0 checks stayed sequential. Fresh focused passes without warnings were
`embedding-02` (10,064 ms), `mux-receipt-01` (22,549 ms), `collected-mux-01`
(29,850 ms), the cleaned physical suffix `exited-suffix-03` (12,298 ms),
`combined-prefix-05` (39,040 ms), `scope-close-01` (39,493 ms) and
`combined-suffix-01` (48,077 ms), all `.log` files in
`/tmp/cm-outbound-mux-20261106/`. They check the selected component operations
before their opaque histories are reused in the integrated endpoint.

The restored strict interaction driver first passed a fresh receipt smoke check
(`strict-smoke-result-03.json`, 19,255 ms), after backing up and invalidating only
that endpoint's interface. Earlier cached smoke results were not accepted as
fresh; one cross-filesystem rename attempt failed during preparation before the
successful copy/unlink. The normal cache and default GC were otherwise retained.

Fresh full strict interaction acceptance of
`ConnectionManagement/Negative/ServerPeersOrigins.agda` passed on its first
integrated check: own `Checking` entry, exit 0, `checked: true`, `DoneExiting`,
empty visible/invisible goals, warnings and errors, and unchanged checked source.
The profile total was 76,232 ms (78.364 s elapsed), with a 13 GiB RTS heap,
15 GiB scope and swap disabled. `full-strict-01.log` and
`full-strict-result-01.json` retain that evidence. The integration's implicit
`actions` argument was made explicit before this check; earlier import/fixture
diagnostics were repaired without weakening assertions or changing runtime rules.
The ordinary CLI confirmation,
`agda ConnectionManagement/Negative/ServerPeersOrigins.agda +RTS -M13G -RTS`,
passed from cache with exit 0 and no warnings (`final-cli.log`); it is not a
second fresh check.
The final targeted four-file proof scan has zero findings; old proof bodies
remain exact prefixes. This is not an imported term-level axiom audit.

At that acceptance checkpoint, the next task was the
[candidate increment 65 TIME_WAIT audit](#next-batch-time_wait-receipt-and-finalizer-route-candidate-increment-65):
find genuine initialized `Terminating` → `cleanupWaiting` execution before
implementing expiry/interruption coverage. Increment 65 had not started at that
checkpoint; its later status is recorded below. SI4/SI5, CM-I4c and G0–G5 remain open.


## Sixty-fifth increment: initialized TIME_WAIT receipt and finalizer routes

**Accepted, 6 November 2026; uncommitted over `eef9971`.**
Increment 64 was committed in that revision; its earlier uncommitted label below
its dated heading records the original acceptance checkpoint.

[ServerPeersTimeWaitReceipt](Properties/ServerPeersTimeWaitReceipt.agda) inverts
an actual guarded TIME_WAIT delivery to observe its awaited entry/worker,
waiting cleanup, original body result, actual interruption and acknowledgement.
Collection membership follows from that acknowledgement. The appended
[CollectedOutboundOrigin](Properties/CollectedOutboundOrigin.agda)
`Frontend.initialize-timewait` takes successful original initialization, the
actual prefix and that receipt event; it derives the worker and origin discovery
internally, without a supplied lookup, membership, PC or resource certificate.
These generic helpers do not establish the integrated witness by themselves.

**Confirmed source contract.** The [pinned audit](../review/connection-management-si4-source-audit-2026-10-27.md#increment-65-time_wait-entry-and-finalizer-audit-6-november-2026)
identifies an existing route rather than a new runtime branch. From the accepted
outbound mux prefix, actual IG idle expiry invokes inbound release, changing
outbound duplex `Ticking` to `Expired` and publishing `RemoteCold`. Actual outbound
release then writes `OutboundIdle`; its own timer selection and separate timeout
write produce `Terminating`. These are distinct timers and transactions.

The reused startup has also queued `AwakeRemote` and `RemotePromotedToHot`.
Those events remain after the idle-release decision; `finishBatch` cannot erase
them. The checked interleaving writes `Terminating` first, then consumes the
actual tail. The CM promote call returns unsupported without changing that
entry, but IG still publishes `RemoteWarm` and then `RemoteHot`. That published
remote state is historical information, not evidence of a live or Hot CM entry.

The initialized witness retains the pending release caller after its
timeout write and counter read, before its cancellation request. Actual
peer/Server/nonempty-IG closure precedes an independent physical mux interruption,
whole-pool close, body exit and genuine finalizer entry. That interruption is
neither a completed outbound release call nor that caller's cancellation
acknowledgement. Real cleanup reads the terminating entry, closes the captured
socket and republishes the map; only then does it enter `cleanupWaiting`, still
retaining the entry and binding. Canonical CM operations follow those real steps.

The two suffixes share that initialized birth and resource packet. The
interrupted route takes actual CM capture/read/request and coupled
`deliverShutdownTimeWait`; receipt derives collection membership but leaves the
entry and map untouched until the separate `finishTimeWait` transaction. The
elapsed route records untimed readiness, finally, counters and physical result
publication before the finished-target acknowledgement. In both cases the CM
target is captured before termination; a late terminated-entry read is different.
Cleanup completion, receipt and physical Async publication remain separate from
the final collective wait. Wrong-phase, premature, duplicate and raw-bypass
controls passed. Standalone TIME_WAIT interruption remains enabled but leaves
CM awaited and uncollected.

Diagnostic tracers and observed socket/provider returns retain their existing
contracts. In particular, the source calls the TIME_WAIT-done tracer before its
finally STM. Neither this source audit nor the checked finite traces establish
backend masking equivalence, a measured timeout, eventual delivery, completed
release/API quiescence, full shutdown or G0–G5 completion.


`Negative/ServerPeersOrigins.TimeWaitChecks` reuses the opaque
`OutboundMuxChecks.BirthPackets` birth. Named `Retention`, `Histories` and `Glue`
modules preserve the same immutable packet, exact fork command and actual
scope-equality transports without unfolding the earlier histories. `cmEntry`
uses the genuine callback return and `beginCM`; `interruptedCMWait` and
`elapsedCMWait` reuse the existing result-wait certificates. Both physical
publication/wait certificates and pre-wait result oracles are derived from the
actual enabled events. Elapsed cleanup retains body exception 77; CM interruption
records cleanup exception 99, which supersedes it at physical publication.

Agda 2.8.0 checks stayed sequential. Fresh focused passes without warnings:
receipt01 21,074 ms (4 GiB heap/5 GiB scope); collected02 28,406 ms; prefix03
50,789 ms; scope01 56,751 ms; waiting01 71,701 ms; suffix01 46,301 ms
(the latter five used 11 GiB heap/13 GiB scope). Root integration focus04 passed
fresh in 58,931 ms at 13 GiB heap/15 GiB scope. All scopes disabled swap.
Exact commands, source hashes and focused evidence are in
`/tmp/cm-timewait-20261106/`, including `A-checks.json` and `B-verification.json`.

Fresh full strict interaction acceptance of
`ConnectionManagement/Negative/ServerPeersOrigins.agda` passed in
`full-strict-05.log`/`full-strict-result-05.json`: own `Checking` entry, exit 0,
`checked: true`, `DoneExiting`, empty visible/invisible goals, warnings and errors,
and unchanged source. Profile total 145,408 ms, elapsed 149.258 s, 20 GiB RTS heap,
25 GiB scope, swap disabled. Ordinary CLI confirmation,
`agda ConnectionManagement/Negative/ServerPeersOrigins.agda +RTS -M20G -RTS`,
passed cached with exit 0 and no warnings; it is not another fresh check.

The initial prefix check exposed the real queued awake/hot tail and freshly
rechecked the unchanged predecessor; that prefix attempt was not accepted.
Earlier 4/11/13 GiB heap exhaustion, two aggregate namespace collisions and
interrupted diagnostic/performance attempts supplied no acceptance. Flat
snapshots, narrow module imports, named proof boundaries and checked equality
transports repaired elaboration while preserving all actual step equations and
original theorem statements. The installed non-debug build could not emit the
requested declaration-level diagnostics. A bounded 20/25 GiB aggregate attempt
was stopped before the accepted run; no result was inferred from its progress.
The strict driver was reused from its prior validated copy; no new smoke test or
interface invalidation was performed. Normal cache/default GC were retained;
only exact predecessor bytes were temporarily restored for focused imports,
then the full new source was reassembled and freshly accepted. Detailed failed
and interrupted attempts remain in the verification evidence.

Source inspection used local pinned Git objects. The local-link checker did not
fetch external URLs; a separate performance review consulted official Agda
[abstraction rules](https://agda.readthedocs.io/en/v2.8.0/language/abstract-definitions.html#scope-of-abstraction).
The final targeted scan of three maintained proof files has zero findings;
it is not an imported term-level axiom audit. No native replay, backend/RTS
audit, presentation refresh or commit was performed. The next planned
[candidate increment 66](#next-batch-framed-mux-outbound-release-receipt-and-return-candidate-increment-66)
addresses genuine framed-mux release receipt/return. SI4/SI5, CM-I4c and G0–G5
remain open.


## Sixty-sixth increment: framed-mux outbound release receipt and return

**Accepted, 6 November 2026; committed in `daf111d`.** Increment 65 is
committed in `a54d4fd`. The broader CM/IG/OG/Server objective remains open.

**Confirmed source contract.** The
[pinned release audit](../review/connection-management-si4-source-audit-2026-10-27.md#increment-66-outbound-release-receipt-audit-6-november-2026)
confirms that consensus `585a86117618ff86d7d5b541f9d23b03356d4c3a` selects network
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`, explicitly identified as the
`leios-prototype` merge. `Core.hs:2021–2037` retains the original handler Async,
writes `Terminating`, traces and reads counters, then sends `AsyncCancelled`
before returning the captured success value. The ordinary release function has
no local mask/unmask and inherits ambient caller masking; it is distinct from
CM's explicitly uninterruptible finalizer.

`MuxHandlerExit.deliverReleaseMux caller err` derives its target exclusively from
the caller's actual `Release.delivering` frame, performs the real mux owner abort
and executes the real source `cancellationDelivered` acknowledgement.
`acknowledgeReleaseFinished caller` requires genuine physical result availability
before executing that same source operation. Both retain `O.advance` and its
`mayDeliver`/`noteDelivery` behavior. Raw delivery remains refused; caller return,
handler publication and CM acknowledgement are separate operations. Server
wrappers preserve admission-role restrictions and governor-owned caller guards.

The generic
[release receipt properties](Properties/ServerPeersReleaseReceipt.agda) derive
`CapturedTarget`, `LiveReceipt` and `FinishedReceipt` by inverting actual enabled
steps. Their fields retain the stored frame, real target operation and real
source acknowledgement; frontend projections also derive caller permission.
`live-shutdown`/`finished-shutdown` preserve the CM coordinator and collection.
[Monitor joins](Properties/ServerPeersMonitorJoins.agda)'s `frameRelease` carries
genuine canonical core release labels through the existing context-preservation
proof. The previous inherited-server/framed predicates remain unchanged.

`Negative/ServerPeersOrigins.ReleaseMuxChecks` reuses the accepted opaque birth
and TIME_WAIT prefixes. Its `Live.actual` executes request → coupled mux receipt
→ separate `returnResult` before pool close, handler cleanup or Async publication,
then follows the real suffix to CM wait. `Finished.actual` starts from genuinely
published handler completion after entry termination/map purge, executes request
→ finished-target acknowledgement → return, and retains the earlier captured
`success(Terminating)` value. A new map lookup cannot retarget either send or
rewrite that reply. This establishes completion of the modeled release API call,
not physical exit of the caller's worker, Async or governor job.

`Histories` and `Retention` preserve the same original fork/resource packet
through live receipt, caller return and final CM wait, and through the finished
branch. `ScopeCertificates.liveCMWait`, `liveComponents` and `finishedComponents`
reuse actual guarded wait/closed-component evidence. `ReceiptObservations`
derives both typed receipt records, outer permissions and unchanged coordinator
from those actual frontend events; these are not supplied receipt assumptions.

Premature, duplicate, missing-caller, inappropriate-window and raw-bypass controls
pass. An independent owner abort leaves the caller pending and return refused.
The wrong-target altered-frame fixture and owned-unwinding-caller context checks
are local guard controls, not initialized reachable interference witnesses.
Receipt alone supplies no future physical result. Result availability remains a
supported modeled observation, not literal RTS `ThreadFinished` or a guarantee
of instantaneous/universal throwTo return.

Focused Agda 2.8.0 checks passed sequentially. Clean fresh runtime/exit-property
profiles were 8,599/14,166 ms; birth-effect checking included a 469,681 ms
transitive rebuild. Fresh root checks covered both origin lowerings, collected
backing, joins (947.754 s) and generic receipts (25.749 s). Auxiliary backing's
original terminal output was lost; its separate cached confirmation passed with
exit 0 in 19.964 s. The complete scratch acceptance passed fresh in 50.345 s,
exit 0 without warnings, at 13 GiB heap/15 GiB scope/swap disabled, with a host
memory guard; its maximum RSS was 6.50 GiB. Exact commands and hashes are in
`/tmp/cm-release-mux-20261106/`, including `A-checks.json`, `B-final-handoff.md`
and `acceptance-08.json`.

Fresh strict interaction acceptance of
`ConnectionManagement/Negative/ServerPeersOrigins.agda` passed in
`full-strict.json`/`full-strict.log`: `agda --interaction-json
--profile=definitions --interaction-exit-on-error +RTS -M20G -RTS`, using
`Cmd_load_no_metas`, `Cmd_metas AsIs` and normal exit. It recorded the endpoint's
own `Checking`, exit 0, `checked: true`, `DoneExiting`, empty visible/invisible
goals, warnings and errors, and unchanged source hash `4c5284d90d22145b…`.
Elapsed time was 130.423 s (profile 126,085 ms), with a 20 GiB heap/25 GiB scope,
swap disabled and normal host-memory guard completion.

Ordinary CLI confirmation, `agda
ConnectionManagement/Negative/ServerPeersOrigins.agda +RTS -M11G -RTS`, passed
cached with exit 0 and no warnings in 40.881 s at 11 GiB heap/13 GiB scope,
swap disabled (`final-cli.json`/`final-cli.log`). This confirms the same unchanged
source; it is not another fresh check.

Earlier lexical errors, a constructor-shadowing warning, one generic equality
error and resource-limited aggregate attempts supplied no acceptance. Proof-only repairs removed expensive
concrete aliases, made transport endpoints explicit and reused generic
trace-edge/frame/observation adapters. All original statement types, actual
state/event/guard definitions and the 48 original trace edges are preserved;
the previous accepted endpoint prefix is byte-identical. Failed/interrupted
attempts and independent transformation reviews remain in the evidence directory.
No theorem was weakened to fit the memory bound. The targeted static scan of
12 maintained proof files found zero issues; it is not an imported term-level
axiom audit.

Live framed-mux and available-result routes do not cover release interruption
at cleanup TIME_WAIT, buffer-provider continuations, classifier tracing or a
blocked node-directed send. Those are model coverage gaps, not automatically
Haskell defects. Diagnostic tracer/provider contracts remain explicit. Global
API/admission quiescence, source refinement, universal progress, SI4/SI5,
CM-I4c and G0–G5 remain open. No native replay, backend/RTS or imported term-level
axiom audit, presentation refresh or commit was performed. Per the user's newer
steering, no next proof wave starts; the next task is the
[source-baseline audit](#next-task-source-baseline-audit).

## Sixty-seventh increment: release-caller delivery at TIME_WAIT

**10 November 2026, at source pin network `2f1c154`.** Increment 66 left release
interruption at cleanup TIME_WAIT as a coverage gap. A release caller delivers
with `throwTo` (`Core.hs` 2032 for the outbound timeout, 1254 for inbound
release). The handler's cleanup runs its TIME_WAIT delay under
`unmask (threadDelay timeWaitTimeout)` (`Core.hs` 667–668), the only
interruptible point in cleanup.

`MuxHandlerExit.deliverReleaseTimeWait caller err` takes its target only from
the caller's own `Release.delivering` frame (`releaseTarget`). The step is enabled
only when that handler is finalizing, holds its current capture and its cleanup
is `cleanupWaiting` (`timeWaitTarget`). One step executes the real
`Cleanup.interruptTimeWait err` source step for the target. It then executes the
real `Release.cancellationDelivered` acknowledgement for the caller and records
the cleanup in the handler's exit frame. It does not publish a handler result,
acknowledge CM shutdown or return the caller. `ServerAdmission` keeps the
governor-owned caller guard (`releaseReceiptCaller`). The proof cascade
(exit projections, auxiliary and collected backing, birth effects and both origin
lowerings) is extended without changing any statement.

[ServerPeersReleaseTimeWait](Properties/ServerPeersReleaseTimeWait.agda) inverts
an actual step. `waiting-observation` derives the captured target, its frame,
finalizing phase, current capture and `cleanupWaiting` entry. `timewait-observation`
derives the two actual source steps and the exact successor. `timewait-shutdown`
shows the CM coordinator is unchanged. The `Frontend` module lowers the runtime
event to that physical receipt and derives the outer caller permission.

[Negative/ServerPeersReleaseTimeWait](Negative/ServerPeersReleaseTimeWait.agda)
starts from the accepted TIME_WAIT branch point (`TimeWaitChecks.Suffix.branchpoint`)
and gives the caller the frame of increment 66 (`ReleaseMuxChecks.reframe`). Its
`actual` run executes eleven events: the caller's request, the delivery, the
caller's return, `finishTimeWait`, the counter read, `finishCleanup` and
publication, then CM request, finished acknowledgement, traversal and final
wait. The core caller calls use their real guarded step. Each handler edge is
lifted through `endpoint-up` with all six permissions discharged on its states.
`initialized` extends the accepted retention certificate (`TimeWaitChecks.retain`
from `TimeWaitChecks.branch`), so the original outbound birth packet and backing
are retained to the final CM wait. Receipt facts come from the actual step.
Before the caller returns there is no result and no released value; afterwards
the caller has its captured result. Controls refuse delivery before the
request, a duplicate, an unknown caller, masked cleanup before TIME_WAIT, a
stale capture, delivery after CM shutdown has already interrupted TIME_WAIT,
substituting the finished-target acknowledgement, raw core delivery and
return before delivery.

**Checking cost and module copies.** A first version of this witness exhausted
a 20 GB heap when lifting the edges. The cause was module aliases: `module R =
ReleaseMuxChecks` is a module copy, and `R.up`'s type names the original
`ReleaseMuxChecks.W.step`. A proof typed with the copy `R.W.step` (or with a
locally applied `Exit RF.bearerClosed`) is definitionally equal but not
syntactically equal. Agda therefore evaluates both concrete steps in full to
compare them. Bisection isolated this: the same application typed with the
original name checks in 48 s at an 8 GB cap. The witness therefore opens the
endpoint's names instead of aliasing them, and composes edges with the
endpoint's own `trace-edge`.

**Validation.** All checks ran sequentially under Agda 2.8.0 with a 20 GB heap,
a 25 GB scope and swap disabled. The witness module checked fresh in 47.9 s
(peak RSS 6.5 GB). Every top module of the 123-module affected set passed with exit 0:
the 18 `Negative/Mux*`, PoolRelays, ServerAdmissionInvariants and ServerIGExit
fixtures, and `Properties/MuxInitiatorTrace`. Fresh strict interaction acceptance of
`Negative/ServerPeersOrigins.agda` passed in 154.8 s (10.9 GB). It recorded the
endpoint's own `Checking` line, exit 0, `DoneExiting`, empty goals, warnings and
errors, and an unchanged source hash. A cached CLI confirmation passed in 45 s.
The endpoint source is unchanged by this increment. No postulate, hole or
termination pragma was added. Evidence: `/tmp/cm-inc67-20261110/accept/`.

CM-I4c, SI4/SI5, admission/API quiescence, source refinement and G3–G5 remain open.

## Sixty-eighth increment: external Server interruption

Checked 10 November 2026. This is SI4 increment 2 of the
[source-coverage audit](SourceLedger.md#si4-source-coverage-audit-10-november-2026).
On ordinary node shutdown, the thread running `Server.with` receives
`AsyncCancelled` while it waits in its race (network `2f1c154`, `Server.hs`
165–175; `Diffusion.hs` 281–296). The race cancels the accept loops, the
listener closes and `TrServerStopped` is traced. Only then does `withAsync`
cancel the action thread. Until that point the peer side (governor, churn,
providers and PSA) is fully live and can still start CM calls. The peer side
then unwinds by cancellation, the action thread is joined, and the IG and CM
scopes unwind as before.

Model changes:

- [ServerAdmission](ServerAdmission.agda) adds the scope action
  `interruptServer`, from `serving` to `closingAccept`, without an action exit.
  The rest of the scope chain is reused.
- In [ServerPeers](ServerPeers.agda), `peerOpen` also holds in the stages from
  `closingAccept` to `serverStopped` while the peer side has not closed, and
  `cancelJoinReturnedAction` requires `peerClosed`. On the returned-action path
  the peer side is closed before `returnAction`, so that path is unchanged.
  Peer-side unwinding remains the abstract `AsyncScope.beginUnwind`; on this path
  its cause is the delivered cancellation.

Checks: the 74 modules affected by the model change pass with no proof change,
through the five top-level modules `Properties/FrontendPhaseCleanup`,
`Negative/ServerAdmissionInvariants`, `Negative/ServerIGExit`,
`Negative/PoolRelays` and `Negative/ServerPeersReleaseTimeWait` (exit 0).

Fresh acceptance passed: a strict interaction-mode load of the endpoint
`Negative/ServerPeersOrigins` after removing its interface reported checked,
fresh checking, no goals, warnings or errors, and an unchanged source hash
(207 s, 11.2 GB). `Negative/PoolRelays` (73 s), a cached endpoint
confirmation (51 s) and `Negative/ServerPeersReleaseTimeWait` (51 s) passed.
Evidence is in the session scratchpad `si4b/`.

`Negative/ServerPeers.Interleaving` adds an initialized witness,
`initialized-interrupt`. It follows the existing path to step 55, where the peer
scopes have finished but the PSA monitor pool is open. It then interrupts the
Server, closes the accept loop and the listener, and traces the stop. The
monitor pool closes after that, and the action thread is joined last. The
supply invariant holds at the end (`interrupt-supply`).

Controls:

- `no-join-before-peer-close`: the action thread cannot be joined while the peer
  side is open.
- `no-return-after-interrupt`: the action cannot return after an interruption.
- `no-second-interrupt`: the Server can be interrupted only once.
- `peer-live-after-stop` and `peer-shut-after-close`: the peer side stays open
  after the stop until it closes.

The witness interrupts after the peer scopes have already unwound by their own
failure. It does not cover a full peer-side unwind started by the interruption,
or new CM calls between the interruption and the action cancellation, although
the model now allows both. The IG thread and an accept loop as race winners
remain open, as do SI5, admission/API quiescence, source refinement and G3–G5.

## Sixty-ninth increment: the inbound governor fails first

Checked 10 November 2026. This is SI4 increment 3 of the
[source-coverage audit](SourceLedger.md#si4-source-coverage-audit-10-november-2026),
modelled faithfully at the user's request rather than excluded.

At network `2f1c154` the IG thread runs `forever step` under a `catch`
(`InboundGovernor.hs` 194–235). If the step raises, the catch runs on the IG
thread while the Server still serves:

1. It deactivates the IG.
2. It drains the information channel.
3. It traces every remote state to `Nothing`.
4. It rethrows.

`waitEither` in `Server.with` then returns the failed IG thread
(`Server.hs` 165–175), and the race closes the accept loops. `withAsync`
cancels and joins the action thread. In node-to-node mode the action thread's
own `waitAny` also observes the IG failure and starts the peer-side unwind.
Finally the IG `withAsync` cancels the finished thread, which is a no-op, and
reads its result.

Model change:

- [ServerAdmission](ServerAdmission.agda) separates the IG thread's phase
  (`IGPhase`: live, caught, inactive, flushed, body exited, result available)
  from the Server thread's stage. The IG stages `igCancelDelivered` to
  `igResultAvailable` are no longer Server stages.
  - `deliverIGBody`, `deactivateIG`, `flushIG`, `finishIGBody` and
    `publishIGResult` are gated by the IG phase.
  - `deliverIGBody` still requires the Server's cancellation request.
  - The new `failIGBody` enters the catch at any Server stage while the IG is
    live.
  - The new `igWins` moves from `serving`, `actionBodyExited` or
    `actionResultAvailable` to `closingAccept` once the IG result is available.
  - `joinIG` requires the Server's cancellation request and the IG result.
  - `cancelPathIG` gives the IG phase at each stage of the cancellation path
    outside the catch. Fixtures use it to state that path's existing points.
- [ServerIGExit](ServerIGExit.agda) adds `fail`, an own-failure receipt with a
  synchronous or asynchronous fault, at the existing receipt sites. It opens
  only while the IG is live, independent of the Server stage. The new plan
  `ownFailure` clears the pending CM call frames like `abandon` and records the
  fault. The snapshot and finish steps check the IG phase instead of the stage.

The existing paths keep their meaning. Their fixtures now state the IG catch as
the Server waiting at `igCancelRequested` while the IG phase advances. Re-expressed:

- `Negative/ServerAdmission`, `ServerAdmissionPrefixFixtures`,
  `ServerIGExitFixtures`, `ServerIGExitControls`, `ServerIGExitCasesFixtures`
  and `ServerIGExitProtocolFixtures`.
- `Negative/ServerPeers`: new `sceneIG`, `stageSceneIG` and
  `outbound-owned-atIG` helpers.
- `Negative/ServerPeersOrigins`: `scopeAtIG`, through `embedIG` in
  `Properties/ServerPeersMuxEmbedding`.

The proof modules that match on IG-exit plans gain an `ownFailure` case that
mirrors `abandon`. `Properties/ServerAdmission`'s lift lemmas carry the IG
phase. `Properties/ServerPeersMonitorJoins` drops the removed stages from an
exhaustive case analysis.

Checks: the six top-level modules covering the 75 affected modules pass
(`Properties/FrontendPhaseCleanup`, `Negative/ServerAdmissionInvariants`,
`Negative/ServerIGExit`, `Negative/ServerIGFirst`, `Negative/PoolRelays`;
`Negative/ServerPeers` passed separately in 678 s, 12.5 GB). Fresh acceptance
passed: a strict interaction-mode load of the changed endpoint
`Negative/ServerPeersOrigins`, after removing its interface, reported checked,
fresh checking, no goals, warnings or errors, and an unchanged source hash
(204 s, 11.9 GB). A cached confirmation (51 s) and
`Negative/ServerPeersReleaseTimeWait` (53 s) passed. Evidence is in the session
scratchpad `si4b/`.

The new witness, [Negative/ServerIGFirst](Negative/ServerIGFirst.agda),
continues the initialized IG-exit prefix. With the Server serving, the IG fails
synchronously at its loop boundary and runs its whole catch: deactivate, flush,
final trace and result. `igWins` then closes the accept loop, the Server stops
and joins the action, requests the IG cancellation, joins the finished IG at
once and enters CM close. The supply invariant holds at the end. A handler
step succeeds during the catch.

Controls:

- `igWins` is refused while the IG is live.
- The catch is entered once.
- The IG loop does not resume after the catch.
- The IG join waits for the IG result.

The witness is at the Server/IG-exit layer, without the peer side. In the
composed runtime the action join additionally requires the peer side to be
closed (increment 68). An own-failure receipt uses the existing receipt sites;
a synchronous exception's exact origin inside the step is not modelled. An
accept loop as race winner, SI5, admission/API quiescence, source refinement
and G3–G5 remain open.

## Seventieth increment: the accept loop fails first

Checked 10 November 2026. This is SI4 increment 4 of the
[source-coverage audit](SourceLedger.md#si4-source-coverage-audit-10-november-2026).
At network `2f1c154` (`Server.hs` 147–249) the accept loop raises in two ways:

- on an `AcceptFailure` other than `ECONNABORTED` ("fatal for the whole
  process"), for example `EMFILE`;
- when `getLocalAddr` or a trace fails after a successful accept. The accepted
  socket is closed first, before any handoff.

Its `finally` then closes the listener and `raceAll`'s `waitAny` rethrows. The
race cancels the waiter, and the Server stops while the action thread is still
running. `withAsync` then cancels and joins the action thread, and the IG and CM
scopes unwind as before.

Model change: [ServerAdmission](ServerAdmission.agda) adds the stage
`acceptFailed` and the scope action `acceptFails`. It is enabled from `serving`,
`actionBodyExited`, `actionResultAvailable`, `closingAccept` and
`acceptCancelRequested`, that is, until the race's cancellation reaches the
loop. `closeListener` (the loop's `finally`) is also enabled from
`acceptFailed`, and the rest of the chain is reused. In
[ServerPeers](ServerPeers.agda), `peerOpen` also holds in `acceptFailed` while
the peer side has not closed. `acceptFailed` admits no new accepted connection.
The accepted socket of the `getLocalAddr` case never enters the model's socket
table, so both triggers are the same step.

Checks: the cascade over all modules affected by the change passes. Its
top-level modules are `Negative/ServerPeers` (1666 s, 13.9 GB),
`Properties/FrontendPhaseCleanup`, `Negative/ServerAdmissionInvariants`,
`Negative/ServerIGExit`, `Negative/ServerIGFirst` and `Negative/PoolRelays`.
Fresh acceptance passed: a strict interaction-mode load of the endpoint
`Negative/ServerPeersOrigins`, after removing its interface, reported checked,
fresh checking, no goals, warnings or errors, and an unchanged source hash
(185 s, 12.4 GB). A cached confirmation (47 s) and
`Negative/ServerPeersReleaseTimeWait` (48 s) passed.

`Negative/ServerPeers.Interleaving` adds `initialized-accept-failure`. It
follows the existing path to step 55, where the PSA monitor pool is open. The
accept loop then fails and the listener closes. The accept result is published
and joined, and the stop is traced. Only then does the monitor pool close, and
the action thread is joined. The supply invariant holds at the end.

Controls:

- The failed loop takes no cancellation request.
- No new connection is accepted after the failure.
- The peer side stays open.
- The loop cannot fail after the stop.

Several listeners, and therefore the cancellation of the other loops by
`withAsyncAll`, remain excluded. SI5, admission/API quiescence, source refinement
and G3–G5 remain open.

## Seventy-first increment: derived shutdown certificate for the outer composition (SI5a)

Checked 10 November 2026. This is the first part of SI5. It derives the
peer-side, Server and relays parts of a complete shutdown from one initialized
history of the outermost composition. The pool relays scope wraps the
Server/peer runtime (`ServerPeersRelays.Protocols`). The CM-coordinator part is
deferred to SI5b, as agreed.

Statement ([ServerShutdownComplete](Properties/ServerShutdownComplete.agda),
`Protocols.complete`). Take a runtime initialized by `T.initialize c g` and an
outer run from it, with relays `initial scheduled`, to a state whose relays are
`finished`. Its final runtime satisfies `Complete`:

- `serverReturned`: the Server stage is `serverReturned`.
- `peerClosed`: the governor and PSA monitor pools are `closedPool`, and the
  scope coordinator is finished.
- `peerComponents`: `Certificates` of [ServerPeers](Properties/ServerPeers.agda).
  Every governor and monitor snapshot job has an available Async result, and
  all four inner scopes are joined.
- `relays`: a node without relays has no thread, and on a node with relays the
  thread is `joined`.

Proof layers:

1. [ServerStageEntry](Properties/ServerStageEntry.agda) shows that only Server
   scope actions change the Server stage, at the admission and IG-exit layers.
   It also shows that the only scope action entering a post-join stage
   (`actionJoined` and later) from an earlier stage is
   `cancelJoinReturnedAction`. The IG-exit plans keep the stage, and only a
   `run` action delegates to the Server.
2. In ServerShutdownComplete, a closed job pool and a finished scope coordinator
   admit no change. Along the projected pool/scope traces of `advance-projects`,
   `peerClosed` therefore persists.
3. At the shared layer, peer and common CM steps keep the stage. A Server scope
   step passes `serverAllowed`, and for `cancelJoinReturnedAction` that is
   `peerClosed`. Through the runtime plans (result caching writes only peer
   context) this gives the invariant: at a post-join stage, the peer side is
   closed. It holds initially (`serving`) and is preserved by every
   `T.advance`.
4. The outer run projects to an inner runtime run. `Certified.from-initial`
   gives the inner return and the relays join, and `present-preserved` ties the
   relays to the initial choice. The invariant at `serverReturned` gives peer
   closure, and `initial-components` gives the component certificates.

[Negative/ServerShutdownComplete](Negative/ServerShutdownComplete.agda) applies
the theorem to the initialized scheduled-node close of `Negative/PoolRelays`
(the accepted server-return run lifted into the relays scope, then relays
cancellation, join and owner return).

Scope and limits:

- **SI5b:** the CM coordinator is closed, with its snapshot handler results
  collected, at the final state. This was open at increment 71 and is done in
  increment 72.
- The following stay excluded:
  - raw admission workers, which outlive the scope;
  - handlers forked after the CM snapshot;
  - several listeners;
  - fatal delivery as the cause of interruption, which stays abstract.
- Accept, action and IG joins are read off the stage order. `serverReturned`
  is entered only from `closingCM`, after `joinAccept`, `cancelJoinReturnedAction`
  and `joinIG`. No separate history record is proved.
- No eventuality or fairness claim: the certificate holds for runs that reach
  the finished relays state.
- [ProductionPolicy](Rules/ProductionPolicy.agda) and its external
  `completeShutdown` boundary are unchanged. In the composed model the boundary
  is superseded by this certificate for the parts above; the standalone policy
  wrapper still uses it.

Checks (one Agda process at a time, 25 GB cgroup, `-M20G`):
`Properties/ServerStageEntry` (37 s, 2.0 GB), `Properties/ServerShutdownComplete`
(51 s, 3.0 GB, no warnings) and `Negative/ServerShutdownComplete` (44 s,
6.2 GB, no warnings, over cached `Negative/PoolRelays`).
No postulates, holes or unsafe flags were added. SI5b, admission/API
quiescence, CM-I4c reference validity and G3–G5 remain open.

## Seventy-second increment: the closed CM coordinator at the final state (SI5b)

Checked 10 November 2026. This completes SI5 for the one-listener profile. It
adds the CM shutdown coordinator to the SI5a certificate, for the same
initialized outer histories.

Statement ([ServerShutdownCoordinator](Properties/ServerShutdownCoordinator.agda),
`Protocols.complete`). Under the premises of SI5a, the final runtime satisfies
`Complete`, which holds the SI5a certificate and `CMClosed`:

- `closed`: the coordinator phase is `Close.closed`.
- `drained`: no captured snapshot entry is left unread (`remaining ≡ []`).
- `physicalWait`: the closing `finishClose` was an actual wrapper transition,
  either the handler supervisor's (`HandlerSupervision.PhysicalWait`) or the
  exit wrapper's (`CoordinatorFrames.ExitWait`). Its oracle is that wrapper's
  handler-result table at the wait, and every collected handler was available
  there.

Proof layers:

1. [CoordinatorFrames](Properties/CoordinatorFrames.agda) defines a coordinator
   `Frame`: a list of real `CMShutdown` steps between two observations, and
   transport of the closing-wait witness. A closed coordinator admits no step,
   and only `finishClose` can produce `closed`. The frame is proved for every
   step of the mux handler supervisor (from its existing projected coordinator
   path), the protocol, monitor and group layers (from the existing
   `direct-shutdown-same` lemmas), and the exit, cancellation, startup-unwind,
   DeltaQ, catch and publication wrappers. These mirror their `step-projects`
   proofs. Exit-wrapper coordinator calls go through `control-frame`, which
   records the physical wait for `finishClose`.
2. [CoordinatorFrontend](Properties/CoordinatorFrontend.agda) lifts the frame
   through the Server (worker metadata, inherited and IG-cleanup steps), the IG
   exit wrapper, the shared Server/peer composition (peer steps write only the
   CM source) and the runtime. The runtime's trace-fault delivery is the only
   plan that replaces the coordinator directly. Its chosen plan carries the exit
   wrapper's actual acknowledgment (`SafePlan`, proved for every event as in
   `HandlerAuxFrontend`).
3. In ServerShutdownCoordinator, `serverReturned` is entered only by
   `finishServer`, which is chosen only on a closed coordinator. A closed
   coordinator stays the same along any frame, so the invariant "a returned
   Server has a closed coordinator" holds initially and after every
   `T.advance`. Initialization yields `Close.initialState` through every
   layer. `CMShutdown.closed-from-initial` on the composed trace gives
   `remaining ≡ []`, and the frame carries the physical wait.

[Negative/ServerShutdownCoordinator](Negative/ServerShutdownCoordinator.agda)
applies the theorem to the same initialized scheduled-node close as
increment 71.

Scope and limits:

- The coordinator certifies only the handlers in its snapshot. Handlers forked
  after the snapshot, raw admission workers and several listeners stay
  excluded, as in SI5a.
- The wait reads the actual result table of the wrapper that performed it. No
  claim is made that the oracle stays true afterwards, or that every handler
  ever forked has ended.
- No eventuality or fairness claim. [ProductionPolicy](Rules/ProductionPolicy.agda)
  is unchanged as a standalone wrapper.
- No existing module was changed; the frames are new modules over the existing
  projections.

Checks (one Agda process at a time, 25 GB cgroup, `-M20G`):
`Properties/CoordinatorFrames` (1 min 56 s), `Properties/CoordinatorFrontend`
(4 min 14 s), `Properties/ServerShutdownCoordinator` (5 min 14 s, 5.4 GB, no
warnings) and `Negative/ServerShutdownCoordinator` (53 s, 6.2 GB, no warnings).
Peak memory was not recorded for the two frame modules.
No postulates, holes or unsafe flags were added. Admission/API quiescence,
CM-I4c reference validity and G3–G5 remain open.

## Seventy-third increment: late admission after the CM shutdown

Checked 10 November 2026. First step of admission/API quiescence, as agreed:
characterize what the source leaves running before modelling a fix.

Source (pin `2f1c154`): the accept loop forks each admission worker with a
plain `async` and drops the handle (`Server.hs` 239–254). The CM `finally`
(`Core.hs` 524–550) reads `stateVar` once (`readTMVar`) and cancels only the
handler threads in that snapshot; nothing marks the CM closed, and
`includeInboundConnectionImpl` has no shutdown guard. A worker whose map take
comes after that read can therefore fork a handler that no scope cancels or
joins. This contradicts the `Server.with` API comment (all server threads
stop when the callback returns) more strongly than CM-PUB1, where workers
stay blocked in STM.

Model witness ([Negative/ServerLateAdmission](Negative/ServerLateAdmission.agda)):
it continues the initialized run of [Negative/ServerAdmission](Negative/ServerAdmission.agda).
In that run the Server has returned and the coordinator has closed over an
empty snapshot. The second raw worker, forked before the close, then takes the
map, counts, allocates a promise, chooses an entry and forks a physical
handler. After these steps the Server is still returned, the coordinator is
still closed with an empty collected list, and the new handler thread exists.
The run is one `S.Executes` from the initializer; the late states are computed
by the step function, not written by hand. The witness is at the Server
admission layer. Whether the shared, runtime and relays layers enable the same
steps after `serverReturned` was not checked, and no composed run was built.

Source replay ([SourceReplay](SourceReplay/README.md#late-admission-after-the-cm-shutdown-10-november-2026)):
IOSim at the pin. IOSimPOR finds a schedule in which `Server.with` returns and
the CM `finally` completes before the Server's own worker takes its first
step. A deterministic run of the retained CM handle after `Server.with`
returns shows the include forking a handler that runs to its own handshake
timeout, with nothing cancelling it. No single explored trace contains the
delayed worker's include itself (a bounded negative). The finding is a strong
candidate, not a one-trace confirmation.

Model consequence: SI5 (increments 71–72) certifies only the handlers in the
coordinator's snapshot. The "handlers forked after the snapshot" exclusion is
now known to be reachable, not only possible.

Checks: `Negative/ServerLateAdmission` (34 s, 4.3 GB, no warnings). Replay:
4 tests, 3 runs, about 1.3 s each, no compiler warnings. Next: the residue
theorem, first that the IG has no pending CM call once joined (c1), then that
no outbound call frame is left once all peer jobs are terminal (c2). The fix
model follows.

## Seventy-fourth increment: no pending inbound-governor CM call at shutdown (residue c1)

Checked 11 November 2026. Second part of the admission/API residue: the
inbound governor is not a CM API caller left behind.

Statement ([IGPendingQuiet](Properties/IGPendingQuiet.agda),
`Protocols.ig-quiet`). For every initialized run of the outer composition that
reaches the finished relays state (the SI5 premises), the final CM source has
an exited, deactivated inbound governor (`continuation ≡ exited`,
`active ≡ false`) with no pending release call (`inboundRelease ≡ nothing`)
and no pending remote call (`remoteCall ≡ nothing`).

Proof layers:

1. [IGQuiet](Properties/IGQuiet.agda): from an exited, deactivated governor,
   every `IG.step` keeps it exited and deactivated. Loop actions need a live
   continuation, deactivation needs an active engine, and all other actions
   rewrite only mux, handle, timer, counter or DB tables.
2. [MachineQuiet](Properties/MachineQuiet.agda): that state with no pending
   call (Q) is preserved by every machine and outbound-machine step. A release
   or remote call can begin only from a `needsCM` continuation; handler
   lifecycle and peer actions only replace mux rows (`SameControl`).
3. The CM peer chain ([PeerJobCM](Properties/PeerJobCM.agda),
   [SubsystemCM](Properties/SubsystemCM.agda),
   [GovernorPoolCM](Properties/GovernorPoolCM.agda),
   [PeerSupervisionCM](Properties/PeerSupervisionCM.agda)) lifts any predicate
   on the whole CM configuration through every peer job, subsystem, governor
   pool and supervision step. Its premises are the actual write kinds:
   control-preserving IG writes, call initializers, monitor completions, raw
   core actions (with a permission), caller-cancellation start, cleanup world
   writes and close-failure results. It is reusable for residue c2.
4. [ServerSourceQuiet](Properties/ServerSourceQuiet.agda) lifts Q through the
   publication layer (its existing outbound-machine traces) and every Server
   step. [ServerIGDone](Properties/ServerIGDone.agda) shows (generated) that a
   Server scope step reaches a finished IG phase only from one or by
   `finishIGBody`, keeps it finished, and enters `igJoined` or later only from
   there or by `joinIG` with a finished IG.
5. In IGPendingQuiet the runtime invariant has three parts: after the IG
   exit's snapshot step Q holds (that step checks exactly Q's fields); a
   finished IG body implies that phase (the exit wrapper refuses the Server's
   own `finishIGBody`); a post-IG stage implies a finished body. It holds
   initially and after every runtime step, and the SI5a `serverReturned`
   gives the result.

[Negative/IGPendingQuiet](Negative/IGPendingQuiet.agda) applies it to the
initialized scheduled-node close.

Scope and limits: this is about the inbound governor's CM calls only. Raw
admission workers remain the known residue (increment 73). Outbound caller
frames (`acquiring`/`releasing`) are residue c2, still open; on the same
fixture they are empty, which is evidence, not a proof. No eventuality claim.

Checks (one Agda process at a time, 25 GB cgroup, `-M20G`, no warnings):
`Properties/IGQuiet` (8 s), `Properties/MachineQuiet` (9 s), the four peer
chain modules (7–10 s each), `Properties/ServerIGDone` (2 min),
`Properties/ServerSourceQuiet` (19 min 15 s, 5.3 GB),
`Properties/IGPendingQuiet` (7 min 28 s, 6.7 GB) and
`Negative/IGPendingQuiet` (52 s, 6.8 GB). No postulates, holes or unsafe flags.

## Seventy-fifth increment: outbound caller frames at shutdown (residue c2)

Checked 11 November 2026. Third part of the admission/API residue.

As first stated, c2 was "no outbound acquire or release call frame
(`O.acquiring`, `O.releasing`) is left at the end of the outer shutdown".
That is false in the model, and the counterexample is kept.

Counterexample ([Negative/ForeignCallerResidue](Negative/ForeignCallerResidue.agda)).
The model admits a foreign CM caller: a worker owned by no peer job and no
monitor. While the peer side is open, it may begin an outbound acquire
(`ServerPeers.coreAllowed`, `GovernorPool.unowned`,
`PeerSupervision.rawAllowed`). Only two writers delete a frame: the caller's
own `returnResult`, and `CallerCancellation.start` (job cancellation or
monitor detach). No shutdown gate inspects `O.acquiring`. The witness:

- inserts `beginAcquire` for worker `ident 900` into the initialized
  scheduled-node close, at the last state before the peer scopes unwind;
- replays every later fixture edge (95 events: peer scopes, Server scope, CM
  receipt, physical close, catch, handler finalizer, CM finish, Server
  finish) by `refl` on the state carrying the extra frame and region;
- closes the relays exactly as `Negative/PoolRelays` does.

At the end the SI5b certificate (`Certificate.complete`) and residue c1
(`ig-quiet`) both hold, yet `acquiring-nonempty` shows the foreign frame
still pending at `selecting`.

This is not a source defect. In the node, `acquireOutboundConnection` and
`releaseOutboundConnection` are called only from peer-state actions run by
the outbound governor's jobs. A foreign caller models an arbitrary holder of
the CM handle. Its frame is that caller's own stack, which the CM neither
owns nor joins.

Restated c2 (approved 11 November 2026, proved in the seventy-sixth
increment): every outbound frame left at the end belongs to a foreign caller,
never to a worker owned by a peer job or monitor.

Checks: `Negative/ForeignCallerResidue` (58 s, 6.8 GB, no warnings).

## Seventy-sixth increment: restated residue c2, foreign frames only

Checked 12 November 2026. Proves the c2 restated in the seventy-fifth
increment.

Endpoint ([Properties/ForeignFrames](Properties/ForeignFrames.agda),
`Protocols.foreign-frames`). For every outer run from
`T.initialize (O.initial c₀) g` to finished relays, at the final state each
worker `w` with an `O.acquiring` (`O.releasing`) frame has no `O.acquired`
(`O.released`) entry, `GovernorPool.unowned w` holds for the job table, and
`PeerSupervision.byWorker w` is `nothing` for the monitor threads. Jobs are
only flagged on deregistration and monitor threads are never deleted, so the
worker was never owned by a peer job or monitor. The premise fixes an empty
initial CM; `T.initialize` alone accepts supplied CM state.

Proof structure:

- Server side ([SourceKeys*](Properties/SourceKeysShared.agda),
  [OutboundKeys](Properties/OutboundKeys.agda)). No Server step changes which
  workers have a frame, either result table, or the peer context; a core step
  changes them exactly by its own outbound action. The relation also carries
  unique keys in the four caller tables (`Store.delete` removes one binding).
- Shared runtime ([OwnedFramesExecution](Properties/OwnedFramesExecution.agda)).
  `Reach = Owned × Unique × Aux` holds from `K.initial (O.initial c) g` along
  `K.Executes`. `Owned`: each frame has no result and its worker is foreign,
  a running job awaiting that call, or a running, observing monitor
  follow-up awaiting it. `Aux` holds peer-table key uniqueness, distinct job
  callers that are not monitor workers, follow-up attachment and detached-job
  identity. Every server, core and peer step constructor is covered.
- Outer runtime ([OwnedFramesRuntimeSelection](Properties/OwnedFramesRuntimeSelection.agda)).
  `Reach` is preserved by every `T.advance` plan; result reads and direct peer
  callers use their selection facts.
- Closure. The run's pool projections start at the initial pools, and the
  certificate's `peerClosed` gives both pools closed, so
  [JobPoolLive](Properties/JobPoolLive.agda) `closed-dead` leaves no running
  handle. That excludes the job and follow-up owners.

Fixtures ([Negative/ForeignFramesFixture](Negative/ForeignFramesFixture.agda)):
`scheduled-close` (the c1 fixture run) and `foreign-close` (the
seventy-fifth increment's counterexample run). `foreign-worker` derives from
the theorem that the surviving frame's worker `ident 900` is foreign.

Consequence for the design. Foreign callers are a model over-approximation;
production calls come only from peer-state actions run by governor jobs. In
a model without them no outbound frame is left at shutdown. A design variant
proving that directly is the seventy-seventh increment.

Checks: fresh `Negative/ForeignFramesFixture` (5 new modules, 123 s, 7.8 GB);
fresh `Properties/OwnedFramesExecution` (67 modules including all
`SourceKeys*`, 815 s, 6.6 GB). No warnings.

## Seventy-seventh increment: owned-callers design variant, original residue c2

Checked 12 November 2026. First design-exploration variant (DESIGN §1).

Variant ([Variants/OwnedCallers](Variants/OwnedCallers.agda)). Only peer jobs
and monitors call the CM. The policy `ownedOnly` refuses the raw core actions
`O.beginAcquire` and `O.beginRelease`. `ServerPeers.coreAllowed` admits these
only for a worker owned by no job and no monitor, so the policy removes
exactly the foreign callers of the seventy-fifth increment. No other route
admits a foreign begin: Server steps never begin a CM call
(`SourceKeysShared.server-keys`), raw peer `Sub.core` actions are already
refused, and direct runtime callers are selected job continuations.

The variant guards the existing rules rather than copying them: `step′`
guards `K.step`; `enact′` guards the `inherit` and `complete` plans and keeps
the original plan selection; `Runs′` and `OuterRuns′` execute the guarded
transitions. `restriction`, `runs-restriction` and `outer-restriction` show
each variant run is a source run, so every source theorem (SI5,
`foreign-frames`) applies. `allowed-build` and `allowed-view` show the
guarded runs are exactly the source runs whose enacted shared actions satisfy
the policy (`Allowed`).

Endpoint ([Properties/OwnedCallers](Properties/OwnedCallers.agda),
`Protocols.no-frames`). For every variant outer run from
`T.initialize (O.initial c₀) g` to finished relays, `O.acquiring` and
`O.releasing` of the final source have no entry for any worker. The variant
keeps `NoForeign` (no frame's worker is foreign) alongside `Reach`
(`no-foreign`); with `foreign-frames` this excludes every final frame.

Fixtures ([Negative/OwnedCallersFixture](Negative/OwnedCallersFixture.agda)):

- `scheduled-policy`, `scheduled-run`, `scheduled-close`: the scheduled close
  satisfies the policy (by computation), so it ends with no frame;
- `foreign-begin-refused`, `complete-begin-refused`,
  `foreign-run-not-variant`, `foreign-source-policy-rejected`: the variant
  refuses the counterexample run at its inserted foreign begin.

Summary of residue c2: the source model guarantees only the restated c2
(seventy-sixth increment); the owned-callers design guarantees the original
c2. The difference is exactly the foreign caller, which the node does not
have.

Checks: fresh `Negative/OwnedCallersFixture` (12 new modules, 107 s, 7.6 GB).
No warnings.

## Seventy-eighth increment: admission quiescence step 2, design exploration

Checked 12 November 2026. The goal is a design in which all Server threads
stop when `Server.with` returns, addressing the seventy-third increment.

Rejected design 1, "Server owns, cancels and joins admission workers"
(phase A). The include callback is explicitly unmasked (`Core.hs` 801–880).
If cancellation arrives after the handler fork but before map publication,
`modifyTMVar` restores the old map (2373–2379), losing the live handler's
binding. Joining the worker does not join its child. A standalone `async`
primitive-contract probe confirmed this window and its post-publication
control. This is a primitive-contract probe, not a replay of CM or Server.

Design 2, "own + join, no cancel" (phase B,
[Variants/ServerOwnedWorkers](Variants/ServerOwnedWorkers.agda)). Workers are
registered at accept and joined only when their results are available.
`outer-erasure` drops the joins; [Properties/ServerOwnedWorkers](Properties/ServerOwnedWorkers.agda)
transports SI5. The late-admission witness is refused at `beginCM`
([fixture](Negative/ServerOwnedWorkersFixture.agda)). It is still not quiescent:
in [Negative/ServerOwnedWorkersCounterexample](Negative/ServerOwnedWorkersCounterexample.agda),
the worker consumes a failed handshake, deletes the binding and is joined,
while its handler remains in the catch with no physical result. CM and relays
finish over an empty snapshot.

Phase C audited routes by which a live handler can leave the map, or lose its
thread reference, before the snapshot. Source ranges are in `Core.hs` at pin
`2f1c154`:

- Inbound failure/query deletion (897–904, 1007–1075), and outbound
  failure/query deletion (1771–1830, delete at 1795), precede handler exit.
- Ordinary self-purge (652–665) and TIME_WAIT final purge (695–713) leave
  tracing, possibly blocking counter reads and physical result publication.
  Even the tail after cleanup has finished can still lack its Async result.
- Outbound bracket cleanup can remove aliases (1452–1471); a fork before
  entry publication (1532–1552) leaves a reservation that CM skips.
- Same-entry overwrite or fresh-entry replacement (839–879, 1558–1563)
  can detach an old handler. Concrete collision/address reachability remains
  a separate obligation.
- Pruning (761–776) writes `Terminated` before physical completion, losing
  the thread reference. Cancellation receipt is not a join.
- Pre-publication exception rollback (870–879, 2376–2377) can omit a forked
  handler; this source concern is outside the selected worker exception model.

A failure/query-only worker-to-handler join leaves the other routes open.
The decision was that only a historical handler registry closes all these
routes among the explored designs.

Source candidate ([Negative/ServerOwnedWorkersSelfPurge](Negative/ServerOwnedWorkersSelfPurge.agda)).
The initialized run admits `Connected`, returns and joins the worker, then
runs the handler's self-purge and pauses it at `cleanupCount`, before exit.
CM closes with an empty snapshot and the relays finish, but the handler has
no physical result (`not-quiescent`). `source-run` also gives the erased
source run. This is a model result, not yet replayed in IOSim: a strong
candidate that `Server.with` can return with a live handler.

Design 3, accepted ([Variants/ServerOwnedHandlers](Variants/ServerOwnedHandlers.agda)),
combines a historical handler registry, Server-owned admission workers
(no cancel), and the owned-callers policy of increment 77. Physical births
register atomically. A registry sweep skips available results or requests
cancellation through existing delivery sites, then waits for every registered
result. During protected cleanup it waits for the actual result. The worker
gate requires joined workers with available results at `closingCM` and
`serverReturned`; the CM gate requires the completed sweep and all registry
results before closure, and preserves that requirement afterwards.

Theorems ([Properties/ServerOwnedHandlers](Properties/ServerOwnedHandlers.agda)):
`outer-erasure` supplies a source run, relabelling registry delivery to existing
physical observations; `si5` transports SI5; `registry-si5` adds the completed
registry wait. `no-late-admission` gives joined workers at the closed Server
stages. At finished relays, `quiescence` gives `Quiescent`: workers are joined,
and every registered and every physical handler thread has its result.
`quiescent-covered` derives live-handler coverage. The initialized progress
and refusal fixtures are in [Negative/ServerOwnedHandlersFixture](Negative/ServerOwnedHandlersFixture.agda).

Scope: safety only. Progress is demonstrated by finite runs only; the model
is untimed and proves no eventual shutdown. The registry is a design proposal,
not part of the pinned source.

Checks (fresh, by the reviewer): `Properties/ServerOwnedHandlers` (105 s,
4.8 GB), `Negative/ServerOwnedWorkersSelfPurge` (27 s),
`Negative/ServerOwnedHandlersFixture` (70 s, 5.3 GB),
`Negative/ServerOwnedWorkersCounterexample` (16 s) and
`Negative/ServerOwnedWorkersFixture` (36 s). No warnings.

Next: IOSim replay of the self-purge candidate.
