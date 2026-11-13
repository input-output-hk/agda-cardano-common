# Primitive and dependency contract matrix (G1)

13 November 2026 (G1 runtime follow-up). [GateAudit plan step 2](GateAudit.md#ordered-gap-closing-plan),
under [DESIGN §§9–10](DESIGN.md#9-implementation-gates-and-validation).
Network **`2f1c154f248659b89523d5679ca532f442e7ed2a`**, selected by consensus
**`2e44d98a843168ba3b189e305820b79943ac7d1e`**. This audits the selected model
profile in [BranchMatrix](BranchMatrix.md).

**All 90 selected primitive rows now have implemented rules and paired controls.**
The five findings below are fixed in the current worktree, following the user's
12 November decision. G1 acceptance remains pending the capped downstream checks
listed in [increment 80](Supervision.md#eightieth-increment-g1-primitive-runtime-closure).
This is model coverage under the supplied IO/timer/blocking contracts, not a
Haskell refinement or a new implementation replay.

## Resolved dependency evidence

The actual retained replay build plan is
`dist-newstyle/cache/plan.json` of the session-local replay build (not
retained in the repository).
SHA256: `2c443751d64a3fa6ab8e967541b64adf69a39aac8ac2e6cbbd8ea462c651701a`.
It reports **GHC 9.6.7, Cabal 3.12.1.0, Linux x86_64**. Its network checkout's
HEAD was independently read as the full pin above. This is resolved build
information, not inference from a Cabal version range. Global units below also
exist in `/home/rye/.cabal/store/ghc-9.6.7/`; base/stm are compiler-package units.
The plan, source archives and installed unit IDs were inspected; no Haskell
build or replay was run for this audit.

| Resolved package | Plan unit / source evidence |
| --- | --- |
| io-classes **1.8.0.1** | Main unit `io-classes-1.8.0.1-85899f4304c78f37c010942b26aa8d3bdfa2647409261abc30f2d3a4787caf89`; selected sublibraries include `si-timers-ca51bcec…` and `strict-stm-4d72005e…`. [CHaP source archive][Classes], SHA256 `b12df6bc63238a83fc1e3250475bb89affa6ca640332f10a77280a7a39d07047`, matched to plan. |
| io-sim **1.8.0.1** | `io-sim-1.8.0.1-b664d61e51f09125914628a399ebaa5c5f5ebb31f9bbb0e9a346dafd8a127e5b`; [CHaP source archive][Sim], SHA256 `b6c0d5f2f5803b63ee945837e06c576ad09db732e950aacdd91c5843689060f7`, matched to plan. |
| async **2.2.6** | `async-2.2.6-2eb63eda2b7e9ce3e3f8063c5fd754ab5778d7a916f5411f401101fa1648a412`; [Hackage source archive][Async], plan SHA256 `148571bc188003101241da6c49131d07324e63a88ed283a84def2e9694599619`. |
| stm **2.5.1.0**, base **4.18.3.0**, exceptions **0.10.7** | Plan pre-existing units `stm-2.5.1.0`, `base-4.18.3.0`, `exceptions-0.10.7`. IO instances delegate to stm/base; the selected path uses io-classes' IO catch/mask, not an inferred exceptions-package instance. |
| network-mux **0.12.0.0**, monoidal-synchronisation **0.1.0.8** | Local units `network-mux-0.12.0.0-inplace`, `monoidal-synchronisation-0.1.0.8-inplace` at the network pin; timer serial helper and synchronization operators are source dependencies too. |
| typed-protocols **1.2.1.0** | Main unit `typed-protocols-1.2.1.0-97caa095d32db19db6e2f7d5b176eb7154a7452f179a86bd0427c484e95f4ee1`; plan archive SHA256 `237d19c67d744d612bb5cc4d2a537762b7b525784543e826d3d759b9d3aa643f`. [Forcing probe](SourceReplay/README.md#handshake-result-forcing-contract-probe) explains the driver/strict Handle boundary. |

Cached archives were extracted read-only into `/tmp/cm-g1-20261112/deps/`.
Recover io-classes/io-sim from
`/home/rye/.cabal/packages/cardano-haskell-packages/<package>/<version>/`
and async from the equivalent `hackage.haskell.org` directory. Package source
paths/ranges below refer to those exact archives. Web source views were
unavailable; the audit uses the local pinned sources, not an unversioned web API.

## Dependency contracts and IO versus IOSim key

Every row cites a source call site plus one of these dependency contracts. The
last column records the corresponding IO/IOSim distinction; combined keys apply
both limitations. “Same” is a selected operation contract, not observational
equivalence of runtimes.

- **D-STM / S.** io-classes `src/Control/Monad/Class/MonadSTM/Internal.hs`
  580–663 delegates IO to stm; defaults 743–785 implement TMVar empty/full
  retry, 815–879 TQueue, 887–1015 TBQueue. io-sim
  `src/Control/Monad/IOSim/Types.hs` 489–555 selects those defaults; its
  `Internal.hs` `execAtomically` handles Retry/OrElse and rolls back tentative
  TVar writes. Map leases are model ownership metadata: raw TMVar does not itself check a
  thread owner; the selected lexical helper contract justifies that restriction.
  Atomic retry exposes no partial write; alternatives are left
  biased when both can commit. Strict wrappers evaluate stored values; they
  do not change the commit boundary. The model's `nothing` also represents
  malformed inputs/refusals, so it must not always be called source STM retry.
- **D-ASYNC / A.** io-classes `MonadAsync.hs` 231–257, 358–407 delegates
  IO to async; IOSim uses the defaults and its fork/result TMVar implementation.
  async `Control/Concurrent/Async/Internal.hs` 146–159, 246–274, 299–341:
  child result is an Either stored after body completion, `waitCatchSTM` reads
  without consuming, `waitSTM` rethrows Left, `cancel` is `throwTo` followed by
  `waitCatch`, and `uninterruptibleCancel` masks both. **IO `waitCatch` retries
  `BlockedIndefinitelyOnSTM`; IOSim's default is simply atomically/read.** GHC
  GC/deadlocked-STM behavior and multicore scheduling are not simulated model
  transitions. Fork success does not imply parent registration or scope ownership.
- **D-MASK / M.** io-classes `MonadThrow.hs` 220–258 delegates IO catch,
  mask, uninterruptibleMask and bracket to base; `MonadFork.hs` 57–77 delegates
  fork/throwTo. IOSim `Types.hs` 394–439 restores the captured masking state;
  `Internal.hs` 580–640, 927–969 implements throwTo and caught-handler masking.
  Both catch handlers run at least MaskedInterruptible. Unmasked receipt is
  allowed; masked-interruptible receipt requires a blocking interruptible
  operation; uninterruptible scope refuses it, even while blocked. Returning
  from throwTo is receipt, not termination. IOSim sees modeled STM/delay/throwTo
  blocking, not arbitrary OS/FFI/tracer blocking, allocation safe points or GC.
  Explicit “blocked” model actions are observation contracts, not evidence
  that invoking an arbitrary tracer/provider must block. Tracer success is also
  an input. Pure policy/rethrow/status-write steps are not extra receipt sites.
- **D-TIMER / T.** io-classes `MonadTimer.hs` 44–51 delegates IO delays,
  registered-delay TVars and timeout to base/stm. Its `si-timers/.../SI.hs`
  72–99, 165–262 implements SI conversion and cancellable delay; NonStandard
  118–168 has pending/fired/cancelled states. IOSim `Types.hs` timer instances
  and `Internal.hs` StartTimeout/ThreadDelay/TimeoutFrame use virtual time and
  matching timeout identities. **`timeout` is an exception-based helper, not
  a left-biased STM orElse race.** Timer expiry need not make an uninterruptible
  action return. Linux [Mux.Timeout][Timeout] 59–67 selects native timeout;
  the alternative Windows monitor is outside this Linux plan. Model token
  expiry/elapsed inputs are untimed and have no deadline/fairness guarantee.
- **D-EVAL / H.** IO catches monadic evaluation/ordinary Haskell forcing
  exceptions at actual forcing points; a lazy host-evaluation failure can
  escape IOSim's monadic handler. [Forcing/publication evidence](SourceReplay/README.md#actual-cm-caller-and-cleanup-replay-for-cm-pub1)
  records that distinction. Protocol descriptors, buffers, OS IO and deployment
  tracers remain supplied contracts; passing Agda equations do not validate them.

## Matrix and counting convention

**90 rows: original inventory 40 met / 50 missing; 12 November fixture audit 85 met / 5 missing; current runtime coverage 90 met / 0 missing.** Rows have exactly **met** or **missing** status, with before
and after measured over this same inventory. “Before missing” includes an absent
named enabled/refusal pairing, even if a related broader fixture already existed;
it does not allege that a previously proved model theorem was false.

**Met** means the selected contract is stated and the existing rule has both a
named enabled example and refusal/rollback control. A permission-layer equation
is explicitly labelled: it tests an existing classifier on generic/local data,
not an initialized delivery step. Where available it is paired with an older
physical dispatch/history witness. The same protected-context refusal can cover
several caller PCs; no separate mechanism is invented. Deliberately forbidden
sites use normal operation as the positive control and receipt as the refusal.
The seven startup PCs and four callback constructors are listed individually;
all `Site`/`DeliverySite`/`Window` constructors of the selected cancellation
adapters are covered. Grouped job/provider rows name their finite actors/PCs.
This is not a general interpreter for every Haskell async-exception safe point.

Original module headers were read before classifying scope: Scenarios are local
or abstract-boundary witnesses; `*Fixtures` build data only; the cited initialized
Negatives prove their own particular finite paths. Existing fixtures were located
by actual declarations and headers; their historical checks are not relabelled
as fresh validation here. New fixture checks are listed below.


### Shared storage, concurrency and synchronization

| ID / primitive and pinned source | Existing model rule | Enabled example | Refusal / rollback control | IO / IOSim | Before → after |
| --- | --- | --- | --- | --- | --- |
| P01 — TMVar take: [Core] 2373–2379; D-STM | [CM](Rules/CM.agda) `takeMap`: empty map cell retries; capture map, keep entry heap. | [take-enabled](Negative/PrimitiveMap.agda) | [take-empty-refused](Negative/PrimitiveMap.agda) | S | missing → **met** |
| P02 — TMVar put/restore: [Core] 2377–2379; D-STM | `putMap`/`restoreMap`: only lease owner publishes; restore saved map with current heap. | [put-enabled](Negative/PrimitiveMap.agda), [restore-enabled](Negative/PrimitiveMap.agda) | [foreign-put-refused](Negative/PrimitiveMap.agda), `foreign-restore-refused`, `put-full-refused`; [restoration-is-not-heap-rollback](Negative/HeapRollback.agda) | S | missing → **met** |
| P03 — STM commit/retry/rollback: [Core] 2382–2399; D-STM | Whole entry+notification transaction commits, or returns `nothing` without a successor. | [burst-fits](Scenarios/IGBatch.agda) | [burst-retries-as-a-whole](Scenarios/IGBatch.agda) / `split-prefix-would-fit`; [full-queue-refuses-entire-commit](Negative/Outbound.agda) | S | met → **met** |
| P04 — Ordered `orElse`: [Sync] 41–69; D-STM | [IGBatch](Rules/IGBatch.agda) `selectBatch`: maturity, commit, queued messages, inactivity, in that order. | [maturity-wins](Scenarios/IGBatch.agda) / `commit-before-queue` | [queue-before-timeout](Scenarios/IGBatch.agda) / `all-retry` | S | met → **met** |
| P05 — Async fork, parent insertion: [JobPool] 122–145; D-ASYNC | [JobPoolKernel](Rules/JobPoolKernel.agda) permits child execution before masked parent registration. | [fast-second-child-returns](Negative/ConcurrentPool.agda) / `second-parent-registers-independently` | [fast-child-dereg-retries](Negative/ConcurrentPool.agda) / `no-reused-child-identity` | A | met → **met** |
| P06 — Promise ordinary write: [CMTypes] 266–322; D-STM | [Handshake](Rules/Handshake.agda) `publishBoundary`: first write succeeds; duplicate returns explicit `writerBlocked` exception outcome, not retry. | [early-publication-is-readable](Scenarios/Handshake.agda) | [duplicate-publication-throws](Scenarios/Handshake.agda) | S/H | met → **met** |
| P07 — Promise read: [CMTypes] 289–315; D-STM | `readResult` blocks on empty and retains result; `forcePromise` is unused by selected handlers/model and is outside this row. | [promise-survives-read](Scenarios/Handshake.agda) | [empty-promise-waits](Scenarios/Handshake.agda) | S | met → **met** |
| P08 — Bounded FIFO/whole flush: [Info] 35–54; D-STM | [InformationChannel](Rules/InformationChannel.agda): capacity 100; producer-owned STM burst; flush preserves order and empties queue. | [fifo-read](Scenarios/IGBatch.agda) / `flush-preserves-order` / `flush-empty-succeeds` | [full-retries](Scenarios/IGBatch.agda) / `burst-retries-as-a-whole` | S | met → **met** |
| P09 — Unbounded completion/command queues: [JobPool] 160–164, 205–209; [Mux] 326–328, 630–646; D-STM | [JobPoolKernel](Rules/JobPoolKernel.agda) completion list; [IGRegistration](Rules/IGRegistration.agda) commands; no capacity guard. | [normal₃](Negative/JobPoolLifecycle.agda); [later-run-publishes-first](Negative/InitiatorCompletionFIFO.agda) | [normal-deregister-before-publication-refused](Negative/JobPoolLifecycle.agda); [physical-FIFO-blocks-shutdown-selection](Negative/MuxGroupShutdown.agda) | S | met → **met** |
| P10 — Protocol first-result ordered STM: [Actions] 361–381; [Sync]; D-STM | [PeerActions](Rules/PeerActions.agda) `first` sorts by protocol number, retaining source not-running guard. | [first-enabled](Negative/PrimitiveResults.agda) | [first-retired-prefix-refused](Negative/PrimitiveResults.agda) / `first-empty-refused` | S | missing → **met** |
| P11 — Protocol all-results STM: [Actions] 383–435; [Sync] 74–129; D-STM | `all`: empty succeeds, every started run must return; errors dominate; no physical termination inferred. | [all-empty-enabled](Negative/PrimitiveResults.agda) / `all-returned-enabled` / `all-error-enabled` | [all-pending-refused](Negative/PrimitiveResults.agda) | S | missing → **met** |
| P12 — `cancel`/`wait`/`waitCatch`/`pollSTM`: [JobPool] 100–110, 211–224; [Core] 534–550; D-ASYNC | Request → receipt → body unwind → deregistration → Async result → join. `waitCatch` observes Either; `wait` rethrows Left; the model retains classified outcomes at the relevant adapters, not arbitrary Haskell exception values. | [cancel₁₈](Negative/JobPoolLifecycle.agda) / `first-captured-handle-still-joins` | [join-before-async-result-refused](Negative/JobPoolLifecycle.agda) / `deregistered-is-not-async-terminal` | A | met → **met** |
| P13 — `throwTo`: [Core] 1254, 2032, 534–546; D-MASK | [CMShutdown](Rules/CMShutdown.agda), release continuations: sender waits for receipt, which is distinct from target result; already finished target needs no delivery. | [handshake-delivery-acknowledged](Negative/HandlerSupervision.agda); [receipt](Negative/ServerPeersReleaseTimeWait.agda) | [receipt-cannot-close-cm](Negative/HandlerSupervision.agda); [prematureReturn](Negative/ServerPeersReleaseTimeWait.agda) | M | met → **met** |
| P14 — `mask`/restore and bracket: [Core] 2373–2379; [JobPool] 122–164; D-MASK | [CallerCancellation](Rules/CallerCancellation.agda), [JobPoolKernel](Rules/JobPoolKernel.agda): local provenance/phase guards; restore original context, not a global masking-state machine. | [blocked-open-delivered](Negative/GovernorPool.agda); [registered-parent-delivery](Negative/PeerSupervisionScenarios.agda) | [ordinary-open-is-masked](Negative/GovernorPool.agda); [masked-parent-refuses-delivery](Negative/PeerSupervisionScenarios.agda) | M | met → **met** |
| P15 — `uninterruptibleMask` and uninterruptible cancel: [Core] 527–550, 600–669, 1453–1465; [JobPool] 100–110; D-MASK | Captured CM shutdown and cleanup have no abort action; caller protected cleanup refuses delivery. TIME_WAIT explicitly restores unmasked context (T07). Blocking in these scopes need not terminate. | [bracket-close](Negative/GovernorPool.agda) / `bracket-remove`; [all-snapshot-handles-joined](Negative/JobPoolLifecycle.agda) | [protected-cleanup-rejects-delivery](Negative/GovernorPool.agda) / `protected-cleanup-rejects-open-override` | M | met → **met** |

### Timers and delays (winner observations, not real-time guarantees)

| ID / primitive and pinned source | Existing model rule | Enabled example | Refusal / rollback control | IO / IOSim | Before → after |
| --- | --- | --- | --- | --- | --- |
| T01 — Outbound-idle registered-delay race: [Core] 2007–2032; D-TIMER + D-STM | [OutboundRelease](Rules/OutboundRelease.agda) `selectWakeup`: changed entry wins if timer also ready; timer selection and later unconditional Terminating write are separate STM actions. | [timer-wins-idle](Negative/PrimitiveTimers.agda); [entry-change-wins-ready-timer](Negative/Outbound.agda) | [timer-not-ready](Negative/PrimitiveTimers.agda) / `duplicate-expiry-refused`; [later-timeout-write-is-separate](Negative/Outbound.agda) | T | missing → **met** |
| T02 — IG inactivity/maturity/idle timers: [IG] 242–278; D-TIMER | [IGRegistration](Rules/IGRegistration.agda) fresh timer tokens; captured-time ordered `selectBatch` inputs. No fairness or autonomous clock. | [timeout-only-when-others-retry](Scenarios/IGBatch.agda) | [queue-before-timeout](Scenarios/IGBatch.agda) / `all-retry` | T | met → **met** |
| T03 — PSA deactivation/close operation timeout: [Actions] 986–1107; D-TIMER | [PeerJobs](Rules/PeerJobs.agda) `operationTimeout`: separate awaitHot/awaitAll routes stop mux and cool peer; does not finish physical cleanup. | [timeout-step](Negative/SubsystemReferences.agda); [Protocols.CloseOriginChecks.Proofs.initialized-timeout](Negative/ServerPeers.agda) | [operation-timeout-before-wait-refused](Negative/PrimitiveTimers.agda) | T | missing → **met** |
| T04 — Demotion-error Cold wait: [Active] 991–998; D-TIMER | `demotionTimeout` completes with `demotionTimedOut` only in `awaitCold`; differs from T03 and handler TIME_WAIT. | [cold-timeout-enabled](Negative/PrimitiveTimers.agda) | [cold-timeout-before-wait-refused](Negative/PrimitiveTimers.agda) | T | missing → **met** |
| T05 — Serial two-second mux drain timeout: [Mux] 763–778; [Timeout] 41–67; D-TIMER | [MuxGroupShutdown](MuxGroupShutdown.agda) successful empty-queues+zero-held drain versus timeout; either may precede Stopped, neither joins the whole pool. | [timeoutStillPossible](Negative/MuxEgressReadiness.agda) | [successfulDrainRefused](Negative/MuxEgressReadiness.agda) | T | met → **met** |
| T06 — Cancellable grant timer/lock: [Bucket] `waitQueued`/`cancel`; [Mux] 454–458; D-TIMER | [MuxEgress](Rules/MuxEgress.agda) queue/arm/grant/disarm; shared IG bucket charge; cancellation removes request/timer without refund, failed write retains held batch. | [timer-armed](Negative/MuxEgressScheduling.agda) / `no-stale-request-or-timer` / `cancel-after-grant` | [no-double-grant](Negative/MuxEgressScheduling.agda) / `granted-after-cancel-refused`; [ranked-lock-before-grant-refused](Negative/MuxEgress.agda) | T/M | met → **met** |
| T07 — TIME_WAIT `unmask (threadDelay ...)`: [Core] 666–669; D-TIMER + D-MASK | [Cleanup](Rules/Cleanup.agda) `timeWaitElapsed`/`interruptTimeWait`; receipt advances actual release sender while finally remains pending. | [receipt](Negative/ServerPeersReleaseTimeWait.agda) / `finally` | [maskedCleanupRefused](Negative/ServerPeersReleaseTimeWait.agda) / `receiptHasNoResult` | T/M | met → **met** |
| T08 — Failure `threadDelay 1`: [Active] 469–476; D-TIMER | [PeerJobs](Rules/PeerJobs.agda) `failureDelayElapsed` is a distinct untimed environment observation; no earlier failure completion. | [delay-enabled](Negative/PrimitiveTimers.agda) | [delay-wrong-wait-refused](Negative/PrimitiveTimers.agda) | T | missing → **met** |
| T09 — Handshake SDU/protocol timeout and inbound query sleep: [Handler] 392–402, 474–484, 516–518; [HandshakeHelper] 82–95; [DriverLimits] 139–140; D-TIMER | [HandshakeContinuation](Rules/HandshakeContinuation.agda), [MuxHandlerSupervision](MuxHandlerSupervision.agda), [MuxHandlerExit](MuxHandlerExit.agda): returned deadline/size limit publishes Left then returns normally; thrown bearer SDU error publishes then rethrows; inbound query publishes before masked-interruptible sleep. | [PrimitiveHandshakeContinuation](Negative/PrimitiveHandshakeContinuation.agda): actual publication, finalizer/result suffix and CM delay receipt. | Same fixture: premature/duplicate publication, wrong window, missing CM request, helper/success cross-use and premature result refusals. | T/H | missing → **met** |
| T10 — Grant refresh expiry/re-arm winner: [Bucket] `waitQueued`; D-TIMER | [MuxEgress](Rules/MuxEgress.agda) `refreshExpired` / `rearmRefresh`, [IGRegistration](Rules/IGRegistration.agda) `grantEffect`: spent timer removed, queued request retained, fresh timer armed. Timer-winning awaitOr is an observed input; no clock/rank/fairness theorem. | [PrimitiveGrantRefresh](Negative/PrimitiveGrantRefresh.agda): repeated paired kernel/bucket cycles and grant/cancel competition. | Same fixture: wrong mode, missing request/timer, duplicate expiry/rearm, cancel-after-refresh and retained-charge controls. | T | missing → **met** |

### Acquisition and release caller delivery sites

| ID / primitive and pinned source | Existing model rule | Enabled example | Refusal / rollback control | IO / IOSim | Before → after |
| --- | --- | --- | --- | --- | --- |
| C01 — [Core] 1273–1832; D-MASK | [CallerCancellation](Rules/CallerCancellation.agda) `plan` at `selecting`: abandon, retaining any committed reservation. | [selecting](Negative/PrimitiveCallerSites.agda) | [protected](Negative/PrimitiveCallerSites.agda) / `wrong-context` | M | missing → **met** |
| C02 — [Core] 1273–1832; D-MASK | [CallerCancellation](Rules/CallerCancellation.agda) `plan` at `count next`: delegate to captured continuation; count alone is not origin evidence. | [counter-enabled](Negative/PrimitiveCallerSites.agda); `counters` preserves nested-PC behavior | [counter-open-refused](Negative/PrimitiveCallerSites.agda); `protected` / `wrong-context` | M | missing → **met** |
| C03 — [Core] 1273–1832; D-MASK | [CallerCancellation](Rules/CallerCancellation.agda) `plan` at `allocatePromise`: abandon before resource acquisition. | [promise](Negative/PrimitiveCallerSites.agda) | [protected](Negative/PrimitiveCallerSites.agda) / `wrong-context` | M | missing → **met** |
| C04 — [Core] 1273–1832; D-MASK | [CallerCancellation](Rules/CallerCancellation.agda) `plan` at `openSocket`: only interruptibleOpen observation; abandon and retain reservation. | [open-blocked](Negative/PrimitiveCallerSites.agda) | [protected](Negative/PrimitiveCallerSites.agda) / `open-ordinary-refused` | M | missing → **met** |
| C05 — [Core] 1273–1832; D-MASK | [CallerCancellation](Rules/CallerCancellation.agda) `plan` at `configureSocket`: close captured socket/reservation. | [configure](Negative/PrimitiveCallerSites.agda) | [protected](Negative/PrimitiveCallerSites.agda) / `wrong-context` | M | missing → **met** |
| C06 — [Core] 1273–1832; D-MASK | [CallerCancellation](Rules/CallerCancellation.agda) `plan` at `bindSocket`: close captured socket/reservation. | [bind](Negative/PrimitiveCallerSites.agda) | [protected](Negative/PrimitiveCallerSites.agda) / `wrong-context` | M | missing → **met** |
| C07 — [Core] 1273–1832; D-MASK | [CallerCancellation](Rules/CallerCancellation.agda) `plan` at `connectSocket`: close captured socket/reservation. | [connect](Negative/PrimitiveCallerSites.agda) | [protected](Negative/PrimitiveCallerSites.agda) / `wrong-context` | M | missing → **met** |
| C08 — [Core] 1273–1832; D-MASK | [CallerCancellation](Rules/CallerCancellation.agda) `plan` at `localAddress`: close captured socket/reservation. | [local-address](Negative/PrimitiveCallerSites.agda) | [protected](Negative/PrimitiveCallerSites.agda) / `wrong-context` | M | missing → **met** |
| C09 — [Core] 1273–1832; D-MASK | [CallerCancellation](Rules/CallerCancellation.agda) `plan` at `updateAddress`: close captured socket/reservation. | [update-address](Negative/PrimitiveCallerSites.agda) | [protected](Negative/PrimitiveCallerSites.agda) / `wrong-context` | M | missing → **met** |
| C10 — [Core] 1273–1832; D-MASK | [CallerCancellation](Rules/CallerCancellation.agda) `plan` at `forkHandler`: close captured socket/reservation. | [fork](Negative/PrimitiveCallerSites.agda) | [protected](Negative/PrimitiveCallerSites.agda) / `wrong-context` | M | missing → **met** |
| C11 — [Core] 1273–1832; D-MASK | [CallerCancellation](Rules/CallerCancellation.agda) `plan` at `connectedCommit before handoff`: forkedBeforeHandoff cleanup retains pre-handoff resource ownership. | [before-handoff](Negative/PrimitiveCallerSites.agda) | [protected](Negative/PrimitiveCallerSites.agda) / `wrong-context` | M | missing → **met** |
| C12 — [Core] 1273–1832; D-MASK | [CallerCancellation](Rules/CallerCancellation.agda) `plan` at `connectedCommit after handoff`: ordinary abandon; handler owns cleanup. | [after-handoff](Negative/PrimitiveCallerSites.agda) | [protected](Negative/PrimitiveCallerSites.agda) / `wrong-context` | M | missing → **met** |
| C13 — [Core] 1273–1832; D-MASK | [CallerCancellation](Rules/CallerCancellation.agda) `plan` at `awaitResult`: detach caller; handler/promise survive. | [await-result](Negative/PrimitiveCallerSites.agda) | [protected](Negative/PrimitiveCallerSites.agda) / `wrong-context` | M | missing → **met** |
| C14 — [Core] 1273–1832; D-MASK | [CallerCancellation](Rules/CallerCancellation.agda) `plan` at `commitResult`: detach caller; committed heap writes survive. | [commit-result](Negative/PrimitiveCallerSites.agda) | [protected](Negative/PrimitiveCallerSites.agda) / `wrong-context` | M | missing → **met** |
| C15 — [Core] 1273–1832; D-MASK | [CallerCancellation](Rules/CallerCancellation.agda) `plan` at `waitingInbound`: detach caller; captured inbound handler survives. | [wait-inbound](Negative/PrimitiveCallerSites.agda) | [protected](Negative/PrimitiveCallerSites.agda) / `wrong-context` | M | missing → **met** |
| C16 — [Core] 1273–1832; D-MASK | [CallerCancellation](Rules/CallerCancellation.agda) `plan` at `complete`: detach before API-return consumption. | [complete](Negative/PrimitiveCallerSites.agda) | [protected](Negative/PrimitiveCallerSites.agda) / `wrong-context` | M | missing → **met** |
| C17 — Captured cleanup close/remove: [Core] 1453–1465; D-MASK | `closeError`/`removeError`: ordinary delivery refused; synchronous close failure may replace the exception and skip removal. | [ordinary-close-throws](Negative/GovernorPool.agda); [close-protected](Negative/PrimitiveCallerSites.agda) / `remove-protected` | [protected-cleanup-rejects-delivery](Negative/GovernorPool.agda) | M | met → **met** |
| C18 — Release caller delivery while waiting/sending: [Core] 1834–2060; D-MASK | `start ordinary` detaches release frame, preserving entry writes, timer choice and unsent pruning targets; no target receipt or caller result fabricated. | [idle-release-delivery](Negative/GovernorPool.agda) / `prune-release-delivery` | [cancelled-release-cannot-resume](Negative/GovernorPool.agda) / `release-does-not-return` | M | met → **met** |

### Physical handler, startup and mux callback delivery sites

| ID / primitive and pinned source | Existing model rule | Enabled example | Refusal / rollback control | IO / IOSim | Before → after |
| --- | --- | --- | --- | --- | --- |
| H01 — Masked setup, blocked supplied operation: [Handler] 386–391, 468–473; D-MASK | [HandlerSupervision](HandlerSupervision.agda) `deliverBlockedSetupCancellation` bypasses the later handshake catch and promise write. | [observed-blocking-setup-delivery](Negative/HandlerSupervision.agda) | [setup-is-not-handshake-catch](Negative/HandlerSupervision.agda) / `setup-cannot-invent-catch-publication` | M | met → **met** |
| H02 — Unmasked handshake: [Handler] 392–400, 474–481; D-MASK | Receipt → caught result → rethrow → finally; promise and Async result remain separate. | [handshake-delivery-acknowledged](Negative/HandlerSupervision.agda) / `actual-catch-publishes` | [wrong-worker-refused](Negative/HandlerSupervision.agda) / `no-result-at-receipt` | M | met → **met** |
| S01 — Blocked buffer acquisition: [Handler] 437, 511; D-MASK | [MuxStartupUnwind](MuxStartupUnwind.agda) `blockedBufferAcquire` only at published; route beforeBuffer. | [buffer-delivery](Negative/PrimitiveStartupSites.agda) | [buffer-after-acquire-refused](Negative/PrimitiveStartupSites.agda) | M | missing → **met** |
| S02 — Blocked bearer setup: [Handler] 438, 512; D-MASK | `blockedBearer` only at bufferReady; provider scope remains outstanding. | [bearer-delivery](Negative/PrimitiveStartupSites.agda) | [bearer-before-acquire-refused](Negative/PrimitiveStartupSites.agda) | M | missing → **met** |
| S03 — [Handler] 439, 513; [Mux] 398–426; D-MASK | `asyncRoute unmaskedStartup` at `runEntered`; bufferOnly before pool, poolBody after pool entry. | [run-entry](Negative/PrimitiveStartupSites.agda) (permission); [a-edge1](Negative/MuxStartupUnwindBranches.agda) (pool route step) | [masked-fork-refused](Negative/PrimitiveStartupSites.agda) | M | missing → **met** |
| S04 — [Handler] 439, 513; [Mux] 398–426; D-MASK | `asyncRoute unmaskedStartup` at `startingTraced`; bufferOnly before pool, poolBody after pool entry. | [starting](Negative/PrimitiveStartupSites.agda) (permission); [a-edge1](Negative/MuxStartupUnwindBranches.agda) (pool route step) | [masked-fork-refused](Negative/PrimitiveStartupSites.agda) | M | missing → **met** |
| S05 — [Handler] 439, 513; [Mux] 398–426; D-MASK | `asyncRoute unmaskedStartup` at `egressReady`; bufferOnly before pool, poolBody after pool entry. | [egress](Negative/PrimitiveStartupSites.agda) (permission); [a-edge1](Negative/MuxStartupUnwindBranches.agda) (pool route step) | [masked-fork-refused](Negative/PrimitiveStartupSites.agda) | M | missing → **met** |
| S06 — [Handler] 439, 513; [Mux] 398–426; D-MASK | `asyncRoute unmaskedStartup` at `poolReady`; bufferOnly before pool, poolBody after pool entry. | [pool](Negative/PrimitiveStartupSites.agda) (permission); [a-edge1](Negative/MuxStartupUnwindBranches.agda) (pool route step) | [masked-fork-refused](Negative/PrimitiveStartupSites.agda) | M | missing → **met** |
| S07 — [Handler] 439, 513; [Mux] 398–426; D-MASK | `asyncRoute unmaskedStartup` at `muxerRegistered j`; bufferOnly before pool, poolBody after pool entry. | [muxer](Negative/PrimitiveStartupSites.agda) (permission); [a-edge1](Negative/MuxStartupUnwindBranches.agda) (pool route step) | [masked-fork-refused](Negative/PrimitiveStartupSites.agda) | M | missing → **met** |
| S08 — [Handler] 439, 513; [Mux] 398–426; D-MASK | `asyncRoute unmaskedStartup` at `demuxerRegistered j k`; bufferOnly before pool, poolBody after pool entry. | [demuxer](Negative/PrimitiveStartupSites.agda) (permission); [a-edge1](Negative/MuxStartupUnwindBranches.agda) (pool route step) | [masked-fork-refused](Negative/PrimitiveStartupSites.agda) | M | missing → **met** |
| S09 — [Handler] 439, 513; [Mux] 398–426; D-MASK | `asyncRoute unmaskedStartup` at `matureTraced j k`; bufferOnly before pool, poolBody after pool entry. | [mature](Negative/PrimitiveStartupSites.agda) (permission); [a-edge1](Negative/MuxStartupUnwindBranches.agda) (pool route step) | [masked-fork-refused](Negative/PrimitiveStartupSites.agda) | M | missing → **met** |
| S10 — Configured lane startup: [Mux] 411–419; D-MASK | [MuxStartupUnwind](MuxStartupUnwind.agda) `unmaskedConfiguredStartup` at cfgReady/cfgMature; distinct pre-cell observed site at cfgBeforePool. Existing real counter retirement precedes buffer handoff. | [PrimitiveConfiguredStartup](Negative/PrimitiveConfiguredStartup.agda), [PrimitiveConfiguredRetirement](Negative/PrimitiveConfiguredRetirement.agda): actual receipt and pool/retire/handoff suffix. | Same fixtures: masked insertion gaps, partial pool, wrong site, registration after fault and duplicate transfer refusals. Legacy [configured-not-covered](Negative/PrimitiveStartupSites.agda) still concerns only the old site. | M | missing → **met** |
| S11 — [Mux] monitor callbacks; [IG] mux tracer; D-MASK | [MuxRuntime](Rules/MuxRuntime.agda) `interruptibleCallback (readActive …)` in restored unmasked body; committed callback prefix survives receipt. | [read-active](Negative/PrimitiveStartupSites.agda) (permission); [h-edge1](Negative/MuxCallbackCancellation.agda); [h-edge1](Negative/MuxCallbackCommitted.agda) | [returned-refused](Negative/PrimitiveStartupSites.agda); [no-abandoned-commit](Negative/MuxCallbackCancellation.agda) | M | missing → **met** |
| S12 — [Mux] monitor callbacks; [IG] mux tracer; D-MASK | [MuxRuntime](Rules/MuxRuntime.agda) `interruptibleCallback (commitTrace …)` in restored unmasked body; committed callback prefix survives receipt. | [commit-trace](Negative/PrimitiveStartupSites.agda) (permission); [h-edge1](Negative/MuxCallbackCancellation.agda); [h-edge1](Negative/MuxCallbackCommitted.agda) | [returned-refused](Negative/PrimitiveStartupSites.agda); [no-abandoned-commit](Negative/MuxCallbackCancellation.agda) | M | missing → **met** |
| S13 — [Mux] monitor callbacks; [IG] mux tracer; D-MASK | [MuxRuntime](Rules/MuxRuntime.agda) `interruptibleCallback (afterStart …)` in restored unmasked body; committed callback prefix survives receipt. | [after-start](Negative/PrimitiveStartupSites.agda) (permission); [h-edge1](Negative/MuxCallbackCancellation.agda); [h-edge1](Negative/MuxCallbackCommitted.agda) | [returned-refused](Negative/PrimitiveStartupSites.agda); [no-abandoned-commit](Negative/MuxCallbackCancellation.agda) | M | missing → **met** |
| S14 — [Mux] monitor callbacks; [IG] mux tracer; D-MASK | [MuxRuntime](Rules/MuxRuntime.agda) `interruptibleCallback (afterFailure …)` in restored unmasked body; committed callback prefix survives receipt. | [after-failure](Negative/PrimitiveStartupSites.agda) (permission); [h-edge1](Negative/MuxCallbackCancellation.agda); [h-edge1](Negative/MuxCallbackCommitted.agda) | [returned-refused](Negative/PrimitiveStartupSites.agda); [no-abandoned-commit](Negative/MuxCallbackCancellation.agda) | M | missing → **met** |

### Pre-publication and post-pool delivery sites

| ID / primitive and pinned source | Existing model rule | Enabled example | Refusal / rollback control | IO / IOSim | Before → after |
| --- | --- | --- | --- | --- | --- |
| U01 — [Handler] 406, 426, 487, newMux helper; D-MASK | [MuxPublicationUnwind](MuxPublicationUnwind.agda) observed blocked masked tracer; no handshake-catch/promise write or pool adoption. | [observe](Negative/MuxPublicationUnwind.agda) `successAsync` | [published-handler-is-not-prepublication](Negative/MuxPublicationUnwind.agda) / `no-late-publication` | M/H | met → **met** |
| U02 — [Handler] 406, 426, 487, newMux helper; D-MASK | [MuxPublicationUnwind](MuxPublicationUnwind.agda) observed blocked masked tracer; no handshake-catch/promise write or pool adoption. | [observe](Negative/MuxPublicationUnwind.agda) `newMuxAsync` | [published-handler-is-not-prepublication](Negative/MuxPublicationUnwind.agda) / `no-late-publication` | M/H | met → **met** |
| U03 — [Handler] `newMux` scheduled setup; D-MASK | `observeFailure egressRule (async err)` after preceding setup step. Requires observed blocking in supplied action/tracer or retrying install transaction; the PC alone does not prove blocking. | [rule-async](Negative/MuxEgressSetupUnwind.agda) | [rule-after-rule-refused](Negative/MuxEgressSetupUnwind.agda) / `plain-rule-refused` | M | met → **met** |
| U04 — [Handler] `newMux` scheduled setup; D-MASK | `observeFailure rankInstall (async err)` after preceding setup step. Requires observed blocking in supplied action/tracer or retrying install transaction; the PC alone does not prove blocking. | [install-async](Negative/MuxEgressSetupUnwind.agda) | [install-before-rule-refused](Negative/MuxEgressSetupUnwind.agda) / `plain-rule-refused` | M | met → **met** |
| U05 — [Handler] `newMux` scheduled setup; D-MASK | `observeFailure rankTrace (async err)` after preceding setup step. Requires observed blocking in supplied action/tracer or retrying install transaction; the PC alone does not prove blocking. | [trace-async](Negative/MuxEgressSetupUnwind.agda) | [trace-before-install-refused](Negative/MuxEgressSetupUnwind.agda) / `plain-rule-refused` | M | met → **met** |
| U06 — Allocation/strict Handle: [Handler] `newMux`, 427–436, 500–510; D-EVAL | Allocation may synchronously force lazy protocol elements. No async delivery inside atomic allocation or at pure strictHandle; driver already forced handshake data. | [prefix14](Negative/MuxPublicationUnwind.agda) (normal allocation); [observe](Negative/MuxPublicationUnwind.agda) `allocationSync`; [forcing probe](SourceReplay/HandshakeForcing.hs) | [allocation-async-refused](Negative/PrimitiveStartupSites.agda) / `strict-async-refused`; [pure-handle-is-not-sync-failure](Negative/MuxPublicationUnwind.agda) | H | met → **met** |
| K01 — Post-close catch caller tracer: [Mux] 431–434; D-MASK | [MuxCatchUnwind](MuxCatchUnwind.agda) `blockedCallerTracer`; closed pool and matching failed status required; replacement escapes same catch. | [edge1](Negative/MuxCatchUnwind.agda) | [no-delivery-at-ordinary-STM](Negative/MuxCatchUnwind.agda) / `no-delivery-after-Dead-return` | M | met → **met** |
| K02 — Post-close catch full IG Dead transaction: [Mux] 433; [IG] Dead callback; D-MASK | `retryingIGDead` requires actual full-queue retry; ordinary ready STM is not interruptible masked delivery. | [retry-admits-masked-delivery](Negative/MuxCatchUnwind.agda) | [no-queue-delivery-with-room](Negative/MuxCatchUnwind.agda) / `retry-retains-source-and-queue` | M | met → **met** |
| K03 — DeltaQ tracer: [Mux] protocol completion; D-MASK | [MuxDeltaQ](MuxDeltaQ.agda) `observeException … (async err)` only while invoked; close/unwind retains prior Dead/queue effects. | [observe-exception](Negative/MuxDeltaQEffects.agda) `cleanCompletion (R.async err)` / `errorCompletion (R.async err)` | [no-exception-without-invocation](Negative/MuxDeltaQ.agda); [Close.no-return-after-throw](Negative/MuxDeltaQEffects.agda) | M | met → **met** |
| K04 — Initiator first-leg mux tracer: [Mux] initiator completion; D-MASK | `observeInitiatorException`: first-leg failure cannot invent DeltaQ or callback return. | [observe-exception](Negative/MuxInitiatorTraceEffects.agda) `cleanCompletion (R.async err)` / `errorCompletion (R.async err)` | [Close.no-DeltaQ-after-first-leg-throw](Negative/MuxInitiatorTraceEffects.agda) / `Close.no-return-after-throw` | M | met → **met** |
| K05 — [Handler] classifier/provider scopes; D-MASK | [MuxExitCancellation](MuxExitCancellation.agda) `bufferBlock` observes blocked provider/tracer/throwTo; pure policy/rethrow stages have no receipt. | [buf-edge4](Negative/MuxExitCancellation.agda) | [buffer-wrong-phase-refused](Negative/PrimitiveExitSites.agda) | M | met → **met** |
| K06 — [Handler] classifier/provider scopes; D-MASK | [MuxExitCancellation](MuxExitCancellation.agda) `errorTraceBlock` observes blocked provider/tracer/throwTo; pure policy/rethrow stages have no receipt. | [trace-edge](Negative/MuxExitCancellation.agda) | [trace-wrong-phase-refused](Negative/PrimitiveExitSites.agda) | M | met → **met** |
| K07 — [Handler] classifier/provider scopes; D-MASK | [MuxExitCancellation](MuxExitCancellation.agda) `nodeSendBlock` observes blocked provider/tracer/throwTo; pure policy/rethrow stages have no receipt. | [node-edge](Negative/MuxExitCancellation.agda) | [send-before-policy-refused](Negative/PrimitiveExitSites.agda) | M | missing → **met** |

### IG, jobs and outer scope delivery sites

| ID / primitive and pinned source | Existing model rule | Enabled example | Refusal / rollback control | IO / IOSim | Before → after |
| --- | --- | --- | --- | --- | --- |
| I01 — [IG] 194–235, 242–278; [Core] release/promote callers; D-MASK | [ServerIGExit](ServerIGExit.agda) `loopBoundary`: restored/unmasked sampleTime loop boundary. | [loop-enabled](Negative/PrimitiveIGSites.agda) (permission) | [loop-wrong-pc-refused](Negative/PrimitiveIGSites.agda) | M | missing → **met** |
| I02 — [IG] 194–235, 242–278; [Core] release/promote callers; D-MASK | [ServerIGExit](ServerIGExit.agda) `batchWait`: restored/unmasked awaitBatch. | [batch-enabled](Negative/PrimitiveIGSites.agda) (permission) | [batch-wrong-pc-refused](Negative/PrimitiveIGSites.agda) | M | missing → **met** |
| I03 — [IG] 194–235, 242–278; [Core] release/promote callers; D-MASK | [ServerIGExit](ServerIGExit.agda) `releaseRead`: masked transaction whose readTMVar retries on taken map. | [release-read-enabled](Negative/PrimitiveIGSites.agda) (permission) | [release-read-ready-refused](Negative/PrimitiveIGSites.agda) | M | missing → **met** |
| I04 — [IG] 194–235, 242–278; [Core] release/promote callers; D-MASK | [ServerIGExit](ServerIGExit.agda) `releaseCounters`: masked counter read whose readTMVar retries on taken map. | [release-counters-enabled](Negative/PrimitiveIGSites.agda) (permission) | [release-counters-ready-refused](Negative/PrimitiveIGSites.agda) | M | missing → **met** |
| I05 — [IG] 194–235, 242–278; [Core] release/promote callers; D-MASK | [ServerIGExit](ServerIGExit.agda) `releaseSend`: observed blocked release throwTo; no receiver acknowledgment. | [release-send-enabled](Negative/PrimitiveIGSites.agda) (permission) | [release-send-before-request-refused](Negative/PrimitiveIGSites.agda) | M | missing → **met** |
| I06 — [IG] 194–235, 242–278; [Core] release/promote callers; D-MASK | [ServerIGExit](ServerIGExit.agda) `promoteRead`: masked promotion transaction with taken map. | [promote-read-enabled](Negative/PrimitiveIGSites.agda) (permission) | [promote-read-ready-refused](Negative/PrimitiveIGSites.agda) | M | met → **met** |
| I07 — [IG] 194–235, 242–278; [Core] release/promote callers; D-MASK | [ServerIGExit](ServerIGExit.agda) `promoteCounters`: masked promotion counters with taken map. | [promote-counters-enabled](Negative/PrimitiveIGSites.agda) (permission) | [promote-counters-ready-refused](Negative/PrimitiveIGSites.agda) | M | missing → **met** |
| I08 — [IG] 194–235, 242–278; [Core] release/promote callers; D-MASK | [ServerIGExit](ServerIGExit.agda) `promoteSend`: observed blocked promotion/prune throwTo; retains unsent tail. | [promote-send-enabled](Negative/PrimitiveIGSites.agda) (permission) | [promote-send-before-request-refused](Negative/PrimitiveIGSites.agda) | M | missing → **met** |
| I09 — DemoteRemote restored boundary: [Core] demoteRemote; [IG] handler; D-MASK | `unmaskedDemote` admits transaction/assertion/counters/returning only for demote, not masked promote. | [demote1](Negative/ServerIGExitCases.agda); [demote-transaction](Negative/PrimitiveIGSites.agda) / `demote-assertion` / `demote-counters` / `demote-return` | [promote-is-not-unmasked-demote](Negative/PrimitiveIGSites.agda); [no-masked-assertion-receipt](Negative/ServerIGExitCases.agda) | M | met → **met** |
| I10 — Final IG catch tracer: [IG] 194–235; D-MASK | Invoked final callback may block masked interruptibly; replacement escapes and retains pending row, original receipt and registry. | [AsyncFailure.fail-step](Negative/ServerIGExitControls.agda) | [AsyncFailure.no-false-return](Negative/ServerIGExitControls.agda) / `no-failure-before-invocation` | M | met → **met** |
| J01 — Restored job body versus masked publication/deregister: [JobPool] 123–164; D-MASK | [JobPoolKernel](Rules/JobPoolKernel.agda) delivers only to bodyRunning; async exceptions bypass synchronous handler/result publication. | [cancel₃](Negative/JobPoolLifecycle.agda) | [queued-normal-does-not-accept-fake-cancel](Negative/JobPoolLifecycle.agda) / `cancelled-body-does-not-publish-fake-failure` | M | met → **met** |
| J02 — PSA monitor normal body/normal finish and parent gap: [Actions] monitoring/fork; [JobPool]; D-MASK | [PeerSupervision](PeerSupervision.agda) observing and normalFinishing deliverable; own masked insertion blocks receipt without blocking other parents. | [registered-parent-delivery](Negative/PeerSupervisionScenarios.agda) / `second-cancellation-not-blocked-by-first-mask` | [masked-parent-refuses-delivery](Negative/PeerSupervisionScenarios.agda) / `first-parent-still-masked` | M | met → **met** |
| J03 — PSA synchronous-handler Cold wait: [Actions] monitoring catch; D-MASK | `monitorDeliverable true (errorWait …)` observes blocked STM; ordinary flag cannot invent this masked wait window. | [blocked-wait-is-interruptible](Negative/PeerSupervisionScenarios.agda) | [ordinary-cancel-cannot-invent-masked-wait-window](Negative/PeerSupervisionScenarios.agda) | M | met → **met** |
| J04 — Outer churn/governor/root/ledger scope receipt: [Diffusion] 930–950; D-ASYNC + D-MASK | [AsyncScope](Rules/AsyncScope.agda) separate request/delivery/body/result/join, ordered owner traversal. Provider bodies are opaque restored-action observations, not an audit of DNS/ledger internals. | [outer-step3](Negative/PeerSupervisionScenarios.agda)–`outer-step26` | [governor-async-body-cannot-outrun-own-pool](Negative/PeerSupervisionScenarios.agda) / `local-root-join-precedes-ledger` | A/M | met → **met** |
| J05 — Relays scope receipt: [Diffusion] withPoolRelays; D-ASYNC | [PoolRelays](Rules/PoolRelays.agda) request after callback return, delivery, result, join; already failed relays only waited for; no normal body return. | [c3](Negative/PoolRelays.agda) / `late-cancel-keeps-result` | [join-without-cancel-refused](Negative/PoolRelays.agda) / `nothing-to-deliver` | A/M | met → **met** |
| J06 — Server owner cancellation/raw admission worker cancellation: [Server] 165–180, 239–254; D-ASYNC + D-MASK | [ServerAdmission](ServerAdmission.agda) owned action/IG/accept-loop unwind; raw admission worker separate cancel/close/result suffix. Source bare async does not give the Server ownership of that child. | [Interleaving.initialized-interrupt](Negative/ServerPeers.agda); [recovery1](Negative/ServerAdmission.agda) | [no-result-before-worker-close](Negative/ServerAdmission.agda) / `no-fake-worker-result` | A/M | met → **met** |
| J07 — Raw admission async fork failure: [Server] 239–252; D-ASYNC | [ServerAdmission](ServerAdmission.agda) `forkFailure`, `closeForkFailure`, `finishForkFailure`: synchronous pre-birth failure reserves acceptPending socket; separate close and propagation, retaining replacement close error. Parent remains masked; no ordinary async receipt at fork. | [PrimitiveAdmissionFork](Negative/PrimitiveAdmissionFork.agda): initialized pre-birth failure/close/propagation/listener path. | Same fixture: no fabricated worker/handler, no pending socket reuse, premature propagation, repeated close and wrong-stage refusals. | A/M | missing → **met** |
| X01 — Unmasked include body exception while map taken, including after handler fork: [Core] 801–880, 2373–2379; D-MASK | [ServerAdmission](ServerAdmission.agda) `workerException` / `workerRestore`, [Server](Rules/Server.agda) `restoreBody`: capture original fault, separately restore saved map masked, then close/result. Heap, promise and physical child are retained. | [PrimitiveIncludeRestoration](Negative/PrimitiveIncludeRestoration.agda): all five body sites, before/after-fork restoration and separate close/result. | Same fixture: no heap/child rollback, wrong lease, premature close/result, normal publication after receipt, raw restore alias, second masked receipt and post-publication rollback refusals. | M | missing → **met** |

## Findings and remaining acceptance work

All five findings are implemented rather than excluded. The source pin and the
90-row inventory stay fixed. Existing theorem statements are retained; proof
consumers receive new cases and lemmas. The impact plan and check record (session-local, not retained)
records batch boundaries, development diagnostics, commands, wall times, peak RSS
and deferred regressions. [Increment 80](Supervision.md#eightieth-increment-g1-primitive-runtime-closure)
summarizes the runtime changes and acceptance boundary.

| Finding / row | Implemented behavior and focused evidence |
| --- | --- |
| **F1 / X01** | Captured unmasked body fault → masked saved-map restoration → separate outer socket close/result. [PrimitiveIncludeRestoration](Negative/PrimitiveIncludeRestoration.agda) retains committed entry/promise writes and the actual child after fork. A symbolic pre-fork child reference is not a physical birth or an evaluation model of the source's lazy mfix value. |
| **F2 / S10** | Configured restored-body sites preserve masked registration gaps and actual pool/counter ownership. [PrimitiveConfiguredStartup](Negative/PrimitiveConfiguredStartup.agda) and [PrimitiveConfiguredRetirement](Negative/PrimitiveConfiguredRetirement.agda) distinguish pre-cell, pool-body, retirement and buffer handoff. |
| **F3 / T10** | Explicit spent-timer expiry and rearm retain the request, while grant/cancel retain the existing charge rules. [PrimitiveGrantRefresh](Negative/PrimitiveGrantRefresh.agda) exercises repeated cycles through the real IG dispatcher. Ready-versus-expired winner, ranks and token availability remain supplied observations. |
| **F4 / T09** | The helper distinguishes protocol deadline/size failures returned as Left, thrown bearer SDU timeout, and inbound query publication/trace/delay. [PrimitiveHandshakeContinuation](Negative/PrimitiveHandshakeContinuation.agda) joins actual publication and outer finally/results, with a real CM cancellation request/receipt/acknowledgement path. These local paths do not supply G2's initialized negotiation-failure witness. |
| **F5 / J07** | Pre-birth async-operation failure reserves the accepted socket without a raw worker; close and loop-failure propagation are separate. [PrimitiveAdmissionFork](Negative/PrimitiveAdmissionFork.agda) checks successful/throwing close, no fabricated birth and no socket-token reuse. The accept-loop result payload retains the existing abstraction. |

Primitive coverage is **90 met / 0 missing**. **G1 is awaiting capped regression
acceptance**, rather than a missing primitive rule. G0's executable selection/seed
and protocol-resource contracts, G2's combined lifecycle paths and G3–G5 remain
independent obligations. No new native build/replay is claimed.

The scope also excludes unused `forcePromise`, OS/FFI and GHC GC machinery,
listener rate-limit and ECONNABORTED delays, whole-node boot, Windows timeout
implementation, full DNS/ledger bodies and per-protocol contents. Existing
policy jitter/backoff and monotonic samples are external inputs described in
[BranchMatrix](BranchMatrix.md#the-profile-actually-exercised), rather than
claims about execution of `threadDelay` or a concrete PRNG. LeiosDB waits are
per-protocol supplied contracts documented in [SourceReplay](SourceReplay/README.md#m6-revalidation-at-network-2f1c154-9-november-2026),
not a newly modeled SQLite/async primitive. Local source/model equations, source
contract inspection and historical implementation replays remain separate.

## New fixture validation

The following is the **12 November inventory-only checkpoint**. It is retained
as historical evidence; the 13 November runtime edits and regression results are
in [increment 80](Supervision.md#eightieth-increment-g1-primitive-runtime-closure)
and the working check record (session-local, not retained).

The seven new modules contain only computational `refl` equations over existing
rules/predicates. Their comments distinguish local permission checks, local
source dispatch and initialized older paths. No existing Agda module, dependency,
project build setting or theorem statement changed. There are no downstream
consumers of these new fixtures; each is its own focused endpoint. Only each
new module's own interface was invalidated for the final fresh check; dependency
interfaces were reused. No cache purge or heavy Cardano_network endpoint was run.

Command for **each row**, from the library root (substitute the listed filename):

```sh
agda ConnectionManagement/Negative/<file>.agda +RTS -M20G -A128m -RTS
```

Checks ran serially with `/usr/bin/time -v`. An external RSS watchdog would stop
a process above 9,500,000 KiB (about 9.1 GiB); it never triggered. The 20 GiB RTS
heap ceiling was retained exactly as requested. Times below are individual wall
times, including the time wrapper; peak RSS is the Agda invocation's measured
maximum, not its configured heap ceiling. Each final log contains its own
`Checking ConnectionManagement.Negative.…` line and exits zero without warnings.

| New fixture module (`.agda` filename) | Wall time | Peak RSS | Result |
| --- | ---: | ---: | --- |
| [PrimitiveMap](Negative/PrimitiveMap.agda) | 5.425 s | 854,724 KiB (0.815 GiB) | **pass**, fresh |
| [PrimitiveTimers](Negative/PrimitiveTimers.agda) | 5.727 s | 853,620 KiB (0.814 GiB) | **pass**, fresh |
| [PrimitiveCallerSites](Negative/PrimitiveCallerSites.agda) | 5.726 s | 908,988 KiB (0.867 GiB) | **pass**, fresh |
| [PrimitiveStartupSites](Negative/PrimitiveStartupSites.agda) | 18.232 s | 2,282,700 KiB (2.177 GiB) | **pass**, fresh |
| [PrimitiveIGSites](Negative/PrimitiveIGSites.agda) | 7.996 s | 1,305,084 KiB (1.245 GiB) | **pass**, fresh |
| [PrimitiveResults](Negative/PrimitiveResults.agda) | 5.580 s | 859,892 KiB (0.820 GiB) | **pass**, fresh |
| [PrimitiveExitSites](Negative/PrimitiveExitSites.agda) | 6.636 s | 940,192 KiB (0.897 GiB) | **pass**, fresh |

Total final check wall time: **55.322 s**. Peak across serial checks: **2.177 GiB**.

Logs, time reports, source/dependency extracts, working row inventory and check
JSON records are under `/tmp/cm-g1-20261112/`. During drafting, one startup
fixture failed scope checking (private module alias; exit 42, 9.646 s,
1,698,588 KiB); its aliases were repaired without changing model rules, then it
passed. That failed check is not acceptance evidence. No other draft failure,
RSS interruption, Haskell build, source replay, broad endpoint rebuild or
term-level dependency axiom audit is claimed.

The targeted static proof audit covers all seven new modules. Local Markdown
links and named fixture declarations were checked separately. Source facts here
come from the pinned source and resolved archives; passing model checks do not
establish Haskell refinement, universal liveness, successful cancellation of
arbitrary providers, or eventual shutdown.

[Classes]: https://chap.intersectmbo.org/package/io-classes-1.8.0.1.tar.gz
[Sim]: https://chap.intersectmbo.org/package/io-sim-1.8.0.1.tar.gz
[Async]: https://hackage.haskell.org/package/async-2.2.6/async-2.2.6.tar.gz
[Timeout]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/network-mux/src/Network/Mux/Timeout.hs
[Core]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs
[CMTypes]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Types.hs
[Sync]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/monoidal-synchronisation/src/Data/Monoid/Synchronisation.hs
[JobPool]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/network-mux/src/Control/Concurrent/JobPool.hs
[Info]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor/InformationChannel.hs
[Mux]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/network-mux/src/Network/Mux.hs
[Handler]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionHandler.hs
[IG]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/InboundGovernor.hs
[Server]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/Server.hs
[Diffusion]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/lib/Ouroboros/Network/Diffusion.hs
[Active]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/lib/Ouroboros/Network/PeerSelection/Governor/ActivePeers.hs
[Actions]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerStateActions.hs
[Bucket]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/network-mux/src/Network/Mux/Egress/Bucket.hs


[HandshakeHelper]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/Protocol/Handshake.hs#L82-L95
[DriverLimits]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/Driver/Limits.hs#L139-L140
