# Design-variant acceptance contract

13 November 2026. Gate plan step 6: documentation acceptance for **owned
callers + Server-owned admission workers joined without cancellation + a
historical CM handler registry swept before coordinator closure**. This is the
accepted model proposal. Increment 100 implements a pinned Haskell prototype
with [specific ordering differences](#model-and-prototype-ordering) and
[finite IOSim evidence](#prototype-result). Eventual shutdown remains open.
Authority: [DESIGN §1](DESIGN.md#1-objective-and-authority),
[Supervision increments 73–78](Supervision.md#seventy-third-increment-late-admission-after-the-cm-shutdown)
and [increment 78's phase C audit](Supervision.md#seventy-eighth-increment-admission-quiescence-step-2-design-exploration).

## 1. Source design and prototype boundary

Use network **`2f1c154f248659b89523d5679ca532f442e7ed2a`**, pinned by consensus
`2e44d98a843168ba3b189e305820b79943ac7d1e`; ranges below refer to that network
revision. Paths are under `ouroboros-network/framework/lib/Ouroboros/Network/`.
The [source ledger](SourceLedger.md) retains baseline/history distinctions.

- **Caller ownership.** Preserve the production ownership of outbound CM calls
  by governor peer jobs and monitors; do not allow arbitrary retained CM handles
  to start new calls during/after teardown. [OwnedCallers](Variants/OwnedCallers.agda)
  excludes raw foreign `beginAcquire`/`beginRelease`, including complete-plan
  aliases. This is an environment/API scope contract, not a shutdown flag already
  present in `Core.hs`.
- **Server worker registry and join.** Replace the discarded admission `Async`
  in [Server.hs:239–254][server-workers] with a retained physical handle.
  Protect fork plus registry insertion against parent interruption; the child
  must run with the original intended masking state. Stop and join accept loops
  before freezing this registry, then join every admission result **without
  cancelling the workers**, before entering CM shutdown or returning Server.
  Integrate this finalizer into every winner/exceptional unwind of the scoped
  action/IG/accept tree ([Server.hs:147–186][server-scopes]), not only normal
  callback return. Retain exception results with `waitCatch`-style observation;
  one failed worker must not skip the remaining joins.
- **Historical handler registry.** In `Core.hs`, retain the actual `Async` from
  both inbound ([839–879][core-inbound]) and outbound ([1532–1563][core-outbound])
  fork paths, independently of the live connection map. Registration must be
  inseparable from successful physical birth under exceptions: a masked parent
  fork/register section or an equivalent handshake must leave no unregistered
  child. The unmasked include body ([801–880][core-include]) and map restoration
  ([2373–2379][core-restore]) must not roll back this history. Keep handles across
  deletion, replacement and pruning; entry identity is not thread identity.
- **CM sweep and masking.** Extend the existing map-snapshot cancellation/wait
  finalizer ([Core.hs:524–550][core-shutdown]) with a historical-registry sweep.
  Retain the existing snapshot certificate. Skip completed handlers; request
  cancellation of pending ones through their actual delivery sites, then wait
  for every registered physical result before declaring the coordinator closed.
  Quiesce all owned callers before the final registry snapshot; closure must
  not race a new birth. Protect teardown against interruption that could bypass
  a join. Preserve `asyncWithUnmask` ([585–604][core-cleanup]), uninterruptible
  cleanup at 604, and the explicitly unmasked TIME_WAIT delay at 667–668 with
  its inner finally through 713. Do not make whole handler bodies permanently
  uninterruptible. Retain historical handles at least through the sweep; any
  earlier reclamation needs a separately justified result certificate.

## 2. Proved acceptance and limits

The current theorem types, not historical fixture counts, define acceptance.
All endpoint statements below concern finite runs in their declared runtime,
with fixed error classifiers and protocol capability parameter.

| Model evidence | Premises and guarantee |
| --- | --- |
| [Properties/OwnedCallers](Properties/OwnedCallers.agda), `Protocols.no-frames` | `T.initialize (O.initial c₀) g ≡ just start`, guarded `OuterRuns′` from `RR.initial scheduled` to `RR.finished`: no worker has an acquire or release frame. This theorem is for the OwnedCallers runtime; it is not silently a new combined-registry theorem. |
| [Properties/ServerOwnedHandlers](Properties/ServerOwnedHandlers.agda), `Protocols.si5`, `registry-si5` | Same explicit initializer, combined-variant `Executes` from `outer (initial start) (RR.initial scheduled)` to finished relays: original SI5 certificate, completed registry sweep and every registry result available. |
| Same module, `no-late-admission`, `no-late-fork` | Initialized combined run reaching `closingCM` or `serverReturned`: every raw admission worker is joined with an available result; its source admission map-take/fork is refused. These boundary theorems need not wait for finished relays. |
| Same module, `quiescence`, `historical-quiescence` | Initialized combined run reaching finished relays: `Quiescent` gives joined worker ownership, actual worker results, every registered result and every physical handler result. Any handler registered at an earlier run prefix also has its result at the endpoint. |
| Same module, `quiescent-covered` | From `Quiescent`, live-handler snapshot coverage follows because no physically pending handler remains. It does not assert that the old map snapshot contained every historical handler. |

[Variant](Variants/ServerOwnedHandlers.agda) and property `outer-erasure`
reuse source steps: joins/registry bookkeeping stutter, registry cancellation
relabels to existing physical observations. This relates model executions; it
neither inserts a registry into the pinned source nor proves Haskell conformance.
[OwnedCallersFixture](Negative/OwnedCallersFixture.agda) checks the policy and
foreign-begin refusals. [ServerOwnedHandlersFixture](Negative/ServerOwnedHandlersFixture.agda)
checks initialized finite progress for failed-handshake/self-purge and refuses
late admission, premature closure, acknowledgement and waits.

These are **safety at a reached endpoint**. They do not prove that an endpoint
is eventually reached, a shutdown deadline, fairness, or progress beyond the
finite runs. The model is untimed. Keep the one-listener/selected outer-scope
profile, explicit `O.initial` boundary and supplied transport/protocol/tracer
observations; arbitrary preloaded continuations and foreign callers are outside
this contract. Multiple listeners and full application bundles require additional
coverage. Increments [82](Supervision.md#eighty-second-increment-inbound-physical-release-receipt-and-clean-lifecycle),
[83](Supervision.md#eighty-third-increment-g2-outbound-clean-lifecycle-and-supervised-handshake-failure),
[84](Supervision.md#production-only-timeout-cooling-witness) and
[85](Supervision.md#eighty-fifth-increment-g3-initialized-concurrency-histories)
provide reduced finite lifecycle/concurrency evidence, not registry implementation
acceptance or whole-system progress. In particular, the production timeout path
stops the mux and lets handler finally dispose of the connection; it needs no
invented foreign CM release. The overlap endpoint deliberately retains live
handlers and is not a shutdown witness.

## 3. Explicit implementation progress assumptions

These are open obligations to validate or repair in the prototype, not premises
already discharged by the safety proofs:

- Runnable workers/handlers and their finalizers must be scheduled; map leases
  must be released and accept shutdown must stop new births. Fork/registration
  failures must close reserved resources without losing a child handle.
- The handshake timeout must bound the worker's actual handshake-result wait,
  including failure/query paths. A timeout alone is insufficient if a tracer or
  allocation failure before publication leaves the promise empty (CM-PUB1).
  Such paths need a guaranteed terminal publication or another explicit recovery
  mechanism before no-cancel joins can be accepted as terminating.
- Worker map/counter/socket operations and admission notification must finish.
  In particular, prove capacity/drain or another terminating policy for a bounded
  IG queue when workers finish after IG deactivation; do not assume an exited
  consumer drains later writes. Any changed shutdown order needs correspondence
  evidence against the variant boundary.
- Handler cancellation must reach a permitted site or find a completed result;
  mux/protocol shutdown, egress drain, buffer finalizers and socket cleanup must
  terminate. Cancellation of handlers preserves cleanup because its critical
  finalizer is uninterruptibly masked; that protection does **not** guarantee
  progress. Blocking tracers/counters/map waits there can prevent shutdown.
  TIME_WAIT must elapse or receive cancellation at its explicit unmasked delay,
  and its protected finally must still finish.
- Tracers and other foreign callbacks must satisfy stated termination/failure
  contracts. No exception from cancellation, tracing or result observation may
  abandon the remaining sweep. Joins may wait for recovery; a watchdog firing
  is a failed progress test, not permission to report quiescence.

## 4. Rejected designs and retained counterexamples

| Rejected variant | Why it fails / evidence |
| --- | --- |
| Own, cancel and join admission workers (phase A) | Cancellation after handler fork but before map publication restores the old map and can lose the child binding. Joining the worker does not join that child. [Increment 78](Supervision.md#seventy-eighth-increment-admission-quiescence-step-2-design-exploration) records the standalone async primitive-contract probe and post-publication control, not a CM/Server replay or maintained variant theorem. [HeapRollback](Negative/HeapRollback.agda) and [PrimitiveIncludeRestoration](Negative/PrimitiveIncludeRestoration.agda) preserve the model's saved-map/retained-child distinction. |
| [Own + join without cancellation, without historical handlers](Variants/ServerOwnedWorkers.agda) | [ServerOwnedWorkersFixture](Negative/ServerOwnedWorkersFixture.agda) refuses late `beginCM`, but [ServerOwnedWorkersCounterexample](Negative/ServerOwnedWorkersCounterexample.agda) leaves a failed-handshake handler in its catch after the worker deletes its binding and joins. [ServerOwnedWorkersSelfPurge](Negative/ServerOwnedWorkersSelfPurge.agda) leaves a successful admission's handler pending after self-purge. Both reach finished relays without handler quiescence. |
| Worker joins handler only on failure/query | The successful `Connected`/self-purge [counterexample](Negative/ServerOwnedWorkersSelfPurge.agda) bypasses that join. The other phase C routes below remain. A join on every successful admission would also change the worker lifetime/progress contract; it is not the explored failure/query-only fix. |

## 5. Pinned prototype and IOSim acceptance plan

Implement the outline in §1 in an isolated prototype at the exact network pin;
keep test instrumentation separate from production changes. Record source and
dependency versions, patch, exact schedules/bounds, physical Async observations
and cleanup order. This original plan predates the prototype result below.

1. Adapt [ServerLateAdmissionReplay.patch](SourceReplay/ServerLateAdmissionReplay.patch)
   and its [increment 73 record](SourceReplay/README.md#late-admission-after-the-cm-shutdown-10-november-2026).
   Delay Server's own accepted worker until teardown starts. Patched teardown
   must wait for that worker, then cover any handler it creates and return with
   all retained results available. Replay default and retained POR schedules;
   rerun at least the recorded 20,000 schedule / 20 branching bounds and report
   actual explored counts. On unpatched source retain the **failing quiescence
   control**: Server/CM can finish with the worker not started and the accepted
   connection unreleased. The direct retained-API test must still demonstrate
   unguarded include after return on the unpatched source. It is a scope-abuse
   control, not a promise that the owned-callers design supports escaped APIs.
   Preserve the fact that the historical POR and direct-API evidence are two
   traces; require a new instrumented single-trace worker test for the prototype.
2. Adapt [ServerHandlerSelfPurgeReplay.patch](SourceReplay/ServerHandlerSelfPurgeReplay.patch)
   and its [increment 78 record](SourceReplay/README.md#handler-self-purge-before-the-cm-returns-12-november-2026).
   After successful admission and worker join, pause the actual handler's cleanup
   counter tracer at Core 665, with an empty map and one socket close. Patched
   CM must remain pending until the gate opens and the handler result is joined;
   it must then return quiescent. Keep the no-pause control. Unpatched CM must
   still return with `pollSTM = Nothing` under the pause: the original tests
   pass by asserting this defect; a positive quiescence assertion must fail.
   Add the full Server/IG/accept-loop route, since the saved replay is direct-CM
   with a synthetic handshake/body. A permanently closed gate must block the
   patch, exposing the cleanup-termination assumption rather than bypassing it.
3. Extend replay coverage across **all phase C detachments**, checking physical
   birth/registry identity, pending result at detachment, and result before CM
   return: inbound failure/query deletion (897–904, 1007–1075); outbound deletion
   (1771–1830, especially 1795); ordinary self-purge (652–665); TIME_WAIT final
   purge (695–713), including the post-cleanup/pre-result tail; outbound bracket
   alias cleanup (1452–1471); reservation/fork before publication (1532–1552);
   same-entry overwrite/fresh-entry replacement (839–879, 1558–1563); pruning
   to Terminated (761–776); and pre-publication exception rollback (870–879,
   2376–2377). These are [pinned Core ranges][core-all]. Use controlled schedules
   with before/after-publication and completed-result controls. Collision/address
   reachability and rollback outside the selected worker exception model must
   be established separately; label synthetic contract tests accordingly.
4. Exercise normal, action-error, IG-first, accept-error and external-cancellation
   teardown; retain clean/handshake-failure/timeout and overlap controls from
   increments 82–85. Check original masks, no cancellation of admission workers,
   all registry results, no births after closure, and no discarded error that
   skips later joins. Include CM-PUB1 pre-publication faults and IG-queue pressure
   as progress tests. Broader listener/application claims require new coverage.

Step 6 is complete as a documentation contract and replay plan. The prototype
below implements the ownership outline; full source correspondence and progress
acceptance remain open. G0–G5 criteria are unchanged.

## Prototype result

16 November 2026. [QuiescentShutdownPrototype.patch](SourceReplay/QuiescentShutdownPrototype.patch)
implements Server admission retention/no-cancel joins and the CM historical
handler registry at the exact pin. Its six files add 695/remove 28 lines; only
60 additions/27 deletions are production code. The old map-snapshot cleanup and
handler masking/TIME_WAIT behavior are retained. Admissions join inside the IG
callback, after action/accept scopes unwind and before CM shutdown.

All eleven original defect/control properties reproduce on pristine production
code; four corresponding positive quiescence assertions fail there. The
prototype passes eighteen IOSim checks, including full Server self-purge,
pre-publication rollback, five teardown routes, strict shutdown and POR at
20,000/20 bounds (597 schedules per property). Four checks intentionally confirm
failed progress: permanently blocked cleanup at CM/Server scope, an unpublished
promise, and 101 producers after IG exit overflowing its capacity-100 queue.
Thus §3's publication and notification progress obligations **remain unsatisfied**;
this is conditional quiescence evidence, not a generally terminating fix.

Existing framework IOSim coverage passes 37 properties at 100 cases plus IG-race
at 10; IG-race at 100 hits the same 60-second limit on baseline and prototype.
Broader phase-C/detachment and deployment-contract acceptance in §5 remains open.
The [replay record](SourceReplay/README.md#quiescent-shutdown-prototype-increment-100)
contains exact fixtures, masks, physical observations, commands and exclusions.
No Agda was run or model theorem changed. Read-only Haskell Git metadata prevented
the requested local branch/commit; the durable edited checkout and standalone
patch are saved. Nothing was pushed.

## Model and prototype ordering

The model and prototype both require admission results before CM's snapshot
and historical handler results before completed shutdown. Their intermediate
steps and caller assumptions differ.

| Boundary | Agda design variant | Increment 100 Haskell prototype |
| --- | --- | --- |
| Admission joins and IG | `joinWorker` observes an available worker result. The variant requires all joins at entry to `closingCM`; the inherited `beginCM` transition additionally requires `igJoined`. This gate allows joins before or after IG exit, subject to those boundaries. | The admission bracket finalizer runs after action/accept scopes unwind, inside the IG callback. On the ordinary route IG can still consume notifications during the joins. If IG wins the race by failing first, later notifications can instead block an admission and prevent CM entry. |
| Historical sweep | `readRegistry` is enabled during `closingCM`. The cursor scans the snapshot, observing each target's available result or its cancellation receipt, then checks all results. `cmGate` requires a completed sweep and available registered results before the coordinator reaches `closed`. The rules permit the sweep to interleave with the inherited map-based shutdown. | The existing map-based finalizer runs first, and the sweep is its `finally` action. It takes a historical snapshot, polls results, sends cancellation to pending handlers and observes `waitCatch` in concurrent branches. The sweep can also run when that first finalizer exits by exception. If the first finalizer blocks, the sweep cannot begin. |
| Caller scope | `OwnedCallers` guards foreign outbound begins and the combined variant checks admission results and refuses late source map take/fork at the stated stages. | No closed-handle flag guards the API. The escaped-handle control still accepts a new include after Server return. Freezing the registry safely assumes callers remain within their owning scopes. |
| Establishing a guarantee | `registry-si5` and `quiescence` concern initialized finite runs that reach finished relays. `no-late-admission` and `no-late-fork` concern initialized runs reaching `closingCM` or `serverReturned`. | The tests observe selected physical results and join order, including self-purge and pre-publication map rollback. A correspondence proof would have to relate the additional sweep threads, trace/exception outcomes, and join/sweep order, with the same caller-scope premises. |

The model code and patch locate the ordering above. Keep these distinctions
when interpreting the IOSim progress failures and the model's endpoint proofs.
[ServerAdmission](ServerAdmission.agda), [ServerOwnedHandlers variant](Variants/ServerOwnedHandlers.agda),
[theorems](Properties/ServerOwnedHandlers.agda), [prototype patch](SourceReplay/QuiescentShutdownPrototype.patch),
[progress tests](SourceReplay/README.md#progress-findings-and-limits).

[server-workers]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/Server.hs#L239-L254
[server-scopes]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/Server.hs#L147-L186
[core-inbound]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L839-L879
[core-outbound]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L1532-L1563
[core-include]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L801-L880
[core-restore]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L2373-L2379
[core-shutdown]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L524-L550
[core-cleanup]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs#L580-L713
[core-all]: https://github.com/IntersectMBO/ouroboros-network/blob/2f1c154f248659b89523d5679ca532f442e7ed2a/ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs
