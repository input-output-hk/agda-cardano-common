# Handler reference-chain preservation

`Properties/HandlerReferences.agda` defines a propositional `Chain`: the original
handler exists, its promise contains a negotiated handle and data flow, the handle
points to the captured mux, and that mux has the handler's connection key. The
handler's captured entry and socket also exist. Entry existence does not require
current CM map membership; socket existence does not require an open socket.
Neither requires current IG registration.

`TrackedChain` additionally ties this chain to a worker's lifecycle frame.
`handler-step-preserves` preserves an existing tracked chain across every
successful `handlerStep`, including actions by a different worker. It uses the
actual dispatcher. No executable rule, guard, or validity filter was added.

The proof combines two independently useful facts:

- `HandlerEvolution` retains the frame's captured mux identity.
- `HandlerAnchors` preserves the installed handle table and existing mux keys,
  while permitting changes to mux status, jobs and callbacks.

`exec-preserves` extends this to finite executions whose actions are all
`handlerStep`. `CSP/HandlerReferences.raw-reachability-preserves` lifts that result
to the raw process-tree trace semantics, using the existing correspondence. A
checked normal-exit suffix closes the job pool and completes buffer release;
its start and end have concrete reference-chain certificates.

## Creation and coverage boundary

Preservation assumes a chain already exists. Attachment checks the presence of
handler, negotiated result, handle and mux, but does not check mux-key coherence
or captured entry/socket existence. `Negative/HandlerReferences.agda` constructs
three malformed configurations: wrong mux key, absent entry, and absent socket.
Attachment succeeds in each, while the existing runtime validity diagnostic
returns false. These are model boundary tests, not reachable source defects.

This is not the full `HandlerValidity.valid` invariant: phase, cleanup, and
unique-ownership obligations remain separate. The all-dispatcher uniqueness and
capture-retention theorems continue to hold. The original `HandlerReferences`
theorem covers only lifecycle actions; the extensions below add publication,
exit, cleanup, release, remote operations including pruning, every IG action,
Server admission and handshake consumers. `CSP/HandlerAll` covers every action
in the current dispatcher. The executable subsystem itself remains partial.
It proves neither progress nor liveness, and does not assert a result after hiding.

`Properties/HandlerAttachment.agda` now derives a new tracked chain from a
successful attachment and `CreationPremises`. These premises require entry/socket
existence for the actual handler and key coherence for the actual negotiated
handle/mux lookup chain. They do not assume the chain exists: attachment success
supplies the handler, result, handle and mux lookup witnesses.

`CSP/HandlerAttachment.raw-attachment-creates` combines creation with preservation
through any finite lifecycle-only suffix. A concrete registration fixture checks
that the worker is initially untracked and obtains a chain after attachment.
`Negative/HandlerAttachment.agda` proves that each of the three malformed fixtures
violates these premises, complementing their successful-attachment witnesses.

## Publication and exit coverage

`Properties/HandlerBoundaries.agda` extends preservation to handler publication
and handler exit, for any acting worker and any protected worker. A successful
publication inserts only into an empty promise-result slot, so it cannot replace
the negotiated result supporting an existing chain. Duplicate publication records
a fault without changing the world. Exit enters cleanup and changes the lifecycle
phase while retaining original references.

`HandlerActions` explicitly admits lifecycle, publication and exit actions.
`CSP/HandlerBoundaries` lifts preservation and conditional attachment creation to
raw traces with arbitrary finite interleavings of these actions. The original
lifecycle-only theorem APIs remain unchanged. Concrete witnesses cover duplicate
publication and the normal-exit suffix through cleanup entry.
`Negative/HandlerBoundaries` excludes raw traces that overwrite a filled promise,
repeat the recorded publication fault, or publish after cleanup entry.

## Cleanup execution coverage

`Properties/HandlerCleanup.agda` proves preservation through every successful
cleanup action, for arbitrary acting and protected workers. It reuses
`put-preserves-present`: writing a closed/uncertain socket or a terminated entry
retains that resource's identity. Taking, publishing and restoring the CM map
leave the entry heap unchanged. TIME_WAIT finalization may remove map membership
without deleting the captured entry. No fresh-resource or ownership premise was
added to the preservation theorem.

`CleanupActions` permits lifecycle, publication, exit and cleanup actions.
`CSP/HandlerCleanup` lifts preservation and conditional attachment creation to
raw finite traces with arbitrary interleavings from this action set. It checks
three concrete paths from a certified cleanup-entry fixture:

- normal cleanup through TIME_WAIT completion;
- failed socket close followed by map restoration and an error outcome;
- interrupted TIME_WAIT followed by finalization, purge and an error outcome.

The resulting chains coexist with a closed socket and empty map, or an uncertain
socket after close failure. These facts establish existence of original resources,
not usability or current registration. The starting fixture is explicitly
certified; the witness does not establish source reachability or eventual cleanup.

`Negative/HandlerCleanup` rules out raw one-action traces that finalize before
TIME_WAIT readiness, publish after failed close, or skip finalization after
interruption. It uses the unchanged dispatcher's refusal results.

## Release and remote-operation coverage

`Properties/HandlerRelease.agda` proves that release proposals preserve the IG
execution engine and that entry writes preserve every existing chain.
`edits-chain` extends the latter fact to arbitrary successful atomic pruning
batches, including repeated targets. A failed batch has no successful endpoint.

`Properties/HandlerRemote.agda` checks all remote-operation branches: promotion,
demotion, ordinary and scored transactions, capacity decisions, pruning selection,
assertions, counters, cancellation delivery and return to IG. Their proposals
preserve the IG execution engine. The dispatcher combines that fact with entry
reference retention and the existing captured-mux retention theorem.

`Properties/HandlerManagement.agda` combines the covered action families, including every IG action.
`CSP/HandlerManagement` lifts arbitrary finite interleavings to raw CSP traces,
and composes conditional attachment creation with the same broader suffix.

| Action family | Reference-chain preservation |
| --- | --- |
| Lifecycle, publication, handler exit | Covered |
| Cleanup, inbound release | Covered |
| Remote promotion/demotion, including pruning | Covered |
| IG decision publication and fresh handle/mux installation | Covered |
| IG responder startup/restart and failed-start stop request | Covered |
| IG monitor, job and tracer execution | Covered |
| Other IG event-loop steps, timers, deactivation and flushing | Covered |
| Server admission and handshake-consumer steps | Covered |

Concrete tracked witnesses cover release through return to IG, self-pruning
through cancellation delivery, and a transaction writing two victims plus the
surviving owner's promotion. The self-pruned worker retains its chain even after
its entry becomes terminated. These are local fixture witnesses, not claims that
outbound acquisition or source execution reaches those fixtures.

Returning to IG changes its continuation; it does not itself publish the captured
registration update. The release witness therefore stops before `IG.commitDecision`.
The IG boundary extension below now covers that publication step.
Negative controls reject wrong cancellation targets and replay of a committed
pruning transaction; a malformed multi-write batch has no endpoint.

## IG publication and installation

`Properties/HandlerIGBoundary.agda` proves two additional cases of the actual IG
dispatcher. `CoveredIG` explicitly names `commitDecision` and `installHandle`;
`ManagementActions.igBoundary` includes just those cases in the existing finite
execution and raw CSP trace theorems. The conditional attachment-creation lift
therefore also permits these operations in its suffix.

Decision publication may replace the entire published governor membership but
leaves the execution engine unchanged. The concrete release witness extends
through `IG.commitDecision`: its registration is absent afterward, while the
tracked original reference chain still holds.

Installation checks that both the handle ID and mux ID are absent. Its proof
uses preservation of existing lookups under fresh insertion, rather than equality
of the complete handle table. The earlier `HandlerAnchors` API remains unchanged.
A checked installation adds an unrelated handle/mux pair while preserving the old
handler's chain. This does not establish a chain for a newly allocated handler or
guarantee that an arbitrary new mux key matches a handler: creation premises
remain explicit.

`Negative/HandlerIGBoundary` rules out overwriting either an occupied handle or
an occupied mux and rejects a second decision publication in the resulting phase.
The witnesses and negatives are raw CSP traces/refusals, before hiding.
The extensions below cover responder start/restart and monitor, job and tracer
execution. The exhaustive IG theorem below also covers the event loop.

## Responder startup and restart

`Properties/MuxStartReferences.agda` proves that `startOne` and `startBundle`
retain the mux connection key in every returned outcome. Bundle failure may
retain successful earlier starts; the proof neither assumes nor introduces a
rollback. It covers arbitrary protocol lists and mux states, including stopped
muxes, unknown protocols and already-running protocols.

`Properties/HandlerIGStartup.agda` uses that result and `setMux-preserves` to
preserve any existing tracked chain through `runResponders`, `restart` and
`requestFailedStop`. These actions may change governor registration, continuation,
protocol status and command queues while retaining handles and captured mux keys.
The acted-on mux need not belong to the worker whose chain is protected.

`ManagementActions.igStartup` extends the existing finite-execution theorem,
raw CSP reachability theorem and conditional attachment-creation lift. Coverage
is explicit via `CoveredStartup`; it does not admit arbitrary IG actions.

`CSP/HandlerIGStartup` checks successful startup, failure on the second protocol
followed by a stop request, and successful/failed restart. The restart snapshots
are local post-completion fixtures, not proofs of their preceding source execution.
`Negative/HandlerIGStartup` checks the retained first command and absent
registration after partial failure, and excludes traces that skip the stop request
or repeat startup/restart in the wrong phase. A queued shutdown command does not
establish that the mux has stopped or that handler cleanup has completed.

## Monitor, job and tracer execution

`Properties/HandlerIGMux.agda` proves preservation through ten parameterized IG
action forms: `monitorCommand`, `monitorCompletion`, `startOnDemand`,
`sampleTracer`, `commitTracer`, `finishStart`, `forkResponder`, `finishProtocol`,
`publishJobResult` and `finishStop`. Each successful action updates a looked-up
mux without changing its connection key. `setMux-preserves` retains all other
captured mux references. Queue changes do not alter the original handler resources.

The proof checks clean and exceptional completion, active/inactive tracer paths,
missing-descriptor faults and stopped-mux transitions. Blocked callbacks have no
successful transition to preserve. The theorem assumes an existing chain, not
valid counters or a promise of eventual callback completion.

`ManagementActions.igMux` extends both raw CSP preservation and conditional
attachment creation. `CSP/HandlerIGMux` reuses existing checked execution paths
for normal shutdown, synchronous failure and asynchronous cancellation after
attachment, and adds tracked startup/job-completion, overlap and tracer-fault
witnesses. In the overlap fixture the original chain survives even though the
callback's event captures the currently registered mux of another incarnation.
The witnesses do not establish source reachability or universal progress.

`Negative/HandlerIGMux` certifies a reference chain in a queue-blocked fixture,
then excludes its tracer commit trace. It also checks expired-idle refusal,
completion before job launch, and monitor consumption before result publication.
Thus reference preservation does not make a blocked callback runnable or fuse the
separate job completion, publication and monitor boundaries.

## Exhaustive IG preservation

`Properties/HandlerIGLoop.agda` covers clock capture, inactivity/idle timer
registration, timer expiry, batch selection, event reading, batch completion,
stopped-mux polling, deactivation and exit flushing. These operations retain the
handle table and mux references; queue replacement is independent of the chain.
The proofs follow the actual dispatcher guards, including monotonic clock checks
and responder mode.

`Properties/HandlerIG.agda` exhaustively matches every `IGAction` constructor and
combines the boundary, startup, mux and loop proofs. Every successful IG step
preserves every existing tracked chain. `ManagementActions.ig` admits arbitrary
IG actions into the mixed finite-execution theorem and conditional creation lift;
the earlier narrower constructors remain available. The next extension covers
admission and handshake steps too.

`CSP/HandlerIG.raw-ig-reachability` lifts this result to arbitrary finite raw CSP
IG traces without a caller-supplied action coverage certificate. Its conclusion
identifies an endpoint configuration with the same tracked chain. This is before
hiding and is reference safety, not deadlock freedom or eventual progress.

Concrete tracked fixtures exercise registration after installation, maturity
batching, queue draining followed by tracer commitment, timer expiry, stopped-mux
polling, and exit followed by a previously sampled callback. The exit endpoint
has an inactive IG and a nonempty queue: flushing does not cancel a callback that
already sampled the active flag. Its reference chain still holds. This preserves
the existing modeled behavior and does not establish a new implementation bug
or source reachability of the fixtures.

`Negative/HandlerIG` rejects backward clock capture, polling a running mux,
repeated deactivation, flushing after exit, and finishing an unconsumed batch.
Each refusal is also lifted to exclusion of its corresponding raw CSP trace.

## Admission, handshake and unrestricted dispatcher traces

`Properties/HandlerAdmission.agda` covers every admission action. Entry selection
may allocate or overwrite an entry, socket close may change its value, and fork
may add a handler. Entry/socket presence survives these writes. The absent-child
guard ensures fork cannot replace the handler record used by an existing chain.
Promise allocation changes the allocation list and supply, not a stored result.
Taking, publishing and restoring the map retain the entry heap.

`Properties/HandlerHandshake.agda` covers every handshake-consumer action in both
responder modes. Success may overwrite the captured entry; error/query processing
may remove its map binding and update the heap. Neither removes the heap object,
the handler, its negotiated result, or the socket. Queue writes and continuation
changes also retain the chain. These results require neither fresh supplies nor
map ownership as extra premises: those are separate, stronger invariants.

`ManagementActions.all-actions` covers every constructor of the current
`Machine.Action`. `all-exec-preserves` therefore accepts arbitrary finite executions
without a coverage certificate. `CSP/HandlerAll.raw-all-preserves` gives the raw
CSP reachability version. `raw-attachment-all-creates` retains the explicit
`CreationPremises` and permits any subsequent dispatcher actions. This establishes
preservation of an existing worker's chain, not automatic tracking of newly forked
workers or correctness of the entire intended CM/IG/OG/Server subsystem.

The new concrete paths start from a local coherent tracked fixture before
handshake consumption, complete its success path, admit a second connection,
then publish and consume the second child's query result. Its binding disappears
and its terminated entry remains; the first worker's chain survives throughout.
Every step uses the unmodified dispatcher. No source reachability of the starting
fixture is asserted. `Negative/HandlerAll` excludes child-token reuse, repeated
result reads in the wrong phase, and writes to a full notification queue. It also
proves that the second child has not implicitly acquired a tracked chain.

Full runtime validity, source refinement and progress remain separate.

## Establishment from selection and matched boundaries

`Properties/HandlerResources.agda` proves that successful entry selection returns
an existing heap object, whether selection reuses or allocates its identity.
`selection-fork-resources` composes consecutive successful selection and fork to
establish the handler's entry/socket resources. A raw fork alone does not check
entry existence, so `fork-resources` keeps that premise explicit.

`Properties/HandlerEstablishment.agda` establishes the remaining lookup chain:

1. Install a fresh handle/mux pair using the original handler's key.
2. Successfully publish a negotiated result naming that installed handle.
3. Attach the handler successfully.

`Prepared` records the installed lookups and resource existence before the
promise is published. Successful publication supplies the final lookup and
establishes `Chain`; `chain-premises` derives the earlier attachment premises
from it. No executable guard was added or changed. Neither a pre-existing chain
nor `CreationPremises` is an input to the new establishment trace theorem.
The installation key and published handle ID are tied together explicitly in
the theorem's trace, rather than being assumed properties of arbitrary inputs.

`CSP/HandlerEstablishment.raw-establishment` takes resource evidence at the fork
boundary and a raw trace of those matched operations followed by any finite
dispatcher suffix. It returns an endpoint with a tracked chain. The concrete
witness derives its resource evidence through actual selection/fork transitions
and starts from the accepted-socket fixture, with no handlers, result, handle or
mux initially installed. It attaches before the admission caller publishes its
map and consumes the result; those subsequent steps preserve the new chain.
This is a finite model trace, not a universal completion or source-refinement
claim. The original theorem covers this consecutive establishment sequence. The
interference extension below permits parent and handshake-consumer steps around
publication and before attachment.

`Negative/HandlerEstablishment` constructs a trace from the same accepted-socket
fixture that installs a mux under a different key, publishes its handle, and
successfully attaches. Its endpoint provably has no coherent tracked chain.
It also rejects attachment before result publication. The wrong-key trace is
reachable in the open model because installation and publication are abstract
input boundaries; it is not evidence of a Haskell implementation bug.
Consequently, an unconditional creation invariant for all currently allowed
boundary inputs would be false. A source-derived boundary contract or a more
detailed allocation/negotiation model is needed before claiming global validity.

## Parent and consumer interleavings before attachment

`Properties/HandlerConsumerEffects.agda` records the world effects of admission
`putMapBack`/`readCounters` and all five handshake-consumer actions. They retain
the handler and promise-result stores and socket values exactly, and retain
entry identities even when updating heap values or removing map bindings.
The existing `HandlerHandshake` chain theorem now uses this shared analysis;
its type and coverage are unchanged.

`Properties/HandlerInterference.agda` transports three kinds of evidence across
arbitrary finite sequences of those actions:

- `Resources`, before handle installation;
- `Prepared`, after installation but without assuming a published result;
- `Chain`, after publication but without assuming a lifecycle attachment.

The actor may be any worker, not just the worker whose references are protected.
`Interference` explicitly restricts action families. This is not yet an
all-dispatcher pre-attachment theorem; the runtime extension below adds mux
execution, handler exit and cleanup in a separate, broader alphabet.
The earlier all-dispatcher theorem for already tracked chains is unchanged.

`CSP/HandlerInterference` supplies raw resource/preparation trace lifts and
`raw-delayed-attachment`. The latter permits a covered sequence before matched
publication and another before successful attachment, then an arbitrary finite
dispatcher suffix. It assumes the actual publication and attachment transitions
succeed; evidence retention is not a proof that either action remains enabled.

The concrete witness begins at the accepted-socket fixture. It publishes the
admission map between fork and installation, reads counters between installation
and result publication, and performs all handshake-consumer phases before
attachment. Resource, prepared and chain certificates are transported through
the respective segments, rather than reconstructed from endpoint lookups.

`Negative/HandlerInterference` rejects result reading and attachment while the
promise is empty despite a valid `Prepared` certificate. It also executes an
untracked handler exit: that particular step retains `Prepared`, but cleanup
blocks subsequent publication. Exit is outside `Interference`; this witness
illustrates the difference between preserved references and continued readiness.

## Mux execution and cleanup before attachment

`Properties/MuxRetention.agda` extracts handle equality and mux-key retention
from all ten monitor/job/tracer action forms previously covered by
`HandlerIGMux`. The latter keeps its existing coverage constructors and chain
proof signatures, now using the shared effect proof. No handler, negotiated
result or lifecycle frame is required to establish the mux effects.

`Properties/CleanupRetention.agda` similarly extracts the effects of every
cleanup action, including socket-close failure, restoration and TIME_WAIT
interruption. Handler and result stores stay equal; entry and socket identities
remain present even when their values change. The existing `HandlerCleanup`
interfaces and chain theorems use this shared proof without changing their types.
This is deliberately weaker than equality of socket values, which cleanup
cannot preserve.

`Properties/HandlerRuntimeInterference.agda` supplies a broader `Interference`
alphabet, embedding the earlier caller alphabet without changing its APIs.
It transports `Resources`, `Prepared` and untracked `Chain` evidence through
mixed finite sequences with arbitrary actor identities:

| Action family | Pre-attachment runtime coverage |
| --- | --- |
| Parent map publication and counter reads | Covered |
| All handshake-consumer actions | Covered |
| Ten mux monitor/job/tracer action forms | Covered |
| Handler exit and every cleanup action | Covered |
| Three IG startup/restart and ten event-loop action forms | Covered |
| IG fresh installation and decision publication | Not yet covered |
| Other admission, lifecycle, publication, release and remote actions | Not yet covered |

`CSP/HandlerRuntimeInterference` lifts resources and preparation to raw traces
and broadens delayed attachment around matched publication. Successful
publication and attachment remain premises. A cleanup or stopped-mux path that
blocks those actions cannot satisfy that trace premise, even though its
reference evidence survives.

The pre-attachment responder-start witness reuses the checked registration and
mux-job path, including its model trace from the accepted-socket fixture. Its
starting `Prepared` certificate is a concrete lookup certificate. The cleanup
witness transports the earlier transition-derived preparation through handler
exit, map acquisition, entry termination, socket close, map removal and counter
reading, before any negotiated result or lifecycle attachment. It ends with a
closed socket, empty map and no tracked frame, while `Prepared` and `Resources`
still hold. A separate local queued-shutdown fixture retains preparation through
monitor consumption and mux stop; its shutdown-command origin is not established.

`Negative/HandlerRuntimeInterference` rejects publication after that cleanup,
proves the child was not implicitly tracked, and rejects attachment to the
stopped mux despite retained preparation. These are reference-safety and
readiness distinctions within the model, not source deadlock or bug claims.

`Properties/LoopRetention` and `Properties/StartupRetention` now extract the
existing IG proofs into handle-equality and mux-key retention effects, without
requiring a handler chain. The old tracked-chain APIs remain wrappers over these
effects. Runtime `Interference` additionally covers all ten loop actions and all
three startup/restart actions; its existing raw CSP trace lifts inherit this
coverage, including partial failure and failed-start shutdown requests.

`CSP/HandlerIGInterference` transports preparation from the installed fixture
through registration and responder execution without attachment. A separate local
two-protocol fixture preserves preparation through partial startup failure and
its shutdown request. `Negative/HandlerIGInterference` rejects a stale clock sample
after a successful batch finish. Retained references imply neither readiness nor
progress; the failure fixture is not claimed reachable from admission.

### All IG actions before attachment

`Properties/IGTableRetention.agda` adds a lookup-retention relation: every old
handle lookup keeps its exact value, and every old mux lookup retains a mux with
the same connection key. Unlike `Anchors`, it permits handle-table growth. The
stronger `Anchors` API and narrower runtime-interference theorem are unchanged.
Fresh insertion uses both executable absence guards; no store-uniqueness premise
is added. `IGBoundaryRetention` supplies installation and decision effects, and
`IGRetention.mode-retains` exhaustively covers all 25 current IG action forms.
The existing tracked boundary theorem reuses these effects through
`HandlerTableRetention`, retaining its public signatures.

`Properties/HandlerAllIGInterference.agda` embeds the runtime alphabet and adds
any `igStep`. Resources, preparation, and untracked chains survive successful
finite executions over this enlarged alphabet. Its raw CSP lifts in
`CSP/HandlerAllIGInterference` also allow any IG action before matched publication
and between publication and successful attachment. The suffix after attachment
remains unrestricted by the already established tracked-chain theorem.

The fresh-installation witness starts at the earlier waiting fixture, adds
unrelated handle/mux IDs, then publishes the original result and attaches the
original handler. Preparation is transported across the insertion, rather than
reconstructed at the endpoint. A separate local pending-decision fixture removes
IG membership without attachment and retains preparation. Its pending continuation
is not claimed reachable from the whole admission trace. Negative controls reject
an occupied handle, an occupied mux, and a second decision outside its phase.

This completes pre-attachment coverage of the current **IG dispatcher**, not the
whole Machine dispatcher. Other admission, lifecycle, publication, release and
remote actions remain outside this interference alphabet. Successful publication
and attachment are still premises; retention establishes neither readiness nor
progress. The following layer adds release and remote actions; admission, lifecycle
and publication interference still require separate treatment. Phase and
source-refinement obligations remain separate.

### Release and remote-state interference

`Properties/ReleaseRetention` and `Properties/RemoteRetention` extract the existing
engine-equality proofs from the tracked-chain modules. They additionally retain
handler and result stores exactly, and entry/socket presence by identity, through
the actual dispatcher guards and atomic entry edits. The batch lemma handles any
successful edit list, including repeated targets; failed edits expose no partial
endpoint. Existing `HandlerRelease` and `HandlerRemote` APIs remain available.

`Properties/HandlerGovernorInterference` embeds all-IG interference and adds every
`releaseStep` and `remoteStep`, including scored pruning and cancellation delivery.
It transports resources, preparation and untracked chains through successful
finite sequences. `CSP/HandlerGovernorInterference` supplies raw trace lifts and
delayed attachment with successful matched publication and attachment as premises.

The release witness transports preparation from the existing registered fixture
through cancellation delivery and membership removal. The promotion witness starts
after responder startup. Both reuse existing paths without inserting a lifecycle
frame. Local self-pruning and two-victim fixtures demonstrate retention after
termination writes and atomic multi-entry edits. Their outbound acquisition history
is not modeled; no admission reachability is claimed for the pruning inputs.
Negative controls reject premature release return, premature self-pruning return,
and a scored transaction whose ticket differs from the current generation.

These are reference-safety results. Cancellation delivery remains an external
input, and no fairness, termination, enabled attachment, or Haskell refinement
follows. The next layer adds handler lifecycle actions. Admission beyond parent
publication/counters and result publication still require separate treatment.
The source contract tying installation to the published negotiated handle also
remains open.

### Lifecycle interference without an attachment premise

`Properties/LifecycleRetention.step-effects` lifts the existing exhaustive
`HandlerEvolution.step-anchors` theorem through the dispatcher. Every successful
handler lifecycle step preserves the world exactly and retains the installed
handle/mux references. No lifecycle frame for the observed handler is a premise.
The executing worker and observed worker may differ. Existing phase, mux and
callback guards remain in the executable step relation.

`HandlerGovernorInterference.Covered` now also includes arbitrary `handlerStep`
actions, so its finite-execution and raw CSP trace lifts inherit this coverage.
The earlier constructors and effect type remain unchanged. This is preservation
of evidence that can be obtained before attachment, not an invariant that the
handler stays unattached. In particular, the alphabet includes attachment itself.
Successful final attachment remains a premise of the delayed-attachment theorem.

`CSP/HandlerLifecycleInterference` transports preparation from the registered
fixture through the release cancellation request, then attachment, delivery,
pool closure, async failure publication, tracing, rethrow and cleanup. The endpoint
has a closed socket and empty CM map while retaining the original references.
The witness uses existing checked paths; cancellation delivery, job-pool closure,
and TIME_WAIT completion remain environment inputs, not liveness conclusions.
Negative controls reject failure publication before the pool join, cleanup before
unwind, and reattachment after cleanup despite retained preparation.

The following layer handles admission and result-publication interference using
lookup preservation. Source correspondence and the matched installation/result
contract remain separate obligations.

### Exhaustive dispatcher preservation before attachment

`Properties/StateRetention` permits growth of handler and result tables while
preserving every existing lookup exactly. Mutable entry/socket values may change,
but their identities remain present. Earlier exact-store retention embeds into
this relation; its existing API is unchanged. `HandlerStateRetention` transports
resource and untracked-chain evidence through these effects.

`AdmissionRetention` extracts the existing exhaustive admission case analysis.
The absent-child guard preserves existing handler records during fork; selection,
rejection, fork failure, map publication/restoration and socket closure retain
existing resource identities. The old `HandlerAdmission.worker-chain` type remains
available as a wrapper. `PublicationRetention` handles fresh result writes and the
explicit duplicate-write outcome, preserving older results. The tracked boundary
proof reuses the fresh-publication effect.

`Properties/HandlerDispatcherInterference.all-actions` exhaustively covers every
current `Machine.Action` constructor. `all-resources`, `all-prepared`, and
`all-chain` therefore preserve existing evidence along **any successful finite
dispatcher execution**, without an action-subset premise or a lifecycle-frame
premise. `CSP/HandlerDispatcherInterference` lifts this to raw traces and removes
the interference-subset premises around delayed matched publication/attachment.
Successful publication and attachment remain necessary premises. A trace may
attach or finalize the observed handler; “before attachment” describes where the
evidence can originate, not an invariant that the handler stays unattached.

The CSP witness reruns the existing second-admission snapshots without optional
lifecycle frames, checking every transition again. The original handler retains
preparation while another child is forked, publishes a query result and has its
binding removed by the handshake consumer. Both result lookups remain present.
A subsequent duplicate-write outcome records the original writer as blocked while
retaining its evidence. Negative controls reject a reused child identity, a
claimed overwrite, and a retry after the writer fault; no tracking is created.

This closes the current dispatcher **preservation** obligation. It does not prove
that arbitrary installations/publications establish coherent references, that
attachment is enabled, that executions progress, or that Haskell refines this
model. Next is the source contract relating actual handle creation, installation
and promise publication, with explicit negative cases for incoherent boundaries.

## Source-origin follow-up

[HandlerOrigin.md](HandlerOrigin.md) records a fresh review of the pinned Haskell
allocation/publication path. `Prepared` and `Chain` establish reference coherence;
they do not equate installed flow with the result's negotiated flow. The new
`Origin` certificate records the exact installed handle descriptor, and a matched
trace theorem carries this through interleavings to attachment. A negative flow
mismatch still has a valid tracked reference chain, demonstrating the distinction.
Source projection and executable admissibility monitoring remain separate work.

## Validation

Run from the standalone library root, one Agda process at a time:

```sh
agda ConnectionManagement/Negative/HandlerDispatcherInterference.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerLifecycleInterference.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerGovernorInterference.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerAllIGInterference.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerIGInterference.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerRuntimeInterference.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerInterference.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerEstablishment.agda +RTS -M2G -RTS
agda ConnectionManagement/CSP/HandlerAll.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerAll.agda +RTS -M2G -RTS
agda ConnectionManagement/CSP/HandlerIG.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerIG.agda +RTS -M2G -RTS
agda ConnectionManagement/CSP/HandlerIGMux.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerIGMux.agda +RTS -M2G -RTS
agda ConnectionManagement/CSP/HandlerIGStartup.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerIGStartup.agda +RTS -M2G -RTS
agda ConnectionManagement/CSP/HandlerIGBoundary.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerIGBoundary.agda +RTS -M2G -RTS
agda ConnectionManagement/CSP/HandlerManagement.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerManagement.agda +RTS -M2G -RTS
agda ConnectionManagement/CSP/HandlerCleanup.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerCleanup.agda +RTS -M2G -RTS
agda ConnectionManagement/CSP/HandlerBoundaries.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerBoundaries.agda +RTS -M2G -RTS
agda ConnectionManagement/CSP/HandlerAttachment.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerAttachment.agda +RTS -M2G -RTS
agda ConnectionManagement/CSP/HandlerReferences.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerReferences.agda +RTS -M2G -RTS
agda ConnectionManagement/CSP/HandlerCapture.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerCapture.agda +RTS -M2G -RTS
agda ConnectionManagement/CSP/HandlerUniqueOwnership.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerUniqueOwnership.agda +RTS -M2G -RTS
```
