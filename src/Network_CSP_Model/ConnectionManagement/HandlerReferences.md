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
exit, cleanup, release and remote operations including pruning. Server,
handshake-consumer and most IG steps remain outside the reference-chain trace
theorem; the IG boundary cases below are now covered.
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

`Properties/HandlerManagement.agda` combines the six covered action families.
`CSP/HandlerManagement` lifts arbitrary finite interleavings to raw CSP traces,
and composes conditional attachment creation with the same broader suffix.

| Action family | Reference-chain preservation |
| --- | --- |
| Lifecycle, publication, handler exit | Covered |
| Cleanup, inbound release | Covered |
| Remote promotion/demotion, including pruning | Covered |
| IG decision publication and fresh handle/mux installation | Covered |
| IG responder startup/restart and failed-start stop request | Covered |
| IG monitor/job/tracer execution and other event-loop steps | Pending |
| Server admission and handshake-consumer steps | Pending |

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
The startup extension below covers responder start/restart; monitor, job, tracer
and other event-loop operations still need preservation proofs.

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

Next, cover monitor commands/completions, protocol jobs and synchronous tracer
callbacks, followed by the remaining IG event-loop actions.

Full runtime validity, source refinement and progress remain separate.

This establishes conditional creation at the attachment boundary, not a proof
that allocation and publication always establish the premises. Next, derive those
premises from the relevant transitions and extend reference preservation through
the remaining dispatcher families. Retain immutable
original references across mutable connection-map and governor membership changes.
Only then combine these results with phase and cleanup obligations for a global
runtime-validity theorem.

## Validation

Run from the standalone library root, one Agda process at a time:

```sh
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
