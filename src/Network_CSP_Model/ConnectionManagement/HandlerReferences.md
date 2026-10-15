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
capture-retention theorems continue to hold, but this reference-chain theorem
covers only lifecycle actions. In particular it does not yet cover interleaved IG
updates, Server allocation, handshake publication, release, pruning or cleanup.
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
agda ConnectionManagement/CSP/HandlerAttachment.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerAttachment.agda +RTS -M2G -RTS
agda ConnectionManagement/CSP/HandlerReferences.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerReferences.agda +RTS -M2G -RTS
agda ConnectionManagement/CSP/HandlerCapture.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerCapture.agda +RTS -M2G -RTS
agda ConnectionManagement/CSP/HandlerUniqueOwnership.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerUniqueOwnership.agda +RTS -M2G -RTS
```
