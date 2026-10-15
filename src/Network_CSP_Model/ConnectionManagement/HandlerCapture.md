# Captured mux identity survives arbitrary finite executions

The model now has a machine-wide preservation theorem for **one specific
property**: once a tracked worker stores a mux ID, no successful dispatcher step
removes or changes that capture. This goes beyond the selected-trace certificates
in [HandlerValidity.md](HandlerValidity.md), without establishing their entire
runtime-validity predicate as a global invariant.

## Statement and proof

`Retains before after` quantifies over every worker and frame found by lookup in
`before`. A frame still exists for that worker in `after`, and its `capturedMux`
is equal to the old value. Other frame fields, including phase, may change.

[Properties/HandlerCapture.agda](Properties/HandlerCapture.agda) proves:

- Inserting a previously absent worker retains all existing captures.
- Updating a known worker's phase retains its capture and every other worker's.
- Every successful lifecycle action, cancellation-delivery note and finalizer
  entry obeys that relation. The proof covers every phase constructor explicitly.

[Properties/HandlerCaptureInvariant.agda](Properties/HandlerCaptureInvariant.agda)
then proves the following for the actual dispatcher:

```agda
advance-retains : ∀ a c {c′} → advance a c ≡ just c′ →
  Retains (handlerLifecycles c) (handlerLifecycles c′)

exec-retains : ∀ {c as c′} → Executes c as c′ →
  Retains (handlerLifecycles c) (handlerLifecycles c′)
```

There is no action whitelist, scheduler assumption, initial-state validity premise
or single-worker restriction. Admission, handshake publication, IG, release,
pruning, lifecycle and cleanup steps all participate. Successful replay inherits
the result. A new attachment can add another worker but cannot replace the capture
of a worker already present.

## CSP interpretation

[CSP/HandlerCapture.agda](CSP/HandlerCapture.agda) uses the existing raw trace
correspondence. Every process reached by a finite raw action trace has a
representing configuration that retains the starting captures. The statement
returns that configuration existentially; it does not assume the process renderer
is injective or infer configuration equality from process equality.

[Negative/HandlerCapture.agda](Negative/HandlerCapture.agda) constructs snapshots
that retarget or remove a stored capture. Both violate `Retains`; the invariant
therefore rules out **every finite execution** from the original snapshot to
either mutation. These isolate the capture property and do not claim source
reachability or full validity of the snapshots.

## Scope

This theorem preserves a stored identity, not the entire reference chain. It does
not prove that the mux exists, that the original promise/handle continues to point
to it, that another worker cannot share it, or that phases and resources are
consistent. Those checks remain covered only by the selected-execution validity
certificates. It also does not establish Haskell refinement, hidden failures or
divergence properties, fairness, or termination of cleanup.

The current machine retains lifecycle frames after finalization. A future explicit
frame-reclamation operation would require a deliberate revision of the no-removal
statement; it must not be added while silently excluding that action from the
preservation theorem.

```sh
agda ConnectionManagement/CSP/HandlerCapture.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerCapture.agda +RTS -M2G -RTS
```

[Unique tracked ownership](HandlerUniqueOwnership.md) is now proved separately,
using a shared proof of permitted tracking-table edits. Next extend global
preservation to the original handler/promise/handle/mux references. Keep phase validity and full source coverage
as separate obligations before treating exploration results as source defects.
