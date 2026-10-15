# Unique tracked ownership is a machine-wide invariant

The exact diagnostic predicate `uniqueOwners` is now preserved by every successful
machine action. Starting from an empty tracking table, no finite execution can
create duplicate tracked worker keys or assign one captured mux to two tracked
workers. This complements [capture retention](HandlerCapture.md), which alone
would permit adding another worker that shares an existing capture.

## Shared transition evidence

[Properties/HandlerEvolution.agda](Properties/HandlerEvolution.agda) factors the
existing lifecycle case analysis into a proof of the actual runtime edit:

| Edit | Evidence required by the proof |
|---|---|
| Unchanged | The runtime table is identical |
| Attachment | Worker lookup is absent and the captured mux is unused |
| Phase update | The frame being updated was found under that worker key |

[Properties/HandlerEvolutionInvariant.agda](Properties/HandlerEvolutionInvariant.agda)
proves every successful `advance` produces one of these edits. This relation is
proof infrastructure, not a new execution rule or a validator guarding the machine.
The former capture-retention API and theorem types remain unchanged; they now
follow from this shared evidence.

## Ownership theorem

[Properties/HandlerUniqueOwnership.agda](Properties/HandlerUniqueOwnership.agda)
defines exactly:

```agda
Unique rt = uniqueOwners rt ≡ true
```

It proves phase updates preserve the whole Boolean result, and fresh attachments
preserve a successful result. The latter uses both source-profile guards:
absence of a worker key alone cannot exclude a shared mux capture.

[Properties/HandlerUniqueOwnershipInvariant.agda](Properties/HandlerUniqueOwnershipInvariant.agda)
lifts the result to every dispatcher action, arbitrary finite executions and
successful replay. Its general form requires uniqueness in the starting table.
Its initial-state corollary needs no extra premise: `initial` has an empty tracking
table for every responder mode and supplied world state.

The [CSP endpoint](CSP/HandlerUniqueOwnership.agda) lifts this invariant to raw
finite process reachability. As with capture retention, it returns a representing
configuration and does not assume the renderer is injective.

## Negative controls and limits

[Negative/HandlerUniqueOwnership.agda](Negative/HandlerUniqueOwnership.agda) adds a
second worker sharing an existing mux. That mutation **preserves the old capture**
but fails uniqueness. The new theorem rules out every finite execution from a
unique snapshot to either that mutation or a duplicate-worker-key snapshot.
These local snapshots isolate the property; they are not source-defect witnesses.

The invariant concerns the tracked table only. Untracked handlers still exist,
and it does not establish that every installed mux has an owner. It also does not
prove validity of the handler/promise/handle/mux reference chain, phase consistency,
source refinement, fairness or cleanup progress. Those obligations remain distinct
from the [selected-state validity certificates](HandlerValidity.md).

```sh
agda ConnectionManagement/CSP/HandlerUniqueOwnership.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerUniqueOwnership.agda +RTS -M2G -RTS
agda ConnectionManagement/CSP/HandlerCapture.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerCapture.agda +RTS -M2G -RTS
```

[Reference-chain preservation](HandlerReferences.md) now covers lifecycle-only
executions from an already-valid chain. Creation and preservation across the
remaining dispatcher families are still required.
