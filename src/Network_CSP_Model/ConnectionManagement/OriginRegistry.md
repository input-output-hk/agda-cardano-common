# Dynamic success-invocation registry

`Rules/OriginRegistry` extends the [attributed action boundary](AttributedOrigin.md)
to a list of dynamically registered worker/handle pairs. There is no fixed target
parameter. `start c` begins with an empty registry; successful allocation creates
a new entry and advances it to `awaitingPublication`. Each subsequent action is
checked against every registered invocation using the existing attributed
single-target monitor.

## Runtime behavior

```mermaid
flowchart TD
  A[Attributed action] --> P[Prepare registry]
  P --> F[Allocation: require fresh worker and handle, add pending entry]
  P --> R[Publication or attachment: require registered worker]
  P --> O[Other dispatch: reject raw allocation]
  F --> C[Original machine transition and all invocation checks]
  R --> C
  O --> C
  C --> S[Commit machine endpoint and all phases together]
  C --> N[On any refusal: no transition]
```

Allocation tags are still observer inputs representing the invoking handler. Each
new entry checks the captured connection key. Publication must use the registered
handle and flow, and attachment must follow observed publication. Another worker's
allocation cannot consume an existing worker or handle identity. Registration and
phase changes are committed only when the underlying machine and every monitor
accept. All monitors inspect the same pre-action configuration; they do not apply
the machine transition sequentially to each other's outputs.

The registry retains entries permanently. This success profile does not support
worker-ID or handle-ID recycling, deregistration, query/error publications or a
new successful invocation under an old worker ID. It permits ordinary admission
and cleanup actions without requiring those workers to be registered. Other
source scheduling constraints remain outside the monitor.

## Proof scope

`Properties/OriginRegistry.step-projects` and `exec-projects` erase accepted actions
into successful transitions of the unchanged open machine, preserving endpoints.
These projection theorems require no resource evidence.

`Invariant` is an `All` predicate over registry entries. Each entry carries the
existing single-target invariant: worker resources plus exact ticket origin in
both allocated and published phases. `drive-certified` uses deterministic machine
projection to establish that every local monitor's endpoint is the same shared
machine endpoint, then reuses the existing invariant-preservation proof.

`reachable` proves the invariant for executions from the empty registry with
`Supported` evidence. `Supported` requires `Resources` for the invoking worker
**at each allocation**, including allocations after later forks. Non-allocation
actions need only the trivial premise. This is a proof premise, not an executable
entry/socket-existence check. It neither authenticates the worker tag nor proves
source-to-model identity correspondence. It also does not require all workers to
exist at the initial state.

`CSP/OriginRegistry` reuses the visible attributed action channel. It proves finite
execution/trace correspondence and erasure of every finite raw trace to an open
machine trace. `raw-invariant` returns the actual reached process endpoint and
execution, together with the implication from `Supported` evidence for that exact
execution to its registry invariant. It does not claim unconditional origin for
arbitrary malformed initial machine states.

These results establish finite model safety under the stated resource premises.
They do not establish source refinement, failures refinement, progress, readiness,
or source deadlock. A monitor rejection is a contract disagreement. No global
source ownership theorem or identity-reuse policy is inferred from freshness
checks in this success profile.

## Overlapping-worker witness

`Negative/OriginRegistry` starts from an explicit machine fixture with two handler
records, distinct sockets/promises, and a shared connection key and CM entry.
It does not claim a two-admission source-reachable prefix.

The checked schedule is:

1. Allocate worker 1's handle and register its ticket.
2. Allocate worker 2's distinct handle while worker 1 awaits publication.
3. Publish worker 2's result.
4. Publish worker 1's result.

Both allocations have explicit resource evidence at their respective steps.
`two-published` checks the exact final two-entry registry, and `all-certified`
applies the generic theorem to both entries. The accepted schedule has a CSP trace.

CSP non-trace controls reject unregistered publication and cross-worker handle
substitution after both allocations. The substitution control uses the same
captured key for both workers, so key agreement alone cannot explain rejection.
Step-equality controls reject worker reuse, handle reuse, raw allocation even with
an empty registry, and a negotiated-flow mismatch. Earlier attributed and
single-target controls are imported transitively.

## Admission-derived witness

`CSP/RegistryAdmission` removes the hand-supplied handler/resource fixture from a
second witness. It begins at `CSP/Fixtures.start`, after two accepted sockets have
been handed to admission workers, with no handler records or registry entries.
This is model reachability from that fixture, not a source `accept()` trace.

```mermaid
sequenceDiagram
  participant A as First admission
  participant H as First handler
  participant B as Second admission
  participant J as Second handler
  participant R as Origin registry
  A->>A: Take map, count, allocate promise, select entry, fork
  H->>R: Allocate handle 0; register pending ticket
  A->>A: Restore map and read counters
  B->>B: Take map, count, allocate promise, select entry, fork
  Note over H,R: First ticket remains pending throughout second admission
  B->>B: Restore map and read counters
  J->>R: Allocate handle 1; register pending ticket
  J->>R: Publish handle 1
  H->>R: Publish handle 0
```

The complete 18-action registry execution has a CSP trace and an erased open
machine trace. Both resource certificates come from `selection-fork-resources`;
the second certificate is transported through parent map restoration and the
counter read. `Supported` is discharged for the complete execution without a
hand-built resource record. `first-retained` certifies the first registry entry
after the second admission, and `all-certified` covers both final entries.
Exact phase checks confirm that both entries are pending before either publication
and both are published at the endpoint.

This witness uses the two distinct connection keys from the admission fixture.
The earlier synthetic shared-key witness remains valuable: its swap control
shows that key agreement alone cannot substitute for worker/handle attribution.
Neither witness extends the registry's success-only scope or models attachment,
mux execution, or handshake-result consumption in this new schedule.

`Negative/RegistryAdmission` proves CSP non-traces for a swapped publication after
the complete two-allocation prefix and repeated allocation after the second
admission. It imports the earlier registry negative controls.

## Reachable identity uniqueness

`Properties/RegistryUnique.Unique` uses the standard library's `AllPairs` over
registry targets. Each earlier target differs from every later target in **both**
worker ID and handle ID. This is stronger than uniqueness of worker/handle pairs:
two different handles cannot share a worker, and two different workers cannot
share a handle.

The proof connects the executable freshness checks to pairwise inequality.
`prepare-unique` permits only a fresh target to be prepended; `drive-targets`
proves that successful phase updates preserve the entire target list in order.
`step-unique` and `exec-unique` retain uniqueness, and `reachable-unique` derives
it from an empty registry for every accepted finite execution.

This theorem has **no** `Supported`, resource, heap-validity or finite-carrier
premise. It holds for `start c` with arbitrary machine configuration `c`.
Descriptor origin still requires the separate per-allocation resource evidence;
identity uniqueness does not supply it. Nor does uniqueness authenticate observer
tags, establish source object identity, or justify recycling an old worker ID.

`CSP/RegistryUnique.raw-unique` retains the exact process endpoint and its unique
registry for every finite raw CSP execution from `start`. `trace-unique` gives
the corresponding existential endpoint for finite traces. Both reuse the existing
execution correspondence; the runtime rules and event alphabet are unchanged.

`Negative/RegistryUnique` derives uniqueness for both the synthetic overlapping
fixture and the admission-derived witness. Separate generic contradictions exclude
a repeated worker even with different handles, and a repeated handle even with
different workers. Two forged endpoint registries are proved unreachable from
any `start c`, for every finite action list. Arbitrarily pre-seeded registries
are not certified by the theorem.

## Publication soundness

`Properties/RegistryPublication.publication-sound` relates an accepted successful
publication to the pre-state origin invariant and identity uniqueness. Its `Sound`
record names an actual registry member and proves:

- Its worker is the publishing worker, and every other member with that worker
  equals the selected entry.
- Its phase was `awaitingPublication` with a particular ticket.
- The published handle and flow equal the selected handle and ticket flow.
- The corresponding entry is present in the post-state with phase `published`.
- The exact handle origin, including ticket mux and protocol bundle, holds both
  before and after the publication.

`worker-member` obtains existence from the executable registration guard;
`owner-unique` obtains uniqueness from pairwise identity separation. `drive-member`
recovers the selected entry's successful single-target monitor transition, so the
handle/flow and phase checks reuse `accepted-publication`. Origin comes from the
pre-state certificate and is retained through the underlying publication action.

`reachable-publication` discharges identity uniqueness from any accepted prefix
starting at an empty registry, and discharges origin from `Supported` evidence for
that prefix. A successful monitor step alone still does not authenticate an
observer tag or supply missing heap-resource evidence.

`CSP/RegistryPublication.raw-publication` lifts this to an arbitrary finite raw
CSP prefix followed by a visible successful publication event. It retains the
actual pre- and post-process endpoints and the recovered prefix execution. The
soundness result remains conditional on resource support for that exact prefix.
It is not a failures-refinement or source-implementation correspondence theorem.

`Negative/RegistryPublication` instantiates the theorem for both publications in
the reverse-order admission-derived schedule. It also proves that the final state
cannot support another `Sound` certificate for any publishing worker, handle,
flow or endpoint: both registry entries are already published, so no pending
entry exists. Earlier ownership-swap and duplicate-identity controls are imported.
This excludes a repeated success in this monitor profile, not every source
publication-fault or query/error outcome.

## Validation and next step

Run sequentially from the standalone library root:

```sh
agda ConnectionManagement/Negative/RegistryPublication.agda +RTS -M2G -RTS
agda ConnectionManagement/Negative/HandlerDispatcherInterference.agda +RTS -M2G -RTS
```

The first admission-derived draft used recursively computed snapshots and exhausted
the 2 GB Agda heap. The checked version uses explicit snapshots and local transition
equalities; it passes with the same heap limit. No checker limit or theorem premise
was relaxed.

Next, connect the publication certificate to attachment and its tracked mux
reference, using the same registered invocation through arbitrary accepted
interleavings.
Lifecycle/reuse policies, query/error profiles, interruption constraints and
concrete source replay remain separate obligations.
