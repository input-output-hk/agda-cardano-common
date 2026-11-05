# Increment 58: collection, physical handlers and pending forks

Initial read-only model/source audit on 5 November 2026, based on model
implementation `1e332cd` and the pre-acceptance increment-58 worktree. The initial
hand-off below retains its unperformed-check wording; subsequent model acceptance
is recorded in [increment 58](../ConnectionManagement/Supervision.md#fifty-eighth-increment-acknowledged-collected-handler-birth-backing).
This is no new implementation-defect claim. Current theorem status belongs to
[project state](../PROJECT_STATE.md) and
[supervision](../ConnectionManagement/Supervision.md).

## Confirmed boundaries

[CMShutdown.step](../ConnectionManagement/Rules/CMShutdown.agda) appends a worker
to `collected` only at `acknowledgeDelivery`. `captureSnapshot` saves entry
identities; `readEntry` reads their current heap values and selects a worker;
`requestCancellation` enters `awaitDelivery`. None of those three operations
appends a worker or establishes physical membership. Repeated bindings/handles
are not deduplicated. Only `finishClose` observes the collective result oracle.

The maintained action interfaces reject direct acknowledgement attempts:
`HandlerSupervision.step (shutdownStep acknowledgeDelivery)` and
`MuxHandlerExit.choose (shutdownStep acknowledgeDelivery)` return `nothing`.
Their public helper functions `acknowledge`/`control` can perform that primitive
operation, so an invariant about enabled frontend actions must inspect their
guarded call sites rather than quantify over arbitrary helper invocations.

The acknowledgement-producing routes requiring coverage are:

| Layer | Route or helper |
| --- | --- |
| [HandlerSupervision](../ConnectionManagement/HandlerSupervision.agda) | Handshake/setup delivery, TIME_WAIT delivery and finished-target acknowledgement |
| [MuxHandlerExit](../ConnectionManagement/MuxHandlerExit.agda) | Mux delivery, TIME_WAIT delivery and finished-target acknowledgement |
| [MuxExitCancellation](../ConnectionManagement/MuxExitCancellation.agda) | `shutdownDelivery` after an enabled delivery window |
| [MuxStartupUnwind](../ConnectionManagement/MuxStartupUnwind.agda) | `enact (acknowledge plan)` after the selected fault/delivery plan |
| [MuxDeltaQ](../ConnectionManagement/MuxDeltaQ.agda) | Ordinary and initiator callback shutdown delivery through an acknowledged fault plan |
| [MuxCatchUnwind](../ConnectionManagement/MuxCatchUnwind.agda) | Shutdown delivery at a selected catch continuation |
| [MuxPublicationUnwind](../ConnectionManagement/MuxPublicationUnwind.agda) | Shutdown delivery at a selected pre-publication site |
| [ServerPeers.Protocols](../ConnectionManagement/ServerPeers.agda) | `deliverStartTraceShutdown` after `startTraceSelection`; directly calls `W.control acknowledgeDelivery` |

Other actions preserve the accumulated list and captured-descriptor projection,
or extend the registry at a real fork; physical phases may change. Capture retention already has the generic
[HandlerBirthEffects](../ConnectionManagement/Properties/HandlerBirthEffects.agda)
and opaque-run interfaces; these avoid replaying complete system reductions.

## Exact same-entry failed-fork control

**At the initial audit: confirmed model behavior by definition inspection;
proposed Agda witness not yet checked.** Use `ServerAdmissionPrefixFixtures 10 A.key₀`, so both requests
have the same full connection key but distinct caller, child and socket tokens:

1. Start from the actual empty `Protocols.initialize` state, perform both
   accepted handoffs, then the first admission through its real fork and
   `putMapBack`. Entry zero and its old physical child now exist.
2. The second admission takes that existing map, counts, allocates its promise
   and chooses the same entry. `Rules.CM.existingInbound` overwrites the
   `unnegotiated` value at **entry zero** with the new, unforked child token.
   `nextEntry` stays one; this is not fresh-entry allocation.
3. `failFork` and `restore` republish the saved map, which still names entry
   zero. They retain the committed heap overwrite. The old physical child
   remains recorded; the new child has no physical registry lookup.

The existing fresh-entry failed-fork fixtures do not prove this exact route:
their restored saved maps need not name the newly allocated entry. The old
[Admission scenario](../ConnectionManagement/Scenarios/Admission.agda) has a
local reserved-entry overwrite/restore control, but its old entry is a supplied
fixture rather than this initialized history.

A pending fork already has the overwritten heap value, but its map is taken,
preventing a fresh snapshot. The failed restore makes the saved binding visible
again. A raw `MuxHandlerExit` coordinator can then snapshot/read/request the
unforked target; physical delivery and result guards prevent manufacturing its
acknowledgement. Such an awaited target is not a collected member.

The drafted frontend prefix stops after restore while Server is still serving.
`ServerAdmission.allowed` gates actual coordinator operations on `closingCM`.
Do not obtain a purported initialized shutdown witness by changing that stage
with a record update. Reaching it requires the real peer/scope/IG cleanup suffix.

## Source fidelity and profile limits

**Confirmed source reading:** the local isolated network checkout reports HEAD
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`. At
`ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs`,
`includeInboundConnectionImpl` (:801–885) writes the existing TVar in the
Reserved/Unnegotiated branches before `forkConnectionHandler`. `modifyTMVar`
(:2366–2381) restores the old map on an exception, without rolling back that
separate committed TVar write. The shutdown finally (:527–548) snapshots the
map, late-reads entries, sends exceptions and collectively waits for results.
The project's [source ledger](../ConnectionManagement/SourceLedger.md) retains
the pin and mapping; consensus baseline is
`585a86117618ff86d7d5b541f9d23b03356d4c3a`.

**Open source question:** the inbound code ties `connThread` through `mfix`.
An interrupted or failed fork can leave an unresolved recursive value; the
model's symbolic child token does not determine concrete thunk evaluation or
the eventual exception. Same-full-key accepted-socket reachability is also a
scenario contract. This audit supplies no native replay, new Haskell defect,
or whole-trace source correspondence for the proposed model control.

**Inference:** physical membership of successfully acknowledged `collected`
workers can be established without proving that every selected entry is backed.
It does not establish live resource ownership, admission quiescence, all-handler
coverage, eventual result publication or whole-system shutdown. Independent raw
admissions can outlive owned-scope return and retain later enabled operations.

**Confirmed initializer limitation:** `HandlerSupervision.initial` excludes
pre-existing handler/cleanup/lifecycle/fault tables. It does not require every
preloaded connection-state worker reference to have physical registry history.
A preloaded `unnegotiated` entry with empty handler tables can therefore pass
initialization while naming a physically absent worker. The coordinator starts
with an empty collected list, and successful guarded acknowledgement remains
the relevant boundary.

## Acceptance handoff and checks

**Historical hand-off, before the coordinator's subsequent acceptance.**

The uncompiled proposal is
`/tmp/cm-collected-backing-20261105/acceptance-draft.agda.txt`. It contains:

- A 14-event initialized frontend same-entry reuse/fork-failure/restore prefix,
  explicit successor equations and an opaque `Runs` witness.
- Old-child presence, new-child absence, retained overwrite and raw-local
  snapshot/read/request controls, keeping the frontend stage gate explicit.
- An initialized preloaded-entry countercontrol and early frontend capture
  refusal.
- Inbound/outbound collected membership and expected physical lookup examples
  reusing `CMResultLifecycleChecks`, `HandlerResourceOriginChecks`,
  `OutboundHandlerResourceOriginChecks` and
  `HandlerBirthBackingChecks.ShutdownBatch`. The inbound run composes existing
  opaque entry, cleanup and final-wait paths.

`positive-api-draft.agda.txt` supplies the concrete opaque-run compositions
against the tentative combined `HandlerAuxFrontend.Frontend` endpoint.
`frontend-tracefault-draft.agda.txt` supplies the exact
`startTraceSelection`-to-`MuxStartupUnwind.start` inversion and the derived
owner-presence/acknowledgement obligations. Both are in the same temporary
directory, uncompiled and subject to the final API.

No Agda process, native replay or external browsing ran for this audit. The
draft must be adapted to the final increment-58 API and pass the coordinator's
focused/full acceptance queue before any proof-completion claim. No shared
source, acceptance, presentation or project-state file was edited by this lane.

## Increment 59 premise audit

**Confirmed by definition inspection:** `ServerPeers.Protocols.initialize`
retains arbitrary `OutboundMachine.Configuration.acquiring` frames.
`OutboundHandlerSupervision.initial` delegates to `HandlerSupervision.initial`;
the latter excludes existing handler/cleanup/lifecycle/fault tables, while
`ServerAdmission.initial` excludes admissions/sockets. Neither requires empty
acquisition frames or promise/result heaps. `Rules.OutboundAcquire.forkOK` and
`OutboundHandlerSupervision.forkOutbound` check the actual fork/child guards,
but do not establish captured entry/promise allocation history.

**Subsequent model acceptance — 5 November, increment 59:**
`Protocols.PreloadedAcquisitionForkControl` now checks that exact initialized
fork, physical descriptor, absent captured entry/promise, and created socket;
it also refutes `HandlerResourceFacts.Facts` and checks the paired `O.initial core`
immediate-fork refusal. See the
[accepted result and validation](../ConnectionManagement/Supervision.md#fifty-ninth-increment-initializer-boundary-and-gap-aware-resource-histories).
This supersedes the planning-stage “unperformed” status of the short control.

**Open question, not a checked countertheorem:** the inferred real
scope/IG-to-CM collected suffix remains unperformed. Missing captured-entry
cleanup can block completion; no final wait for this malformed case is asserted.
Do not substitute a data-only Server-stage change for the actual suffix.

Existing outbound-origin APIs explicitly use `initialize (OutboundMachine.initial core)`.
Increment 59 now makes the witnessed inbound occurrence/alignment premises explicit;
increment 58's arbitrary initializer remains unchanged. Preloaded promise/result heaps
also prevent inferring global freshness from allocation-event existence alone.
This model audit retains network pin `96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`;
no new source replay or Haskell defect is claimed.


**Subsequent inbound result — increment 60:**
[Automatic inbound reconstruction](../ConnectionManagement/Supervision.md#sixtieth-increment-automatic-inbound-occurrence-reconstruction)
uses the successful Server initializer's empty admissions table and actual enabled
inbound fork to derive the earlier allocation/selection and resource facts.
The preloaded **outbound acquisition** control above remains valid; this inbound
result does not remove that profile boundary or prove a malformed collected suffix.
