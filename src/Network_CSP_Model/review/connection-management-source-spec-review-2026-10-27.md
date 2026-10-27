# Connection-management review against leios-prototype and network-spec §5 (2026-10-27)

Hand-off document for a follow-up agent. Part A lists divergences between the
`ConnectionManagement/` model and the pinned Haskell source; these are actionable
in this repository. Part B lists incorrect descriptions in the network
specification §5; these are not fixed here (they are errata for upstream
`docs/network-spec/connection-manager.tex`). Part C lists drift between the pin
and ouroboros-network `main`.

All model paths are relative to `src/Network_CSP_Model/ConnectionManagement/`.
"Verified" means the finding was re-checked by hand against the quoted source
lines after the review agent reported it; the other findings were checked by the
review agent with quoted source and Agda lines but not re-checked by hand.

## 0. Setup

- Source pin: ouroboros-network `96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`
  (leios-prototype tip, "Merge the 2026-10-01 network release
  (ouroboros-network-1.3.0.0) into leios-prototype"), pinned by ouroboros-consensus
  leios-prototype `cabal.project` (consensus `585a8611…`).
- The local `../ouroboros-network` checkout on branch `leios-prototype` is **stale**
  (103 commits behind the pin). Do not read source from its working tree. The pin
  commit object has been fetched into that clone, so read it with
  `git -C <ouroboros-network> show 96ee6e0e:<path>` or export it:
  ```
  git -C <ouroboros-network> archive 96ee6e0e ouroboros-network/framework network-mux/src \
    ouroboros-network/lib/Ouroboros/Network/PeerSelection ouroboros-network/lib/Ouroboros/Network/Diffusion \
    ouroboros-network/lib/Ouroboros/Network/Diffusion.hs docs/network-spec | tar -x -C "$TMPDIR/net96ee"
  ```
- Source paths below are abbreviated: `Core.hs`, `Types.hs`, `ConnMap.hs`, `State.hs`
  are under `ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/`;
  `InboundGovernor.hs`, `ConnectionHandler.hs`, `Server.hs`, `ConnectionId.hs` under
  `ouroboros-network/framework/lib/Ouroboros/Network/`; `Mux.hs` and `JobPool.hs`
  under `network-mux/src/{Network,Control/Concurrent}/`; `PeerStateActions.hs`,
  `Governor/*.hs` under `ouroboros-network/lib/Ouroboros/Network/PeerSelection/`;
  `Policies.hs` is `ouroboros-network/lib/Ouroboros/Network/Diffusion/Policies.hs`.
- Typecheck from `src/Network_CSP_Model/` (see `CLAUDE.md`); endpoints are listed in
  `ConnectionManagement/README.md`.

## Part A — model vs pinned source

### A1. Medium — initiator failure overtakes queued mini-protocol results (Verified)

- Model: `Subsystem.agda:257-264` (`advance (observeInitiatorFailure ref)`), with
  `Rules/IGRegistration.agda:369-371,378-379` (`monitorCompletion`, `startOnDemand`).
- Source: `JobPool.hs:160-164`; `Mux.hs:429-431,459-464`.
- Source: every mini-protocol job result, initiator or responder, is written to one
  FIFO completion queue (`atomically $ writeTQueue cq res`). The mux monitor takes
  job results first (`FirstToFinish (EventJobResult <$> JobPool.waitForJob jobpool)`)
  and processes `MiniProtocolException` only in queue order:
  `writeTVar muxStatus $ Failed e`, `TraceExceptionExit`, `TraceState Dead`, `throwIO e`.
- Model: `observeInitiatorFailure` fires whenever the mux is `M.ready` and the
  callback is `M.returned`; it does not consult the pending `completions` queue and
  is not subject to the tracked-handler phase gate that `allowIG` applies to IG
  actions.
- Consequence (spurious traces): a responder clean exit queued before the initiator
  failure is dropped (no `MiniProtocolTerminated`, `RemoteDemotedToWarm`,
  `WaitIdleRemote`, no counter decrement); an on-demand responder start can happen
  after the failure was queued; during tracked `poolClosing` the status can become
  `Failed` before pool closure.
- Suggested fix: route initiator results through the same `completions` queue (or
  require `completions` empty before `observeInitiatorFailure`), and gate it by the
  same phase condition as other monitor actions. Update `Outbound.md:647`, which
  only says it "changes a looked-up mux's status/callback".
- Acceptance: a negative/scenario module showing a queued responder clean exit is
  processed before the failure; existing endpoints still typecheck.

### A2. Low — IG mux tracer attached regardless of provenance/data flow (Verified)

- Model: `Rules/IGRegistration.agda:321-326` (`installHandle` always sets
  `just (M.counters (+ 0) (+ 0))`), `Rules/MuxRuntime.agda:155-157` (`traceSTM k
  muxStopped` always writes `muxFinished k`).
- Source: `ConnectionHandler.hs:359-369` (outbound handler) — the IG tracer and
  `ResponderCounters` are added only for `InResponderMode … | Duplex <-
  connectionDataFlow agreedOptions`; otherwise `_notResponder -> pure $
  Mx.tracersWithBearer connectionId muxTracers` ("the IG will never be informed of
  this remote"). Compare inbound `ConnectionHandler.hs:437-440`.
- Consequence: an outbound-unidirectional mux would enqueue `MuxFinished` into the
  capacity-100 IG queue and could block its monitor on a full queue; impossible in
  source. No current scenario installs an outbound-unidirectional handle, so
  reachability today is unverified.
- Suggested fix: pass provenance/data flow to `installHandle` and attach counters
  and the IG trace only for the duplex/responder case. Also see C2.

### A3. Low — missing descriptor takes precedence over expired-RemoteIdle retry

- Model: `Rules/IGRegistration.agda:337-338` (`missingDescriptor`, defined at
  `:235-237`, checked before `traceSTM`), compare `Rules/MuxRuntime.agda:160-163`.
- Source: `InboundGovernor.hs:647-676` — `getProtocolTemp miniProtocolNum
  csMiniProtocolMap` is lazy and forced only in `commit`; the `RemoteIdle timeoutSTM
  -> do expired <- timeoutSTM; if expired then retry else commit` branch runs first.
- Consequence: with an expired idle timer and a same-key replacement registration
  lacking protocol `n`, source retries; model raises `M.tracerFailed n`. The claim in
  `IGRegistration.md` that a missing descriptor is "not misreported as queue retry"
  holds only while the timer has not expired.
- Suggested fix: check the expired-RemoteIdle retry before `missingDescriptor`, or
  document the restriction.

### A4. Low — target sanity predicate weaker than source; ignore semantics differ

- Model: `Rules/OutboundGovernor.agda:40-41` (`sane t` only checks
  `active ≤ established ≤ known`); `Subsystem.agda:156-158` (`setTargets` refused when
  not sane).
- Source: `PeerSelection/Governor/Types.hs:265-279` (`sanePeerSelectionTargets` also
  requires `active <= 100`, `established <= 1000`, `known <= 10000`, plus root and
  big-ledger clauses); `Governor/Monitor.hs:69-71` (`check (targets' /= targets &&
  sanePeerSelectionTargets targets')` on the *current* TVar value).
- Consequence: the model accepts e.g. active = 200. In source, a sane value
  overwritten by an insane one before the governor reads it is never applied; in
  the model the earlier sane value stays pending and is applied.
- Suggested fix: add the missing clauses (or document the weaker predicate) and
  model target input as an overwritable variable read by the governor.
  `Outbound.md` says "Targets must be sane", which implies the source predicate.

### A5. Low — `clearFailDelay = 60`, production policy is 120 (Verified)

- Model: `Subsystem.agda:70` (`… 0 0 5 60 nothing false`: `maxRetries = 5`,
  `clearFailDelay = 60`); used by `Rules/OutboundGovernor.agda:205,289-297`.
- Source: `Policies.hs:170-171` (`policyMaxConnectionRetries = 5`,
  `policyClearFailCountDelay = 120 -- seconds`). The 60 mirrors
  `SourceReplay/GovernorCMReplay.patch:141`, not production.
- Also: `Outbound.md:802-803` says `maxRetries = 5` is "a model setting, not a claim
  about … deployment default", but production uses exactly 5.
- Suggested fix: document both values with their provenance (production vs replay),
  or switch `clearFailDelay` to 120.

### A6. Low — ShutdownNode choosable for any CM fault; governor continues afterwards

- Model: `Rules/PeerJobs.agda:113` (`collectAcquire … just (Cases.raised _) = just
  (set f acquirePolicy w)`), `:201-206` (`chooseNodePolicy` → `nodeDelivery` →
  `deliverNodeException` → `failedEstablishment f w`, then ordinary retry).
- Source: `PeerStateActions.hs:798-801` (`ShutdownNode -> throwTo spsMainThreadId e
  >> throwIO e`); `Diffusion.hs:286-293,591` (`spsRethrowPolicy = rethrowPolicy`
  maps only `IOManagerError -> ShutdownNode`, everything else `mempty`).
- Consequence: over-approximation — the environment can choose ShutdownNode for e.g.
  `ConnectionExists`, and post-ShutdownNode traces continue as if the node were
  alive. `Outbound.md:759` covers only ShutdownPeer.
- Suggested fix: restrict ShutdownNode to an `IOManagerError`-like abstract fault, or
  terminate the configuration after it; at minimum document it.

### A7. Low — retried reuse selection is not deterministic in the model

- Model: `Rules/OutboundAcquire.agda:121-125`, `Rules/OutboundCases.agda:28`,
  `Outbound.md:64-67`.
- Source: `Core.hs:1276-1279,1379-1388` — `stdGen <- stateTVar stdGenVar
  Random.splitGen` and `State.lookupByRemoteAddr stdGen peerAddr state` in one STM;
  Terminating/Terminated branches `retry`, which rolls back the split, so a re-run
  with unchanged TVars re-picks the same bucket member.
- Model: `select (just e)` lets the environment pick any member on each attempt.
- Suggested fix: document this over-approximation next to "concrete PRNG
  state/distribution is abstract"; the comment "retries on terminal entries until
  the map changes" should also mention `stdGenVar` changes by other threads.

### A8. Low — stale docs and comments

- `Outbound.md:55-56` names Core `requestOutboundConnection` /
  `unregisterOutboundConnection`; at the pin they are `acquireOutboundConnection` /
  `releaseOutboundConnection` (`Types.hs:577,589`), implemented by
  `acquireOutboundConnectionImpl` (`Core.hs:1264`) and
  `releaseOutboundConnectionImpl` (`Core.hs:1834`).
- `HandlerOrigin.md:19` says "this increment does not model outbound acquisition";
  outbound acquisition is now executed through the same `installHandle` boundary.
- `Rules/Handshake.agda:123-124` says IG consumption is absent until IG batch/
  registration rules exist; `Rules/IGBatch` and `Rules/IGRegistration` now drain it.
- `Store.agda:3-4` says source ordered/random remote selection is not implemented;
  `OutboundAcquire.validSelection` (`:55-64`) now implements reservation-priority
  bucket selection.

### A9. Low — wrong or truncated source citations

| Location | Current cite | Correct cite | Note |
|---|---|---|---|
| `Pruning.md:15` | `ConnectionId.hs:43–53` | `ConnectionId.hs:41–44` | file has 49 lines |
| `Outbound.md:569` | `Core.hs:625–661` | `Core.hs:606–662` | removal 641–653, close 655–662 |
| `SourceLedger.md:481` `[include]` | `#L778-L1040` | `#L780-L1101` | omits identity-guard tail and `computeConnStateOnError` |
| `RemoteState.md:8` | `InboundGovernor.hs#L464-L518` | `#L463-L513` | 515–520 is `RemotePromotedToHot` |
| `InboundRelease.md:7` | `InboundGovernor.hs:529–568` | `529–572` | doc relies on `_otherwise -> return Nothing` at 572 |
| `IGRegistration.md` | peer-commit readiness `949–959` | `945–955` | 958–960 is `IGAssertionLocation` |
| `SourceLedger.md` `[diffusion]` | `Diffusion.hs#L625-L825` | add `539-600` | CM wiring and peer-state-actions wiring (timeouts, `spsRethrowPolicy`) |
| `SourceLedger.md` `[og-monitor]` | `Monitor.hs#L97-L150` | extend to `L320` | demotion application 166–257, `asyncDemotion` 262–320 |
| `SourceLedger.md` `[registry]` | `ClientRegistry.hs#L75-L193` | add `196-207`, `217+` | `cleanup` and `bracketSyncWithFetchClient` |

### A10. Confirmed consistent (no action)

CM admission order and hard limit; handshake consumer; cleanup and TIME_WAIT;
outbound acquire/release case tables, including `FirstToFinish` ordering and the
prune branch; inbound release, promotion/demotion, pruning selection; IG event
families and `firstOf` priority; remote-state updates; responder restart/terminate;
`runMiniProtocolSTM` check order; mux monitor priority and shutdown order; peer
status transitions; establish/activate/deactivate/close actions and timeouts;
`waitForOutboundDemotion`; job pool; failure accounting and backoff
`5*2^(min (pred fc) 5) ± 2`. The three `SourceReplay/*.patch` files
`git apply --check` cleanly against the pin (excluding `.cabal` hunks).

## Part B — incorrect descriptions in network-spec §5

Applies to `References/Network/network-spec.pdf` and to the latest published PDF:
`docs/network-spec/` is byte-identical between the pin and ouroboros-network `main`
`4646039f` (2026-10-22); `connection-manager.tex` was last changed 2025-06-16
(`c9e80366`). The CM method renames landed in PR #5000 on 2024-10-29, the same day
the CM chapter was added (#5001) with the old names. Page numbers are printed
pages (PDF page = printed + 2). These are errata for upstream, not tasks in this
repository; a follow-up could draft an upstream issue or PR from them.

High:

1. §5.8.2 API outdated (p.55–56): `requestOutboundConnection` is
   `acquireOutboundConnection :: DiffusionMode -> peerAddr -> Provenance -> …`
   (`Types.hs:500`; `Provenance = Inbound` only reuses, never connects;
   added in 0.24.0.0); `includeInboundConnection` takes a `Word32` hard limit and a
   `ConnectionId` (`Types.hs:503-507`); `unregister*` are `release*` taking
   `ConnectionId`, outbound returns `OperationResult AbstractState`
   (`Types.hs:589-594,650-653`); `promotedToWarmRemote` requires `HasResponder`, not
   `HasInitiator` (`Types.hs:608-611`; tex line 718); `OperationResult` has
   `TerminatedConnection` and `InState` is `AbstractState` (`Types.hs:448-451,674`);
   `Connected` carries `DataFlow`, `Disconnected` a `DisconnectionException`
   (`Types.hs:478-494`).
2. "both are non-blocking" (p.64; tex lines 1096, 1278) is false: outbound release
   waits `outboundIdleTimeout` (`Core.hs:2007-2020`), and the caller waits
   synchronously (`PeerStateActions.hs:1104`). Verified.

Medium:

3. "InitiatorMode is not allowed" (p.55) is false: `Diffusion.hs:538-548` runs a CM
   with `NotInResponderMode` and an initiator-only handler. Verified.
4. Notifying the IG (p.53, 62, 64, 76): the server only calls
   `includeInboundConnection` (`Server.hs:240-248`); the CM writes `NewConnection`
   (`Core.hs:983-988`). Outbound notification happens only after a fresh Duplex
   negotiation (`Core.hs:1617-1630`); never for unidirectional, never on hand-over
   (`Core.hs:1336-1346,1359-1369,1661-1702`).
5. DemotedToCold^{*}_{Local} (p.62): from `OutboundState^τ Duplex` the target is
   `InboundIdleState Duplex` with a prune check, and `DuplexState → InboundState
   Duplex` is omitted (`Core.hs:1903-1982`); the text contradicts the spec's own
   figure (tex line 872).
6. Prune bullets (p.63; table rows p.67, 69): `DuplexState → InboundState Duplex`
   never prunes and cannot raise the inbound count (`Core.hs:209-212,1968-1985`);
   the `OutboundState^τ` case targets `InboundIdleState`. Verified.
7. Commit triggers and idle-timer owner (p.61–62): only `releaseInboundConnection`
   commits (`Core.hs:1183-1196`); outbound release from `InboundIdleState` is a no-op
   (`Core.hs:1947-1951`); the idle timer belongs to the IG, not the server
   (`InboundGovernor.hs:470-481,529-532`).
8. Acquire on `UnnegotiatedState Inbound` (p.66, 68): ends in `OutboundState^τ
   Duplex` via Awake^{Duplex}_{Local}, not `DuplexState` (`Core.hs:944-952,
   1694-1702`); `ReservedOutboundState` throws `ConnectionExists`
   (`Core.hs:1284-1289`); inbound unidirectional gives `ForbiddenConnection`.
9. After AwakeDuplex Local (p.74): idle-timer expiry makes the IG run `CommitRemote`,
   giving `TimeoutExpired`/`KeepTr` and then `RemoteCold` (`Core.hs:1145-1157`,
   `InboundGovernor.hs:556-570`), not AwakeDuplex Remote.
10. "60s idle period before reconnecting" (p.66; tex line 1445): reconnect delays are
    10 s after a protocol error and 5 s doubling after a connection failure
    (`Policies.hs:83`, `Governor/EstablishedPeers.hs:463-530`); the 60 s values are
    TIME_WAIT and the inbound peers retry delay.
11. Pruning decided by the IG (p.64): `prunePolicy` runs in the CM's
    `mkPruneAction` (`Core.hs:756`) and ranks by upstreamness before a random score
    (`Policies.hs:273-300`).
12. Overwritten (p.67): the reservation is keyed by `UnknownLocalAddr`
    (`Core.hs:1410`), while `includeInboundConnection` looks up the full
    `ConnectionId` (`Core.hs:837`; `ConnMap.hs:171-174`), so inbound creates a fresh
    entry and the outbound attempt fails with `ConnectionExists`
    (`Core.hs:1510-1523`). Confidence medium.

Low:

13. Acquire/include errors (p.55): CM errors are thrown, not returned
    (`Core.hs:1286-1395,1424`); `Disconnected` also covers the CM-enforced hard
    limit, handshake query and terminating connection (`Core.hs:802-806,879-891`).
    This also corrects §5.6, which makes the server alone responsible for limits.
14. Tables: 5.7 (p.73) `DuplexState` row goes to `OutboundState^τ Duplex` and returns
    `UnsupportedState`; `InboundState` row returns `UnsupportedState`; True/False is
    `CommitTr`/`KeepTr` (`Core.hs:1203-1230`). 5.2 "•" row with `Provenance = Inbound`
    throws `InboundConnectionNotFound` (`Core.hs:1393-1397`). 5.3 `InboundState
    Duplex` returns `UnsupportedState` (`Core.hs:1952-1966`); `InboundIdleState
    Unidirectional` does nothing (`Core.hs:1947-1951`). 5.4 `UnnegotiatedState` is
    accepted as self-connection (`Core.hs:854`); "•" row depends on the hard limit.
15. Smaller: p.74 release from `OutboundIdleState^τ` returns `CommitTr`, not a no-op
    (`Core.hs:1178-1186`, `InboundGovernor.hs:539-546`); p.78 `WaitIdleRemote` with
    `TerminatedConnection` is not "forgotten" (`InboundGovernor.hs:489`); p.59
    Reserve/Overwritten cannot occur in ResponderMode (`Types.hs:548-552,577-580`);
    p.57 `OutboundIdleState^τ` listed without `DataFlow` (`State.hs:212`).

Not verified (sources outside the export): "Duplex only for versions >
NodeToNodeV_7"; "two threads per pipelined mini-protocol"; "the scheduled connect
will fail" after Overwritten.

## Part C — drift between the pin and ouroboros-network main

`main` `4646039f` contains release 2.0.0.0 (2026-10-21), not yet merged into
leios-prototype. The model correctly follows the pin; these matter when the pin
moves.

- C1. Stale `MuxFinished` no longer blocks. At the pin the IG blocks on
  `Mux.stopped` (`InboundGovernor.hs:400-402`) and the model matches it
  (`Rules/IGRegistration.agda:199-203`, `waitStopped`). On `main` the IG checks
  `MuxFinished` without blocking and ignores an event from an earlier connection
  with the same `ConnectionId` (new trace `TrStaleMuxFinished`); previously this
  could stall the IG and then unregister the replacement connection.
- C2. `mkMiniProtocolInfo` / `toMiniProtocolInfos` take `Provenance` and `DataFlow`
  to filter supported mini-protocols; relevant to A2 and to which responders start
  on unidirectional connections.
- C3. The IG traces `TrUnexpectedlyFalseAssertion` when a responder of a registered
  connection starts or terminates while its responders are no longer tracked.

## Suggested order of work

1. A1 (only medium model bug), with a scenario/negative control.
2. A8 and A9 (mechanical doc fixes).
3. A2–A7: fix or document each over-approximation.
4. Optionally draft Part B as an upstream issue; port C1–C3 when the pin advances.
