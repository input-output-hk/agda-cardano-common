# Outbound hot→warm demotion at the leios-prototype pins (research notes)

Revisions: ouroboros-network `4b3ab7664f609a1aee0f0c24dcfcfd0ab899fc42` ("the pin"); ouroboros-consensus
`27fa649ff`. Consensus's `cabal.project:59-68` pins ouroboros-network at exactly this commit
("-- Points to ouroboros-network/leios-prototype ... tag: 4b3ab7664f..."), so both trees are consistent.
typed-protocols: consensus pins `9b4627221a` (`cabal.project:70-74`); that commit is NOT in the local clone
(local HEAD `4fc22b8`), so typed-protocols driver citations below are at `4fc22b8` (Collect semantics are
the long-standing ones; flagged as not verified at the exact pin).

## Citation key

ouroboros-network (paths from repo root):

| Key | File |
|---|---|
| `FMux` | `ouroboros-network/framework/lib/Ouroboros/Network/Mux.hs` |
| `PSA` | `ouroboros-network/lib/Ouroboros/Network/PeerSelection/PeerStateActions.hs` |
| `Pol` | `ouroboros-network/lib/Ouroboros/Network/Diffusion/Policies.hs` |
| `Diff` | `ouroboros-network/lib/Ouroboros/Network/Diffusion.hs` |
| `AP` | `ouroboros-network/lib/Ouroboros/Network/PeerSelection/Governor/ActivePeers.hs` |
| `Mon` | `ouroboros-network/lib/Ouroboros/Network/PeerSelection/Governor/Monitor.hs` |
| `GTy` | `ouroboros-network/lib/Ouroboros/Network/PeerSelection/Governor/Types.hs` |
| `Churn` | `ouroboros-network/lib/Ouroboros/Network/PeerSelection/Churn.hs` |
| `CMsg` | `ouroboros-network/api/lib/Ouroboros/Network/ControlMessage.hs` |
| `Lim` | `ouroboros-network/api/lib/Ouroboros/Network/Protocol/Limits.hs` |
| `N2N` | `cardano-diffusion/lib/Cardano/Network/NodeToNode.hs` |
| `CSCodec` | `ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/ChainSync/Codec.hs` |
| `CSTL` | `cardano-diffusion/protocols/lib/Cardano/Network/Protocol/ChainSync/Codec/TimeLimits.hs` |
| `CSPipe` | `ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/ChainSync/PipelineDecision.hs` |
| `BFCodec` / `TxCodec` / `KACodec` / `PSCodec` | `ouroboros-network/protocols/lib/Ouroboros/Network/Protocol/{BlockFetch,TxSubmission2,KeepAlive,PeerSharing}/Codec.hs` |
| `BFC` | `ouroboros-network/lib/Ouroboros/Network/BlockFetch/Client.hs` |
| `BFCS` | `ouroboros-network/lib/Ouroboros/Network/BlockFetch/ClientState.hs` |
| `BFReg` | `ouroboros-network/lib/Ouroboros/Network/BlockFetch/ClientRegistry.hs` |
| `TxOut` | `ouroboros-network/lib/Ouroboros/Network/TxSubmission/Outbound.hs` |
| `KA` | `ouroboros-network/lib/Ouroboros/Network/KeepAlive.hs` |
| `PS` | `ouroboros-network/lib/Ouroboros/Network/PeerSharing.hs` |
| `Mux` | `network-mux/src/Network/Mux.hs` |
| `Ingress` | `network-mux/src/Network/Mux/Ingress.hs` |
| `CMCore` | `ouroboros-network/framework/lib/Ouroboros/Network/ConnectionManager/Core.hs` |

ouroboros-consensus (paths from repo root):

| Key | File |
|---|---|
| `CN2N` | `ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/Network/NodeToNode.hs` |
| `Node` | `ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/Node.hs` |
| `LN` | `ouroboros-consensus/src/ouroboros-consensus/LeiosDemoOnlyTestNotify.hs` |
| `LF` | `ouroboros-consensus/src/ouroboros-consensus/LeiosDemoOnlyTestFetch.hs` |
| `LDL` | `ouroboros-consensus/src/ouroboros-consensus/LeiosDemoLogic.hs` |
| `CSC` | `ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/MiniProtocol/ChainSync/Client.hs` |
| `CSJ` | `ouroboros-consensus/src/ouroboros-consensus/Ouroboros/Consensus/MiniProtocol/ChainSync/Client/Jumping.hs` |

typed-protocols (local `4fc22b8`): `TPDrv` = `typed-protocols/src/Network/TypedProtocol/Driver.hs`.

---

## 1. Mini-protocol temperatures

### Facts (cited)

- Three temperatures: `FMux:90-94` "There are three kinds of applications: warm, hot and established (ones
  that run in both warm and hot states)." / `data ProtocolTemperature = Established | Warm | Hot`.
- Bundle: `FMux:167-184` `data TemperatureBundle a = TemperatureBundle { withHot :: !(WithProtocolTemperature Hot a), withWarm :: ..., withEstablished :: ... }`;
  monoid is pointwise (`FMux:186-193`), so bundles can be `<>`-appended per temperature.
- `FMux:217-218` `type OuroborosBundle mode initiatorCtx responderCtx bytes m a b = TemperatureBundle [MiniProtocol mode ...]`.
- Network's N2N bundle `N2N:240-325` (`nodeToNodeProtocols`):
  - `N2N:253-280` hot: "-- Hot protocols: 'chain-sync', 'block-fetch' and 'tx-submission'." — ChainSync, BlockFetch,
    TxSubmission (all `miniProtocolStart = StartOnDemand`), plus Peras cert/vote diffusion only if `PerasSupported`
    (`N2N:281-298`). Consensus negotiates Peras unsupported (`CN2N:1661-1665`, "consensus currently negotiates 'PerasUnsupported'").
  - `N2N:300-301` warm: `(WithWarm [])` "-- Warm protocols: reserved for 'tip-sample'." — EMPTY.
  - `N2N:303-325` established: KeepAlive (`StartOnDemandAny`) and PeerSharing (only if `PeerSharingEnabled`).
- Consensus adds the Leios protocols as HOT by monoid-appending a second bundle:
  - initiator-only: `CN2N:1567-1588` `<> mempty { withHot = WithHot [ MiniProtocol { miniProtocolNum = leiosNotifyMiniProtocolNum, ... InitiatorProtocolOnly (... aLeiosNotifyClient ...) }, MiniProtocol { miniProtocolNum = leiosFetchMiniProtocolNum, ... aLeiosFetchClient ... } ] }`
    (comment `CN2N:1570` "-- TODO: Also move the leios protocols into NodeToNodeProtocols?").
  - duplex: `CN2N:1637-1659`, same, `InitiatorAndResponderProtocol` with `aLeiosNotifyServer` / `aLeiosFetchServer`.
  - Numbers: `LN:108-109` `leiosNotifyMiniProtocolNum = Mux.MiniProtocolNum 18`; `LF:91-92` `leiosFetchMiniProtocolNum = Mux.MiniProtocolNum 19`.
  - Both `StartOnDemand` (`CN2N:1573`, `1581`).

Summary at these revisions:

| Temperature | Protocols (N2N, consensus leios-prototype) |
|---|---|
| Hot | ChainSync (2), BlockFetch (3), TxSubmission2 (4), LeiosNotify (18), LeiosFetch (19) [Peras off] |
| Warm | none |
| Established | KeepAlive (8), PeerSharing (10, if enabled) |

(Protocol numbers other than 18/19 are the usual N2N ones; not re-cited here.)

---

## 2. The hot→warm demotion action

### Facts (cited)

**Who decides.** Governor jobs `jobDemoteActivePeer` are scheduled by the "above target" rules:
`AP:741`, `AP:851`, `AP:943` (in `aboveTargetBigLedgerPeers` `AP:657`, `aboveTargetLocal` `AP:756`,
`aboveTargetOther` `AP:859`). Churn lowers the active target and waits `deactivateTimeout` for it
(`Churn:433-437` `updateTargets DecreasedActivePeers numberOfActivePeers deactivateTimeout decreaseActivePeers ...`;
big-ledger analogue `Churn:391-395`).

**The job.** `AP:1041-1043`: `job = do deactivatePeerConnection peerconn; return . Completion ...` — on normal return
the peer is removed from `activePeers` but stays established (`AP:1054-1076`, `TraceDemoteHotDone`) = **Warm**.

**`deactivatePeerConnection`** (`PSA:984-1045`):
- `PSA:997-999` (atomically, only if `PeerHot`):
  `writeTVar (getControlVar SingHot pchAppHandles) Terminate` / `writeTVar (getControlVar SingWarm pchAppHandles) Continue`.
  Established control var is not touched, so KeepAlive/PeerSharing keep running.
- Hot initiators observe it via their context: `PSA:465-467` `ExpandedInitiatorContext { ..., eicControlMessage = readTVar (getControlVar tok appHandles), ... }`
  (consensus reads it as `eicControlMessage = controlMessageSTM`, e.g. `CN2N:1114`, `1446`, `1491`).
- It then WAITS (last-to-finish) for all hot initiators, under a timeout:
  `PSA:1001-1005` "-- Hot protocols should stop within 'spsDeactivateTimeout'." `timeout spsDeactivateTimeout $ join . atomically $ do res <- awaitAllResults SingHot pchAppHandles`.
  `awaitAllResults` (`PSA:409-423`) `sequence`s each protocol's completion STM, i.e. it blocks (retry) until every hot
  mini-protocol has returned or errored (the per-protocol STM is mux's completion action, `PSA:1171-1173`, `Mux:762-772`
  "The result is a STM action to block and wait on the protocol completion.").
- All succeeded → hot marked not running and status `PeerHot → PeerWarm`, trace `HotToWarm` (`PSA:1007-1014`).
- Some errored → status `PeerCooling`, trace `PeerStatusChangeFailure (HotToCooling ..) (ApplicationFailure errs)`, rethrow
  `MiniProtocolExceptions` (`PSA:1015-1023`). (Mux has already failed: a mini-protocol exception sets mux `Failed` and
  rethrows, `Mux:458-463`.)
- **Timeout** (`PSA:1025-1033`):
  `Nothing -> do Mux.stop pchMux; trace <- atomically $ updateUnlessCoolingOrCold pchPeerStatus PeerCooling; ... (HotToCooling pchConnectionId) TimeoutError; throwIO (DeactivationTimeout pchConnectionId)`.
  `Mux.stop` just enqueues `CmdShutdown` and "does not wait for any protocol threads to finish" (`Mux:173-179`).
- Design intent stated in the module doc `PSA:109-116`: "[synchronous /hot → warm/ transition]: Within a timeout, stop hot
  protocols and let the warm protocols continue running. If the timeout expires the connection is closed. Note that this
  will impact inbound side of a duplex connection. We cannot do any better: closing is a cooperative action since we
  require to arrive at a well defined state of the multiplexer (no outstanding data in ingress queue). This transition
  must use last to finish synchronisation of all hot mini-protocols."

**Timeout value / configuration.**
- `PSA:565-570` field `spsDeactivateTimeout :: DiffTime` "Peer deactivation timeout: timeouts stopping hot protocols."
- `Diff:586` `spsDeactivateTimeout = Diffusion.Policies.deactivateTimeout`.
- `Pol:25-31` `deactivateTimeout = 300` with comment "The maximal timeout on 'ChainSync' (in 'StMustReply' state) is @269s@, see `maxChainSyncTimeout` below." — **this comment is stale**, see §3 (`maxChainSyncTimeout = 911` at the pin).
- Not configurable at runtime: a top-level constant (also re-exported `ouroboros-network/lib/Ouroboros/Network/Diffusion/Configuration.hs:19`).
- Related: `closeConnectionTimeout = 120` (`Pol:40-41`) for warm→cold.

**What happens after a timeout or error (→ Cold).**
- `DeactivationTimeout` is a `PeerSelectionTimeoutException` (`PSA:528-530`), thrown out of the governor job; the job's
  `handler` (`AP:982-1039`) waits up to `c_PEER_DEMOTION_TIMEOUT` for the peer to become `PeerCold`:
  `AP:988-991` `timeout c_PEER_DEMOTION_TIMEOUT $ atomically $ monitorPeerConnection peerconn >>= check . (== PeerCold) . fst`,
  with `GTy:271` `c_PEER_DEMOTION_TIMEOUT = 10*60`.
  If it became cold: peer removed from `activePeers` AND `establishedPeers` (`AP:1015-1017`), trace `TraceDemoteHotFailed`
  (`AP:1027`). If that also timed out: peer kept in both sets, `DemotionTimeoutException` (`AP:1010-1014`, "It's quite bad if demoting fails").
- `PeerCooling → PeerCold` is driven by the peer monitoring loop: `PSA:682-685` `PeerCooling -> do waitForOutboundDemotion spsConnectionManager pchConnectionId; writeTVar pchPeerStatus PeerCold`
  (CM side: `CMCore:437-440`). So after `Mux.stop`, the connection is torn down via the connection handler/CM and the peer ends **Cold**.
- Backoff on this path: the job handler only removes the peer and sets the tepid flag; it does not call
  `KnownPeers.reportFailures` (`AP:1007-1017`). `reportFailures` is applied to *asynchronous* demotions to cold in
  `Mon:186-200` ("Asynchronous transition to cold peer can only be a result of a failure."), and the monitor excludes
  peers in `inProgressDemoteHot` (`Mon:298-302`, `305-308`). Repromote delays come from `ExitPolicy`
  (`epErrorDelay`/`epReturnDelay`, `PSA:928-937`).
- Asynchronous hot→warm also exists: if a hot protocol *returns* by itself, the monitoring loop calls
  `deactivatePeerConnection` (`PSA:744-748`); if a hot protocol *errors*, the peer goes `PeerCooling` (`PSA:709-720`).

### Inference
- For modelling: the outcome is a 3-way choice at the end of the bounded wait —
  all-hot-returned ⇒ Warm; some-hot-errored ⇒ Cold (via Cooling, mux failed); timeout (300 s) ⇒ `Mux.stop` ⇒ Cold
  (via Cooling) and the governor sees `TraceDemoteHotFailed`. Only the first ends Warm.

---

## 3. How hot initiators react to `Terminate`

### Facts (cited) — the mechanism
- `CMsg:7-22`: `data ControlMessage = Continue | Quiesce | Terminate`; "Terminate — The client is expected to terminate as soon as possible."
  `Quiesce` "is not used for any hot protocol".
- Helper `CMsg:43-55` `timeoutWithControlMessage`: `Terminate -> return Nothing; Continue -> retry; Quiesce -> retry` `` `orElse` (Just <$> stm) ``
  (Terminate wins over an available `stm` result).
- Polling is cooperative: each client reads `controlMessageSTM` only at its own (client-agency) decision points. A client
  blocked in a server-agency state is inside the typed-protocols driver, which does not look at the control var.
  Pipelined drivers: `TPDrv:303-307` `Collect Nothing` blocks on `readTQueue collectQueue`; `TPDrv:309-312`
  `Collect (Just k')` does `tryReadTQueue` and continues with `k'` if nothing is there.

### ChainSync client (consensus)
- Terminate is checked before each request: `CSC:1265-1268`
  `nextStep ... = Stateful $ \kis -> atomically controlMessageSTM >>= \case Terminate -> terminateAfterDrain n $ AskedToTerminate`.
  `terminateAfterDrain` = `drainThePipe n` then `terminate` (`CSC:910-914`); `drainThePipe` collects every outstanding
  reply with `CollectResponse Nothing` (`CSC:937-943`).
- At the tip the pipeline decision is non-pipelined: `CSPipe:181-183` `goZero Zero clientTipBlockNo serverTipBlockNo | clientTipBlockNo == serverTipBlockNo = (Request, goLow)`;
  `CSC:1420-1422` `(Zero, (Request, ..)) -> SendMsgRequestNext onMsgAwaitReply (handleNext ...)`.
  So a caught-up client sits in `StNext StCanAwait` → (MsgAwaitReply) → `StNext StMustReply` until the next header.
- Time limits used by consensus: `Node:738` `(timeLimitsChainSync llrnChainSyncIdleTimeout)`, from `CSTL`:
  `CSTL:64` `SingNext SingCanAwait -> shortWait` (`Lim:134-135` `shortWait = Just 10`);
  `CSTL:65-84` `SingNext SingMustReply`: `IsTrustable -> (Nothing, rnd)` (never), `IsNotTrustable ->` uniform in
  `(minChainSyncTimeout, maxChainSyncTimeout)`; `CSCodec:53-60` `minChainSyncTimeout = 601`, `maxChainSyncTimeout = 911`.
  (`CSTL:78-79` comment still says "picked uniformly from the interval 135 - 269" — stale.)
  `StIdle` (client agency) uses the idle timeout `ChainSyncIdleTimeout 3373` (`cardano-diffusion/lib/Cardano/Network/Diffusion/Configuration.hs:77`).
- Can it terminate while awaiting a server reply? **No**: in StCanAwait/StMustReply it must first receive the reply
  (RollForward/RollBackward); only then does it return to `nextStep` and see Terminate.
- Side note: in CSJ, a jumper may block in `jgNextInstruction` (`CSC:1277`, `CSJ:298-306`, retry while `nextJumpVar` is
  `Nothing`, `CSJ:448-450`) after the Terminate check, without re-reading the control var. Caught-up nodes are
  disengaged (`CSJ:433` `Disengaged DisengagedDone -> pur RunNormally`).

### BlockFetch client (network)
- `BFC:122-130`: in `senderAwait`, `result <- acknowledgeFetchRequest tracer controlMessageSTM stateVars; case result of Nothing -> ... return $ senderTerminate outstanding`;
  `BFCS:551-553` uses `timeoutWithControlMessage controlMessageSTM (takeTFetchRequestVar ...)`.
- `BFC:183-190` `senderTerminate Zero = Yield MsgClientDone (Done ())`; `senderTerminate (Succ n) = Collect Nothing (\_ -> senderTerminate n)`
  — it waits for every in-flight range (BFBusy/BFStreaming) before MsgClientDone.
- Limits `BFCodec:62-64`: `SingBFIdle = waitForever`, `SingBFBusy = longWait`, `SingBFStreaming = longWait` (`Lim:137-138` `longWait = Just 60`).
- Coupling: the BlockFetch client's registry bracket waits up to `deactivateTimeout` for the ChainSync client of the same
  peer to finish (`BFReg:160-163` `ExitCaseSuccess _ -> deactivateTimeout`; `BFReg:183-194`).
- Can it terminate while awaiting a server reply? It cannot abort an in-flight batch, but each batch is bounded by 60 s
  per state; it never waits for *new* data from the server.

### TxSubmission2 (outbound = initiator = "client")
- The only Terminate check: `TxOut:131-145`, on a **blocking** `MsgRequestTxIds` from the remote:
  `mbtxs <- timeoutWithControlMessage controlMessageSTM $ do ... check (not $ null txs) ...; case mbtxs of Nothing -> pure (SendMsgDone ())`.
  Non-blocking requests and `recvMsgRequestTxs` do not look at the control var (`TxOut:155-174`).
- In `StIdle` the remote (inbound/server) has agency and the client waits: `TxCodec:84` `SingIdle = waitForever`;
  `TxCodec:80-83` `SingInit = waitForever`, `SingTxIds SingBlocking = waitForever`, `SingTxIds SingNonBlocking = shortWait`, `SingTxs = shortWait`.
- So the outbound side can only stop when the remote inbound side next sends a blocking `MsgRequestTxIds`. (TxSubmission
  inbound is a *responder*; it is not started/stopped by outbound `PeerStateActions` — `startProtocols` only runs the
  initiator direction, `PSA:1176-1195`.)

### KeepAlive and PeerSharing (established — not stopped by hot→warm)
- KeepAlive client checks Terminate between pings: `KA:63-68` `decisionSTM ... Terminate -> return Terminate`, `KA:103` `Terminate -> pure (SendMsgDone (pure ()))`;
  limits `KACodec:105-106` `SingClient = Just 97`, `SingServer = Just 60`.
- PeerSharing client: `PS:115-123` first-to-finish between a request and `Terminate -> return Nothing`; `PSCodec:159-160` `SingIdle = waitForever`, `SingBusy = longWait`.
- Neither receives Terminate on hot→warm (`PSA:997-999` writes only the hot and warm vars).

### LeiosNotify client (consensus leios-prototype)
- Protocol: `LN:178-179` `StateAgency StIdle = ClientAgency`, `StateAgency StBusy = ServerAgency`; messages `LN:159-176`
  (`MsgLeiosNotificationRequestNext : StIdle → StBusy`, four replies `StBusy → StIdle`, `MsgDone : StIdle → StDone`). No
  MsgQuit/MsgCanceled at this revision (grep finds neither in the consensus tree).
- Time limits `LN:210-214`: `SingIdle -> waitForever`, `SingBusy -> waitForever`.
- Wiring `CN2N:494-515`: `leiosNotifyClientPeerPipelined (atomically $ controlMessageSTM >>= \case Terminate -> pure (Left ()); _ -> do Leios.awaitImmTipCanForecastNow ...; pure $ Right leiosNotifyPipelineDepth) ...`;
  `CN2N:1679-1680` `leiosNotifyPipelineDepth = 100 -- TODO magic number`; run with `timeLimitsLeiosNotify` (`CN2N:1453-1459`).
- Client body `LN:476-533`:
  - `go` evaluates `checkDone` first (`LN:482-484`); `Left x` → `drainThePipe x n` (`LN:485-487`);
  - `Right maxDepth`: `Zero -> sendAnother`; `Succ m -> Collect (if natToInt n >= maxDepth then Nothing else Just $ sendAnother stop n) (\MkC -> go stop m)` (`LN:488-494`);
  - `drainThePipe x (Succ m) = Collect Nothing (\MkC -> drainThePipe x m)`; only at `Zero` does it `Yield ... MsgDone` (`LN:525-533`).
- Can it terminate while awaiting a server reply? **No.** It can send `MsgDone` only after all `n` outstanding requests
  have been answered; there is no message that cancels an outstanding StBusy request.

### LeiosFetch client (consensus leios-prototype)
- Stop predicate `CN2N:693` `((== Terminate) <$> controlMessageSTM)` passed to `nextLeiosFetchClientCommand` (`LDL:679-734`):
  non-blocking `checkOrBlock` (`LDL:714-722`) and blocking `awaitStopOrRequest` (`LDL:726-734`) both test `stopSTM` first.
- Client body `LF:520-567`: no instruction and `n = Zero` → block on `next` (stop-or-request) (`LF:532`);
  `n = Succ m` → `Collect Nothing` (`LF:533-537`); `Left x` → `drainThePipe x n` (`LF:546-548`).
- Limits `LF:208-214`: `SingIdle -> waitForever`, `SingBlock -> longWait`, `SingBlockTxs -> longWait`.
- Can it terminate while awaiting a reply? It drains outstanding fetches (each bounded by 60 s); with nothing in flight it
  sees Terminate at once.

---

## 4. Mux / connection level

### Facts (cited)
- "Warm" = hot initiators finished, everything else still running: `PSA:109-111` (above); `PSA:250-253` "established and warm
  protocol are always running as far as mux is concerned when the peer is not cold"; after success the hot results are
  stored as `NotRunning` (`PSA:1008-1009`) so they can be restarted on the next warm→hot (`PSA:979` `startProtocols SingHot`).
- A finished initiator's mux slot becomes idle and is not restarted automatically: `Mux:342-343` `writeTVar miniProtocolStatusVar StatusIdle; putTMVar completionVar (Right result)`;
  `Mux:452-456` "Protocols that runs to completion are not automatically restarted." `runMiniProtocol` refuses a restart while one
  is running (`Mux:796-798` `ProtocolAlreadyRunning`).
- A mini-protocol exception kills the whole mux (`Mux:458-463` `writeTVar muxStatus $ Failed e ... throwIO e`), hence the
  whole connection (`PSA:137-139` "The multiplexer guarantees that whenever one of the mini-protocols errors the connection is closed.").
- An unfinished hot protocol when the deactivate timeout fires: `Mux.stop` (`PSA:1027`) — the entire mux shuts down,
  all mini-protocols (including established/warm, and on a duplex connection the responders) go with it.
- Ingress for a protocol whose initiator is not running still goes to that protocol's ingress queue; over the limit the
  demuxer throws: `Ingress:122-134` `if len' <= fromIntegral qMax then ... else throwSTM $ IngressQueueOverRun (msNum sdu) (msDir sdu)`.
- Connection manager on outbound hot→warm: `deactivatePeerConnection` makes no CM call (`PSA:986-1045`). The CM is involved
  only for warm→cold (`PSA:1104` `releaseOutboundConnection`) and Cooling→Cold (`PSA:683`, `PSA:843` `waitForOutboundDemotion`).
  Inbound governor: not involved in outbound hot→warm; `PSA:112` notes a closed connection "will impact inbound side of a duplex connection".

### Inference
- The ingress-queue rule is why an initiator cannot simply walk away with requests outstanding: late replies would sit in
  the idle protocol's queue (and either overrun it, killing the mux, or be read by the next hot incarnation in the wrong
  state). That matches `PSA:113-114` "we require to arrive at a well defined state of the multiplexer (no outstanding data in ingress queue)".
- A peer's own `MsgDone` on an outbound initiator ends the remote's responder of that protocol; for duplex connections the
  remote IG sees that responder terminate (GovernorWedge covers IG behaviour; not re-checked here).

---

## 5. Which hot protocols can block a timely hot→warm (Praos blocks arriving, no Leios load), and PR 2344

Scenario: caught-up node, outbound connection hot, new Praos block every ~20 s on average, LeiosNotify server has
nothing to send (no announcements, offers or votes), LeiosFetch has no requests.

| Hot protocol | When Terminate is written, it is typically ... | Terminates when ... | Blocks demotion past 300 s? |
|---|---|---|---|
| ChainSync | in `StMustReply` (non-pipelined at tip) | next header arrives (~one Praos block interval), then `nextStep` sees Terminate | **No** in this scenario. Only if no block for > 300 s (fact: StMustReply limit is 601–911 s untrusted, never for trustable; `CSTL:68-83`, `CSCodec:53-60`; so ChainSync alone can exceed `deactivateTimeout`, contrary to `Pol:27-28`'s comment) |
| BlockFetch | idle (`senderAwait`) or with a batch in flight | immediately, or after in-flight batches (≤ 60 s per state) | No |
| TxSubmission2 (outbound) | in `StIdle` waiting for the remote, or in a blocking `StTxIds` | at the next blocking `MsgRequestTxIds` (immediately if already in one) | Not in the usual case (inference: depends on the remote inbound policy; cannot be excluded from this side's code alone) |
| LeiosFetch | idle, n = 0 | immediately (`LDL:726-728`) | No |
| **LeiosNotify** | after it has pipelined requests the server never answers | **never** (no replies with no Leios load; `StBusy` = `waitForever`) | **Yes — always** |

### Facts behind the LeiosNotify row
- While Continue, the client sends requests up to depth 100 without waiting (`LN:488-502`, `Collect (Just sendAnother)` is
  non-blocking per `TPDrv:309-312`), then blocks in `Collect Nothing` at `n >= 100` (`LN:493`, `TPDrv:303-304`).
- When it does see Terminate (in `checkDone` between steps, `LN:484-487`), it enters `drainThePipe`, which needs one reply per
  outstanding request (`LN:530-533`). With no Leios traffic none arrives, and `StBusy` has no time limit (`LN:214`).
- Therefore `awaitAllResults SingHot` never completes, `timeout spsDeactivateTimeout` (300 s) fires, `Mux.stop`, `PeerCooling`,
  `DeactivationTimeout` (`PSA:1025-1033`), the governor job handler waits for `PeerCold` and removes the peer from the
  established set (`AP:988-1017`): **hot → (300 s) → Cold**, not Warm. This is exactly PR 2344's stated motivation.

### Inferences
- No other hot protocol can on its own make hot→warm fail in this scenario; LeiosNotify is sufficient and, at these revisions, makes
  it fail on every outbound demotion of a peer with no Leios traffic. The time cost is ≥ 300 s per demotion (the
  churn loop waits `deactivateTimeout` for its decrease step too, `Churn:433-437`).
- ChainSync is a secondary risk only under long empty-slot streaks (> 300 s without a block), because its StMustReply
  timeout (601–911 s, or none for trustable peers) is longer than `deactivateTimeout`. The `Pol:27-28` comment assumes ≤ 269 s,
  which no longer holds at the pin (`CSCodec:53-60`).
- TxSubmission2 depends on the remote's inbound side sending a blocking request; the outbound side cannot force it.

### What PR 2344 changes (NOT in the local clones — no `MsgQuit`/`MsgCanceled` anywhere in consensus `27fa649ff`;
description taken from this repo's model headers, not from upstream code)
- From `Cardano_network/Parametric/Leios/LeiosNotifyPipelined.agda:8-14` and `LeiosNotifyP.agda:28-47` (the user's port of
  PR 2344 / cardano-blueprint PR 67 table): new `MsgQuit` (`StIdle → StQuit`) and `MsgCanceled` (`StBusy → StIdle`);
  "The consensus-side client is PIPELINED: it may send MsgQuit while requests are still outstanding, and from then on it
  IGNORES (does not deliver) the replies / MsgCanceled still owed for them, awaiting MsgDone. The network-side server READS AHEAD:
  when MsgQuit arrives while it still owes replies, it answers every outstanding request with MsgCanceled and then sends MsgDone."
- Inference: with this, LeiosNotify's exit no longer waits for Leios traffic. It needs about one round trip
  (MsgQuit → n×MsgCanceled → MsgDone), and the ingress queue is empty when it returns (every owed reply is consumed). So
  in the scenario above all hot protocols finish well within 300 s and the demotion ends **Warm**. What the pin gives
  without the PR: a CSP model should let `StBusy` of LeiosNotify block forever and treat the end of the deactivate wait as an
  external timeout event leading to `Mux.stop`/Cold.
- Not verified here: the exact upstream PR diff (whether it also changes `timeLimitsLeiosNotify`, the pipelining depth, or
  `CN2N:504-515` to issue MsgQuit on Terminate). Check the PR itself before citing those details.

---

## 6. Reusable pieces in `Network_CSP_Model`

- `Cardano_network/Parametric/Leios/LeiosNotifyQuit.agda`: real (ported) LeiosNotify peers with MsgQuit/MsgCanceled;
  `blk` (server application silent) and `blk-stall`/`blk-deadlock` (the NON-pipelined stall: once RequestNext is sent with
  a silent server, the client cannot quit). This is the pre-PR "LeiosNotify never returns" lemma in CSP form.
- `LeiosNotifyQuitCancel.agda` (bounded quit if the server cancels), `LeiosNotifyQuitLive.agda` (quit liveness under
  fairness, LTL `◇ᵗ (atom Ended)`), `LeiosNotifyQuitTerm.agda` (MsgDone is last; `quit-irrevocable`),
  `LeiosNotifyQuitFD.agda` (table conformance, FD), `LeiosNotifyPipelined.agda` / `LeiosNotifyPipelinedProps.agda`
  (depth-1 pipelined client with read-ahead quit — the PR 2344 behaviour; this is what makes the hot set finish).
- `LeiosNotifyQuitNet.agda` (the pair over the real breakable medium — what a `break` does) and `LeiosNotifyIsolation.agda`
  (a terminated LeiosNotify peer leaves the rest of the node bundle unchanged — reusable for "established protocols keep running").
- `Cardano_network/MediumEquivA` + `NetCommon` breakable media (`break` in `Net`): a ready model for `Mux.stop`/connection
  close (= Cold).
- `Cardano_network/Terminable/` (`NetT`, `NetworkT` `CopyT … □ mdone → SKIP`, `FourNodeDiamondTerminable`): per-instance
  termination (`mdone l d id`) of medium cells — the shape needed so a terminated hot instance frees its mux cell while
  others continue; `NetworkTRefinement` still has postulates (per CLAUDE.md).
- `GovernorWedge/`: `Timeout.agda` already models "a bounded await with a visible `tmo` event" (fix #1), the same pattern
  as `timeout spsDeactivateTimeout (awaitAllResults SingHot)`; `Model.agda`'s `Conn` (mux statuses, `Mux.stop`/`stopped`)
  and `Wedged.agda`'s "Blocked survives every step" are directly reusable lemmas/patterns. Its citation key matches this note's.

Not found / ambiguous:
- PR 2344 code (not in local consensus clone); typed-protocols commit `9b4627221a` (not in local clone).
- Whether the remote TxSubmission inbound (V2 logic) can keep the outbound side in `StIdle` indefinitely was not traced.
