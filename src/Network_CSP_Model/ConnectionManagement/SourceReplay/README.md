# Socket-open reservation replay

Checked 16 October 2026 against network commit
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d` with GHC 9.6.7, Cabal 3.12.1.0
and the pinned project's resolved dependencies (including io-sim 1.8.0.1).

[SocketOpenFailure.patch](SocketOpenFailure.patch) adds two characterization tests
to the existing ConnectionManager IOSim harness. Only the test module changes;
CM implementation code is unchanged. This reproduces the **CM-level reservation
leak under an injected socket-open exception**. Full diffusion/OG supervision and
real operating-system socket exhaustion are not exercised.

| Injected failure | Map after first attempt | Second attempt | Open calls | Close calls |
| --- | --- | --- | --- | --- |
| `openToConnect` | Exactly the peer's unknown-local ReservedOutbound entry | ConnectionExists; no second open | 1 | 0 |
| `configureSocket` after successful open | Empty | IOException from a fresh configuration attempt; map empty again | 2 | 2 |

Both first attempts raise IOException. The tests inspect `readState` after both
attempts and compare the entire nested map, including the unknown-local key.
The injected exception is ResourceExhausted. The control confirms that the
post-acquisition bracket cleanup runs; it does not merely test the mock's error.
These passing tests deliberately characterize the leak; they are not assertions
that recovery is correct and would need updating if the implementation is fixed.

## Reproduce

In an isolated checkout of the pin, apply the patch using its absolute path:

```sh
git rev-parse HEAD
git apply --check /absolute/path/to/SocketOpenFailure.patch
git apply /absolute/path/to/SocketOpenFailure.patch
cabal build ouroboros-network:framework-sim-tests --offline -j2
cabal list-bin ouroboros-network:framework-sim-tests
```

Run the executable printed by `list-bin` with:

```sh
/path/to/framework-sim-tests -p '/socket-/' --quickcheck-tests 1
/path/to/framework-sim-tests -p '/Ouroboros.Network.ConnectionManager/' \
  --quickcheck-tests 100 --quickcheck-replay 42
```

The offline build requires dependencies already in the Cabal store. The initial
build found two test API mistakes (`modifyTVar'` versus strict `modifyTVar`, and
function-valued `Tracer` versus `nullTracer`); both were corrected. Cabal's log
write required access outside the workspace. The final build exited 0 without
new compiler warnings.

The focused run passed both cases. The broader filter reported all 12 selected
tests passing, with two pre-existing racy tests ignored. Its existing generated
transition/pruning tests reported zero observed transitions/connections and a
pruning coverage warning (0%, expected 35%). Do not treat that broader run as
strong concurrency/pruning coverage. The two new cases are deterministic;
repeating them 100 times does not add schedule coverage.

## Mapping and scope

The open-failure case corresponds to `CSP/OutboundOpenFailure.agda`: reserve,
allocate promise, fail open, return IOException, then reject a second acquire.
Core's reservation is outside the `bracketOnError` acquisition; the resource
release cannot run when acquisition itself throws. No socket or handler exists
for the reserved entry in this trace.

The replay calls the actual CM directly and catches errors in the test caller.
It does not run OG's job pool, rethrow policy, backoff or node supervision. The
pinned diffusion IO-error policy contributes `mempty` (ShutdownPeer), but this
source observation is not an integrated replay of deployment policy. Inbound
admission does not remove this unknown-local reservation: exact-key admission
and reservation-prioritizing outbound lookup preserve the obstruction. Node
shutdown/restart is outside this replay. No Haskell-to-Agda
refinement theorem, real-node reproducer or production fix is claimed.

## Integrated model continuation

[`CSP/GovernorOpenFailure.agda`](../CSP/GovernorOpenFailure.agda) extends the
model's first failed acquisition through OG completion, backoff, a fresh job and
second failure completion. The 64-action trace and its
[negative controls](../Negative/GovernorOpenFailure.agda) typecheck with Agda 2.8.0
and a 2 GB heap limit. They establish model reachability, not an IOSim replay of
the entire governor. The direct CM replay above is the source evidence for the
acquisition segment only.

## Verified OG / peer-state-actions / CM replay

[GovernorCMReplay.patch](GovernorCMReplay.patch) is the compiled and tested
version of the original draft. It applies independently to the same network pin
and leaves production code unchanged. Apply `SocketOpenFailure.patch` separately
to run its controls alongside it. `git apply --check` passed against the clean
pinned checkout. Do not apply the draft and verified patches together.

The new test uses actual `peerSelectionGovernor`, `withPeerStateActions` and CM,
with one ordinary peer supplied by a one-shot root fixture. It has no local roots,
protected extra peers, churn or peer sharing. Discovery, transport and socket
exhaustion are injected; handler/bearer sentinels fail if reached. No successful
handshake or mini-protocol is simulated.

All three fixed seeds (0, 1, 42) pass these assertions:

- Six failures: IOException followed by five ConnectionExists exceptions.
- Failure counts Just 1 through Just 5, then Nothing; only the sixth forgets.
- Consecutive completion delays lie within 2 seconds of 5, 10, 20, 40 and 80
  seconds, matching source jitter with no injected transport latency.
- The final observer callback sees no peer in the public-root set and no cold
  promotion in progress. This observes the actual decision state; it does not
  claim coverage of production public-state publication or all job-pool contents.
- CM still has exactly the unknown-local ReservedOutbound binding; open=1,
  connect=0 and close=0 before governor-scope shutdown.

The callback only records observations. It does not modify governor decisions.
The root provider blocks later discovery requests, so forgetting is assessed
without rediscovery. Protected-peer infinite retries, full diffusion supervision,
real OS exhaustion, recovery and universal liveness remain outside this test.

Validation on 16 October 2026 used GHC 9.6.7 and Cabal 3.12.1.0:

```sh
cabal build ouroboros-network:framework-sim-tests -j2
cabal list-bin ouroboros-network:framework-sim-tests
/path/to/framework-sim-tests -p '/GovernorCMReplay/||/socket-/' --quickcheck-tests 1
```

The build and all five focused cases exited 0. Initial draft compilation exposed
ambiguous names and unqualified record fields; these were fixed, and the final
build emitted no compiler warnings. Cabal needed permission to write its external
cache/logs. Logs in this session: `/tmp/cm-governor-replay-resume-build.log` and
`/tmp/cm-governor-replay-resume-tests.log`. The existing broader generated suite
was not rerun; its earlier coverage warning still applies. Three fixed seeds do
not constitute exhaustive scheduling or randomness coverage.

## Verified over-limit outbound-release replay

[OverLimitReleaseReplay.patch](OverLimitReleaseReplay.patch) is a standalone
characterization test against the same network pin. It applies to a clean checkout
without either socket-failure or governor patch. It adds a test module and test
registration only; production CM code is unchanged. The registration hunks may
need combining when installing multiple replay patches in one checkout.

The test reaches its precondition using public CM calls: acquire a fresh outbound
duplex connection to one peer, then admit an inbound duplex connection to another.
It checks the complete map before release: self is `OutboundDup Ticking`, the
other peer is `InboundIdle Duplex`. No CM entry or state variable is injected.
The same configured hard limit is passed to inbound admission.

| Case | Hard limit | Selected victim | Result after release and victim cleanup |
| --- | --- | --- | --- |
| Surviving self | 1 | Other peer | Self remains `OutboundDup Ticking`; other is removed |
| Self-pruning control | 1 | Self | Self is removed; other remains inbound-idle |
| Capacity control | 2 | None | Self changes to `InboundIdle Duplex`; other remains inbound-idle |

All three calls return `OperationSuccess (OutboundDupSt Ticking)`, describing the
pre-release abstract state. The test checks success separately from the resulting
map and asserts the exact pruning event: both candidates, one victim, one requested
prune. The capacity control asserts that there was no pruning event. It waits up
to 10 simulated seconds for victim cleanup rather than assuming cancellation
delivery joins the handler.

This reproduces the source mismatch in `Core.hs:1903–1939`: the over-limit branch
discards `pruneSelf` and never writes the prospective inbound-idle state for a
survivor. `mkPruneAction:732–777` writes only selected victims. The corrected
Agda `Negative/Outbound.over-limit-release-retains-surviving-self` fixture agrees
with this source observation. No production fix or global refinement is claimed.

The transport and successful duplex handshake are synthetic. The handler fills
its promise then waits interruptibly; production CM performs all allocation,
state transitions, cancellation and finalization. A deterministic test pruning
policy chooses the victim; this does not exercise the deployed diffusion policy,
a real mux, real sockets, or OG's response to release. Unlike the Agda branch
fixture, the CM precondition is established through its actual API.

Reproduce in a clean checkout of `96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d`:

```sh
git apply --check /absolute/path/to/OverLimitReleaseReplay.patch
git apply /absolute/path/to/OverLimitReleaseReplay.patch
cabal build ouroboros-network:framework-sim-tests -j2
cabal list-bin ouroboros-network:framework-sim-tests
/path/to/framework-sim-tests -p '/OverLimitReleaseReplay/' --quickcheck-tests 1
```

Validation used GHC 9.6.7 and Cabal 3.12.1.0. Build exited 0; the focused run
including all three release tests, three governor seeds and two socket controls
reported **all eight tests passing**. Initial compilation required qualifying
`CM.TrPruneConnections`; the final build had no compiler warnings. Initial Cabal
resolution warned that its package indexes were 34 days old; the source pin was
not changed. Logs: `/tmp/cm-release-replay-build.log` and
`/tmp/cm-release-replay-tests.log`. Standalone patch applicability was separately
checked against the clean pin. The test ran in the existing combined replay
checkout; no broad generated suite or Agda rebuild was needed for this test-only
addition. These deterministic cases establish finite source behavior, not
exhaustive schedules or deployment impact.

## IO catch-mask boundary probe (29 October 2026)

`CatchMaskProbe.hs` is a small **GHC IO semantics probe**, not a replay of the
pinned Network.Mux, an IOSim schedule or the combined subsystem. It verifies the
exception-boundary assumptions used by `MuxCatchUnwind`:

```sh
runghc ConnectionManagement/SourceReplay/CatchMaskProbe.hs
```

Run from the Network_CSP_Model library root with GHC 9.6.7 / base 4.18.3.0. It
passed with pool-close, catch:MaskedInterruptible, outer-finally in that order;
the replacement UserInterrupt escaped. The original ThreadKilled enters the
catch only after the bracket release. The handler then blocks on an empty MVar;
UserInterrupt is delivered there and escapes to outer finally without entering
the same catch again. There is a five-second observation timeout.

The locally cached io-classes 1.8.0.1 source's `MonadCatch IO` delegates to
`Control.Exception.catch`. This version fits the pin's network-mux `^>=1.8`
constraint; the earlier replay records io-sim 1.8.0.1. This probe exercises
only the IO boundary and does not establish a new resolved dependency lock.
Mux.hs:275–279 places the async catch outside the JobPool bracket;
ConnectionHandler.hs:378–380 and :450–452 explicitly unmask Mux.run. A catch
entered from unmasked IO runs masked interruptibly: asynchronous delivery needs
an interruptible operation, such as an actually blocked caller tracer or a
retrying full IG information queue. An ordinary nonblocking status write is not
such a delivery site. Enclosing uninterruptible masking would prevent delivery;
provider/mask implementations and custom tracer behavior remain contracts.

The Agda adapter checks the actual post-close phase/status and retains the
caught exception and abandoned callback. Queue-retry controls distinguish real
full-queue retry from a transaction with room. The probe establishes the small
IO boundary only; it neither runs the concrete tracer nor proves source/model
refinement, whole-system shutdown or a deployment deadlock.


## Handshake-result forcing contract probe

Checked 30 October 2026 at the unchanged network pin above, with GHC 9.6.7,
typed-protocols 1.2.1.0 and io-classes 1.8.0.1.
[HandshakeForcing.hs](HandshakeForcing.hs) exercises the actual driver Done branch,
HandshakeResult NFData, Mux.new and strict Handle construction. It is a contract
probe: no transport, wire negotiation, makeConnectionHandler, CM cleanup,
IOSim scheduling or deployment tracer is exercised.

From an isolated checkout with the framework test dependencies already built:

```sh
cabal exec --offline -- runghc /absolute/path/to/HandshakeForcing.hs
```

The checked run used /tmp/cm-pub1-replay-20261029 and a temporary Cabal config
via --config-file=/tmp/cm-review-20261029/cabal-writable.config. That config copies
the existing settings, replacing build-summary and logs-dir with writable /tmp
paths; the global configuration is unchanged. This avoids the historical
read-only summary failure. It does not turn that earlier build's exit 1 into a
successful build. cabal exec and the probe exited 0; no new baseline test suite
run is claimed.

Expected output:

```text
version data forced before return: caught BadVersionData
application forced before return: caught BadApplication
list spine forced before return: caught BadList
lazy protocol element survived driver return
lazy protocol element forced inside Mux.new: caught BadProtocol
real strict Handle construction returned
all forcing controls passed
```

Faults are injected into values, and tests check their identities. The Done
probe has send/receive sentinels; neither is used. The lazy protocol element
case also observes TraceNewMux before the allocation failure. The list spine
itself must be non-bottom because both TemperatureBundle and its temperature
wrappers have strict fields. No assertion is made that production applications
actually supply such malformed elements.

This evidence supports rejecting the previous positive strictHandle model case.
The four tracer cases still require concrete deployment contracts and outer
recovery composition. Handler-body and CM replay increments are recorded below.
The separate allocation fault has since been added at returnedSuccess; its
Agda acceptance is pending (Supervision.md increment 17).


## Production handler body replay for CM-PUB1

Checked 30 October 2026 at the same network pin and resolved dependencies.
[PublicationHandler.hs](PublicationHandler.hs) calls actual makeConnectionHandler
in initiator/responder mode, for both outbound and inbound roles. The remote side
runs the corresponding real handshake peer, with the production CBOR codecs and
queue bearers. Production source is unchanged. This is a handler-body replay;
CM's surrounding finally, socket/map cleanup, calling governor and Server are
not included.

Run from the isolated built checkout:

```sh
cabal exec --offline -- runghc -Wall /absolute/path/to/PublicationHandler.hs
```

The checked run uses the temporary writable Cabal config described above.
All ten cases pass, without final compiler warnings. Each role has these five
synchronous injected-fault cases:

| Failure location | Ordinary promise writes | Observed callback order |
| --- | --- | --- |
| TrHandshakeSuccess | None; reader retries | success |
| TraceNewMux | None; reader retries | success, newMux |
| Lazy protocol element inside Mux.new | None; reader retries | success, newMux |
| Application payload forced inside handshake (control) | One Left HandlerError | None |
| TraceStarting after publication (control) | One Right HandshakeConnectionResult | success, newMux, starting |

The writer wrapper delegates the real PromiseWriter STM operations and records
writes in the same transaction. All cases observe zero forcePromise calls and
the exact injected exception at the production classifier tracer. Assertions
require remote negotiation to succeed and the actual handler action to produce
an exceptional Async result before inspecting writes/promise. The retry check
uses the real reader with STM orElse; no writerless synthetic handler is used.
The harness bounds each case by ten seconds, scopes both Asyncs and joins their
results. Its rethrow policy is explicitly mempty (ShutdownPeer), with a null IG
tracer and no real operating-system socket. These are chosen inputs, not audited
deployed tracer/policy contracts.

Logs: /tmp/cm-review-20261029/publication-handler-both.log. Earlier outbound-only
versions passed, then exact fault checking and both roles were added; redundant
imports were removed before the final warning-free run. The saved repository
artifact is the both-role version.

These results reproduce empty promises at the real production-handler boundary
under the stated synchronous injections, and validate the lazy allocation fault
as a distinct location. They do not prove a caller remains blocked permanently,
CM cleanup/physical scope completion, full diffusion deadlock, deployed fault
reachability, async blocking-tracer delivery, or universal schedule coverage.
The next increment below adds the actual CM caller/finally and async tracer
receipt; outer recovery composition remains open.
The allocation case and an initialized inbound history are now drafted in Agda;
full acceptance checks are pending.


## Actual CM caller and cleanup replay for CM-PUB1

Checked 30 October 2026 at network pin
`96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d` using GHC 9.6.7/base 4.18.3.0 and
the resolved dependencies above. [PublicationCM.hs](PublicationCM.hs) runs the
actual CM and production makeConnectionHandler in **IO**, with encoded handshakes
over paired queue bearers. It calls acquireOutboundConnection or
includeInboundConnection from a fresh CM. Production source remains unchanged.

```sh
cabal exec --offline -- runghc -Wall /absolute/path/to/PublicationCM.hs
```

The checked command used the writable temporary Cabal configuration described
above. The original **14 cases** passed (seven per inbound/outbound role); their
results are below. The saved artifact now passes **18 cases**, adding the four
CM-owned shutdown cases in the following subsection. Final runghc -Wall exits 0
without warnings; log /tmp/cm-review-20261029/publication-CM-owned-final.log.
The earlier 14-case log remains publication-CM-IO.log.

| Injection, for each role | Writer result | Caller at observation | Cleanup before observation |
| --- | --- | --- | --- |
| TrHandshakeSuccess sync error | No write | Pending, blocked on STM | Handler finished, map empty, one close |
| TraceNewMux sync error | No write | Pending, blocked on STM | Same |
| Lazy protocol element during Mux.new | No write | Pending, blocked on STM | Same |
| TrHandshakeSuccess blocked tracer + AsyncCancelled | No write | Pending, blocked on STM | Same |
| TraceNewMux blocked tracer + AsyncCancelled | No write | Pending, blocked on STM | Same |
| Early application payload error (control) | One Left | Disconnected | Same |
| TraceStarting error after publication (control) | One Right | Connected or Disconnected | Same |

The table's close is the synthetic Snocket.close callback, not an operating-system
socket. The entire CM ConnMap must be empty, including remote and local keys.
The writer wrapper delegates the real writer operations and records ordinary
writes atomically; all cases require zero forcePromise calls. Sync cases must
reach the production classifier with the exact injected fault. Async cases
must bypass that classifier. The blocking tracers check MaskedInterruptible,
signal entry, and retry in STM; delivery occurs only after GHC reports the
handler blocked on STM. The sending thread is the external test harness, not
CM's shutdown snapshot/traversal.

The harness captures the actual handler ThreadId inside its MaskedAction.
A bounded readiness loop requires GHC threadStatus = ThreadFinished **before**
caller/map/writer observations; neither elapsed time nor close/map state is used
as the completion oracle. The pending caller must have ThreadBlocked BlockedOnSTM
and the expected completed counter callbacks on its own thread: two outbound,
one inbound. These counts distinguish the earlier outbound reservation callback
from the callback immediately preceding the actual promise read (Core.hs:1582–1584
and :895–897). In these fresh branches, zero promise writes prevent reaching any
later result-consumer action. The controls require caller completion. Late
publication races deliberately permit Connected or Disconnected; the final run
observed both across roles.

Each complete CM experiment has a ten-second bound. After observations, the
harness cancels/joins a pending caller and then leaves the real CM scope. The
remote handshake also has a scoped Async and must return success. No caller or
CM API is used after scope closure. The ordinary policy is explicitly mempty
(ShutdownPeer), IG tracer is null, transport is synthetic, and payload/tracer
faults are injected. This is a reproduction of **blocked acquisition after handler
cleanup under those inputs**, not evidence those inputs occur in deployment,
a permanently blocked job, exhaustive scheduling, full diffusion deadlock or
universal shutdown.

An earlier IOSim attempt passed both outbound sync tracer cases with an actual
EventThreadFinished before observation. Its pure lazy-allocation injection then
failed as a host evaluation error, outside the simulator's monadic exception
handling. That attempt exited 1; it is not a passing ten-case IOSim replay.
The saved replay uses actual IO to exercise ordinary Haskell payload faults
without changing production evaluation. Its earlier compile iterations repaired
name/API imports; the final run is warning-free. The scratch IOSim traceEvents
API returned tuples in resolved io-sim 1.8.0.1, converted to SimEvent for checking.

The five-case inbound/outbound and both CM wait endpoints now pass at 8 GB.
Next: model the raw Server admission-worker lifetime identified by the Server
replay below, then integrate broader caller/governor/Server recovery. The CM-owned
replay covers a single handler at each selected tracer; broader scope composition
remains open. Concrete deployment tracer/payload
contracts and broader safety/liveness gates remain open.


### CM-owned shutdown delivery (four additional cases)

The saved PublicationCM.hs also runs SuccessCMShutdown and NewMuxCMShutdown for
both inbound/outbound. These cases use **CM's actual finally** at Core.hs:527–548
to snapshot, read the entry, send AsyncCancelled and wait for its handler.
The harness sends no exception to that handler in these cases.

Before leaving the CM continuation, the test requires the exact singleton nested
map at the known local/remote key with UnnegotiatedSt for the right provenance,
a caller at its promise-read boundary, a handler actually blocked on STM in the
masked-interruptible tracer, zero writes/force calls and zero closes. It then
cancels/joins the **caller**, verifies that the exact live CM map and blocked
handler are unchanged, and returns from the continuation. This keeps all CM API
use inside its scope.

After Core.with returns, instrumentation must report no promise write, one
synthetic close, classifier bypass and GHC handler ThreadFinished. The lifecycle
markers must occur in this order:

```text
observed-open → caller-cancelled → cm-shutdown → socket-close → after-with
```

Only thread identities and instrumentation are observed after scope exit; no
CM API is called then. These cases show CM shutdown can cancel/join the blocked
handler under this profile. They do **not** leave a caller job running after
CM closure or prove how a production governor/server cancels its jobs. The
original 14 cases still observe the pending caller while CM remains open.
The two observation phases must not be merged into a claim of permanent blocking.
The final 18-case run also checks the original synchronous/async controls.

The first draft needed the actual ConnMap.LocalAddr constructor; after repair
and an extra exact-map check following caller cancellation, the repository
artifact passed all 18 cases with -Wall and no warnings. Source pin and dependency
versions are unchanged; the isolated network checkout remains clean.


## Actual Server admission-worker lifetime replay

[PublicationServer.hs](PublicationServer.hs) runs the actual Server.with,
InboundGovernor.with, CM and production handler, at the same network pin and
resolved versions. One synthetic listener accepts one queue-bearer connection;
the next accept blocks. The remote side runs the actual encoded handshake client.
Server's own accept loop forks the admission worker; the harness does not replace
it with a synthetic caller. The production IG tracer is attached normally.

```sh
cabal exec --offline -- runghc -Wall /absolute/path/to/PublicationServer.hs
```

The checked repository run used the writable temporary Cabal config, exited 0,
and emitted no warnings. Six cases passed; log
/tmp/cm-review-20261029/publication-Server-final.log.

| Injection | Admission status after Server.with returns | Connection/listener close callbacks |
| --- | --- | --- |
| TrHandshakeSuccess sync | Blocked on STM | 1 / 1 |
| TraceNewMux sync | Blocked on STM | 1 / 1 |
| Lazy allocation payload | Blocked on STM | 1 / 1 |
| TrHandshakeSuccess blocked tracer + async | Blocked on STM | 1 / 1 |
| TraceNewMux blocked tracer + async | Blocked on STM | 1 / 1 |
| Early handshake payload error (control) | Finished | 2 / 1 |

Before the server callback returns, the test requires successful remote
negotiation, GHC handler ThreadFinished, an empty entire CM map, zero force writes,
the expected ordinary writer calls, callback order and classifier fault identity.
The actual admission worker is identified through the CM counter tracer, excluding
the captured handler. Pending cases require one caller counter callback, placing
it at Core.hs:895–897's fresh promise read; no promise write occurred. Async
injections require an actually blocked MaskedInterruptible tracer and bypass the
sync classifier. The control writes Left, finishes the admission and observes the
handler cleanup close plus Server's Disconnected close; no OS descriptor reuse or
double-close safety conclusion is drawn from these synthetic counts.

After actual Server.with returns, the listener has closed but the five fault-case
admission workers are still blocked in STM. Instrumentation then explicitly
cancels each such worker and waits for ThreadFinished, so the test leaves no
orphan behind. No CM API is called outside its scope. A ten-second bound covers
each complete experiment. The source checkout remains unchanged.

**CM-PUB1 Server consequence:** pinned Server.hs:239–254 uses plain async for
includeInboundConnection and discards the Async handle. Its withAsync/race tree
owns the action, IG and accept loops, not those admission workers. The callback
API comment at :132–133 says all server threads stop when the callback returns;
the replay demonstrates an exception to that claim under the stated injected
fault contracts. This is a finite unjoined-admission-worker observation, not a
universal/permanent thread leak or deployment deadlock.

The instrumentation retains ThreadIds to inspect and clean up the workers;
those references may affect GHC garbage collection and deadlocked-STM detection.
It does not retain the original PromiseReader/Writer or test forced-GC recovery.
BlockedIndefinitelyOnSTM, external shutdown and process termination can change
later behavior. Concrete deployment tracer/payload contracts remain unverified.

The earlier 18-case CM replay explicitly owns/cancels its callers. Its four
CM-owned deliveries establish handler cleanup within that chosen caller scope;
they must not be cited as evidence Server cancels its raw admission workers.
Model Server admission as independent raw Async actors before deriving SI5;
remaining logical admission PCs alone do not certify physical thread lifetime.


Formal model continuation: ServerAdmission.agda and its properties/negative
endpoint now check. The initialized post-setup single-listener witness includes
two explicit handoffs (reusing the old two-admission fixture), actual IG/CM
cleanup and a separate physical/PC/empty-promise certificate for worker zero.
It refutes all-worker completion from owned scope return and includes an explicit
later cancellation/close/result suffix. This differs from the one-accept IO
fixture; no whole trace-refinement theorem equates them. New-writer invariants,
remaining admission/owned-scope failures and full outer composition are open.
See Supervision increment 18. No native replay was rerun for those Agda changes.
