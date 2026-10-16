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
