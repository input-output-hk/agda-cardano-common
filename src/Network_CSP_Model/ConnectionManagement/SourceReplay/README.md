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
admission or node shutdown may change the later outcome. No Haskell-to-Agda
refinement theorem, real-node reproducer or production fix is claimed.

## Integrated model continuation

[`CSP/GovernorOpenFailure.agda`](../CSP/GovernorOpenFailure.agda) extends the
model's first failed acquisition through OG completion, backoff, a fresh job and
second failure completion. The 64-action trace and its
[negative controls](../Negative/GovernorOpenFailure.agda) typecheck with Agda 2.8.0
and a 2 GB heap limit. They establish model reachability, not an IOSim replay of
the entire governor. The direct CM replay above is the source evidence for the
acquisition segment only.
