# Lookahead replay cost experiments

`../replay_cost.py` measures an explicitly supplied compiled `LookaheadMain` on
synthetic normalized inputs. It does not build a checker, capture a node, or
modify any existing log. Local client, local server and paired checks use the
same generated endpoint projections. Profile: generic successful client
callbacks, unit return, `node-next` server, driver-log observation, prefix EOF.

## Workloads and expectation basis

| Family | Construction | Dimension |
| --- | --- | --- |
| `serial` | Issue one request, deliver its normal reply, collect, repeat; then Quit/Done | Increasing length at occupancy one |
| `pipeline` | Issue all requests before delivering normal replies; then Quit/Done | Increasing outstanding requests |
| `cancel-drain` | Issue all requests, deliver Quit, publish the server quit flag, cancel each owed reply, drain and exchange Done | Increasing pending shutdown work |
| `delayed-send` | Commit/decode a request and normal reply before emitting their Send hooks; finish both hooks and collect before repeating | Receive-before-delayed-Send order |

Every normal reply is `BlockOffer HASH 23 31`. Repeated payloads keep `HASH=43`;
distinct payloads use ascending hexadecimal hashes. Votes and other message
kinds are covered by the existing functional tests, not this cost dimension.
The paired format lists each endpoint's rows in its own order; it does not
assert the file's client-then-server block order as the physical schedule.
All families include Quit/Done wire rows. Acceptance still has the checker's
finite-prefix meaning rather than a whole-node cleanup claim.

The construction rationale is independent of the benchmark result:

- The [client source model](../../../../LeiosNotifyPipeLookahead/ClientModel.agda)
  can issue arbitrary finite batches with a sufficiently large dynamic callback
  depth; successful reply handling and collection allow the next cycle. Busy
  termination registers and drains the existing Quit marker before Await Done.
- The [server source model](../../../../LeiosNotifyPipeLookahead/Model.agda)
  admits/registers each request. Normal reply selection is allowed before Quit;
  after publication its cancellation branch discharges all outstanding jobs.
  Retirement and completion flushing precede Done.
- The [driver model](../../../../LeiosNotifyPipeLookahead/DriverModel.agda)
  separates packet commit/decode from delayed Send hooks. The existing
  [native delayed-Send regression](../../DriverDecideNativeTests.agda) supplies
  an independently checked single-cycle witness for exactly that race.

These are documented parameterized schedule constructions, **not new Agda
certificates for every generated fixture**. A completed rejection or invalid
input is recorded as an unexpected completed result requiring investigation of
the generator, profile and checker. It is not labeled an implementation bug.

## Reproduction and resource limits

From the repository root, with an existing binary:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/replay_cost.py --selftest
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/replay_cost.py \
  --binary /absolute/path/to/LookaheadMain \
  --out /tmp/new-lookahead-cost-run \
  --sizes 1,2,4,8,16,32,64 --payloads repeated
```

The output directory must be new and outside the repository. Inputs, captured
output, GNU-time statistics and incremental JSON reports are retained there.
The report hashes the binary, generator, reused CLI helper, relevant model
sources and fixtures. `--payloads both` compares repeated and distinct values;
`--modes` and `--families` select comma-separated subsets.

Every checker process runs serially with a default 512M RTS heap, five-second
wall limit, 3 GiB sampled group RSS limit and 64 KiB combined retained output.
The full run has a 120-second budget. Increase limits only explicitly. No Agda
or GHC compiler is started. Stop all other heavy jobs before benchmarking.

The Linux/GNU-time wrapper supplies per-child peak RSS and CPU times separately
from the harness's 5 ms sampled wrapper/descendant RSS. Short-lived peaks may be
missed by sampling; GNU-time wall values have coarse precision. Harness wall
time includes launching and measurement overhead. Host load and allocator noise
limit comparisons; measurements establish no universal complexity bound.

Only an exact first-line verdict tag with the matching exit code is a completed
decision. Timeout, heap/RSS/output failure, launch failure and untagged/mismatched
exit remain inconclusive. After one series becomes inconclusive, larger counts
in that same mode/family/payload series are explicitly `not-run`; no verdict or
cost is extrapolated for them. The same applies after the total budget expires.

The selftest checks fixture count/order/conservation, then launches nine tiny
Python subprocess controls for accepted/rejected/invalid tags, untagged and
mismatched exits, heap diagnostics, timeout, RSS and output limits. It launches
no compiled checker. This validates operational reporting, not protocol proofs.

## Measured findings, 5 November 2026

The [dated result record](result-cost-20261105.json) retains source/binary
identities, exact commands, per-case fixture hashes, statuses, timings and
resource limits. The existing wave-4 binary was reused, with `-O0` code from
the separately recorded build; no compiler or checker source was changed.
The following are single measurements on this machine, not stable limits:

| Workload | Observed result |
| --- | --- |
| Local client and server, all four families | All 56 cases accepted through 64 exchanges; each has 130 normalized rows |
| Paired delayed-Send, repeated payload | All seven sizes accepted; 64 exchanges/260 total rows took 0.064 s |
| Paired cancel drain | One and two pending requests accepted in 0.034 s and 1.645 s; four reached the five-second limit |
| Paired serial normal traffic followed by Quit/Done | One exchange reached the five-second limit |
| Paired batched normal traffic followed by Quit/Done | One exchange reached the five-second limit |
| Paired serial normal traffic, prefix before Quit | All seven sizes accepted; 64 exchanges/256 rows took 0.074 s |
| Paired outstanding-request-only prefix | All seven sizes accepted; 64 requests/128 total rows took 0.023 s |
| Paired delayed-Send, 64 distinct notification values | All seven sizes accepted; 64 exchanges/260 rows took 0.365 s |

The baseline prepared 84 cases: 65 accepted, three inconclusive timeouts and 16
explicitly unlaunched larger cases. Its run took 17.712 s. The bounded follow-up
prepared and accepted 21 cases in 0.846 s. No completed rejection or invalid
input occurred. The follow-up's exact Python probe source is embedded in the
record for reproduction; it uses the same generator/measurement API and takes
explicit prefixes, without modifying the original generated closed inputs.

The three timeouts had sampled wrapper/descendant peaks of 552472, 547572 and
544532 KiB respectively, below the 3 GiB sampled cap. There was no observed heap
exhaustion, RSS-limit failure or OOM. Killing the whole timeout group prevents
GNU time from writing its normal completion summary, so child peak/CPU metrics
for those cases remain unknown. Among completed baseline cases the greatest
GNU-time child peak was 255436 KiB. Follow-up child peaks stayed at or below
27196 KiB. These differing metric scopes are not interchangeable.

The closed-versus-prefix comparison demonstrates observed search sensitivity
for these fixtures, input orders and binary. It does not prove a universal
causal explanation or asymptotic bound. All paired searches use the checker's
existing successor/merge order; no randomization, warmup or repeated-trial
statistics were performed. A different finite enumeration order can have very
different cost. No checker optimization is implemented in this work.

For practical replay, run the inexpensive local checks before attempting paired
search with explicit budgets. Preserve the full original trace. A shorter
accepted prefix is diagnostic evidence about that prefix; it does not replace
an inconclusive result for the full trace or justify dropping Quit/Done.
Synthetic measurements do not qualify arbitrary real captures, production
throughput/latency, physical logger fidelity or deployed conformance.
