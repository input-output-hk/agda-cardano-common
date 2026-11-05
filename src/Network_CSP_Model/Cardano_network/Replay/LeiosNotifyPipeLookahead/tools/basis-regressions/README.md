# Exact-value basis regressions

[DriverUniqueTests.agda](../../DriverUniqueTests.agda) checks that removing
duplicate **whole candidate Notification values** preserves the original driver
language. It does not remove visible rows or alter a Notification's internal
`Votes` list.

The kernel tests construct two real exchanges for any exact notification and
either server contract. With a representative equal to the repeated notification,
the occurrence basis has five entries and the unique basis has one. The actual
source run still contains all eight visible records. Both an ordered Votes list
with an internal repeated vote and the empty Votes representative are covered.
Unique-basis/source/native transports retain the exact input; tiny computed
decisions cover representative collisions and unfinished EOF. The native scope
is the fixed summary-parameter packet model, with unit return and the declared
successful callback contract.

The two negative payload families have independent universal packet-conservation
refutations for all three endpoint merges: removing an internal duplicate vote
and reordering the same vote multiset cannot match the sole recorded server
packet. Expected failure is established by these model proofs, not by observing
the checker's result. Pending Send hooks do not repair a different first packet.

`regressions.py` contains 18 small compiled-checker fixtures, exercising both
contracts, two exchanges with repeated values, representative collisions,
delayed Send records, exact repeated Votes, EOF prefixes, and the two negative
payload families. It reuses the unchanged
[CLI test helper](../test_lookahead_cli.py) for input syntax, execution and verdict
classification. It records the binary and helper hashes before and after, and
stops after the first inconclusive case. A timeout, heap failure or untagged exit
is inconclusive, including an untagged exit code 1.

```sh
python3 -I -B regressions.py --selftest
python3 -I -B regressions.py \
  --binary /path/to/LookaheadMain \
  --expect-sha256 BINARY_SHA256 \
  --out /tmp/new-basis-regressions \
  --timeout 2
```

The output directory must be new and outside the repository. Actual checker
processes run serially with a 512M RTS heap. The same harness and fixture bytes
can compare the immutable old executable with a freshly built unique-basis
candidate. Timing and acceptance are finite runtime evidence; the generic
membership/run preservation theorem supplies the language argument. This is not
a raw-capture certificate, a throughput claim, or implementation refinement.

The [recorded kernel and runtime checks](results-unique-regressions-20261105.json)
include all 18 identical fixtures against both immutable executables. Each
completed with the independently expected result; no timing improvement is
claimed from these tiny correctness regressions.
