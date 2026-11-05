# Necessary-precheck regressions

This area measures the cheap local-language, exact common-prefix and pending-Send count guards
before the unchanged complete paired search. All fixtures are synthetic
normalized endpoint inputs. Prior-wave producers and evidence are read-only.
Passing the guards is **not** protocol acceptance.

## Guard and fallback controls

The driver defines 17 additional controls. Six are positive EOF/pending-hook
races. They include both Receive records before their Send hooks and a
second-round case with one pending sender in **each** direction:

```text
client: Recv A, Send RequestNext, Recv A
server: Recv RequestNext, Recv RequestNext, Send A
```

A real schedule completes/handles the first reply after its early Receive,
records Request1, then commits Request2. The server's independent reader can
record Request2 before its pending Send1. It can then finish Send1, commit
reply2, and allow its client Receive before Send2. A strict recorded
`receive-count <= send-count` rule would wrongly reject this prefix.

The original local/common-prefix-only counterexample is:

```text
client: []
server: Recv RequestNext, Recv RequestNext
```

Both local quotients accept; the command lists `[]` and `[Request, Request]`
are common-prefix compatible, and both response lists are empty. Yet a fresh
source run has only one pending client Send slot. With no recorded client
Sends, it cannot physically commit the two commands required by the two
server Receives. The original complete search therefore had to reject after those two guards
passed. A related control has one client Send and three server Receives. The
new count guard refutes both directly: recorded Receives may exceed recorded
Sends by at most one, independently per direction. It imposes no reverse cap
on queued Sends and does not require recorded lengths to be equal.

Other controls separate the guards: matching response packet histories with
no server Request violate the local server language; late exact payload and
inner-Votes mismatches after a shared first reply pass the local languages
but fail common-prefix packet compatibility. Full late-mismatch controls keep
all Quit and Done rows. Lead-to-Quit remains invalid until the pending Request
Send is recorded.

The guard suite also protects the explicit server callback contract. A normal
reply after recorded Quit is valid under `node-next` when selected before quit
flag publication; the selected reply survives later publication. Matching
Canceled-before-Quit inputs are accepted under `generic-next` and rejected
under `node-next`. Neither change is inferred from message kind alone.

Guard-pass annotations in the runtime report are source-review expectations,
not instrumentation of an internal branch. Root-owned kernel gates preserve the original base-guard pass/source-absence
distinction, then show the count guard refutes those excessive-receive cases. The harness neither changes these proofs nor infers guard
sufficiency from a completed checker result.

Even all three guards are not an acceptance certificate. The existing paired
CLI case `client=[Recv Canceled], server=[]` passes the local, common-prefix
and count predicates, yet the fresh server cannot physically produce a reply
before recording a Request Receive. The generic normal-reply version has
root-owned kernel gates for all-guard success and actual fallback rejection.
The public decision retains complete paired search whenever the guards pass.

## Historical prefix-only run

The first 274-case run used the binary SHA-256
`623b812da389604c268ed3872ba6a1c7195ed3e16a2a2e6f5cb9d82133825443`.
All 72 old rejection cases completed correctly, as did the 105-positive,
62-CLI and 18-exact suites. However, the extra one-client-Send/three-server-
Receives guard case still timed out at two seconds. The harness exited
nonzero and that result remains inconclusive, not a completed rejection.
The deliberate missing-file CLI case was separately expected inconclusive.

[The exact source snapshot](precheck_regressions_prefix_only.py), SHA-256
`b819229d8b61871c1a534c7b91f1a2a41e6b051f5db8112286edfd0e59dae356`, and
[the historical result](result-prefix-only-20261105.json) preserve this first
run without relaxing its expected status. The full external report SHA-256 is
`94254214c6d0ded75af0670aff22bcf65b08a31e9bff98b171dc05c938952d80`.
The subsequent count-aware comparison keeps all 274 fixture bytes, command templates/checker flags,
expected statuses and diagnostic assertions unchanged; only guard metadata
identifies which new necessary condition refutes the two count deficits.

## Complete regression scope

The default run contains 274 named cases:

| Suite | Cases | Source |
| --- | ---: | --- |
| guards | 17 | New exact pending-hook, common-prefix and fallback controls |
| rejection | 72 | Immutable `rejection-cost/rejection_cost.py` matrix |
| positive | 105 | Original 84 closed-family/mode/size cases plus 21 original follow-ups |
| cli | 62 | Immutable `test_lookahead_cli.py` flags, diagnostics and schema cases |
| exact | 18 | Immutable `basis-regressions/regressions.py` exact-value cases |

The 72 rejection and 105 positive fixture hashes are checked against their
prior committed inventories before any model process runs. The other suites
reuse the exact original fixture producers; their source hashes are retained.
Named cases can share input bytes and are not claimed as independent distinct
protocol patterns.

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/precheck/precheck_regressions.py --selftest
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/precheck/precheck_regressions.py \
  --binary /absolute/path/to/new/LookaheadMain --expected-sha256 ACTUAL_SHA256 \
  --out /tmp/new-precheck-regressions --timeout 2 --total-timeout 180
```

`--out` must be a new directory outside the repository. `--suites` selects a
comma-separated subset. Runs are serial, with a 512M RTS heap, sampled 3 GiB
process-group RSS ceiling and bounded output. Every measured case receives the
full same per-case ceiling; a global ceiling skips cases rather than reducing
that ceiling. Inconclusive results stop larger members of an applicable
rejection/positive series. The one deliberate missing-file CLI case is
expected to remain operationally inconclusive, never protocol rejection.

The runner also compares legacy `Replay/Main.agda` HEAD/before/after hashes;
it does not rebuild or change that file.

## Baseline probe

The existing unique-basis binary SHA-256 is
`7c3ab336c11ef53de9b2feb4905a50b67d99e98834b976fe58cf21be4c837401`.
The previous 72-fixture rejection reports remain the baseline; they are not
rerun here. The central two-server-Receives/no-client-Send fallback control was
probed once under two seconds/512M and completed as `protocol-rejected` in
0.014313 seconds. Its exact fixture SHA-256 is
`80601ffb5f14ad99b75edfcd3a00b0b9cfb4a5e47e409c47c7891aeb348dc6d6`.
The full probe report is
`/tmp/leiosnotify-precheck-baseline-probe-20261105/report.json`, SHA-256
`49f8ccb4b03c6761c5b010bfdbd6d02b14c2ce604772500a1e83612db05927d8`.
This is a counterexample to sufficiency of the original local/common-prefix
pair; the new count guard refutes it directly. It is not an example of a bad
capture or a claim that all incompatible pairs are cheap.

No raw JSON lexical theorem, authenticated endpoint pairing, deployed source
conformance, clean completion from EOF, or universal runtime bound follows
from these regressions.

## Final count-aware measurement

The final binary is
`/var/tmp/leiosnotify-wave8-count-cli-20261105/generated/LookaheadMain`, SHA-256
`d7bf4b88247a87a535d3e1639603c90c69b09a0a138a808c4fb8932de4726938`.
The full 274-case run matched every unchanged expected outcome under two
seconds/512M per case. All fixture hashes, command templates/checker flags, expectations and
asserted diagnostics match the historical prefix-only run. Actual binary and
fixture-artifact paths differ between runs.

| Suite | Actual final outcome |
| --- | --- |
| guards, 17 | 8 accepted prefixes; 9 protocol rejections |
| rejection, 72 | 4 accepted prefixes; 66 protocol rejections; 2 invalid inputs |
| positive, 105 | 105 accepted prefixes |
| CLI, 62 | 23 accepted; 11 rejected; 27 invalid; 1 deliberately missing file remains inconclusive |
| exact, 18 | 14 accepted prefixes; 4 protocol rejections |

The complete run took 4.848712 seconds; greatest sampled process-group RSS was
24,972 KiB. The historical three-Receives/one-Send timeout became a completed
rejection in 0.013002 seconds, without changing its input or expected status.
The 72-case rejection suite now runs through size 64 with no series blocked;
its slowest case took 0.024689 seconds. These are bounded sampled measurements,
not a universal cost theorem. There were no unexpected timeouts or completed
statuses; the deliberate missing-file case is kept separate.

The exact prefix-only source snapshot and nonzero first-run result remain
unchanged. The live script changes only count-guard metadata/rationales; it
retains all 274 input bytes, command templates/checker flags, expectations
and diagnostic assertions; actual binary and artifact paths differ. Its final source SHA-256 is
`c14e4d4e07d404b9ffc5ab0bd550178cc17b735789eede62418266881c9980fc`.
Legacy `Replay/Main.agda`, helper sources and each measured binary retained
their before/after hashes.

[The final record](result-precheck-20261105.json) includes exact commands,
source/fixture identities, the historical failure and final outcomes. Full
external reports are retained separately so a transient artifact can never be
mistaken for a kernel proof or a real-log capture certificate.
