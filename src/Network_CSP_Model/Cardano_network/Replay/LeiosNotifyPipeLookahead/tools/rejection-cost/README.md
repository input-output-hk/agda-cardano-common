# Rejection-heavy replay costs

This harness tests rejection robustness on synthetic normalized paired endpoint
inputs. It neither acquires raw logs nor modifies a protocol model. The ordered
baseline binary is
`/var/tmp/leiosnotify-wave6-cli-20261105/generated/LookaheadMain`, SHA-256
`609d2a99ab0f918f3f485b12dd0682e78f701adba9e585372b8fd3b0b6b3e7c6`.
The current checkout may already contain the later unique-basis import; that
checkout is **not** attributed to this older binary. Its prior build/source
record remains in the immutable `tools/search-order` evidence.

## Fixture obligations

All nine growing negative series keep the original Request counts and both
Quit/Done records. Message agency and normalized grammar are valid. Their
expected rejection uses these independent source facts, rather than a rule
that arbitrary row deletion/duplication is invalid:

| Series | Reason no fresh source witness exists |
| --- | --- |
| First client payload changed; repeated server payload | Exact client/server packet FIFO lists disagree at the first reply. |
| Last client payload changed; repeated server payload | The shared packet prefix ends in different retained hash values. |
| Last client payload changed; distinct server payloads | The same FIFO contradiction applies without collapsing distinct values. |
| Extra server reply; repeated values | There are `n` recorded server requests and `n+1` server reply Sends, contradicting server request/reply conservation. |
| Extra server reply; distinct values | The same count contradiction holds for independently retained payloads. |
| Extra client reply after logged Quit | At that FIFO position the server has recorded Done. A pending suffix Send cannot repair the earlier Reply/Done mismatch. Lead cannot occur after recorded Quit. |
| Server Done before its final owed reply | Done requires zero owed work; only `n-1` replies precede Done for `n` requests. The moved last reply is also impossible after closed. |
| Client Done before its Quit Send hook | Physical Quit commit alone leaves the client in `writingQuit`; its Receive-Done rule requires the state reached after the Quit Send record. |
| Second server Done | Recording the first Done closes the server, which cannot commit/send a second Done. |

The source references are `DriverConservation.to-client`,
`ServerConservation.initial-balance` / `no-extra-replies` / `closed-balance`,
and the actual `ClientModel.sentQuit*` / `receivedDone` and `Model.finish`
control rules. The Python generator is not a new kernel theorem. A separate
worker reviewed all nine rationales against the source and confirmed that
pending sender hooks do not repair these full-history contradictions.

Four valid controls include closed normal exchange and unfinished EOF on
either endpoint, plus both Receive records preceding both missing Send hooks.
Those missing Send records are **not** classified as invalid. Three short
logical negative controls and two explicitly invalid agency/grammar controls
run before the expensive series.

The default matrix has 72 fixture names: nine controls plus nine series at
sizes 1, 2, 4, 8, 16, 32 and 64. At size one the early/late and repeated/distinct
payload variants share bytes, and the two extra-server variants share bytes.
Thus nine size-one series measurements represent six distinct negative shapes,
not nine independent negative patterns.

## Reproduce and compare

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/rejection-cost/rejection_cost.py --selftest
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/rejection-cost/rejection_cost.py \
  --binary /var/tmp/leiosnotify-wave6-cli-20261105/generated/LookaheadMain \
  --expected-binary-sha256 609d2a99ab0f918f3f485b12dd0682e78f701adba9e585372b8fd3b0b6b3e7c6 \
  --out /tmp/new-rejection-baseline --timeout 2 --total-timeout 60
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/rejection-cost/rejection_cost.py \
  --binary /absolute/path/to/candidate/LookaheadMain \
  --reference /tmp/new-rejection-baseline/report.json \
  --out /tmp/new-rejection-candidate --timeout 2 --total-timeout 60
```

Both output directories must be new and outside the repository. The reference
mode requires exactly the same 72 fixture names and byte hashes. Each measured
case receives the full same two-second ceiling and 512M RTS heap, with sampled
3 GiB process-group RSS and bounded output. A total ceiling skips a case rather
than silently reducing its individual budget. A timeout/resource failure is
inconclusive and blocks larger sizes in that series. Every fixture is still
generated and hashed, including unrun cases.

The harness exits zero when measurement completes without an unexpected
completed status or changed executable/helper source; this does **not** mean
that every rejection was decided. Always inspect the separate counts for
`protocol-rejected`, `inconclusive` and `not-run`.

## Initial ordered baseline

[The frozen baseline record](baseline-20261105.json) retains exact identities
and per-case summaries. The run took 18.177561 seconds: all nine controls had
their expected completed statuses (four accepted, three rejected, two invalid).
All nine negative series timed out at size one under two seconds each. The
remaining 54 larger cases were not launched. Greatest sampled process-group
RSS was 516,168 KiB; no OOM verdict was inferred.

This exposes a practical negative-search limit despite inexpensive positive
workloads. It establishes neither growth with length nor a repeated-versus-
distinct payload effect, because those larger cases were not run and size-one
policy variants are identical. A future candidate result must retain the same
limits and inconclusive classification. No deployed conformance, complete
capture, general complexity bound or successful completion from EOF follows.

## Exact-byte unique-basis comparison

The candidate binary is
`/var/tmp/leiosnotify-wave7-cli-20261105/generated/LookaheadMain`, SHA-256
`7c3ab336c11ef53de9b2feb4905a50b67d99e98834b976fe58cf21be4c837401`.
All 72 generated fixture hashes match the ordered baseline reference. The
candidate was measured under the same two-second/512M case limits and
60-second total ceiling.

The completed statuses are unchanged: four accepted controls, three rejected
controls and two invalid controls. All nine size-one closed-negative series
still timed out, with 54 larger cases not run. No completed result contradicted
its independently reviewed expectation. Candidate runtime was 18.176674 seconds;
its greatest sampled process-group RSS was 539,516 KiB. Both runtimes contain
nine censored timeouts, so their similar totals are not a speedup measurement.

**Deduplicating callback candidate values does not resolve this measured
negative-search gap.** The record does not claim a growth curve, a policy
comparison at larger sizes, or a universal failure: the tiny short negative
controls did complete. The baseline and candidate external reports are
`/tmp/leiosnotify-rejection-baseline-20261105/report.json` and
`/tmp/leiosnotify-rejection-candidate-20261105/report.json`.
[The comparison record](result-rejection-cost-20261105.json) retains their exact
identities, all fixture hashes, logical rationales, budgets and per-case
statuses. Prior-wave source/tools/evidence remain unchanged.
