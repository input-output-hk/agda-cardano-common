# LeiosNotify capture preparation audit

T8.1 preparation, 5 November 2026, at repository checkpoint `a25388c5`.
This is an evidence/completeness inventory, **not a replay acceptance or
rejection verdict**. Original captures, nearby scripts and node processes are
unchanged. The root agent maintains the shared project plan and topic pages.

The streaming [auditor](../capture_audit.py) and compact
[four-file report](captures-20261105.json) retain exact SHA-256 identities,
line/byte coordinates, message/field counts, target-agency role segments,
observed NewMux generations, bounded coordinate examples and literal reversed
endpoint candidates. Full per-segment coordinates can be reproduced with
`--full-sessions`; do not commit the large raw logs. The report records its
exact process argv, UTC audit time, final script hash and nearby-note hashes.

## Observed files

All four files are stable during the final audit and all 10,940,000 lines parse
as JSON records. The 4,100,745,768 input bytes are hashed without sorting,
deduplication or repair. The final process uses a 256 MiB address-space limit
and a 300-second CPU limit; observed Linux peak self RSS is 45,440 KiB.

| Capture basename | Lines | Notify rows | RequestNext | Votes | NewMux rows | Local role segments | Done observed |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `cardano-node-20261029.log` | 2680000 | 292073 | 0 | 0 | 2781 | 2221 | 82 |
| `miniprotocols-cardano-node.log` | 2675000 | 1965040 | 0 | 0 | 0 | 2932 | 429 |
| `miniprotocols.log` | 4215000 | 3242715 | 0 | 0 | 0 | 3334 | 761 |
| `cardano-node-20261014.log` | 1370000 | 49900 | 0 | 0 | 1761 | 1962 | 41 |

The first two are the user-supplied paths. The latter two are nearby alternatives
found during the audit; they do not resolve the missing-request evidence.
RequestNext counts include both `RequestNext` and `NotificationRequestNext`
namespace spellings. The literal `MsgLeiosNotificationRequestNext` is also absent
from every audited file, independent of the namespace classification.

| Capture | Quit | Canceled | Notify rows without thread metadata |
| --- | ---: | ---: | ---: |
| `cardano-node-20261029.log` | 82 | 81614 | 292073 |
| `miniprotocols-cardano-node.log` | 429 | 427348 | 1965040 |
| `miniprotocols.log` | 762 | 758881 | 3242715 |
| `cardano-node-20261014.log` | 0 | 0 | 49900 |

The October 29 file covers parsed `at` values
`2026-10-29T06:30:21.000627140Z` through
`2026-10-29T06:45:02.162766026Z`; the requested Grafana file covers
`2026-10-30T17:28:32.013598729Z` through
`2026-10-30T19:01:20.335672137Z`. These are observed timestamp ranges, not
certificates of capture coverage or causal order.

## Suitability for the selected replay target

**Confirmed finding:** none of the four files supplies evidence-complete fresh
sessions for the planned request-accounting lookahead profile. All contain
ordinary reply records but zero RequestNext records. The first two have 2219
and 2915 segments respectively whose first visible record is a reply; their
remaining 2 and 17 segments begin with an initial-command-shaped Quit but have
no observed preceding NewMux. Across all four files, no local segment combines
an initial-command-shaped first event with an observed NewMux boundary.

This does not identify a deployed protocol error. The upstream binary revision,
peer variant, exact tracer selection and lossless observation relation are not
established. Omitted/filtered requests, an older/different protocol build,
pre-existing sessions and export behavior remain possibilities. Do not invent
requests to make the captures fit the fresh-state target. A selected small
Quit/Done fragment might form an abstract trace under an explicit initial-state
assertion, but this inventory does not establish that assertion.

In driver-log mode a client may receive a reply before its pending RequestNext
Send record, including at a truncated EOF. A first-reply position alone is
therefore not rejection evidence. The conclusion here concerns missing capture
and initial-state provenance, not a FIFO-before-Send rule.

The retained metadata fields are present and pass the auditor's selected basic
checks for the observed kinds: BlockAnnouncement hash/slot/body-size; BlockOffer
hash/slot/bytes-size; BlockTxsOffer hash/slot; Quit/Canceled/Done kinds. There are
no Votes records from which to assess a vote-list capture. Presence of these
fields does not establish a complete native header/body representation or prove
the raw-to-native payload observation theorem.

Both requested files contain records from 29 hosts; literal reversed endpoint
pairs occur (134 and 142 candidates). This is useful inventory, **not proof of
paired protocol sessions**. Private/public IPv4 and IPv6 endpoint spellings,
connection reuse, node identity and observed generations must be resolved before
pairing. The auditor does not guess NAT/DNS mappings, match packets or merge
endpoint traces. Roles use the selected target's message agency; no Haskell
peer implementation is inferred from that role.

No recognized startup/build identity was found. Source revision and build
configuration remain **unknown**, including whether the binaries use the pinned
baseline, CollectOne, another branch or mixed versions. Filenames and dates are
not source provenance. Thread identifiers are absent on every Notify record;
per-thread order cannot be independently reconstructed from them. The file
order is retained, while sorted `at` values are not treated as causal proof.

Observed Done closes a local wire segment in this inventory. It does not prove
all prior requests were captured, physical return/cleanup, paired completion or
whole-node shutdown. EOF without Done remains a prefix, not successful closure.
Only NewMux and observed Done delimit this inventory; mux Dead is not treated
as a fresh-session boundary or used to discard late records.

## Nearby exporter risks, with attribution limits

The report hashes `get_log.sh`, `get_log_v1.sh`, and
`Exporting Loki logs from Grafana with a browser session.md` from the same
Grafana directory. They were read as text and **not executed**; credentials and
browser sessions are not accessed or copied into the report.

Two source-level findings require care:

- The notes' example Notify query lists only
  `BlockAnnouncement|BlockOffer|BlockTxsOffer|Done`. It omits RequestNext, Quit,
  Canceled and Votes. A capture made with that exact selector cannot supply the
  complete selected driver-log alphabet.
- Both nearby exporter scripts sort page output by timestamps and advance the
  next page to `last + 1` after a full 5000-row page. If a capped response omits
  other records with that final timestamp, advancing past it can skip those
  records. A lossless exporter needs an overlap/tie strategy with trustworthy
  event identity or an authoritative capture method; naive timestamp-only
  deduplication can also discard legitimate repeated messages.

**The use of these particular scripts/query for the audited files is unproven.**
In particular, the requested files contain Quit/Canceled, so they cannot simply
be attributed to the notes' narrow example selector. The source findings are
capture-method risks, not evidence that a specific omitted line was lost by one
of these scripts. No script credential/configuration changes are proposed here.

## Concrete next capture recipe

1. Use two controlled endpoints. Record actual binary hashes, node boot/session
   identifiers, peer entry points, source revisions (consensus, typed-protocols
   and network), build/container identity, tracer config hashes, callback
   contract, client depth and observation mode. Do not substitute the model pin
   for an unknown deployed revision.
2. Start authoritative capture **before** a new connection and mini-protocol
   run. Retain startup and connection/mux/protocol start/restart records, endpoint
   addresses and ports, node IDs, connection generations and any NAT mapping
   needed to identify the same bearer at both ends.
3. Enable and retain the complete `LeiosNotify.Remote` Send/Receive family,
   including RequestNext/NotificationRequestNext, Quit, all four notification
   variants, Canceled and Done. Use the actual build's tracer configuration;
   do a controlled one-request preflight and verify both RequestNext hooks are
   physically captured. If configuration or logging code suppresses them, fix
   that capture boundary before collecting a large run. Retain every field
   needed by the declared metadata/native observation profile, including vote
   order and duplicates if Votes is exercised.
4. Prefer original per-node structured output with thread IDs and trustworthy
   source order/sequence coordinates. Record logger drops/overflow and exporter
   selection, bounds and paging evidence. Preserve per-node order; do not use
   global timestamp sorting as a substitute for a causal merge. Driver-log mode
   must allow a peer's Receive to precede the sender's delayed Send record.
5. Exercise idle Quit, ordinary traffic, pending replies, selected normal across
   Quit, blocked next/cancellation and interrupted prefixes. Stop/rotate capture
   only after recording the desired terminal events or explicitly label EOF as
   a prefix. Retain physical driver outcomes when making completion claims;
   Done alone is insufficient for whole-node cleanup claims.
6. Save untouched originals and a checksum manifest for both endpoint captures
   and configuration/provenance. Once T7's certified observation/search is ready,
   normalize without fabrication and replay under explicit fresh-state/source/
   contract assumptions. Missing evidence must remain a capture diagnosis,
   separate from model rejection.

No node was started, no new capture was generated and no T8.2 replay verdict is
claimed by this work. T8.1.1 acquisition and T8.1.2 complete provenance remain
open until such a capture and manifest actually exist.

## Subsequent source diagnosis and preflight

The [next wave's source ledger and capture procedure](../capture-preflight/README.md)
identify four explicit Silence entries for Send/Receive RequestNext and Votes
in the inspected local Leios testnet config at
`614b10d21691e40ed3a3e5a3462b08497fcfe443`. This is a concrete configuration
finding and a plausible explanation, not established attribution to these old
captures. An unapplied fragment enables those entries for review against the
actual build; no deployed configuration has been changed.

A final hash-guarded strict preflight of the same October 29 raw file parses all
2,680,000 records, retains the same raw SHA-256 and confirms zero RequestNext and
Votes among 292,073 Notify rows. It exits 3 for missing capture evidence with a
null protocol verdict; source/helper identities and limits are in the
[preflight record](../capture-preflight/result-preflight-20261105.json).
The [raw correspondence workflow](../../README.md#raw-input-correspondence-and-capture-preflight)
now compares supplied normalized artifacts and byte/thread maps with original
JSON. Formal logger fidelity, fresh acquisition and deployment identity remain
separate from this executable check and the historical inventory above.

## Reproduction and validation

From the repository root, run `python3 -I -B` on `../capture_audit.py` with the
four absolute input paths and three `--source-note` arguments recorded in
`command_argv`, followed by `--out` for a new compact JSON report. The default
memory guard is 256 MiB. Add `--full-sessions` only when complete segment
coordinates are needed, directing that larger artifact outside the repository.

`python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/capture_audit.py --selftest`
passes checks for byte-exact hashing, original file coordinates, Done versus EOF,
split-after-Done behavior, timestamp decreases, thread preservation, missing
metadata and refusal to infer a source revision. These validate the auditor's
bookkeeping, not the protocol. The final four-file guarded scan exits zero;
there is no GHC/Agda build or proof claim in this audit.
