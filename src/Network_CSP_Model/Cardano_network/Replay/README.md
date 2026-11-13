# Trace replay

Start with the [replay usage guide](USAGE.md) for builds, raw-log preparation,
session lifecycles, pairing and verdicts. Both executables also provide
`--help` and `-h` with commands and examples.

Two executables check normalized mini-protocol logs against first-order
session specifications with protocol-specific PTree bridges. Fetch's local
bridges retain decoded request bitmaps and counts, with explicit receive-side
limits; the spec client send rule supplies canonicity, so client completeness
and equivalence need no separate sender premise, as detailed below:

| Executable | Protocols and models | Guide |
| --- | --- | --- |
| [`Main.agda`](Main.agda) | LeiosFetch, LeiosNotifyP (alternating and bounded pipelined peers), BlockFetch, ChainSync and TxSubmission2; local, interleaved and paired modes | This README |
| [`LeiosNotifyPipeLookahead/LookaheadMain.agda`](LeiosNotifyPipeLookahead/LookaheadMain.agda) | LeiosNotify against the pinned lookahead implementation model (pipelined client, lookahead server), including logs that silence RequestNext and Votes | [Lookahead README](LeiosNotifyPipeLookahead/README.md) |

Both accept prefixes, including unfinished sessions at EOF. An accepted prefix
is not evidence of delivery or successful completion.

Raw-log adapters, pair-manifest normalization and CLI regression scripts live
in [LogProcessing](LogProcessing/README.md), directly under this replay folder.

For devnet captures without `NewMux`, `normalize_logs.py --connection-lifecycle`
uses explicit successful handshakes and matching handler cleanups to separate
connection generations. It preserves source coordinates, writes a lifecycle
audit and rejects ambiguous generation evidence. The default mux-based mode
is unchanged. See [LogProcessing](LogProcessing/README.md#devnet-captures-without-newmux)
for the capture requirements and command.

Paired ChainSync, LeiosNotifyP, LeiosFetchP, BlockFetch and TxSubmission2 replay checks communication consistency between explicitly
paired opposite endpoints. The [implementation note](../../../docs/notes/paired-chainsync-replay.md)
documents its input grammar, certificates, tracer boundary and limitations;
the [plan](../../../docs/specs/paired-trace-replay-plan.md) tracks remaining work.

## Current-schema LeiosFetch replay (2026-11-11)

The replay schema and constants target `ouroboros-consensus` `leios-prototype`
at **`e6511527`** (`e651152750388ccf20700eb28149751981a396f4`).
`BlockTxs` is a positional reply carrying only transaction count and byte size;
it has no reply hash, slot or bitmap. See the [grammar and diagnostics](USAGE.md#leiosfetch-grammar-and-diagnostics).
Fetch's default client depth is **150** in local, interleaved and paired modes;
an explicit bound overrides it. Its server remains sequential.

Acceptance has two layers in [the session spec](LeiosFetchSession.agda):

- `wire`: bitmap decoding, protocol state, depth, FIFO reply kinds and client
  receive byte/count caps.
  [Wire constants](LeiosFetchWire.agda) are `maxTxs = 17142`,
  `maxBitmapEntries = 268`, `txsCap = 550000`, `ebCap = 660000`.
- `client`: request count versus bitmap popcount, client-send offsets < `maxTxs`,
  and checked replies' count/hash matches. Both roles require the logged request count to equal bitmap popcount.
  On a server-role session, count and hash failures are labelled `client:` because
  they are checks the receiving client makes.

The client can silently stop and drain outstanding replies by kind without
count/hash matching; wire checks remain active and new requests are forbidden.
The server can silently throw while holding a request. Prefix acceptance therefore
does not assert that all replies passed application checks, or that an unanswered
request was actually served or thrown. Paired acceptance additionally matches all
retained message fields across the two directional FIFOs.

### Stage 2 positional model and replay follow-ups

The protocol model now uses `MsgLFPBlockTxs : List Tx → MessageLeiosFetchP`.
The client retains its requested point and offsets, accepts a checked reply only
when `length txs ≡ length bm`, then delivers `(q , zip bm txs)` to the application.
Since stage 3A, `LeiosFetchP` receives a count mismatch and then becomes `Stop`
(no further event or τ step of that peer), representing upstream's client error
at peer scope; whole-connection teardown is abstracted. The server sends
`map proj₂ es`; the application reply carrier remains
`(EBHash × LSlot) × List (ℕ × Tx)`. `LeiosFetchPipe` checks FIFO kind and count,
while its existing stop-and-drain path consumes replies by kind with any count.
The first-order replay still applies wire decoder caps while draining.

The stage-3A stop replaces stage 2's receive refusal. Stage 3B+C now implements
negative store reads and server throws, reply-wide validation before deposits,
all-offset chunked requests, and client stops on oversized or mismatched EBs and
failed reply checks. A client-thread stop also silences that link's shared Notify
client. See the [Leios behavior and scope](../Parametric/Leios/README.md#stage-3bc-behavior).
Application carriers, peer states, `LeiosFetchPipe`, the replay spec, node-level
safety and no-livelock statements are unchanged. The
[stage-3B+C outcome](../../../docs/specs/2026-11-11-leiosfetch-upstream-alignment-design.md#stage-3bc-outcome)
records the helper changes, accepted rulings and measured checks.

Only a **client Send** of BlockTxsRequest requires `T (canonical (offsets b))`:
every decoded offset is below `maxTxs` (`17142`). The diagnostic is
`client: request offset exceeds maxTxs`. The count bound follows from canonical
offsets and the logged count matching popcount.
An honest client's requested offsets come from an EB of at most `maxTxs`
transactions. Valid bitmap decoding alone permits 268 words with popcount
17150 and padding offsets through 17151, so it does not imply this bound. **Server Recv remains uncapped**:
upstream [`msgLeiosBlockTxsRequest`](https://github.com/IntersectMBO/ouroboros-consensus/blob/e651152750388ccf20700eb28149751981a396f4/ouroboros-consensus/src/ouroboros-consensus/LeiosDemoLogic.hs#L281-L308)
serves every requested offset or throws, with no request-count guard.
Both roles still check the logged count against bitmap popcount; replies still
have the wire count cap only on client receives, including draining.
Under D11, server sends have no byte or count cap: a requested Block of
700000 bytes or a requested 17143-transaction reply above `txsCap` is accepted
on the server side. The requested hash or count must still match.
These same received values are rejected on the client side with `wire:` reasons.

Local and interleaved drain-only acceptances retain their existing first line
(`accepted (<n> events)` locally; `accepted (<n> events, <m> sessions)` in
interleaved mode), followed by `note: checked reading fails …` on line 2.
Interleaved notes identify the session and its local event index; independent
session queues stay separate. Paired Fetch retains its existing
`accepted paired prefix (…)` first line and witness. Paired mode prints no drain note
because no legal pair needs a client drain: the session spec's `sSendBlock`
preserves the requested hash and `sSendTxs` preserves the requested count, while
paired FIFO matching delivers exactly what the server sent. Thus a pair with
legal server behaviour and matching FIFOs cannot fail those client reply checks;
paired mode needs no silent client stop for such pairs. The paired-drain
regression still rejects because the client receives Block `b` while the server
sent Block `a`, violating FIFO matching. The checker and its witness are unchanged.

### Stage 3B+C server throw and Stage 3D counted bridges

A negative body read stops the serving thread and leaves the inventory unchanged.
[`unknownEBThrows`](LeiosFetchBridgeSanity.agda) remains an actual model-run
witness. The generic node logic also stops on missing offsets or transactions.
The replay instance now has a decoder-sized table and holds its unit transaction,
so its valid nonempty requests proceed to transaction reads rather than missing
an offset in the former empty table. An accepted unanswered prefix does not
establish that a concrete implementation threw or tore down its connection.

### Stage 3F bridge and local-run statements

Stage 1 returned an accepted representative existentially and related whole
classes of logs under an observation that erased counts. Stage 3D replaces those
shapes with **counted, conditional soundness** and direct log equivalences.
Stage 3F additionally retains decoded request offsets. Canonicity follows from
the spec client send rule; client completeness and equivalence need no separate
honest-sender or canonical-request premise.
Each restated endpoint below shows its old signature (the stage-1 statements at
`cd63f3c7`) → its new signature (current source).

[`server-sound`](LeiosFetchServerSound.agda):

```agda
-- Old
server-sound : ∀ bs {t M} → serverModel bs ⟹∖√⟨ t ⟩ M
             → ∃[ es ] (ObsS t es × HasTrace server₀ es)
-- → New
server-sound : ∀ bs {t M es} → serverModel bs ⟹∖√⟨ t ⟩ M
             → ObsS t es → WireOK es → HasTrace server₀ es
```

[`client-sound`](LeiosFetchClientBridge.agda):

```agda
-- Old
client-sound : ∀ {t M} → pipe k l d ⟹∖√⟨ t ⟩ M
             → ∃[ es ] (ObsC t es × HasTrace client₀ es)
-- → New
client-sound : ∀ {t M es} → pipe k l d ⟹∖√⟨ t ⟩ M
             → ObsC t es → WireOK es → HasTrace client₀ es
```

[`server-bridge`](LeiosFetchServerComplete.agda):

```agda
-- Old
server-bridge : ∀ {es} → (∃[ es′ ] (es′ ≈♭ es × HasTrace server₀ es′))
              ⇔ (∃[ bs ] ∃[ t ] ∃[ M ] (serverModel bs ⟹∖√⟨ t ⟩ M × ObsS t es))
-- → New
server-bridge : ∀ {es} → HasTrace server₀ es
              ⇔ (WireOK es × ∃[ bs ] ∃[ t ] ∃[ M ]
                  (serverModel bs ⟹∖√⟨ t ⟩ M × ObsS t es))
```

[`client-bridge`](LeiosFetchClientBridge.agda):

```agda
-- Old
client-bridge : ∀ {es} → (∃[ es′ ] (es′ ≈♭ es × HasTrace client₀ es′))
              ⇔ (∃[ t ] ∃[ M ] (pipe k l d ⟹∖√⟨ t ⟩ M × ObsC t es))
-- → New
client-bridge : ∀ {es} → HasTrace client₀ es
              ⇔ (WireOK es × ∃[ t ] ∃[ M ]
                  (pipe k l d ⟹∖√⟨ t ⟩ M × ObsC t es))
```

Fixed-store completeness retains its explicit request premise:

```agda
server-complete : ∀ bs {es} → All (ReqHeld bs) es → HasTrace server₀ es
                → ∃[ t ] ∃[ M ] (serverModel bs ⟹∖√⟨ t ⟩ M × ObsS t es)
```

[Observation](LeiosFetchObs.agda) retains request hashes/slots, Block hashes,
and both transaction counts (`length bm` / `length txs` in the model). It drops
model receives that fail decoding, matching decoder-before-logging upstream.
Stage 3F additionally retains exact decoded request offsets. The relation is
`Decodes b bm = T (validᵇ b) × offsets b ≡ bm`, together with
`n ≡ length bm`. This is what upstream `decodeBitmaps` computes, not a separate
bitmap premise. `Msg♭` records the decoded offsets and validity Boolean, so
request observation equality supplies `Decodes` (see `request-match`).
It still forgets byte sizes. [WireOK](LeiosFetchWireOK.agda)
requires each received Block's size ≤ 660000, each received BlockTxs count
≤ 17142 and size ≤ 550000. Requests and server sends have no `WireOK` premise.
Exact bitmap observations alone therefore do not establish receive-side limits.
The regression server log with a 660001-byte Block is accepted under D11;
a client receive of that size fails WireOK. Current logged byte sizes omit
parts of the encoded framing, so passing these one-sided receive checks does
not establish that the whole encoded message met its decoder limit. In particular,
`ebBytesSize` includes the inner EB framing, while `txsBytesSize` sums inner
transaction bytes; full message framing and individual transaction lengths are
not recorded. `WireOK` is a check on these logged summaries, not an exact wire
size certificate, and cannot establish decoder compliance from current logs.

D8′ distinguishes server decoding from honest client sends. Server requests use
`decodable`: strictly ascending offsets below `64 * 268 = 17152`. Honest sends
and the pipe use `canonical`: strictly ascending offsets below `17142`.
[`LeiosFetchWords`](LeiosFetchWords.agda) proves canonical implies decodable and
encoding validity/popcount preservation for all decodable lists. The valid
17150-count server request now has a counted model-run witness; honest clients
still cannot send that count. Client receives, including drained replies, keep the wire
count cap. Drain mode intentionally skips handler count matching.

`ReplayParams` uses option (a), extended to all 17152 decoder offsets: each EB
table entry is `(tt , tt)`. The [replay server model](LeiosFetchServerModel.agda)
extends the original body store menu with a read of the held unit transaction.
This is necessary for nonzero counted replies: the previous body-only store had
no transaction-read partner. `ReqHeld` pairs held request hashes with bounds for
every requested table offset; every corresponding transaction is held by this
store. The total server bridge chooses the requested body inventory and derives
the offset premise from wire validity. Soundness still covers every initial
body inventory. This artificial serving table includes decoder padding; it is
not an honest-body-size witness. The generic honest-node canonicity lemma still
requires `length (ebTxs h) ≤ maxTxs`, including locally forged bodies.

[Client completeness](LeiosFetchClientBridge.agda) realizes every accepted
client trace, at every bound, link and direction. The client send rule supplies
canonical decoded offsets below 17142. Completeness chooses `offsets b` from
the actual logged bitmap, replacing the earlier count-only witness `upTo n`:

```agda
client-complete : HasTrace client₀ es
                → ∃[ t ] ∃[ M ] (run t M × ObsC t es)
```

No separate `Honest` premise is needed for completeness or equivalence.
A one-bit padding request at offset 17151 is rejected on client send with
`client: request offset exceeds maxTxs`; server receive still accepts it.
Soundness consumes observation and receive-side `WireOK`.
This bridge certifies the spec-written `LeiosFetchPipe`, not the existing
`LFPclientStClient`. Byte sizes remain abstracted; these results do not supply an
exact-field composed Fetch bridge or establish deployed implementation refinement.

The composed [store-backed server endpoint](LeiosFetchPairedStoreTrace.agda),
`LeiosFetchPairedStoreTrace.server-legal`, changes as follows (old → new):

```agda
-- Old
server-legal : ∀ (k : ℕ) (l : Link) (d : Dir) (bs : Bodies)
  {events : List Pair.Event} {end : PTree PairEv PairI ⊤} →
  system k l d bs PairTrace.⟹∖√⟨ events ⟩ end →
  ∃[ es ] (ObsS (projectServer events) es ×
    Replay.Traces.HasTrace (F.Spec.leiosFetch k) F.server₀ es)
-- → New
server-legal : ∀ (k : ℕ) (l : Link) (d : Dir) (bs : Bodies)
  {events : List Pair.Event} {end : PTree PairEv PairI ⊤} {es} →
  system k l d bs PairTrace.⟹∖√⟨ events ⟩ end →
  ObsS (projectServer events) es → WireOK es →
  Replay.Traces.HasTrace (F.Spec.leiosFetch k) F.server₀ es
```

The inhabited `request-server-legal` gate applies it to a specific admissible
log; the wrong-hash negative control remains impossible.

[Paired local normalization](LeiosFetchPairedLocal.agda) now preserves the visible
list with an existential endpoint and retains silent stopping explicitly:

```agda
data Run (r : Role) : St → List E → St → Set where
  finish : ∀ {s} → Run r s [] s
  stopped : ∀ {q es t} → Run r (cDrain q) es t → Run r (cOpen q) es t
  visible : ∀ {s e t es u} → next r s e ≡ just t → Run r t es u → Run r s (e ∷ es) u

lower : ∀ {r s es t} → Local._⇒⟨_⟩_ s es t → ∃ (Run r (normal s) es)
```

A terminal throw cannot preserve the normalized endpoint: `normal (sBusy r)`
is ready, whereas the original run may end at `sThrown`. The `stopped` case
retains `cStop` and `lift` restores it. The old `tau-normal` equality lemma was
removed because stopping and throwing do not normalize to equality. The
`wire-language` equivalence keeps its statement with this extended `Run`;
paired deterministic `next` still chooses service and a prefix does not witness
an actual throw.

### Stage 1 devnet results

On 2026-11-11, normalization and replay of
`/home/rye/YE_Workspace_Research/Workspace_IOG/git_repos/leios-local/ouroboros-leios/demo/proto-devnet/tmp-devnet/node{1,2,3}/node.log`
(captured 2026-11-10; logged `gitRevision 7b8ca5a178ee47a6f34be88de299ce936588bf9d`)
accepted **11/11 sessions, 88 endpoint events**, at default depth 150. Node1,
node2 and node3 contributed 5/38, 4/30 and 2/20 sessions/events respectively.
All **4/4 matched pairs** accepted (`accepted paired prefix`), covering 76 endpoint
events (38 messages observed at both endpoints). Three earlier sessions, totaling
12 events, have no opposite endpoint in the supplied node3 log, which starts after
node3's restart; they were checked locally only. No session or pair was rejected.
All 11 sessions are depth-1 request/reply alternation; none contains Done,
pipelining beyond depth 1, draining or a throw, so the run does not exercise
those branches.
The run recorded output and manifests under `/tmp/leiosfetch-devnet-stage1/`.
These are finite-prefix results, not delivery, validity or implementation-wide
conformance proofs.

## Lookahead Notify replay

[LeiosNotifyPipeLookahead](LeiosNotifyPipeLookahead/README.md) models the pinned
consensus implementation (`2416493b`): the client registers a receiver job before
each RequestNext, and the server's reader can receive Quit while its sender has
a reply in flight. Local wire languages are proved equivalent to the source model
and the native PTree; a paired decision covers both endpoints through the driver
model, with five proved necessary prechecks before a complete search. Separate
profiles check the node's fixed-depth client policy and the full node policy.
The [CLI and manifest runner](LeiosNotifyPipeLookahead/README.md#normalized-input-and-cli-delivery)
report `accepted-prefix`, `protocol-rejected`, `invalid-input` and, for silenced
pairs only, `undetermined` (exit 3). Raw-log fidelity, logger correspondence and
Haskell refinement stay outside the proofs.

The [silenced observation](LeiosNotifyPipeLookahead/README.md#silenced-observation-replay)
`driver-log-no-request-votes` is for logs whose configuration silences RequestNext
and Votes (Leios testnet config `614b10d2`). Its local verdicts are exact for the
erased languages. A paired `undetermined` means only that the canonical
reconstruction failed; it is not a refutation. Under it, the
[October 29 capture](../../../docs/notes/leiosnotify-silenced-capture-replay.md)
is accepted as a prefix in every local session and literal pair. That is weak
conformance evidence: silenced acceptance constrains only the Quit/Canceled/Done
order and, in pairs, FIFO consistency of the visible replies. It is not
full-observation acceptance.

The [bounded-language relation](LeiosNotifyPipeLookahead/README.md#bounded-and-lookahead-wire-languages)
shows that the bounded `LeiosNotifyPipeline` server language is included in the
lookahead server language under `genericNext` only, that the bounded client
language is included in the lookahead client language, and that every converse
fails.

## Paired BlockFetch and TxSubmission2

```sh
Main --paired-blockfetch PAIR.txt [K_BF]
Main --paired-txsubmission2 PAIR.txt [K_TS]
python3 -I src/Cardano_network/Replay/LogProcessing/paired_sessions.py manifest.json PAIR.txt
```

**Both are certified first-order paired checkers.** BlockFetch bounds the client
pipeline (default **100**) and preserves sequential server batch processing.
TxSubmission2 bounds the server/requester pipeline (default **4**); its
client/submitter remains sequential. The shared fresh-session manifest uses
protocol `BlockFetch` or `TxSubmission2`. Existing canonical and exact tracer
namespace grammars are accepted; TxSubmission2 uses `TxSubmission.Remote.*`,
including `MsgInit`, and requires explicit blocking/ID-reply-emptiness tags.

The checker searches all order-preserving merges of the endpoint inputs. Two
initially empty, unbounded directional FIFOs match message observations.
BlockFetch compares message kinds only; TxSubmission2 also compares blocking
style and ID-reply emptiness. Payloads, hashes, ranges, transaction IDs and
contents are not compared. EOF accepts unfinished prefixes and can leave
messages in flight. Zero capacity permits BlockFetch idle ClientDone and
TxSubmission2 blocking exchanges, while disabling the respective pipelined work.

`BlockFetchPairedSession` and `TxSubmission2PairedSession` prove both projections
into the existing local replay models. `BlockFetchPairedLocal` proves that its
state-type adapter preserves every existing client/server transition. The
shared certified search supplies a merged execution with exact input
projections, or refutes all such merges.

**Both protocols also have composed PTree/FIFO bridges.**
`BlockFetchPairedBridge` targets the existing `BlockFetchPipe.client` and
sequential server; `TxSubmission2PairedBridge` targets the existing strict
`TxSubmission2Pipe.client` and pipelined server. The shared `CSP/AsyncPair`
composition forwards complete native payloads through two initially empty
FIFOs. For arbitrary Params, depth, link and direction, `checker-sound` maps an
accepted certificate to one joint execution and `checker-complete` maps an
observed joint execution back to a certificate. `bridge`, `inputs-bridge` and
`certificate-bridge` express the corresponding equivalences.

The replay-to-PTree construction requires a Block inhabitant for BlockFetch,
or a TxHash inhabitant for TxSubmission2. The PTree-to-replay direction needs
neither. The final observation still erases payload contents beyond the
retained control fields. These are explicit peer/FIFO products, with no claim
about the existing node/mux assembly or Haskell refinement.
See [the paired control note](../../../docs/notes/paired-control-replay.md)
for examples, observation limits and validation.

## Exact-field paired Notify bridge

`LeiosNotifyPairedBridge` proves soundness, completeness, trace equivalence and
endpoint-input/witness correspondence for the existing Notify pair checker at
all depths. Its native peer/FIFO target uses `LeiosNotifyExactParams.exactParams`:
summary carriers preserve every normalized Notify field, including ordered and
repeated vote entries. This is a concrete representation of retained summaries,
not a full-block or signature-validity theorem, nor an arbitrary-Params bridge.
Fetch's exact-field composed bridge remains open. See the
[exact Notify bridge note](../../../docs/notes/leiosnotify-exact-paired-bridge.md).

## Paired LeiosNotifyP and LeiosFetchP

```sh
Main --paired-notify PAIR.txt [K_NOTIFY]
Main --paired-fetch PAIR.txt [K_FETCH]
python3 -I src/Cardano_network/Replay/LogProcessing/paired_sessions.py manifest.json PAIR.txt
```

**Default capacities: Notify 1, Fetch client 150.** Notify uses bounded credits
at both endpoints; Fetch retains its sequential server. Both use exact parsed
message equality on two initially empty FIFOs and return source-mapped merge
witnesses. Headers and manifest protocol names are `LeiosNotifyP` and
`LeiosFetchP`; tracer namespaces retain their existing names without `P`.
Both local projection proofs are checked. Fetch's silent serve step is covered
by an exact weak-language normalization theorem.

**The older coarse local bridges alone do not establish exact-field composed
correspondence:** they erase some fields checked here, and
the original Notify peers still alternate at depth one. The new
`LeiosNotifyPipe` extension now has local kind/direction equivalence at every
depth, with explicit native payload witnesses for completeness. See the
[bounded Notify bridge note](../../../docs/notes/leiosnotify-pipeline-bridge.md).
The next layer now supplies actual peer/FIFO PTree compositions using the
shared `CSP/AsyncPair` library, with proved operational trace correspondence.
Fetch additionally has a store-backed target and inherited projected server
legality; a formal counterexample shows why its unconstrained bare server
cannot be used directly for checker soundness. Those older target scopes still require exact log-observation and joint
completeness proofs; the separate summary-preserving Notify result above
provides both for its explicitly stated native instance.
See [the Leios paired note](../../../docs/notes/paired-leios-replay.md) for
input examples, manifest grammar, exact fields, proofs and validation.

## Paired ChainSync pilot

```sh
Main --paired-chainsync PAIR.txt [K_CS]
python3 -I src/Cardano_network/Replay/LogProcessing/chainsync_pair.py manifest.json PAIR.txt
```

The manifest explicitly identifies the connection, session and both local
endpoint generations, and attests fresh capture. Two directional FIFOs match
receives against sends. The checker searches order-preserving merges, using
both existing local state machines, with client capacity 300 by default.
Acceptance prints a source-mapped witness and accepts in-flight messages at EOF.
Rejection excludes every valid merge under those declared capture assumptions.
Input/evidence errors are reported separately. No cross-node timestamp sort or
automatic connection pairing is performed.

`Paired`, `PairedDecide` and `ChainSyncPairedSession` certify the first-order
machine, merge search and local projections. `ChainSyncPairedBridge` now proves
both directions against the original client/server PTrees composed through
explicit full-payload FIFO queues; `inputs-bridge` includes the existential
merge order. Completeness needs one `Block` inhabitant; soundness does not.
This product is not the existing node/mux assembly. The existing raw adapter
skips the server's Serialised
tracer, so real paired captures need additional explicit server adaptation;
this pilot accepts normalized sessions and supplied source maps.

## TxSubmission2 submitter and requester

```sh
Main --txsubmission2 FILE [K_TS]
Main --interleaved FILE [K_FETCH [K_NOTIFY [K_BF [K_CS [K_TS]]]]]
```

**The client submits; the server requests and pipelines.** `TxSubmission2Session`
checks Init, a FIFO of nonblocking ID/transaction requests, exclusive blocking
ID requests, nonempty blocking replies, and client Done only in the blocking
state. The default requester message capacity is **4**, a configurable replay
policy, not an asserted prototype-wide pipeline limit. Client consumption is
sequential and ignores that bound.

Input retains Blocking/NonBlocking and Empty/NonEmpty ID-reply shapes, using
`TxSubmission.Remote.*` namespaces (`MsgInit` for Init). Tags are
`txsubmission2:client/server`. Transaction contents, acknowledgements, ID
membership and byte budgets are outside this control-only checker. Decisions
are certified against the first-order model. `TxSubmission2ClientBridge` and
`TxSubmission2ServerBridge` prove exact finite control-trace correspondence with
the strict `TxSubmission2Pipe.client` and pipelined `.server`, for arbitrary
parameters, depth and endpoint. Soundness is unconditional; completeness needs
one `TxHash` inhabitant for nonempty replies. `TxSubmission2BridgeTests` supplies
inhabited PTree witnesses and negative controls.

**Standard node logs lack required TxSubmission2 control fields.** Mixed
adaptation now includes this protocol by default and fails precisely when
blocking or reply-emptiness evidence is missing. An enriched tracer can supply
those fields. Use `--exclude-txsubmission2` explicitly to normalize only the
other protocols. See [the TxSubmission2 note](../../../docs/notes/txsubmission2-replay.md)
for the pinned sources, exact grammar, validation and devnet coverage audit.

## ChainSync client and server

```sh
Main --chainsync FILE [K_CS]
Main --interleaved FILE [K_FETCH [K_NOTIFY [K_BF [K_CS]]]]
```

`ChainSyncSession` checks both roles; **only the client pipelines RequestNext**.
The default client bound is **300**, matching the pinned network high watermark.
AwaitReply retains the oldest request and must be followed by a roll response;
FindIntersect and Done require an empty pipeline. The server is sequential and
ignores the client bound. `chainsync:client` and `chainsync:server` select product
components; standalone input selects the role with its header.

`ChainSyncParse` accepts kind-only Send/Recv rows and exact
`ChainSync.Remote.Send.*` / `Receive.*` namespaces. Payloads are outside the
checked language. The mixed adapter now handles five protocols and devnet
JSON wrappers, preserving source line numbers. Previous CLI forms remain valid.

**Certification scope:** `ChainSyncClientBridge` and `ChainSyncServerBridge`
prove both directions between replay and `ChainSyncPipe.client` / the existing
`ChainSync.CSserverStClient`, for arbitrary parameters, depth and endpoint.
Completeness needs one `Block` inhabitant; soundness does not.
`ChainSyncBridgeTests` supplies inhabited PTree runs and a transferred negative
control. Observation erases payloads and API events, and excludes semantic
termination; wire Done remains visible. These are standalone-peer results.
The current adapter still lacks a verified
boundary for mini-protocol restarts on surviving connections: two supplied
devnet streams reject a new FindIntersect after an outstanding AwaitReply.
See [the ChainSync note](../../../docs/notes/chainsync-replay.md) for exact source
pins, transition rules, checks, snapshot hashes and rejection analysis.

## Module naming

Protocol-specific modules use the full `LeiosFetch`, `LeiosNotify`,
`BlockFetch`, `ChainSync`, or `TxSubmission2` prefix. Role-specific bridge modules include `Client` or `Server`;
`LeiosNotifyBridge` contains both roles. The `LeiosNotify` prefix here refers to
**LeiosNotifyP**, not the earlier demo peer. `LeiosFetchServerModel` defines the
composed server; its proof endpoints are `LeiosFetchServerSound` and
`LeiosFetchServerComplete`.

Shared infrastructure retains neutral names: `Common`, `Namespaces`,
`ReplayParams`, `PipelineBounds`, `Sessions`, `ParseSessions`, `SessionReport`, and `Main`.
`LeiosFetchInterleaved*` and `LeiosFetchParseInterleaved` are the older
Fetch-only product APIs; `Sessions` is the heterogeneous product.

Some protocol modules also export reusable helpers: `LeiosFetchParse` provides
parsing utilities, `LeiosFetchServerParts.OutInv` and
`LeiosFetchServerForward.Fire` provide generic proof helpers, and
`BlockFetchClientSession` defines the wire alphabet shared with the server.
`BlockFetchReport` retains its neutral role name because its parser and event
printer serve both roles, alongside the legacy client reporter.

The naming cleanup changes module paths and imports only; it does not change
protocol definitions, theorem statements, CLI arguments, or log formats.
Downstream Agda imports must use the new names; there are no compatibility
modules at the old paths.

## BlockFetch client and server

```sh
Main --blockfetch FILE [K_BF]
Main --interleaved FILE [K_FETCH [K_NOTIFY [K_BF]]]
```

The shared **control-only** BlockFetch mode selects its checker from the
`role client` or `role server` header. `K_BF` defaults to 100 and applies only
to clients; supplying it for a server does not alter sequential server behavior.
Client files contain kind-only rows such as `Send RequestRange`, `Recv StartBatch`,
`Recv Block`, `Recv BatchDone`, `Recv NoBlocks`, and `Send ClientDone`. Exact
`BlockFetch.Remote.Send.*` / `Receive.*` namespaces are accepted too. Extra
payload tokens are rejected rather than silently treated as validated data.

`BlockFetchClientSession` provides certified decisions; `BlockFetchClientBridge` proves
soundness and completeness against `BlockFetchPipe.client` at every depth and
endpoint. Completeness explicitly takes an inhabited block value to construct
erased payloads. The proof hides application handoffs and internal collection;
it concerns finite wire-control traces, not block validity or whole-node behavior.

A `role server` file uses directions relative to the server. It permits one
range at a time: Recv RequestRange,
then Send NoBlocks or Send StartBatch / Block* / BatchDone, returning to idle.
Recv ClientDone closes an idle session. `BlockFetchServerSession` supplies its
certified decider, and `BlockFetchServerBridge` proves both directions against
the existing sequential `BFserverStClient`, including unlogged API handoffs.
Completeness has the same explicit block-inhabitance premise as the client.

Both modes accept unfinished prefixes. Server input must describe protocol
receives, not earlier mux ingress. The latest `cardano-node-20261014.log` contains
no `BlockFetch.Remote.*` observations, so it supplies no live-log validation for
these modes. The supplied three-node local-devnet logs likewise contain no
BlockFetch wire events, but all their Fetch/Notify sessions pass replay.
Raw BlockFetch adaptation is not yet provided.

Mixed manifests accept `blockfetch:client` and `blockfetch:server` alongside
`fetch:*` and `notify:*`. Bounds are independent (defaults 150, 1, 100). The
existing one/two-bound forms retain those defaults for omitted arguments.
`--blockfetch-client FILE [K_BF]` and `--blockfetch-server FILE` remain compatible
role-specific entry points; the latter still rejects a depth argument.

Each product component is checked independently. Acceptance does not match
one endpoint's sends to another endpoint's receives. See [the BlockFetch implementation note](../../../docs/notes/blockfetch-pipeline.md)
for source pins, theorem scope and testing commands.

## One model for interleaved sessions

`Sessions.agda` folds the generic heterogeneous product in
`Semantics/Replay/Interleave.agda` into a finite session model. The manifest
fixes each session's role and initial state. A tagged event changes only its
session; a silent step advances one component. Each component retains its own
protocol state and applicable bound; no event can consume another session's
pending request or credit.

The generic `projection-equivalence` theorem proves that a global trace is
permitted exactly when both component projections are permitted. Recursively,
`check` decides the finite product using local deciders: `yes` carries a trace
witness of the product, and `no` refutes product trace membership. This avoids
searching all permutations of independent server silent steps. No new
postulates, termination overrides, or classical assumptions are introduced.
The generic product, instance, parser, reporting and tests use `--safe`.

The generic product permits different event and state types and universes on
its two sides. Future mini-protocol replay specifications can therefore be
combined through the same product once their local replay interfaces and
deciders are provided. The executable combines all three protocols through `Sessions.agda` and
`ParseSessions.agda`; the original Fetch-only modules remain library APIs.

## Quit/Canceled shutdown (2026-11-02)

The protocol update follows the earlier `agda-cardano-common` shutdown work
(`41e5ed2dba05cbc0d62ef253b9b19e4e4baf3d7a` on
`kangfeng/leios-notify-graceful-shutdown`) and the consensus prototype at
`2416493bfdbe93b761b3a4bb1ccf2b4a913e5e4b`.
`lnpSendDone` now requests Quit; Done is a responder message. The new
`lnpSendCanceled` API cancels one request during normal operation. Quit and
Canceled do not split sessions: Done, NewMux, or the selected lifecycle boundary
does. Older Notify traces with initiator Done must be recaptured or explicitly
versioned; they do not describe this protocol.

For example, save this as `/tmp/notify-shutdown.txt` and run
`Main --notify /tmp/notify-shutdown.txt 2`:

```text
role client
Send RequestNext
Send RequestNext
Send Quit
Recv Votes -
Recv Canceled
Recv Done
```

It accepts six events. An in-flight notification can arrive after Quit; it is
drained without delivering it to the application. Done before the two owed
replies is rejected. Tests also construct an exact native paired execution with
two cancellations and a final Done.

The October 29 capture's Notify messages now normalize, including Quit/Canceled.
It contains no RequestNext observations, so strict replay from fresh sessions
cannot certify it: the first observed announcement has no request credit.
No requests are synthesized. The lookahead checker's silenced observation
accepts the same capture as prefixes, with the weaker meaning described in
[Lookahead Notify replay](#lookahead-notify-replay). Fetch replies missing hash/slot/bitmap fields are
a separate input limitation. See [the shutdown note](../../../docs/notes/leiosnotify-quit-cancel.md) for the
validation record and capture results.

## Configurable Notify pipeline depth (2026-10-14)

The executable accepts independent Fetch and Notify bounds:

```sh
Main FILE [K_FETCH]
Main --notify FILE [K_NOTIFY]
Main --interleaved FILE [K_FETCH [K_NOTIFY]]

# Use the audited prototype's request-count limits:
/tmp/leios-replay-build/Main --notify /tmp/notify-session.txt 1000
/tmp/leios-replay-build/Main --interleaved /tmp/leios-replay-20261014/interleaved.txt 150 1000
```

Current defaults are **Fetch 150, Notify 1**. A single interleaved bound still applies
to Fetch. Bounds are nonnegative decimal integers; malformed or extra arguments
print usage. Notify zero disables requests but permits an empty prefix or Quit/Done shutdown.

`LeiosNotifyPipeline.agda` supplies a safe specification parameterized by depth
and role. Each session is `openN n`, `quitting n`, or closed. RequestNext
increments the outstanding count only below the bound. A notification or Canceled
consumes one positive credit. Client Send Quit (server Recv Quit) freezes new
requests at any count. The client drains owed notifications/Canceled without API
delivery; after reading Quit the producer emits Canceled for each remaining
credit. Server Send Done (client Recv Done) requires `quitting 0` and closes
permanently. EOF can leave requests or shutdown outstanding. Each interleaved
session has its own counter. RequestNext identifies no hash; this local checker
does not validate blocks or votes.

`Sessions.modelWithDepth` and `checkWithDepth` pass the two bounds to their
respective components. `SessionReport.reportWithDepth` and
`reportNotifyWithDepth` expose them to the CLI. Original `model`, `check`,
`report`, and `reportNotify` calls retain depth-one Notify defaults.

**Proof scope:** `LeiosNotifySession` and `LeiosNotifyBridge` describe the
updated alternating `LeiosNotifyP` peers. `strict-into-pipeline` and
`LeiosNotifyPipeDepthOne.old-to-new` embed their observations in capacity one.
The converse is false: `Send RequestNext; Send Quit` is legal in the pipeline
and illegal in the alternating peer. The former depth-one equivalence has been
removed. The decider and heterogeneous product remain certified at every bound.
`LeiosNotifyPipeBridge` proves local wire-control equivalence for the bounded
native peers; `LeiosNotifyPairedBridge` retains its exact-field two-FIFO scope,
including Quit/Canceled/Done. This does not prove Haskell implementation
refinement, byte budgets, shared application state or composed-node behavior.

Mixed and standalone Notify rejection reports binary-search prefix membership
using prefix closure, then retrieve the preceding accepted state. This reduces
the number of repeated prefix decisions from linear to logarithmic in the event
count; parsing, each decision, and product projection still have their own cost.
The original Fetch-only reporter retains its sequential scan.

Validation includes `LeiosNotifyPipelineTests.agda` for fill/refill/drain, both roles,
overflow, underflow, busy Done, closed sessions, zero, prefixes, session isolation,
independent bounds, and diagnostics. The old bridge tests still check with
`agda --safe`. Compiled CLI tests cover legacy calls, malformed arguments,
mixed bounds, and acceptance of 1,000 requests versus rejection of the 1,001st.

The requested latest test input was
`/home/rye/YE_Workspace_Research/Workspace_IOG/Tests_Experiments/cardano-node-20261014.log`.
Normalization produced **3,621 sessions and 73,271 events** in
`/tmp/leios-replay-20261014`: 1,682 Fetch sessions and 1,939 Notify sessions.
There are no normalized Notify RequestNext records. At Fetch 150 / Notify 1,000,
the full interleaved checker rejects at global event **3,329**, session **67**:
a received BlockAnnouncement with outstanding count zero. Its preceding 3,328
events accept. Prefix closure therefore rules out acceptance of the complete
normalized stream, regardless of later events. No requests were synthesized;
this finding does not by itself establish a prototype violation or identify why
request records are absent from the log.

## LeiosNotifyP and mixed-protocol replay (2026-10-13)

This section describes the original depth-one reference and initial extension.
The executable now uses the configurable model above.

**Implemented:** `LeiosNotifySession` models the existing depth-one
`LeiosNotifyP` control flow. `Sessions` folds Fetch and Notify specifications
into one heterogeneous product; `ParseSessions` routes each event using its
manifest entry. The older Fetch-only modules remain available as library APIs.
The CLI now uses `SessionReport` for interleaved input.

| Current state | Client event | Server event | Next state |
|---|---|---|---|
| idle | Send RequestNext | Recv RequestNext | busy |
| busy | Recv notification | Send notification | idle |
| busy | Recv Canceled | Send Canceled | idle |
| idle | Send Quit | Recv Quit | quitting |
| quitting | Recv Done | Send Done | closed |

A notification is one of `BlockAnnouncement`, `BlockOffer`, `BlockTxsOffer`,
or `Votes`. All other transitions reject. In particular, repeated requests,
unsolicited notifications/Canceled, Quit while busy, premature Done, and events
after Done reject in this alternating reference. The pipelined model permits
Quit while busy and drains the outstanding responses.
The machine has no silent transitions; finite successor enumeration and
trivial τ accessibility give a total trace decider. Empty traces and outstanding
requests at EOF accept as prefixes. This reference model has exactly one
outstanding request; `LeiosNotifyPipeline` now supplies the executable's
independently configurable Notify bound.

The mixed adapter preserves the original tracer namespace on **every event
row**, in both the global stream and per-session files. For example:

```text
sessions notify:client fetch:client
0 LeiosNotify.Remote.Send.RequestNext
1 LeiosFetch.Remote.Send.BlockRequest ab 7
0 LeiosNotify.Remote.Receive.BlockOffer cd 8 20
1 LeiosFetch.Remote.Receive.Block ab 20
```

Per-session files omit only the leading numerical session id. The namespace
identifies protocol, wire direction and message kind without consulting the
manifest. `Receive` corresponds to the legacy `Recv`; both Notify request
namespace spellings (`RequestNext` and `NotificationRequestNext`) are accepted.
The parser rejects a namespace belonging to another protocol, including shared
message names such as Done. The manifest still assigns each independent state
machine its protocol and role. Legacy `Send/Recv Message` input remains valid,
and the Fetch-only adapter retains its previous output format.

The normalized Notify payload grammar below uses the legacy direction/message
notation; namespace-form rows carry exactly the same trailing payload fields:

```text
<Send|Recv> RequestNext
<Send|Recv> BlockAnnouncement -
<Send|Recv> BlockAnnouncement <ebHash> <ebSlot> <ebBodySize>
<Send|Recv> BlockOffer <ebHash> <ebSlot> <ebBytesSize>
<Send|Recv> BlockTxsOffer <ebHash> <ebSlot>
<Send|Recv> Votes -
<Send|Recv> Votes <rbHash>:<voterId>,<rbHash>:<voterId>,...
<Send|Recv> Quit
<Send|Recv> Canceled
<Send|Recv> Done
```

Hashes are hexadecimal naturals; slots, sizes and voter ids are decimal
naturals. `-` denotes an absent announcement header or an empty vote list.
The parser retains these fields, but control transitions do not constrain them:
RequestNext names no hash, and this replay does not validate blocks or votes.

For example, the following is one accepted product trace:

```text
sessions notify:client fetch:client notify:server
0 Send RequestNext
1 Send BlockRequest ab 7
2 Recv RequestNext
0 Recv BlockOffer cd 8 20
2 Send Votes -
1 Recv Block ab 20
```

Manifest entries are `fetch:client`, `fetch:server`, `notify:client` and
`notify:server`. Bare `client` and `server` retain their old Fetch meaning.
Protocol-inappropriate messages and undeclared session ids are parse errors.
Each Notify session has its own idle/busy/closed state; a notification cannot
consume another session's request. Product trace membership is decided using
the same proved projection equivalence as Fetch-only interleaving.

Compile `Main.agda` as described below, then run:

```sh
python3 -I src/Cardano_network/Replay/LogProcessing/normalize_logs.py LOG /tmp/leios-mixed
/tmp/leios-replay-build/Main --interleaved /tmp/leios-mixed/interleaved.txt 4
/tmp/leios-replay-build/Main --notify /tmp/notify-session.txt
```

Standalone Notify input starts with `role client` or `role server` and has
untagged events. Its report uses the product format with one session. Existing
`Main FILE [K]` remains the Fetch-only checker mode. The single log adapter,
`normalize_logs.py`, handles mixed logs by default; use `--fetch-only` for the
former Fetch-only normalized format.
The mixed adapter groups by `(connectionId, role, protocol)` and generation,
assigns ids in first-event order, and preserves raw-file ordering. Done ends
only its own protocol/role session; NewMux closes **all protocols and roles**
on that connection. Mux Dead still does not split. Mixed per-session filenames
include the protocol, and `index.tsv` appends a protocol column. The source-map
and rejection-index conventions remain unchanged.

**Correspondence with the original peers:** `LeiosNotifyBridge.client-bridge` and
`LeiosNotifyBridge.server-bridge` establish both directions for the existing
`LNPclientStClient` and `LNPserverStClient`, at `replayParams`, link 0, direction
`hi`. They retain wire direction and all eight message kinds, while erasing all
notification payloads and omitting local API/done events. Completeness chooses
canonical payloads; it does not reconstruct logged hashes, slots, sizes, or
votes. Unlike the Fetch client bridge, this proof needs no replacement peer.
It is a standalone-peer result, not a bridge to `NodeLogicL`, a shared store,
or the composed node/network. The proof uses `--guardedness` and typechecks
with command-line `agda --safe`; the local spec, product and parser use `--safe`.

**Log coverage matters:** the adapter never synthesizes RequestNext. The
available `govstall-a1-20260927-full-head10000.log` extract contains 461 Notify
records and no Notify RequestNext records. Normalization yields 87 total
Fetch/Notify sessions; strict replay rejects at global event 2, session 1,
a received BlockAnnouncement at raw line 271. This is not sufficient evidence
of an implementation violation: the input is an extract and lacks the request
evidence required by this model. The locally inspected prototype also has
pipelined Notify peers, whereas Agda `LeiosNotifyP` is depth-one. Bounded
pipelining is supported by the replay extension above, and the pinned pipelined
implementation and an observation for silenced requests are covered by
[Lookahead Notify replay](#lookahead-notify-replay).

Validation includes `LeiosNotifyTests.agda` (positive witnesses, negative controls,
protocol parsing and interleaving), `LeiosNotifyBridge.agda` and explicit client/server trace witnesses in
`LeiosNotifyBridgeTests.agda` checked with `--safe`,
existing Fetch decision/product tests and both Fetch bridge endpoints, adapter
selftests, and compiled CLI integration tests:

```sh
python3 -I src/Cardano_network/Replay/LogProcessing/normalize_logs.py --selftest
python3 -I src/Cardano_network/Replay/LogProcessing/test_notify_replay.py /tmp/leios-replay-build/Main
```

## Run (Fetch-only normalization)

From `src/`, compile outside the repository:

```sh
agda --compile --compile-dir=/tmp/leios-replay-build Cardano_network/Replay/Main.agda
```

From the repository root, normalize one node's raw log and check the single
interleaved stream:

```sh
python3 -I src/Cardano_network/Replay/LogProcessing/normalize_logs.py --fetch-only LOG /tmp/leios-replay-log
/tmp/leios-replay-build/Main --interleaved /tmp/leios-replay-log/interleaved.txt 4
```

The existing `Main FILE [K]` mode and per-session adapter files remain available.
`K` defaults to 4 in both modes. The CLI prints accepted, rejected, or parse-error
reports; its process exit status does not encode these verdicts. (`LookaheadMain`
does encode them; see its README.)

## Format and session identity

```text
sessions client server client
0 Send BlockRequest ab 5
1 Recv BlockRequest cd 6
2 Send BlockRequest ef 7
1 Send Block cd 100
0 Recv Block ab 100
```

Session ids are zero-based positions in the header. Undeclared ids are parse
errors. Local event fields use the same syntax as `LeiosFetchParse.agda`, including
hexadecimal hashes and decimal slots and sizes. An empty log is `sessions`
with no events.

The adapter assigns ids in first-event order. Id `i` corresponds to `sNNNN`
in `index.tsv`, where `NNNN = i + 1`. The manifest thus fixes a role for each
connection/role/generation. A new generation is allocated after `Done` or at a
`Net.Mux.Remote.NewMux` boundary. Both roles of that connection end at `NewMux`;
`Net.Mux.Remote.State Dead` is not a boundary. Distinct peers and duplex roles
have separate state, and a reused connection never inherits the old queue.

`interleaved.txt` preserves raw-file event order, rather than concatenating
sessions or sorting timestamps. Its companion `interleaved.src` contains
`raw-line timestamp session-id` for each event. `index.tsv` retains the
connection id, role, first/last timestamps and `done`/`mux`/`eof` end reason.
A rejection reports the global 1-based event index, the zero-based session id,
and that component's state after the preceding accepted global prefix. Event
index `i` maps to normalized line `i + 1` and row `i` of `interleaved.src`.
Mixed/Notify rejection diagnostics binary-search prefix membership; the
Fetch-only reporter retains its sequential prefix scan.

## Scope of the result

This model is independent interleaving of session specifications. The manifest
and adapter establish session identity and boundaries; the Agda model does not
certify the raw-log adapter, mux lifecycle, or the provenance of those tags.
An externally relabelled stream may describe different sessions.

The existing PTree bridges still apply to individual projections: the existing
LeiosFetchP server with serving threads/store, and the new FIFO LeiosFetchPipe
client. There is no new PTree bridge to the composed node or network here.
In particular, independent server witnesses do not establish a common body
store, and acceptance does not verify shared node logic, payload validity,
cross-node send/receive matching, or delivery liveness. Adding shared state and
synchronisation requires a stronger model and additional bridge proofs.

## Verification

```sh
cd src
agda Cardano_network/Replay/LeiosFetchInterleavedTests.agda
agda Cardano_network/Replay/LeiosNotifyTests.agda
agda Cardano_network/Replay/LeiosNotifyPipelineTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyBridgeTests.agda
agda Cardano_network/Replay/Main.agda
```

From the repository root:

```sh
python3 -I src/Cardano_network/Replay/LogProcessing/normalize_logs.py --selftest
```

The lookahead checker has its own validation roots and CLI suite; see
[its README](LeiosNotifyPipeLookahead/README.md#validation).

The Agda tests include explicit positive product witnesses and negative
refutations, independent client bounds, cross-session isolation, server silent
steps, mixed roles, wrong hashes, closed sessions, new generations, valid
unfinished prefixes, malformed manifests, unknown tags and empty logs.
Adapter tests check order, exact agreement of each projection with the existing
session files, source mappings, `NewMux`/`Dead`, post-Done generations and empty
logs.
