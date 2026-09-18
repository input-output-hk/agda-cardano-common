# The Cardano N2N mini-protocols in this model

What is modelled, how, and what has been proved about each. For a reader who knows
the `ouroboros-network` node-to-node mini-protocol specifications and CSP, but not
this repository. References are `Module.agda:line`, relative to this directory
(`src/CSP/Examples/Cardano_network/`) unless prefixed with `src/`.

## 1. Overview

Six mini-protocols are modelled. Their identifiers are the constructors of `IDs`
(`Base.agda:33-35`), a parameter-free enumeration — the model identifies a
protocol by constructor, not by a numeric wire id. Only the two Leios protocols
carry a numeric id anywhere in the source, and only in a comment.

| `IDs` constructor | Numeric id in source | Peer module | Lines | Verified beyond typechecking |
|---|---|---|--:|---|
| `N2N_KeepAlive` | — | `KeepAlive.agda` | 273 | yes — the medium refinement chain is instantiated at this protocol |
| `N2N_ChainSync` | — | `ChainSync.agda` | 353 | yes — terminable-medium carrier; relay link inside `announceSafeT` |
| `N2N_BlockFetch` | — | `BlockFetch.lagda.md` | 1225 | yes — own `≈DR` refinements, provenance, liveness, priority |
| `N2N_TxSubmission` | — | `TxSubmission.agda` | 346 | no — typechecked only; exercised in the uniform bundle |
| `N2N_LeiosNotify` | 18 (`LeiosNotify.agda:13`) | `LeiosNotify.agda` | 255 | yes — carries the announcement in `announceSafeT` |
| `N2N_LeiosFetch` | 19 (`LeiosFetch.agda:13`) | `LeiosFetch.agda` | 373 | yes — the dominated side of the priority order |

**Initiator/agency convention.** A "connection" here is a *protocol-independent*
TCP link `Link = Fin numLinks` (`Params.agda:38`) plus a `Dir` (`Base.agda:104-105`):
`lo` means the lower-indexed endpoint initiates that mini-protocol instance, `hi`
the higher. A link may run two instances of the same protocol, one per direction;
`linkConfig : Fin numLinks → List (Dir × IDs)` (`Params.agda:41`) says which
`(direction, protocol)` pairs are live on each link, and an unlisted pair is
absent. Within a protocol, agency is the usual Ouroboros one, encoded by which
peer offers the `api` event in a state (§2).

## 2. The common modelling pattern

Every peer module follows the same six steps, so learning one is learning all six.

**Per-protocol event type.** A four-constructor GADT over the protocol's own
alphabet — e.g. `KAEv` (`KeepAlive.agda:82-86`): `sendXX : Link → Dir → XXEv
Payload` (peer → net, emitted with `!`); `receiveXX` (net → peer, bound with
`?`); `apiXXev : (l : Link) (d : Dir) (m : ApiXXTag) → XXEv (ApiXXCar m)` (the
peer-local application interface); `doneXX : Link → Dir → XXEv ⊤`. Wire events
negotiate one shared `Payload = Time × Mode × Length × Messages`
(`Data.agda:631-632`), whose `Messages` is the six-way sum of the per-protocol
message datatypes (`Data.agda:131-136`). CSPm carried the payload in the event
*label*; here it is the negotiated `?`/`!` value (`KeepAlive.agda:21-23`). Each
module also hand-writes `XXEv-≟ : (x y : AnyTypes XXEv) → Dec (x ≡ y)` (e.g.
`ChainSync.agda:71`) comparing `(constructor, l, d, tag)` — the carried value is
not part of event identity — and opens `CSP.Operators {E = XXEv}` at it
(`ChainSync.agda:131-132`).

**Peers as productive `iter` loops.** A peer is a *non-recursive* step function
over a finite state enum, tied with `iter` (`src/CSP/Operators.agda:1031`, via
`iter-bind` at `:1053`):

```agda
clientStep : Link → Dir → CSState → PTree CSEv (ExtI CSEv) (CSState ⊎ Rr)
CSclientStClient l d = iter (clientStep l d) stIdle      -- ChainSync.agda:252-253
```

`inj₁ s` loops back at state `s`, `inj₂ _` terminates (√). Both peers of a
protocol walk the *same* state enum; only agency differs — in each state one side
offers `apiXXev …` (application-driven) while the other branches on the
`receiveXX` value. That is how agency is encoded. Branching is a single
`pchoice v` whose offer map returns `nothing` for every event it does not accept,
rather than a `□` of pattern inputs (`KeepAlive.agda:24-28`). Every module is
`{-# OPTIONS --guardedness #-}`; none uses `NON_TERMINATING`.

**Renaming into the shared alphabet.** Each peer module ends with a documentation
stub `ιXXNet : ∀ {A} → XXEv A → Maybe (Net Payload A)` recording only the
intended wire images (`KeepAlive.agda:269-273`) — `Maybe`-valued because
`api`/`done` have no `Net` image. The real, total injection is in
`NetworkPar.agda`, into the *superset* alphabet `Net_Api Payload`
(`Net.agda:1075-1089`), which adds `done`, one `apiXX` channel per protocol, the
node-local `store`/`env` channels and the fault trigger `break`. For KeepAlive:
`sendKA l d ↦ input l d N2N_KeepAlive`, `receiveKA ↦ output …`,
`apiKAev l d a ↦ apiKA l d a`, `doneKA ↦ done … N2N_KeepAlive`, plus a partial
inverse `ιKA⁻¹` and left-inverse proof `ιKA-linv` fed to `CSP.Rename`; then
`KAclientA l d = RenKA.renameMap (KAclientStClient l d)`
(`NetworkPar.agda:96-97`). All six are treated the same way, yielding
`KAclientA`/`KAserverA`, `CSclientA`/`CSserverA`, `BFclientA`/`BFserverA`,
`TSclientA`/`TSserverA`, `LNclientA`/`LNserverA`, `LFclientA`/`LFserverA`.

**Bundling and the medium** (`NetworkPar.agda`, `NetCommon.agda`).
`nodeBundle l cl sv` (`:421-428`) is config-driven: it maps over `linkConfig l`
and per `(d , id)` picks `clientPeer l d id` when `d ≡ cl`, `serverPeer l d id`
when `d ≡ sv`, else `Skip`; `clientPeer`/`serverPeer` (`:401-416`) are **total**
on `IDs`, so all six protocols have real peers. `miniProtocols l cl sv`
(`:433-441`) is the uniform alternative — all twelve peers interleaved with `⦀`,
ignoring `linkConfig`. Peers then meet the medium on the `{| input, output |}`
event set `ioES` (`NetCommon.agda:127`), i.e. on the `(l, d, id)`-indexed
`input`/`output` channels only, via `withNet q = NetworkA ∥⇘ ioES ⇙ q`
(`NetCommon.agda:131-133`). The medium is the faithful multiplexer
`NetworkA`/`NetworkLinkA` or its copy specification `CopySpecA`
(`NetCommon.agda:83,88,159`), plus the `break`-interrupted
`CopySpecBreakableA`/`NetworkLinkBreakableA` (`:151-171`). Application logic
synchronises with the peers on the api alphabet `apiES` (`ApiAlphabet.agda`).

## 3. Protocol by protocol

### KeepAlive (`N2N_KeepAlive`)

States (`KeepAlive.agda:158-161`): `stClient`, `stServer Cookie`, `stDone`.
Messages (`Data.agda:79-81`): `MsgKeepAlive Cookie`,
`MsgKeepAliveResponse Cookie`, `MsgKADone`.

Client (`:181-220`): `stClient` offers `apiKA sendKAMsg`, binding the request
cookie from the api value, and sends `MsgKeepAlive cookieReq` → `stServer
cookieReq`; or `sendKADone` → `MsgKADone` → `stDone`. In `stServer cookieReq` it
receives `MsgKeepAliveResponse cookieRsp` and *guards the cookie match*: equal ⇒
back to `stClient`; unequal ⇒ it fires `apiKA errCookie ! (cookieReq, cookieRsp)`
and returns (`:209-211`). Server (`:233-256`): receives the request, reports it
as `apiKA recvKACookie ! cookieReq`, echoes `MsgKeepAliveResponse`, and on
`MsgKADone` fires `doneKA` and terminates.

*Abstracted away* (module header, `:20-38`): the receive side does not constrain
`Mode`/`Time`/`Length` at all, whereas the CSPm receive patterns pinned
`FromInitiator`/`FromResponder`; `Time`/`Length` are opaque `Params` domains and
the peers stamp the fillers `time₀`/`length₀`. So there is **no timeout and no
round-trip-time measurement** — most of what the real KeepAlive is for.

*Verified:* the medium refinement chain is instantiated exactly here — the
single-channel instance `p1` is `numLinks = 1`,
`linkConfig _ = (lo , N2N_KeepAlive) ∷ []` (`NetworkVerification/README.md:7`),
so `net≈DR` and everything downstream is about a medium carrying one KeepAlive
instance. The KeepAlive *client peer* also has the τ-free leaf specs
`KAclient`/`FrozenKAclient` in the CSP-refinement liveness route
(`FourNode/Liveness/README.md`).

### ChainSync (`N2N_ChainSync`)

States (`ChainSync.agda:139-144`): `stIdle`, `stCanAwait`, `stMustReply`,
`stIntersect`, `stDone` — the real state machine. All eight messages
(`Data.agda:92-99`): `MsgCSRequestNext`, `MsgCSAwaitReply`,
`MsgCSRollForward Header Tip`, `MsgCSRollBackward Point Tip`,
`MsgCSFindIntersect (List Point)`, `MsgCSIntersectFound Point Tip`,
`MsgCSIntersectNotFound Tip`, `MsgCSDone`.

The header tabulates both peers (`:12-28`). The consumer is api-driven in
`stIdle` (`RequestNext` / `FindIntersect pts` / `Done`) and receive-driven in
`stCanAwait`/`stMustReply`/`stIntersect`, forwarding each reply to the application
as `apiCS recvCSRollforward` etc. The producer is the mirror: receive-driven in
`stIdle`, where it notifies with `apiCS reqCSRequestNext`/`reqCSFindIntersect` or
fires `doneCS` on `MsgCSDone`, and api-driven in the reply states. The
`AwaitReply → MustReply` blocking distinction is modelled.

*Abstracted away:* chain validity and ordering — `Header`/`Point`/`Tip` are
derived types over opaque domains and no peer checks that a rollforward extends
anything; no timeouts, as above.

*Verified:* nothing about ChainSync in isolation. It is the protocol the
terminable medium's single-instance carrier is built at (one
`(lo , N2N_ChainSync)`, `Terminable/NetworkTRefinement.agda:4-5`), and a
load-bearing link in the announcement-safety relay chain — the generic node
logic's `clientLoop`/`serverLoop` drive `apiCS`
(`Parametric/NodeLogic.agda:278-311`), so it sits inside `announceSafeT` (§4).

### BlockFetch (`N2N_BlockFetch`)

States (`BlockFetch.lagda.md:162-165`): `stIdle`, `stBusy`, `stStreaming`,
`stDone`; the literate module carries the state diagram at `:32-53`. Messages
(`Data.agda:84-89`): `MsgRequestRange ChainRange`, `MsgStartBatch`,
`MsgNoBlocks`, `MsgBlock Block`, `MsgBatchDone`, `MsgClientDone`.

Client (`:192-244`): `stIdle` offers `apiBF sendBFRequestRange` or
`sendBFClientDone`; `stBusy` receives `MsgStartBatch` (→ `stStreaming`) or
`MsgNoBlocks` (→ `stIdle`); `stStreaming` delivers each `MsgBlock b` as
`apiBF recvBFBlock ! b` and stays, until `MsgBatchDone`. Server (`:251-307`) is
the mirror, notifying the range request as `apiBF reqBFRange`.

This module is much the largest because it also builds, over its *own* abstract
alphabets, the specifications the refinements are proved against: `BFabstract`
(serial spec, `:460`), `BFabstractP` (pipelined, capacity-2 streaming buffer,
`:555`), `clientBF`/`serverBF`/`clientServerBF` synchronised on the wire-message
set `msgBF` (`:632-662`), and a network version with a one-place copy medium
`copyL`, `networkBF` (`:1054`) and a capacity-3 sequential spec `BFnetSpec`
(`:1223`).

*Abstracted away:* block content (`Block` is opaque, and the requested range is
never checked against the delivered stream); pipelining *depth* is not a
parameter but baked into the chosen spec — capacity 2 for `BFabstractP`,
capacity 3 for `BFnetSpec`, each matching its implementation term rather than a
configurable window.

*Verified* — `BlockFetchRefinement/`, with no postulates in any of the five
modules:

- `BlockFetchAbsRefinement.agda` (3776) — `clientServerBF ∖ msgBF` and
  `BFabstract ∖ msgBF` are both divergence-free, giving the `⊇D` half of
  `(BFabstract ∖ msgBF) ⊑FD (clientServerBF ∖ msgBF)`.
- `BlockFetchAbsRefinementBisim.agda` (3914) —
  `clientServerBF ∖ msgBF ≈DR BFabstractP ∖ msgBF`, directly as a
  divergence-respecting weak bisimulation (a strict expansion cannot match the
  reordered pair of hidden τ's; the header explains why).
- `BlockFetchNetRefinement.agda` (3612) + `BlockFetchNetRefinementNet.agda`
  (930 — the 106-node `Good` graph giving `net-noDiv`) +
  `BlockFetchNetRefinementBisim.agda` (8562) —
  `BFnetSpec ∖ bfMsgES ≈DR networkBF ∖ ioBF`.

Scope caveat: these are stated over `BFAbsEv`/`BFNetEv`, BlockFetch's own
abstract alphabets, which carry no `Link`/`Dir`. `README.md:199-205` records this
subfolder as not yet ported to the `Link × Dir` medium — it is *not* a refinement
of the current multiplexer. BlockFetch is nonetheless the protocol three further
campaigns are about (§4).

### TxSubmission2 (`N2N_TxSubmission`)

States (`TxSubmission.agda:125-131`): `stInit`, `stIdle`, `stTxIdsBlocking`,
`stTxIdsNonBlocking`, `stTxs`, `stDone`. Messages (`Data.agda:102-107`):
`MsgTSInit`, `MsgTSRequestTxIds BlockingStyle ℕ ℕ`,
`MsgTSReplyTxIds (List Txid)`, `MsgTSRequestTxs (List Txid)`,
`MsgTSReplyTxs (List Tx)`, `MsgTSDone`.

Note the role inversion the real protocol has: `clientStep` is the **submitter**
(the initiator, which has the transactions) and `serverStep` the **requester**
(`:6-9`). The submitter's `stInit` clause is unconditional — send `MsgTSInit`,
hand agency over (`:182-185`). The requester then pulls
(`sendTSRequestTxIdsBlocking` / `…Pipelined` / `sendTSRequestTxsPipelined`,
`:275-289`) and the submitter replies from the matching state; `MsgTSDone` is
reachable only from `stTxIdsBlocking` (`:212-216`), as specified.

*Abstracted away:* the header is explicit (`:14-15`) — the "Pipelined" api tags
are just the `NonBlocking` variant, with **no actual concurrency; the model is
sequential**. There is no in-flight window and no pipelining depth. The `ℕ × ℕ`
acknowledge/request counts are carried through api and wire but never
constrained, and `Tx`/`Txid` are opaque.

*Verified:* nothing. Typechecked only; instantiated in the uniform
`miniProtocols` bundle and hence exercised in the four-node diamond scenarios.

### LeiosNotify (`N2N_LeiosNotify`, id 18)

States (`LeiosNotify.agda:119-122`): `stIdle`, `stBusy`, `stDone`. Messages
(`Data.agda:110-115`): `MsgLNRequestNext`, `MsgLNBlockAnnouncement Header`,
`MsgLNBlockOffer Point`, `MsgLNBlockTxsOffer Point`,
`MsgLNVotesOffer (List Vote)`, `MsgLNDone`.

Consumer (`:145-189`): from `stIdle`, api `sendLNRequestNext` →
`MsgLNRequestNext` → `stBusy`, or `sendLNDone` → `stDone`; in `stBusy` it
branches on which of the four notifications arrived and delivers it as the
matching `apiLN recvLN…`. Producer (`:196-244`): receives the request as a silent
state change (`:202`), and in `stBusy` the *application* picks exactly one of the
four notifications to send.

*Abstracted away:* this is the single-protocol LeiosNotify of the earlier draft
(header, `:13`), not the restructured CIP-164 family; announcement and offer
contents are opaque, and there is no batching.

*Verified:* this is the protocol the headline safety property is *about* —
`announceSafeT` gates `apiLN _ _ sendLNBlockAnnouncement` on the set of hashes
actually forged (§4).

### LeiosFetch (`N2N_LeiosFetch`, id 19)

States (`LeiosFetch.agda`, the `LFState` block): `stIdle`, `stBlock`,
`stBlockTxs`, `stVotes`, `stBlockRange`, `stDone`. Messages
(`Data.agda:119-128`): `MsgLFBlockRequest EBHash`, `MsgLFBlock EB`,
`MsgLFBlockTxsRequest Point LFBitmap`, `MsgLFBlockTxs (List Tx)`,
`MsgLFVotesRequest (List Vote)`, `MsgLFVoteDelivery (List VoteBlob)`,
`MsgLFBlockRangeRequest ChainRange`,
`MsgLFNextBlockAndTxsInRange Block (List Tx)`,
`MsgLFLastBlockAndTxsInRange Block (List Tx)`, `MsgLFDone`.

The consumer picks one of four request kinds from `stIdle` (`:184-215`), or
terminates; the producer delivers in the matching busy state. The block-range
case genuinely **streams**: the producer may send any number of
`MsgLFNextBlockAndTxsInRange`, staying in `stBlockRange` (`:345-348`), before a
final `MsgLFLastBlockAndTxsInRange` returns to `stIdle` (`:350`). On the consumer
side both arrive through the *same* api tag `recvLFRangeBlock`, the last one
returning to `stIdle` (`:255-258`).

*Abstracted away:* the same draft-protocol caveat as LeiosNotify (`:13`);
`EB`/`EBHash`/`LFBitmap`/`VoteBlob` are opaque, so the selective-tx bitmap selects
nothing in particular and no vote is validated.

*Verified:* it is the *dominated* side of the priority work (§4).

## 4. Cross-protocol verification

**Medium equivalence** — protocol-agnostic in statement, KeepAlive-instantiated.
The master theorem is `net≈DR : Network ≈DR CopySpec`, a divergence-respecting
weak bisimulation between the multiplexer and the per-`(l, d, id)` copy
specification, generic in the payload. The failures-divergences and trace
refinements, `network-deadlockFree`, `Network-divergenceFree` and their lifts to
the renamed `NetworkA` all follow by generic transfer: ten modules, **0
postulates**. The instance checked is the single KeepAlive channel `p1`. The
link-indexed rendering has results for *any* per-link `≢ [] × Unique` config —
`netLink≈DR`/`≈FD`/`⊑FD`/`spec⊑FD-Link` (`NetworkVerification/NetworkLinkEquiv.agda:96-116`),
also postulate-free — with breakable counterparts `netLinkBreakable≈DR`/`≈FD`
(`MediumEquivA.agda:275,284`) lifted to the diamond as
`breakableSystem≈DR`/`≈FD` (`FourNode/BreakableSystemEquiv.agda:423,429`). See
[`NetworkVerification/README.md`](NetworkVerification/README.md).

**Announcement safety — LeiosNotify.** `announceSafeT : ∀ (p : Params) (t :
Topology p) → LinkCfgWf p → AnnounceSpecT ⊑T systemOf (λ n → nodeLogic n [])`
(`Parametric/AnnounceSafeConcrete.agda:115`): a network of honest relays never
announces an unforged block, at **trace refinement `⊑T`** (the order that states
exactly a trace property — `⊑FD` would not imply it), over the concrete per-link
multiplexer, for every `Params` and `Topology`. The gated channel is
LeiosNotify's `apiLN _ _ sendLNBlockAnnouncement`, but the relay chain the proof
must close also runs through ChainSync and BlockFetch, since `nodeLogic`'s
per-endpoint thread quadruple drives `apiCS`/`apiBF`/`apiLN`
(`Parametric/NodeLogic.agda:58-62`). The only premise, `LinkCfgWf`, is decided at
the shipped instances, so `lineAnnounceSafeT`/`starAnnounceSafeT`/`diamondAnnounceSafeT`
(`Parametric/AnnounceSafeInstances.agda:59,71,86`) are premise-free. Scope: every
node is honest, and the property is deliberately *not* claimed against a
dishonest peer. Full assumption list, including the one inherited classical seam:
[`Parametric/AnnouncementSafety.md`](Parametric/AnnouncementSafety.md).

**Block provenance — BlockFetch.** The payload invariant underneath announcement
safety: the assume-guarantee carrier `Wf` ("every block I emit is well-announced,
provided every block I was handed was") and its congruences, because every
component in the chain is a relay (`Parametric/BlockProvenance.agda`). The
BlockFetch peers' `Wf` facts are proved over the peers' own alphabet `BFEv` and
transported across `ιBF` (`Parametric/BlockProvenanceBF.agda`);
`Parametric/BlockProvenanceSafe.agda` bridges `Wf` to safety's `Safe` carrier
under the side condition `Covers G`, which is why a single leaf's `Wf` fact is
not bridgeable.

**Priority — BlockFetch over LeiosFetch.** `bfOverLf : PriOrderC` makes, per
link, `sndmsg … N2N_BlockFetch` dominate that link's `sndmsg … N2N_LeiosFetch`
and orders nothing else, keying on the `IDs` tag every wire channel carries.
`NetworkLinkPri.agda` overlays `Priᶜ bfOverLf` on the per-link `Inputsₗ` *send
queue*, so LeiosFetch is pruned only while a BlockFetch message is genuinely
queued. `Priority/TxSidePriOneLink.agda` proves P1 prune-under-contention, P2
delayed-not-lost and P3 no-deadlock on a concrete one-link `Params`, at a
hand-built representative contention state that is *not* proved reachable;
`FourNodeDiamondPri.lagda.md` is a construction only. See
[`Priority/README.md`](Priority/README.md).

**Liveness — BlockFetch.** `blockLiveness⁺ : BlockLiveness⁺`
(`FourNode/Liveness/LTL/BlockLiveness.agda:48`), an LTL satisfaction statement
for the four-node breakable diamond whose two payload-exact atoms are BlockFetch
api events: `producedA b` is `apiBF … sendBFBlock` carrying `b`, `arrivedD b` is
`apiBF … recvBFBlock` carrying exactly the same `b`
(`FourNode/Liveness/LTL/Spec.lagda.md:108-127`). A second, independent route
states the same property as a `⊑FD` refinement, and its τ-free leaf specs are for
the *KeepAlive* client peer; both routes share one `≈DR` bisimulation. See
[`FourNode/Liveness/README.md`](FourNode/Liveness/README.md).

**Graceful shutdown — ChainSync instance.** `Terminable/` is self-contained
because the parent alphabet has no `mdone`: each copy cell runs until its own
`mdone l d id` fires, then terminates. `Terminable/NetworkTRefinement.agda`
assembles `CopySpecT ≈FD NetworkT` at a single `(lo , N2N_ChainSync)` instance,
generic in the payload — but its header states this holds **modulo 3 remaining
postulates** (`nd-net`, `sim-fwd-ev`, `sim-fwd-tau`; `:29-32`), so it is not a
complete proof.

## 5. Typechecking a peer module

From `src/` (never the repository root); imports are checked transitively.

```
cd src && agda CSP/Examples/Cardano_network/ChainSync.agda
```
