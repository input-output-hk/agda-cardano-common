# Linear Leios — what this directory proves

A port of the two Leios mini-protocols as implemented on the `leios-prototype` branch of
`ouroboros-consensus` (`LeiosDemoOnlyTest{Notify,Fetch}.hs`, protocol numbers 18/19), a
**Linear-Leios node logic** over them, **seven network-wide safety theorems — S0 and
S1–S5 — each with a premise-free instance stated against the shipped system itself**, the
node-level theorems they were lifted from, **eight negative controls**, and **no-livelock
theorems for a two-node instance and for the shipped three-node line** (`noLivelock2`,
`noLivelockL`) with their controls (section F). Everything
here is built on the repository's generic CSP-over-process-trees layer and on
`Cardano_network`'s existing `Params`/`Net`/`Node` scaffolding; nothing in the older
estate was changed to accommodate it.

The design spec is
`docs/superpowers/specs/2026-09-21-leios-prototype-protocols-design.md`; the two payload
abstractions are recorded in
`docs/superpowers/decisions/2026-09-21-leios-tx-closure-and-object-identities.md`. The
branch's public status record is `csp-ptree-agda/src/CSP/Laws_status.md` §"Leios prototype".

> **Read section C before quoting anything from sections A0, A or B.** All seven
> disciplines — S0 (announcement safety) and S1–S5 (the origin/soundness family) — are
> now NETWORK-wide trace-refinement facts about
> `systemOfWithNode (nodeWith nodeBundleP) NetworkLinkBreakableA (λ n → nodeLogicL n st₀)`,
> and each has a premise-free instance stated against `LeiosInstanceL.leiosSystemL`
> itself; they are section A0. Section A keeps the NODE-level theorems they were lifted
> from, which remain the load-bearing content. **Every negative control is still at node
> level or below** (section B). Nothing anywhere here is a delivery-liveness or a validity
> statement: the two progress-shaped results, section F's `noLivelock2` and `noLivelockL`,
> say the two-node instance and the shipped three-node line respectively have no infinite
> run of hidden events — not that any block is ever delivered.

---

## A0. The seven network-wide theorems

**Every discipline on this branch is now proved of the whole network.** All seven have the
same shape, over the builder, the medium and the per-node logic that
`LeiosInstanceL.leiosSystemL` (`:174`) is itself composed from:

```agda
Spec ⊑T systemOfWithNode (nodeWith nodeBundleP) NetworkLinkBreakableA (λ n → nodeLogicL n st₀)
```

— each node running `nodeLogicL` from empty stores behind its own twelve prototype peers,
all nodes interleaved against the concrete per-link multiplexer with the io channels
hidden. And each comes with a **premise-free instance stated against `leiosSystemL`
itself**, so the shipped witness is the subject of a theorem and not merely an instance of
one.

| # | ∀ theorem | module:line | premises of the ∀ form | shipped line, premise-free |
|---|---|---|---|---|
| S0 | `annSafeLT` | `AnnounceSystemL.agda:428-435` | `LinkCfgWf` | `leiosAnnSafeLT` (`:462-466`) |
| S1 | `bodySoundLT` | `BodySystemL.agda:246-249` | **none** | `leiosBodySoundLT` (`:270-272`) |
| S2 | `voteSoundLT` | `VoteSystemL.agda:254-257` | **none** | `leiosVoteSoundLT` (`:279-281`) |
| S2′ | `blobSoundLT` | `BlobSystemL.agda:249-255` | `nodeOf`, `nodeOf-voterOf` | `leiosBlobSoundLT` (`:276-278`) |
| S3 | `certSoundLT` | `CertSystemL.agda:263-268` | `CertifiesMono` | `leiosCertSoundLT` (`:286-288`) |
| S4 | `certRbSoundLT` | `CertRbSystemL.agda:261-264` | **none** | `leiosCertRbSoundLT` (`:286-288`) |
| **S5** | **`txSoundLT`** | **`TxSystemL.agda:260-263`** | **none** | **`leiosTxSoundLT`** (`:284-286`) |

**The dozen devnet.** `LeiosInstanceDozen.agda` instantiates all seven, premise-free, at
the 12-node, 45-link Leios demo devnet (3 BPs, each with 3 own relays; the 9 relays a K9
mesh; `pL 45 12`, `voterOf = id`), against `dozenSystem` (`:168`): `dozenAnnSafeT`
(`:182`, via `dozenLCfgWf`), `dozenBodySoundT`, `dozenVoteSoundT`, `dozenBlobSoundT`,
`dozenCertSoundT` (`:218`, oracle monotonicity re-proved as `dozenCertMono`),
`dozenCertRbSoundT`, `dozenTxSoundT` (`:233`). No no-livelock result is provided there.

Each `*LT` is ∀-`Params`, ∀-`LeiosParams`, ∀-topology, ∀-`voterOf`; the `apiES` argument
is fixed to the shared `ApiAlphabet.apiES`, which is where both of S0's `Assembly`
premises are discharged. S2′'s two extras are **parameter data, not hypotheses about the
logic**: a map `nodeOf : VoterId → Node` and the retraction
`nodeOf-voterOf : ∀ n → nodeOf (voterOf n) ≡ n` (`BlobSystemL.agda:251-252`), both the
identity at the shipped line. S3's `CertifiesMono` is a hypothesis about the **oracle**,
discharged by `CertSound.certMonoL` (`:816-817`). S0's `LinkCfgWf` is the medium
transport's and is *decided* at the shipped line by `leiosLCfgWf`
(`AnnounceSystemL.agda:450-451`). S5's `Generic` takes exactly the five arguments
`NodeLogicL.Generic` takes (`TxOrigin.agda:176-180`) and carries no premise at all, in the
∀ form as much as at the line.

**Why the lift is sound — the endpoint re-keying.** The node-level statements of §A are
sound at node level for a reason that does **not** survive a naive lift: each of the five
disciplines S1–S4 used to be *endpoint-agnostic* in its mints, minting at every `(l , d)`,
which is harmless only because inside `nodeP n (nodeLogicL n st₀)` the only `store`/`env`
channels that occur are the `homeOf n` ones. Lifted naively, **node X's mint would have
licensed node Y's deposit**. That warning was correct, and it has now been *discharged*
rather than dropped: every one of those five keys is indexed by the endpoint, and S5 —
written after the re-keying — was indexed from the start —

| discipline | key | mint | gate |
|---|---|---|---|
| S1 | `BodyKey = (Link × Dir) × EBHash` (`BodyOrigin.agda:272-273`) | `bodyMints` (`:347-351`) | `bodyGate` (`:360`) |
| S2 | `VoteKeyE = (Link × Dir) × VoteKey` (`VoteSound.agda:358-359`) | `voteMints` (`:424-429`) | `voteGate` (`:469`) |
| S2′ | `BlobKey = (Link × Dir) × VoteBlob` (`BlobOrigin.agda:237-238`) | `isPutVote` (`:331`) | `vouchedAt` (`:347-348`), `blobGate` (`:352`) |
| S3 | `Minted = List ((Link × Dir) × VoteBlob)` (`CertSound.agda:249-250`) | `certMints` (`:295-297`) | `certGate` (`:322`) via `blobsAt` (`:267`) |
| S4 | `CertRbKey = (Link × Dir) × RbHash` (`CertRbOrigin.agda:280-281`) | `certRbMints` (`:352-356`) | `vouchedRb` (`:361-362`), `certRbGate` (`:366`) |
| S5 | `TxKey = (Link × Dir) × TxHash` (`TxOrigin.agda:279-280`) | `txMints` (`:397-403`) | `vouched` (`:407`), `txGate` (`:412`) |

— and every gate reads the **deposit's own endpoint**, normalising through `homeAt` where
the minting channel is an api channel rather than a store channel. `homeOf` is injective
(`homeOf-inj`, `BlobOrigin.agda:296-297`), so node X's keys are keys no deposit of node
Y's can spend. That is the whole content of
the lift, and it is the reason the lift is sound: keep the reasoning, it is not scaffolding.

S5 needs **two** normalisations rather than one, and that is `NodeLogicL`'s direction rule
and not a choice: its Notify-client mint (`apiLP l d lfpSendBlockTxsRequest`) is keyed by
`homeAt (l , d)` because `lnClientLoopL` drives `d`, while its TxSubmission mint
(`apiTS l d sendTSRequestTxsPipelined`) is keyed by `homeOpp (l , d)` because the
TxSubmission requester is a SERVER peer and `tsPull` drives `opposite d` — `homeAt`
(`TxOrigin.agda:353-354`) and `homeOpp` (`:361-362`). Its third mint, `env l d envSubmit`,
is already node-local, because `submitEv n` and `putTxEv n` both fire at `homeOf n`, so
record η closes that third of the discipline definitionally.

**The honest comparison is "no weaker", never "strictly stronger".** The node-level
theorem texts in §A are byte-identical to what they were before the re-keying, but their
**specifications are different processes**. For each discipline the new gate reads the old
gate's keys with the foreign endpoints dropped, so whenever the new gate stands open the
old one did too — every trace the new spec permits, the old one permitted. The converse is
not proved, **no separating witness exists anywhere on the branch**, and commit `cabe60cf`
exists because that implication was once written the wrong way round. Do not write
"strictly stronger". **This rule applies to the five RE-KEYED disciplines only.** S5 is a
new theorem: it had no endpoint-blind predecessor, so there is no comparison to make, and
inventing one — in either direction — would be a fabrication.

**What none of the seven says.** Nothing about liveness: `⊑T` is a safety order and **no
module exhibits a good node reaching a gated event** (§C). Nothing about validity. Nothing
about divergence (section F's no-livelock theorems are separate results, about a two-node
instance and about the shipped three-node line, and are not delivery liveness either). And nothing about *which* node forged, in S0's case, because the spec's
forged set is global — see below.

### S0 — announcement safety, in detail

**What it says.** Every trace of the whole N-node network — each node running the fifteen
Linear-Leios thread families against its five stores behind its own prototype peer bundle,
all nodes interleaved against the concrete per-link multiplexer with the io channels hidden
— is a trace of `AnnounceSpecT` (`AnnounceSafe.agda:275`). So **no node ever announces a
ranking block whose announced EB hash no `env _ _ envForge` produced**, on EITHER announce
channel: `AnnounceInvariant.AnnEv` covers `apiLN … sendLNBlockAnnouncement` and the
prototype `apiLP … lnpSendBlockAnnouncement` under one `announceOK`, so the statement is
not silently about the channel `nodeLogicL` never fires.

**HALF OF S0's SPEC IS INERT, and a write-up must say so.** `announceOffer` gates *both*
announce channels, but `nodeLogicL` fires only the `apiLP` one
(`AnnounceThreadsL.agda:265-268` — `lnServerLoopL` is the announce leaf, and `ok-annP` is
the only announce guarantee it needs) and `nodeBundleP` carries the prototype peers, so
**the `apiLN` arm is never exercised by the Leios system at all.** That is not vacuity —
the gate it carries is a real test, and the old-peer theorem
`AnnounceSafeConcrete.announceSafeT` does exercise that arm — but the two-channel gate is
**one** piece of Leios content, not two, and may not be presented as two.

**THE HONEST ANNOUNCE PATH IS UNWITNESSED AT LEIOS.** `AnnounceReachLBad` shows the gate
reachable *with the guard removed* (§B). In the honest logic a block reaches `held` through
the deliberately **ungated** `putEv` wire branch of `storeStepL`, so whether the shipped
node ever announces at all is a **liveness** question that nothing here answers.
`Parametric.RelayLive.announce-fires` (`:259`) does this for the Praos relay logic; **there
is no Leios analogue.** (Section F's `live2` delivers an RB across the link of a two-node
instance through ChainSync/BlockFetch; it fires no announcement.) "S0 constrains a path the system actually takes" is NOT
established and may not be written.

**Premises.** Exactly one: `AnnounceSafeConcrete.LinkCfgWf p` — every link's
mini-protocol configuration non-empty and duplicate-free. It is carried by the
copy-medium → concrete-medium transport alone (`MediumEquivA.netLinkBreakable≈DR`'s two
honest hypotheses, owner-accepted) and is **decided** at the shipped Leios line, so
`leiosAnnSafeLT` has no premise at all. There is no store premise: the invariant is
`All (WellAnnounced ms) held` and the nodes start from `st₀`, where `held = []`.

**What it does NOT say.** Nothing about liveness (`⊑T` is a safety order and no module
exhibits a node reaching an announcement). Nothing about WHICH node forged — the spec's
forged set is global, which is the whole reason the statement is true (see
`AnnounceSafe.agda`'s header: `storeStepL`'s `putEv` deposits a wire-received block with
NO announcement check, so a node-local gate would make it false). Nothing about
divergence. And nothing about the *content* of an announcement beyond its announced EB
hash.

**Why the peer bundle gets a waiver, not a vacuity claim.** The prototype LeiosNotify
producer really does accept an announcement and re-emit it
(`LeiosNotifyP.agda:285-290`, renamed onto `apiLP` by `PeersP.ιLNP`), so it cannot be
proved to carry nothing. `peersPG` (`AnnounceSystemL.agda:165`) therefore *excludes* that
channel — it is a peer RELY, exactly as `apiLN … sendLNBlockAnnouncement` already is in
`BlockProvenanceBF.peersG` — and `sep-apiL`'s `c-annP` arm discharges it from the fact
that `apiES` SYNCHRONISES the announcement, so no peer can fire it solo. The guarantee is
then owed by the logic, and `lnServerLoopL`'s gate (`AnnounceThreadsL.agda:455-467`) pays
it. The store half is `AnnounceStoreL`, whose ungated `putEv` is discharged from the rely
rather than assumed.

**The two negative controls.** `AnnounceStoreLBad.agda` — with `acceptForgeL`'s withholding
arm removed, the store fact fails (`¬wf-blockStoreLBad`, `:221`): S0's gate is
load-bearing. `AnnounceReachLBad.agda` — with the forge route's *announcement* check
removed, the gated event really fires (`ann-gate-reachable`, `:444`). Both are below the
theorem's level; see §B.

### The other six, in one line each

Each of S1–S5 lifts the node-level discipline of the same name (§A) with **no change to
its content** — the `*SoundLT` proof term is `osafe→⊑T (wf→osafe wf-system (noRet-system
…))` in every case, one `Wf fullα []` fact about the whole network turned into one
refinement. What makes them so much smaller than S0 is recorded in `CertSystemL`'s header:
every origin discipline confines `Carries` to a **single `store` channel**, so every
alphabet is `OriginLeaves.fullα`, every `Sep` is a two-liner, `HideCov` needs no `Covers`
enumeration, and the medium is a six-line vacuity rather than a copy→concrete transport —
hence no `LinkCfgWf`. S0 could not do that, because its medium really does carry blocks.

**S3 was the PILOT, and it was the EASIEST — not the hardest.** An earlier revision of
this file said "S3's lift is strictly harder than S2's, because its gate sits on the store
side of the `⦀`". **That was refuted by doing it.** S3's mint (`store l d stPutVote`) and
its gated label (`store l d stCert`) are *both* node-local store events emitted by the
same process, `NodeLogicL.voteStore` — so the endpoint re-keying is immediate, the
thread side of `∥⇘ storeES ⇙` takes the empty guarantee alphabet and is discharged by
`OriginLeaves.wf-∅` in one line, and the store side carries one honest loop invariant
(`InvV ld ms vs = proj₁ vs ⊆ blobsAt ld ms`, `CertSound.agda:591-592`). The store side is
not a penalty; it is what made S3 the shortest route, so `CertSystemL` was built first and
the other four inherit its assembly. Do not re-derive the old claim.

### S5 — transaction origin, and the three limits that travel with it

**What it says.** No node of the network ever puts a transaction in its mempool unless the
environment handed it that transaction at its own `env … envSubmit`, or a TxSubmission
reply delivered one whose hash the node had itself asked for at
`apiTS … sendTSRequestTxsPipelined`, or its hash is one the EB body table names for a point
that node itself requested the tx closure of at `apiLP … lfpSendBlockTxsRequest`. The
∀ theorem is `txSoundLT` (`TxSystemL.agda:260-263`), the shipped line `leiosTxSoundLT`
(`:284-286`), the node-level content `TxOrigin.txSound` (`:1045-1046`).

**Two of the three mint clauses carry content; the first is non-droppable bookkeeping.**
All three deposit routes fire the same `store home(n) stPutTx` and the gate is *per
channel*, so each route's deposit must be licensed by something:

* `env l d envSubmit` is **self-licensing bookkeeping** — `submit` deposits that very
  transaction one step later (`NodeLogicL.agda:506-507`). It carries no content, and it
  cannot be dropped either: without it `submit`'s own deposit is unprovable.
* `apiTS l d sendTSRequestTxsPipelined` is **content**. `putAllTx`'s guard
  `memberOf (txHash tx) ids` (`NodeLogicL.agda:713-717`) is what discharges `wf-tsPull`
  (`TxOrigin.agda:826`); delete the guard and the leaf is unprovable, because a delivered
  transaction's hash need not be in `ids`.
* `apiLP l d lfpSendBlockTxsRequest` is **content**. `putChecked`'s guard
  `⌊ txHash tx ≟ k ⌋`, with `k` read out of `at? o (ebTxs h)` at the point `h` the request
  named, is what discharges `wf-lnClient` (`TxOrigin.agda:866`) — and `TxOriginBad`
  machine-checks that deleting it is an actual refutation (§B).

This "one clause is bookkeeping, the rest is content" shape is the honest shape of **S1 and
S4 too**: S1's `env _ _ envForge` mint and S4's `apiBF _ _ recvBFBlock` mint are likewise
licensing the depositor's own immediately-preceding event.

**Three limits, and a write-up must carry all three.**

1. **No transaction in this model ever reaches consensus.** `ebTxs` is a `LeiosParams`
   field (`LeiosParams.agda:69-74`) fixed independently of any node's mempool, and nothing
   anywhere builds an EB or a ranking block out of `Mem`. The mempool's only two readers
   are wire servers — `tsServeBody` via `stGetTxAt` and `serveTxs` via `stGetTx` — so a
   transaction goes mempool → wire → mempool and stops. **S5 is diffusion hygiene, NOT the
   analogue of S1**: S1 guards the store the *voter* reads. The two may not be presented as
   peers.
2. **The key space saturates at the shipped line.** `LeiosInstanceL` takes
   `Tx = TxHash = Bool` with `txHash = id`, so the whole per-endpoint key space is **two**
   keys and two `envSubmit` events mint all of it. The theorem stays non-vacuous
   ∀-`Params` and the control still bites, but the shipped-line window is two events wide.
   **This is parity with S1, not a new defect** — `EBHash = Bool` too, so S1's forge mint
   saturates identically.
3. **No module exhibits a good node reaching `stPutTx`**, so S5 constrains nothing the
   shipped system is *shown* to do. As everywhere else in this estate (§C).

Beyond the three: `txHash` is nowhere assumed injective, so both wire guards fix the HASH
and not the CONTENT; and the minted set is append-only and unpaired
(`mintedAfter at a ms = mints at a ++ ms`, `OriginSafe.agda:203-204`), so one request licenses unboundedly many later
deposits of those hashes at that node. S5 is "every deposit has an earlier origin", not
"one request, one deposit".

**S5's vacuity alphabet is the MIRROR IMAGE of S1's.** `BodyOrigin.noPuts` excludes `stPut`
and `stPutBody` and says nothing about `stPutTx`; S5's `noTxPut` (`TxOrigin.agda:594-596`)
excludes `stPutTx` and nothing else. Because S5 gates one tag that the forge touches not at
all, `forgeL`/`forgeBodyL`/`forgeCertL` and `fetchBody` — content-bearing for S1 and/or S4
— are one-line vacuities here (`oo-forgeL`, `TxOrigin.agda:639`; `oo-fetchBody`, `:773`),
while S5's two content-bearing wire leaves are among S1's cheapest. The two disciplines pay
in different places; neither subsumes the other, and no theorem on the branch relates them.

**The model changed for this.** Commit `0c2d3e63` gave `putAllTx` its `ids` guard. It was
the one deposit path of three with no wire check — `fetchBody` checks the delivered body's
hash against the point it asked for, `putChecked` checks each closure entry against the
hash the table names — so the asymmetry was unintentional, and fixing it makes the model
**more faithful**, not less. It is also what turned S5's TxSubmission clause from
bookkeeping into content: before the guard, that clause had nothing to discharge it.

---

## A. The node-level theorems the lift rests on

These are **not** superseded: they are the load-bearing content, and each system theorem
of §A0 is their discipline folded over the network. All have the same shape. A *discipline*
says which labels **mint** keys and which labels are **gated** by the keys minted so far;
the specification `OriginSpecT` (`OriginSafe.agda:231`) permits every trace except one that
fires a gated label whose gate is shut; and the theorem is that the node refines that
specification at `⊑T`:

```agda
Spec ⊑T nodeP n (nodeLogicL n st₀)        -- nodeP = nodeWith nodeBundleP
```

`nodeLogicL n st₀` (`NodeLogicL.agda:783`) is one node's whole logic — **five** node-level
threads (`forgeL`, `ebIndex`, `voter`, `submit`, `certSink`) in parallel with every
incident endpoint's ten, synchronised on `storeES` with all five stores — and `nodeP` wraps
that in the node's own prototype peer bundle, synchronised on `apiES`. `st₀` is the
empty-store state. (Five, not six: the certificate-RB forge became part of `forgeL` at
`76bb8ec2`, so node 0 of `leiosLLine`, which has degree 1, runs **fifteen** threads in
all.)

| # | Theorem | Module:line | Premises | Quantification |
|---|---|---|---|---|
| S1 | `bodySound` | `BodyOrigin.agda:971` | **none** | ∀ `Params`, ∀ `LeiosParams`, ∀ topology, ∀ `apiES`, ∀ `voterOf`, ∀ node |
| S2 | `voteSound` | `VoteSound.agda:1079` | **none** | as above |
| S2′ | `blobSound` | `BlobOrigin.agda:772` | `nodeOf`, `nodeOf-voterOf` | as above, plus the voter/node retraction |
| S3 | `certSound` | `CertSound.agda:791` | `CertifiesMono` | as above |
| S3 | `certSoundL` | `CertSound.agda:827` | **none** | the shipped instance only |
| S4 | `certRbSound` | `CertRbOrigin.agda:840` | **none** | as S1 |
| S5 | `txSound` | `TxOrigin.agda:1045` | **none** | as S1 |

The specifications of S1–S4 — all five disciplines, `certSound` and `certSoundL` sharing
one — were **re-keyed by the deposit endpoint** for the lift (§A0). Those theorem texts did
not change; the specifications are different processes, and the honest comparison is
**"no weaker"**. **S5 is not in that group**: it was written
endpoint-indexed from the start, so it has no predecessor and no such comparison exists.

### S1 — `bodySound`: an EB body is forged here or was asked for here

```agda
-- BodyOrigin.agda:951-952
BodySound : Set₁
BodySound = ∀ (n : Node) → BodySpecT ⊑T nodeP n (nodeLogicL n st₀)

-- BodyOrigin.agda:971-972
bodySound : BodySound
bodySound n = soundOf n (nodeLogicL n st₀) (wf-logic n) (noRet-logic n)
```

A node never stores an endorser-block body it neither forged nor requested. Minting is on
the environment's forge (`env _ _ envForge`) and on a LeiosFetch block request
(`apiLP _ _ lfpSendBlockRequest`); the gated label is the body deposit, and the gate is
membership of `ebHash eb` in the minted set (`bodyMints`, `BodyOrigin.agda:347-351`;
`bodyGate`, `BodyOrigin.agda:360`). **Premise-free.** Declared over
`Generic` (`BodyOrigin.agda:170-173`), whose parameters are `Params`, `LeiosParams`,
`Topology`, `apiES` and `voterOf`.

### S2 — `voteSound`: a vote blob is vouched for

```agda
-- VoteSound.agda:1064-1065
VoteSound : Set₁
VoteSound = ∀ (n : Node) → VoteSpecT ⊑T nodeP n (nodeLogicL n st₀)

-- VoteSound.agda:1079-1080
voteSound : VoteSound
voteSound n = soundOf n (nodeLogicL n st₀) (wf-logic n) (noRet-logic n)
```

A node deposits no vote blob it cannot vouch for: either a neighbour delivered that exact
blob on `lnpRecvVotes`, or the node itself read the ranking block the blob names *and* the
body of the endorser block that block announces. Three key sorts are minted — `kRb` on a
block read, `kBody` on a body read, `kRelay` on a Notify votes delivery
(`voteMints`, `VoteSound.agda:424-429`) — and only the `stPutVote` deposit is gated
(`voteGate`, `VoteSound.agda:469`). **Premise-free.**

### S2′ — `blobSound`: a relayed ballot has an origin

```agda
-- BlobOrigin.agda:757-758
BlobSound : Set₁
BlobSound = ∀ (n : Node) → BlobSpecT ⊑T nodeP n (nodeLogicL n st₀)

-- BlobOrigin.agda:772-773
blobSound : BlobSound
blobSound n = soundOf n (nodeLogicL n st₀) (wf-logic n) (noRet-logic n)
```

A node never deposits a blob attributed to **another** voter unless an `lnpRecvVotes`
delivery carried that exact blob; blobs it casts itself are attributed to itself
(`vouchedAt`, `BlobOrigin.agda:347-348`). **Two extra module parameters carry it**: a map
`nodeOf : VoterId → Node` and the round-trip law
`nodeOf-voterOf : ∀ n → nodeOf (voterOf n) ≡ n` (`BlobOrigin.agda:163-166`). At
`LeiosInstanceL` both are the identity, so they are discharged there.

### S3 — `certSound` / `certSoundL`: no certificate the oracle does not grant

```agda
-- CertSound.agda:776-777
CertSound : Set₁
CertSound = ∀ (n : Node) → CertSpecT ⊑T nodeP n (nodeLogicL n st₀)

-- CertSound.agda:791-792
certSound : CertSound
certSound n = soundOf n (nodeLogicL n st₀) (wf-logic n) (noRet-logic n)
```

`stCert r` fires only when the oracle certifies `r` against the vote blobs actually
deposited at this node (`certMints`, `CertSound.agda:295-297`; `certGate`,
`CertSound.agda:322`, which reads `blobsAt` of the DEPOSIT'S OWN endpoint, `:267`). The generic form carries one hypothesis about the **oracle**, not
about the logic:

```agda
-- CertSound.agda:328-329
CertifiesMono : Set
CertifiesMono = LeiosP.CertifiesMono p lp
```

— more blobs never withdraw a certificate. A *counting* quorum is inadmissible
(`[a,a] ⊆ [a]`). At the shipped oracle the premise is discharged, giving the one positive
stated at a concrete instance:

```agda
-- CertSound.agda:816-817
certMonoL : CSL.CertifiesMono
certMonoL sub r eq = any-mono _ sub eq

-- CertSound.agda:827-828
certSoundL : CSLS.CertSound
certSoundL = CSLS.certSound
```

`CSL` is `Generic leiosLParams leiosLP leiosLLine apiES (λ n → n)` (`CertSound.agda:811`)
— the three-node Linear-Leios line. `certSoundL` is therefore **unconditional but
instance-specific**, and it is a NODE-level statement. The claim about `leiosSystemL`
itself is a different theorem, `CertSystemL.leiosCertSoundLT` (§A0), which spends
`certMonoL` the same way at the system level.

### S4 — `certRbSound`: a certificate-carrying RB is earned or received

```agda
-- CertRbOrigin.agda:820-821
CertRbSound : Set₁
CertRbSound = ∀ (n : Node) → CertRbSpecT ⊑T nodeP n (nodeLogicL n st₀)

-- CertRbOrigin.agda:840-841
certRbSound : CertRbSound
certRbSound n = soundOf n (nodeLogicL n st₀) (wf-logic n) (noRet-logic n)
```

A node never puts a certificate-carrying ranking block into its own store unless its own
vote store had certified the RB that certificate names, or the block arrived off the wire.
A certificate-free block is free; a certificate-carrying one needs `rbCert b` to be in the
minted set (`vouchedRb`, `CertRbOrigin.agda:361-362`; `certRbGate`, `CertRbOrigin.agda:366`).
**Premise-free.** Note the two mint clauses:

```agda
-- CertRbOrigin.agda:352-356
certRbMints : (at : AnyTypes (Net_Api Payload)) → proj₁ at → List CertRbKey
certRbMints (_ , store l d (stHasCert r)) _ = ((l , d) , r) ∷ []
certRbMints (_ , apiBF l d recvBFBlock)   b =
  maybe′ (λ r → (homeAt (l , d) , r) ∷ []) [] (rbCert b)
certRbMints _                             _ = []
```

The second clause is deliberately **ungated and self-licensing** — see section C. The
re-keying narrows it to the *receiving* node; it does not turn it into a constraint.

### S5 — `txSound`: a transaction was handed over or asked for

```agda
-- TxOrigin.agda:1025-1026
TxSound : Set₁
TxSound = ∀ (n : Node) → TxSpecT ⊑T nodeP n (nodeLogicL n st₀)

-- TxOrigin.agda:1045-1046
txSound : TxSound
txSound n = soundOf n (nodeLogicL n st₀) (wf-logic n) (noRet-logic n)
```

A node deposits a transaction in its mempool only if the environment submitted that very
transaction or the node itself asked for its hash on the wire. Three labels mint
(`txMints`, `TxOrigin.agda:397-403`) and only the mempool deposit is gated (`vouched`,
`:407`; `txGate`, `:412`). **Premise-free**, over the same five module parameters as S1
(`TxOrigin.agda:176-180`). The gated channel is emitted by **threads** (`submit`,
`putAllTx` inside `tsPull`, `putChecked` inside the Notify client), never by a store, so
this is S1's orientation: the thread group carries `fullα`, the store group `∅α`, and the
assembly is `wf-withStores` (`:998`). Read §A0's S5 subsection for the three limits before
quoting it; in particular **S5 is diffusion hygiene and not the analogue of S1**.

---

## B. The negative controls

Eight in all: the six S1–S5 refutations below, plus S0's two (§A0). Each of the six
changes exactly **one** slot of the composite the positive is stated over, exhibits a trace
of the broken composite, and shows that trace is not a trace of the specification. All six
are at the concrete `leiosLParams` line, at node 0, at **node level or below** — a level
below every positive in §A0, and two levels below now that all seven are network-wide.

| Theorem | Control | Module:line | Substitution | Initial state | Composite |
|---|---|---|---|---|---|
| S1 | `bodySound-node-FAILS` | `BodyOriginBad.agda:395` | `lnClientLoopLBodyBad` for the Notify client | `st₀` | **reduced** — one thread + five stores, no bundle |
| S2 | `voteSound-node-FAILS` | `VoteSoundBad.agda:377` | `voterBad` in the voter slot | `stSeeded` | `nodeLogicL`'s own, inside `nodeP` |
| S2′ | `blobSound-node-FAILS` | `BlobOriginBad.agda:432` | `voterBlobBad` in the voter slot | `stSeeded` | `nodeLogicL`'s own, inside `nodeP` |
| S3 | `certSound-node-FAILS` | `CertSoundBad.agda:514` | `voteStoreBad` as the **fifth store** | `stSeeded` | `nodeLogicL`'s own, inside `nodeP` |
| S4 | `certRbSound-node-FAILS` | `CertRbOriginBad.agda:391` | `forgeLBad` (`:202`) in the forge slot | `st₀` | `nodeLogicL`'s own, inside `nodeP` |
| **S5** | **`txSound-node-FAILS`** | **`TxOriginBad.agda:555`** | `putCheckedBad` (`:189`) inside the Notify client, via `lnClientLoopLTxBad` (`:217`) | `st₀` | **reduced** — two threads + five stores, no bundle |

Round R2 (commits `ff0be020`..`d71e63a5`) restated four of the five controls that existed
then over `nodeLogicL`'s own composite, using the new `par-brBoth` introduction rule in
`CSP/Laws/Traces/TraceLawsParallel.agda`. `BodyOriginBad` was not restated; its reduction
is structural, not a missing lemma (section C). **S5's control, landed later, is reduced
for the identical structural reason** — its defect is on the wire branch and every `apiLP`
channel is inside `apiES` — so `par-brBoth` does not help it either.

### S2 — the body read is load-bearing

```agda
-- VoteSoundBad.agda:365-366
VoteSound-node-Bad : Set₁
VoteSound-node-Bad = VoteSpecT ⊑T badNode

-- VoteSoundBad.agda:377-378
voteSound-node-FAILS : ¬ VoteSound-node-Bad
voteSound-node-FAILS h = noGet (proj₂ (h _ bad-vote-fires))
```

`voterBad` (`VoteSoundBad.agda:149`) deletes `voterBody`'s `stGetBody` step, so the voter
votes on a block whose announced EB body it never read. `nodeLogicLBad`
(`VoteSoundBad.agda:161`) is `nodeLogicL`'s composite with that one slot changed;
`badNode = nodeP nA (nodeLogicLBad nA stSeeded)` (`VoteSoundBad.agda:181`). The seed
(`VoteSoundBad.agda:176`) holds one ranking block and nothing else, in particular **no**
body. Two visible events suffice, and the module pins that it is the body conjunct and
not an incidental hash mismatch that refuses the deposit
(`rb-conjunct-holds`, `VoteSoundBad.agda:331`; `body-conjunct-fails`, `:336`).

### S2′ — the voter's own attribution is load-bearing

```agda
-- BlobOriginBad.agda:419-420
BlobSound-node-Bad : Set₁
BlobSound-node-Bad = BlobSpecT ⊑T badNode

-- BlobOriginBad.agda:432-433
blobSound-node-FAILS : ¬ BlobSound-node-Bad
blobSound-node-FAILS h = noGet (proj₂ (h _ bad-blob-fires))
```

`voterBlobBad` (`BlobOriginBad.agda:169`) casts its ballot under another voter's name.
`nodeLogicLBlobBad` at `:181`, `badNode` at `:211`, and the seed `stSeeded` at `:206-207`
(one ranking block, one EB body).

### S3 — the oracle consultation is load-bearing

```agda
-- CertSoundBad.agda:500-501
CertSound-node-Bad : Set₁
CertSound-node-Bad = CertSpecT ⊑T badNode

-- CertSoundBad.agda:514-515
certSound-node-FAILS : ¬ CertSound-node-Bad
certSound-node-FAILS h = noGet (proj₂ (h _ bad-cert-fires))
```

The substituted slot is a **store**, not a thread: `voteStoreBad`
(`CertSoundBad.agda:210`) drops the oracle guard whole and fires `stCert` on every
deposit. The control also supplies its own stricter oracle `certifies₂`
(`CertSoundBad.agda:140`), a two-voter quorum, packaged as
`leiosLP₂ = record leiosLP { certifies = certifies₂ }` (`CertSoundBad.agda:146-147`).
`nodeLogicLCertBad` at `:222`, `badNode` at `:252`, and the seed `stSeeded` at `:247-248`.
Quote this as
"unsound **against a two-voter quorum**", never as "unsound".

### S1 — the wire-path guard is load-bearing (reduced composite)

```agda
-- BodyOriginBad.agda:384-385
BodySound-node-Bad : Set₁
BodySound-node-Bad = BodySpecT ⊑T badLogic

-- BodyOriginBad.agda:395-396
bodySound-node-FAILS : ¬ BodySound-node-Bad
bodySound-node-FAILS h = noReqNext (proj₂ (h _ bad-body-fires))
```

`badLogic = nodeLogicLBodyBad nA st₀` (`BodyOriginBad.agda:198-199`) is **one thread
against the five stores** (`BodyOriginBad.agda:181-185`), with the peer bundle and the
other fourteen threads absent. What it refutes is therefore `BodySpecT ⊑T <that composite>`, not
`BodySpecT ⊑T nodeP …`. The compensator is at the identical reduced composite with the
honest client in the thread slot:

```agda
-- BodyOriginBad.agda:403
bodySound-logic-good : BodySpecT ⊑T nodeLogicLBodyGood nA st₀
```

### S4 — the `stHasCert` rendezvous is load-bearing

```agda
-- CertRbOriginBad.agda:379-380
CertRbSound-node-Bad : Set₁
CertRbSound-node-Bad = CertRbSpecT ⊑T badNode

-- CertRbOriginBad.agda:391-392
certRbSound-node-FAILS : ¬ CertRbSound-node-Bad
certRbSound-node-FAILS h = noForgeCert (proj₂ (h _ bad-cert-fires))
```

`forgeLBad` (`CertRbOriginBad.agda:202-203`) deposits straight away instead of first
rendezvousing on `stHasCert r`. `nodeLogicLCertRbBad` at `:209`, and
`badNode = nodeP nA (nodeLogicLCertRbBad nA st₀)` (`CertRbOriginBad.agda:218-219`) — **at
`st₀`, the positive's own state**, so S4's A/B differs in exactly one thread and in
nothing else. Its compensator is the positive theorem itself:

```agda
-- CertRbOriginBad.agda:398-399
certRbSound-node-good : CertRbSpecT ⊑T nodeP nA (nodeLogicL nA st₀)
certRbSound-node-good = certRbSound nA
```

The control keeps its own `leiosLP₃` (`CertRbOriginBad.agda:126-127`), a record update of
`leiosLP` changing only `rbCert`, so its statement does not move with the shipped
instance. (`leiosLP` now carries the same value; see `LeiosInstanceL.agda:140`, and
`rbCert-agrees` at `CertRbOriginBad.agda:136` pins it.) The module's own header now says
"THE COMPOSITE IS NOT REDUCED" (`:36`) and agrees with its definition; an earlier revision
of this file flagged that header as stale, which it no longer is.

### S5 — the tx-closure offset-hash guard is load-bearing (reduced composite)

```agda
-- TxOriginBad.agda:543-544
TxSound-node-Bad : Set₁
TxSound-node-Bad = TxSpecT ⊑T badLogic

-- TxOriginBad.agda:555-556
txSound-node-FAILS : ¬ TxSound-node-Bad
txSound-node-FAILS h = noForge (proj₂ (h _ bad-tx-fires))
```

`putCheckedBad` (`TxOriginBad.agda:189-193`) drops `putChecked`'s `⌊ txHash tx ≟ k ⌋` and
stores whatever the reply carries at a valid offset. `badLogic`
(`TxOriginBad.agda:243-244`) is `nodeLogicLTxBad nA st₀` (`:226-230`): the **forge thread
and the broken Notify client** against the node's five real stores on the same
`∥⇘ storeES ⇙`, with the peer bundle and the other thirteen threads absent. So what is
refuted is `TxSpecT ⊑T <that composite>`, not `TxSpecT ⊑T nodeP …` — the same
`apiES`-structural reduction as S1's (§C).

**Why the forge thread is in it, and why the stores are still `st₀`.** Unlike
`BodyOriginBad`, the broken branch cannot be reached from empty stores by the client alone:
`fetchTxs` blocks at `getBodyEv n (proj₁ q)` before it sends its request
(`NodeLogicL.agda:625-629`), so the node must already hold the EB body of the point it was
offered. Rather than seed the body store — which would have cost the "from empty stores"
claim — the eight-event trace is **prefixed with the two-event forge deposit**
(`bad-tx-fires`, `TxOriginBad.agda:425`). Nothing is seeded anywhere.

**Two controls on the control, and the second is new in this estate.**

```agda
-- TxOriginBad.agda:563
txSound-logic-good : TxSpecT ⊑T goodLogic

-- TxOriginBad.agda:575-576
good-refuses : ¬ traces goodLogic badTrace
good-refuses h = noForge (proj₂ (txSound-logic-good _ h))
```

The first is the identical composite at the identical empty stores with the honest
`lnClientLoopL` in the client slot, assembled from `oo-forgeL` and `wf-lnClient` — the very
leaves `txSound` spends. The second **derives**, from that fact and the
specification-side refusal alone, that the violating trace is not a trace of the honest
composite: the mutation test, *proved* rather than run. Five pins record the shipped-instance
facts the break rests on — `table-pin` (`:257`), `offsets-pin` (`:261`),
`honest-rejects` (`:276`), `gate-requested` (`:467`) and `gate-unrequested` (`:472`); the
last two pin that the refusal is the OFFSET-HASH MISMATCH and nothing else.

### S0's two controls

Neither is shaped like S0's theorem, and that is deliberate — **announcement safety at
node level is false-or-vacuous**, so there is no node-level S0 to refute
(`AnnounceReachLBad.agda:26-32`).

| Control | Module:line | What it is |
|---|---|---|
| `¬wf-blockStoreLBad` | `AnnounceStoreLBad.agda:221` | With `acceptForgeL`'s withholding arm removed, the **store-level lemma** fails. The forge gate is load-bearing. Level: the RB store alone, not the node and not the network. |
| `ann-gate-reachable` | `AnnounceReachLBad.agda:444` | With the forge route's **announcement check** removed, the gated event really fires: `traces badNode (evForge ∷ evReq ∷ evGetAt ∷ evAnn ∷ [])`. Level: **level 2 of the acceptance ladder** — one node (node 0 of the concrete line) inside `nodeP`, a `traces` witness and not a `¬ _⊑T_`, over a BROKEN logic. |

Neither licenses anything about the honest path: see the "unwitnessed announce path" rule
in §A0. **Never put either of them and `annSafeLT`'s ∀-quantification in one sentence.**

### The other two negative facts

Neither is a control at all; both are properties of *designs that were rejected*.

| Fact | Module:line | What it is |
|---|---|---|
| `chatter-diverges` | `Negative/Chatter.agda:179` | `Diverges chatterPair` — the unchanged relay loop announces the same held block forever, so an infinite τ-path exists once the store and Notify channels are hidden. This is why `NodeLogicL.lnServerLoopL` carries a read pointer. |
| `wedge-reachable` / `wedge-stuck` | `wedge-reachable` at `Negative/FetchWedge.agda:147`, `wedge-stuck` at `:238` | A pointer-driven fetch asks for a body the neighbour does not hold; both sides of the rendezvous are in `storeES`, so the pair has **no** transition at all. Level: a pair plus one step, not a system. |

---

## C. How to read these claims

### All seven are NETWORK level at `⊑T`; every control is below that

Each of S0 and S1–S5 is a `systemOfWithNode` trace-refinement fact (section A0), and each
has a premise-free instance against `leiosSystemL` itself. Section A's node-level
statements remain as the content the system theorems are folded from.

**The lift warning this section used to carry has been DISCHARGED, not dropped, and the
reasoning is why the lift is sound.** Each discipline used to be *endpoint-agnostic* in its
mints — it minted at every `(l , d)` — which is harmless at node level only because inside
`nodeP n (nodeLogicL n st₀)` the only `store`/`env` channels are the `homeOf n` ones and no
bundle peer offers a `store` channel at all. **Lifted naively, node X's mint would have
licensed node Y's deposit.** The fix each module's header prescribed is the one that was
taken: index the key by `(l , d)` and gate a deposit at `(l , d)` on keys carrying that
same `(l , d)`. Every one of the five re-keyed disciplines now does exactly that (the key
table in §A0), `homeOf` is injective, and so a mint at node X opens no gate at node Y.
Keep this paragraph: a reader who does not know *why* the keys are indexed cannot tell the
lift from a mistake. **S5 was written endpoint-indexed from the start**, so it never
carried the warning — and it is the only discipline needing TWO normalisations, because its
two wire threads drive opposite directions (§A0).

**One claim this section used to make was REFUTED.** It said "S3's lift is strictly harder
than S2's, because its gate sits on the store side of the `⦀`". S3 was in fact the
**easiest** of the five, and became the pilot: its mint (`store l d stPutVote`) and its
gated label (`store l d stCert`) are both node-local store events emitted by the same
process, `NodeLogicL.voteStore`, so the thread side of `∥⇘ storeES ⇙` takes the empty
guarantee alphabet and is discharged in one line, and the store side needs one honest loop
invariant and no `homeAt` machinery at all. `CertSystemL` was built first and the other
four inherit its assembly almost verbatim. **Do not re-derive the old claim.**

S0 is still the odd one out in *shape*, not in level: its discipline
(`Parametric.BlockProvenance`'s `Carries`/`WellAnnounced`) mints on the ENVIRONMENT's
forge, which survives `∖ ioES` and is therefore global already, so it needs no re-keying —
and that same globality is why a node-LOCAL announcement gate would be *false*
(`storeStepL`'s `putEv` deposits a wire-received block with no announcement check). The
price is the only premise on the branch, `LinkCfgWf`, which the six origin theorems avoid
because their medium is a vacuity rather than a transport.

S0 also does not re-establish `AnnounceSafeConcrete.announceSafeT`, which remains a
separate theorem about the *old* relay logic and the old peers; the two share the
specification `AnnounceSpecT`, the medium transport and every leaf below the node logic,
and differ in the node builder and the node logic.

### No delivery liveness, and no validity

All results on this branch, node-level and network-level alike, are purely safety-shaped —
**except section F's no-livelock theorems**, which are divergence-freedom of a two-node
instance (`noLivelock2`) and of the shipped three-node line (`noLivelockL`), and the
LeiosNotify peer-PAIR results of `LeiosNotifyQuit.agda` (§D: conformance to the blueprint
state table, deadlock- and divergence-freedom of one directly composed client/server pair,
and termination after the client's quit) with their companion `LeiosNotifyQuitFD.agda`
(§D: receptiveness of each peer against the most general table partner, and the hidden pair
`≈DR` / `≈FD` the table with internal agency choices) and `LeiosNotifyQuitCancel.agda` (§D:
a client that stops requesting terminates within 7 visible events when the server cancels,
8 under load, on every run) and `LeiosNotifyQuitLive.agda` (§D: in the LTL library's run
semantics, every run with the client eventually not requesting and weakly fair quit /
server sends reaches √, each assumption shown necessary) and `LeiosNotifyQuitTerm.agda`
(§D: clean termination — MsgDone is the last event, nothing but MsgDone follows MsgQuit,
no half-closed state, and termination only through the Quit/Done handshake) and
`LeiosNotifyQuitNet.agda` (§D: the same peers over the real breakable copy cell — no io after
a link break, a break before the handshake completes forfeits √, and √ only after a break) and
`LeiosNotifyIsolation.agda` (§D: bundle level — once a configured LeiosNotify peer has
terminated, `nodeBundleP` is `∼` / `≈DR` the bundle without it, in a state the other peers
reach alone along the run's trace minus LeiosNotify's events) and `LeiosNotifyPipelined.agda`
/ `LeiosNotifyPipelinedProps.agda` (§D: a depth-1 PIPELINED client and READ-AHEAD server
over two one-way FIFOs — protocol-order table conformance, deadlock/divergence freedom,
quit completion within 8 events with the server application silent, the shutdown shape),
and none of these is
delivery liveness: **no module exhibits a good node actually reaching the gated
event**, and no theorem says a forged block ever arrives anywhere. The lift changed the
level and nothing else — `⊑T` is a safety order, and `systemOfWithNode` does not make it
one about progress. Three liveness ceilings are recorded in `NodeLogicL`'s own
comments and are reachable in the good logic — the forge thread's `stHasCert` rendezvous
blocks forever when the RB is never certified (`NodeLogicL.agda:400-403`; since R3 that
thread is `forgeL`, not a separate `forgeCert`); `bodyOfferBody`'s offer pointer waits at
an RB whose EB body, or whose EB's tx closure, never arrives, so neither the body nor the
closure of any later RB is offered on that endpoint (`:569-571`); `fetchTxs`'s leading
`getBodyEv` blocks the single Notify client thread (`:625-629`). None of this is
deadlock-freedom and none of it may be quoted as such.

**Two liveness bugs fixed on 2026-10-02, no theorem statement changed, argued by code
reading, not by a liveness theorem** (design
`docs/superpowers/specs/2026-10-02-leios-rb-dedup-and-closure-gate-design.md`). *RB echo:*
`storeStepL`'s `putEv` arm deposited every block it was handed, so two neighbours served
one block back and forth forever; it now keeps `held` when the block is already there and
still prepends a fresh one (`NodeLogicL.agda:314`), so no read pointer shifts. *Tx-closure
wedge:* `bodyOfferBody` sent `lnpSendBlockTxsOffer` as soon as it held the EB body, and a
peer's closure request then blocked `serveTxs` at a transaction this node lacked, stopping
the shared LeiosFetchP producer; the closure offer now waits in `awaitTxs` until the
mempool holds the whole closure (`:564-568`), so `serveTxs` can no longer block on a
closure this node offered (`:678-684`). That gate is the closure-pointer ceiling above, and
its trigger is the one bug 2 had: the environment never submits the closure transaction.
Spec §3.3's environment-duty assumption is what clears it — the fix narrows the blast
radius rather than making closure-starved runs live. Votes, announcements and Fetch body
serving keep flowing on that endpoint, but body diffusion of later EBs past that pointer
still stops, so downstream voters then block at `getBodyEv` for each later EB; this is a
model-versus-prototype divergence, since the prototype sends `MsgLeiosBlockOffer` per EB,
independent of another EB's closure. The forge route (`NodeLogic.acceptForge`) is not
deduped, and the forger is not required to hold the closure: an EB whose closure the
environment never submits is never closure-offered. Pinned by `DedupGateSanity`
(`dedup-held`, `fresh-prepends`, `gate-waits`, `empty-mempool-withholds`) — store- and
thread-local `viewV` facts about `storeStepL`/`bodyOfferBody` in isolation, not facts about
the composite; there is no delivery-liveness theorem here. The proof's RB-store bound
relies on the dedup and fails for the pre-fix store (`StoreBad`, store level); no
system-level failure of `bound2`/`noLivelock2` without the dedup is machine-checked. The
echo fix is now backed at two nodes by section F's `noLivelock2`, and on the shipped line
by `noLivelockL`; the tx-closure-wedge fix
remains argued by code reading only — the wedge is a deadlock, not a livelock.

Nor is anything a validity statement. The prototype's votes carry no verdict at all, so S3
says nothing about whether a certificate is *deserved*; S1 says a body was forged or
requested here, not that requesting it was *right*, and its guard is a hash test with
`ebHash` nowhere assumed injective; S2′ does not show the claimed voter really cast the
blob; S4's wire clause mints a hash, so one delivery licenses the deposit of every block
carrying that same certificate hash; and S5 says nothing about whether the transaction the
node asked for was one it should have asked for — any id a reply offers may be requested,
and a request MINTS — with `txHash` nowhere assumed injective, so both of its wire guards
fix the hash and not the content.

### The S4 write-up rule

These two sentences are what this branch may and may not be quoted on
(`Laws_status.md:1987`/`:1989-1990`; the second pair at `:2002`/`:2004`):

> **Quotable: "S4 has content at the shipped instance."**
>
> **NOT quotable: "S4 was shown to constrain a demonstrated behaviour of the shipped
> Leios line."**

The gate is machine-checked to be a real test *at the shipped instance* and not merely
inferred across instances — `NodeLogicLSanity.gate-uncertified-at-leiosLP` (`:202`) and
`gate-certified-at-leiosLP` (`:210`). But **no exhibited trace anywhere on this branch has
the gate refusing anything**: the forge deposit is reachable-in-principle and never
exhibited. And the wire clause is ungated and self-licensing
(`certRbMints … recvBFBlock`, `CertRbOrigin.agda:354-355`), so the only cert-RB depositor this
branch exhibits inside `nodeLogicL` is the BlockFetch `clientLoop`, whose deposit is
licensed by its own immediately-preceding `recvBFBlock`.

**DO NOT OVERSELL THE NETWORK FORM EITHER.** `certRbSoundLT` is the weakest of the seven in
content and the lift does not change that. The wire clause is **self-licensing by design**:
`certRbMints` on `apiBF l d recvBFBlock` mints exactly the key the following `stPut`
demands, so the wire route is unconstrained at system level just as it is at node level.
The endpoint re-keying narrows it to the *receiving* node — necessary for the network
statement to mean anything — and is not a new restriction on what a node may accept. Both
`CertRbOrigin`'s and `CertRbSystemL`'s headers carry this (`CertRbSystemL.agda:23-33`).

> **Quotable: "a cert-RB a node *invents* was certified by that node."**
>
> **NOT quotable: "every cert-RB in the network was earned somewhere."**

### The probe levels in `NodeLogicLSanity` differ and must not be conflated

`NodeLogicLSanity.agda` is a non-vacuity certificate for the R1 repair (two pure-rendezvous
`env` arms that unblocked `forgeCert` and `submit`). Nothing imports it. Its six probes sit
at **three different levels**:

| Probe | Line | Level |
|---|---|---|
| `forgeCert-first-step` | `:134` | an **LTS step of the full composite** `nodeLogicL nA st₀` |
| `submit-first-step` | `:157` | an **LTS step of the full composite** |
| `uncertified-blocks` | `:177` | a `viewV` fact about the **isolated** `voteStore nA _`, at ONE hash |
| `certified-offers` | `:185` | ditto, the same hash with `certs = rCert ∷ []` |
| `gate-uncertified-at-leiosLP` | `:202` | about the **specification gate** `certRbGate` at `leiosLP` — not about any process |
| `gate-certified-at-leiosLP` | `:210` | ditto — and note that since the re-keying the licensing key is `((fzero , lo) , rCert)`, i.e. the endpoint-indexed one |

Probes 3 and 4 are process facts about the store at one hash and two states; the ∀ version
is structural, in `NodeLogicL.offerCerts`, and is **not** what they pin. Probes 5 and 6
say nothing about the implementation. Nothing here may be quoted as a fact about the
composite except probes 1 and 2.

### Pairing a positive with its refutation

The standing rule "never pair a positive with its refutation" is **narrowed, not dropped**.
Since R2, the *composite* caveat is retired for S2/S2′/S3/S4 — those four controls run over
`nodeLogicL`'s own composite inside `nodeP`. **It is NOT retired for S1 or S5**, whose
composites are reduced. And every refutation is still at a **concrete parameter line**, at
**node 0**, at **NODE level or below**, and three of the six run from a **seeded** state
(`stSeeded`) whereas every positive is at `st₀`; S1, S4 and S5 are at `st₀`.
**The level gap WIDENED with the lift**: the positives are now network-wide and the
refutations are still at one node, so the distance to be respected is two levels, not one.
So: never pair an ∀-quantified positive with its concrete refutation in one sentence, and
never read a system-level break out of any of them. The same goes for S0's two controls
(§B), which sit lower still — one at the RB store alone, one at level 2 of the acceptance
ladder.

The `-good` compensators reflect that. `voteSound-node-good` (`VoteSoundBad.agda:386`),
`blobSound-node-good` (`BlobOriginBad.agda:443`) and `certSound-node-good`
(`CertSoundBad.agda:524`) are each the positive's own assembly applied to the *unmodified*
`nodeLogicL nA stSeeded`, so they compensate the **seed and nothing else**.
`certRbSound-node-good` (`CertRbOriginBad.agda:398`) is `certRbSound nA` itself.
`txSound-logic-good` (`TxOriginBad.agda:563`) compensates S5's **reduction**, at the
identical reduced composite and the identical `st₀`; and `good-refuses`
(`TxOriginBad.agda:575`) derives from it that the honest composite does not have the
violating trace — the only *derived* mutation test in this directory.

### Why S1 and S5 are still reduced, and why `par-brBoth` does not help either

S2/S2′/S3 were reduced because `ebIndex`, the voter, `lnServerLoopL` and `bodyOfferLoop` all
offer `stGetAt 0`: the full composite's first step is a **both-offer non-sync collision**,
for which the repo had `par-brBoth` eliminations but no introduction. R2 built the
introduction, so those three reductions are gone. (Their traces pay one extra τ per
collision: `par-pVis` fires a both-offer non-sync event into an inline internal choice
rather than picking a side.)

S1's and S5's reductions have a different cause and the lemma is irrelevant to both. The
defect lives on the **wire branch**, so the violating trace must contain `apiLP` events —
`lnpSendRequestNext`, `lnpRecvBlockOffer`, `lfpSendBlockRequest`, `lfpRecvBlock` — and every
`apiLP` channel is inside **`apiES`**. Inside `nodeP` each of those four events would have
to be driven through the twelve-peer bundle's `⦀⋆` together with the LeiosFetch consumer's
own wire state machine (`BodyOriginBad.agda:26-38`). That is an `apiES`-structural cost,
not a collision; `par-brBoth` addresses collisions. Hence `bodySound-logic-good`
(`BodyOriginBad.agda:403`) survives as a genuine compensator at the identical reduced
composite.

S5's control is the same story at a different channel quadruple —
`lnpSendRequestNext`, `lnpRecvBlockTxsOffer`, `lfpSendBlockTxsRequest`, `lfpRecvBlockTxs`
(`TxOriginBad.agda:29-39`) — with one extra wrinkle: its composite keeps `forgeL` as well
as the broken client, because `fetchTxs` blocks at its leading body read, so the body has
to be forged rather than seeded (§B). Its compensators are `txSound-logic-good` and
`good-refuses`.

A trace of the logic need not survive the bundle — `∥⇘ apiES ⇙` only restricts — so neither
control by itself refutes the node-level statement for the broken logic. What each refutes
is the load-bearing half: `bodySound n` is `soundOf n _ (wf-logic n) _` and `txSound n` is
the same shape, the bundle contributing only the vacuous `wf-linkBundlesP`.

---

## D. The directory

39 modules, 18,481 lines, not counting the no-livelock work of section F
(`LeiosInstance2.agda`, `LeiosInstance3.agda` and `NoLivelock/`, 31 modules, 11,959 lines).

### The model

| Module | Lines | Purpose |
|---|--:|---|
| `LeiosParams.agda` | 93 | The Leios parameter record over a `Params`: the vote-blob algebra (a vote names the **ranking block** it endorses), the certification oracle `certifies` and its `CertifiesMono` law, the two EB projections `ebTxs`/`ebSize`, and `rbCert`. No validation oracle — the prototype's votes carry no verdict. |
| `NodeLogicL.agda` | 788 | **The Linear-Leios node logic.** An additive layer over `Parametric.NodeLogic`, which is untouched. `nodeLogicL` (`:783`) is **five** node-level threads (`forgeL`, `ebIndex`, `voter`, `submit`, `certSink`) in parallel with each endpoint's ten, synchronised on `storeES` with five stores (block, EB-entry, body, mempool, vote). The certificate-RB forge is part of `forgeL` since `76bb8ec2`; `envForgeCert` and the sixth thread are gone, and `storeStepL` (`:311-316`) has **four** branches. All three mempool deposit routes now carry a wire check: `fetchBody` against the point it asked for, `putChecked` against the offset hash, and — since `0c2d3e63` — `putAllTx` (`:713-717`) against the `ids` of its own round. |
| `PeersP.agda` | 170 | The **prototype** peer bundle `nodeBundleP`, over `LeiosNotifyP`/`LeiosFetchP` (`apiLP`). Additive: `NetworkPar` and `Node.agda` are untouched; a node runs one bundle or another via `Node.nodeWith`. |
| `PeersR.agda` | 85 | The earlier **request-reporting** bundle `nodeBundleR`, which swaps in the reporting LeiosFetch/TxSubmission servers of the *old* CIP-draft peers. Superseded: it now carries zero `Wf` facts and one consumer, `PeersRSanity`. |
| `LeiosInstanceL.agda` | 176 | The concrete three-node Linear-Leios line over its own `Params` (`leiosLParams`, `:94`; `leiosLP`, `:130`; `leiosLLine`, `:156`), and the system `leiosSystemL` (`:174`) — the prototype bundle over `NetworkLinkBreakableA`. |
| `LeiosInstanceDozen.agda` | 234 | The 12-node, 45-link **dozen devnet** (BP1–3 each with 3 own relays, relays in a K9 mesh) as the family member `pL 45 12`/`lpF 45 12`: `dozenTopo` (`:124`) by `mkTopology` with `irr`/`cover` decided, `refl` degree checks, `dozenSystem` (`:168`), and S0–S5 premise-free at it (section A0). `voterOf = id` over-approximates (relays do not vote); no no-livelock. |

### The proof framework

| Module | Lines | Purpose |
|---|--:|---|
| `OriginSafe.agda` | 771 | The **generic origin/soundness carrier**, written once for all six origin disciplines: `Minted`, `originOffer`, the specification `OriginSpecT` (`:231`) and `OriginSpec` (`:238`), the coinductive record `OSafe` (`:253`), the leaf predicate `FreeAt`, the `∥⇘⇙`/`⦀` closure lemmas, and the bridge `osafe→⊑T` (`:751`). |
| `OriginLeaves.agda` | 333 | The **discipline-independent leaves**: the part of an origin proof that depends only on the gated channel being a `store` channel, plus the nine prototype-bundle `Wf` facts (`RLNP`, `RLFP`, `ooLNP`, `ooLFP`, `wf-clientPeerP`, `wf-serverPeerP`, `wf-slotP`, `wf-nodeBundleP`, `wf-linkBundlesP`) hoisted out of `VoteSound`. |
| `AnnounceStoreL.agda` | 389 | **The store half of S0**, in the announce discipline (`Parametric.BlockProvenance`'s `Carries`/`WellAnnounced`): `wf-blockStoreL` under the content-bearing `All (WellAnnounced ms) held`, the four other stores vacuously, and `wf-storesL` for the group, all on `BlockProvenanceNode`'s existing `storeG`. `storeStepL`'s UNGATED `putEv` is discharged from the rely, not assumed as a premise. |
| `AnnounceStoreLBad.agda` | 231 | **S0's store control**: with `acceptForgeL`'s withholding arm removed, the store fact fails (`¬wf-blockStoreLBad`, `:221`). The forge gate is load-bearing. |
| `AnnounceReachLBad.agda` | 455 | **S0's reachability control**: with the forge route's *announcement* check removed, the gated event really fires (`ann-gate-reachable`, `:444`). Level 2 of the acceptance ladder — one node, broken logic, a `traces` witness. |
| `AnnounceThreadsL.agda` | 616 | **The thread half of S0**, all fifteen thread families on `threadsGL` (= `threadsG` minus the read-pointer rely `store … (stGetAt k)`, which five of them read a held block through), plus the node-level join `wf-nodeLogicL : Wf nodeG …` and `annIn-threadsGL`/`annIn-nodeG`, so `wf→gate` applies on BOTH announce channels. Three threads are content-bearing: `forgeL` (the only depositor), `serverLoopL` and the announce leaf `lnServerLoopL`. |
| `AnnounceSystemL.agda` | 466 | **S0, AT THE SYSTEM LEVEL** (section A0): the prototype peer bundle on the shrunk `peersPG` (`:165`), the three `Sep` conditions, `Covers`/`HideCov`, the node, the `⦀Fin⁺` fold against the copy medium, `noTick`, and the transport to the concrete multiplexer. `annSafeLT` (`:428`) ∀-`Params` under `LinkCfgWf`; `leiosAnnSafeLT` (`:462`) premise-free at the shipped line. |

### The system assemblies (section A0)

Six of a kind plus S0's. Each is the same five-step assembly — `wf-med`, `wf-nodeC`,
`wf-system`, then `osafe→⊑T (wf→osafe wf-system (noRet-system …))` — over the discipline's
own re-keyed leaves, and each ends with the shipped premise-free line against
`leiosSystemL`.

| Module | Lines | Theorem | shipped line |
|---|--:|---|---|
| `BodySystemL.agda` | 272 | S1 `bodySoundLT` (`:246`) | `leiosBodySoundLT` (`:270`) |
| `VoteSystemL.agda` | 281 | S2 `voteSoundLT` (`:254`) | `leiosVoteSoundLT` (`:279`) |
| `BlobSystemL.agda` | 278 | S2′ `blobSoundLT` (`:249`) | `leiosBlobSoundLT` (`:276`) |
| `CertSystemL.agda` | 317 | S3 `certSoundLT` (`:263`) — **the pilot**; its header records what the other four inherit | `leiosCertSoundLT` (`:286`) |
| `CertRbSystemL.agda` | 288 | S4 `certRbSoundLT` (`:261`) | `leiosCertRbSoundLT` (`:286`) |
| `TxSystemL.agda` | 286 | S5 `txSoundLT` (`:260`) — reuses `BodySystemL`'s `sep-io`/`hideCov-full`/`med-noNeed`/`wf-med`/`noRet-system` verbatim | `leiosTxSoundLT` (`:284`) |

Why these are so much smaller than `AnnounceSystemL`: every origin discipline confines
`Carries` to a single `store` channel, so every alphabet is `OriginLeaves.fullα`, every
`Sep` is a two-liner, `HideCov ioES fullα` is `λ _ _ → tt` with no `Covers` enumeration,
and the medium is a six-line vacuity instead of a copy→concrete transport — which is also
why none of the six carries `LinkCfgWf`. The one per-instance cost is `hideKeep-io`'s
nineteen clauses, whose type mentions the discipline's `mints` — now owed by a **seventh**
consumer (`TxSystemL.agda:52-63`), which records why the hoist is still not taken.

**The route, and why `OSafe` alone cannot take it.** `OSafe` has no structural closure over
`Prefix`/`Output`/`_>>=_`/`loop`, and its `noTick` field is *refutable* of a peer bundle
— peers terminate on `done` (`VoteSound.agda:72-73`). Both problems were already solved by
the assume-guarantee framework one directory up: `Parametric.BlockProvenance.Carrier` and
its returning-tree layer `Parametric.BlockProvenanceWfR.Body` carry no `noTick` obligation
and come with `wfR-Prefix`, `wfR-Output`, `wfR-□`, `wfR->>=`, `wf-loop` and `wf-loop0`.
Each discipline is an instance of them; `wf→osafe` (e.g. `VoteSound.agda:655-661`) is the one
bridge back into `OriginSafe`, and `osafe→⊑T` finishes.

**The `OSafe` congruence family is consequently UNUSED, and that includes the system lift.**
`osafe-Par`/`osafe-ParL`/`osafe-ParR`/`osafe-both`/`osafe-⦀`/`osafe-⦀Fin⁺`/`osafe-Hide`/
`osafe-ParS`/`osafe-ParS′` and the whole `OSafe∖` layer (`OriginSafe.agda:330-655`) have
**no consumer in this directory**; the only names the disciplines import are `OSafe` itself,
its three fields and `osafe→⊑T` (e.g. `VoteSound.agda:535`). They could not have served the
network lift in any case: `OSafe`'s `noTick` is **unconditional**, and the peer bundle can
tick — peers terminate on `done`. The `Wf`/`Carries` framework carries the whole fold, with
`wf→osafe` applied exactly **once, at the top**, where `noTick` is supplied by
`noRet-system` over the per-node `noRet-logic`.

### The theorems and their controls

| Module | Lines | |
|---|--:|---|
| `BodyOrigin.agda` | 972 | S1 `bodySound` |
| `BodyOriginBad.agda` | 407 | S1's control (reduced composite) + `bodySound-logic-good` |
| `VoteSound.agda` | 1080 | S2 `voteSound` |
| `VoteSoundBad.agda` | 390 | S2's control + `voteSound-node-good` |
| `BlobOrigin.agda` | 773 | S2′ `blobSound` |
| `BlobOriginBad.agda` | 447 | S2′'s control + `blobSound-node-good` |
| `CertSound.agda` | 828 | S3 `certSound` (premised) and `certSoundL` (discharged at the shipped oracle) |
| `CertSoundBad.agda` | 528 | S3's control, the two-voter oracle `certifies₂`, + `certSound-node-good` |
| `CertRbOrigin.agda` | 841 | S4 `certRbSound` |
| `CertRbOriginBad.agda` | 399 | S4's control + `certRbSound-node-good` (= the positive) |
| `TxOrigin.agda` | 1046 | S5 `txSound` |
| `TxOriginBad.agda` | 576 | S5's control (reduced composite) + `txSound-logic-good` + the derived `good-refuses` |

### Probes and negative facts

| Module | Lines | Purpose |
|---|--:|---|
| `NodeLogicLSanity.agda` | 212 | Six probes at three levels (see section C). Imported by nobody. |
| `DedupGateSanity.agda` | 113 | The two 2026-10-02 regression pins, `viewV` facts at `leiosLParams`: `dedup-held`/`fresh-prepends` (the RB store's `putEv` arm keeps a held block and prepends a fresh one) and `gate-waits`/`empty-mempool-withholds` (`bodyOfferBody` waits for the closure before `lnpSendBlockTxsOffer`, then sends it). Store- and thread-local, not composite facts. Imported by nobody. |
| `PeersPSanity.agda` | 73 | `lfpP-reports-request` (`:68`) — a `refl` typechecking probe that the prototype LeiosFetch server reports the request to the application. |
| `PeersRSanity.agda` | 43 | The line system over `nodeBundleR`; the only remaining consumer of `PeersR`. |
| `Negative/Chatter.agda` | 189 | `chatter-diverges` (`:179`) — the unchanged relay chatters. Design law L's justification. |
| `Negative/FetchWedge.agda` | 247 | `wedge-reachable` (`:147`) / `wedge-stuck` (`:238`) — the pointer-driven fetch wedge (spec correction C2). |

### The LeiosNotify peer pair: graceful shutdown (ouroboros-consensus PR 2344)

| Module | Lines | Purpose |
|---|--:|---|
| `LeiosNotifyQuit.agda` | 1898 | The ported `LeiosNotifyP` client (at `(l , lo)`) and server (at `(l , hi)`) — the real step functions, not a copy. The peers follow the cardano-blueprint table literally (no pipelining, no lookahead), so they are composed DIRECTLY: the server is renamed (`srv`: its receive becomes the client end's send and vice versa) and the pair synchronises on the wire (`sys`), api/done left open. Each component is abstracted by a small LTS (`Abs`/`AbsI`, closed under `Par⊤` by `Prod`); a 9-phase invariant `J` is inductive. (T) `LNPSpec` is the table as one process over the protocol messages; `sys-conforms` (every trace of the pair, api/done projected away by `wire`, is a trace of `LNPSpec`, termination included), and per peer `client-conforms` / `server-conforms`. (a) `sys-deadlockFree`, `sys-divergenceFree`. (b) with every server api send blocked, incl. the new `lnpSendCanceled` (`blk`): `blk-afterQuit` (after the client's `lnpSendDone`: deadlock-free, divergence-free, at most 3 more visible events, so every run ends in √). (c) the non-pipelined stall: `blk-stall` / `blk-deadlock` (after RequestNext the blocked pair is stuck; the client, in StBusy, cannot quit), and `blkC-cancelThenQuit` (with only the cancel allowed, MsgCanceled, the quit and MsgDone reach √). (d) the old pre-PR-2344 negative control is removed (without pipelining both protocols stall identically; the only difference is MsgCanceled, i.e. (c)). Pair level, not system level. Imported by `LeiosNotifyQuitFD` and `LeiosNotifyQuitCancel`. |
| `LeiosNotifyQuitFD.agda` | 1383 | Companion of `LeiosNotifyQuit` (imports it; same real peers, `srv`, `sys`, `Abs`/`Prod`). The blueprint table as data (`row`, `:155`) and as a process `Tbl` (`:281`) generic in who holds agency: an internal state is an `ExtI`-indexed τ-menu over EVERY row payload, an external one a menu accepting every row payload. (R) RECEPTIVENESS against the most general table partners, wire synchronised, api/done open: `ServerEnv` (`:662`; server states internal — any reply / MsgCanceled / MsgDone with any payload) and `ClientEnv` (`:668`); `client-receptive : DeadlockFree (client ∥ ServerEnv)` (`:823`), `server-receptive : DeadlockFree (srv ∥ ClientEnv)` (`:941`), plus `client-receptive-divFree` / `server-receptive-divFree`. The partner commits by a τ to ONE message where the peer has no agency and no api move, so deadlock freedom = the peer accepts every table-permitted message (e.g. the client accepts MsgCanceled in StBusy). Negative control: `badClient` (`:672`, the table client without the row StBusy --MsgCanceled--> StIdle, i.e. upstream's throw) gives `bad-deadlock : HasDeadlock (badClient ∥ ServerEnv)` (`:984`). (FD) `sysH = sys ∖ apiDoneES` (`:1003`, all api / done hidden) and `LNPSpec⊓` (`:1024`, every agency choice internal, wire only): `sysH≈DR : sysH ≈DR LNPSpec⊓` (`:1369`), hence `LNPSpec⊓-⊑FD` (`:1378`) and `LNPSpec⊓-≈FD` (`:1382`), and `sysH-divergenceFree` (`:1111`, hiding adds no divergence). Restriction: `LNPSpec⊓` sends the chosen message content on the peers' fixed envelope (`time₀` / sender mode / `length₀`), as the model's peers never vary it; `⊑FD` uses csp-ptree's `DRImpliesFD` (its classical axiom `¬-divergent→normal`). Pair level. Imported by nobody. |
| `LeiosNotifyQuitCancel.agda` | 611 | Companion of `LeiosNotifyQuit` (imports it; reuses `sys`, `blkC`, `blk-stall`, the abstractions, the invariant `J` via `Walk`, `cτ?` / `sτ?`). "The client wants out": `stop W = W [| noRN |] Skip` (`:97`) refuses the client's `lnpSendRequestNext` api trigger from an ARBITRARY reachable state `W` on. A rank on `J` (`rk`, `:127`) is a variant (`kstep`, `:231`); progress uses the quit at StIdle and the cancel at StBusy (`kprog`, `:271`); a generic `Stop` module (`:285`) packages the results over any policy-restricted system. (N) no load (`blkC`, notifications refused, cancel open): `cancel-quitCompletes` (`:428`) — for every `blkC`-reachable `W`, `stop W` is deadlock-free, divergence-free and every √-free trace has at most 7 visible events (worst case: RequestNext commanded but unsent, then MsgRequestNext, cancel api, MsgCanceled, `lnpSendDone`, MsgQuit, done, MsgDone); `cancel-√reachable` (`:437`, √ reachable from every reachable state, constructive); `cancel-tight` (`:486`, 7 attained). (L) load (`sys`, all server api sends open): `load-quitCompletes` (`:527`, bound 8: one notification still delivered), `load-√reachable` (`:534`), `load-tight` (`:571`, 8 attained with an empty vote list). Uniform bounds, no fairness: infinite payload branching, bounded depth. (X) contrast: `stuckStop` (`:592`, `stop` never unsticks) and `blk-stall-stop` (`:609`, with the cancel also refused the busy client stays stuck). DeadlockFree is relative to the environment offering the open api / done events. Pair level. Imported by nobody. |
| `LeiosNotifyQuitLive.agda` | 826 | Companion of `LeiosNotifyQuit` / `LeiosNotifyQuitCancel` (imports both; reuses `sys`, `blk`, `noStepX`, `Prod`, `Walk`, the rank `rk` and its variant `kstep`). Fairness-conditional quit liveness in csp-ptree's LTL library: runs are the library's maximal weak runs `Trace` (`Semantics.LTL.Traces_Based`), the goal `◇ᵗ (atom Ended)` (`:149`, a √ step or a returned leaf). Environment: the applications may WITHHOLD commands (client `lnpSendRequestNext` / `lnpSendDone`, server's five `lnpSend*`; never wire, deliveries or done) — `envP X = sys [| X |] Skip` (`:221`) for any `CmdOnly X` (`:217`). Assumptions: (F1) `F1` (`:235`, ◇□ ¬RequestNext, library `□ᵗ`/`Fires`); (F2)/(F3) `PFair X QuitC` / `PFair X SrvSend` (`:230`) — the library's weak fairness `Fair` with enabledness read in the PAIR (`PEn`, `:225`) instead of after the environment's refusal (the library's own `Fair` is vacuous against a withholding environment). MAIN `quit-live` (`:438`): every run of `envP X` satisfying F1, F2, F3 reaches √ — via a generic descent `Live` (`:281`): after F1's point the rank (≤ 8) drops at every visible step, `div` is impossible, a `stuck` leaf is the pair idle (F2 violated) or busy (F3 violated). `quit-live-sys` (`:360`): every run of `sys` itself (closed world) with F1 alone reaches √. Necessity, each a concrete run never reaching √: `nf3` (`:580`; `blk`'s stall run `stall`, F1 ∧ F2 ∧ ¬F3), `nf2` (`:639`; client commands withheld, stuck at start, F1 ∧ F3 ∧ ¬F2), `nf1` (`:822`; always-willing environment, the infinite request/cancel loop `lp1`, F2 ∧ F3 ∧ ¬F1). Constructive (no `Classical`); the imported `Traces_Based` carries two unused postulates. Pair level. Imported by nobody. |
| `LeiosNotifyQuitTerm.agda` | 432 | Companion of `LeiosNotifyQuit` (imports it; reuses `sys`, `sys₀`, `SysA`/`SysI`, `Gen.runE`, `Walk.walk`, `J`, `wire`). CLEAN TERMINATION of the pair, each a statement about every √-free trace of `sys`. Helpers: `msgOf` / `CarriesW m e` (`:77`, `e` a wire event carrying message `m`) and `occ m` (`:88`, occurrences). (2a) `done-last` (`:263`): if `s₁ ++ e ∷ s₂` is a trace and `e` carries MsgDone, then `s₂ ≡ []` (no event at all follows, wire or api/done) and the reached state has returned (√). (2b) `quit-irrevocable` (`:271`): if `e` carries MsgQuit, `s₂` is a prefix of [the server's `doneLNP l hi` , MsgDone]; corollary `quit-only-done` (`:289`): every wire event of `s₂` carries MsgDone (no RequestNext, notification, MsgCanceled or second MsgQuit). (2c) `joint-termination` (`:325`): every reachable state is `Par⊤ wire C S` with `C` returned iff `S` returned, and a returned state has both returned; phase core `jEndC` / `jEndS` (`:298`, `:310`: in every `J` phase, client at End iff server at End). (2d) `handshake-only` (`:425`): if the state after `s` has returned, `wire s ≡ w₀ ++ [MsgQuit , MsgDone]` with the peers' exact events and `w₀` free of both, so `occ MsgLNPQuit (wire s) ≡ 1` and `occ MsgLNPDone (wire s) ≡ 1`. Proved on the abstract run, not via `sys-conforms`: `LNPSpec` accepts every envelope and `wire` erases the server's done, so table-level reasoning gives strictly weaker forms. Steps carrying MsgQuit / MsgDone are the rendezvous `cSQ`/`sQi`, `cDn`/`sDS` (`quitStep`, `doneStep`); post-quit phases `PostQ` owe an exact remaining trace (`postQ`); (2d) transfers an owed projection backwards (`oweStep`). Constructive (no `Classical`). Pair level. Imported by nobody. |
| `LeiosNotifyQuitNet.agda` | 1172 | The LeiosNotify pair over the REAL medium (imports `LeiosNotifyQuit` for the client abstraction `CPos`/`CStp`, `PeerLNP`'s server views, `PeersP`'s rename, `MediumEquivA.nr-Copy`, `NetworkDeadlockFree`'s copy-cell probes). `netPair` (`:371`): the real client and server renamed exactly as `PeersP` (both named `(l , lo)`, as `Node.bundleAtWith` places them), interleaved, synchronised on `ioES` (io left visible) with the breakable copy cell `renameMap (Copy l lo N2N_LeiosNotify) △ (break l ⟶₀ Skip)` (justified by `MediumEquivA.breakablePerLink`; for an LN-only link its hypotheses hold trivially). Findings in the header: one cell carries BOTH directions of an instance (demultiplexed by payload); `break` is per link, permanent and unannounced to the peers; the cell never returns. Invariants: `Live` (medium live, peers at known phases `QSt`) / `Broken` (medium returned). (i) `noIoAfterBreak` (`:885`) / `noIoAfterBreak-tr` (`:891`): after a `break l` no `input`/`output` event (any link, any id) occurs. (ii) `earlyBreak-no√` (`:907`): a `break l` in a reachable state with the peers not finished (`¬ PeersDone`) makes √ unreachable — a break during LeiosNotify forfeits graceful shutdown. (iii) `no√WithoutBreak` (`:924`): every √ has `break l` in its trace (the cell never returns, so a complete handshake WITHOUT a break ends stuck, not in √); `graceful√` (`:1130`): a concrete run RequestNext, MsgCanceled, quit, done, MsgDone, then `break l`, reaching √. The bound on api/done events after an early break is not proved. Constructive (no `Classical`). Pair level over one link. Imported by nobody. |
| `LeiosNotifyIsolation.agda` | 504 | "LeiosNotify terminating does not affect the other mini-protocols", at the level of the node's PEER BUNDLE (∀ `Params`, ∀ link, ∀ configuration). Generic over any interleaved bundle `⦀⋆ Ps`: (A) `bundle-elim` / `bundle-intro` (`:215`, `:236`) — a √-free run is exactly one run per component merged by csp-ptree's `ILv`, the reached state τ-resolving to the bundle of the ends (`BundleRun`, the right-nested counterpart of `InterleaveNest.Nest-reach-elim/intro`); (B) `⦀⋆-drop∼` (`:265`) — a `Returned` component deletes up to STRONG bisimulation (`Skip` unit of `⦀`, `cong-Par-∼`); (C) MAIN `drop-terminated` (`:325`, record `Dropped`) — along any √-free run, once component i has returned: the run's trace splits as i's own trace interleaved with s′ (`ILv-del`), the bundle WITHOUT i reaches a state V along s′ by itself, and the reached state is `∼` V (`drop-terminated-DR`: `≈DR`). (D) `lnGone` (`:392`): (C) at `nodeBundleP` (`nodeBundleP-slots`, by `refl`) for the slot of any configured `(d , N2N_LeiosNotify)`, identified as `LNPclientA` / `LNPserverA` (`slot-client`, `slot-server`), the LN-free bundle being the builder over the configuration minus that instance (`del-slots`). (E) non-vacuity `lnClientEnds` (`:488`): on every link configured with LeiosNotify on `lo`, the bundle runs the quit handshake (`quitTr`: quit command, MsgQuit, MsgDone; every other peer idle) to a state whose de-interleaving has the LN client returned. Findings recorded in the header, not theorems: in the SHIPPED system LN never terminates (`apiES` syncs `apiLP` and `done`; `NodeLogicL` never offers `lnpSendDone`, `NodeLogic` no `done`; the cell never returns), so system-level non-interference is vacuous; `NodeLogicL`'s threads are interleaved and stores hold no locks, but the ONE Notify client thread also drives the LeiosFetch client (`fetchBody` / `fetchTxs`), so with LN gone that endpoint's LF client is never driven again. No alphabet-disjointness facts (the bundle is an interleaving, so none are needed). Constructive; `ParallelUnit`'s import puts `DRImpliesFD`'s postulate in the closure, unused (no `≈FD` stated). Bundle level. Imported by nobody. |
| `LeiosNotifyPipelined.agda` | 233 | The PR 2344 PIPELINED pair as a model (no new tag / message; `LeiosNotifyP` untouched). Depth 1: both peers loop over `LNPState` and REUSE `clientStepP` / `serverStepP` verbatim, plus exactly one extra transition each in StBusy — the client's PIPELINED QUIT (`pipeQuit`, `:111`: `lnpSendDone` → MsgQuit → `drainP`, `:105`, which accepts the owed reply / MsgCanceled WITHOUT delivery, then awaits MsgDone) and the server's READ-AHEAD (`readAhead`, `:138`: MsgQuit read while a request is held → MsgCanceled → StQuit); cancel keeps table semantics (`lnpSendCanceled` any time). `pcStep` (`:122`) / `LNPpipeClient` (`:129`), `psStep` (`:149`) / `LNPreadAheadServer` (`:156`). Channels: two one-way capacity-2 FIFOs `fifo l i o` (`:216`; a FIFO closes after its direction's last message, MsgQuit / MsgDone, so a completed shutdown is √), `psys` (`:232`) = (client(l,lo) ⦀ server(l,hi)) [| wire |] (fifo l lo hi ⦀ fifo l hi lo), api/done open, no renaming. Header records the mapping to PR 2344 and the MODELLING GAP: the real per-instance medium is ONE one-place cell shared by both directions (`LeiosNotifyQuitNet` header) and cannot carry crossing pipelined traffic — pipelining needs per-direction buffering, so `psys` is a pair-level model over idealised channels, not over `NetworkLink`. Imported by `LeiosNotifyPipelinedProps`. |
| `LeiosNotifyPipelinedProps.agda` | 2275 | Properties of `psys` and of `pblk` (`:969`, all FIVE server api sends refused, as `LeiosNotifyQuit.blk`), ∀ `Params`, ∀ link. Reuses `LeiosNotifyQuit`'s `Abs`/`AbsI`/`Gen`/`Prod`/`SkA`, `LNPSpec` and its row lemmas, and `PeerLNP`'s views of the reused rounds; one generic FIFO abstraction (`Fifo`, `:762`); a 25-phase invariant `J` (`:1006`, step lemma `J-ev`, `:1240`) with side facts for the quit region, a rank, and protocol-order bookkeeping (`Ans`, `:158`: RN ↦ a reply, Quit ↦ MsgDone). (P1) `psys-protocolOrder` (`:1715`): for every √-free trace, `alt (cm s) (sm s)` (`:1637`; client / server messages in send order, interleaved c₁ s₁ c₂ s₂ …, then only the FIRST unanswered client message) is a trace of `LNPSpec`, termination included, and `length (sm s) ≤ length (cm s)` (causality); structure `psys-pairing` (`:1619`, `Pair`, `:1610`: `cm s ≡ cs₀ ++ pend`, pend ∈ {[], [RN], [Quit], [RN,Quit]}, `cs₀` paired with `sm s`). Deviation: the full tail "… RN Quit" (pipelined, RN unanswered) is NOT a table trace, so `alt` truncates and `Pair` records the rest. (P2) `pblk-afterQuit` (`:1570`): after `lnpSendDone` (incl. pipelined), deadlock-free, divergence-free, at most 8 visible events; `pblk-tight` (`:2207`, 8 attained). (P3) `psys-quitShape` (`:1883`): MsgQuit sent with k = \|cm s₁\| ∸ \|sm s₁\| outstanding ⇒ k ≤ 1, no client message after it, server messages after it a prefix of k replies then MsgDone (`QuitTail`, `:1743`); `psys-attribution` (`:2045`: notifications sent ≤ notification commands), `pblk-noNotification` (`:2051`), `pblk-quitShape` (`:2083`, `QuitTailC`: with the application silent the outstanding request gets MsgCanceled). (P4) `psys-deadlockFree` (`:1547`), `psys-divergenceFree` (`:1551`). (P5) `pblk-deadlockFree` (`:1559`), `stall-vs-pipelined` (`:2274`: `HasDeadlock (blk l) × DeadlockFree pblk`), `pblk-quitAfterRN` (`:2155`: RequestNext received by the server — `blk-stall`'s situation — then pipelined quit, read-ahead MsgCanceled, MsgDone, √). `psys-noBlock` (`:2260`): capacity 2 suffices, a sender always finds room. Constructive (no `Classical`, no postulate). Pair level. Imported by nobody. |

---

## E. Provenance and reproduction

* Branch `examples/leios_prototype_protocols`. S0's network lift landed at **`2bf2813a`**;
  the next five at **`5296124c`** (S3, the pilot), **`61bea75d`** (S2′), **`3c9efa1f`**
  (S1), **`8664a426`** (S4) and **`ec5174ba`** (S2). S5 landed last, in four commits:
  **`0c2d3e63`** (the `putAllTx` guard — a model change, see §A0), **`1b5f718f`**
  (`TxOrigin`, the node level), **`1e29b189`** (`TxSystemL`, the network lift) and
  **`8c6070ce`** (`TxOriginBad`, the control).
* Zero postulates, zero holes, no `NON_TERMINATING` in any module of this directory.
* All ten node-level theorem and control endpoints **that existed then** were typechecked
  **cold** (each
  module's own `.agdai` removed first, one agda at a time, each run carrying its own
  literal `Checking …` line) at `d71e63a5`: **10/10 EXIT 0, zero warnings, 20-21 s each**.
  Logs are in the git-ignored ledger at
  `.superpowers/sdd/2026-09-21-leios-prototype-protocols/logs/r2-final-*.log`.
* The S0 chain — `AnnounceStoreL`, `AnnounceStoreLBad`, `AnnounceThreadsL`,
  `AnnounceSystemL`, plus `AnnounceSafeCopy`/`AnnounceSafeConcrete`/
  `AnnounceSafeInstances`/`BlockProvenancePeers` and all sixteen Leios endpoints — was
  re-checked cold the same way at `2bf2813a`: **24/24 EXIT 0, zero warnings.** The shipped
  `AnnounceSafeConcrete.announceSafeT` is textually unchanged.
* The four-node estate below `Net` is covered transitively and was genuinely rebuilt in
  the same round (`logs/r2-sweep3.log`, EXIT 0, 105 modules, 43 m 49 s).
* **The six system endpoints at this tip (`ec5174ba`).** `AnnounceSystemL`, `BodySystemL`,
  `VoteSystemL`, `BlobSystemL`, `CertSystemL` and `CertRbSystemL` were re-checked on
  2026-10-01 with **each endpoint's own `.agdai` removed first**, one agda at a time, each
  run carrying its own literal `Checking …` line: **6/6, zero warnings, 19.6–21.6 s each**
  (warm below the endpoint; Agda writes an interface only on success, and all six
  interfaces were rewritten). The five S1–S4 system modules postdate the `d71e63a5` and
  `2bf2813a` cold rounds above, so **no full cold-cache log exists for them** and none is
  claimed here; their closures are the same as the node-level endpoints' plus the five
  assemblies.
* **The three S5 modules postdate every round above.** `TxOrigin`, `TxSystemL` and
  `TxOriginBad` were green at the commits that landed them (`1b5f718f`, `1e29b189`,
  `8c6070ce`), and `0c2d3e63` — the only `.agda` change to the pre-existing estate — was
  swept green when it landed; the three leaves over `putAllTx` that it touched
  (`BodyOrigin.oo-putAllTx`, `VoteSound.oo-putAllTx`, `AnnounceThreadsL.wfR-putAllTx`) are
  inside the S1/S2/S0 closures and so are covered by those endpoints. **No cold-cache log
  exists for any of the three S5 modules and none is claimed**, and this documentation pass
  ran no typecheck at all — it changed no `.agda` file.

To re-check one endpoint:

```sh
cd src/Network_CSP_Model
rm -f _build/2.8.0/agda/Cardano_network/Parametric/Leios/<Module>.agdai
systemd-run --user --scope -p MemoryMax=25G -p MemorySwapMax=0 \
  -- stdbuf -oL agda Cardano_network/Parametric/Leios/<Module>.agda \
     +RTS -M20G -RTS
```

Four things about that command, each of them measured:

* **`-M` must sit BELOW `MemoryMax`.** `-M` caps the *heap*; RSS is heap plus copy-space
  plus fragmentation, so equal values give GHC's collector no headroom and the cgroup kills
  the process while GHC still believes it is within its limit — a bare `EXIT 137` with no
  GHC message. Do **not** add an explicit `-c`: `-M` already switches the oldest generation
  to compacting above ~30 % of the cap, and forcing always-compact cost roughly 4×
  throughput here.
* **Remove the endpoint's own `.agdai` first.** Otherwise a run can exit 0 without ever
  visiting the endpoint.
* **Only one agda at a time.** A cold rebuild leaves very little system headroom.
* A cold four-node estate rebuild costs **~45 minutes** and peaks at **22.17 GB**. Once
  warm, each Leios endpoint is 20-25 s.

`Parametric/Spike/HideDiverge.agda` (three `?` holes),
`Cardano_network/EvBothProbe.agda` (a stale `numConns` literal — note the path: it sits
beside `Parametric/`, not inside it, and an earlier revision of this file said
`Parametric/EvBothProbe.agda`, which does not exist) and the
`NetworkVerification/Liveness/PipePair*` chain are RED, all three pre-existing and
predating this work, and none is in any endpoint's closure here.

---

## F. No livelock (the two-node instance, then the shipped three-node line)

**The theorem.** `NoLivelock/Bound2.noLivelock2 : ∀ s → ¬ divergences (rawSys2 ∖ H2) s`
(`NoLivelock/Bound2.agda:214`): with every channel but `env` and `break` hidden, no trace of
the two-node system reaches a state that can run hidden events forever. No module
parameters, no hypotheses. It is spec §3.2 exactly
(`docs/superpowers/specs/2026-10-03-leios-no-livelock-design.md`).

**The instance** (`LeiosInstance2.agda`). `p2 = pL 1 2` (`:28-29`) is `leiosLParams` with
ONE link and `VoterId = Fin 2` — since Stage L, a member of the instance family
`LeiosInstanceP.pL` (see the Stage-L subsection below); `lp2 = lpF 1 2` (`:32-33`) is
`leiosLP` carried over; `line2` (`:44-45`) joins node 0 (the `lo` end of link 0) to node 1
(the `hi` end). The system is the UNHIDDEN composite
`rawSys2 = NetworkLinkA ∥⇘ ioES ⇙ ⦀Fin⁺ 1 node2` (`:58-59`) over the concrete, non-breakable
multiplexer, each node being `nodeWith nodeBundleP n (nodeLogicL n st₀)` (`:54-55`).

**`H2 = HP 1 2`** (`:62-63`) is every channel except `env` and `break`: all api, store and
wire channels. Its decision `hSet-dec` (`LeiosInstanceP.agda:98-117`) has one clause per
channel; `env` and `break` are the only `no`s, and `break` never occurs over `NetworkLinkA`.

**`F2`.** `F2 m = c2 * m + c2₀` with **`c2 = 92640`** and **`c2₀ = 208104`**
(`NoLivelock/Bound2.agda:66-75`), and `bound2 : ∀ {s Q} → rawSys2 ⟹⟨ s ⟩ Q → #H H2 s ≤ F2
(#V H2 s)` (`:208`): on every trace the hidden events are at most linear in the visible
(`env`) ones. The constants are concrete and crude — the linear system is solved by hand in
`fin` (`:93`) — and are not claimed tight. Their size is proof-by-summation: synchronised
labels are counted on both sides at each sync layer — `nodeF′` (`NoLivelock/Logic2.agda:886-887`,
moved there from `Bound2` in Stage L) counts api labels in both the bundle and the logic, and
`Logic2.lH` (`:762`, doubling comment at `:800`) doubles the store labels — plus per-group worst-case slack. For
calibration, `live2`'s 25-event trace has 1 visible event and 24 hidden.

**How it is proved.** `noLivelock2 s = noLivelockT H2 F2 bound2 noDiv2` (`NoLivelock/Bound2.agda:215`), the
Stage-G bridge `noLivelockT` (`csp-ptree-agda/src/CSP/Laws/FD/NoLivelock.agda:243`).

* *Premise (b), no reachable state diverges:* `noDiv2` (`NoLivelock/Tau2.agda:59`), from
  `rawSys2-τ-AccReach` (`:55`) by the Stage-G accessibility calculus.
* *Premise (a), the counting bound:* one summary per component — every peer (its relays
  and alphabet facts, `NoLivelock/Peer*`, `PeerAlpha`), every thread (its event count
  against its trigger, `Threads`, `ThreadAlpha`), every store (its read bounds,
  `Stores`, `StoresProv`) and the medium (`MediumRelay`) — each stated over the
  component's OWN trace and composed through projection (`Par-trace-elim`, the `Σc`
  additivity of `csp-ptree-agda/src/CSP/Laws/DivFree/Count`, `CountRename` across the renamings) in
  `Logic2` and `Bound2`.
* *The RB-store bounds come from VALUE PROVENANCE and the store's dedup* (owner decision
  D1-b). `ProvSys.sys-prov` (`NoLivelock/ProvSys.agda:296`): every RB on any chain label of
  a `rawSys2` trace was forged earlier in it by some `envForge`; `sys-inX` (`:300`) turns
  that into the rely of `StoresProv.blockStore-reads-prov`
  (`NoLivelock/StoresProv.agda:338`): every read index is below |X| + the forges, X being
  the blocks forged on the trace. This route does not use the finiteness of `Block`. Since
  Stage L, `sys-prov` and `sys-inX` take the medium's provenance as an argument
  (`PA ChS ChS InM med → …`), so Stage C and Stage L share them.
* *The mempool, vote-store and certificate bounds come from those stores' own dedup over
  FINITE carriers*: `Stores.mempool-reads` (index < 2, `Tx = Bool`,
  `NoLivelock/Stores.agda:446`), `voteStore-reads` (index < `length U`, which is 6 at `U6`;
  `VoteBlob = Fin 2 × Maybe Bool`, `:516`) and `voteStore-certs` (at most 3 certificates,
  `RbHash = Maybe Bool`, `:558`). **These three depend on `p2`'s finite carriers**; an instance with an infinite
  `Tx`, `VoteBlob` or `RbHash` would need a provenance argument like the RB store's.
  The thread counts carry the same dependency through `lp2`'s one-entry body table:
  `Threads.ao≤1` (at most one offset per EB, `NoLivelock/Threads.agda:434-437`), `aw-Dp`
  (the closure gate holds at most one mempool read, `:210-212`), "a closure request
  carries at most one offset" (`:463`) and the depth-5 body offerer
  (`bodyOfferLoop-count`, `:306-308`) all size on that table. `leiosLP` carries the same
  table, so Stage L is unaffected; a generic `Params`/`LeiosParams` version would need
  spec §5's weighting by `1 + |ebTxs h|` instead.

**Postulates.** None. The closure of `noLivelock2` is 92 local modules after Stage L (90 at
Stage C) with 0 postulates and 0 escape pragmas, reaches neither `Parametric/Assembly.agda`
nor `FourNode/`, and uses **neither sanctioned classical seam** (`¬-divergent→normal`,
`modA-transfer`); with the two controls added (`Bound2`, `Live2`, `StoreBad` together) it is
97 local modules after Stage L (94 at Stage C), again with 0 postulates, 0 escape pragmas
and no estate.

**The controls, at their levels.**

* **Non-vacuity — on `rawSys2` itself** (owner decision D3-a).
  `NoLivelock/Live2.live2` (`NoLivelock/Live2.agda:465`) is a 25-event trace of `rawSys2`
  in which node 0 forges the block `nothing`, six medium messages cross the link
  (`MsgCSRequestNext`, `MsgCSAwaitReply`, `MsgCSRollForward`, `MsgRequestRange`,
  `MsgStartBatch`, `MsgBlock`, all on link 0's `hi` cells) — only `MsgCSRollForward` (the
  header) and `MsgBlock` carry the block itself, the other four are protocol messages —
  and node 1 deposits it: one
  forge at node 0, **none at node 1**, and a `stPut` at node 1, so the deposit crossed the
  link. It is built from per-component traces with exact-endpoint versions of the
  trace-intro lemmas (hoisted in Stage L to `csp-ptree-agda/src/CSP/Laws/Traces/TraceIntroExact.agda`);
  no step of a composite is computed.
* **Negative control — STORE LEVEL** (owner decision D2-b). `NoLivelock/StoreBad` takes
  the RB store with the PRE-FIX deposit arm `Ret (b ∷ held)` (`pArm`,
  `NoLivelock/StoreBad.agda:87-88`). Fed only the block `nothing` — so the provenance rely
  `InX (nothing ∷ [])` holds — and never forged into, it serves every read index
  (`storeBad-unbounded`, `:248`), so the bound `blockStore-reads-prov` proves for the real
  store, `j < |X| + forges = 1`, is FALSE for it (`storeBad-refutes`, `:281`). The level
  is the STORE, not `rawSys2`: this deviates from spec §7's system-level wording ("a
  finite trace of the two-node system") **with owner approval**, following the
  `Negative/Chatter.agda` precedent ("LEVEL: the THREAD/STORE PAIR, not `systemOf`"). It
  shows the RB dedup is load-bearing for the store bound the proof uses; it exhibits no
  system-level divergence.

**KeepAlive caveat (argued by code reading, not proved).** KeepAlive is inert in this
model: no thread offers `apiKA`, so neither KeepAlive peer ever moves. An unboundedly
repeating KeepAlive driver would break the bound — and the theorem — unless the KA events
stayed visible (outside `H`).

**What it is NOT.**

* **It is not delivery liveness.** It says no infinite run of hidden events exists; it
  does **not** say that a forged block arrives anywhere, or that any node makes progress.
  No "every forged block arrives" theorem exists on this branch; `live2` shows one
  delivery is *possible*, and is a non-vacuity witness, not a liveness theorem.
* **It is about the two-node instance only.** It is about `rawSys2` (one link, two voters,
  the non-breakable medium, only `H2` hidden). The shipped three-node
  `LeiosInstanceL.leiosSystemL` is the Stage-L theorem below.

**Modules (as of Stage C, before Stage L generalised them in place).** `LeiosInstance2.agda` and `NoLivelock/` (24 modules), 10,552 lines, plus the
generic `csp-ptree-agda/src/CSP/Laws/DivFree/{Count,CountMore,CountRename,ReachExtra,Prov,ProvMore,RenAlpha}`
(1,974 lines): 12,526 lines in all. `Live2` and `StoreBad` are imported by nobody.
**Reproduction.** On 2026-10-05 every one of these 32 modules (the 25 above and the seven
generic ones) was re-checked with its own `.agdai` deleted first, one agda at a time, each run
carrying its own literal `Checking …` line: 32/32 exit 0, zero warnings. `Logic2` is the
heavy one: it ran out of heap at `-M7G` and checked in 227 s under
`MemoryMax=24G`/`-M20G`; every other module took at most 16 s.

### Stage L — no livelock of the shipped three-node line

**The theorem.** `NoLivelock/NoLivelockL.noLivelockL : ∀ s → ¬ divergences
(LIL.leiosSystemL ∖ HL) s` (`NoLivelock/NoLivelockL.agda:65`), `LIL` being
`LeiosInstanceL`. It is about the SHIPPED system `leiosSystemL` (`LeiosInstanceL.agda:174`):
three nodes, two links, three voters, the BREAKABLE medium, the prototype peer bundle. With
every channel but `env` and `break` hidden, no trace reaches a state that can run hidden
events forever. The module has no parameters and the theorem has no hypotheses; it is spec
§3.3 exactly.

**`HL = HP 2 3`** (`LeiosInstance3.agda:64-65`) is every channel except `env` and `break`,
decided by `LeiosInstanceP.hSet-dec` (`LeiosInstanceP.agda:98-117`, one clause per channel,
`env` and `break` the only `no`s). `leiosSystemL` already hides the wire channels `ioES`, so
the theorem is about a NESTED hiding.

**`FL`.** `FL m = cL * m + cL₀` with **`cL = 185232`** and **`cL₀ = 534972`**
(`NoLivelock/BoundL.agda:127-136`), and `boundL : ∀ {s Q} → rawL ⟹⟨ s ⟩ Q → #H HL s ≤ FL
(#V HL s)` (`:325`). The linear system is solved by hand in `finL` (`:175`), with the
derivation in the comments above `cL`/`cL₀`. The constants are crude and are **not claimed
tight**. (A mutant with `cL = 185231` breaks `finL`'s closing equation; that shows only that
the numeral is pinned by the proof's own arithmetic, not that `FL` is tight.)

**The route: the Stage-C proof, generalised in place over an instance family.**

* *Instances are members of a family, by definition.* `LeiosInstanceP` defines `pL k m`
  (`k` links, `m` voters, `LeiosInstanceP.agda:54`), its Leios parameters `lpF k m` (`:73`)
  and the hidden set `HP k m` (`:120-121`). `LeiosInstance3` proves the bridges, all `refl`:
  `leiosLParams ≡ pL 2 3` and `leiosLP ≡ lpF 2 3` (`LeiosInstance3.agda:42-47`), and, for
  Stage C, `p2 ≡ pL 1 2` and `lp2 ≡ lpF 1 2`. It defines the unhidden three-node composite
  `rawL` (`:50-51`) and proves `sysL≡ : leiosSystemL ≡ rawL ∖ ioES` (`:54-55`), also `refl`.
* *Stage C's modules take the family as parameters.* `TauLogic`, `TauAssembly`, `Threads`,
  `ThreadAlpha`, `ThreadsProv`, `Stores`, `StoresProv`, `PeerAlpha`, `ProvSys` and `Logic2`
  are generalised over `(k m : ℕ) (t : Topology (pL k m)) (vo : Node → VoterId)` and a vote
  universe `(U , allV)`. Stage C re-instantiates them at `pL 1 2`, and its `noLivelock2` and
  `bound2` statements are byte-identical to `9b823bc1`.
* *Node B's second endpoint is counted.* Node B is the only node with two endpoints
  (`epsB`, `LeiosInstance3.agda:58-59`). `Logic2`'s node layer folds the threads and
  bundles over every endpoint, and `BoundL` keeps `refl` checks that B's thread and relay
  constants are the two-endpoint sums.
* *The assembly.* `BoundL` writes out the three nodes: one summary per node (`Logic2.nodeF`),
  the relay cancellation across the three (`cancel3`, `:139`), and `finL`. `sysBL` (`:233`)
  splits `rawL`'s trace with `case Par-trace-elim …`, never with `with`.
* *The rely of the RB-store bound* is the existing provenance chain at the new instance,
  `ProvSys 2 3 … sys-inX mediumB-prov`. There is no separate `ProvSysL` module.

**The breakable medium.** `NetworkLinkBreakableA` (`NetCommon.agda:173-174`) puts each
link's renamed `NetOneLink` under an interrupt `△ (break l ⟶₀ Skip)`.
`MediumBreak.mediumB-relay`, `mediumB-io` and `mediumB-prov` (`NoLivelock/MediumBreak.agda:140-151`)
carry the plain medium's relay, alphabet and provenance facts through the interrupt. They go
via the generic `csp-ptree-agda/src/CSP/Laws/DivFree/TraceInterrupt.agda` (`△-trace-elim`, `:48`): every
run of an interrupt is a run of the body followed by a run of the handler.
* **`break` is VISIBLE**: it is not in `HL`, so a link break is observable, and it is never
  a source of hidden steps.
* **`break` has ZERO weight** in every count `boundL` uses. `BoundL.zB` (`:97`) proves each
  weight is 0 on `IsBrk` (`MediumBreak.agda:109`).

**The nested hiding** is handled by the generic bridge
`csp-ptree-agda/src/CSP/Laws/FD/NoLivelockHide.noLivelockT-∖` (`NoLivelockHide.agda:96`). It takes a
counting bound for the inner process `rawL` against `HL`, the inclusion `ioES ⊆ᴱ HL`
(`NoLivelockL.ioES⊆HL`, `NoLivelockL.agda:39`, one clause per channel) and `rawL`'s
τ-accessibility, and it yields no divergence of `(rawL ∖ ioES) ∖ HL`. Under the inner
hiding, `#H HL` can only drop (`#H-hide`, `:77`) and `#V HL` is unchanged (`#V-hide`,
`:87`).
* Premise (b) is `Tau3.rawL-τ-AccReach` (`NoLivelock/Tau3.agda:55`), with the premise-free
  `NetworkLinkBreakableA-τ-AccReach` as its medium leaf.
* `noLivelockL s = noLivelockT-∖ ioES HL FL FL-mono ioES⊆HL boundL rawL-τ-AccReach`
  (`NoLivelockL.agda:66`).

**Non-vacuity, across BOTH links: on `rawL` and on `leiosSystemL` itself.** `NoLivelock/LiveL.liveL`
(`NoLivelock/LiveL.agda:613`) is a 49-event trace of `rawL`. The run:
1. Node A forges the block `nothing`.
2. Stage C's 24-event `Live2` run happens on link 0, with A serving B. It ends in B's `stPut`.
3. The same run happens on link 1, with B serving C. B's endpoint-(1 , lo) server thread
   reads index 0 of B's RB store, which is the block B has just deposited.

Twelve medium messages cross the breakable medium, six per link.

Its type pins the run, through `Pins` (`:606-608`):
* one forge at A, and none at B or C;
* a `stPut` at B and a `stPut` at C;
* no `break` event.

So the block crossed link 0 and then link 1 through B's store, as the trace's events show
(`gB` reads the slot `ptB` filled). `liveL∖` (`:622`) is the
same run with its 24 wire events hidden: a 25-event trace of the shipped
`LIL.leiosSystemL`, through `HideX`, with the same pins.

How it is built:
* It follows `Live2`'s method: per-component traces assembled with the exact-endpoint
  lifts.
* Those lifts were hoisted in Stage L from `Live2` to the generic
  `csp-ptree-agda/src/CSP/Laws/Traces/TraceIntroExact.agda` (`Live2` now imports them).
* A new lift `△X` (`TraceIntroExact.agda:211`) carries a run of a link through its armed
  `break` handler.
* No step of a composite is computed, and there is no `with` on a system trace.

One mutation was run: making B's link-1 server read index 1 instead of 0 turns `LiveL` red
at `srvB`.

**The finite-carrier dependencies carry over** from Stage C (see the two-node bullets
above), now at the three-voter instance:
* The vote bound is `voteStore-reads` at `U9`, the nine blobs of `VB 3`, with `allV9`
  (`LeiosInstanceP.agda:138-153`) proving `U9` complete.
* The mempool bound uses `Tx = Bool`.
* The certificate bound uses `RbHash = Maybe Bool`.
* The thread counts size on the one-entry body table that `lpF` shares with `leiosLP` and
  with Stage C's `lp2` (`lpL≡`).

An instance with an infinite `Tx`, `VoteBlob` or `RbHash`, or a larger body table, would
need the provenance / weighting arguments of spec §5.

**Postulates.** None. The closure of `noLivelockL` is 97 local modules, with 0 postulates
and 0 escape pragmas. It reaches neither `Parametric/Assembly.agda` nor `FourNode/`, and it
uses neither sanctioned classical seam. With `LiveL` added it is 101 local modules,
again with 0 postulates and 0 escape pragmas.

**A note on the TDD red step.** Agda refuses to import a module that still has holes
(`[SolvedButOpenHoles]`), so a red step cannot put its hole in an upstream bridge. The red
steps of `NoLivelockL` and `LiveL` therefore hole their OWN leaves or headline bodies:
* `NoLivelockL`: `ioES⊆HL` and `FL-mono`;
* `LiveL`: `liveL` and `liveL∖`.

In both, everything else in the module, the headline statement included, is checked
against the real upstream modules.

**KeepAlive caveat**, carried from Stage C: KeepAlive is inert in this model, and an
unboundedly repeating KeepAlive driver would break the bound unless its events stayed
visible.

**What it is NOT.**
* **It is not delivery liveness.** It says that no infinite run of hidden events exists.
  It does **not** say that a forged block reaches B or C, or that any node makes progress.
  `liveL` shows that one delivery across both links is *possible*. It is a non-vacuity
  witness, not a liveness theorem.
* It is not about the four-node estate, and it is not about a generic `Params`.

**Modules.** Stage L adds the following modules, 1,989 lines in all:
* in the Leios directory: `LeiosInstanceP`, `LeiosInstance3`, and `NoLivelock/{BoundL,
  MediumBreak, Tau3, NoLivelockL, LiveL}`;
* the generic `csp-ptree-agda/src/CSP/Laws/DivFree/{ParLabels,TraceInterrupt}`,
  `csp-ptree-agda/src/CSP/Laws/FD/NoLivelockHide` and `csp-ptree-agda/src/CSP/Laws/Traces/TraceIntroExact`.

It also edits Stage C's modules in place. The line metric for Stage L is the inserted
`.agda` lines against `1081c18c`: **2,728**. `LiveL` is imported by nobody.
**Reproduction.** On 2026-10-05, every Stage-L and Stage-C module was re-checked cold: each
module's own `.agdai` was deleted, one agda ran at a time, and every module has its own
`Checking …` line. Every run exited 0, with no warnings (task L7 report).
