# Linear Leios — what this directory proves

A port of the two Leios mini-protocols as implemented on the `leios-prototype` branch of
`ouroboros-consensus` (`LeiosDemoOnlyTest{Notify,Fetch}.hs`, protocol numbers 18/19), a
**Linear-Leios node logic** over them, and **five safety theorems, each with a negative
control**. Everything here is built on the repository's generic CSP-over-process-trees
layer and on `Cardano_network`'s existing `Params`/`Net`/`Node` scaffolding; nothing in
the older estate was changed to accommodate it.

The design spec is
`docs/superpowers/specs/2026-09-21-leios-prototype-protocols-design.md`; the two payload
abstractions are recorded in
`docs/superpowers/decisions/2026-09-21-leios-tx-closure-and-object-identities.md`. The
branch's public status record is `csp-ptree-agda/src/CSP/Laws_status.md` §"Leios prototype".

> **Read section C before quoting anything from sections A or B.** Every result on this
> branch is a NODE-level trace-refinement fact. There is no network-wide statement here,
> and none of the five theorems is a liveness or a validity statement.

---

## A. The five theorems

All five have the same shape. A *discipline* says which labels **mint** keys and which
labels are **gated** by the keys minted so far; the specification `OriginSpecT`
(`OriginSafe.agda:231`) permits every trace except one that fires a gated label whose gate
is shut; and the theorem is that the node refines that specification at `⊑T`:

```agda
Spec ⊑T nodeP n (nodeLogicL n st₀)        -- nodeP = nodeWith nodeBundleP
```

`nodeLogicL n st₀` (`NodeLogicL.agda:755`) is one node's whole logic — six node-level
threads in parallel with every incident endpoint's ten, synchronised on `storeES` with all
five stores — and `nodeP` wraps that in the node's own prototype peer bundle, synchronised
on `apiES`. `st₀` is the empty-store state.

| # | Theorem | Module:line | Premises | Quantification |
|---|---|---|---|---|
| S1 | `bodySound` | `BodyOrigin.agda:840` | **none** | ∀ `Params`, ∀ `LeiosParams`, ∀ topology, ∀ `apiES`, ∀ `voterOf`, ∀ node |
| S2 | `voteSound` | `VoteSound.agda:915` | **none** | as above |
| S2′ | `blobSound` | `BlobOrigin.agda:701` | `nodeOf`, `nodeOf-voterOf` | as above, plus the voter/node retraction |
| S3 | `certSound` | `CertSound.agda:724` | `CertifiesMono` | as above |
| S3 | `certSoundL` | `CertSound.agda:760` | **none** | the shipped instance only |
| S4 | `certRbSound` | `CertRbOrigin.agda:695` | **none** | as S1 |

### S1 — `bodySound`: an EB body is forged here or was asked for here

```agda
-- BodyOrigin.agda:820-821
BodySound : Set₁
BodySound = ∀ (n : Node) → BodySpecT ⊑T nodeP n (nodeLogicL n st₀)

-- BodyOrigin.agda:840-841
bodySound : BodySound
bodySound n = soundOf n (nodeLogicL n st₀) (wf-logic n) (noRet-logic n)
```

A node never stores an endorser-block body it neither forged nor requested. Minting is on
the environment's forge (`env _ _ envForge`) and on a LeiosFetch block request
(`apiLP _ _ lfpSendBlockRequest`); the gated label is the body deposit, and the gate is
membership of `ebHash eb` in the minted set (`bodyMints`, `BodyOrigin.agda:255-258`;
`bodyGate`, `BodyOrigin.agda:266`). **Premise-free.** Declared over
`Generic` (`BodyOrigin.agda:155-159`), whose parameters are `Params`, `LeiosParams`,
`Topology`, `apiES` and `voterOf`.

### S2 — `voteSound`: a vote blob is vouched for

```agda
-- VoteSound.agda:900-901
VoteSound : Set₁
VoteSound = ∀ (n : Node) → VoteSpecT ⊑T nodeP n (nodeLogicL n st₀)

-- VoteSound.agda:915-916
voteSound : VoteSound
voteSound n = soundOf n (nodeLogicL n st₀) (wf-logic n) (noRet-logic n)
```

A node deposits no vote blob it cannot vouch for: either a neighbour delivered that exact
blob on `lnpRecvVotes`, or the node itself read the ranking block the blob names *and* the
body of the endorser block that block announces. Three key sorts are minted — `kRb` on a
block read, `kBody` on a body read, `kRelay` on a Notify votes delivery
(`voteMints`, `VoteSound.agda:314-318`) — and only the `stPutVote` deposit is gated
(`voteGate`, `VoteSound.agda:351-352`). **Premise-free.**

### S2′ — `blobSound`: a relayed ballot has an origin

```agda
-- BlobOrigin.agda:686-687
BlobSound : Set₁
BlobSound = ∀ (n : Node) → BlobSpecT ⊑T nodeP n (nodeLogicL n st₀)

-- BlobOrigin.agda:701-702
blobSound : BlobSound
blobSound n = soundOf n (nodeLogicL n st₀) (wf-logic n) (noRet-logic n)
```

A node never deposits a blob attributed to **another** voter unless an `lnpRecvVotes`
delivery carried that exact blob; blobs it casts itself are attributed to itself
(`vouchedAt`, `BlobOrigin.agda:304`). **Two extra module parameters carry it**: a map
`nodeOf : VoterId → Node` and the round-trip law
`nodeOf-voterOf : ∀ n → nodeOf (voterOf n) ≡ n` (`BlobOrigin.agda:156-158`). At
`LeiosInstanceL` both are the identity, so they are discharged there.

### S3 — `certSound` / `certSoundL`: no certificate the oracle does not grant

```agda
-- CertSound.agda:709-710
CertSound : Set₁
CertSound = ∀ (n : Node) → CertSpecT ⊑T nodeP n (nodeLogicL n st₀)

-- CertSound.agda:724-725
certSound : CertSound
certSound n = soundOf n (nodeLogicL n st₀) (wf-logic n) (noRet-logic n)
```

`stCert r` fires only when the oracle certifies `r` against the vote blobs actually
deposited at this node (`certMints`, `CertSound.agda:246-248`; `certGate`,
`CertSound.agda:266`). The generic form carries one hypothesis about the **oracle**, not
about the logic:

```agda
-- CertSound.agda:273-274
CertifiesMono : Set
CertifiesMono = LeiosP.CertifiesMono p lp
```

— more blobs never withdraw a certificate. A *counting* quorum is inadmissible
(`[a,a] ⊆ [a]`). At the shipped oracle the premise is discharged, giving the one positive
stated at a concrete instance:

```agda
-- CertSound.agda:749-750
certMonoL : CSL.CertifiesMono
certMonoL sub r eq = any-mono _ sub eq

-- CertSound.agda:760-761
certSoundL : CSLS.CertSound
certSoundL = CSLS.certSound
```

`CSL` is `Generic leiosLParams leiosLP leiosLLine apiES (λ n → n)` (`CertSound.agda:744`)
— the three-node Linear-Leios line. `certSoundL` is therefore **unconditional but
instance-specific**; it is still a NODE-level statement, not a claim about
`leiosSystemL`.

### S4 — `certRbSound`: a certificate-carrying RB is earned or received

```agda
-- CertRbOrigin.agda:675-676
CertRbSound : Set₁
CertRbSound = ∀ (n : Node) → CertRbSpecT ⊑T nodeP n (nodeLogicL n st₀)

-- CertRbOrigin.agda:695-696
certRbSound : CertRbSound
certRbSound n = soundOf n (nodeLogicL n st₀) (wf-logic n) (noRet-logic n)
```

A node never puts a certificate-carrying ranking block into its own store unless its own
vote store had certified the RB that certificate names, or the block arrived off the wire.
A certificate-free block is free; a certificate-carrying one needs `rbCert b` to be in the
minted set (`vouchedRb`, `CertRbOrigin.agda:265`; `certRbGate`, `CertRbOrigin.agda:270`).
**Premise-free.** Note the two mint clauses:

```agda
-- CertRbOrigin.agda:258-261
certRbMints : (at : AnyTypes (Net_Api Payload)) → proj₁ at → List RbHash
certRbMints (_ , store _ _ (stHasCert r)) _ = r ∷ []
certRbMints (_ , apiBF _ _ recvBFBlock)   b = maybe′ (λ r → r ∷ []) [] (rbCert b)
certRbMints _                             _ = []
```

The second clause is deliberately **ungated and self-licensing** — see section C.

---

## B. The five negative controls

Each control changes exactly **one** slot of the composite the positive is stated over,
exhibits a trace of the broken composite, and shows that trace is not a trace of the
specification. All five are at the concrete `leiosLParams` line, at node 0.

| Theorem | Control | Module:line | Substitution | Initial state | Composite |
|---|---|---|---|---|---|
| S1 | `bodySound-node-FAILS` | `BodyOriginBad.agda:388` | `lnClientLoopLBodyBad` for the Notify client | `st₀` | **reduced** — one thread + five stores, no bundle |
| S2 | `voteSound-node-FAILS` | `VoteSoundBad.agda:375` | `voterBad` in the voter slot | `stSeeded` | `nodeLogicL`'s own, inside `nodeP` |
| S2′ | `blobSound-node-FAILS` | `BlobOriginBad.agda:435` | `voterBlobBad` in the voter slot | `stSeeded` | `nodeLogicL`'s own, inside `nodeP` |
| S3 | `certSound-node-FAILS` | `CertSoundBad.agda:502` | `voteStoreBad` as the **fifth store** | `stSeeded` | `nodeLogicL`'s own, inside `nodeP` |
| S4 | `certRbSound-node-FAILS` | `CertRbOriginBad.agda:348` | `forgeCertBad` in the forge-cert slot | `st₀` | `nodeLogicL`'s own, inside `nodeP` |

Round R2 (commits `ff0be020`..`d71e63a5`) restated four of the five over `nodeLogicL`'s own
composite, using the new `par-brBoth` introduction rule in
`CSP/Laws/Traces/TraceLawsParallel.agda`. `BodyOriginBad` was not restated; its reduction
is structural, not a missing lemma (section C).

### S2 — the body read is load-bearing

```agda
-- VoteSoundBad.agda:363-364
VoteSound-node-Bad : Set₁
VoteSound-node-Bad = VoteSpecT ⊑T badNode

-- VoteSoundBad.agda:375-376
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
(`rb-conjunct-holds`/`body-conjunct-fails`, `VoteSoundBad.agda:330`/`:335`).

### S2′ — the voter's own attribution is load-bearing

```agda
-- BlobOriginBad.agda:422-423
BlobSound-node-Bad : Set₁
BlobSound-node-Bad = BlobSpecT ⊑T badNode

-- BlobOriginBad.agda:435-436
blobSound-node-FAILS : ¬ BlobSound-node-Bad
blobSound-node-FAILS h = noGet (proj₂ (h _ bad-blob-fires))
```

`voterBlobBad` (`BlobOriginBad.agda:169`) casts its ballot under another voter's name.
`nodeLogicLBlobBad` at `:181`, `badNode` at `:211`, seed at `:206` (one ranking block, one
EB body).

### S3 — the oracle consultation is load-bearing

```agda
-- CertSoundBad.agda:488-489
CertSound-node-Bad : Set₁
CertSound-node-Bad = CertSpecT ⊑T badNode

-- CertSoundBad.agda:502-503
certSound-node-FAILS : ¬ CertSound-node-Bad
certSound-node-FAILS h = noGet (proj₂ (h _ bad-cert-fires))
```

The substituted slot is a **store**, not a thread: `voteStoreBad`
(`CertSoundBad.agda:210`) drops the oracle guard whole and fires `stCert` on every
deposit. The control also supplies its own stricter oracle `certifies₂`
(`CertSoundBad.agda:140`), a two-voter quorum, packaged as
`leiosLP₂ = record leiosLP { certifies = certifies₂ }` (`CertSoundBad.agda:147`).
`nodeLogicLCertBad` at `:222`, `badNode` at `:252`, seed at `:247`. Quote this as
"unsound **against a two-voter quorum**", never as "unsound".

### S1 — the wire-path guard is load-bearing (reduced composite)

```agda
-- BodyOriginBad.agda:377-378
BodySound-node-Bad : Set₁
BodySound-node-Bad = BodySpecT ⊑T badLogic

-- BodyOriginBad.agda:388-389
bodySound-node-FAILS : ¬ BodySound-node-Bad
bodySound-node-FAILS h = noReqNext (proj₂ (h _ bad-body-fires))
```

`badLogic = nodeLogicLBodyBad nA st₀` (`BodyOriginBad.agda:197`) is **one thread against
the five stores** (`BodyOriginBad.agda:180`), with the peer bundle and the other fifteen
threads absent. What it refutes is therefore `BodySpecT ⊑T <that composite>`, not
`BodySpecT ⊑T nodeP …`. The compensator is at the identical reduced composite with the
honest client in the thread slot:

```agda
-- BodyOriginBad.agda:396
bodySound-logic-good : BodySpecT ⊑T nodeLogicLBodyGood nA st₀
```

### S4 — the `stHasCert` rendezvous is load-bearing

```agda
-- CertRbOriginBad.agda:335-336
CertRbSound-node-Bad : Set₁
CertRbSound-node-Bad = CertRbSpecT ⊑T badNode

-- CertRbOriginBad.agda:348-349
certRbSound-node-FAILS : ¬ CertRbSound-node-Bad
certRbSound-node-FAILS h = noForgeCert (proj₂ (h _ bad-cert-fires))
```

`forgeCertBad` (`CertRbOriginBad.agda:185`) deposits straight away instead of first
rendezvousing on `stHasCert r`. `nodeLogicLCertRbBad` at `:195`, and
`badNode = nodeP nA (nodeLogicLCertRbBad nA st₀)` (`CertRbOriginBad.agda:204`) — **at
`st₀`, the positive's own state**, so S4's A/B differs in exactly one thread and in
nothing else. Its compensator is the positive theorem itself:

```agda
-- CertRbOriginBad.agda:355-356
certRbSound-node-good : CertRbSpecT ⊑T nodeP nA (nodeLogicL nA st₀)
certRbSound-node-good = certRbSound nA
```

The control keeps its own `leiosLP₃` (`CertRbOriginBad.agda:130`), a record update of
`leiosLP` changing only `rbCert`, so its statement does not move with the shipped
instance. (`leiosLP` now carries the same value; see `LeiosInstanceL.agda:140-141`.)

**The in-file prose of `CertRbOriginBad` is out of date on this point.** Its header
section is still titled "WHY THE COMPOSITE IS REDUCED", `:21` still says "over a REDUCED
composite", and the comments at `:333` and `:342-343` still describe the composite as
reduced and the level as "the node logic's THREAD GROUP". The definition at `:204`
contradicts all four: the composite is `nodeP nA (…)`, the full one. The definition is
authoritative.

### The other two negative facts

Neither is one of the five controls; both are properties of *designs that were rejected*.

| Fact | Module:line | What it is |
|---|---|---|
| `chatter-diverges` | `Negative/Chatter.agda:179` | `Diverges chatterPair` — the unchanged relay loop announces the same held block forever, so an infinite τ-path exists once the store and Notify channels are hidden. This is why `NodeLogicL.lnServerLoopL` carries a read pointer. |
| `wedge-reachable` / `wedge-stuck` | `Negative/FetchWedge.agda:147` / `:238` | A pointer-driven fetch asks for a body the neighbour does not hold; both sides of the rendezvous are in `storeES`, so the pair has **no** transition at all. Level: a pair plus one step, not a system. |

---

## C. How to read these claims

### Everything is NODE level, at `⊑T`

Every positive and every control is a trace-refinement fact about
`nodeP n (nodeLogicL n st₀)` — one node's logic inside its own peer bundle. **No result
here is about a network.** A lift is not a corollary: each discipline is
*endpoint-agnostic* in its mints (it mints at every `(l , d)`), which is sound at node
level only because inside `nodeP n (nodeLogicL n st₀)` the only `store`/`env` channels are
the `homeOf n` ones and no bundle peer offers a `store` channel at all. **Lifted naively,
node X's mint would licence node Y's deposit.** The fix each module's header prescribes is
to index the key by `(l , d)` and gate a deposit at `(l , d)` on keys carrying that same
`(l , d)`; S3's lift is strictly harder than S2's, because its gate sits on the store side
of the `⦀`.

There is **no S0 on this branch.** Announcement safety for `nodeLogicL` is a network-wide
statement (at node level it is either false or vacuous) and was deferred. Nothing here may
be quoted as announcement safety for the Leios node logic, and nothing here re-establishes
`AnnounceSafeConcrete.announceSafeT`, which remains a theorem about the *old* relay logic
and the old peers.

### No liveness, and no validity

All five results are purely safety-shaped: **no module exhibits a good node actually
reaching the gated event.** Three liveness ceilings are recorded in `NodeLogicL`'s own
comments and are reachable in the good logic — `forgeCert`'s `stHasCert` rendezvous blocks
forever when the RB is never certified; `serveTxs`'s `getTxEv` blocks when the node holds
a body but not a transaction of its closure (and since `ebServeLoop` and `ebTxsServeLoop`
drive the same LeiosFetchP producer, this also stops EB-body serving on that endpoint);
`fetchTxs`'s leading `getBodyEv` blocks the single Notify client thread. None of this is
deadlock-freedom and none of it may be quoted as such.

Nor is anything a validity statement. The prototype's votes carry no verdict at all, so S3
says nothing about whether a certificate is *deserved*; S1 says a body was forged or
requested here, not that requesting it was *right*, and its guard is a hash test with
`ebHash` nowhere assumed injective; S2′ does not show the claimed voter really cast the
blob; S4's wire clause mints a hash, so one delivery licenses the deposit of every block
carrying that same certificate hash.

### The S4 write-up rule

These two sentences are what this branch may and may not be quoted on
(`Laws_status.md:1814`/`:1816`):

> **Quotable: "S4 has content at the shipped instance."**
>
> **NOT quotable: "S4 was shown to constrain a demonstrated behaviour of the shipped
> Leios line."**

The gate is machine-checked to be a real test *at the shipped instance* and not merely
inferred across instances — `NodeLogicLSanity.gate-uncertified-at-leiosLP` (`:194`) and
`gate-certified-at-leiosLP` (`:200`). But **no exhibited trace anywhere on this branch has
the gate refusing anything**: the forge deposit is reachable-in-principle and never
exhibited. And the wire clause is ungated and self-licensing
(`certRbMints … recvBFBlock`, `CertRbOrigin.agda:260`), so the only cert-RB depositor this
branch exhibits inside `nodeLogicL` is the BlockFetch `clientLoop`, whose deposit is
licensed by its own immediately-preceding `recvBFBlock`.

### The probe levels in `NodeLogicLSanity` differ and must not be conflated

`NodeLogicLSanity.agda` is a non-vacuity certificate for the R1 repair (two pure-rendezvous
`env` arms that unblocked `forgeCert` and `submit`). Nothing imports it. Its six probes sit
at **three different levels**:

| Probe | Line | Level |
|---|---|---|
| `forgeCert-first-step` | `:125` | an **LTS step of the full composite** `nodeLogicL nA st₀` |
| `submit-first-step` | `:148` | an **LTS step of the full composite** |
| `uncertified-blocks` | `:169` | a `viewV` fact about the **isolated** `voteStore nA _`, at ONE hash |
| `certified-offers` | `:177` | ditto, the same hash with `certs = rCert ∷ []` |
| `gate-uncertified-at-leiosLP` | `:194` | about the **specification gate** `certRbGate` at `leiosLP` — not about any process |
| `gate-certified-at-leiosLP` | `:200` | ditto |

Probes 3 and 4 are process facts about the store at one hash and two states; the ∀ version
is structural, in `NodeLogicL.offerCerts`, and is **not** what they pin. Probes 5 and 6
say nothing about the implementation. Nothing here may be quoted as a fact about the
composite except probes 1 and 2.

### Pairing a positive with its refutation

The standing rule "never pair a positive with its refutation" is **narrowed, not dropped**.
Since R2, the *composite* caveat is retired for S2/S2′/S3/S4 — those four controls run over
`nodeLogicL`'s own composite inside `nodeP`. But every refutation is still at a **concrete
parameter line**, at **node 0**, at **NODE level**, and three of the five run from a
**seeded** state (`stSeeded`) whereas every positive is at `st₀`; S4 alone is at `st₀`. So:
never pair an ∀-quantified positive with its concrete refutation in one sentence, and never
read a system-level break out of any of them.

The `-good` compensators reflect that. `voteSound-node-good` (`VoteSoundBad.agda:384`),
`blobSound-node-good` (`BlobOriginBad.agda:446`) and `certSound-node-good`
(`CertSoundBad.agda:512`) are each the positive's own assembly applied to the *unmodified*
`nodeLogicL nA stSeeded`, so they compensate the **seed and nothing else**.
`certRbSound-node-good` (`CertRbOriginBad.agda:355`) is `certRbSound nA` itself.

### Why S1 is still reduced, and why `par-brBoth` does not help it

S2/S2′/S3 were reduced because `ebIndex`, the voter, `lnServerLoopL` and `bodyOfferLoop` all
offer `stGetAt 0`: the full composite's first step is a **both-offer non-sync collision**,
for which the repo had `par-brBoth` eliminations but no introduction. R2 built the
introduction, so those three reductions are gone. (Their traces pay one extra τ per
collision: `par-pVis` fires a both-offer non-sync event into an inline internal choice
rather than picking a side.)

S1's reduction has a different cause and the lemma is irrelevant to it. Its defect lives on
the **wire branch**, so the violating trace must contain `apiLP` events —
`lnpSendRequestNext`, `lnpRecvBlockOffer`, `lfpSendBlockRequest`, `lfpRecvBlock` — and every
`apiLP` channel is inside **`apiES`**. Inside `nodeP` each of those four events would have
to be driven through the twelve-peer bundle's `⦀⋆` together with the LeiosFetch consumer's
own wire state machine (`BodyOriginBad.agda:26-38`). That is an `apiES`-structural cost,
not a collision; `par-brBoth` addresses collisions. Hence `bodySound-logic-good`
(`BodyOriginBad.agda:396`) survives as a genuine compensator at the identical reduced
composite.

A trace of the logic need not survive the bundle — `∥⇘ apiES ⇙` only restricts — so S1's
control does not by itself refute the node-level statement for the broken logic. What it
refutes is the load-bearing half: `bodySound n` is `soundOf n _ (wf-logic n) _`, the bundle
contributing only the vacuous `wf-linkBundlesP`.

---

## D. The directory

22 modules, 9,168 lines.

### The model

| Module | Lines | Purpose |
|---|--:|---|
| `LeiosParams.agda` | 93 | The Leios parameter record over a `Params`: the vote-blob algebra (a vote names the **ranking block** it endorses), the certification oracle `certifies` and its `CertifiesMono` law, the two EB projections `ebTxs`/`ebSize`, and `rbCert`. No validation oracle — the prototype's votes carry no verdict. |
| `NodeLogicL.agda` | 760 | **The Linear-Leios node logic.** An additive layer over `Parametric.NodeLogic`, which is untouched. `nodeLogicL` (`:755`) is six node-level threads (`forgeL`, `forgeCert`, `ebIndex`, `voter`, `submit`, `certSink`) in parallel with each endpoint's ten, synchronised on `storeES` with five stores (block, EB-entry, body, mempool, vote). |
| `PeersP.agda` | 170 | The **prototype** peer bundle `nodeBundleP`, over `LeiosNotifyP`/`LeiosFetchP` (`apiLP`). Additive: `NetworkPar` and `Node.agda` are untouched; a node runs one bundle or another via `Node.nodeWith`. |
| `PeersR.agda` | 85 | The earlier **request-reporting** bundle `nodeBundleR`, which swaps in the reporting LeiosFetch/TxSubmission servers of the *old* CIP-draft peers. Superseded: it now carries zero `Wf` facts and one consumer, `PeersRSanity`. |
| `LeiosInstanceL.agda` | 176 | The concrete three-node Linear-Leios line over its own `Params` (`leiosLParams`, `:94`; `leiosLP`, `:130`; `leiosLLine`, `:156`), and the system `leiosSystemL` (`:174`) — the prototype bundle over `NetworkLinkBreakableA`. |

### The proof framework

| Module | Lines | Purpose |
|---|--:|---|
| `OriginSafe.agda` | 771 | The **generic origin/soundness carrier**, written once for all five disciplines: `Minted`, `originOffer`, the specification `OriginSpecT` (`:231`) and `OriginSpec` (`:238`), the coinductive record `OSafe` (`:253`), the leaf predicate `FreeAt`, the `∥⇘⇙`/`⦀` closure lemmas, and the bridge `osafe→⊑T` (`:751`). |
| `OriginLeaves.agda` | 333 | The **discipline-independent leaves**: the part of an origin proof that depends only on the gated channel being a `store` channel, plus the nine prototype-bundle `Wf` facts (`RLNP`, `RLFP`, `ooLNP`, `ooLFP`, `wf-clientPeerP`, `wf-serverPeerP`, `wf-slotP`, `wf-nodeBundleP`, `wf-linkBundlesP`) hoisted out of `VoteSound`. |

**The route, and why `OSafe` alone cannot take it.** `OSafe` has no structural closure over
`Prefix`/`Output`/`_>>=_`/`loop`, and its `noTick` field is *refutable* of a peer bundle
— peers terminate on `done` (`VoteSound.agda:57-60`). Both problems were already solved by
the assume-guarantee framework one directory up: `Parametric.BlockProvenance.Carrier` and
its returning-tree layer `Parametric.BlockProvenanceWfR.Body` carry no `noTick` obligation
and come with `wfR-Prefix`, `wfR-Output`, `wfR-□`, `wfR->>=`, `wf-loop` and `wf-loop0`.
Each discipline is an instance of them; `wf→osafe` (e.g. `VoteSound.agda:514`) is the one
bridge back into `OriginSafe`, and `osafe→⊑T` finishes.

### The theorems and their controls

| Module | Lines | |
|---|--:|---|
| `BodyOrigin.agda` | 841 | S1 `bodySound` |
| `BodyOriginBad.agda` | 400 | S1's control (reduced composite) + `bodySound-logic-good` |
| `VoteSound.agda` | 916 | S2 `voteSound` |
| `VoteSoundBad.agda` | 388 | S2's control + `voteSound-node-good` |
| `BlobOrigin.agda` | 702 | S2′ `blobSound` |
| `BlobOriginBad.agda` | 450 | S2′'s control + `blobSound-node-good` |
| `CertSound.agda` | 761 | S3 `certSound` (premised) and `certSoundL` (discharged at the shipped oracle) |
| `CertSoundBad.agda` | 516 | S3's control, the two-voter oracle `certifies₂`, + `certSound-node-good` |
| `CertRbOrigin.agda` | 696 | S4 `certRbSound` |
| `CertRbOriginBad.agda` | 356 | S4's control + `certRbSound-node-good` (= the positive) |

### Probes and negative facts

| Module | Lines | Purpose |
|---|--:|---|
| `NodeLogicLSanity.agda` | 202 | Six probes at three levels (see section C). Imported by nobody. |
| `PeersPSanity.agda` | 73 | `lfpP-reports-request` (`:68`) — a `refl` typechecking probe that the prototype LeiosFetch server reports the request to the application. |
| `PeersRSanity.agda` | 43 | The line system over `nodeBundleR`; the only remaining consumer of `PeersR`. |
| `Negative/Chatter.agda` | 189 | `chatter-diverges` (`:179`) — the unchanged relay chatters. Design law L's justification. |
| `Negative/FetchWedge.agda` | 247 | `wedge-reachable` (`:147`) / `wedge-stuck` (`:238`) — the pointer-driven fetch wedge (spec correction C2). |

---

## E. Provenance and reproduction

* Branch `examples/leios_prototype_protocols`, HEAD **`d71e63a5`**.
* Zero postulates, zero holes, no `NON_TERMINATING` in any module of this directory.
* All ten theorem and control endpoints were typechecked **cold** (each module's own
  `.agdai` removed first, one agda at a time, each run carrying its own literal
  `Checking …` line) at HEAD: **10/10 EXIT 0, zero warnings, 20-21 s each**. Logs are in
  the git-ignored ledger at
  `.superpowers/sdd/2026-09-21-leios-prototype-protocols/logs/r2-final-*.log`.
* The four-node estate below `Net` is covered transitively and was genuinely rebuilt in
  the same round (`logs/r2-sweep3.log`, EXIT 0, 105 modules, 43 m 49 s).

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

`Parametric/Spike/HideDiverge.agda` (three `?` holes), `Parametric/EvBothProbe.agda` (a
stale `numConns` literal) and the `NetworkVerification/Liveness/PipePair*` chain are RED,
all three pre-existing and predating this work, and none is in any endpoint's closure here.
