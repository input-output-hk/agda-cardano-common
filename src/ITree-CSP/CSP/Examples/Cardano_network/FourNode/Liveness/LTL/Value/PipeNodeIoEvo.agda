{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the whole-nodes io EVOLUTION cone
-- (`Praos.PipeNodeIoEvo`), sub-obligation (d) of the `PipeInvProd.TauIoS` arm.
--
-- `PipeNodeFix.top-nodes-io-abs-client-cls` already delivers, for an io fire of
-- `absNodesOf s`: the successor state `s′` with `med s ≡ med s′`, the concrete
-- weak run, and the SIX driver fixities (prod-AB/prod-AC/cp-B/cp-C/cons-BD/
-- cons-CD).  What it does NOT deliver is any CONTENT for the four tracked BF
-- clients — its `ClientClass1.clAdv` carries a `ClientAdv`, which `adv-of`
-- makes total on any pair, so it says nothing — and it exposes NO server slot
-- at all (node A goes through the frozen driver-only peel
-- `WalkConvNodeFix.nodeA-ev-io-abs-fix`).
--
-- THIS leaf re-mirrors the same four-node dispatch on top of
-- `PipeBundleIoEvo.absBundleG-io-evo`, so the successor carries, per node:
--   · a `CliIoCls` for every tracked BF CLIENT  (bfC-AB on B, bfC-AC on C,
--     bfC-BD and bfC-CD on D)     — fixed / ¬-holding / the payload WAS a block
--   · a `SrvIoCls` for every tracked BF SERVER  (bfS-AB and bfS-AC on A,
--     bfS-BD on B, bfS-CD on C)   — fixed / ¬-holding
-- plus the six driver fixities, kept verbatim.  Node A is re-mirrored too (the
-- frozen peel drops both upstream servers).
--
-- The four tracked clients are exactly `PipeInv.upClient`/`dnClient` and the
-- four tracked servers exactly `PipeSrvInv.upSrv`/`dnSrv`, so the output is
-- precisely the antecedent material of `PipeInv.Coupled`'s two CLIENT clauses
-- and of `PipeSrvInv.SrvCoupled`'s two clauses.
--
-- Every non-firing node keeps ALL its slots `inj₁ refl` (its node record is a
-- LITERAL in the successor `mkSys`); a firing node's co-located non-fired peer
-- likewise (a LITERAL in the `mkNodeX`).
--
-- Consumed by `PipeTauIo`, `PipeValTauIo` and (through the ⁺ instance of §1b)
-- `LiveLegStep`.  No postulate/hole/meta.  SESSION-52: this module is the ONE
-- io-side base module the owner`s grant #1 opens, for the strict `Cf`/`Sf`
-- generalisation of §1b; the frozen cone is re-derived as its instance in §8 and
-- both frozen consumers see no change.  Everything else here is untouched.
-- SESSION-55 (same grant, second exercise): §1c adds the SERVER MIRROR of §1b's
-- ownership layer — `NoSrvWriteAt` and its four per-node witnesses — and `sRefl`
-- now takes it exactly as `cRefl` takes `NoCliReadAt`.  `facts₀` ignores the new
-- argument, so the frozen cone is again re-derived verbatim and `PipeTauIo` /
-- `PipeValTauIo` see NO change.
--
-- *** (T5, OWNER GRANT #11 — THE FOURTH FACT FAMILY, SERVER HALF) ***  A caller
-- proving an invariant on a CHAINSYNC SERVER slot needs the same channel the three
-- existing ones give the BF peers and the `InertPos`s, and for the reason grant #6
-- already states at `InertFact` below: the successor `css′` is bound EXISTENTIALLY
-- by `BundleEvo` and no consumer downstream can recover it, so the fact has to be
-- reported HERE, where the fired peer is decoded.  `CssFact`/`Csf`/`csRefl` and
-- `AllCssFacts` are that channel.  Three things keep it cheap and regression-free:
--   · its `Refl` witness is PREMISE-FREE, exactly like grant #6's `iRefl` — the
--     fixed-slot answer is about the SAME term, so no ownership layer (grant #7's
--     `NoCliReadAt`/`NoSrvWriteAt`) is needed;
--   · only NODES B AND C gain a peel field: the two tracked CS servers are
--     `LiveRelayOpen.dnCSs legBD = csS-BD (nB)` and `dnCSs legCD = csS-CD (nC)`, so
--     `NodeAEvR-io`/`NodeDEvR-io` are untouched (nothing tracks node A's or node
--     D's CS servers);
--   · every addition is TRAILING (`BundleEvo`'s conjunct, the two peel-record
--     fields, `top-nodes-io-evoP`'s component) except `IoFacts`' own `Csf`, which
--     must precede `bd` to be in scope of it — and a record is by NAME, so that
--     insertion cannot shift a reader.
-- `Csf₀ = ⊤` and `csRefl = tt`, so §8's frozen cone keeps its exact type and
-- `PipeTauIo`/`PipeValTauIo` see no change for the third time.
--
-- *** (T6c, OWNER GRANT #12 — THE CLIENT HALF, THE A/D SERVER SLOTS, AND THE
-- CHANNEL-PARAMETRIC OWNERSHIP LAYER.) ***  Grant #11's parenthesis above — "the
-- CLIENT half (`CscFact`) is deliberately NOT added: no consumer" — expired: the
-- ChainSync channel invariant's JOIN (`LiveChanJoinCS`) needs, per hop, BOTH peers'
-- io evolution, because every `LiveChanCS.HopEvo` arm names the mover's adjacency
-- AND the other peer's fixity, and `ccPre` — the clause that refutes the client's
-- three wire-sends under the server's pre region — is about the CLIENT.  Three
-- additions, all trailing except `IoFacts`' own field (which must precede `bd`, and
-- a record is by NAME so no reader shifts):
--
--   · `CscFact`/`Cscf`/`cscRefl` + one trailing `BundleEvo` conjunct — the exact
--     mirror of grant #11's block;
--   · SIX new peel-record fields.  The eight per-leg CS io slots all sit at
--     `(link , hi)`, and WHERE each lives is forced by the bundle keys: node A's
--     bundles are `absBundleG l lo hi`, so the UP-hop CS SERVERS (`csS-AB`,
--     `csS-AC`) are node A's at its `sv`; node D's are `absBundleG l hi lo`, so the
--     DOWN-hop CS CLIENTS (`csC-BD`, `csC-CD`) are node D's at its `cl`; and the
--     relay's UP-hop CS CLIENTS (`csC-AB`, `csC-AC`) are node B's/C's at their `cl`.
--     Grant #11's two slots were the DOWN-hop SERVERS.  So all four nodes gain
--     slots — A two `Csf`, B and C one `Cscf` each, D two `Cscf`.
--   · *** THE OWNERSHIP LAYER IS NOW PARAMETRIC IN THE CHANNEL. ***  `csRefl` was
--     premise-free; it can no longer be, because the join's io arms must refute
--     "the CS cell filled while BOTH of the hop's peers stayed fixed", and two
--     fixities are not a contradiction — only the payload's ROLE separates the two
--     peers, which share the key `(link , hi)`.  That is grant #7's argument at a
--     second channel, so rather than mirror its four predicates the `IDs` is made a
--     PARAMETER of all four: `NoCliReadAt`/`NoCliWriteAt`/`NoSrvWriteAt`/
--     `NoSrvReadAt` (hence `NoCliIoAt`/`NoSrvIoAt`) take `(id : IDs)`, and the eight
--     `-link`/`-role` witnesses plus the eight per-node witnesses take it
--     IMPLICITLY — their bodies never inspect the channel, so not one clause body
--     changes.  The four keys the per-node witnesses already cover are exactly the
--     four the CS families need, with the same role assignment.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Relation.Nullary using ( yes; no; ¬_ )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; _≢_; refl; sym; trans; cong; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeNodeIoEvo (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; apiES; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Net p using
  ( Net_Api; Net_Api-≟; Link
  ; apiCS; apiBF; apiKA; apiTS; apiLN; apiLF; done; input; output
  ; sndmsg; rcvmsg; tx; sndack; rcvack; ack; break )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using
  ( Dir; lo; hi; IDs; N2N_BlockFetch
  -- (T6c, grant #12) the CS families' channel, and the channel the four ownership
  -- predicates below are now PARAMETRIC in
  ; N2N_ChainSync )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; EventSet; viewV )
  renaming ( ∅ES to ∅ESa )
open EventSet using ( mem )

import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload}) as PEA

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; τ; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_ )

import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep
open SStep using ( NetProc; absNodeA; absNodeB; absNodeC; absNodeD; absBundleG; ⦀-noOffer
                 ; absNodesOf; nodesOf )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA
  using ( io⇒¬api; apiLink-inj; ApiHasLink; ahlIn; ahlOut; ahlDone
        ; ahlCS; ahlBF; ahlKA; ahlTS; ahlLN; ahlLF )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_RouteLnLf blkA
  using ( noOffer→viewV )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink blkA
  using ( nodeA-drv-io-no; nodeB-drv-io-no; nodeC-drv-io-no; nodeD-drv-io-no
        ; linkAB≢linkAC; linkAB≢linkBD; linkAC≢linkCD; linkBD≢linkCD
        ; ClientIo; ServerIo; client-server-excl )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink2 blkA
  using ( nodeC-io-no-when-B; nodeD-io-no-when-B; nodeD-io-no-when-C
        ; nodeB-io-no-when-A; nodeC-io-no-when-A; nodeD-io-no-when-A
        ; RoleFP; lo≢hi; linkAB≢linkCD; linkAC≢linkBD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink3 blkA
  using ( absNodeA-io-fp; absNodeB-io-fp; absNodeC-io-fp; absNodeD-io-fp
        ; absNodeD-io-no-when-C; absGroupA-io-no; absGroupB-io-no; absBundleG-io-ahl )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink6 blkA
  using ( bundleG-io-no; ∥⇘⇙-wev-soloL; ⦀-wev-L; ⦀-wev-R
        ; nodeA-io-no-when-B; nodeA-io-no-when-C; nodeA-io-no-when-D
        ; nodeB-io-no-when-C; nodeB-io-no-when-D; nodeC-io-no-when-D )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; mkSys; med; nA; nB; nC; nD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( upClient; dnClient; BFcHasBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA
  using ( upSrv; dnSrv )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleEvo blkA
  using ( BFsHasBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleIoEvo blkA
  using ( BlkReadAt; BundleGEvRio⁺; bgEBio⁺; absBundleG-io-evo )

------------------------------------------------------------------------
-- (1) THE TWO PER-PEER io CLASSIFIERS — the bundle result's two arms, named so
-- the per-node records can carry them.
------------------------------------------------------------------------

-- one BF CLIENT peer's io evolution, INDEXED BY THE PEER'S OWN KEY `(l,d)`:
-- fixed, or the successor is not holding a block, or the io was a BF wire READ
-- AT THAT KEY carrying a block.  The key index is load-bearing: the consumer
-- discharges `Coupled`'s client clause from the CELL clause, which reads the
-- medium at the LEG's own `(link,dir,BF)`, so the fired key has to be pinned.
CliIoCls : (l : Link) (d : Dir) → SN.BFcPos → SN.BFcPos
         → {X : Set 0ℓ} → Net_Api Payload X → X → Set
CliIoCls l d bfc bfc′ e a = (bfc ≡ bfc′) ⊎ ((BFcHasBlk bfc′ → ⊥) ⊎ BlkReadAt l d bfc′ e a)

-- one BF SERVER peer's io evolution: fixed, or the successor is not holding
SrvIoCls : SN.BFsPos → SN.BFsPos → Set
SrvIoCls bfs bfs′ = (bfs ≡ bfs′) ⊎ (BFsHasBlk bfs′ → ⊥)

------------------------------------------------------------------------
-- (1b) THE FACT INTERFACE — SESSION-52 IN-PLACE GENERALISATION (owner grant #1).
--
-- The four-node dispatch below is entirely INDEPENDENT of WHICH per-peer fact
-- the bundle layer reports: it only ever passes the fired slot's fact through
-- and puts `inj₁ refl` in the non-fired ones.  Both are recorded here as two
-- ABSTRACT predicates `Cf`/`Sf` plus the bundle dispatcher `bd` that delivers
-- them, exactly the `Cf`/`Sf` shape `PipeBundleIoEvo.absBundleBF-ev-io-evo`
-- (`:277-284`) already uses one layer down.  The ORIGINAL cone is re-derived
-- verbatim as the instance `top-nodes-io-evo = top-nodes-io-evoP facts₀`
-- (`Cf₀`/`Sf₀`/`bd₀` below), so `PipeTauIo` and `PipeValTauIo` — the only two
-- consumers, and they import `CliIoCls`/`SrvIoCls`/`AllCliIoCls`/`AllSrvIoCls`/
-- `top-nodes-io-evo` only — see NO change at all.  A caller that needs a
-- STRONGER per-peer fact (a PREDECESSOR-negative keep, or a positive hand-over)
-- instantiates the same dispatch with its own `Cf`/`Sf`.
------------------------------------------------------------------------

-- an abstract per-BF-CLIENT fact, at the peer's own key and the fired label
CliFact : Set₁
CliFact = (l : Link) (d : Dir) → SN.BFcPos → SN.BFcPos
        → {X : Set 0ℓ} → Net_Api Payload X → X → Set

-- an abstract per-BF-SERVER fact, at the peer's own key and the fired label
SrvFact : Set₁
SrvFact = (l : Link) (d : Dir) → SN.BFsPos → SN.BFsPos
        → {X : Set 0ℓ} → Net_Api Payload X → X → Set

-- an abstract per-BUNDLE INERT fact, at the bundle's own key — its link and its
-- CLIENT direction, which identify a bundle uniquely (`linkAB` carries node A's
-- `absBundleG linkAB lo hi` AND node B's `absBundleG linkAB hi lo`) — and the
-- fired label.  SESSION-56 (owner grant #6): the THIRD channel from the bundle
-- dispatcher to the top, added for exactly the reason §1b gives for `Cf`/`Sf`.
-- The eight `InertPos` slots are the system's only PERMANENTLY frozen peers (the
-- KA/TS/LN/LF client+server pairs: their rows are `apiXX`, which no driver ever
-- offers), so a caller proving a peer-level freeze invariant needs the fired
-- bundle's `ip`-fixity reported HERE, where the fired peer is decoded — the
-- successor `ip′` is bound existentially below and nothing downstream can
-- recover it (no slot injectivity anywhere in the tree).
--
-- *** (T5, review M-4) ERA-SCOPE THAT PARENTHESIS. ***  The REASON is sound and is
-- why this channel exists — and why grant #11's fourth family below was added on the
-- identical argument — but the wording is the ABSOLUTE one the T3/T4 reversal
-- refuted: coarse `tableSpec` POSITION injectivity IS derivable, and `LiveCSRow` §2/§3
-- proved it for both ChainSync tables (that is what the whole CS row layer rests on).
-- Read the parenthesis as scoped to the SLOTS of a bundle/node/group decomposition,
-- where it holds for a reason of its own — recovering one needs `_⦀_`/`_∥⇘⇙_`
-- injectivity and the tree has no such lemma — and never as a claim about tables.
InertFact : Set₁
InertFact = (l : Link) (cl : Dir) → SN.InertPos → SN.InertPos
          → {X : Set 0ℓ} → Net_Api Payload X → X → Set

-- (grant #11) an abstract per-CS-SERVER fact, at the peer's own key — its link and
-- its SERVER direction, which is where the bundle decodes it — and the fired label.
-- The CS servers are the fourth family this cone tracks; the header says why the
-- channel is the only place the fact can be reported.
CssFact : Set₁
CssFact = (l : Link) (sv : Dir) → SN.CSsPos → SN.CSsPos
        → {X : Set 0ℓ} → Net_Api Payload X → X → Set

-- (T6c, grant #12) … and the CS CLIENT mirror, at the bundle's own CLIENT
-- direction.  The fifth family, and the last one the ChainSync channel invariant's
-- join needs: `LiveChanCS.HopEvo`'s eight arms each name the non-mover, so the hop's
-- CLIENT slot has to travel beside its server's.
CscFact : Set₁
CscFact = (l : Link) (cl : Dir) → SN.CScPos → SN.CScPos
        → {X : Set 0ℓ} → Net_Api Payload X → X → Set

-- the bundle-level io evolution at abstract facts: the five successor slots, the
-- concrete weak run, one fact per BF slot, and (trailing, grant #6) the bundle's
-- own inert fact (the Σ form of `PipeBundleIoEvo.BundleGEvRio⁺`, so a caller can
-- supply its own dispatcher)
BundleEvo : (Cf : CliFact) (Sf : SrvFact) (If : InertFact) (Csf : CssFact)
            (Cscf : CscFact)
            (l : Link) (cl sv : Dir)
            (csc : SN.CScPos) (css : SN.CSsPos) (bfc : SN.BFcPos) (bfs : SN.BFsPos)
            (ip : SN.InertPos)
            {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) (Bd′ : NetProc) → Set₁
BundleEvo Cf Sf If Csf Cscf l cl sv csc css bfc bfs ip {X} e a Bd′ =
  Σ[ csc′ ∈ SN.CScPos ] Σ[ css′ ∈ SN.CSsPos ] Σ[ bfc′ ∈ SN.BFcPos ]
  Σ[ bfs′ ∈ SN.BFsPos ] Σ[ ip′ ∈ SN.InertPos ]
      (Bd′ ≡ absBundleG l cl sv csc′ css′ bfc′ bfs′ ip′)
    × (SN.bundleG l cl sv csc css bfc bfs ip
         ═[ ev (evl (evLabel X e a)) ]═► SN.bundleG l cl sv csc′ css′ bfc′ bfs′ ip′)
    × Cf l cl bfc bfc′ e a
    × Sf l sv bfs bfs′ e a
    × If l cl ip ip′ e a
    -- (grant #11) TRAILING: the bundle's CS SERVER, at its own `(l , sv)` key
    × Csf l sv css css′ e a
    -- (T6c, grant #12) TRAILING behind it: the bundle's CS CLIENT, at `(l , cl)`
    × Cscf l cl csc csc′ e a

-- CHANNEL OWNERSHIP, the FIXED-SLOT premise (session-53).  A per-peer fact that
-- IDENTIFIES THE READER — "if this io was a wire read on channel `id` at MY key
-- carrying a block then I now hold it" — is NOT free at a slot that did not move:
-- the reader could in principle be another peer holding the same key.  It is not,
-- and this predicate is the reason: on an `output` (a wire READ) the label is not
-- a CLIENT-role read on `id` at `(k , kd)`.  Every other label shape leaves the
-- reader-identifying fact vacuous, hence `⊤`.
--
-- *** (T6c) ERA-SCOPE THE `BF` IN THIS BLOCK. ***  Grant #12 made the predicate
-- `IDs`-PARAMETRIC (`id` is now an argument), so every "BF" below names the
-- ORIGINAL instantiation, not the predicate: at `id = N2N_BlockFetch` it is grant
-- #7's fact verbatim, and at `id = N2N_ChainSync` it is what the ChainSync channel
-- invariant's join uses to refute "the CS cell moved while both of the hop's peers
-- stayed fixed".  Read "BF wire read/write" as "wire read/write ON THE CHANNEL `id`".
-- Nothing about the ARGUMENT changed: the body never inspects the channel, which is
-- why the eight `-link`/`-role` witnesses and the eight per-node ones took the new
-- parameter IMPLICITLY with not one clause body edited.

NoCliReadAt : (k : Link) (kd : Dir) (id : IDs) {X : Set 0ℓ}
            → Net_Api Payload X → X → Set
NoCliReadAt k kd id (output l₀ d₀ id₀) x =
    (k ≡ l₀) → (kd ≡ d₀) → (id ≡ id₀)
  → ClientIo (output l₀ d₀ id₀) x → ⊥
NoCliReadAt k kd id _ _ = ⊤

-- OWNERSHIP BY LINK: a fire whose event carries another link is not a read at
-- `k`'s key at all (nine label shapes, eight of them vacuous)
noCliRead-link : (k : Link) (kd : Dir) {id : IDs} {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
                 {l₁ : Link}
  → ApiHasLink l₁ e → k ≢ l₁ → NoCliReadAt k kd id e a
noCliRead-link k kd ahlIn   ne = tt
noCliRead-link k kd ahlOut  ne = λ e1 _ _ _ → ne e1
noCliRead-link k kd ahlDone ne = tt
noCliRead-link k kd ahlCS   ne = tt
noCliRead-link k kd ahlBF   ne = tt
noCliRead-link k kd ahlKA   ne = tt
noCliRead-link k kd ahlTS   ne = tt
noCliRead-link k kd ahlLN   ne = tt
noCliRead-link k kd ahlLF   ne = tt

-- OWNERSHIP BY ROLE: within a bundle the SERVER end holds `(l , sv)` too, so the
-- link alone cannot settle `sv`.  What settles it is the bundle's own io
-- fingerprint: a client-role fire sits at `cl ≢ sv`, and a server-role fire
-- cannot ALSO be client-role (`client-server-excl`).  This is the arm that pays
-- for the leg's server sharing its client's read key.
noCliRead-role : (k : Link) (cl sv : Dir) → cl ≢ sv
  → {id : IDs} {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a → RoleFP cl sv e a → NoCliReadAt k sv id e a
noCliRead-role k cl sv cl≢sv {e = output l₀ d₀ id₀} iomem (inj₁ (dc , _)) =
  λ _ e2 _ _ → cl≢sv (sym (trans e2 dc))
noCliRead-role k cl sv cl≢sv {e = output l₀ d₀ id₀} {a = x} iomem (inj₂ (_ , si)) =
  λ _ _ _ ci → client-server-excl (output l₀ d₀ id₀) x iomem ci si
noCliRead-role k cl sv cl≢sv {e = input  _ _ _} iomem role = tt
noCliRead-role k cl sv cl≢sv {e = done   _ _ _} iomem role = tt
noCliRead-role k cl sv cl≢sv {e = apiCS  _ _ _} iomem role = tt
noCliRead-role k cl sv cl≢sv {e = apiBF  _ _ _} iomem role = tt
noCliRead-role k cl sv cl≢sv {e = apiKA  _ _ _} iomem role = tt
noCliRead-role k cl sv cl≢sv {e = apiTS  _ _ _} iomem role = tt
noCliRead-role k cl sv cl≢sv {e = apiLN  _ _ _} iomem role = tt
noCliRead-role k cl sv cl≢sv {e = apiLF  _ _ _} iomem role = tt
noCliRead-role k cl sv cl≢sv {e = sndmsg _ _ _} iomem role = tt
noCliRead-role k cl sv cl≢sv {e = rcvmsg _ _ _} iomem role = tt
noCliRead-role k cl sv cl≢sv {e = tx     _ _ _} iomem role = tt
noCliRead-role k cl sv cl≢sv {e = sndack _ _ _} iomem role = tt
noCliRead-role k cl sv cl≢sv {e = rcvack _ _ _} iomem role = tt
noCliRead-role k cl sv cl≢sv {e = ack    _ _ _} iomem role = tt
noCliRead-role k cl sv cl≢sv {e = break  _}     iomem role = tt

------------------------------------------------------------------------
-- (1b′) THE CLIENT-SIDE WRITE MIRROR (grant #7, the `ChanLeg` join's io arms).
--
-- §1b certifies a fixed client against a client-role READ at its key.  The io
-- class of the channel-invariant join needs the OTHER direction too: the leg's
-- cell is a SINGLE slot that BOTH peers write, so a cell FILL carrying an
-- INITIATOR payload is the CLIENT's request write — and refuting "the cell filled
-- while both of the hop's peers stayed fixed" is exactly what the invariant's
-- `cvReq` clause needs (it is FALSE at such a state, so the case has to be
-- refuted, not absorbed).  Both mirrors below are the read/write transpose of
-- §1b's pair; `ClientIo`/`ServerIo` are already stated for BOTH label shapes
-- (`SysIoLink:2471-2481`), so nothing else changes.
------------------------------------------------------------------------

-- the fixed CLIENT slot's ownership premise on the WRITE direction: this io is no
-- client-role wire WRITE on channel `id` at `(k , kd)`.  (T6c: `id`-parametric —
-- see the `NoCliReadAt` block's era-scope note.)
NoCliWriteAt : (k : Link) (kd : Dir) (id : IDs) {X : Set 0ℓ}
             → Net_Api Payload X → X → Set
NoCliWriteAt k kd id (input l₀ d₀ id₀) x =
    (k ≡ l₀) → (kd ≡ d₀) → (id ≡ id₀)
  → ClientIo (input l₀ d₀ id₀) x → ⊥
NoCliWriteAt k kd id _ _ = ⊤

-- OWNERSHIP BY LINK (the `input` transpose of `noCliRead-link`)
noCliWrite-link : (k : Link) (kd : Dir) {id : IDs} {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
                  {l₁ : Link}
  → ApiHasLink l₁ e → k ≢ l₁ → NoCliWriteAt k kd id e a
noCliWrite-link k kd ahlIn   ne = λ e1 _ _ _ → ne e1
noCliWrite-link k kd ahlOut  ne = tt
noCliWrite-link k kd ahlDone ne = tt
noCliWrite-link k kd ahlCS   ne = tt
noCliWrite-link k kd ahlBF   ne = tt
noCliWrite-link k kd ahlKA   ne = tt
noCliWrite-link k kd ahlTS   ne = tt
noCliWrite-link k kd ahlLN   ne = tt
noCliWrite-link k kd ahlLF   ne = tt

-- OWNERSHIP BY ROLE (the `input` transpose of `noCliRead-role`)
noCliWrite-role : (k : Link) (cl sv : Dir) → cl ≢ sv
  → {id : IDs} {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a → RoleFP cl sv e a → NoCliWriteAt k sv id e a
noCliWrite-role k cl sv cl≢sv {e = input l₀ d₀ id₀} iomem (inj₁ (dc , _)) =
  λ _ e2 _ _ → cl≢sv (sym (trans e2 dc))
noCliWrite-role k cl sv cl≢sv {e = input l₀ d₀ id₀} {a = x} iomem (inj₂ (_ , si)) =
  λ _ _ _ ci → client-server-excl (input l₀ d₀ id₀) x iomem ci si
noCliWrite-role k cl sv cl≢sv {e = output _ _ _} iomem role = tt
noCliWrite-role k cl sv cl≢sv {e = done   _ _ _} iomem role = tt
noCliWrite-role k cl sv cl≢sv {e = apiCS  _ _ _} iomem role = tt
noCliWrite-role k cl sv cl≢sv {e = apiBF  _ _ _} iomem role = tt
noCliWrite-role k cl sv cl≢sv {e = apiKA  _ _ _} iomem role = tt
noCliWrite-role k cl sv cl≢sv {e = apiTS  _ _ _} iomem role = tt
noCliWrite-role k cl sv cl≢sv {e = apiLN  _ _ _} iomem role = tt
noCliWrite-role k cl sv cl≢sv {e = apiLF  _ _ _} iomem role = tt
noCliWrite-role k cl sv cl≢sv {e = sndmsg _ _ _} iomem role = tt
noCliWrite-role k cl sv cl≢sv {e = rcvmsg _ _ _} iomem role = tt
noCliWrite-role k cl sv cl≢sv {e = tx     _ _ _} iomem role = tt
noCliWrite-role k cl sv cl≢sv {e = sndack _ _ _} iomem role = tt
noCliWrite-role k cl sv cl≢sv {e = rcvack _ _ _} iomem role = tt
noCliWrite-role k cl sv cl≢sv {e = ack    _ _ _} iomem role = tt
noCliWrite-role k cl sv cl≢sv {e = break  _}     iomem role = tt

-- the fixed CLIENT slot's ownership premise, BOTH directions (the pair the cone's
-- `cRefl` now hands over)
NoCliIoAt : (k : Link) (kd : Dir) (id : IDs) {X : Set 0ℓ}
          → Net_Api Payload X → X → Set
NoCliIoAt k kd id e a = NoCliReadAt k kd id e a × NoCliWriteAt k kd id e a

-- the four tracked clients' ownership premises when NODE A fires (both of A's
-- bundles put A at the SERVER end, so A's own two keys go by role)
noCliA : {id : IDs} {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} → ioES .mem (X , e) a
  → (ApiHasLink linkAB e × RoleFP lo hi e a) ⊎ (ApiHasLink linkAC e × RoleFP lo hi e a)
  → NoCliIoAt linkAB hi id e a × NoCliIoAt linkAC hi id e a
      × NoCliIoAt linkBD hi id e a × NoCliIoAt linkCD hi id e a
noCliA iomem (inj₁ (ahl , role)) =
    (noCliRead-role linkAB lo hi lo≢hi iomem role , noCliWrite-role linkAB lo hi lo≢hi iomem role)
  , (noCliRead-link linkAC hi ahl (λ q → linkAB≢linkAC (sym q)) , noCliWrite-link linkAC hi ahl (λ q → linkAB≢linkAC (sym q)))
  , (noCliRead-link linkBD hi ahl (λ q → linkAB≢linkBD (sym q)) , noCliWrite-link linkBD hi ahl (λ q → linkAB≢linkBD (sym q)))
  , (noCliRead-link linkCD hi ahl (λ q → linkAB≢linkCD (sym q)) , noCliWrite-link linkCD hi ahl (λ q → linkAB≢linkCD (sym q)))
noCliA iomem (inj₂ (ahl , role)) =
    (noCliRead-link linkAB hi ahl linkAB≢linkAC , noCliWrite-link linkAB hi ahl linkAB≢linkAC)
  , (noCliRead-role linkAC lo hi lo≢hi iomem role , noCliWrite-role linkAC lo hi lo≢hi iomem role)
  , (noCliRead-link linkBD hi ahl (λ q → linkAC≢linkBD (sym q)) , noCliWrite-link linkBD hi ahl (λ q → linkAC≢linkBD (sym q)))
  , (noCliRead-link linkCD hi ahl (λ q → linkAC≢linkCD (sym q)) , noCliWrite-link linkCD hi ahl (λ q → linkAC≢linkCD (sym q)))

-- ditto when NODE B fires (B is the CLIENT on AB — that slot is the fired one
-- and needs no premise — and the SERVER on BD, so `linkBD` goes by role)
noCliB : {id : IDs} {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} → ioES .mem (X , e) a
  → (ApiHasLink linkAB e × RoleFP hi lo e a) ⊎ (ApiHasLink linkBD e × RoleFP lo hi e a)
  → NoCliIoAt linkAC hi id e a × NoCliIoAt linkBD hi id e a × NoCliIoAt linkCD hi id e a
noCliB iomem (inj₁ (ahl , role)) =
    (noCliRead-link linkAC hi ahl (λ q → linkAB≢linkAC (sym q)) , noCliWrite-link linkAC hi ahl (λ q → linkAB≢linkAC (sym q)))
  , (noCliRead-link linkBD hi ahl (λ q → linkAB≢linkBD (sym q)) , noCliWrite-link linkBD hi ahl (λ q → linkAB≢linkBD (sym q)))
  , (noCliRead-link linkCD hi ahl (λ q → linkAB≢linkCD (sym q)) , noCliWrite-link linkCD hi ahl (λ q → linkAB≢linkCD (sym q)))
noCliB iomem (inj₂ (ahl , role)) =
    (noCliRead-link linkAC hi ahl linkAC≢linkBD , noCliWrite-link linkAC hi ahl linkAC≢linkBD)
  , (noCliRead-role linkBD lo hi lo≢hi iomem role , noCliWrite-role linkBD lo hi lo≢hi iomem role)
  , (noCliRead-link linkCD hi ahl (λ q → linkBD≢linkCD (sym q)) , noCliWrite-link linkCD hi ahl (λ q → linkBD≢linkCD (sym q)))

-- ditto when NODE C fires (mirror of B on leg CD)
noCliC : {id : IDs} {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} → ioES .mem (X , e) a
  → (ApiHasLink linkAC e × RoleFP hi lo e a) ⊎ (ApiHasLink linkCD e × RoleFP lo hi e a)
  → NoCliIoAt linkAB hi id e a × NoCliIoAt linkBD hi id e a × NoCliIoAt linkCD hi id e a
noCliC iomem (inj₁ (ahl , role)) =
    (noCliRead-link linkAB hi ahl linkAB≢linkAC , noCliWrite-link linkAB hi ahl linkAB≢linkAC)
  , (noCliRead-link linkBD hi ahl (λ q → linkAC≢linkBD (sym q)) , noCliWrite-link linkBD hi ahl (λ q → linkAC≢linkBD (sym q)))
  , (noCliRead-link linkCD hi ahl (λ q → linkAC≢linkCD (sym q)) , noCliWrite-link linkCD hi ahl (λ q → linkAC≢linkCD (sym q)))
noCliC iomem (inj₂ (ahl , role)) =
    (noCliRead-link linkAB hi ahl linkAB≢linkCD , noCliWrite-link linkAB hi ahl linkAB≢linkCD)
  , (noCliRead-link linkBD hi ahl linkBD≢linkCD , noCliWrite-link linkBD hi ahl linkBD≢linkCD)
  , (noCliRead-role linkCD lo hi lo≢hi iomem role , noCliWrite-role linkCD lo hi lo≢hi iomem role)

-- ditto when NODE D fires (D is the CLIENT on both its links, so BOTH its slots
-- are fired-or-co-located and only the two upstream keys need a premise)
noCliD : {id : IDs} {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} → ioES .mem (X , e) a
  → (ApiHasLink linkBD e × RoleFP hi lo e a) ⊎ (ApiHasLink linkCD e × RoleFP hi lo e a)
  → NoCliIoAt linkAB hi id e a × NoCliIoAt linkAC hi id e a
noCliD iomem (inj₁ (ahl , role)) =
    (noCliRead-link linkAB hi ahl linkAB≢linkBD , noCliWrite-link linkAB hi ahl linkAB≢linkBD)
  , (noCliRead-link linkAC hi ahl linkAC≢linkBD , noCliWrite-link linkAC hi ahl linkAC≢linkBD)
noCliD iomem (inj₂ (ahl , role)) =
    (noCliRead-link linkAB hi ahl linkAB≢linkCD , noCliWrite-link linkAB hi ahl linkAB≢linkCD)
  , (noCliRead-link linkAC hi ahl linkAC≢linkCD , noCliWrite-link linkAC hi ahl linkAC≢linkCD)

------------------------------------------------------------------------
-- (1c) CHANNEL OWNERSHIP, THE SERVER MIRROR (session-55, `LiveTokenExcl` P2).
--
-- The exact mirror of §1b's client block, for the WRITE direction.  A per-peer
-- fact that IDENTIFIES THE WRITER — "if this io was a wire WRITE on channel `id` at
-- MY key carrying a block then I HELD that block and no longer do" — is NOT free at
-- a slot that did not move: the writer could in principle be another peer holding
-- the same key.  It is not, and this predicate is the reason: on an `input` (a
-- wire WRITE) the label is not a SERVER-role write on `id` at `(k , kd)`.  Every
-- other label shape leaves the writer-identifying fact vacuous, hence `⊤`.
--
-- (T6c: `id`-parametric — see the `NoCliReadAt` block's era-scope note.  The
-- ChainSync instantiation of THIS predicate and its client twin are what
-- `LiveChanJoinCS`'s io arms refute *(neither CS peer moved)* with.)
------------------------------------------------------------------------

-- the fixed SERVER slot's ownership premise: this io is no server-role wire
-- write on channel `id` at `(k , kd)`
NoSrvWriteAt : (k : Link) (kd : Dir) (id : IDs) {X : Set 0ℓ}
             → Net_Api Payload X → X → Set
NoSrvWriteAt k kd id (input l₀ d₀ id₀) x =
    (k ≡ l₀) → (kd ≡ d₀) → (id ≡ id₀)
  → ServerIo (input l₀ d₀ id₀) x → ⊥
NoSrvWriteAt k kd id _ _ = ⊤

-- OWNERSHIP BY LINK: a fire whose event carries another link is not a write at
-- `k`'s key at all (nine label shapes, eight of them vacuous — the `input` one
-- is where the mirror differs from `noCliRead-link`'s `output`)
noSrvWrite-link : (k : Link) (kd : Dir) {id : IDs} {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
                  {l₁ : Link}
  → ApiHasLink l₁ e → k ≢ l₁ → NoSrvWriteAt k kd id e a
noSrvWrite-link k kd ahlIn   ne = λ e1 _ _ _ → ne e1
noSrvWrite-link k kd ahlOut  ne = tt
noSrvWrite-link k kd ahlDone ne = tt
noSrvWrite-link k kd ahlCS   ne = tt
noSrvWrite-link k kd ahlBF   ne = tt
noSrvWrite-link k kd ahlKA   ne = tt
noSrvWrite-link k kd ahlTS   ne = tt
noSrvWrite-link k kd ahlLN   ne = tt
noSrvWrite-link k kd ahlLF   ne = tt

-- OWNERSHIP BY ROLE: within a bundle the CLIENT end holds `(l , cl)` too, so the
-- link alone cannot settle `cl` — and a tracked SERVER's key is exactly the
-- CLIENT direction of the OTHER node's bundle on that link.  What settles it is
-- the bundle's own io fingerprint: a server-role fire sits at `sv ≢ cl`, and a
-- client-role fire cannot ALSO be server-role (`client-server-excl`).
noSrvWrite-role : (k : Link) (cl sv : Dir) → cl ≢ sv
  → {id : IDs} {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a → RoleFP cl sv e a → NoSrvWriteAt k cl id e a
noSrvWrite-role k cl sv cl≢sv {e = input l₀ d₀ id₀} {a = x} iomem (inj₁ (_ , ci)) =
  λ _ _ _ si → client-server-excl (input l₀ d₀ id₀) x iomem ci si
noSrvWrite-role k cl sv cl≢sv {e = input l₀ d₀ id₀} iomem (inj₂ (ds , _)) =
  λ _ e2 _ _ → cl≢sv (trans e2 ds)
noSrvWrite-role k cl sv cl≢sv {e = output _ _ _} iomem role = tt
noSrvWrite-role k cl sv cl≢sv {e = done   _ _ _} iomem role = tt
noSrvWrite-role k cl sv cl≢sv {e = apiCS  _ _ _} iomem role = tt
noSrvWrite-role k cl sv cl≢sv {e = apiBF  _ _ _} iomem role = tt
noSrvWrite-role k cl sv cl≢sv {e = apiKA  _ _ _} iomem role = tt
noSrvWrite-role k cl sv cl≢sv {e = apiTS  _ _ _} iomem role = tt
noSrvWrite-role k cl sv cl≢sv {e = apiLN  _ _ _} iomem role = tt
noSrvWrite-role k cl sv cl≢sv {e = apiLF  _ _ _} iomem role = tt
noSrvWrite-role k cl sv cl≢sv {e = sndmsg _ _ _} iomem role = tt
noSrvWrite-role k cl sv cl≢sv {e = rcvmsg _ _ _} iomem role = tt
noSrvWrite-role k cl sv cl≢sv {e = tx     _ _ _} iomem role = tt
noSrvWrite-role k cl sv cl≢sv {e = sndack _ _ _} iomem role = tt
noSrvWrite-role k cl sv cl≢sv {e = rcvack _ _ _} iomem role = tt
noSrvWrite-role k cl sv cl≢sv {e = ack    _ _ _} iomem role = tt
noSrvWrite-role k cl sv cl≢sv {e = break  _}     iomem role = tt

-- (grant #7) the fixed SERVER slot's ownership premise on the READ direction: this
-- io is no server-role wire READ on channel `id` at `(k , kd)`.  (T6c:
-- `id`-parametric — see the `NoCliReadAt` block's era-scope note.)  The transpose of
-- `NoSrvWriteAt`, needed for the same reason its client twin is (a cell holding an
-- INITIATOR payload is read by the SERVER, so a drain at a hop whose peers both
-- stayed fixed has to be refutable)
NoSrvReadAt : (k : Link) (kd : Dir) (id : IDs) {X : Set 0ℓ}
            → Net_Api Payload X → X → Set
NoSrvReadAt k kd id (output l₀ d₀ id₀) x =
    (k ≡ l₀) → (kd ≡ d₀) → (id ≡ id₀)
  → ServerIo (output l₀ d₀ id₀) x → ⊥
NoSrvReadAt k kd id _ _ = ⊤

-- OWNERSHIP BY LINK (the `output` transpose of `noSrvWrite-link`)
noSrvRead-link : (k : Link) (kd : Dir) {id : IDs} {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
                 {l₁ : Link}
  → ApiHasLink l₁ e → k ≢ l₁ → NoSrvReadAt k kd id e a
noSrvRead-link k kd ahlIn   ne = tt
noSrvRead-link k kd ahlOut  ne = λ e1 _ _ _ → ne e1
noSrvRead-link k kd ahlDone ne = tt
noSrvRead-link k kd ahlCS   ne = tt
noSrvRead-link k kd ahlBF   ne = tt
noSrvRead-link k kd ahlKA   ne = tt
noSrvRead-link k kd ahlTS   ne = tt
noSrvRead-link k kd ahlLN   ne = tt
noSrvRead-link k kd ahlLF   ne = tt

-- OWNERSHIP BY ROLE (the `output` transpose of `noSrvWrite-role`)
noSrvRead-role : (k : Link) (cl sv : Dir) → cl ≢ sv
  → {id : IDs} {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a → RoleFP cl sv e a → NoSrvReadAt k cl id e a
noSrvRead-role k cl sv cl≢sv {e = output l₀ d₀ id₀} {a = x} iomem (inj₁ (_ , ci)) =
  λ _ _ _ si → client-server-excl (output l₀ d₀ id₀) x iomem ci si
noSrvRead-role k cl sv cl≢sv {e = output l₀ d₀ id₀} iomem (inj₂ (ds , _)) =
  λ _ e2 _ _ → cl≢sv (trans e2 ds)
noSrvRead-role k cl sv cl≢sv {e = input  _ _ _} iomem role = tt
noSrvRead-role k cl sv cl≢sv {e = done   _ _ _} iomem role = tt
noSrvRead-role k cl sv cl≢sv {e = apiCS  _ _ _} iomem role = tt
noSrvRead-role k cl sv cl≢sv {e = apiBF  _ _ _} iomem role = tt
noSrvRead-role k cl sv cl≢sv {e = apiKA  _ _ _} iomem role = tt
noSrvRead-role k cl sv cl≢sv {e = apiTS  _ _ _} iomem role = tt
noSrvRead-role k cl sv cl≢sv {e = apiLN  _ _ _} iomem role = tt
noSrvRead-role k cl sv cl≢sv {e = apiLF  _ _ _} iomem role = tt
noSrvRead-role k cl sv cl≢sv {e = sndmsg _ _ _} iomem role = tt
noSrvRead-role k cl sv cl≢sv {e = rcvmsg _ _ _} iomem role = tt
noSrvRead-role k cl sv cl≢sv {e = tx     _ _ _} iomem role = tt
noSrvRead-role k cl sv cl≢sv {e = sndack _ _ _} iomem role = tt
noSrvRead-role k cl sv cl≢sv {e = rcvack _ _ _} iomem role = tt
noSrvRead-role k cl sv cl≢sv {e = ack    _ _ _} iomem role = tt
noSrvRead-role k cl sv cl≢sv {e = break  _}     iomem role = tt

-- the fixed SERVER slot's ownership premise, BOTH directions (the pair `sRefl` now
-- hands over)
NoSrvIoAt : (k : Link) (kd : Dir) (id : IDs) {X : Set 0ℓ}
          → Net_Api Payload X → X → Set
NoSrvIoAt k kd id e a = NoSrvWriteAt k kd id e a × NoSrvReadAt k kd id e a

-- the two tracked servers node A does NOT own, when NODE A fires (both of A's
-- bundles put A at the server end, and both downstream servers sit on OTHER links)
noSrvA : {id : IDs} {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} → ioES .mem (X , e) a
  → (ApiHasLink linkAB e × RoleFP lo hi e a) ⊎ (ApiHasLink linkAC e × RoleFP lo hi e a)
  → NoSrvIoAt linkBD hi id e a × NoSrvIoAt linkCD hi id e a
noSrvA iomem (inj₁ (ahl , role)) =
    (noSrvWrite-link linkBD hi ahl (λ q → linkAB≢linkBD (sym q)) , noSrvRead-link linkBD hi ahl (λ q → linkAB≢linkBD (sym q)))
  , (noSrvWrite-link linkCD hi ahl (λ q → linkAB≢linkCD (sym q)) , noSrvRead-link linkCD hi ahl (λ q → linkAB≢linkCD (sym q)))
noSrvA iomem (inj₂ (ahl , role)) =
    (noSrvWrite-link linkBD hi ahl (λ q → linkAC≢linkBD (sym q)) , noSrvRead-link linkBD hi ahl (λ q → linkAC≢linkBD (sym q)))
  , (noSrvWrite-link linkCD hi ahl (λ q → linkAC≢linkCD (sym q)) , noSrvRead-link linkCD hi ahl (λ q → linkAC≢linkCD (sym q)))

-- ditto when NODE B fires (on link AB node B is the CLIENT at `hi`, which is
-- exactly node A's tracked server key — that slot goes by ROLE)
noSrvB : {id : IDs} {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} → ioES .mem (X , e) a
  → (ApiHasLink linkAB e × RoleFP hi lo e a) ⊎ (ApiHasLink linkBD e × RoleFP lo hi e a)
  → NoSrvIoAt linkAB hi id e a × NoSrvIoAt linkAC hi id e a × NoSrvIoAt linkCD hi id e a
noSrvB iomem (inj₁ (ahl , role)) =
    (noSrvWrite-role linkAB hi lo (λ q → lo≢hi (sym q)) iomem role , noSrvRead-role linkAB hi lo (λ q → lo≢hi (sym q)) iomem role)
  , (noSrvWrite-link linkAC hi ahl (λ q → linkAB≢linkAC (sym q)) , noSrvRead-link linkAC hi ahl (λ q → linkAB≢linkAC (sym q)))
  , (noSrvWrite-link linkCD hi ahl (λ q → linkAB≢linkCD (sym q)) , noSrvRead-link linkCD hi ahl (λ q → linkAB≢linkCD (sym q)))
noSrvB iomem (inj₂ (ahl , role)) =
    (noSrvWrite-link linkAB hi ahl linkAB≢linkBD , noSrvRead-link linkAB hi ahl linkAB≢linkBD)
  , (noSrvWrite-link linkAC hi ahl linkAC≢linkBD , noSrvRead-link linkAC hi ahl linkAC≢linkBD)
  , (noSrvWrite-link linkCD hi ahl (λ q → linkBD≢linkCD (sym q)) , noSrvRead-link linkCD hi ahl (λ q → linkBD≢linkCD (sym q)))

-- ditto when NODE C fires (mirror of B on leg CD)
noSrvC : {id : IDs} {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} → ioES .mem (X , e) a
  → (ApiHasLink linkAC e × RoleFP hi lo e a) ⊎ (ApiHasLink linkCD e × RoleFP lo hi e a)
  → NoSrvIoAt linkAB hi id e a × NoSrvIoAt linkAC hi id e a × NoSrvIoAt linkBD hi id e a
noSrvC iomem (inj₁ (ahl , role)) =
    (noSrvWrite-link linkAB hi ahl linkAB≢linkAC , noSrvRead-link linkAB hi ahl linkAB≢linkAC)
  , (noSrvWrite-role linkAC hi lo (λ q → lo≢hi (sym q)) iomem role , noSrvRead-role linkAC hi lo (λ q → lo≢hi (sym q)) iomem role)
  , (noSrvWrite-link linkBD hi ahl (λ q → linkAC≢linkBD (sym q)) , noSrvRead-link linkBD hi ahl (λ q → linkAC≢linkBD (sym q)))
noSrvC iomem (inj₂ (ahl , role)) =
    (noSrvWrite-link linkAB hi ahl linkAB≢linkCD , noSrvRead-link linkAB hi ahl linkAB≢linkCD)
  , (noSrvWrite-link linkAC hi ahl linkAC≢linkCD , noSrvRead-link linkAC hi ahl linkAC≢linkCD)
  , (noSrvWrite-link linkBD hi ahl linkBD≢linkCD , noSrvRead-link linkBD hi ahl linkBD≢linkCD)

-- ditto when NODE D fires (D is the CLIENT at `hi` on both its links, so the
-- fired link's own relay server goes by ROLE and the other three by LINK)
noSrvD : {id : IDs} {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} → ioES .mem (X , e) a
  → (ApiHasLink linkBD e × RoleFP hi lo e a) ⊎ (ApiHasLink linkCD e × RoleFP hi lo e a)
  → NoSrvIoAt linkAB hi id e a × NoSrvIoAt linkAC hi id e a
      × NoSrvIoAt linkBD hi id e a × NoSrvIoAt linkCD hi id e a
noSrvD iomem (inj₁ (ahl , role)) =
    (noSrvWrite-link linkAB hi ahl linkAB≢linkBD , noSrvRead-link linkAB hi ahl linkAB≢linkBD)
  , (noSrvWrite-link linkAC hi ahl linkAC≢linkBD , noSrvRead-link linkAC hi ahl linkAC≢linkBD)
  , (noSrvWrite-role linkBD hi lo (λ q → lo≢hi (sym q)) iomem role , noSrvRead-role linkBD hi lo (λ q → lo≢hi (sym q)) iomem role)
  , (noSrvWrite-link linkCD hi ahl (λ q → linkBD≢linkCD (sym q)) , noSrvRead-link linkCD hi ahl (λ q → linkBD≢linkCD (sym q)))
noSrvD iomem (inj₂ (ahl , role)) =
    (noSrvWrite-link linkAB hi ahl linkAB≢linkCD , noSrvRead-link linkAB hi ahl linkAB≢linkCD)
  , (noSrvWrite-link linkAC hi ahl linkAC≢linkCD , noSrvRead-link linkAC hi ahl linkAC≢linkCD)
  , (noSrvWrite-link linkBD hi ahl linkBD≢linkCD , noSrvRead-link linkBD hi ahl linkBD≢linkCD)
  , (noSrvWrite-role linkCD hi lo (λ q → lo≢hi (sym q)) iomem role , noSrvRead-role linkCD hi lo (λ q → lo≢hi (sym q)) iomem role)

-- the io cone's fact interface: the two per-peer facts and their dispatcher
record IoFacts : Set₂ where
  field
    Cf : CliFact
    Sf : SrvFact
    If : InertFact
    -- (grant #11) the fourth family.  INSERTED here rather than appended, because
    -- `bd` below mentions it; a record is by NAME, so no reader can be shifted.
    Csf : CssFact
    -- (T6c, grant #12) the fifth family, inserted beside `Csf` for its reason
    Cscf : CscFact
    bd : (l : Link) (cl sv : Dir) → cl ≢ sv
       → (csc : SN.CScPos) (css : SN.CSsPos) (bfc : SN.BFcPos) (bfs : SN.BFsPos)
         (ip : SN.InertPos)
       → {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
       → ioES .mem (X , e) a
       → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X e a)) ]─► Bd′
       → BundleEvo Cf Sf If Csf Cscf l cl sv csc css bfc bfs ip e a Bd′
    -- the FIXED-SLOT witnesses.  Every non-fired peer is a LITERAL in the
    -- successor node record, so the dispatch needs each fact to hold of a slot
    -- that did not move; at the frozen classifiers this is `inj₁ refl`.
    -- SESSION-53: `cRefl` now takes the fixed slot's OWNERSHIP premise.  At the
    -- frozen classifiers it is ignored; at an instance whose client fact
    -- IDENTIFIES THE READER it is exactly what makes the fixed slot's answer
    -- true (see `NoCliReadAt` above).
    cRefl : (l : Link) (d : Dir) (bfc : SN.BFcPos)
            {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
          → NoCliIoAt l d N2N_BlockFetch e a → Cf l d bfc bfc e a
    -- SESSION-55: `sRefl` now takes the fixed slot's OWNERSHIP premise too, the
    -- exact mirror of `cRefl`'s.  At the frozen classifiers it is ignored; at an
    -- instance whose server fact IDENTIFIES THE WRITER it is what makes the fixed
    -- slot's answer true (see `NoSrvWriteAt` above).
    sRefl : (l : Link) (d : Dir) (bfs : SN.BFsPos)
            {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
          → NoSrvIoAt l d N2N_BlockFetch e a → Sf l d bfs bfs e a
    -- SESSION-56 (grant #6): the inert family's FIXED-SLOT witness.  A bundle
    -- that did not fire keeps its `InertPos` LITERALLY in the successor node
    -- record, so — unlike `cRefl`/`sRefl`, whose facts identify a reader/writer
    -- and therefore need an ownership premise — this one needs NO premise at any
    -- instance: the slot is the same term on both sides.
    iRefl : (l : Link) (cl : Dir) (ip : SN.InertPos)
            {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
          → If l cl ip ip e a
    -- (grant #11) the CS-server family's fixed-slot witness — PREMISE-FREE, for
    -- `iRefl`'s reason and not `cRefl`/`sRefl`'s: a CS server that did not fire is
    -- the SAME term in the successor node record, and the fact identifies neither a
    -- reader nor a writer, so there is nothing to own
    -- (T6c, grant #12) … and it can no longer be premise-free: the join's io arms
    -- must refute "the CS cell filled while BOTH of the hop's peers stayed fixed",
    -- and two fixities are not a contradiction — the hop's two peers share the key
    -- `(link , hi)`, so only the payload's ROLE separates them.  This is grant #7's
    -- argument at the ChainSync channel, which is why the four ownership predicates
    -- above are now `IDs`-parametric rather than mirrored.
    csRefl : (l : Link) (sv : Dir) (css : SN.CSsPos)
             {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
           → NoSrvIoAt l sv N2N_ChainSync e a → Csf l sv css css e a
    -- (T6c, grant #12) the CS CLIENT family's fixed-slot witness, the exact mirror
    cscRefl : (l : Link) (cl : Dir) (csc : SN.CScPos)
              {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
            → NoCliIoAt l cl N2N_ChainSync e a → Cscf l cl csc csc e a
open IoFacts public

------------------------------------------------------------------------
-- (2) PER-NODE io PEEL RECORDS.  Each carries the CONCRETE successor node, the
-- concrete weak run, the tracked clients' `CliIoCls`, the tracked servers'
-- `SrvIoCls` and the node's driver fixities.
------------------------------------------------------------------------

-- node A hosts the TWO upstream BF servers (bfS-AB, bfS-AC) and both producers
data NodeAEvR-io (F : IoFacts) (na : SN.NodeStateA) {X : Set 0ℓ}
                 (e : Net_Api Payload X) (a : X)
                 (M : NetProc) : Set₁ where
  naEBio : (na′ : SN.NodeStateA) → M ≡ absNodeA na′
        → SN.decNodeA na ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeA na′
        → Sf F linkAB hi (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.bfS-AB na′) e a
        → Sf F linkAC hi (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.bfS-AC na′) e a
        → SN.NodeStateA.prod-AB na ≡ SN.NodeStateA.prod-AB na′
        → SN.NodeStateA.prod-AC na ≡ SN.NodeStateA.prod-AC na′
        -- grant #6: A's two bundles' inert facts (A is the CLIENT at `lo` in both)
        → If F linkAB lo (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AB na′) e a
        → If F linkAC lo (SN.NodeStateA.inert-AC na) (SN.NodeStateA.inert-AC na′) e a
        -- (T6c, grant #12) TRAILING: node A hosts BOTH UP-HOP CS SERVERS, at its two
        -- bundles' `sv`.  Grant #11 gave node A no CS slot at all.
        → Csf F linkAB hi (SN.NodeStateA.csS-AB na) (SN.NodeStateA.csS-AB na′) e a
        → Csf F linkAC hi (SN.NodeStateA.csS-AC na) (SN.NodeStateA.csS-AC na′) e a
        → NodeAEvR-io F na e a M

-- node B hosts the upstream client of leg BD (bfC-AB) and its downstream
-- server (bfS-BD), plus the relay driver
data NodeBEvR-io (F : IoFacts) (nb : SN.NodeStateB) {X : Set 0ℓ}
                 (e : Net_Api Payload X) (a : X)
                 (M : NetProc) : Set₁ where
  nbEBio : (nb′ : SN.NodeStateB) → M ≡ absNodeB nb′
        → SN.decNodeB nb ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeB nb′
        → Cf F linkAB hi (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfC-AB nb′) e a
        → Sf F linkBD hi (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.bfS-BD nb′) e a
        → SN.NodeStateB.cp-B nb ≡ SN.NodeStateB.cp-B nb′
        -- grant #6: B's two bundles (CLIENT at `hi` on AB, at `lo` on BD)
        → If F linkAB hi (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-AB nb′) e a
        → If F linkBD lo (SN.NodeStateB.inert-BD nb) (SN.NodeStateB.inert-BD nb′) e a
        -- (grant #11) TRAILING: B hosts leg BD's tracked CS SERVER (`dnCSs legBD`)
        → Csf F linkBD hi (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.csS-BD nb′) e a
        -- (T6c, grant #12) TRAILING: B hosts leg BD's UP-hop CS CLIENT, at its AB
        -- bundle's `cl` (`LiveChanCS.upCScOf legBD`)
        → Cscf F linkAB hi (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csC-AB nb′) e a
        → NodeBEvR-io F nb e a M

-- node C mirrors node B on leg CD
data NodeCEvR-io (F : IoFacts) (nc : SN.NodeStateC) {X : Set 0ℓ}
                 (e : Net_Api Payload X) (a : X)
                 (M : NetProc) : Set₁ where
  ncEBio : (nc′ : SN.NodeStateC) → M ≡ absNodeC nc′
        → SN.decNodeC nc ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeC nc′
        → Cf F linkAC hi (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfC-AC nc′) e a
        → Sf F linkCD hi (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.bfS-CD nc′) e a
        → SN.NodeStateC.cp-C nc ≡ SN.NodeStateC.cp-C nc′
        -- grant #6: C's two bundles (CLIENT at `hi` on AC, at `lo` on CD)
        → If F linkAC hi (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-AC nc′) e a
        → If F linkCD lo (SN.NodeStateC.inert-CD nc) (SN.NodeStateC.inert-CD nc′) e a
        -- (grant #11) TRAILING: C hosts leg CD's tracked CS SERVER (`dnCSs legCD`)
        → Csf F linkCD hi (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.csS-CD nc′) e a
        -- (T6c, grant #12) TRAILING: the leg-CD mirror
        → Cscf F linkAC hi (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csC-AC nc′) e a
        → NodeCEvR-io F nc e a M

-- node D hosts the TWO downstream clients (bfC-BD, bfC-CD) and both consumers
data NodeDEvR-io (F : IoFacts) (nd : SN.NodeStateD) {X : Set 0ℓ}
                 (e : Net_Api Payload X) (a : X)
                 (M : NetProc) : Set₁ where
  ndEBio : (nd′ : SN.NodeStateD) → M ≡ absNodeD nd′
        → SN.decNodeD nd ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeD nd′
        → Cf F linkBD hi (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfC-BD nd′) e a
        → Cf F linkCD hi (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfC-CD nd′) e a
        → SN.NodeStateD.cons-BD nd ≡ SN.NodeStateD.cons-BD nd′
        → SN.NodeStateD.cons-CD nd ≡ SN.NodeStateD.cons-CD nd′
        -- grant #6: D's two bundles (D is the CLIENT at `hi` in both)
        → If F linkBD hi (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-BD nd′) e a
        → If F linkCD hi (SN.NodeStateD.inert-CD nd) (SN.NodeStateD.inert-CD nd′) e a
        -- (T6c, grant #12) TRAILING: node D hosts BOTH DOWN-HOP CS CLIENTS, at its two
        -- bundles' `cl`.  These are the two slots the `pp2` arm's own hop needs.
        → Cscf F linkBD hi (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csC-BD nd′) e a
        → Cscf F linkCD hi (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csC-CD nd′) e a
        → NodeDEvR-io F nd e a M

------------------------------------------------------------------------
-- (3) NODE A (re-mirror of `WalkConvNodeFix.nodeA-io-{AB,AC}-abs-fix`, whose
-- result drops both server slots).  A's two bundles put A at the SERVER end
-- (`absBundleG link lo hi`), so the fired bundle's server arm IS the tracked
-- one and the other bundle's server is a LITERAL.
------------------------------------------------------------------------

-- A fires on link AB: bfS-AB evolves (fired), bfS-AC fixed (literal)
nodeA-io-AB-evo : (F : IoFacts) (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeAEvR-io F na e a ((Bd′ ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)))
nodeA-io-AB-evo F na {X} {e} {a} iomem sBAB
  with bd F linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) iomem sBAB
... | csc′ , css′ , bfc′ , bfs′ , ip′ , eq , run , cli , srv , inrt , csf , cscf =
      naEBio (SN.mkNodeA csc′ css′ bfc′ bfs′ (SN.NodeStateA.prod-AB na) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) ip′ (SN.NodeStateA.inert-AC na))
        (cong (λ z → (z ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na))) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeA-drv-io-no na iomem))
           (⦀-wev-L _ _
              (noOffer→viewV _ (bundleG-io-no linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)
                 (absBundleG-io-ahl linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) iomem sBAB) linkAB≢linkAC iomem))
              run))
        srv (sRefl F linkAC hi (SN.NodeStateA.bfS-AC na)
               (noSrvWrite-link linkAC hi
                  (absBundleG-io-ahl linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) iomem sBAB)
                  (λ q → linkAB≢linkAC (sym q)) , noSrvRead-link linkAC hi
                  (absBundleG-io-ahl linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) iomem sBAB)
                  (λ q → linkAB≢linkAC (sym q)))) refl refl
        -- grant #6: AB is the FIRED bundle (its fact comes from `bd`), AC is a literal
        inrt (iRefl F linkAC lo (SN.NodeStateA.inert-AC na))
        -- (T6c, grant #12) AB fired at `lo hi`, so the bundle's own CS-SERVER fact IS
        -- the tracked up-hop slot's; AC's server is a literal and goes by LINK
        csf
        (csRefl F linkAC hi (SN.NodeStateA.csS-AC na)
           (noSrvWrite-link linkAC hi
           (absBundleG-io-ahl linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) iomem sBAB)
           (λ q → linkAB≢linkAC (sym q)) , noSrvRead-link linkAC hi
           (absBundleG-io-ahl linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) iomem sBAB)
           (λ q → linkAB≢linkAC (sym q))))

-- A fires on link AC: bfS-AC evolves (fired), bfS-AB fixed (literal)
nodeA-io-AC-evo : (F : IoFacts) (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeAEvR-io F na e a ((absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ⦀ Bd′) ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)))
nodeA-io-AC-evo F na {X} {e} {a} iomem sBAC
  with bd F linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) iomem sBAC
... | csc′ , css′ , bfc′ , bfs′ , ip′ , eq , run , cli , srv , inrt , csf , cscf =
      naEBio (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na) csc′ css′ bfc′ bfs′ (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) ip′)
        (cong (λ z → (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ⦀ z) ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na))) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeA-drv-io-no na iomem))
           (⦀-wev-R _ _
              (noOffer→viewV _ (bundleG-io-no linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
                 (absBundleG-io-ahl linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) iomem sBAC) (λ q → linkAB≢linkAC (sym q)) iomem))
              run))
        (sRefl F linkAB hi (SN.NodeStateA.bfS-AB na)
           (noSrvWrite-link linkAB hi
              (absBundleG-io-ahl linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) iomem sBAC)
              linkAB≢linkAC , noSrvRead-link linkAB hi
              (absBundleG-io-ahl linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) iomem sBAC)
              linkAB≢linkAC)) srv refl refl
        -- grant #6: AC is the FIRED bundle, AB is a literal
        (iRefl F linkAB lo (SN.NodeStateA.inert-AB na)) inrt
        -- (T6c, grant #12) the mirror: AC fired, AB's CS server goes by LINK
        (csRefl F linkAB hi (SN.NodeStateA.csS-AB na)
           (noSrvWrite-link linkAB hi
           (absBundleG-io-ahl linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) iomem sBAC)
           linkAB≢linkAC , noSrvRead-link linkAB hi
           (absBundleG-io-ahl linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) iomem sBAC)
           linkAB≢linkAC))
        csf

-- node A dispatcher: peel the two A bundles + the produce drivers
nodeA-ev-io-evo : (F : IoFacts) (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodeA na ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeAEvR-io F na e a M
nodeA-ev-io-evo F na {X} {e} {a} iomem step
  with PEA.Par-ev-elim apiES (λ _ _ → tt)
         (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
          ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
         (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na))
         step
... | PEA.evSync amem _ _ = ⊥-elim (io⇒¬api {X} {e} {a} iomem amem)
... | PEA.evR _ sD      = ⊥-elim (nodeA-drv-io-no na iomem (_ , sD))
... | PEA.evBoth _ _ sD = ⊥-elim (nodeA-drv-io-no na iomem (_ , sD))
... | PEA.evL _ sB
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
           (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
           sB
...   | PEA.evSync () _ _
...   | PEA.evBoth _ sBAB sBAC = ⊥-elim (linkAB≢linkAC
          (apiLink-inj (absBundleG-io-ahl linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) iomem sBAB)
                       (absBundleG-io-ahl linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) iomem sBAC)))
...   | PEA.evL _ sBAB = nodeA-io-AB-evo F na iomem sBAB
...   | PEA.evR _ sBAC = nodeA-io-AC-evo F na iomem sBAC

------------------------------------------------------------------------
-- (4) NODE B (mirror `PipeNodeFix.nodeB-io-{AB,BD}-abs-cls`, adding the
-- server slot).  On link AB node B is the CLIENT (`hi lo`), on link BD it is
-- the SERVER (`lo hi`).
------------------------------------------------------------------------

-- B fires on link AB: bfC-AB evolves (client end), bfS-BD fixed (literal)
nodeB-io-AB-evo : (F : IoFacts) (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeBEvR-io F nb e a ((Bd′ ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
nodeB-io-AB-evo F nb {X} {e} {a} iomem sBAB
  with bd F linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) iomem sBAB
... | csc′ , css′ , bfc′ , bfs′ , ip′ , eq , run , cli , srv , inrt , csf , cscf =
      nbEBio (SN.mkNodeB csc′ css′ bfc′ bfs′ (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) ip′ (SN.NodeStateB.inert-BD nb))
        (cong (λ z → (z ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb)) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeB-drv-io-no nb iomem))
           (⦀-wev-L _ _
              (noOffer→viewV _ (bundleG-io-no linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)
                 (absBundleG-io-ahl linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) iomem sBAB) linkAB≢linkBD iomem))
              run))
        cli (sRefl F linkBD hi (SN.NodeStateB.bfS-BD nb)
               (noSrvWrite-link linkBD hi
                  (absBundleG-io-ahl linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) iomem sBAB)
                  (λ q → linkAB≢linkBD (sym q)) , noSrvRead-link linkBD hi
                  (absBundleG-io-ahl linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) iomem sBAB)
                  (λ q → linkAB≢linkBD (sym q)))) refl
        -- grant #6: AB is the FIRED bundle, BD is a literal
        inrt (iRefl F linkBD lo (SN.NodeStateB.inert-BD nb))
        -- (grant #11) the tracked CS server lives in the UNFIRED BD bundle, so it is
        -- the same term in the successor record (the AB bundle's own CS server, at
        -- `(linkAB , lo)`, is not tracked by anything and its fact is discarded)
        (csRefl F linkBD hi (SN.NodeStateB.csS-BD nb)
           (noSrvWrite-link linkBD hi
           (absBundleG-io-ahl linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) iomem sBAB)
           (λ q → linkAB≢linkBD (sym q)) , noSrvRead-link linkBD hi
           (absBundleG-io-ahl linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) iomem sBAB)
           (λ q → linkAB≢linkBD (sym q))))
        -- (T6c, grant #12) AB fired at `hi lo`, so the bundle's own CS-CLIENT fact IS
        -- the tracked up-hop slot's
        cscf

-- B fires on link BD: bfS-BD evolves (server end), bfC-AB fixed (literal)
nodeB-io-BD-evo : (F : IoFacts) (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeBEvR-io F nb e a ((absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ⦀ Bd′) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
nodeB-io-BD-evo F nb {X} {e} {a} iomem sBBD
  with bd F linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) iomem sBBD
... | csc′ , css′ , bfc′ , bfs′ , ip′ , eq , run , cli , srv , inrt , csf , cscf =
      nbEBio (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) csc′ css′ bfc′ bfs′ (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) ip′)
        (cong (λ z → (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ⦀ z) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb)) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeB-drv-io-no nb iomem))
           (⦀-wev-R _ _
              (noOffer→viewV _ (bundleG-io-no linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
                 (absBundleG-io-ahl linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) iomem sBBD) (λ q → linkAB≢linkBD (sym q)) iomem))
              run))
        (cRefl F linkAB hi (SN.NodeStateB.bfC-AB nb)
           (noCliRead-link linkAB hi
              (absBundleG-io-ahl linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) iomem sBBD)
              linkAB≢linkBD , noCliWrite-link linkAB hi
              (absBundleG-io-ahl linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) iomem sBBD)
              linkAB≢linkBD)) srv refl
        -- grant #6: BD is the FIRED bundle, AB is a literal
        (iRefl F linkAB hi (SN.NodeStateB.inert-AB nb)) inrt
        -- (grant #11) BD fired at `lo hi`, so the bundle's own CS-server fact IS the
        -- tracked slot's
        csf
        -- (T6c, grant #12) … and the tracked UP-hop CS CLIENT is in the UNFIRED AB
        -- bundle, so it goes by LINK
        (cscRefl F linkAB hi (SN.NodeStateB.csC-AB nb)
           (noCliRead-link linkAB hi
           (absBundleG-io-ahl linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) iomem sBBD)
           linkAB≢linkBD , noCliWrite-link linkAB hi
           (absBundleG-io-ahl linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) iomem sBBD)
           linkAB≢linkBD))

-- node B dispatcher
nodeB-ev-io-evo : (F : IoFacts) (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodeB nb ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeBEvR-io F nb e a M
nodeB-ev-io-evo F nb {X} {e} {a} iomem step
  with PEA.Par-ev-elim apiES (λ _ _ → tt)
         (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
          ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
         (SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
         step
... | PEA.evSync amem _ _ = ⊥-elim (io⇒¬api {X} {e} {a} iomem amem)
... | PEA.evR _ sD      = ⊥-elim (nodeB-drv-io-no nb iomem (_ , sD))
... | PEA.evBoth _ _ sD = ⊥-elim (nodeB-drv-io-no nb iomem (_ , sD))
... | PEA.evL _ sBb
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb))
           (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
           sBb
...   | PEA.evSync () _ _
...   | PEA.evBoth _ sBAB sBBD = ⊥-elim (linkAB≢linkBD
          (apiLink-inj (absBundleG-io-ahl linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) iomem sBAB)
                       (absBundleG-io-ahl linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) iomem sBBD)))
...   | PEA.evL _ sBAB = nodeB-io-AB-evo F nb iomem sBAB
...   | PEA.evR _ sBBD = nodeB-io-BD-evo F nb iomem sBBD

------------------------------------------------------------------------
-- (5) NODE C — the leg-CD mirror of node B.
------------------------------------------------------------------------

-- C fires on link AC: bfC-AC evolves (client end), bfS-CD fixed (literal)
nodeC-io-AC-evo : (F : IoFacts) (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeCEvR-io F nc e a ((Bd′ ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
nodeC-io-AC-evo F nc {X} {e} {a} iomem sBAC
  with bd F linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) iomem sBAC
... | csc′ , css′ , bfc′ , bfs′ , ip′ , eq , run , cli , srv , inrt , csf , cscf =
      ncEBio (SN.mkNodeC csc′ css′ bfc′ bfs′ (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) ip′ (SN.NodeStateC.inert-CD nc))
        (cong (λ z → (z ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc)) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeC-drv-io-no nc iomem))
           (⦀-wev-L _ _
              (noOffer→viewV _ (bundleG-io-no linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)
                 (absBundleG-io-ahl linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) iomem sBAC) linkAC≢linkCD iomem))
              run))
        cli (sRefl F linkCD hi (SN.NodeStateC.bfS-CD nc)
               (noSrvWrite-link linkCD hi
                  (absBundleG-io-ahl linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) iomem sBAC)
                  (λ q → linkAC≢linkCD (sym q)) , noSrvRead-link linkCD hi
                  (absBundleG-io-ahl linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) iomem sBAC)
                  (λ q → linkAC≢linkCD (sym q)))) refl
        -- grant #6: AC is the FIRED bundle, CD is a literal
        inrt (iRefl F linkCD lo (SN.NodeStateC.inert-CD nc))
        -- (grant #11) the tracked CS server is in the UNFIRED CD bundle
        (csRefl F linkCD hi (SN.NodeStateC.csS-CD nc)
           (noSrvWrite-link linkCD hi
           (absBundleG-io-ahl linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) iomem sBAC)
           (λ q → linkAC≢linkCD (sym q)) , noSrvRead-link linkCD hi
           (absBundleG-io-ahl linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) iomem sBAC)
           (λ q → linkAC≢linkCD (sym q))))
        -- (T6c, grant #12) AC fired at `hi lo`: the bundle's own CS-CLIENT fact
        cscf

-- C fires on link CD: bfS-CD evolves (server end), bfC-AC fixed (literal)
nodeC-io-CD-evo : (F : IoFacts) (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeCEvR-io F nc e a ((absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ⦀ Bd′) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
nodeC-io-CD-evo F nc {X} {e} {a} iomem sBCD
  with bd F linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) iomem sBCD
... | csc′ , css′ , bfc′ , bfs′ , ip′ , eq , run , cli , srv , inrt , csf , cscf =
      ncEBio (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) csc′ css′ bfc′ bfs′ (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) ip′)
        (cong (λ z → (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ⦀ z) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc)) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeC-drv-io-no nc iomem))
           (⦀-wev-R _ _
              (noOffer→viewV _ (bundleG-io-no linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
                 (absBundleG-io-ahl linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) iomem sBCD) (λ q → linkAC≢linkCD (sym q)) iomem))
              run))
        (cRefl F linkAC hi (SN.NodeStateC.bfC-AC nc)
           (noCliRead-link linkAC hi
              (absBundleG-io-ahl linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) iomem sBCD)
              linkAC≢linkCD , noCliWrite-link linkAC hi
              (absBundleG-io-ahl linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) iomem sBCD)
              linkAC≢linkCD)) srv refl
        -- grant #6: CD is the FIRED bundle, AC is a literal
        (iRefl F linkAC hi (SN.NodeStateC.inert-AC nc)) inrt
        -- (grant #11) CD fired at `lo hi`, so the bundle's own fact IS the tracked
        -- slot's
        csf
        -- (T6c, grant #12) … and the up-hop CS CLIENT is in the UNFIRED AC bundle
        (cscRefl F linkAC hi (SN.NodeStateC.csC-AC nc)
           (noCliRead-link linkAC hi
           (absBundleG-io-ahl linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) iomem sBCD)
           linkAC≢linkCD , noCliWrite-link linkAC hi
           (absBundleG-io-ahl linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) iomem sBCD)
           linkAC≢linkCD))

-- node C dispatcher
nodeC-ev-io-evo : (F : IoFacts) (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodeC nc ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeCEvR-io F nc e a M
nodeC-ev-io-evo F nc {X} {e} {a} iomem step
  with PEA.Par-ev-elim apiES (λ _ _ → tt)
         (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
          ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
         (SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
         step
... | PEA.evSync amem _ _ = ⊥-elim (io⇒¬api {X} {e} {a} iomem amem)
... | PEA.evR _ sD      = ⊥-elim (nodeC-drv-io-no nc iomem (_ , sD))
... | PEA.evBoth _ _ sD = ⊥-elim (nodeC-drv-io-no nc iomem (_ , sD))
... | PEA.evL _ sBc
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc))
           (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
           sBc
...   | PEA.evSync () _ _
...   | PEA.evBoth _ sBAC sBCD = ⊥-elim (linkAC≢linkCD
          (apiLink-inj (absBundleG-io-ahl linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) iomem sBAC)
                       (absBundleG-io-ahl linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) iomem sBCD)))
...   | PEA.evL _ sBAC = nodeC-io-AC-evo F nc iomem sBAC
...   | PEA.evR _ sBCD = nodeC-io-CD-evo F nc iomem sBCD

------------------------------------------------------------------------
-- (6) NODE D — two tracked CLIENTS, no tracked server (mirror
-- `PipeNodeFix.nodeD-io-{BD,CD}-abs-cls`, client class strengthened).
------------------------------------------------------------------------

-- D fires on link BD: bfC-BD evolves (fired), bfC-CD fixed (literal)
nodeD-io-BD-evo : (F : IoFacts) (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeDEvR-io F nd e a ((Bd′ ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)))
nodeD-io-BD-evo F nd {X} {e} {a} iomem sBBD
  with bd F linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) iomem sBBD
... | csc′ , css′ , bfc′ , bfs′ , ip′ , eq , run , cli , srv , inrt , csf , cscf =
      ndEBio (SN.mkNodeD csc′ css′ bfc′ bfs′ (SN.NodeStateD.cons-BD nd) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) ip′ (SN.NodeStateD.inert-CD nd))
        (cong (λ z → (z ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeD-drv-io-no nd iomem))
           (⦀-wev-L _ _
              (noOffer→viewV _ (bundleG-io-no linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)
                 (absBundleG-io-ahl linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) iomem sBBD) linkBD≢linkCD iomem))
              run))
        cli (cRefl F linkCD hi (SN.NodeStateD.bfC-CD nd)
               (noCliRead-link linkCD hi
                  (absBundleG-io-ahl linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) iomem sBBD)
                  (λ q → linkBD≢linkCD (sym q)) , noCliWrite-link linkCD hi
                  (absBundleG-io-ahl linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) iomem sBBD)
                  (λ q → linkBD≢linkCD (sym q)))) refl refl
        -- grant #6: BD is the FIRED bundle, CD is a literal
        inrt (iRefl F linkCD hi (SN.NodeStateD.inert-CD nd))
        -- (T6c, grant #12) BD fired at `hi lo`, so the bundle's own CS-CLIENT fact IS
        -- the tracked down-hop slot's; CD's client goes by LINK
        cscf
        (cscRefl F linkCD hi (SN.NodeStateD.csC-CD nd)
           (noCliRead-link linkCD hi
           (absBundleG-io-ahl linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) iomem sBBD)
           (λ q → linkBD≢linkCD (sym q)) , noCliWrite-link linkCD hi
           (absBundleG-io-ahl linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) iomem sBBD)
           (λ q → linkBD≢linkCD (sym q))))

-- D fires on link CD: bfC-CD evolves (fired), bfC-BD fixed (literal)
nodeD-io-CD-evo : (F : IoFacts) (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeDEvR-io F nd e a ((absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ⦀ Bd′) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)))
nodeD-io-CD-evo F nd {X} {e} {a} iomem sBCD
  with bd F linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) iomem sBCD
... | csc′ , css′ , bfc′ , bfs′ , ip′ , eq , run , cli , srv , inrt , csf , cscf =
      ndEBio (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd) csc′ css′ bfc′ bfs′ (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) ip′)
        (cong (λ z → (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ⦀ z) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeD-drv-io-no nd iomem))
           (⦀-wev-R _ _
              (noOffer→viewV _ (bundleG-io-no linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
                 (absBundleG-io-ahl linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) iomem sBCD) (λ q → linkBD≢linkCD (sym q)) iomem))
              run))
        (cRefl F linkBD hi (SN.NodeStateD.bfC-BD nd)
           (noCliRead-link linkBD hi
              (absBundleG-io-ahl linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) iomem sBCD)
              linkBD≢linkCD , noCliWrite-link linkBD hi
              (absBundleG-io-ahl linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) iomem sBCD)
              linkBD≢linkCD)) cli refl refl
        -- grant #6: CD is the FIRED bundle, BD is a literal
        (iRefl F linkBD hi (SN.NodeStateD.inert-BD nd)) inrt
        -- (T6c, grant #12) the mirror
        (cscRefl F linkBD hi (SN.NodeStateD.csC-BD nd)
           (noCliRead-link linkBD hi
           (absBundleG-io-ahl linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) iomem sBCD)
           linkBD≢linkCD , noCliWrite-link linkBD hi
           (absBundleG-io-ahl linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) iomem sBCD)
           linkBD≢linkCD))
        cscf

-- node D dispatcher
nodeD-ev-io-evo : (F : IoFacts) (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodeD nd ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeDEvR-io F nd e a M
nodeD-ev-io-evo F nd {X} {e} {a} iomem step
  with PEA.Par-ev-elim apiES (λ _ _ → tt)
         (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
          ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
         (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))
         step
... | PEA.evSync amem _ _ = ⊥-elim (io⇒¬api {X} {e} {a} iomem amem)
... | PEA.evR _ sD      = ⊥-elim (nodeD-drv-io-no nd iomem (_ , sD))
... | PEA.evBoth _ _ sD = ⊥-elim (nodeD-drv-io-no nd iomem (_ , sD))
... | PEA.evL _ sBd
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
           (absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
           sBd
...   | PEA.evSync () _ _
...   | PEA.evBoth _ sBBD sBCD = ⊥-elim (linkBD≢linkCD
          (apiLink-inj (absBundleG-io-ahl linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) iomem sBBD)
                       (absBundleG-io-ahl linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) iomem sBCD)))
...   | PEA.evL _ sBBD = nodeD-io-BD-evo F nd iomem sBBD
...   | PEA.evR _ sBCD = nodeD-io-CD-evo F nd iomem sBCD

------------------------------------------------------------------------
-- (7) THE WHOLE-NODES CLASSIFIERS and the top dispatcher (mirror
-- `PipeNodeFix.top-nodes-io-abs-client-cls`, both slot families carried).
------------------------------------------------------------------------

-- the four `PipeInv`-tracked BF clients' io evolutions
AllCliIoCls : (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) → Set
AllCliIoCls s s′ e a =
    CliIoCls linkAB hi (upClient legBD s) (upClient legBD s′) e a
  × CliIoCls linkAC hi (upClient legCD s) (upClient legCD s′) e a
  × CliIoCls linkBD hi (dnClient legBD s) (dnClient legBD s′) e a
  × CliIoCls linkCD hi (dnClient legCD s) (dnClient legCD s′) e a

-- the four `PipeSrvInv`-tracked BF servers' io evolutions
AllSrvIoCls : SysState → SysState → Set
AllSrvIoCls s s′ =
    SrvIoCls (upSrv legBD s) (upSrv legBD s′)
  × SrvIoCls (upSrv legCD s) (upSrv legCD s′)
  × SrvIoCls (dnSrv legBD s) (dnSrv legBD s′)
  × SrvIoCls (dnSrv legCD s) (dnSrv legCD s′)

-- the four tracked BF clients' io evolutions, at an ABSTRACT client fact
AllCliFacts : (F : IoFacts) (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) → Set
AllCliFacts F s s′ e a =
    Cf F linkAB hi (upClient legBD s) (upClient legBD s′) e a
  × Cf F linkAC hi (upClient legCD s) (upClient legCD s′) e a
  × Cf F linkBD hi (dnClient legBD s) (dnClient legBD s′) e a
  × Cf F linkCD hi (dnClient legCD s) (dnClient legCD s′) e a

-- the four tracked BF servers' io evolutions, at an ABSTRACT server fact
AllSrvFacts : (F : IoFacts) (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) → Set
AllSrvFacts F s s′ e a =
    Sf F linkAB hi (upSrv legBD s) (upSrv legBD s′) e a
  × Sf F linkAC hi (upSrv legCD s) (upSrv legCD s′) e a
  × Sf F linkBD hi (dnSrv legBD s) (dnSrv legBD s′) e a
  × Sf F linkCD hi (dnSrv legCD s) (dnSrv legCD s′) e a

-- the EIGHT bundles' inert facts, at an ABSTRACT inert fact (grant #6), in node
-- order A, B, C, D — each bundle at its own (link, client-direction) key
AllInertFacts : (F : IoFacts) (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) → Set
AllInertFacts F s s′ e a =
    If F linkAB lo (SN.NodeStateA.inert-AB (nA s)) (SN.NodeStateA.inert-AB (nA s′)) e a
  × If F linkAC lo (SN.NodeStateA.inert-AC (nA s)) (SN.NodeStateA.inert-AC (nA s′)) e a
  × If F linkAB hi (SN.NodeStateB.inert-AB (nB s)) (SN.NodeStateB.inert-AB (nB s′)) e a
  × If F linkBD lo (SN.NodeStateB.inert-BD (nB s)) (SN.NodeStateB.inert-BD (nB s′)) e a
  × If F linkAC hi (SN.NodeStateC.inert-AC (nC s)) (SN.NodeStateC.inert-AC (nC s′)) e a
  × If F linkCD lo (SN.NodeStateC.inert-CD (nC s)) (SN.NodeStateC.inert-CD (nC s′)) e a
  × If F linkBD hi (SN.NodeStateD.inert-BD (nD s)) (SN.NodeStateD.inert-BD (nD s′)) e a
  × If F linkCD hi (SN.NodeStateD.inert-CD (nD s)) (SN.NodeStateD.inert-CD (nD s′)) e a

-- (grant #11) the TWO tracked CS SERVERS, at an ABSTRACT CS-server fact.  They are
-- `PipeSrvInv`'s own down-hop slots at the ChainSync channel — `LiveRelayOpen.dnCSs`
-- verbatim — which is why there are two and not four: the up-hop CS peers of a leg
-- are its relay's CS CLIENTS and belong to the (unbuilt) client half.
AllCssFacts : (F : IoFacts) (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) → Set
AllCssFacts F s s′ e a =
    Csf F linkBD hi (SN.NodeStateB.csS-BD (nB s)) (SN.NodeStateB.csS-BD (nB s′)) e a
  × Csf F linkCD hi (SN.NodeStateC.csS-CD (nC s)) (SN.NodeStateC.csS-CD (nC s′)) e a

-- *** (T6c, grant #12) THE TWO NEW FAMILIES ARE SEPARATE AND APPENDED, not a widening
-- of the one above. ***  Widening `AllCssFacts` from two components to four would have
-- moved every positional reader of it (`LiveChanJoin.dnCssRow`, `LiveDrvBF`'s four io
-- arms); as two new families the grant is purely additive there.
-- the TWO tracked UP-HOP CS SERVERS — node A's, in leg order (`LiveChanCS.upCSsOf`)
AllCssUpFacts : (F : IoFacts) (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) → Set
AllCssUpFacts F s s′ e a =
    Csf F linkAB hi (SN.NodeStateA.csS-AB (nA s)) (SN.NodeStateA.csS-AB (nA s′)) e a
  × Csf F linkAC hi (SN.NodeStateA.csS-AC (nA s)) (SN.NodeStateA.csS-AC (nA s′)) e a

-- … and the FOUR tracked CS CLIENTS, in hop-then-leg order: the two UP-hop ones (the
-- relays' own, `LiveChanCS.upCScOf`) and the two DOWN-hop ones (node D's, `dnCScOf` —
-- the `pp2` hop's client, and the slot the whole grant exists for)
AllCscFacts : (F : IoFacts) (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) → Set
AllCscFacts F s s′ e a =
    Cscf F linkAB hi (SN.NodeStateB.csC-AB (nB s)) (SN.NodeStateB.csC-AB (nB s′)) e a
  × Cscf F linkAC hi (SN.NodeStateC.csC-AC (nC s)) (SN.NodeStateC.csC-AC (nC s′)) e a
  × Cscf F linkBD hi (SN.NodeStateD.csC-BD (nD s)) (SN.NodeStateD.csC-BD (nD s′)) e a
  × Cscf F linkCD hi (SN.NodeStateD.csC-CD (nD s)) (SN.NodeStateD.csC-CD (nD s′)) e a

-- TOP: an io fire of the whole abstract node group, with the medium untouched,
-- the concrete weak run, BOTH tracked slot families classified AT AN ABSTRACT
-- PER-PEER FACT, the six driver phases fixed, and (trailing, grant #6) the eight
-- bundles' inert facts
top-nodes-io-evoP : (F : IoFacts) (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ s′ ∈ SysState ] (med s ≡ med s′) × (M ≡ absNodesOf s′)
      × (nodesOf s ═[ ev (evl (evLabel X e a)) ]═► nodesOf s′)
      × AllCliFacts F s s′ e a
      × AllSrvFacts F s s′ e a
      × (SN.NodeStateA.prod-AB (nA s) ≡ SN.NodeStateA.prod-AB (nA s′))
      × (SN.NodeStateA.prod-AC (nA s) ≡ SN.NodeStateA.prod-AC (nA s′))
      × (SN.NodeStateB.cp-B (nB s) ≡ SN.NodeStateB.cp-B (nB s′))
      × (SN.NodeStateC.cp-C (nC s) ≡ SN.NodeStateC.cp-C (nC s′))
      × (SN.NodeStateD.cons-BD (nD s) ≡ SN.NodeStateD.cons-BD (nD s′))
      × (SN.NodeStateD.cons-CD (nD s) ≡ SN.NodeStateD.cons-CD (nD s′))
      × AllInertFacts F s s′ e a
      -- (grant #11) TRAILING: the two tracked CS servers' facts
      × AllCssFacts F s s′ e a
      -- (T6c, grant #12) … and, TRAILING, the two UP-hop CS SERVERS and the four CS
      -- CLIENTS.  Appended in that order, so every positional reader of the first
      -- fourteen components keeps its pattern except the ones that ended on a
      -- NON-wildcard — those were re-cut at this task, and the trap is banked.
      × AllCssUpFacts F s s′ e a
      × AllCscFacts F s s′ e a
top-nodes-io-evoP F s iomem nodesStep
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (absNodeA (nA s)) (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s))) nodesStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sA sRest = ⊥-elim (absGroupA-io-no (nA s) (nB s) (nC s) (nD s) iomem sA (_ , sRest))
... | PEA.evL _ sA with nodeA-ev-io-evo F (nA s) iomem sA
...   | naEBio na′ Meq weakRunA srvAB srvAC epAB epAC iAB iAC csAB csAC =
        mkSys (med s) na′ (nB s) (nC s) (nD s) , refl ,
        cong (λ z → z ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) Meq ,
        ⦀-wev-L (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (⦀-noOffer (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (nodeB-io-no-when-A (nB s) iomem fpA)
             (⦀-noOffer (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (nodeC-io-no-when-A (nC s) iomem fpA) (nodeD-io-no-when-A (nD s) iomem fpA))))
          weakRunA
        , (cRefl F linkAB hi (upClient legBD s) (proj₁ nsA) , cRefl F linkAC hi (upClient legCD s) (proj₁ (proj₂ nsA)) , cRefl F linkBD hi (dnClient legBD s) (proj₁ (proj₂ (proj₂ nsA))) , cRefl F linkCD hi (dnClient legCD s) (proj₂ (proj₂ (proj₂ nsA))))
        , (srvAB , srvAC , sRefl F linkBD hi (dnSrv legBD s) (proj₁ nwA) , sRefl F linkCD hi (dnSrv legCD s) (proj₂ nwA))
        , epAB , epAC , refl , refl , refl , refl
        -- grant #6: A fired (its two facts come from the node record); B, C and D
        -- are LITERAL in the successor, so their six bundles go by `iRefl`
        , (iAB , iAC
          , iRefl F linkAB hi (SN.NodeStateB.inert-AB (nB s))
          , iRefl F linkBD lo (SN.NodeStateB.inert-BD (nB s))
          , iRefl F linkAC hi (SN.NodeStateC.inert-AC (nC s))
          , iRefl F linkCD lo (SN.NodeStateC.inert-CD (nC s))
          , iRefl F linkBD hi (SN.NodeStateD.inert-BD (nD s))
          , iRefl F linkCD hi (SN.NodeStateD.inert-CD (nD s)))
        -- (grant #11) A fired: B and C are LITERAL, so both tracked CS servers are
        , (csRefl F linkBD hi (SN.NodeStateB.csS-BD (nB s)) (proj₁ nwAc)
          , csRefl F linkCD hi (SN.NodeStateC.csS-CD (nC s)) (proj₂ nwAc))
        -- (T6c, grant #12) A fired, so BOTH up-hop CS servers' facts come off its own
        -- peel; all four CS clients are literal and go by the ownership pair
        , (csAB , csAC)
        , (cscRefl F linkAB hi (SN.NodeStateB.csC-AB (nB s)) (proj₁ nsAc)
          , cscRefl F linkAC hi (SN.NodeStateC.csC-AC (nC s)) (proj₁ (proj₂ nsAc))
          , cscRefl F linkBD hi (SN.NodeStateD.csC-BD (nD s)) (proj₁ (proj₂ (proj₂ nsAc)))
          , cscRefl F linkCD hi (SN.NodeStateD.csC-CD (nD s)) (proj₂ (proj₂ (proj₂ nsAc))))
  where fpA = absNodeA-io-fp (nA s) iomem sA
        nsA = noCliA iomem fpA
        nwA = noSrvA iomem fpA
        -- (T6c, grant #12) the SAME two witnesses at the ChainSync channel: the
        -- ownership layer is `IDs`-parametric, so these are the identical terms with
        -- the implicit channel solved by the CS families' premise instead of the BF
        -- ones'.  Two lines per branch, and not one witness body changed.
        --
        -- *** DO NOT MERGE THESE WITH `nsA`/`nwA`.  THE DUPLICATION IS FORCED. ***
        -- They are syntactically identical, and a successor will be tempted; Agda
        -- does NOT generalise a `where` binding over an unsolved implicit, so the BF
        -- uses below pin the first copy's `{id}` to `N2N_BlockFetch` and the CS uses
        -- need a binding of their own.  BANKED (T6c review M-4): an `IDs`-parametric
        -- witness needs ONE `where` BINDING PER CHANNEL — that is the price of the
        -- cheap (id-generalising) route over mirroring the four predicates, and at
        -- sixteen bindings across the four branches it is still the cheap one.
        nsAc = noCliA iomem fpA
        nwAc = noSrvA iomem fpA
top-nodes-io-evoP F s iomem nodesStep | PEA.evR _ sRest
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s)) sRest
... | PEA.evSync () _ _
... | PEA.evBoth _ sB sCD = ⊥-elim (absGroupB-io-no (nB s) (nC s) (nD s) iomem sB (_ , sCD))
... | PEA.evL _ sB with nodeB-ev-io-evo F (nB s) iomem sB
...   | nbEBio nb′ Meq weakRunB cliAB srvBD ecpB iAB iBD qBD cscAB =
        mkSys (med s) (nA s) nb′ (nC s) (nD s) , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (z ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) Meq ,
        ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (nodeA-io-no-when-B (nA s) iomem fpB))
          (⦀-wev-L (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (noOffer→viewV _ (⦀-noOffer (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (nodeC-io-no-when-B (nC s) iomem fpB) (nodeD-io-no-when-B (nD s) iomem fpB)))
             weakRunB)
        , (cliAB , cRefl F linkAC hi (upClient legCD s) (proj₁ nsB) , cRefl F linkBD hi (dnClient legBD s) (proj₁ (proj₂ nsB)) , cRefl F linkCD hi (dnClient legCD s) (proj₂ (proj₂ nsB)))
        , (sRefl F linkAB hi (upSrv legBD s) (proj₁ nwB) , sRefl F linkAC hi (upSrv legCD s) (proj₁ (proj₂ nwB)) , srvBD , sRefl F linkCD hi (dnSrv legCD s) (proj₂ (proj₂ nwB)))
        , refl , refl , ecpB , refl , refl , refl
        -- grant #6: B fired; A, C and D are literal
        , (iRefl F linkAB lo (SN.NodeStateA.inert-AB (nA s))
          , iRefl F linkAC lo (SN.NodeStateA.inert-AC (nA s))
          , iAB , iBD
          , iRefl F linkAC hi (SN.NodeStateC.inert-AC (nC s))
          , iRefl F linkCD lo (SN.NodeStateC.inert-CD (nC s))
          , iRefl F linkBD hi (SN.NodeStateD.inert-BD (nD s))
          , iRefl F linkCD hi (SN.NodeStateD.inert-CD (nD s)))
        -- (grant #11) B fired: its own CS server's fact comes off the peel, C's is
        -- a literal
        , (qBD , csRefl F linkCD hi (SN.NodeStateC.csS-CD (nC s)) (proj₂ (proj₂ nwBc)))
        -- (T6c, grant #12) node A is LITERAL, so both up-hop CS servers go by the
        -- pair; B's own up-hop CS CLIENT comes off its peel
        , (csRefl F linkAB hi (SN.NodeStateA.csS-AB (nA s)) (proj₁ nwBc)
          , csRefl F linkAC hi (SN.NodeStateA.csS-AC (nA s)) (proj₁ (proj₂ nwBc)))
        , (cscAB
          , cscRefl F linkAC hi (SN.NodeStateC.csC-AC (nC s)) (proj₁ nsBc)
          , cscRefl F linkBD hi (SN.NodeStateD.csC-BD (nD s)) (proj₁ (proj₂ nsBc))
          , cscRefl F linkCD hi (SN.NodeStateD.csC-CD (nD s)) (proj₂ (proj₂ nsBc)))
  where fpB = absNodeB-io-fp (nB s) iomem sB
        nsB = noCliB iomem fpB
        nwB = noSrvB iomem fpB
        nsBc = noCliB iomem fpB
        nwBc = noSrvB iomem fpB
top-nodes-io-evoP F s iomem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absNodeC (nC s)) (absNodeD (nD s)) sCD
... | PEA.evSync () _ _
... | PEA.evBoth _ sC sD = ⊥-elim (absNodeD-io-no-when-C (nD s) iomem (absNodeC-io-fp (nC s) iomem sC) (_ , sD))
... | PEA.evL _ sC with nodeC-ev-io-evo F (nC s) iomem sC
...   | ncEBio nc′ Meq weakRunC cliAC srvCD ecpC iAC iCD qCD cscAC =
        mkSys (med s) (nA s) (nB s) nc′ (nD s) , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (z ⦀ absNodeD (nD s)))) Meq ,
        ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (nodeA-io-no-when-C (nA s) iomem fpC))
          (⦀-wev-R (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (noOffer→viewV _ (nodeB-io-no-when-C (nB s) iomem fpC))
             (⦀-wev-L (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (noOffer→viewV _ (nodeD-io-no-when-C (nD s) iomem fpC))
                weakRunC))
        , (cRefl F linkAB hi (upClient legBD s) (proj₁ nsC) , cliAC , cRefl F linkBD hi (dnClient legBD s) (proj₁ (proj₂ nsC)) , cRefl F linkCD hi (dnClient legCD s) (proj₂ (proj₂ nsC)))
        , (sRefl F linkAB hi (upSrv legBD s) (proj₁ nwC) , sRefl F linkAC hi (upSrv legCD s) (proj₁ (proj₂ nwC)) , sRefl F linkBD hi (dnSrv legBD s) (proj₂ (proj₂ nwC)) , srvCD)
        , refl , refl , refl , ecpC , refl , refl
        -- grant #6: C fired; A, B and D are literal
        , (iRefl F linkAB lo (SN.NodeStateA.inert-AB (nA s))
          , iRefl F linkAC lo (SN.NodeStateA.inert-AC (nA s))
          , iRefl F linkAB hi (SN.NodeStateB.inert-AB (nB s))
          , iRefl F linkBD lo (SN.NodeStateB.inert-BD (nB s))
          , iAC , iCD
          , iRefl F linkBD hi (SN.NodeStateD.inert-BD (nD s))
          , iRefl F linkCD hi (SN.NodeStateD.inert-CD (nD s)))
        -- (grant #11) C fired: B's CS server is a literal, C's comes off the peel
        , (csRefl F linkBD hi (SN.NodeStateB.csS-BD (nB s)) (proj₂ (proj₂ nwCc)) , qCD)
        -- (T6c, grant #12) the leg-CD mirror of the node-B branch
        , (csRefl F linkAB hi (SN.NodeStateA.csS-AB (nA s)) (proj₁ nwCc)
          , csRefl F linkAC hi (SN.NodeStateA.csS-AC (nA s)) (proj₁ (proj₂ nwCc)))
        , (cscRefl F linkAB hi (SN.NodeStateB.csC-AB (nB s)) (proj₁ nsCc)
          , cscAC
          , cscRefl F linkBD hi (SN.NodeStateD.csC-BD (nD s)) (proj₁ (proj₂ nsCc))
          , cscRefl F linkCD hi (SN.NodeStateD.csC-CD (nD s)) (proj₂ (proj₂ nsCc)))
  where fpC = absNodeC-io-fp (nC s) iomem sC
        nsC = noCliC iomem fpC
        nwC = noSrvC iomem fpC
        nsCc = noCliC iomem fpC
        nwCc = noSrvC iomem fpC
top-nodes-io-evoP F s iomem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD | PEA.evR _ sD
    with nodeD-ev-io-evo F (nD s) iomem sD
... | ndEBio nd′ Meq weakRunD cliBD cliCD econsBD econsCD iBD iCD cscBD cscCD =
        mkSys (med s) (nA s) (nB s) (nC s) nd′ , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ z))) Meq ,
        ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (nodeA-io-no-when-D (nA s) iomem fpD))
          (⦀-wev-R (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (noOffer→viewV _ (nodeB-io-no-when-D (nB s) iomem fpD))
             (⦀-wev-R (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (noOffer→viewV _ (nodeC-io-no-when-D (nC s) iomem fpD))
                weakRunD))
        , (cRefl F linkAB hi (upClient legBD s) (proj₁ nsD) , cRefl F linkAC hi (upClient legCD s) (proj₂ nsD) , cliBD , cliCD)
        , (sRefl F linkAB hi (upSrv legBD s) (proj₁ nwD) , sRefl F linkAC hi (upSrv legCD s) (proj₁ (proj₂ nwD)) , sRefl F linkBD hi (dnSrv legBD s) (proj₁ (proj₂ (proj₂ nwD))) , sRefl F linkCD hi (dnSrv legCD s) (proj₂ (proj₂ (proj₂ nwD))))
        , refl , refl , refl , refl , econsBD , econsCD
        -- grant #6: D fired; A, B and C are literal
        , (iRefl F linkAB lo (SN.NodeStateA.inert-AB (nA s))
          , iRefl F linkAC lo (SN.NodeStateA.inert-AC (nA s))
          , iRefl F linkAB hi (SN.NodeStateB.inert-AB (nB s))
          , iRefl F linkBD lo (SN.NodeStateB.inert-BD (nB s))
          , iRefl F linkAC hi (SN.NodeStateC.inert-AC (nC s))
          , iRefl F linkCD lo (SN.NodeStateC.inert-CD (nC s))
          , iBD , iCD)
        -- (grant #11) D fired: B and C are LITERAL
        , (csRefl F linkBD hi (SN.NodeStateB.csS-BD (nB s)) (proj₁ (proj₂ (proj₂ nwDc)))
          , csRefl F linkCD hi (SN.NodeStateC.csS-CD (nC s)) (proj₂ (proj₂ (proj₂ nwDc))))
        -- (T6c, grant #12) D fired: BOTH down-hop CS CLIENTS come off its own peel —
        -- these are the two slots `pp2` needs — and node A's two servers plus the two
        -- relays' clients are literal
        , (csRefl F linkAB hi (SN.NodeStateA.csS-AB (nA s)) (proj₁ nwDc)
          , csRefl F linkAC hi (SN.NodeStateA.csS-AC (nA s)) (proj₁ (proj₂ nwDc)))
        , (cscRefl F linkAB hi (SN.NodeStateB.csC-AB (nB s)) (proj₁ nsDc)
          , cscRefl F linkAC hi (SN.NodeStateC.csC-AC (nC s)) (proj₂ nsDc)
          , cscBD , cscCD)
  where fpD = absNodeD-io-fp (nD s) iomem sD
        nsD = noCliD iomem fpD
        nwD = noSrvD iomem fpD
        nsDc = noCliD iomem fpD
        nwDc = noSrvD iomem fpD

------------------------------------------------------------------------
-- (8) THE ORIGINAL CONE, RE-DERIVED AS THE INSTANCE (owner grant #1's term).
-- `Cf₀`/`Sf₀` are the two frozen classifiers of §1 and `bd₀` is
-- `PipeBundleIoEvo.absBundleG-io-evo` in `BundleEvo`'s Σ form, so
-- `top-nodes-io-evo` below has the SAME type and the SAME content as before this
-- generalisation: `AllCliFacts facts₀ s s′ e a` unfolds to `AllCliIoCls s s′ e a`
-- and `AllSrvFacts facts₀ s s′ e a` to `AllSrvIoCls s s′` by record projection.
------------------------------------------------------------------------

-- the frozen client classifier as a `CliFact`
Cf₀ : CliFact
Cf₀ l d bfc bfc′ e a = CliIoCls l d bfc bfc′ e a

-- the frozen server classifier as a `SrvFact` (it needs neither key nor label)
Sf₀ : SrvFact
Sf₀ l d bfs bfs′ e a = SrvIoCls bfs bfs′

-- the frozen cone asks NOTHING of the inert slots, so its inert fact is trivial
-- (grant #6's regression guarantee: `top-nodes-io-evo` below keeps its exact
-- former TYPE by projecting the new slot away, so `PipeTauIo`/`PipeValTauIo` —
-- its only two consumers — see no change at all)
If₀ : InertFact
If₀ l cl ip ip′ e a = ⊤

-- … and it asks nothing of the CS servers either (grant #11's regression guarantee:
-- §8's cone keeps its exact former TYPE by projecting the new slot away, so
-- `PipeTauIo`/`PipeValTauIo` see no change for the third time)
Csf₀ : CssFact
Csf₀ l sv css css′ e a = ⊤

-- (T6c, grant #12) … nor of the CS clients, for the same regression reason: §8's
-- cone keeps its exact former TYPE by projecting the two new slots away, so
-- `PipeTauIo`/`PipeValTauIo` see no change for the FOURTH time
Cscf₀ : CscFact
Cscf₀ l cl csc csc′ e a = ⊤

-- the frozen bundle dispatcher in `BundleEvo` form
bd₀ : (l : Link) (cl sv : Dir) → cl ≢ sv
    → (csc : SN.CScPos) (css : SN.CSsPos) (bfc : SN.BFcPos) (bfs : SN.BFsPos)
      (ip : SN.InertPos)
    → {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
    → ioES .mem (X , e) a
    → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X e a)) ]─► Bd′
    → BundleEvo Cf₀ Sf₀ If₀ Csf₀ Cscf₀ l cl sv csc css bfc bfs ip e a Bd′
bd₀ l cl sv cl≢sv csc css bfc bfs ip iomem step
  with absBundleG-io-evo l cl sv cl≢sv csc css bfc bfs ip iomem step
... | bgEBio⁺ csc′ css′ bfc′ bfs′ ip′ eq run cli srv =
      csc′ , css′ , bfc′ , bfs′ , ip′ , eq , run , cli , srv , tt , tt , tt

-- the frozen fact interface
facts₀ : IoFacts
facts₀ = record { Cf = Cf₀ ; Sf = Sf₀ ; If = If₀ ; Csf = Csf₀ ; Cscf = Cscf₀
               ; bd = bd₀
               ; cRefl = λ l d bfc _ → inj₁ refl ; sRefl = λ l d bfs _ → inj₁ refl
               ; iRefl = λ l cl ip → tt ; csRefl = λ l sv css _ → tt
               ; cscRefl = λ l cl csc _ → tt }

-- TOP (the frozen cone, unchanged for `PipeTauIo` / `PipeValTauIo`)
top-nodes-io-evo : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ s′ ∈ SysState ] (med s ≡ med s′) × (M ≡ absNodesOf s′)
      × (nodesOf s ═[ ev (evl (evLabel X e a)) ]═► nodesOf s′)
      × AllCliIoCls s s′ e a
      × AllSrvIoCls s s′
      × (SN.NodeStateA.prod-AB (nA s) ≡ SN.NodeStateA.prod-AB (nA s′))
      × (SN.NodeStateA.prod-AC (nA s) ≡ SN.NodeStateA.prod-AC (nA s′))
      × (SN.NodeStateB.cp-B (nB s) ≡ SN.NodeStateB.cp-B (nB s′))
      × (SN.NodeStateC.cp-C (nC s) ≡ SN.NodeStateC.cp-C (nC s′))
      × (SN.NodeStateD.cons-BD (nD s) ≡ SN.NodeStateD.cons-BD (nD s′))
      × (SN.NodeStateD.cons-CD (nD s) ≡ SN.NodeStateD.cons-CD (nD s′))
top-nodes-io-evo s iomem nodesStep =
  -- grant #6: project the (trivial) inert slot away, so this cone's TYPE is
  -- byte-for-byte the one `PipeTauIo`/`PipeValTauIo` already consume
  let (s′ , medEq , Meq , run , cli , srv , e1 , e2 , e3 , e4 , e5 , e6 , _) =
        top-nodes-io-evoP facts₀ s iomem nodesStep
  in  s′ , medEq , Meq , run , cli , srv , e1 , e2 , e3 , e4 , e5 , e6
