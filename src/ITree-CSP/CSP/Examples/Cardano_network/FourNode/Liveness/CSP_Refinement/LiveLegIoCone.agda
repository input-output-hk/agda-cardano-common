{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — THE STRENGTHENED io CONE for `LegInv`
-- (`Praos.LiveLegIoCone`), session-52 / Task-3 slice E.
--
-- WHY THIS MODULE EXISTS.  `LiveLegStep`'s two io arms take their per-peer facts
-- as MODULE PREMISES (leaves 1-4 of the task-3 inventory) because the frozen
-- cone's classifiers are SUCCESSOR-negative:
--
--   `PipeNodeIoEvo.CliIoCls l d bfc bfc′ e a
--       = (bfc ≡ bfc′) ⊎ ((BFcHasBlk bfc′ → ⊥) ⊎ BlkReadAt l d bfc′ e a)`
--   `PipeNodeIoEvo.SrvIoCls bfs bfs′ = (bfs ≡ bfs′) ⊎ (BFsHasBlk bfs′ → ⊥)`
--
-- and an OCCUPANCY transport needs the PREDECESSOR-negative form: "a slot that
-- HELD a block is io-fixed" (a holding client/server has no io row other than
-- its own wire write), plus, on the write, the producer-site positive answer.
-- The successor is bound EXISTENTIALLY by the cone, and there is no slot
-- injectivity anywhere in the tree (session-30's measured negative result,
-- re-confirmed by the instalment-4 review), so a SECOND peel cannot be tied to
-- the first: the fact has to be emitted where the fired peer is decoded.
--
-- HOW.  `PipeNodeIoEvo` is now generalised in place over the `IoFacts` interface
-- (owner grant #1; its §1b, with the frozen cone re-derived as `facts₀`), and
-- `PipeBundleIoEvo.absBundleBF-ev-io-evo` was ALREADY `Cf`/`Sf`-abstract.  So this
-- module supplies a SECOND instance `facts⁺` of the same dispatch:
--   · `CliInKeep bfc bfc′ = (bfc ≡ bfc′) ⊎ (BFcHasBlk bfc → ⊥)`   (leaves 2, 3's
--     client twin) — the client's own io decode proves it by pattern matching,
--     because `bcBlk1 b`'s ONLY outgoing row is the api `recvBFBlock`;
--   · `SrvIoCls⁺`, THREE arms: fixed / the predecessor was not holding / it was
--     holding `b` and THIS io is its own wire WRITE of exactly `b` at its own key
--     (leaves 1, 3).
-- Nothing here re-mirrors a cone; the four-node dispatch and the twelve-peer
-- bundle peel are the frozen ones, invoked at stronger facts.
--
-- *** LEAF 1 WAS FALSE AS STATED, AND THIS IS THE FIX. ***  The predecessor's
-- `SrvInCls⁺` had only TWO arms (fixed / holding-and-writing).  A tracked server
-- also writes from `bsStart1`, `bsNoBlk1` and `bsBatchDone1`
-- (`PipeSrvIoDec.decBFs-sendBF-succ`, `:202`, `:214`, `:238`), and at such a fire
-- the slot is NEITHER fixed NOR holding — so the two-arm form is refuted by a
-- `bsStart1` write.  The middle arm `(BFsHasBlk bfs → ⊥)` is what makes it true,
-- and it costs the consumer nothing: `LiveLegStep.srvHop-in` is applied under
-- `SrvHas⁺ b bfs`, which refutes it in one line.
--
-- Base modules touched: NONE beyond `PipeNodeIoEvo`'s granted generalisation.
-- No postulate/hole/meta.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
-- (grant #7) the row's `just` and its injectivity, for the fired-row terms
open import Data.Maybe using ( just )
open import Data.Maybe.Properties using ( just-injective )
open import Data.Maybe.Properties using ( just-injective )
open import Relation.Nullary using ( yes; no )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; _≢_; refl; sym; trans; cong; subst )

open import Class.DecEq using ( DecEq; _≟_ )
import Class.DecEq.Instances as DecEqI

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegIoCone
  (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p
open import CSP.Examples.Cardano_network.Base using
  ( Dir; hi; IDs; Mode; FromResponder
  ; N2N_ChainSync; N2N_BlockFetch; N2N_KeepAlive
  ; N2N_TxSubmission; N2N_LeiosNotify; N2N_LeiosFetch )
open import CSP.Examples.Cardano_network.Net p using
  ( Net_Api; Net_Api-≟; Link
  ; apiCS; apiBF; apiKA; apiTS; apiLN; apiLF; done; input; output
  ; sndmsg; rcvmsg; tx; sndack; rcvack; ack; break ; store; env )
open import CSP.Examples.Cardano_network.Data p
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )
open import CSP.Examples.Cardano_network.NetworkPar p using ( ιCS; ιBF; ιKA; ιTS; ιLN; ιLF )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_; wev; τ*-refl; τ*-step )

import CSP.Examples.Cardano_network.ChainSync p as CS
import CSP.Examples.Cardano_network.BlockFetch p as BF
import CSP.Examples.Cardano_network.KeepAlive p as KA
import CSP.Examples.Cardano_network.TxSubmission p as TS
import CSP.Examples.Cardano_network.LeiosNotify p as LN
import CSP.Examples.Cardano_network.LeiosFetch p as LF

import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep
open SStep using ( NetProc; absBFc; absBFs; absBundleG; absNodesOf; nodesOf
                 ; coarsenBFc; coarsenBFs; decBFc-sil-step
                 -- §3b (grant #6): the KA peers, the other inert peers' decodes
                 -- and the interleave non-offer the local KA split needs
                 ; absKAc; absKAs; absCSc; absCSs; absTSc; absTSs
                 ; absLNc; absLNs; absLFc; absLFs; coarsenKAc; ⦀-noOffer )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using ( BFcPos; BFsPos; decBFc; decBFs
              ; bcHead; bcSil; bcReq1; bcDone1; bcBlk1
              ; bsHead; bsSil; bsReq1; bsDone1; bsStart1; bsNoBlk1; bsBlk1; bsBatchDone1 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; med; nA; nB; nC; nD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( tableSpec-ev-inv; nothing-absurd )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink blkA
  using ( ClientIo; ServerIo )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink6 blkA as SIL6
open SIL6 using ( Tbfc; Tbfs; mkMbfc; bfc-fire-blk; absBFs-ev-dir; absBFc-ev-dir
                ; BundleCSEvR-abs; bcscEB; bcssEB
                ; BundleKAEvR-abs; bkacEB; bkasEB
                ; BundleTSEvR-abs; btscEB; btssEB
                ; BundleLNEvR-abs; blncEB; blnsEB
                ; BundleLFEvR-abs; blfcEB; blfsEB
                ; absBundleCS-ev-prod; absBundleKA-ev-prod; absBundleTS-ev-prod
                ; absBundleLN-ev-prod; absBundleLF-ev-prod
                )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( BFcHasBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleEvo blkA
  using ( BFsHasBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValFill blkA
  using ( blkPayload )
-- §1c: the banked producer-site half of the write-ownership fact
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeFillSource blkA
  using ( PlIsBlk; blockFill-forces-srv )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeCliIoDec blkA
  using ( decBFc-sendBF-succ; decBFc-receiveBF-succ
        -- §6: the READ decode's third component IS the frozen classifier's second arm
        ; BfcIoSucc
        -- (grant #7) the ROW-carrying inversions and the two row types
        ; decBFc-sendBF-succ-row; decBFc-receiveBF-succ-row )
import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeCliIoDec blkA as CLI
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvIoDec blkA
  using ( decBFs-sendBF-succ; decBFs-receiveBF-succ
        -- (grant #7) ditto on the server side
        ; decBFs-sendBF-succ-row; decBFs-receiveBF-succ-row )
import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvIoDec blkA as SRV
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleIoEvo blkA
  using ( BundleBFEvRio; bioCli; bioSrv; absBundleBF-ev-io-evo )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeNodeIoEvo blkA
  using ( CliFact; SrvFact; IoFacts; BundleEvo; NoCliReadAt
        ; AllCliFacts; AllSrvFacts; top-nodes-io-evoP
        -- §6: the FROZEN successor-directed classifiers and their four-slot
        -- families, which the PAIRED instance reports beside the ⁺ ones
        ; CliIoCls; SrvIoCls; AllCliIoCls; AllSrvIoCls
        -- (grant #7) the fixed-slot ownership PAIRS the widened cone hands over
        ; NoCliIoAt; NoSrvIoAt
        -- §1c: the SERVER mirror of the fixed-slot ownership premise (grant #1)
        ; NoSrvWriteAt
        -- §3b: the THIRD fact family and its eight-slot cone view (grant #6)
        ; InertFact; AllInertFacts
        -- (T5, grant #11) the FOURTH family — the CS SERVERS — and its two-slot
        -- cone view.  §4's two ChainSync clauses are where it is answered.
        ; CssFact; AllCssFacts
        -- (T6c, grant #12) the FIFTH family — the CS CLIENTS — plus the two new
        -- cone views (the up-hop servers and the four clients).  `AllCssFacts` is
        -- UNCHANGED, so `LiveDrvBF`'s four io arms keep their premise types.
        ; CscFact; AllCssUpFacts; AllCscFacts )
-- (T5, grant #11) the CS row layer, one layer down: the row-carrying 12-peer peel
-- and the coarse row it delivers are what the new fact family CARRIES, and both were
-- landed by T4 (`absBundleCS-ev-prod⁺` is generic in the CS event, and
-- `ιCS (sendCS l d) = input l d N2N_ChainSync` DEFINITIONALLY — `NetworkPar:184-185`
-- — which is why the io labels need no new peel at all)
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveCSRow blkA
  using ( CSsRow; BundleCSEvR-abs⁺; bcscEB⁺; bcssEB⁺; absBundleCS-ev-prod⁺
        -- (T6c, grant #12) the CLIENT row the peel already recovers (and `bdP` used
        -- to DISCARD), and the two key pins that turn a fired CS row into the fired
        -- DIRECTION — which is what certifies the co-located peer at the same key
        ; CScRow; cscRow-key; cssRow-key )

-- §3b (grant #6): the frozen KA client and the ONE bundle inversion that reports
-- its freeze — shared with `LiveLegApiCone`, whose `done` labels can move the
-- same slot
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveKAFrozen blkA
  using ( KAcAtHead; kaW-send; kaW-recv; KAFire; kaFireF; kaFire )

------------------------------------------------------------------------
-- (1) THE TWO STRENGTHENED PER-PEER FACTS.
--
-- Both keep the frozen classifiers' SHAPE — a disjunction whose FIRST arm is
-- `bfc ≡ bfc′` — because that arm is what the four-node dispatch puts in every
-- non-fired slot (`IoFacts.cRefl`/`sRefl`).  The strengthening is entirely in the
-- arms the FIRED slot supplies.
------------------------------------------------------------------------

-- a BF CLIENT's io evolution, PREDECESSOR-negative: fixed, or it was not holding
-- a block BEFORE the io.  (`bcBlk1 b` offers only the api `recvBFBlock`, so a
-- holding client can neither read nor write the wire — hence a client that DID
-- fire an io was not holding, and one that did not fire is fixed.)
CliInKeep : (bfc bfc′ : BFcPos) → Set
CliInKeep bfc bfc′ = (bfc ≡ bfc′) ⊎ (BFcHasBlk bfc → ⊥)

-- THE PRODUCER-SITE POSITIVE ANSWER, label-directed: on a wire WRITE the fired
-- server was at `bsBlk1 b` and the write is at its OWN key carrying exactly `b`.
-- `⊥` off an `input` label: no other io shape can move a block OUT of a server.
SrvWroteBlk : (k : Link) (kd : Dir) (bfs : BFsPos)
              {X : Set 0ℓ} → Net_Api Payload X → X → Set
SrvWroteBlk k kd bfs (input l₀ d₀ id₀) x =
  Σ[ b ∈ Block ] (bfs ≡ bsBlk1 b)
    × (k ≡ l₀) × (kd ≡ d₀) × (N2N_BlockFetch ≡ id₀) × (x ≡ blkPayload b)
SrvWroteBlk k kd bfs _ _ = ⊥

-- a BF SERVER's io evolution, PREDECESSOR-directed and in THREE arms: fixed /
-- it was not holding / it wrote its block to its own cell (see the header on why
-- the middle arm is not optional)
SrvIoCls⁺ : SrvFact
SrvIoCls⁺ k kd bfs bfs′ e a =
  (bfs ≡ bfs′) ⊎ ((BFsHasBlk bfs → ⊥) ⊎ SrvWroteBlk k kd bfs e a)

-- THE READER-IDENTIFYING HALF (leaf 4, session-53): on a BF wire READ at the
-- slot's OWN key `(k , kd)` whose payload carries a block, THIS slot holds
-- exactly that block afterwards.  `⊤` off an `output` label: no other io shape
-- moves a block INTO a client.  This is the half `CliBlkVal` does NOT give — it
-- lives inside the frozen classifier's THIRD arm, and the other two arms (fixed
-- / ¬-holding successor) say nothing about who fired.
CliRead⁺ : (k : Link) (kd : Dir) (q : BFcPos)
           {X : Set 0ℓ} → Net_Api Payload X → X → Set
CliRead⁺ k kd q (output l₀ d₀ id₀) x =
    (k ≡ l₀) → (kd ≡ d₀) → (N2N_BlockFetch ≡ id₀)
  → (b : Block) (t0 : Time) (md : Mode) (ln : Length)
  → x ≡ (t0 , md , ln , blockFetch (MsgBlock b)) → q ≡ bcBlk1 b
CliRead⁺ k kd q _ _ = ⊤

-- the client fact as a `CliFact`: the PREDECESSOR-negative keep (leaves 2, 3)
-- AND the reader identification (leaf 4)
CliIoCls⁺ : CliFact
CliIoCls⁺ k kd bfc bfc′ e a = CliInKeep bfc bfc′ × CliRead⁺ k kd bfc′ e a

------------------------------------------------------------------------
-- (1b)  *** THE PAIRED FACTS — SESSION-55, TokenExcl (P1). ***
--
-- The exclusions of `LiveTokenExcl` need the FROZEN, SUCCESSOR-directed
-- classifiers (`PipeNodeIoEvo.CliIoCls`/`SrvIoCls`) at THE SAME successor the ⁺
-- cone binds: a client that holds at `s′` either held at `s` or JUST READ (the
-- frozen third arm), and a server never GAINS on an io (the frozen second arm).
-- The ⁺ facts are PREDECESSOR-directed and cannot deliver either — but the arms
-- that prove them are already computed and DISCARDED at the four callbacks of §3:
-- `decBFs-{send,receive}BF-succ`'s fourth component IS `BFsHasBlk bfs′ → ⊥`
-- (`PipeSrvIoDec:193`/`:257`) and `decBFc-{send,receive}BF-succ`'s fourth is
-- `BFcHasBlk bfc′ → ⊥` resp. `BfcIoSucc` (`PipeCliIoDec:271`/`:308`), which is
-- LITERALLY the frozen classifier's second disjunct.  So the fix is a FACT
-- WIDENING off witnesses in hand, not a second dispatch: the cone runs ONCE at
-- the PAIRED facts and reports both directions at one successor.
--
-- WHY A PAIR AND NOT A THIRD ARM.  A disjunct would WEAKEN the fact; the two
-- directions are independent and both are needed at the same slot.  The ⁺-only
-- view is recovered by `proj₁` (§5's `bd⁺`/`facts⁺`/`top-nodes-io-evo⁺` keep
-- their exact former types, so `LiveLegStep` sees no change at all).
------------------------------------------------------------------------

------------------------------------------------------------------------
-- (1b′)  *** THE FIRED COARSE ROW — grant #7, the io half of the `ChanLeg` join. ***
--
-- The two adjacency-reporting facts.  Either the peer is FIXED — and then the io
-- was no BF io of that peer's ROLE at its key at all, which is the cone's ownership
-- pair (grant #7 widened `cRefl`/`sRefl` to hand over BOTH directions) — or its
-- coarse table FIRED, and the fact IS the row `LiveChanInv`'s §4b producers turn
-- into a `SrvSendAdj`/`CliReadAdj`/… in one application.
--
-- WHY THE FIXED ARM CARRIES THE OWNERSHIP PAIR, and why grant #7 had to widen the
-- cone for it: a leg's cell is ONE slot that BOTH of its peers write and read, so
-- "the cell filled while both of the hop's peers stayed fixed" is a case the join
-- must REFUTE (the channel invariant's `cvReq` is genuinely false at such a state).
-- The pair is exactly the refutation: at the fired key one of the two roles owns
-- the io, so the OTHER peer's fixed answer contradicts the fired label.
------------------------------------------------------------------------

-- the row itself, label-directed (the two io shapes carry it; nothing else can)
CliRowAt : (k : Link) (kd : Dir) (bfc bfc′ : BFcPos)
           {X : Set 0ℓ} → Net_Api Payload X → X → Set
CliRowAt k kd bfc bfc′ (input  l₀ d₀ N2N_BlockFetch) x = CLI.CliSendRow k kd l₀ d₀ bfc bfc′ x
CliRowAt k kd bfc bfc′ (output l₀ d₀ N2N_BlockFetch) x = CLI.CliReadRow k kd l₀ d₀ bfc bfc′ x
CliRowAt k kd bfc bfc′ _ _ = ⊥

-- … and the client's adjacency fact: fixed-and-not-the-owner, or the fired row
CliRowP : (k : Link) (kd : Dir) (bfc bfc′ : BFcPos)
          {X : Set 0ℓ} → Net_Api Payload X → X → Set
CliRowP k kd bfc bfc′ e a =
  ((bfc ≡ bfc′) × NoCliIoAt k kd N2N_BlockFetch e a) ⊎ CliRowAt k kd bfc bfc′ e a

-- the server's row, label-directed
SrvRowAt : (k : Link) (kd : Dir) (bfs bfs′ : BFsPos)
           {X : Set 0ℓ} → Net_Api Payload X → X → Set
SrvRowAt k kd bfs bfs′ (input  l₀ d₀ N2N_BlockFetch) x = SRV.SrvSendRow k kd l₀ d₀ bfs bfs′ x
SrvRowAt k kd bfs bfs′ (output l₀ d₀ N2N_BlockFetch) x = SRV.SrvReadRow k kd l₀ d₀ bfs bfs′ x
SrvRowAt k kd bfs bfs′ _ _ = ⊥

-- … and the server's adjacency fact
SrvRowP : (k : Link) (kd : Dir) (bfs bfs′ : BFsPos)
          {X : Set 0ℓ} → Net_Api Payload X → X → Set
SrvRowP k kd bfs bfs′ e a =
  ((bfs ≡ bfs′) × NoSrvIoAt k kd N2N_BlockFetch e a) ⊎ SrvRowAt k kd bfs bfs′ e a

-- *** (T5, grant #11) THE CS SERVER's io fact — the fourth family's instance. ***
-- The BF pair above needs a label-DIRECTED row (`CliRowAt`/`SrvRowAt`) because its
-- rows are stated at the two io shapes only; the CS row does NOT, because
-- `LiveCSRow.CSsRow` is already event-generic — it is the coarse table applied to
-- the fired label, whatever the label is.  So the fact is two lines and the consumer
-- needs no channel dispatch: at a position with no io row (`ccIdle`, `csCanAwait` —
-- `LiveCSRow` §4b's four refutations) the fired-row arm is refuted directly.
--
-- The fixed arm carries NO ownership certificate, unlike `SrvRowP`'s: the fact does
-- not identify a writer, so grant #11's `csRefl` was premise-free (grant #6's
-- `iRefl` shape).
--
-- *** (T6c) THIS FAMILY IS FROZEN, and that is deliberate. ***  Its four consumers
-- are `LiveDrvBF`'s io arms; grant #12's needs are met by the two families BELOW,
-- carried BESIDE it in the pair `CssPairP`, so not one landed premise type moves.
CssRowP : CssFact
CssRowP k kd css css′ e a = (css ≡ css′) ⊎ CSsRow k kd e a css css′

-- *** (T6c, grant #12) THE LABEL-DIRECTED CS io FACTS — the shape the channel
-- INVARIANT's join needs, and the two reasons it differs from `CssRowP`. ***
--
-- (i) LABEL-DIRECTED.  A consumer holding the bare `⊎` at `input l₀ d₀ id₀` for a
-- FOREIGN channel must refute a `csSnxt` row at a VARIABLE position, and that does
-- not reduce: Agda's clause matching blocks on the first blocked pattern, so the
-- table's catch-all (`NodeSpecs:490`) is unreachable while the position is a
-- variable (measured at T6c: `[UnequalTerms] … input l₀ d₀ N2N_BlockFetch … !=
-- nothing`).  Refuting it position by position is ~110 clauses across the four
-- tables; directing the FACT costs nothing, because `bdP` below already answers
-- `inj₁ refl` at all twenty-five non-CS clauses — the label-directed answer there is
-- `refl`.  This is exactly why the BF pair above is label-directed too.
--
-- (ii) THE FIXED ARM CARRIES THE OWNERSHIP CERTIFICATE.  The join's io arms must
-- refute "the CS cell filled while BOTH of the hop's peers stayed fixed", and two
-- fixities are not a contradiction: the hop's two peers share the key `(link , hi)`
-- (node A's server and node B's client on AB; node B's server and node D's client on
-- BD), so link ownership cannot separate them and only the payload's ROLE can.  That
-- is grant #7's argument at the ChainSync channel, which is why grant #12 made the
-- ownership predicates `IDs`-parametric instead of mirroring them.
CssIoRowP : CssFact
CssIoRowP k kd css css′ (input l₀ d₀ N2N_ChainSync) x =
  ((css ≡ css′) × NoSrvIoAt k kd N2N_ChainSync (input l₀ d₀ N2N_ChainSync) x)
  ⊎ CSsRow k kd (input l₀ d₀ N2N_ChainSync) x css css′
CssIoRowP k kd css css′ (output l₀ d₀ N2N_ChainSync) x =
  ((css ≡ css′) × NoSrvIoAt k kd N2N_ChainSync (output l₀ d₀ N2N_ChainSync) x)
  ⊎ CSsRow k kd (output l₀ d₀ N2N_ChainSync) x css css′
CssIoRowP k kd css css′ _ _ = css ≡ css′

-- … and the CS CLIENT mirror, the family grant #12 exists for
CscIoRowP : CscFact
CscIoRowP k kd csc csc′ (input l₀ d₀ N2N_ChainSync) x =
  ((csc ≡ csc′) × NoCliIoAt k kd N2N_ChainSync (input l₀ d₀ N2N_ChainSync) x)
  ⊎ CScRow k kd (input l₀ d₀ N2N_ChainSync) x csc csc′
CscIoRowP k kd csc csc′ (output l₀ d₀ N2N_ChainSync) x =
  ((csc ≡ csc′) × NoCliIoAt k kd N2N_ChainSync (output l₀ d₀ N2N_ChainSync) x)
  ⊎ CScRow k kd (output l₀ d₀ N2N_ChainSync) x csc csc′
CscIoRowP k kd csc csc′ _ _ = csc ≡ csc′

-- the CS SERVER slot's PAIRED fact: grant #11's frozen one beside grant #12's
-- label-directed one, at one and the same successor — the `CliIoClsP` shape
CssPairP : CssFact
CssPairP k kd css css′ e a =
  CssRowP k kd css css′ e a × CssIoRowP k kd css css′ e a

-- the label-directed SERVER fixity witness, at every label (the dispatch is
-- unavoidable — the fact itself is label-directed).  This is `csRefl`'s answer.
cssIoRow-fix : (k : Link) (kd : Dir) (css : SN.CSsPos)
               {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
             → NoSrvIoAt k kd N2N_ChainSync e a → CssIoRowP k kd css css e a
cssIoRow-fix k kd css {e = input  _ _ N2N_ChainSync}    nw = inj₁ (refl , nw)
cssIoRow-fix k kd css {e = input  _ _ N2N_BlockFetch}   nw = refl
cssIoRow-fix k kd css {e = input  _ _ N2N_KeepAlive}    nw = refl
cssIoRow-fix k kd css {e = input  _ _ N2N_TxSubmission} nw = refl
cssIoRow-fix k kd css {e = input  _ _ N2N_LeiosNotify}  nw = refl
cssIoRow-fix k kd css {e = input  _ _ N2N_LeiosFetch}   nw = refl
cssIoRow-fix k kd css {e = output _ _ N2N_ChainSync}    nw = inj₁ (refl , nw)
cssIoRow-fix k kd css {e = output _ _ N2N_BlockFetch}   nw = refl
cssIoRow-fix k kd css {e = output _ _ N2N_KeepAlive}    nw = refl
cssIoRow-fix k kd css {e = output _ _ N2N_TxSubmission} nw = refl
cssIoRow-fix k kd css {e = output _ _ N2N_LeiosNotify}  nw = refl
cssIoRow-fix k kd css {e = output _ _ N2N_LeiosFetch}   nw = refl
cssIoRow-fix k kd css {e = done   _ _ _} nw = refl
cssIoRow-fix k kd css {e = apiCS  _ _ _} nw = refl
cssIoRow-fix k kd css {e = apiBF  _ _ _} nw = refl
cssIoRow-fix k kd css {e = apiKA  _ _ _} nw = refl
cssIoRow-fix k kd css {e = apiTS  _ _ _} nw = refl
cssIoRow-fix k kd css {e = apiLN  _ _ _} nw = refl
cssIoRow-fix k kd css {e = apiLF  _ _ _} nw = refl
cssIoRow-fix k kd css {e = sndmsg _ _ _} nw = refl
cssIoRow-fix k kd css {e = rcvmsg _ _ _} nw = refl
cssIoRow-fix k kd css {e = tx     _ _ _} nw = refl
cssIoRow-fix k kd css {e = sndack _ _ _} nw = refl
cssIoRow-fix k kd css {e = rcvack _ _ _} nw = refl
cssIoRow-fix k kd css {e = ack    _ _ _} nw = refl
cssIoRow-fix k kd css {e = store  _ _ _} nw = refl
cssIoRow-fix k kd css {e = env    _ _ _} nw = refl
cssIoRow-fix k kd css {e = break  _}     nw = refl

-- … the CLIENT twin, `cscRefl`'s answer
cscIoRow-fix : (k : Link) (kd : Dir) (csc : SN.CScPos)
               {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
             → NoCliIoAt k kd N2N_ChainSync e a → CscIoRowP k kd csc csc e a
cscIoRow-fix k kd csc {e = input  _ _ N2N_ChainSync}    nb = inj₁ (refl , nb)
cscIoRow-fix k kd csc {e = input  _ _ N2N_BlockFetch}   nb = refl
cscIoRow-fix k kd csc {e = input  _ _ N2N_KeepAlive}    nb = refl
cscIoRow-fix k kd csc {e = input  _ _ N2N_TxSubmission} nb = refl
cscIoRow-fix k kd csc {e = input  _ _ N2N_LeiosNotify}  nb = refl
cscIoRow-fix k kd csc {e = input  _ _ N2N_LeiosFetch}   nb = refl
cscIoRow-fix k kd csc {e = output _ _ N2N_ChainSync}    nb = inj₁ (refl , nb)
cscIoRow-fix k kd csc {e = output _ _ N2N_BlockFetch}   nb = refl
cscIoRow-fix k kd csc {e = output _ _ N2N_KeepAlive}    nb = refl
cscIoRow-fix k kd csc {e = output _ _ N2N_TxSubmission} nb = refl
cscIoRow-fix k kd csc {e = output _ _ N2N_LeiosNotify}  nb = refl
cscIoRow-fix k kd csc {e = output _ _ N2N_LeiosFetch}   nb = refl
cscIoRow-fix k kd csc {e = done   _ _ _} nb = refl
cscIoRow-fix k kd csc {e = apiCS  _ _ _} nb = refl
cscIoRow-fix k kd csc {e = apiBF  _ _ _} nb = refl
cscIoRow-fix k kd csc {e = apiKA  _ _ _} nb = refl
cscIoRow-fix k kd csc {e = apiTS  _ _ _} nb = refl
cscIoRow-fix k kd csc {e = apiLN  _ _ _} nb = refl
cscIoRow-fix k kd csc {e = apiLF  _ _ _} nb = refl
cscIoRow-fix k kd csc {e = sndmsg _ _ _} nb = refl
cscIoRow-fix k kd csc {e = rcvmsg _ _ _} nb = refl
cscIoRow-fix k kd csc {e = tx     _ _ _} nb = refl
cscIoRow-fix k kd csc {e = sndack _ _ _} nb = refl
cscIoRow-fix k kd csc {e = rcvack _ _ _} nb = refl
cscIoRow-fix k kd csc {e = ack    _ _ _} nb = refl
cscIoRow-fix k kd csc {e = store  _ _ _} nb = refl
cscIoRow-fix k kd csc {e = env    _ _ _} nb = refl
cscIoRow-fix k kd csc {e = break  _}     nb = refl

-- the PAIRED client fact: the ⁺ (predecessor-directed) pair, the frozen
-- (successor-directed) classifier AND (grant #7, trailing) the fired row, at one
-- and the same successor
CliIoClsP : CliFact
CliIoClsP k kd bfc bfc′ e a =
  CliIoCls⁺ k kd bfc bfc′ e a × CliIoCls k kd bfc bfc′ e a × CliRowP k kd bfc bfc′ e a

------------------------------------------------------------------------
-- (1c)  *** THE WRITE-OWNERSHIP HALF — SESSION-55, TokenExcl (P2). ***
--
-- `PipeFillSource.blockFill-forces-srv` says a BLOCK-carrying cell fill forces
-- `BFsHasBlk` of the FIRING server.  What the exclusions need is the same fact
-- ABOUT THE LEG'S OWN SERVER, i.e. the IDENTIFICATION of the firing peer with the
-- slot — and that is not free at a slot that did not move, because a bundle's
-- CLIENT shares the link.  `PipeNodeIoEvo`'s §1c (grant #1's second exercise)
-- supplies the missing premise `NoSrvWriteAt` at every fixed slot, exactly as its
-- §1b supplies `NoCliReadAt` for the READ direction; here the two answers meet.
------------------------------------------------------------------------

-- the WRITE-OWNERSHIP answer: a BF wire WRITE at the slot's OWN key carrying a
-- BLOCK came out of THIS slot, which held the block and no longer does.  `⊤` off
-- an `input` label: no other io shape moves a block OUT of a server.
SrvWriteOwn : (k : Link) (kd : Dir) (bfs bfs′ : BFsPos)
              {X : Set 0ℓ} → Net_Api Payload X → X → Set
SrvWriteOwn k kd bfs bfs′ (input l₀ d₀ id₀) x =
    (k ≡ l₀) → (kd ≡ d₀) → (N2N_BlockFetch ≡ id₀) → PlIsBlk x
  → BFsHasBlk bfs × (BFsHasBlk bfs′ → ⊥)
SrvWriteOwn k kd bfs bfs′ _ _ = ⊤

-- the write-hit is VACUOUS on a channel other than BlockFetch
writeHit-chan : (k : Link) (kd : Dir) (bfs bfs′ : BFsPos)
                (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
  → (N2N_BlockFetch ≡ id₀ → ⊥) → SrvWriteOwn k kd bfs bfs′ (input l₀ d₀ id₀) x
writeHit-chan k kd bfs bfs′ l₀ d₀ id₀ x ne = λ _ _ e3 _ → ⊥-elim (ne e3)

-- the write-hit is VACUOUS at a key whose direction is not the fired one
writeHit-dir : (k : Link) (kd : Dir) (bfs bfs′ : BFsPos)
               (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
  → (kd ≡ d₀ → ⊥) → SrvWriteOwn k kd bfs bfs′ (input l₀ d₀ id₀) x
writeHit-dir k kd bfs bfs′ l₀ d₀ id₀ x ne = λ _ e2 _ _ → ⊥-elim (ne e2)

-- a BLOCK payload on a WRITE is SERVER-originated (`msgOrigin (MsgBlock b) ≡
-- FromResponder`), which is what lets the fixed slot's ownership premise fire
plIsBlk⇒srvIo : (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
              → PlIsBlk x → ServerIo (input l₀ d₀ id₀) x
plIsBlk⇒srvIo _ _ _ (_ , _ , _ , blockFetch (MsgBlock _))         blk = refl
plIsBlk⇒srvIo _ _ _ (_ , _ , _ , blockFetch (MsgRequestRange _))  ()
plIsBlk⇒srvIo _ _ _ (_ , _ , _ , blockFetch MsgStartBatch)        ()
plIsBlk⇒srvIo _ _ _ (_ , _ , _ , blockFetch MsgNoBlocks)          ()
plIsBlk⇒srvIo _ _ _ (_ , _ , _ , blockFetch MsgBatchDone)         ()
plIsBlk⇒srvIo _ _ _ (_ , _ , _ , blockFetch MsgClientDone)        ()
plIsBlk⇒srvIo _ _ _ (_ , _ , _ , chainSync _)                     ()
plIsBlk⇒srvIo _ _ _ (_ , _ , _ , keepAlive _)                     ()
plIsBlk⇒srvIo _ _ _ (_ , _ , _ , txSubmission _)                  ()
plIsBlk⇒srvIo _ _ _ (_ , _ , _ , leiosNotify _)                   ()
plIsBlk⇒srvIo _ _ _ (_ , _ , _ , leiosFetch _)                    ()

-- THE FIXED-SLOT WRITE-OWNERSHIP ANSWER: sixteen label shapes make it vacuous;
-- on the seventeenth (`input`) the ownership premise refutes the hypotheses
writeOwn-fix : (k : Link) (kd : Dir) (bfs : BFsPos)
               {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
             → NoSrvWriteAt k kd N2N_BlockFetch e a → SrvWriteOwn k kd bfs bfs e a
writeOwn-fix k kd bfs {e = input  l₀ d₀ id₀} {a = x} nw =
  λ e1 e2 e3 blk → ⊥-elim (nw e1 e2 e3 (plIsBlk⇒srvIo l₀ d₀ id₀ x blk))
writeOwn-fix k kd bfs {e = output _ _ _} nw = tt
writeOwn-fix k kd bfs {e = done   _ _ _} nw = tt
writeOwn-fix k kd bfs {e = apiCS  _ _ _} nw = tt
writeOwn-fix k kd bfs {e = apiBF  _ _ _} nw = tt
writeOwn-fix k kd bfs {e = apiKA  _ _ _} nw = tt
writeOwn-fix k kd bfs {e = apiTS  _ _ _} nw = tt
writeOwn-fix k kd bfs {e = apiLN  _ _ _} nw = tt
writeOwn-fix k kd bfs {e = apiLF  _ _ _} nw = tt
writeOwn-fix k kd bfs {e = sndmsg _ _ _} nw = tt
writeOwn-fix k kd bfs {e = rcvmsg _ _ _} nw = tt
writeOwn-fix k kd bfs {e = tx     _ _ _} nw = tt
writeOwn-fix k kd bfs {e = sndack _ _ _} nw = tt
writeOwn-fix k kd bfs {e = rcvack _ _ _} nw = tt
writeOwn-fix k kd bfs {e = ack    _ _ _} nw = tt
writeOwn-fix k kd bfs {e = store  _ _ _} nw = tt
writeOwn-fix k kd bfs {e = env    _ _ _} nw = tt
writeOwn-fix k kd bfs {e = break  _}     nw = tt

-- the PAIRED server fact: the three ⁺ arms, the frozen "never gains" one AND the
-- write-ownership answer (P2)
SrvIoClsP : SrvFact
SrvIoClsP k kd bfs bfs′ e a =
  SrvIoCls⁺ k kd bfs bfs′ e a × SrvIoCls bfs bfs′ × SrvWriteOwn k kd bfs bfs′ e a
  × SrvRowP k kd bfs bfs′ e a

-- NOTE (P1, measured): the READ decode's own third component IS the frozen
-- classifier's second disjunct — `BfcIoSucc l d l′ d′ bfc′ a` unfolds to
-- `(BFcHasBlk bfc′ → ⊥) ⊎ BlkReadAt l d bfc′ (output l′ d′ N2N_BlockFetch) a` —
-- so `§3`'s read callback answers with a bare `inj₂ cls`.  It is NOT wrapped in a
-- named bridge: the payload occurs only under the STUCK applications `PlIsBlk`/
-- `CliBlkVal`, so a bridge's implicit `x` is unsolvable and eleven
-- `[UnsolvedConstraints]` follow (the campaign's explicit-index rule, third
-- measured instance).  Inline at the concrete payload, everything reduces.

-- the read-hit is VACUOUS when the read payload is not a block
readHit-noBlk : (k : Link) (kd : Dir) (q : BFcPos)
                {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {x : Payload}
  → ((b : Block) (t0 : Time) (md : Mode) (ln : Length)
       → x ≢ (t0 , md , ln , blockFetch (MsgBlock b)))
  → CliRead⁺ k kd q (output l₀ d₀ id₀) x
readHit-noBlk k kd q nb = λ _ _ _ b t0 md ln hx → ⊥-elim (nb b t0 md ln hx)

-- the read-hit is VACUOUS on a channel other than BlockFetch
readHit-chan : (k : Link) (kd : Dir) (q : BFcPos)
               {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {x : Payload}
  → (N2N_BlockFetch ≡ id₀ → ⊥) → CliRead⁺ k kd q (output l₀ d₀ id₀) x
readHit-chan k kd q ne = λ _ _ e3 → ⊥-elim (ne e3)

-- the read-hit is VACUOUS at a key whose direction is not the fired one
readHit-dir : (k : Link) (kd : Dir) (q : BFcPos)
              {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {x : Payload}
  → (kd ≡ d₀ → ⊥) → CliRead⁺ k kd q (output l₀ d₀ id₀) x
readHit-dir k kd q ne = λ _ e2 _ → ⊥-elim (ne e2)

-- the block a wire payload carries is unique (`MsgBlock` is a constructor)
blkPl-inj : {t0 t1 : Time} {md md1 : Mode} {ln ln1 : Length} {b b1 : Block}
  → (t0 , md , ln , blockFetch (MsgBlock b)) ≡ (t1 , md1 , ln1 , blockFetch (MsgBlock b1))
  → b ≡ b1
blkPl-inj refl = refl

-- the FIXED-SLOT answer: a client slot that did not move satisfies BOTH halves
-- as soon as the io was not its own client-role block read.  Fifteen label
-- shapes make the read-hit vacuous; on the sixteenth the ownership premise
-- refutes the hypotheses (`msgOrigin (MsgBlock b) ≡ FromResponder`, so a block
-- payload on an `output` IS a client-role read).
cRefl⁺ : (l : Link) (d : Dir) (bfc : BFcPos)
         {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
       → NoCliReadAt l d N2N_BlockFetch e a → CliIoCls⁺ l d bfc bfc e a
cRefl⁺ l d bfc {e = output l₀ d₀ id₀} nb =
  inj₁ refl , λ e1 e2 e3 b t0 md ln hx →
    ⊥-elim (nb e1 e2 e3 (subst (λ z → ClientIo (output l₀ d₀ id₀) z) (sym hx) refl))
cRefl⁺ l d bfc {e = input  _ _ _} nb = inj₁ refl , tt
cRefl⁺ l d bfc {e = done   _ _ _} nb = inj₁ refl , tt
cRefl⁺ l d bfc {e = apiCS  _ _ _} nb = inj₁ refl , tt
cRefl⁺ l d bfc {e = apiBF  _ _ _} nb = inj₁ refl , tt
cRefl⁺ l d bfc {e = apiKA  _ _ _} nb = inj₁ refl , tt
cRefl⁺ l d bfc {e = apiTS  _ _ _} nb = inj₁ refl , tt
cRefl⁺ l d bfc {e = apiLN  _ _ _} nb = inj₁ refl , tt
cRefl⁺ l d bfc {e = apiLF  _ _ _} nb = inj₁ refl , tt
cRefl⁺ l d bfc {e = sndmsg _ _ _} nb = inj₁ refl , tt
cRefl⁺ l d bfc {e = rcvmsg _ _ _} nb = inj₁ refl , tt
cRefl⁺ l d bfc {e = tx     _ _ _} nb = inj₁ refl , tt
cRefl⁺ l d bfc {e = sndack _ _ _} nb = inj₁ refl , tt
cRefl⁺ l d bfc {e = rcvack _ _ _} nb = inj₁ refl , tt
cRefl⁺ l d bfc {e = ack    _ _ _} nb = inj₁ refl , tt
cRefl⁺ l d bfc {e = store  _ _ _} nb = inj₁ refl , tt
cRefl⁺ l d bfc {e = env    _ _ _} nb = inj₁ refl , tt
cRefl⁺ l d bfc {e = break  _}     nb = inj₁ refl , tt

------------------------------------------------------------------------
-- (2) THE FOUR PEER LEMMAS.  Each is stated about the peer's OWN step and its
-- PREDECESSOR position only — no successor is named — so each composes with the
-- frozen decode instead of re-deriving it.  The holding position's clause is the
-- frozen decode's own `nothing-absurd` refutation; every other position makes
-- `BF{c,s}HasBlk` reduce to `⊥`, so the premise IS the answer.
------------------------------------------------------------------------

-- a BF client that fires the wire WRITE was not holding a block
cli-nohold-send : (l : Link) (d : Dir) (bfc : BFcPos)
    {l′ : Link} {d′ : Dir} {a : Payload} {M : NetProc}
  → absBFc l d bfc ─[ ev (evl (evLabel Payload (ιBF (BF.sendBF l′ d′)) a)) ]─► M
  → BFcHasBlk bfc → ⊥
cli-nohold-send l d (bcHead st) step h = h
cli-nohold-send l d (bcSil st)  step h = h
cli-nohold-send l d (bcReq1 r)  step h = h
cli-nohold-send l d bcDone1     step h = h
cli-nohold-send l d (bcBlk1 b)  step h
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq = nothing-absurd ceq

-- a BF client that fires the wire READ was not holding a block
cli-nohold-recv : (l : Link) (d : Dir) (bfc : BFcPos)
    {l′ : Link} {d′ : Dir} {a : Payload} {M : NetProc}
  → absBFc l d bfc ─[ ev (evl (evLabel Payload (ιBF (BF.receiveBF l′ d′)) a)) ]─► M
  → BFcHasBlk bfc → ⊥
cli-nohold-recv l d (bcHead st) step h = h
cli-nohold-recv l d (bcSil st)  step h = h
cli-nohold-recv l d (bcReq1 r)  step h = h
cli-nohold-recv l d bcDone1     step h = h
cli-nohold-recv l d (bcBlk1 b)  step h
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq = nothing-absurd ceq

-- a BF server that fires the wire READ was not holding a block
srv-nohold-recv : (l : Link) (d : Dir) (bfs : BFsPos)
    {l′ : Link} {d′ : Dir} {a : Payload} {M : NetProc}
  → absBFs l d bfs ─[ ev (evl (evLabel Payload (ιBF (BF.receiveBF l′ d′)) a)) ]─► M
  → BFsHasBlk bfs → ⊥
srv-nohold-recv l d (bsHead st)   step h = h
srv-nohold-recv l d (bsSil st)    step h = h
srv-nohold-recv l d (bsReq1 r)    step h = h
srv-nohold-recv l d bsDone1       step h = h
srv-nohold-recv l d bsStart1      step h = h
srv-nohold-recv l d bsNoBlk1      step h = h
srv-nohold-recv l d bsBatchDone1  step h = h
srv-nohold-recv l d (bsBlk1 b)    step h
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsBlk1 b)) step
... | q′ , ceq , Meq = nothing-absurd ceq

-- THE PRODUCER-SITE LEMMA: a BF server that fires the wire WRITE either was not
-- holding a block, or was at `bsBlk1 b` and wrote exactly `b` at its own key.
-- (The three key/payload decisions are `PipeSrvIoDec.decBFs-sendBF-succ`'s own,
-- `:226-237`; only carrying their answers was missing.)
srv-write-fact : (l : Link) (d : Dir) (bfs : BFsPos)
    {l′ : Link} {d′ : Dir} {a : Payload} {M : NetProc}
  → absBFs l d bfs ─[ ev (evl (evLabel Payload (ιBF (BF.sendBF l′ d′)) a)) ]─► M
  → (BFsHasBlk bfs → ⊥)
    ⊎ Σ[ b ∈ Block ] (bfs ≡ bsBlk1 b) × (l ≡ l′) × (d ≡ d′) × (a ≡ blkPayload b)
srv-write-fact l d (bsHead st)  step = inj₁ (λ h → h)
srv-write-fact l d (bsSil st)   step = inj₁ (λ h → h)
srv-write-fact l d (bsReq1 r)   step = inj₁ (λ h → h)
srv-write-fact l d bsDone1      step = inj₁ (λ h → h)
srv-write-fact l d bsStart1     step = inj₁ (λ h → h)
srv-write-fact l d bsNoBlk1     step = inj₁ (λ h → h)
srv-write-fact l d bsBatchDone1 step = inj₁ (λ h → h)
srv-write-fact l d (bsBlk1 b) {l′} {d′} {a} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsBlk1 b)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl
      with a ≟ (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b))
...     | yes refl = inj₂ (b , refl , refl , refl , refl)
...     | no _ = ⊥-elim (nothing-absurd ceq)
srv-write-fact l d (bsBlk1 b) step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
srv-write-fact l d (bsBlk1 b) step | q′ , ceq , Meq | no _    | _    = ⊥-elim (nothing-absurd ceq)

-- THE READER-SITE DECODE, with the successor NAMED.  `decBFc-receiveBF-succ`
-- answers with the DISJUNCTION `BfcIoSucc`, whose ¬-holding arm the type permits
-- even at a `MsgBlock` payload — and once the successor is bound existentially by
-- that `with`, no second peel can identify it (session-30's negative result).  So
-- the block-payload slice of `bfc-recv-hstep` is re-derived here with the
-- successor written out: `bcHead stStreaming --MsgBlock b--> bcBlk1 b` is the ONE
-- block-gaining client row, and the other three heads have no `MsgBlock` row at
-- all.  HEAD slice first, so `bcSil` reuses it behind one τ.
-- (P1: the two KEY equalities ride along — the positive clause decides them
-- anyway, and the frozen classifier's read arm `BlkReadAt` needs exactly them)
cli-read-blk-h : (l : Link) (d : Dir) (st : BF.BFState)
    {l′ : Link} {d′ : Dir} {t0 : Time} {md : Mode} {ln : Length}
    {b : Block} {M : NetProc}
  → absBFc l d (bcHead st)
      ─[ ev (evl (evLabel Payload (ιBF (BF.receiveBF l′ d′))
                    (t0 , md , ln , blockFetch (MsgBlock b)))) ]─► M
  → (decBFc l d (bcHead st)
       ─[ ev (evl (evLabel Payload (ιBF (BF.receiveBF l′ d′))
                     (t0 , md , ln , blockFetch (MsgBlock b)))) ]─► decBFc l d (bcBlk1 b))
    × (M ≡ absBFc l d (bcBlk1 b)) × (l′ ≡ l) × (d′ ≡ d)
    × CLI.CliReadRow l d l′ d′ (bcHead st) (bcBlk1 b) (t0 , md , ln , blockFetch (MsgBlock b))
cli-read-blk-h l d BF.stIdle step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
cli-read-blk-h l d BF.stBusy step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
cli-read-blk-h l d BF.stDone step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
cli-read-blk-h l d BF.stStreaming {l′} {d′} {t0} {md} {ln} {b} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl =
        SIL6.RFBF.renameMap-ev-fwd (bfc-fire-blk l d b t0 md ln)
      , mkMbfc l d (bcBlk1 b) Meq (just-injective (sym ceq)) , refl , refl
      , (refl , refl , trans ceq (cong just (just-injective (sym ceq))))
cli-read-blk-h l d BF.stStreaming step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
cli-read-blk-h l d BF.stStreaming step | q′ , ceq , Meq | no _    | _    = ⊥-elim (nothing-absurd ceq)

-- the whole-position form: only the two head-shaped positions can read at all
cli-read-blk : (l : Link) (d : Dir) (bfc : BFcPos)
    {l′ : Link} {d′ : Dir} {t0 : Time} {md : Mode} {ln : Length}
    {b : Block} {M : NetProc}
  → absBFc l d bfc
      ─[ ev (evl (evLabel Payload (ιBF (BF.receiveBF l′ d′))
                    (t0 , md , ln , blockFetch (MsgBlock b)))) ]─► M
  → (decBFc l d bfc
       ═[ ev (evl (evLabel Payload (ιBF (BF.receiveBF l′ d′))
                     (t0 , md , ln , blockFetch (MsgBlock b)))) ]═► decBFc l d (bcBlk1 b))
    × (M ≡ absBFc l d (bcBlk1 b)) × (l′ ≡ l) × (d′ ≡ d)
    × CLI.CliReadRow l d l′ d′ bfc (bcBlk1 b) (t0 , md , ln , blockFetch (MsgBlock b))
cli-read-blk l d (bcHead st) step with cli-read-blk-h l d st step
... | f , m , k1 , k2 , row = wev τ*-refl f τ*-refl , m , k1 , k2 , row
-- (grant #7) the SIL position's row IS the HEAD's (`absBFc-sil-collapse`)
cli-read-blk l d (bcSil st) step with cli-read-blk-h l d st step
... | f , m , k1 , k2 , row = wev (τ*-step (decBFc-sil-step l d st) τ*-refl) f τ*-refl , m , k1 , k2 , row
cli-read-blk l d (bcReq1 r) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
cli-read-blk l d bcDone1 step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc bcDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
cli-read-blk l d (bcBlk1 b₀) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b₀)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

------------------------------------------------------------------------
-- (3) THE FOUR STRENGTHENED BUNDLE CALLBACKS.  Each is the frozen decode paired
-- with its peer lemma: the decode names the successor and the concrete weak run,
-- the lemma supplies the ⁺ arm.  `absBundleBF-ev-io-evo` takes them as `Cf`/`Sf`
-- callbacks, so the twelve-peer peel itself is REUSED, not re-mirrored.
------------------------------------------------------------------------

-- the wire-WRITE client callback, at `CliIoClsP` (the reader-identifying half is
-- `⊤` on an `input` label — a write moves nothing IN; the FROZEN half is the
-- decode's own fourth component, `BFcHasBlk bfc′ → ⊥`, no longer discarded)
kcSend : (l : Link) (cl sv : Dir) → cl ≢ sv → (bfc : BFcPos) {l′ : Link} {d′ : Dir}
    {a : Payload} {P′ : NetProc}
  → absBFc l cl bfc ─[ ev (evl (evLabel Payload (ιBF (BF.sendBF l′ d′)) a)) ]─► P′
  → Σ[ bfc′ ∈ BFcPos ]
      (decBFc l cl bfc ═[ ev (evl (evLabel Payload (ιBF (BF.sendBF l′ d′)) a)) ]═► decBFc l cl bfc′)
      × (P′ ≡ absBFc l cl bfc′)
      × (CliIoClsP l cl bfc bfc′ (input l′ d′ N2N_BlockFetch) a × (sv ≡ d′ → ⊥))
kcSend l cl sv cl≢sv bfc sM with decBFc-sendBF-succ-row l cl bfc sM
... | bfc′ , run , Meq , nb , row = bfc′ , run , Meq
    , (((inj₂ (cli-nohold-send l cl bfc sM) , tt) , inj₂ (inj₁ nb) , inj₂ row)
      , λ q → cl≢sv (sym (trans q (absBFc-ev-dir l cl bfc sM))))

-- the wire-READ client callback, at `CliIoCls⁺`.  ELEVEN payload shapes: ten
-- make the read-hit vacuous and delegate to the frozen decode; the `MsgBlock`
-- one goes through `cli-read-blk`, which names the successor — the frozen
-- decode's own answer cannot, and that is the whole of leaf 4's client side.
kcRecv : (l : Link) (cl sv : Dir) → cl ≢ sv → (bfc : BFcPos) {l′ : Link} {d′ : Dir}
    {a : Payload} {P′ : NetProc}
  → absBFc l cl bfc ─[ ev (evl (evLabel Payload (ιBF (BF.receiveBF l′ d′)) a)) ]─► P′
  → Σ[ bfc′ ∈ BFcPos ]
      (decBFc l cl bfc ═[ ev (evl (evLabel Payload (ιBF (BF.receiveBF l′ d′)) a)) ]═► decBFc l cl bfc′)
      × (P′ ≡ absBFc l cl bfc′)
      -- (grant #7) … and, as `kcSend` already did on the WRITE side, the CO-LOCATED
      -- SERVER's ownership refutation: a client io fires at the client's own
      -- direction, so a bundle read by the client is no read at `sv`
      × (CliIoClsP l cl bfc bfc′ (output l′ d′ N2N_BlockFetch) a × (sv ≡ d′ → ⊥))
kcRecv l cl sv cl≢sv bfc {a = t0 , md , ln , blockFetch (MsgBlock b)} sM
  with cli-read-blk l cl bfc sM
... | run , Meq , k1 , k2 , row = bcBlk1 b , run , Meq
                , (((inj₂ (cli-nohold-recv l cl bfc sM)
                   , λ _ _ _ b₁ _ _ _ hx → cong bcBlk1 (blkPl-inj hx))
                  , inj₂ (inj₂ (k1 , k2 , tt , refl)) , inj₂ row)
                , λ q → cl≢sv (sym (trans q (absBFc-ev-dir l cl bfc sM))))
kcRecv l cl sv cl≢sv bfc {a = _ , _ , _ , blockFetch (MsgRequestRange _)} sM with decBFc-receiveBF-succ-row l cl bfc sM
... | bfc′ , run , Meq , cls , row = bfc′ , run , Meq
    , (((inj₂ (cli-nohold-recv l cl bfc sM) , readHit-noBlk l cl bfc′ (λ _ _ _ _ → λ ()))
       , inj₂ cls , inj₂ row)
      , λ q → cl≢sv (sym (trans q (absBFc-ev-dir l cl bfc sM))))
kcRecv l cl sv cl≢sv bfc {a = _ , _ , _ , blockFetch MsgStartBatch} sM with decBFc-receiveBF-succ-row l cl bfc sM
... | bfc′ , run , Meq , cls , row = bfc′ , run , Meq
    , (((inj₂ (cli-nohold-recv l cl bfc sM) , readHit-noBlk l cl bfc′ (λ _ _ _ _ → λ ()))
       , inj₂ cls , inj₂ row)
      , λ q → cl≢sv (sym (trans q (absBFc-ev-dir l cl bfc sM))))
kcRecv l cl sv cl≢sv bfc {a = _ , _ , _ , blockFetch MsgNoBlocks} sM with decBFc-receiveBF-succ-row l cl bfc sM
... | bfc′ , run , Meq , cls , row = bfc′ , run , Meq
    , (((inj₂ (cli-nohold-recv l cl bfc sM) , readHit-noBlk l cl bfc′ (λ _ _ _ _ → λ ()))
       , inj₂ cls , inj₂ row)
      , λ q → cl≢sv (sym (trans q (absBFc-ev-dir l cl bfc sM))))
kcRecv l cl sv cl≢sv bfc {a = _ , _ , _ , blockFetch MsgBatchDone} sM with decBFc-receiveBF-succ-row l cl bfc sM
... | bfc′ , run , Meq , cls , row = bfc′ , run , Meq
    , (((inj₂ (cli-nohold-recv l cl bfc sM) , readHit-noBlk l cl bfc′ (λ _ _ _ _ → λ ()))
       , inj₂ cls , inj₂ row)
      , λ q → cl≢sv (sym (trans q (absBFc-ev-dir l cl bfc sM))))
kcRecv l cl sv cl≢sv bfc {a = _ , _ , _ , blockFetch MsgClientDone} sM with decBFc-receiveBF-succ-row l cl bfc sM
... | bfc′ , run , Meq , cls , row = bfc′ , run , Meq
    , (((inj₂ (cli-nohold-recv l cl bfc sM) , readHit-noBlk l cl bfc′ (λ _ _ _ _ → λ ()))
       , inj₂ cls , inj₂ row)
      , λ q → cl≢sv (sym (trans q (absBFc-ev-dir l cl bfc sM))))
kcRecv l cl sv cl≢sv bfc {a = _ , _ , _ , chainSync _} sM with decBFc-receiveBF-succ-row l cl bfc sM
... | bfc′ , run , Meq , cls , row = bfc′ , run , Meq
    , (((inj₂ (cli-nohold-recv l cl bfc sM) , readHit-noBlk l cl bfc′ (λ _ _ _ _ → λ ()))
       , inj₂ cls , inj₂ row)
      , λ q → cl≢sv (sym (trans q (absBFc-ev-dir l cl bfc sM))))
kcRecv l cl sv cl≢sv bfc {a = _ , _ , _ , keepAlive _} sM with decBFc-receiveBF-succ-row l cl bfc sM
... | bfc′ , run , Meq , cls , row = bfc′ , run , Meq
    , (((inj₂ (cli-nohold-recv l cl bfc sM) , readHit-noBlk l cl bfc′ (λ _ _ _ _ → λ ()))
       , inj₂ cls , inj₂ row)
      , λ q → cl≢sv (sym (trans q (absBFc-ev-dir l cl bfc sM))))
kcRecv l cl sv cl≢sv bfc {a = _ , _ , _ , txSubmission _} sM with decBFc-receiveBF-succ-row l cl bfc sM
... | bfc′ , run , Meq , cls , row = bfc′ , run , Meq
    , (((inj₂ (cli-nohold-recv l cl bfc sM) , readHit-noBlk l cl bfc′ (λ _ _ _ _ → λ ()))
       , inj₂ cls , inj₂ row)
      , λ q → cl≢sv (sym (trans q (absBFc-ev-dir l cl bfc sM))))
kcRecv l cl sv cl≢sv bfc {a = _ , _ , _ , leiosNotify _} sM with decBFc-receiveBF-succ-row l cl bfc sM
... | bfc′ , run , Meq , cls , row = bfc′ , run , Meq
    , (((inj₂ (cli-nohold-recv l cl bfc sM) , readHit-noBlk l cl bfc′ (λ _ _ _ _ → λ ()))
       , inj₂ cls , inj₂ row)
      , λ q → cl≢sv (sym (trans q (absBFc-ev-dir l cl bfc sM))))
kcRecv l cl sv cl≢sv bfc {a = _ , _ , _ , leiosFetch _} sM with decBFc-receiveBF-succ-row l cl bfc sM
... | bfc′ , run , Meq , cls , row = bfc′ , run , Meq
    , (((inj₂ (cli-nohold-recv l cl bfc sM) , readHit-noBlk l cl bfc′ (λ _ _ _ _ → λ ()))
       , inj₂ cls , inj₂ row)
      , λ q → cl≢sv (sym (trans q (absBFc-ev-dir l cl bfc sM))))

-- the wire-WRITE server callback, at `SrvIoCls⁺` (the ONE genuinely positive arm
-- of the whole io axis: `sym` on the two key equalities re-orients the decode's
-- `l′ ≡ l` into the classifier's `k ≡ l₀`, and the id equality is `refl` because
-- the dispatcher's clause has already matched `N2N_BlockFetch`)
ksSend : (l : Link) (cl sv : Dir) → cl ≢ sv → (bfs : BFsPos) {l′ : Link} {d′ : Dir}
    {a : Payload} {P′ : NetProc}
  → absBFs l sv bfs ─[ ev (evl (evLabel Payload (ιBF (BF.sendBF l′ d′)) a)) ]─► P′
  → Σ[ bfs′ ∈ BFsPos ]
      (decBFs l sv bfs ═[ ev (evl (evLabel Payload (ιBF (BF.sendBF l′ d′)) a)) ]═► decBFs l sv bfs′)
      × (P′ ≡ absBFs l sv bfs′)
      × (SrvIoClsP l sv bfs bfs′ (input l′ d′ N2N_BlockFetch) a × (cl ≡ d′ → ⊥))
ksSend l cl sv cl≢sv bfs sM with decBFs-sendBF-succ-row l sv bfs sM | srv-write-fact l sv bfs sM
... | bfs′ , run , Meq , nb′ , row | inj₁ nb = bfs′ , run , Meq
    , ((inj₂ (inj₁ nb) , inj₂ nb′
       , (λ _ _ _ blk → blockFill-forces-srv l sv bfs sM blk , nb′) , inj₂ row)
      , λ q → cl≢sv (trans q (absBFs-ev-dir l sv bfs sM)))
... | bfs′ , run , Meq , nb′ , row | inj₂ (b , hb , le , de , pay) =
      bfs′ , run , Meq
    , ((inj₂ (inj₂ (b , hb , le , de , refl , pay)) , inj₂ nb′
       , (λ _ _ _ blk → blockFill-forces-srv l sv bfs sM blk , nb′) , inj₂ row)
      , λ q → cl≢sv (trans q (absBFs-ev-dir l sv bfs sM)))

-- the wire-READ server callback, at `SrvIoCls⁺` (a reader never wrote, so the
-- third arm is `⊥` at an `output` label and the answer is the middle one) PLUS
-- the CO-LOCATED CLIENT's ownership answer: a server io fires at the server's own
-- direction (`absBFs-ev-dir`), so a bundle read by the server is not a read at
-- `cl`.  It has to ride HERE because the bundle datatype's `bioSrv` arm does not
-- carry the server's step, and the callback's own fact is the caller's choice.
ksRecv : (l : Link) (cl sv : Dir) → cl ≢ sv → (bfs : BFsPos) {l′ : Link} {d′ : Dir}
    {a : Payload} {P′ : NetProc}
  → absBFs l sv bfs ─[ ev (evl (evLabel Payload (ιBF (BF.receiveBF l′ d′)) a)) ]─► P′
  → Σ[ bfs′ ∈ BFsPos ]
      (decBFs l sv bfs ═[ ev (evl (evLabel Payload (ιBF (BF.receiveBF l′ d′)) a)) ]═► decBFs l sv bfs′)
      × (P′ ≡ absBFs l sv bfs′)
      × (SrvIoClsP l sv bfs bfs′ (output l′ d′ N2N_BlockFetch) a × (cl ≡ d′ → ⊥))
ksRecv l cl sv cl≢sv bfs sM with decBFs-receiveBF-succ-row l sv bfs sM
... | bfs′ , run , Meq , nb′ , row =
      bfs′ , run , Meq
    , ((inj₂ (inj₁ (srv-nohold-recv l sv bfs sM)) , inj₂ nb′ , tt , inj₂ row)
      , λ q → cl≢sv (trans q (absBFs-ev-dir l sv bfs sM)))

-- the io instance of grant #6's third fact family: the KA-client freeze is
-- PRESERVED.  Conditional, and it has to be — a KA client that is NOT at its head
-- really does fire wire events (`kcWmsg` writes, `kcAwait` reads), so the only
-- true statement is the preservation one.
InertKeep : InertFact
InertKeep l cl ip ip′ e a = KAcAtHead ip → KAcAtHead ip′

------------------------------------------------------------------------
-- (3b′) THE FIXED-SLOT OWNERSHIP BUILDERS (grant #7).  Eight one-liners: at a
-- NON-BlockFetch channel no BF peer owns the io (the ten non-BF clauses of the
-- dispatcher), and at a BF io whose DIRECTION is not this slot's the same holds
-- (the four BF arms, where the fired peer's own direction is known).
------------------------------------------------------------------------

-- a fixed CLIENT at a non-BF wire WRITE owns nothing
cliOwn-in-chan : (k : Link) (kd : Dir) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
               {id : IDs} → (id ≡ id₀ → ⊥) → NoCliIoAt k kd id (input l₀ d₀ id₀) x
cliOwn-in-chan k kd l₀ d₀ id₀ x ne = tt , λ _ _ e3 _ → ⊥-elim (ne e3)

-- … at a non-BF wire READ
cliOwn-out-chan : (k : Link) (kd : Dir) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
                {id : IDs} → (id ≡ id₀ → ⊥) → NoCliIoAt k kd id (output l₀ d₀ id₀) x
cliOwn-out-chan k kd l₀ d₀ id₀ x ne = (λ _ _ e3 _ → ⊥-elim (ne e3)) , tt

-- the SERVER mirrors
srvOwn-in-chan : (k : Link) (kd : Dir) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
               {id : IDs} → (id ≡ id₀ → ⊥) → NoSrvIoAt k kd id (input l₀ d₀ id₀) x
srvOwn-in-chan k kd l₀ d₀ id₀ x ne = (λ _ _ e3 _ → ⊥-elim (ne e3)) , tt

srvOwn-out-chan : (k : Link) (kd : Dir) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
                {id : IDs} → (id ≡ id₀ → ⊥) → NoSrvIoAt k kd id (output l₀ d₀ id₀) x
srvOwn-out-chan k kd l₀ d₀ id₀ x ne = tt , λ _ _ e3 _ → ⊥-elim (ne e3)

-- a fixed CLIENT at a BF write fired in ANOTHER direction owns nothing
cliOwn-in-dir : (k : Link) (kd : Dir) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
              {id : IDs} → (kd ≡ d₀ → ⊥) → NoCliIoAt k kd id (input l₀ d₀ id₀) x
cliOwn-in-dir k kd l₀ d₀ id₀ x ne = tt , λ _ e2 _ _ → ⊥-elim (ne e2)

-- … and at a BF read
cliOwn-out-dir : (k : Link) (kd : Dir) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
               {id : IDs} → (kd ≡ d₀ → ⊥) → NoCliIoAt k kd id (output l₀ d₀ id₀) x
cliOwn-out-dir k kd l₀ d₀ id₀ x ne = (λ _ e2 _ _ → ⊥-elim (ne e2)) , tt

-- the SERVER mirrors
srvOwn-in-dir : (k : Link) (kd : Dir) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
              {id : IDs} → (kd ≡ d₀ → ⊥) → NoSrvIoAt k kd id (input l₀ d₀ id₀) x
srvOwn-in-dir k kd l₀ d₀ id₀ x ne = (λ _ e2 _ _ → ⊥-elim (ne e2)) , tt

srvOwn-out-dir : (k : Link) (kd : Dir) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
               {id : IDs} → (kd ≡ d₀ → ⊥) → NoSrvIoAt k kd id (output l₀ d₀ id₀) x
srvOwn-out-dir k kd l₀ d₀ id₀ x ne = tt , λ _ e2 _ _ → ⊥-elim (ne e2)

------------------------------------------------------------------------
-- (4) THE STRENGTHENED BUNDLE DISPATCHER — `PipeBundleIoEvo.absBundleG-io-evo`'s
-- twenty-seven clauses at the ⁺ facts, in `BundleEvo`'s Σ form.  The five
-- non-BF channels keep BOTH BF slots LITERAL, so both facts are `inj₁ refl`; the
-- two BF clauses route the fired peer through the callbacks of §3.  Since grant
-- #6 every clause also answers the INERT fact: twenty-five of them pass `ip`'s
-- `kac` through untouched (`λ h → h`), and the two KA-channel ones take it from
-- `kaFire`.
------------------------------------------------------------------------

-- the io bundle inversion at the ⁺ per-peer facts
bdP : (l : Link) (cl sv : Dir) → cl ≢ sv
    → (csc : SN.CScPos) (css : SN.CSsPos) (bfc : BFcPos) (bfs : BFsPos)
      (ip : SN.InertPos)
    → {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
    → ioES .mem (X , e) a
    → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X e a)) ]─► Bd′
    → BundleEvo CliIoClsP SrvIoClsP InertKeep CssPairP CscIoRowP l cl sv csc css bfc bfs ip e a Bd′
bdP l cl sv cl≢sv csc css bfc bfs ip {e = input l′ d′ N2N_ChainSync} {a = a} iomem step
  with absBundleCS-ev-prod⁺ l cl sv cl≢sv csc css bfc bfs ip {e₁ = CS.sendCS l′ d′} step
... | bcscEB⁺ csc′ eq run row = csc′ , css , bfc , bfs , ip , eq , run , ((inj₁ refl , tt) , inj₁ refl , inj₁ (refl , cliOwn-in-chan l cl l′ d′ N2N_ChainSync a (λ ()))) , (inj₁ refl , inj₁ refl , writeHit-chan l sv bfs bfs l′ d′ N2N_ChainSync a (λ ()) , inj₁ (refl , srvOwn-in-chan l sv l′ d′ N2N_ChainSync a (λ ()))) , (λ h → h) , (inj₁ refl , inj₁ (refl , srvOwn-in-dir l sv l′ d′ N2N_ChainSync a (λ q → cl≢sv (sym (trans q (proj₂ (cscRow-key l cl (SStep.coarsenCSc csc) (CS.sendCS l′ d′) row))))))) , inj₂ row
... | bcssEB⁺ css′ eq run row = csc , css′ , bfc , bfs , ip , eq , run , ((inj₁ refl , tt) , inj₁ refl , inj₁ (refl , cliOwn-in-chan l cl l′ d′ N2N_ChainSync a (λ ()))) , (inj₁ refl , inj₁ refl , writeHit-chan l sv bfs bfs l′ d′ N2N_ChainSync a (λ ()) , inj₁ (refl , srvOwn-in-chan l sv l′ d′ N2N_ChainSync a (λ ()))) , (λ h → h) , (inj₂ row , inj₂ row) , inj₁ (refl , cliOwn-in-dir l cl l′ d′ N2N_ChainSync a (λ q → cl≢sv (trans q (proj₂ (cssRow-key l sv (SStep.coarsenCSs css) (CS.sendCS l′ d′) row)))))
bdP l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_ChainSync} {a = a} iomem step
  with absBundleCS-ev-prod⁺ l cl sv cl≢sv csc css bfc bfs ip {e₁ = CS.receiveCS l′ d′} step
... | bcscEB⁺ csc′ eq run row = csc′ , css , bfc , bfs , ip , eq , run , ((inj₁ refl , readHit-chan l cl bfc (λ ())) , inj₁ refl , inj₁ (refl , cliOwn-out-chan l cl l′ d′ N2N_ChainSync a (λ ()))) , (inj₁ refl , inj₁ refl , tt , inj₁ (refl , srvOwn-out-chan l sv l′ d′ N2N_ChainSync a (λ ()))) , (λ h → h) , (inj₁ refl , inj₁ (refl , srvOwn-out-dir l sv l′ d′ N2N_ChainSync a (λ q → cl≢sv (sym (trans q (proj₂ (cscRow-key l cl (SStep.coarsenCSc csc) (CS.receiveCS l′ d′) row))))))) , inj₂ row
... | bcssEB⁺ css′ eq run row = csc , css′ , bfc , bfs , ip , eq , run , ((inj₁ refl , readHit-chan l cl bfc (λ ())) , inj₁ refl , inj₁ (refl , cliOwn-out-chan l cl l′ d′ N2N_ChainSync a (λ ()))) , (inj₁ refl , inj₁ refl , tt , inj₁ (refl , srvOwn-out-chan l sv l′ d′ N2N_ChainSync a (λ ()))) , (λ h → h) , (inj₂ row , inj₂ row) , inj₁ (refl , cliOwn-out-dir l cl l′ d′ N2N_ChainSync a (λ q → cl≢sv (trans q (proj₂ (cssRow-key l sv (SStep.coarsenCSs css) (CS.receiveCS l′ d′) row)))))
-- the two KA-channel clauses go through §3b's local split, which is the ONE
-- inversion that reports the freeze fact beside the successor it builds
bdP l cl sv cl≢sv csc css bfc bfs ip {e = input l′ d′ N2N_KeepAlive} {a = a} iomem step
  with kaFire l cl sv cl≢sv csc css bfc bfs ip kaW-send step
... | kaFireF ip′ eq run frz = csc , css , bfc , bfs , ip′ , eq , run , ((inj₁ refl , tt) , inj₁ refl , inj₁ (refl , cliOwn-in-chan l cl l′ d′ N2N_KeepAlive a (λ ()))) , (inj₁ refl , inj₁ refl , writeHit-chan l sv bfs bfs l′ d′ N2N_KeepAlive a (λ ()) , inj₁ (refl , srvOwn-in-chan l sv l′ d′ N2N_KeepAlive a (λ ()))) , frz , (inj₁ refl , refl) , refl
bdP l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_KeepAlive} {a = a} iomem step
  with kaFire l cl sv cl≢sv csc css bfc bfs ip kaW-recv step
... | kaFireF ip′ eq run frz = csc , css , bfc , bfs , ip′ , eq , run , ((inj₁ refl , readHit-chan l cl bfc (λ ())) , inj₁ refl , inj₁ (refl , cliOwn-out-chan l cl l′ d′ N2N_KeepAlive a (λ ()))) , (inj₁ refl , inj₁ refl , tt , inj₁ (refl , srvOwn-out-chan l sv l′ d′ N2N_KeepAlive a (λ ()))) , frz , (inj₁ refl , refl) , refl
bdP l cl sv cl≢sv csc css bfc bfs ip {e = input l′ d′ N2N_TxSubmission} {a = a} iomem step
  with absBundleTS-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = TS.sendTS l′ d′} step
... | btscEB tsc′ eq run = csc , css , bfc , bfs , record ip { tsc = tsc′ } , eq , run , ((inj₁ refl , tt) , inj₁ refl , inj₁ (refl , cliOwn-in-chan l cl l′ d′ N2N_TxSubmission a (λ ()))) , (inj₁ refl , inj₁ refl , writeHit-chan l sv bfs bfs l′ d′ N2N_TxSubmission a (λ ()) , inj₁ (refl , srvOwn-in-chan l sv l′ d′ N2N_TxSubmission a (λ ()))) , (λ h → h) , (inj₁ refl , refl) , refl
... | btssEB tss′ eq run = csc , css , bfc , bfs , record ip { tss = tss′ } , eq , run , ((inj₁ refl , tt) , inj₁ refl , inj₁ (refl , cliOwn-in-chan l cl l′ d′ N2N_TxSubmission a (λ ()))) , (inj₁ refl , inj₁ refl , writeHit-chan l sv bfs bfs l′ d′ N2N_TxSubmission a (λ ()) , inj₁ (refl , srvOwn-in-chan l sv l′ d′ N2N_TxSubmission a (λ ()))) , (λ h → h) , (inj₁ refl , refl) , refl
bdP l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_TxSubmission} {a = a} iomem step
  with absBundleTS-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = TS.receiveTS l′ d′} step
... | btscEB tsc′ eq run = csc , css , bfc , bfs , record ip { tsc = tsc′ } , eq , run , ((inj₁ refl , readHit-chan l cl bfc (λ ())) , inj₁ refl , inj₁ (refl , cliOwn-out-chan l cl l′ d′ N2N_TxSubmission a (λ ()))) , (inj₁ refl , inj₁ refl , tt , inj₁ (refl , srvOwn-out-chan l sv l′ d′ N2N_TxSubmission a (λ ()))) , (λ h → h) , (inj₁ refl , refl) , refl
... | btssEB tss′ eq run = csc , css , bfc , bfs , record ip { tss = tss′ } , eq , run , ((inj₁ refl , readHit-chan l cl bfc (λ ())) , inj₁ refl , inj₁ (refl , cliOwn-out-chan l cl l′ d′ N2N_TxSubmission a (λ ()))) , (inj₁ refl , inj₁ refl , tt , inj₁ (refl , srvOwn-out-chan l sv l′ d′ N2N_TxSubmission a (λ ()))) , (λ h → h) , (inj₁ refl , refl) , refl
bdP l cl sv cl≢sv csc css bfc bfs ip {e = input l′ d′ N2N_LeiosNotify} {a = a} iomem step
  with absBundleLN-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = LN.sendLN l′ d′} step
... | blncEB lnc′ eq run = csc , css , bfc , bfs , record ip { lnc = lnc′ } , eq , run , ((inj₁ refl , tt) , inj₁ refl , inj₁ (refl , cliOwn-in-chan l cl l′ d′ N2N_LeiosNotify a (λ ()))) , (inj₁ refl , inj₁ refl , writeHit-chan l sv bfs bfs l′ d′ N2N_LeiosNotify a (λ ()) , inj₁ (refl , srvOwn-in-chan l sv l′ d′ N2N_LeiosNotify a (λ ()))) , (λ h → h) , (inj₁ refl , refl) , refl
... | blnsEB lns′ eq run = csc , css , bfc , bfs , record ip { lns = lns′ } , eq , run , ((inj₁ refl , tt) , inj₁ refl , inj₁ (refl , cliOwn-in-chan l cl l′ d′ N2N_LeiosNotify a (λ ()))) , (inj₁ refl , inj₁ refl , writeHit-chan l sv bfs bfs l′ d′ N2N_LeiosNotify a (λ ()) , inj₁ (refl , srvOwn-in-chan l sv l′ d′ N2N_LeiosNotify a (λ ()))) , (λ h → h) , (inj₁ refl , refl) , refl
bdP l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_LeiosNotify} {a = a} iomem step
  with absBundleLN-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = LN.receiveLN l′ d′} step
... | blncEB lnc′ eq run = csc , css , bfc , bfs , record ip { lnc = lnc′ } , eq , run , ((inj₁ refl , readHit-chan l cl bfc (λ ())) , inj₁ refl , inj₁ (refl , cliOwn-out-chan l cl l′ d′ N2N_LeiosNotify a (λ ()))) , (inj₁ refl , inj₁ refl , tt , inj₁ (refl , srvOwn-out-chan l sv l′ d′ N2N_LeiosNotify a (λ ()))) , (λ h → h) , (inj₁ refl , refl) , refl
... | blnsEB lns′ eq run = csc , css , bfc , bfs , record ip { lns = lns′ } , eq , run , ((inj₁ refl , readHit-chan l cl bfc (λ ())) , inj₁ refl , inj₁ (refl , cliOwn-out-chan l cl l′ d′ N2N_LeiosNotify a (λ ()))) , (inj₁ refl , inj₁ refl , tt , inj₁ (refl , srvOwn-out-chan l sv l′ d′ N2N_LeiosNotify a (λ ()))) , (λ h → h) , (inj₁ refl , refl) , refl
bdP l cl sv cl≢sv csc css bfc bfs ip {e = input l′ d′ N2N_LeiosFetch} {a = a} iomem step
  with absBundleLF-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = LF.sendLF l′ d′} step
... | blfcEB lfc′ eq run = csc , css , bfc , bfs , record ip { lfc = lfc′ } , eq , run , ((inj₁ refl , tt) , inj₁ refl , inj₁ (refl , cliOwn-in-chan l cl l′ d′ N2N_LeiosFetch a (λ ()))) , (inj₁ refl , inj₁ refl , writeHit-chan l sv bfs bfs l′ d′ N2N_LeiosFetch a (λ ()) , inj₁ (refl , srvOwn-in-chan l sv l′ d′ N2N_LeiosFetch a (λ ()))) , (λ h → h) , (inj₁ refl , refl) , refl
... | blfsEB lfs′ eq run = csc , css , bfc , bfs , record ip { lfs = lfs′ } , eq , run , ((inj₁ refl , tt) , inj₁ refl , inj₁ (refl , cliOwn-in-chan l cl l′ d′ N2N_LeiosFetch a (λ ()))) , (inj₁ refl , inj₁ refl , writeHit-chan l sv bfs bfs l′ d′ N2N_LeiosFetch a (λ ()) , inj₁ (refl , srvOwn-in-chan l sv l′ d′ N2N_LeiosFetch a (λ ()))) , (λ h → h) , (inj₁ refl , refl) , refl
bdP l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_LeiosFetch} {a = a} iomem step
  with absBundleLF-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = LF.receiveLF l′ d′} step
... | blfcEB lfc′ eq run = csc , css , bfc , bfs , record ip { lfc = lfc′ } , eq , run , ((inj₁ refl , readHit-chan l cl bfc (λ ())) , inj₁ refl , inj₁ (refl , cliOwn-out-chan l cl l′ d′ N2N_LeiosFetch a (λ ()))) , (inj₁ refl , inj₁ refl , tt , inj₁ (refl , srvOwn-out-chan l sv l′ d′ N2N_LeiosFetch a (λ ()))) , (λ h → h) , (inj₁ refl , refl) , refl
... | blfsEB lfs′ eq run = csc , css , bfc , bfs , record ip { lfs = lfs′ } , eq , run , ((inj₁ refl , readHit-chan l cl bfc (λ ())) , inj₁ refl , inj₁ (refl , cliOwn-out-chan l cl l′ d′ N2N_LeiosFetch a (λ ()))) , (inj₁ refl , inj₁ refl , tt , inj₁ (refl , srvOwn-out-chan l sv l′ d′ N2N_LeiosFetch a (λ ()))) , (λ h → h) , (inj₁ refl , refl) , refl
bdP l cl sv cl≢sv csc css bfc bfs ip {e = input l′ d′ N2N_BlockFetch} {a = a} iomem step
  with absBundleBF-ev-io-evo l cl sv cl≢sv csc css bfc bfs ip
         (λ z → CliIoClsP l cl bfc z (input l′ d′ N2N_BlockFetch) a × (sv ≡ d′ → ⊥))
         (λ z → SrvIoClsP l sv bfs z (input l′ d′ N2N_BlockFetch) a × (cl ≡ d′ → ⊥))
         {e₁ = BF.sendBF l′ d′} (kcSend l cl sv cl≢sv bfc) (ksSend l cl sv cl≢sv bfs) step
... | bioCli bfc′ eq run (cf , nd) =
      csc , css , bfc′ , bfs , ip , eq , run , cf
    , (inj₁ refl , inj₁ refl , writeHit-dir l sv bfs bfs l′ d′ N2N_BlockFetch a nd
      -- (grant #7) the client fired, so this write is not at the SERVER's direction
      , inj₁ (refl , srvOwn-in-dir l sv l′ d′ N2N_BlockFetch a nd)) , (λ h → h) , (inj₁ refl , refl) , refl
... | bioSrv bfs′ eq run (sf , nd) =
      csc , css , bfc , bfs′ , ip , eq , run
      -- (grant #7) … and symmetrically: the server fired, so not at the CLIENT's
    , ((inj₁ refl , tt) , inj₁ refl , inj₁ (refl , cliOwn-in-dir l cl l′ d′ N2N_BlockFetch a nd))
    , sf , (λ h → h) , (inj₁ refl , refl) , refl
bdP l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_BlockFetch} {a = a} iomem step
  with absBundleBF-ev-io-evo l cl sv cl≢sv csc css bfc bfs ip
         (λ z → CliIoClsP l cl bfc z (output l′ d′ N2N_BlockFetch) a × (sv ≡ d′ → ⊥))
         (λ z → SrvIoClsP l sv bfs z (output l′ d′ N2N_BlockFetch) a × (cl ≡ d′ → ⊥))
         {e₁ = BF.receiveBF l′ d′} (kcRecv l cl sv cl≢sv bfc) (ksRecv l cl sv cl≢sv bfs) step
... | bioCli bfc′ eq run (cf , nd) =
      csc , css , bfc′ , bfs , ip , eq , run , cf
    , (inj₁ refl , inj₁ refl , tt
      , inj₁ (refl , srvOwn-out-dir l sv l′ d′ N2N_BlockFetch a nd)) , (λ h → h) , (inj₁ refl , refl) , refl
... | bioSrv bfs′ eq run (sf , nd) =
      csc , css , bfc , bfs′ , ip , eq , run
    , ((inj₁ refl , readHit-dir l cl bfc nd) , inj₁ refl
      , inj₁ (refl , cliOwn-out-dir l cl l′ d′ N2N_BlockFetch a nd)) , sf , (λ h → h) , (inj₁ refl , refl) , refl
bdP l cl sv cl≢sv csc css bfc bfs ip {e = done   _ _ _} iomem step = ⊥-elim iomem
bdP l cl sv cl≢sv csc css bfc bfs ip {e = apiCS  _ _ _} iomem step = ⊥-elim iomem
bdP l cl sv cl≢sv csc css bfc bfs ip {e = apiBF  _ _ _} iomem step = ⊥-elim iomem
bdP l cl sv cl≢sv csc css bfc bfs ip {e = apiKA  _ _ _} iomem step = ⊥-elim iomem
bdP l cl sv cl≢sv csc css bfc bfs ip {e = apiTS  _ _ _} iomem step = ⊥-elim iomem
bdP l cl sv cl≢sv csc css bfc bfs ip {e = apiLN  _ _ _} iomem step = ⊥-elim iomem
bdP l cl sv cl≢sv csc css bfc bfs ip {e = apiLF  _ _ _} iomem step = ⊥-elim iomem
bdP l cl sv cl≢sv csc css bfc bfs ip {e = sndmsg _ _ _} iomem step = ⊥-elim iomem
bdP l cl sv cl≢sv csc css bfc bfs ip {e = rcvmsg _ _ _} iomem step = ⊥-elim iomem
bdP l cl sv cl≢sv csc css bfc bfs ip {e = tx     _ _ _} iomem step = ⊥-elim iomem
bdP l cl sv cl≢sv csc css bfc bfs ip {e = sndack _ _ _} iomem step = ⊥-elim iomem
bdP l cl sv cl≢sv csc css bfc bfs ip {e = rcvack _ _ _} iomem step = ⊥-elim iomem
bdP l cl sv cl≢sv csc css bfc bfs ip {e = ack    _ _ _} iomem step = ⊥-elim iomem
bdP l cl sv cl≢sv csc css bfc bfs ip {e = store  _ _ _} iomem step = ⊥-elim iomem
bdP l cl sv cl≢sv csc css bfc bfs ip {e = env    _ _ _} iomem step = ⊥-elim iomem
bdP l cl sv cl≢sv csc css bfc bfs ip {e = break  _}     iomem step = ⊥-elim iomem

------------------------------------------------------------------------
-- (5) THE TWO CONES — the frozen four-node dispatch at the PAIRED facts (§1b),
-- and the ⁺-only view PROJECTED out of it.  ONE line of content each:
-- everything else in this module exists to build the two fact records.
--
-- `facts⁺`/`top-nodes-io-evo⁺` keep their exact former TYPES, so `LiveLegStep`'s
-- `AllCli⁺`/`AllSrvIn⁺` and its four selectors are untouched by (P1); only
-- `bd⁺`'s BODY changes, from the dispatch itself to `proj₁` of the paired one.
------------------------------------------------------------------------

-- the fixed-slot answer at the PAIRED client fact: the ⁺ answer (which needs the
-- ownership premise) beside the frozen one (a slot that did not move IS fixed)
cReflP : (l : Link) (d : Dir) (bfc : BFcPos)
         {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
       → NoCliIoAt l d N2N_BlockFetch e a → CliIoClsP l d bfc bfc e a
cReflP l d bfc nb = cRefl⁺ l d bfc (proj₁ nb) , inj₁ refl , inj₁ (refl , nb)

-- the PAIRED fact interface: ONE cone call reports BOTH directions at ONE successor
factsP : IoFacts
factsP = record { Cf = CliIoClsP ; Sf = SrvIoClsP ; If = InertKeep
                -- (T5, grant #11) the FOURTH family: the tracked CS SERVERS' io fact,
                -- (T6c, grant #12) now PAIRED with its label-directed twin, and the
                -- FIFTH family beside it
                ; Csf = CssPairP ; Cscf = CscIoRowP ; bd = bdP
                -- (grant #7) the cone now hands over BOTH directions' ownership
                -- premises; the ⁺ halves read the one they need
                ; cRefl = cReflP
                ; sRefl = λ l d bfs nw →
                    (inj₁ refl , inj₁ refl , writeOwn-fix l d bfs (proj₁ nw)
                    , inj₁ (refl , nw))
                -- grant #6: a bundle that did not fire keeps its `InertPos`
                -- LITERALLY, so the fixed-slot answer is the identity
                ; iRefl = λ l cl ip h → h
                -- (grant #11) … and its CS server likewise for the frozen half;
                -- (T6c, grant #12) the label-directed half takes the ROLE certificate,
                -- and the CS CLIENT family's witness is its exact mirror
                ; csRefl = λ l sv css nw → (inj₁ refl , cssIoRow-fix l sv css nw)
                ; cscRefl = λ l cl csc nb → cscIoRow-fix l cl csc nb }

-- the ⁺-only bundle dispatcher, projected off the paired one
bd⁺ : (l : Link) (cl sv : Dir) → cl ≢ sv
    → (csc : SN.CScPos) (css : SN.CSsPos) (bfc : BFcPos) (bfs : BFsPos)
      (ip : SN.InertPos)
    → {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
    → ioES .mem (X , e) a
    → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X e a)) ]─► Bd′
    → BundleEvo CliIoCls⁺ SrvIoCls⁺ InertKeep CssPairP CscIoRowP l cl sv csc css bfc bfs ip e a Bd′
bd⁺ l cl sv cl≢sv csc css bfc bfs ip iomem step
  with bdP l cl sv cl≢sv csc css bfc bfs ip iomem step
... | csc′ , css′ , bfc′ , bfs′ , ip′ , eq , run , cf , sf , frz , qs , qc =
      csc′ , css′ , bfc′ , bfs′ , ip′ , eq , run , proj₁ cf , proj₁ sf , frz , qs , qc

-- the ⁺ fact interface
facts⁺ : IoFacts
facts⁺ = record { Cf = CliIoCls⁺ ; Sf = SrvIoCls⁺ ; If = InertKeep
                -- (grant #11) the same CS-server fact the paired dispatcher answers,
                -- (T6c) paired, and the fifth family
                ; Csf = CssPairP ; Cscf = CscIoRowP ; bd = bd⁺
                -- (grant #7) ditto: the ⁺ client answer needs the READ half
                ; cRefl = λ l d bfc nb → cRefl⁺ l d bfc (proj₁ nb)
                ; sRefl = λ l d bfs _ → inj₁ refl
                ; iRefl = λ l cl ip h → h
                -- (grant #11) the frozen half; (T6c) the label-directed half and the
                -- fifth family, exactly as in the paired record
                ; csRefl = λ l sv css nw → (inj₁ refl , cssIoRow-fix l sv css nw)
                ; cscRefl = λ l cl csc nb → cscIoRow-fix l cl csc nb }

-- TOP: the io cone with the two PREDECESSOR-directed slot families (leaves 1, 2
-- and 3 of the task-3 inventory, discharged)
top-nodes-io-evo⁺ : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ s′ ∈ SysState ] (med s ≡ med s′) × (M ≡ absNodesOf s′)
      × (nodesOf s ═[ ev (evl (evLabel X e a)) ]═► nodesOf s′)
      × AllCliFacts facts⁺ s s′ e a
      × AllSrvFacts facts⁺ s s′ e a
      × (SN.NodeStateA.prod-AB (nA s) ≡ SN.NodeStateA.prod-AB (nA s′))
      × (SN.NodeStateA.prod-AC (nA s) ≡ SN.NodeStateA.prod-AC (nA s′))
      × (SN.NodeStateB.cp-B (nB s) ≡ SN.NodeStateB.cp-B (nB s′))
      × (SN.NodeStateC.cp-C (nC s) ≡ SN.NodeStateC.cp-C (nC s′))
      × (SN.NodeStateD.cons-BD (nD s) ≡ SN.NodeStateD.cons-BD (nD s′))
      × (SN.NodeStateD.cons-CD (nD s) ≡ SN.NodeStateD.cons-CD (nD s′))
top-nodes-io-evo⁺ s iomem nodesStep =
  -- grant #6: the ⁺-only cone keeps its exact former TYPE (`LiveLegStep`'s four
  -- selectors are untouched), so the trailing inert slot is projected away here
  let (s′ , medEq , Meq , run , cli , srv , e1 , e2 , e3 , e4 , e5 , e6 , _) =
        top-nodes-io-evoP facts⁺ s iomem nodesStep
  in  s′ , medEq , Meq , run , cli , srv , e1 , e2 , e3 , e4 , e5 , e6

------------------------------------------------------------------------
-- (6) THE PAIRED CONE and its two FROZEN readings — TokenExcl (P1).
--
-- `LiveTokenExcl`'s io arms read the FROZEN families only; they take the PAIRED
-- ones because those are what a single cone call delivers, and the frozen
-- readings below are pure `proj₂`.  Stated as named families so the arms'
-- signatures name a cone OUTPUT and not a premise.
------------------------------------------------------------------------

-- the four tracked BF clients at the PAIRED fact
AllCliP : (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) → Set
AllCliP s s′ e a = AllCliFacts factsP s s′ e a

-- the four tracked BF servers at the PAIRED fact
AllSrvP : (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) → Set
AllSrvP s s′ e a = AllSrvFacts factsP s s′ e a

-- (T5, grant #11) the TWO tracked CS servers at the new fact — `dnCSs legBD` and
-- `dnCSs legCD`, in that order.  This is the slot the CS driver-tail coupling's io
-- arms read, and the whole reason the fourth channel exists.
AllCssP : (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) → Set
AllCssP s s′ e a = AllCssFacts factsP s s′ e a

-- (T6c, grant #12) the TWO tracked UP-hop CS servers (node A's) …
AllCssUpP : (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) → Set
AllCssUpP s s′ e a = AllCssUpFacts factsP s s′ e a

-- … and the FOUR tracked CS CLIENTS (the two relays' up-hop ones and node D's two
-- down-hop ones).  This is the family the CS channel invariant's join was blocked on.
AllCscP : (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) → Set
AllCscP s s′ e a = AllCscFacts factsP s s′ e a

-- the FROZEN client family, read off the paired one
frozenCli : (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
          → AllCliP s s′ e a → AllCliIoCls s s′ e a
-- (grant #7) the frozen half is now the MIDDLE component (the row is trailing)
frozenCli s s′ e a (c1 , c2 , c3 , c4) =
  proj₁ (proj₂ c1) , proj₁ (proj₂ c2) , proj₁ (proj₂ c3) , proj₁ (proj₂ c4)

-- the FROZEN server family, read off the paired one
frozenSrv : (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
          → AllSrvP s s′ e a → AllSrvIoCls s s′
frozenSrv s s′ e a (q1 , q2 , q3 , q4) =
  proj₁ (proj₂ q1) , proj₁ (proj₂ q2) , proj₁ (proj₂ q3) , proj₁ (proj₂ q4)

-- TOP (PAIRED): the io cone reporting the PREDECESSOR-directed ⁺ families AND
-- the FROZEN successor-directed ones at ONE AND THE SAME successor
top-nodes-io-evoP⁺ : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ s′ ∈ SysState ] (med s ≡ med s′) × (M ≡ absNodesOf s′)
      × (nodesOf s ═[ ev (evl (evLabel X e a)) ]═► nodesOf s′)
      × AllCliP s s′ e a
      × AllSrvP s s′ e a
      × (SN.NodeStateA.prod-AB (nA s) ≡ SN.NodeStateA.prod-AB (nA s′))
      × (SN.NodeStateA.prod-AC (nA s) ≡ SN.NodeStateA.prod-AC (nA s′))
      × (SN.NodeStateB.cp-B (nB s) ≡ SN.NodeStateB.cp-B (nB s′))
      × (SN.NodeStateC.cp-C (nC s) ≡ SN.NodeStateC.cp-C (nC s′))
      × (SN.NodeStateD.cons-BD (nD s) ≡ SN.NodeStateD.cons-BD (nD s′))
      × (SN.NodeStateD.cons-CD (nD s) ≡ SN.NodeStateD.cons-CD (nD s′))
      -- grant #6: the eight bundles' KA-client freeze answers, trailing
      × AllInertFacts factsP s s′ e a
      -- (T5, grant #11) … and the two tracked CS SERVERS' facts behind those
      × AllCssP s s′ e a
      -- (T6c, grant #12) … and, TRAILING, the two UP-hop CS servers and the four CS
      -- CLIENTS
      × AllCssUpP s s′ e a
      × AllCscP s s′ e a
top-nodes-io-evoP⁺ = top-nodes-io-evoP factsP
