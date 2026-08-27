{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — THE STRENGTHENED api (VISIBLE) CONE for `LegInv`
-- (`Praos.LiveLegApiCone`), session-54 / Task-3 slice B.
--
-- WHY THIS MODULE EXISTS.  `LiveLegStep`'s visible arm takes its three api-side
-- step facts as the module premise `VisLeaves` (leaves 6, 7 and 9 of the task-3
-- inventory) because every api-side server witness the frozen visible cone
-- exposes is SUCCESSOR-negative or value-only:
--
--   `PipeSrvInv.UpSrvEvo l s s′
--       = (upSrv l s ≡ upSrv l s′) ⊎ ((BFsHasBlk (upSrv l s′) → ⊥) ⊎ ProdSent …)`
--   `PipeBundleEvo.BfsSucc l d bfs′ e a
--       = (BFsHasBlk bfs′ → ⊥) ⊎ Σ[ b″ ] label-pin × (bfs′ ≡ bsBlk1 b″)`
--   `PipeEvDriverCone.SrvValEvo l bfs bfs′ e a = (bfs ≡ bfs′) ⊎ BfsSucc l hi bfs′ e a`
--
-- and an OCCUPANCY transport needs the PREDECESSOR-directed form: "a slot that
-- HELD a block is api-fixed" (`bsBlk1`'s only outgoing row is the io wire WRITE,
-- never an api), plus, on the producer's / relay's own `sendBFBlock`, the
-- POSITIVE answer "the co-firing server landed exactly the sent block".  The
-- successor is bound EXISTENTIALLY by the cone and there is no slot injectivity
-- anywhere in the tree (session-30's measured negative, re-confirmed by the
-- instalment-4 and -5 reviews), so a SECOND peel cannot be tied to the first:
-- the facts have to be emitted where the fired peer is decoded.
-- ((T5, review M-4) ERA-SCOPE "anywhere in the tree": the claim is about a
-- decomposition's SLOTS, whose recovery needs `_⦀_`/`_∥⇘⇙_` injectivity, and NOT about
-- tables — coarse `tableSpec` position injectivity is derivable and `LiveCSRow` §2/§3
-- proves it for both ChainSync tables.  The unqualified sentence is the phrasing the
-- T3/T4 reversal refuted; the conclusion it supports here is unaffected.)
--
-- *** THE FINDING OF THIS SLICE: OWNER GRANT #3 IS NOT NEEDED. ***  The reviewed
-- route asked for one in-place `Cf`/`Sf` abstraction of
-- `PipeBundleEvo.absBundleBF-ev-evo`.  It is already there:
-- `PipeBundleIoEvo.absBundleBF-ev-io-evo` is that abstraction, and it is
-- LABEL-GENERIC (`e₁ : BF.BFEv X`, no `ioES` anywhere in it — the "io" in the
-- name records its first consumer, not a restriction).  So this module
-- instantiates it at api labels and NO base module is touched at all;
-- `PipeBundleEvo` stays byte-identical and its fourteen importers are never
-- invalidated.
--
-- WHAT IS MIRRORED, and why it cannot be avoided.  `PipeNodeIoEvo`'s four-node
-- dispatch asserts every DRIVER is fixed (true of an io, false of an api), so
-- the api side has no reusable `top-nodes-*-evoP`.  This module therefore
-- re-mirrors the api tower — `PipeBundleEvo.absBundleG-api-evo`'s twenty-seven
-- channel clauses, `PipeNodeAEvo`'s node-A peel and `PipeEvDriverCone`'s node-B/C
-- peels and `driverExpose` — at the strengthened facts, REUSING every frozen
-- refutation, weak-run tower and driver classifier verbatim.  Node D holds no
-- leg BF server, so §5-§7 left its frozen peel alone; §8 (task 5) re-mirrors it
-- too, because node D DOES hold both legs' down-hop BF CLIENTS and the frozen
-- record reports no row about them — see §8's own header for why that needs no
-- base edit.
--
-- *** (T3b) THIS FILE IS THE §1-§7 HALF OF A SPLIT. ***  §8-§11 — node D's ⁺
-- re-mirror, the api-side leaf record `VisLeaves⁺`, the two landings, the
-- whole-nodes report `DriverExposed⁺`/`driverExpose⁺` and its three per-leg
-- selectors — now live in `LiveLegApiExpose`, which imports this module.  What
-- stays here is the PER-PEER, UP-HOP cone plus the row types every layer above
-- quotes (`SrvApiRowP`/`CliApiRowP`, `SrvReqRow`, `SrvSbLand`, `DnReqLand`,
-- `DnSbLand`, `DnSrvDrv`).  The dependency is one-directional: nothing here
-- mentions the assembly.  See `LiveLegApiExpose`'s header for where the cut is
-- and why it is there.
--
-- *** (T4) THE CHAINSYNC AXIS NOW TRAVELS BESIDE THE BLOCKFETCH ONE. ***  §4's
-- `BundleApiEvo` and §7's two relay-node peel results carry two APPENDED slots — the
-- CS CLIENT's and the CS SERVER's api-axis adjacency facts (`CScApiRowP`/`CSsApiRowP`,
-- `LiveCSRow` §4a) — and the dispatcher's two ChainSync clauses fill them from the
-- ROW-CARRYING bundle peel `absBundleCS-ev-prod⁺`.  Nothing was widened to get them:
-- the fired coarse row is recovered POST HOC from coarse-position injectivity of the
-- two CS tables (`LiveCSRow` §2/§3), which is why this file's new dependency is a
-- module strictly BELOW it and no frozen decode, no LTL module and no base module was
-- touched.  The standing obligation that comes with the route is a REVIEW one, named
-- as `LiveCSRow.SupportDistinct`: a future `NodeSpecs` row that gives two coarse
-- positions the same offer support breaks the recovery (and goes red there, not here).
--
-- The `Sf` interface is `Set`-valued while `BfsSucc`'s label pin lives in `Set₁`,
-- so the pin travels through the bundle peel as the `Set`-valued `SbbAt`
-- (`SbbData`, an Event-level decoder): `SbbAt` is obtained from the pin by ONE
-- `cong` and the pin is recovered from `SbbAt` by the single label enumeration
-- `sbbAt⇒pin`.
--
-- *** (T6d) THE CS AXIS NOW CARRIES ITS SECOND LANDING, AND `DnCsDrv` IS A PAIR. ***
-- The `pp2` arm of the driver-tail coupling is entered by the produce driver's
-- `pp1 → pp2` `sendCSAwaitReply` step, so it needs the same five layers T5's `pp1`
-- arm needed, one event later: §1c‴'s label pin, §2b‴'s landed form, a TRAILING slot
-- on §4's `BundleApiEvo` (filled vacuously at twenty-five sites and genuinely at the
-- two `apiCS` ones), a THIRTEENTH `cpStepKindQ-of⁺` component off `padv-into-pp2` /
-- `prod-a12-anchor`, and `DnCsAwLand` travelling in `DnCsDrv`'s landing arm — which
-- is therefore now the PAIR `DnCsReqLand × DnCsAwLand`, exactly as `DnSrvDrv`'s
-- landing arm has been the pair `DnReqLand × DnSbLand` since (T2).  One relay step is
-- one driver advance, so no second record field and no second peel is involved.
--
-- Base modules touched: NONE.  No postulate/hole/meta.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Unit.Polymorphic using ( ⊤; tt )
-- (T10) the NON-polymorphic unit, for the two `done`-crossing inversions: `done`'s
-- own carrier is `Data.Unit.⊤` (`PipeBundleEvo:184` states `SrvDoneRow` at it)
open import Data.Unit using () renaming ( ⊤ to ⊤₀ )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Maybe using ( Maybe; just; nothing )
open import Data.Maybe.Properties using ( just-injective )
open import Relation.Nullary using ( yes; no )
open import Class.DecEq using ( DecEq; _≟_ )
import Class.DecEq.Instances as DecEqI
open import Relation.Binary.PropositionalEquality
  using ( _≡_; _≢_; refl; sym; trans; cong; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegApiCone
  (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using
  ( p; apiES; linkAB; linkAC; linkBD; linkCD; produce )
open import CSP.Examples.Cardano_network.Base using
  ( Dir; lo; hi
  ; N2N_ChainSync; N2N_BlockFetch; N2N_KeepAlive
  ; N2N_TxSubmission; N2N_LeiosNotify; N2N_LeiosFetch )
open import CSP.Examples.Cardano_network.Net p using
  ( Net_Api; Net_Api-≟; Link
  ; apiCS; apiBF; apiKA; apiTS; apiLN; apiLF; done; input; output
  ; sndmsg; rcvmsg; tx; sndack; rcvack; ack; break
  ; ApiBFTag; ApiBFCar
  ; sendBFRequestRange; sendBFClientDone; sendBFStartBatch; sendBFNoBlocks
  ; sendBFBlock; sendBFBatchDone; recvBFBlock; reqBFRange
  -- (T5) the CS api tags §1c″'s label decoder and the `pp1` landing dispatch on
  ; ApiCSTag; ApiCSCar
  ; sendCSRequestNext; sendCSFindIntersect; sendCSDone; sendCSAwaitReply
  ; sendCSRollForward; sendCSRollBackward; sendCSIntersectFound
  ; sendCSIntersectNotFound; recvCSRollforward; recvCSRollback
  ; recvCSIntersectFound; recvCSIntersectNotFound
  ; reqCSRequestNext; reqCSFindIntersect )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( Block )
-- (T1) `ChainRange` is `ApiBFCar reqBFRange` (`Net.agda:99`), the carrier §1c's
-- label decoder and S1's own-key server row are stated at
open import CSP.Examples.Cardano_network.Data p using ( Payload; ChainRange )
open import CSP.Examples.Cardano_network.NetworkPar p using ( ιBF )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; EventSet; viewV )
open EventSet using ( mem )
open Op using () renaming ( ∅ES to ∅ESa )
open Op using ( _>>=_; Skip )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel; Event; sVis )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_; wev; τ*-refl; τ*-step )

import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload}) as PEA

import CSP.Examples.Cardano_network.ChainSync p as CS
import CSP.Examples.Cardano_network.BlockFetch p as BF
import CSP.Examples.Cardano_network.KeepAlive p as KA
import CSP.Examples.Cardano_network.TxSubmission p as TS
import CSP.Examples.Cardano_network.LeiosNotify p as LN
import CSP.Examples.Cardano_network.LeiosFetch p as LF

import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep
open SStep using ( NetProc; absBFc; absBFs; absBundleG
                 ; absNodeA; absNodeB; absNodeC; absNodeD; absNodesOf; nodesOf
                 ; coarsenBFc; coarsenBFs; coarsenCSc; coarsenCSs
                 ; decBFc-sil-step; decBFs-sil-step
                 ; reflect-node-api; apiSync; ⦀-ev-L; ⦀-ev-R )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using ( CScPos; CSsPos; BFcPos; BFsPos; InertPos
              ; kac; kas; tsc; tss; lnc; lns; lfc; lfs
              ; ProdPh; ConsPh; CPPh; consuming; producing; cph; cblk; cp3
              ; pp0; pp1; pp2; pp3; pp4; pp5; pp6; pp7; pp8; pp9
              ; ConsDPh; consD; decConsD
              ; bundleG; decBFc; decBFs; decProd; decCons; decCP
              ; decNodeA; NodeStateA; mkNodeA
              ; decNodeB; NodeStateB; mkNodeB; decNodeC; NodeStateC; mkNodeC; decNodeD
              ; cp0; cp1; cp2; cp4; cp5; cp6
              ; bcHead; bcSil; bcReq1; bcDone1; bcBlk1
              ; bsHead; bsSil; bsReq1; bsDone1; bsStart1; bsNoBlk1; bsBlk1; bsBatchDone1 )
-- (T2) the COARSE server table and its `sendBFStartBatch` row — §2b′'s landing
-- reads the successor position off `bfSnxt`, and `ceqBFs03` IS that row
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.NodeSpecs blkA as NS
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_PeerEvCSBF blkA
  -- (T10) … its `sendBFBatchDone` row beside it, which §2b′⁺'s landing reads, and
  -- the CLIENT's `recvBFBlock` row, which §2b′⁶'s does
  using ( ceqBFs03; ceqBFs06; ceqBFc10 )
-- (T10) the decidable-equality unsticker the `done`-row's own key comparison needs
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_TauCore blkA
  using ( ≟-yes-refl )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA using
  ( SysState; mkSys; med; nA; nB; nC; nD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA using
  ( ApiHasLink; apiLink-inj; ahlBF; ahlCS; decProd-ev-link; decCP-ev-link
  -- (T8c-iii) the CONSUME half's own link witness, for the classifier's nineteenth
  -- component (`decCP-ev-link`'s own up-link clause calls exactly this)
  ; decCons-ev-link
  -- (P8): the node-D consume driver's link, and the two label readers the
  -- `recvBFBlock` table inversion needs
  ; decConsD-ev-link; prefix-ev-lab; output-ev-lab
  -- (P5) grant #6: the CS/BF/`done` label class the api cone is ever called at —
  -- what conditions the inert freeze answer, and what refutes the four `apiXX`
  -- clauses of the bundle dispatcher
  ; IsApiCSBF )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( tableSpec-ev-inv; nothing-absurd; bind-ev-inv; step-fcong; output-ev-inv
        ; ret-no-ev )
open import CSP.Laws.Traces.PrefixInversion (Net_Api-≟ {Payload}) using ( ⟶₀-ev-inv )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysRoute blkA using
  ( absNodeA-fp; absNodeB-fp; absNodeC-fp; absNodeD-fp
  ; nodeB-no-when-A; nodeC-no-when-A; nodeD-no-when-A
  ; nodeC-no-when-B; nodeD-no-when-B; nodeD-no-when-C
  ; absNodeB-no-when-A; absNodeC-no-when-A; absNodeD-no-when-A
  ; absNodeC-no-when-B; absNodeD-no-when-B; absNodeD-no-when-C
  -- (P8): a `recvBFBlock` is a CONSUMER-role event, and the roles are disjoint
  ; ApiIsProd; ApiIsCons; aicBFrecv; prod≢cons )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink blkA using
  ( linkAB≢linkAC; linkAB≢linkBD; linkAC≢linkCD; linkBD≢linkCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_RouteLnLf blkA
  using ( noOffer→viewV )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink6 blkA as SIL6
open SIL6 using
  ( ⦀-wev-L; ⦀-wev-R; ∥⇘⇙-wev-sync; ev→wev; Tbfc; Tbfs; mkMbfs; bfs-fire-blk
  ; absBundleG-api-no; bundleG-api-no; drvA-AB-no; drvA-AC-no
  ; nodeA-no-when-B; nodeA-no-when-C; nodeA-no-when-D
  ; nodeB-no-when-C; nodeB-no-when-D; nodeC-no-when-D
  ; BundleCSEvR-abs; bcscEB; bcssEB
  ; BundleKAEvR-abs; bkacEB; bkasEB
  ; BundleTSEvR-abs; btscEB; btssEB
  ; BundleLNEvR-abs; blncEB; blnsEB
  ; BundleLFEvR-abs; blfcEB; blfsEB
  ; absBundleCS-ev-prod; absBundleKA-ev-prod; absBundleTS-ev-prod
  ; absBundleLN-ev-prod; absBundleLF-ev-prod )

open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkClassify blkA using
  ( prodAdv-of; consAdv-of )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkMeasure blkA using
  ( ProdAdv; a01; a12; a23; a34; a45; a56; a67; a78; a89
  ; ConsAdv; c01; c12; c23; c34; c45; c56 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA using
  ( TwoLegs; legBD; legCD; phOf; linkOf; InCp03; cblkOf )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeEvDriver blkA using
  ( RelayStepKind; rMove; rFwd; rRecv )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeEvRelay blkA using
  ( consAdv→rk; prodAdv→rk; pp0≢pp5; padv-pp5-fwd )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkDAnchor blkA using
  ( cons-c34-anchor )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA using
  ( prodOf; relayOf; cellUp; cellDn; upClient; dnClient
  ; RelayPre; RelayHas; RelayFwd; ConsRecv; ProdSent; ProdNotSent; BFcHasBlk
  ; prodSent-notSent-⊥ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA using
  ( upSrv; dnSrv; UpSrvEvo; DnSrvEvo )
-- (T1) the leg's DOWNSTREAM link, so S1's cone slot can be stated hop-generically
-- (`dnLink legBD = linkBD`, `dnLink legCD = linkCD`) instead of per-leg
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeFillSource blkA using
  ( dnLink )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeProdFire blkA using
  ( IsSBB; decCons-sbb-⊥; decProd-sbb-pp5
  -- (P7): the two extra link disequalities and the three non-A node refutations
  -- that make the producer LANDING vacuous off node A's own two up links
  ; linkAB≢linkCD; linkAC≢linkBD
  ; nodeB-link; nodeB-sbb-AB-⊥; nodeC-link; nodeC-sbb-AC-⊥; nodeD-link
  -- (P8): `evl` injectivity, for transporting the `recvBFBlock` decode along a
  -- fired-label equality
  ; evl-inj )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValInv blkA using
  ( RelayValOK )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValFill blkA using
  ( bundle-recv-cliPos; decProd-sbb-val )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValRelay blkA using
  ( cpStepKindL-of⁺; RelayAt; relayAt⇒eq )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleRecv blkA using
  ( bundle-recvBFBlock-forces-src )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleEvo blkA using
  ( BFsHasBlk; BfsSucc
  ; decBFc-apiBF-succ⁺; decBFs-apiBF-succ⁺; decBFs-doneBF-succ⁺; decBFc-doneBF-absurd
  -- (grant #8) the ROW-carrying inversions and the three row types
  ; decBFc-apiBF-succ-row⁺; decBFs-apiBF-succ-row⁺; decBFs-doneBF-succ-row⁺
  ; CliApiRow; SrvApiRow; SrvDoneRow )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeNodeAEvo blkA using
  ( srvEvo⇒up )
-- (P5) grant #6: the frozen KA client and the ONE KA inversion that reports its
-- freeze.  The api class needs it because `done l d N2N_KeepAlive` IS `IsApiCSBF`
-- (`SysOracle:1949` — `aicDone` at ANY channel) and its bundle clause moves `kac`.
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveKAFrozen blkA
  using ( KAcAtHead; kaW-done; kaFireF; kaFire )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeEvDriverCone blkA using
  ( srvEvo⇒fwd; upLinkOf; LegDriverStep; ldProd; ldRelay; ldCons; ldFix
  -- ASSEMBLY slice A1: the VALUE step data beside the driver step, so ONE peel
  -- of `driverExpose⁺` (`LiveLegApiExpose`) serves every premise of `LiveLegStep`'s
  -- visible arm
  ; LegValStep; lvStep )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleIoEvo blkA using
  ( BFcDecodeP; BFsDecodeP; BundleBFEvRio; bioCli; bioSrv; absBundleBF-ev-io-evo )
-- (T4) the ChainSync ROW layer: the CS axis' own api-adjacency facts and the
-- row-carrying bundle peel.  This is the CS twin of grant #8's BF rows, obtained
-- WITHOUT widening any decode — the row is recovered post hoc from COARSE-position
-- injectivity of the two CS tables (`LiveCSRow` §2/§3), which is why no frozen
-- module and no LTL module is touched for it.
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveCSRow blkA
  using ( CScApiRowP; CSsApiRowP; cscApiRow-fix; cssApiRow-fix
        ; cscApiRowP-api; cscApiRowP-done; cssApiRowP-api; cssApiRowP-done
        ; absBundleCS-ev-prod⁺; bcscEB⁺; bcssEB⁺
        -- (T5) the raw coarse rows, the client's fired-key pin and §4b's per-key
        -- LANDING — the three objects the `pp1` arm's cone half is built from
        ; CScRow; CSsRow; cscRow-key; cssReqLands
        -- (T6d) … and §4c's per-key landing at the `pp2` region's ENTRY, the one
        -- object §2b‴'s landed form is built from
        ; cssAwaitLands
        -- (T7) … and the CLIENT-side pair §2b⁗ is built from: the SERVER's key pin
        -- (the refuting clause, `cscRow-key`'s twin) and T5's own `recvCSRollforward`
        -- per-key LANDING, which already quantifies the `Header × Tip` value and so
        -- pays the `cp5` event's value gate in full (§1c⁗ (i))
        ; cssRow-key; cscRfwLands
        -- (T11b) … and §4c's fourth per-key landing, the `pp3` arm's own — the one
        -- object §2b⁶'s landed form is built from
        ; cssRfwLands )

------------------------------------------------------------------------
-- §1  THE `Set`-VALUED LABEL PIN.
--
-- `BFsDecodeP`'s server fact is `Sf : BFsPos → Set`, but `BfsSucc`'s block arm
-- pins the label by an equation between `Event`s, which is `Set₁`.  So the pin
-- travels as an equation between `Maybe (Link × Dir × Block)`s, read off the
-- Event by the total decoder `SbbData`.  Going IN costs one `cong`; coming OUT
-- costs the single label enumeration `sbbAt⇒pin` below, which is the only place
-- in this module where `Net_Api` is enumerated.
------------------------------------------------------------------------

-- the Event-level decoder of a `sendBFBlock` observation: its key and its block
SbbData : Event → Maybe (Link × Dir × Block)
SbbData (evLabel _ (apiBF l′ d′ sendBFBlock) x) = just (l′ , d′ , x)
SbbData _                                       = nothing

-- "the fired observation IS `apiBF l d sendBFBlock` carrying `b`", `Set`-valued
SbbAt : (l : Link) (d : Dir) (b : Block) {X : Set 0ℓ} → Net_Api Payload X → X → Set
SbbAt l d b {X} e a = SbbData (evLabel X e a) ≡ just (l , d , b)

-- IN: the `Set₁` label pin gives the `Set`-valued one by one `cong`
pin⇒sbbAt : (l : Link) (d : Dir) (b : Block) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
          → evLabel X e a ≡ evLabel Block (apiBF l d sendBFBlock) b
          → SbbAt l d b e a
pin⇒sbbAt l d b e a lbl = cong SbbData lbl

-- OUT: an observation whose `SbbData` is `just` at the key IS the `sendBFBlock`
-- observation — recover both `IsSBB` and the full pin.  THE ONLY enumeration of
-- `Net_Api` in this module (`apiBF`'s eight tags plus the fifteen other shapes).
sbbAt⇒pin : {l : Link} {d : Dir} {b : Block} {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
          → SbbAt l d b e a
          → IsSBB (evLabel X e a) × ApiHasLink l e
            × (evLabel X e a ≡ evLabel Block (apiBF l d sendBFBlock) b)
sbbAt⇒pin (apiBF l′ d′ sendBFBlock)        a refl = tt , ahlBF , refl
sbbAt⇒pin (apiBF l′ d′ sendBFRequestRange) a ()
sbbAt⇒pin (apiBF l′ d′ sendBFClientDone)   a ()
sbbAt⇒pin (apiBF l′ d′ sendBFStartBatch)   a ()
sbbAt⇒pin (apiBF l′ d′ sendBFNoBlocks)     a ()
sbbAt⇒pin (apiBF l′ d′ sendBFBatchDone)    a ()
sbbAt⇒pin (apiBF l′ d′ recvBFBlock)        a ()
sbbAt⇒pin (apiBF l′ d′ reqBFRange)         a ()
sbbAt⇒pin (apiCS  _ _ _) a ()
sbbAt⇒pin (apiKA  _ _ _) a ()
sbbAt⇒pin (apiTS  _ _ _) a ()
sbbAt⇒pin (apiLN  _ _ _) a ()
sbbAt⇒pin (apiLF  _ _ _) a ()
sbbAt⇒pin (done   _ _ _) a ()
sbbAt⇒pin (input  _ _ _) a ()
sbbAt⇒pin (output _ _ _) a ()
sbbAt⇒pin (sndmsg _ _ _) a ()
sbbAt⇒pin (rcvmsg _ _ _) a ()
sbbAt⇒pin (tx     _ _ _) a ()
sbbAt⇒pin (sndack _ _ _) a ()
sbbAt⇒pin (rcvack _ _ _) a ()
sbbAt⇒pin (ack    _ _ _) a ()
sbbAt⇒pin (break  _)     a ()

-- two `SbbAt`s at the same key name the SAME block (`just`/product injectivity)
sbbAt-inj : {l : Link} {d : Dir} {b b′ : Block} {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
          → SbbAt l d b e a → SbbAt l d b′ e a → b ≡ b′
sbbAt-inj {b = b} {b′} sd sd′
  with just-injective (trans (sym sd) sd′)
... | refl = refl

------------------------------------------------------------------------
-- §1b  THE `recvBFBlock` LABEL PIN, (P8).
--
-- The exact twin of §1 at the DELIVERY tag.  It is needed for the same reason:
-- `Set` is not injective, so a label equation between `evLabel`s with different
-- carriers cannot be matched on `refl`, and the pin has to travel as a `Set`-
-- valued equation between `Maybe (Link × Dir × Block)`s.  Going IN is one `cong`;
-- coming OUT is the single enumeration `rbbAt⇒pin`, which also reads off the
-- CONSUMER ROLE (`ApiIsCons`) and the LINK — the two facts that make the delivery
-- landing vacuous on the three non-D node arms of the cone.
------------------------------------------------------------------------

-- the Event-level decoder of a `recvBFBlock` observation: its key and its block
RbbData : Event → Maybe (Link × Dir × Block)
RbbData (evLabel _ (apiBF l′ d′ recvBFBlock) x) = just (l′ , d′ , x)
RbbData _                                       = nothing

-- "the fired observation IS `apiBF l d recvBFBlock` carrying `b`", `Set`-valued
RbbAt : (l : Link) (d : Dir) (b : Block) {X : Set 0ℓ} → Net_Api Payload X → X → Set
RbbAt l d b {X} e a = RbbData (evLabel X e a) ≡ just (l , d , b)

-- IN: the `Set₁` label pin gives the `Set`-valued one by one `cong`
rpin⇒rbbAt : (l : Link) (d : Dir) (b : Block) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
           → evLabel X e a ≡ evLabel Block (apiBF l d recvBFBlock) b
           → RbbAt l d b e a
rpin⇒rbbAt l d b e a lbl = cong RbbData lbl

-- OUT: an observation whose `RbbData` is `just` at the key IS the `recvBFBlock`
-- observation — recover the CONSUMER role, the link, and the full pin
rbbAt⇒pin : {l : Link} {d : Dir} {b : Block} {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
          → RbbAt l d b e a
          → ApiIsCons e × ApiHasLink l e
            × (evLabel X e a ≡ evLabel Block (apiBF l d recvBFBlock) b)
rbbAt⇒pin (apiBF l′ d′ recvBFBlock)        a refl = aicBFrecv , ahlBF , refl
rbbAt⇒pin (apiBF l′ d′ sendBFRequestRange) a ()
rbbAt⇒pin (apiBF l′ d′ sendBFClientDone)   a ()
rbbAt⇒pin (apiBF l′ d′ sendBFStartBatch)   a ()
rbbAt⇒pin (apiBF l′ d′ sendBFNoBlocks)     a ()
rbbAt⇒pin (apiBF l′ d′ sendBFBlock)        a ()
rbbAt⇒pin (apiBF l′ d′ sendBFBatchDone)    a ()
rbbAt⇒pin (apiBF l′ d′ reqBFRange)         a ()
rbbAt⇒pin (apiCS  _ _ _) a ()
rbbAt⇒pin (apiKA  _ _ _) a ()
rbbAt⇒pin (apiTS  _ _ _) a ()
rbbAt⇒pin (apiLN  _ _ _) a ()
rbbAt⇒pin (apiLF  _ _ _) a ()
rbbAt⇒pin (done   _ _ _) a ()
rbbAt⇒pin (input  _ _ _) a ()
rbbAt⇒pin (output _ _ _) a ()
rbbAt⇒pin (sndmsg _ _ _) a ()
rbbAt⇒pin (rcvmsg _ _ _) a ()
rbbAt⇒pin (tx     _ _ _) a ()
rbbAt⇒pin (sndack _ _ _) a ()
rbbAt⇒pin (rcvack _ _ _) a ()
rbbAt⇒pin (ack    _ _ _) a ()
rbbAt⇒pin (break  _)     a ()

-- two `RbbAt`s at the same key name the SAME block (`just`/product injectivity)
rbbAt-inj : {l : Link} {d : Dir} {b b′ : Block} {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
          → RbbAt l d b e a → RbbAt l d b′ e a → b ≡ b′
rbbAt-inj {b = b} {b′} rd rd′
  with just-injective (trans (sym rd) rd′)
... | refl = refl

-- transport the `recvBFBlock` decode along a fired-label equality
rbbAt-along : {R : Set} {x y : Event} {l : Link} {d : Dir} {b : Block}
            → (evl {R = R} x) ≡ evl y
            → RbbData x ≡ just (l , d , b) → RbbData y ≡ just (l , d , b)
rbbAt-along {l = l} {d} {b} eq h =
  subst (λ z → RbbData z ≡ just (l , d , b)) (evl-inj eq) h

-- a consume driver fires `recvBFBlock` ONLY from the delivering phase `cp3`: at
-- every other phase the driver's head is a DIFFERENT channel, off which the
-- `RbbData` decode is `nothing`.  This is the REVERSE of `WalkDAnchor`'s gated
-- anchor, and the reason (P8) needed the driver step out of `NodeDDrv`.
decCons-rbb-cp3 : (l : Link) (d : Dir) (b : Block₃) (cp : ConsPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {l₀ : Link} {d₀ : Dir} {b₀ : Block}
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃}
  → decCons l d b cp ─[ ev (evl (evLabel X e a)) ]─► M
  → RbbAt l₀ d₀ b₀ e a → cp ≡ cp3
decCons-rbb-cp3 l d b cp0 step h
  with rbbAt-along (proj₁ (proj₂ (⟶₀-ev-inv step))) h
... | ()
decCons-rbb-cp3 l d b cp1 step h with rbbAt-along (proj₂ (prefix-ev-lab step)) h
... | ()
decCons-rbb-cp3 l d b cp2 step h with rbbAt-along (output-ev-lab step) h
... | ()
decCons-rbb-cp3 l d b cp3 step h = refl
decCons-rbb-cp3 l d b cp4 step h with rbbAt-along (output-ev-lab step) h
... | ()
decCons-rbb-cp3 l d b cp5 step h
  with rbbAt-along (proj₁ (proj₂ (⟶₀-ev-inv step))) h
... | ()
decCons-rbb-cp3 l d b cp6 step h =
  ⊥-elim (ret-no-ev {P = decCons l d b cp6} refl step)

-- … the same through node D's `>> Skip` wrapper
decConsD-rbb-cp3 : (l : Link) (cd : ConsDPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {l₀ : Link} {d₀ : Dir} {b₀ : Block} {M : NetProc}
  → decConsD l cd ─[ ev (evl (evLabel X e a)) ]─► M
  → RbbAt l₀ d₀ b₀ e a → cph cd ≡ cp3
-- (the phase has to be a CONSTRUCTOR for the `>>=` force-shape argument of
-- `bind-ev-inv` to be `refl`, exactly as in `SysOracle.decConsD-ev-link`)
decConsD-rbb-cp3 l (consD b cp0) step h
  with bind-ev-inv (λ _ → Skip) (decCons l hi b cp0) refl step
... | _ , sc , refl = decCons-rbb-cp3 l hi b cp0 sc h
decConsD-rbb-cp3 l (consD b cp1) step h
  with bind-ev-inv (λ _ → Skip) (decCons l hi b cp1) refl step
... | _ , sc , refl = decCons-rbb-cp3 l hi b cp1 sc h
decConsD-rbb-cp3 l (consD b cp2) step h
  with bind-ev-inv (λ _ → Skip) (decCons l hi b cp2) refl step
... | _ , sc , refl = decCons-rbb-cp3 l hi b cp2 sc h
decConsD-rbb-cp3 l (consD b cp3) step h
  with bind-ev-inv (λ _ → Skip) (decCons l hi b cp3) refl step
... | _ , sc , refl = decCons-rbb-cp3 l hi b cp3 sc h
decConsD-rbb-cp3 l (consD b cp4) step h
  with bind-ev-inv (λ _ → Skip) (decCons l hi b cp4) refl step
... | _ , sc , refl = decCons-rbb-cp3 l hi b cp4 sc h
decConsD-rbb-cp3 l (consD b cp5) step h
  with bind-ev-inv (λ _ → Skip) (decCons l hi b cp5) refl step
... | _ , sc , refl = decCons-rbb-cp3 l hi b cp5 sc h
decConsD-rbb-cp3 l (consD b cp6) step h =
  ⊥-elim (ret-no-ev {P = decConsD l (consD b cp6)} refl step)

------------------------------------------------------------------------
-- §1c  THE `reqBFRange` LABEL PIN, (T1) — S1's own.
--
-- The exact twin of §1b at the PRODUCE driver's request tag, and it exists for the
-- same reason: `Set` is not injective, so a label equation between `evLabel`s with
-- different carriers cannot be matched on `refl`, and the pin has to travel as a
-- `Set`-valued equation between `Maybe (Link × Dir × ChainRange)`s.  Going IN is
-- one `cong`; coming OUT is the single enumeration `rbrAt⇒pin`, which reads off the
-- LINK — the fact that makes S1's landing vacuous on every arm of the cone that
-- fired somewhere else.
--
-- *** WHY TAG-SPECIFIC AND NOT TAG-GENERIC. ***  `ApiBFCar reqBFRange` IS
-- `ChainRange` (`Net.agda:99`), so this decoder is NON-dependent, exactly like
-- `SbbData`/`RbbData`.  A decoder generic in the `ApiBFTag` would have to carry
-- `Σ[ m ∈ ApiBFTag ] (Link × Dir × ApiBFCar m)` and be inverted through a
-- dependent-pair injectivity; nothing funded needs it.  T2's `sendBFStartBatch`
-- twin is this block with the tag and the carrier changed (carrier `⊤`), and T8's
-- `sendBFClientDone` twin likewise.
--
-- *** (T7 fix round) THE COMPRESSION QUESTION, SETTLED — AND ON DIFFERENT GROUNDS THAN
-- "NOTHING FUNDED NEEDS IT", WHICH IS THE WEAK REASON AND IS NOW FOUR INSTANCES OLD. ***
-- There are five §1c-shaped blocks (§1c here, §1c′ T2, §1c″ T5, §1c‴ T6d, §1c⁗ T7) plus
-- §1d; FOUR carry an `⇒ahl` map (this block's out-map is `rbrAt⇒pin`, a different shape
-- carrying a `ChainRange`), and those four measure 30 clauses of which 28 are `()`
-- (`sbAt⇒ahl` 24/22).  The genuinely near-identical set is the THREE apiCS-axis blocks,
-- `csrAt`/`csaAt`/`csfAt`.
--
--   · *** THE PRICE IS LOWER THAN THIS NOTE IMPLIED. ***  The dependent-pair injectivity
--     it invokes is NOT needed on the CS axis: §1c⁗'s finding (i) is that the decoder
--     reports the KEY ONLY and the value never travels, so the shared key type is the
--     NON-dependent `ApiCSTag × Link × Dir` and plain `just-injective` suffices — no UIP.
--     (`DecEq-ApiCSTag` exists at `Net.agda:295` if it ever were.)  A shared
--     `CsKey`/`CsAt`/`csAt⇒ahl` block is ~23 lines with ONE `apiCS _ _ _` clause and 15
--     non-`apiCS` absurd ones, plus ~3 per tag, against 3 × ~37 ≈ 111 today: a **≈79-line
--     saving**, and every pin name is FILE-LOCAL (no consumer outside this module), so the
--     migration touches ~19 in-file sites and no other interface.
--   · *** AND IT IS STILL DECLINED, BECAUSE THE FORWARD SAVING IS EXACTLY ZERO. ***  No
--     SIXTH apiCS block can arrive.  Re-derived here rather than relayed: the only row
--     into `csAreq` — the equation `cp6` and `pp0` both state, i.e. the WHOLE remaining CS
--     residual — is `csSnxt l d csIdle (_ , output l′ d′ N2N_ChainSync) (… chainSync
--     MsgCSRequestNext) ≡ just csAreq` (`NodeSpecs:415-418`), an `output` WIRE READ keyed
--     on a message constructor and not an `apiCS` label at all.  So `cp6`/`pp0`'s landing
--     pin is io-shaped, not §1c-shaped; and `cp4`/`pp3` are on the BlockFetch axis.  ***
--     The apiCS pin family is CLOSED AT THREE, permanently. ***
--
-- So the compression is retrospective tidying only: ≈79 lines against 2-4 api-cone build
-- rounds (17 modules, ~360s each, re-measured at T7) and the loss of one narrow tripwire
-- (a new `ApiCSTag` constructor would stop breaking the three maps; it would still break
-- `csCnxt`'s tables, and these decoders already carry a `_` catch-all).  *** Build it only
-- if this file is being opened for another reason anyway, and do not re-litigate it on the
-- "nothing funded needs it" grounds — the real reason is that the family cannot grow. ***
------------------------------------------------------------------------

-- the Event-level decoder of a `reqBFRange` observation: its key and its range
RbrData : Event → Maybe (Link × Dir × ChainRange)
RbrData (evLabel _ (apiBF l′ d′ reqBFRange) x) = just (l′ , d′ , x)
RbrData _                                      = nothing

-- "the fired observation IS `apiBF l d reqBFRange` carrying `r`", `Set`-valued
RbrAt : (l : Link) (d : Dir) (r : ChainRange) {X : Set 0ℓ} → Net_Api Payload X → X → Set
RbrAt l d r {X} e a = RbrData (evLabel X e a) ≡ just (l , d , r)

-- IN: the `Set₁` label pin gives the `Set`-valued one by one `cong`
pin⇒rbrAt : (l : Link) (d : Dir) (r : ChainRange) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
          → evLabel X e a ≡ evLabel ChainRange (apiBF l d reqBFRange) r
          → RbrAt l d r e a
pin⇒rbrAt l d r e a lbl = cong RbrData lbl

-- OUT: an observation whose `RbrData` is `just` at the key IS the `reqBFRange`
-- observation — recover the LINK and the full pin
rbrAt⇒pin : {l : Link} {d : Dir} {r : ChainRange} {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
          → RbrAt l d r e a
          → ApiHasLink l e × (evLabel X e a ≡ evLabel ChainRange (apiBF l d reqBFRange) r)
rbrAt⇒pin (apiBF l′ d′ reqBFRange)         a refl = ahlBF , refl
rbrAt⇒pin (apiBF l′ d′ sendBFRequestRange) a ()
rbrAt⇒pin (apiBF l′ d′ sendBFClientDone)   a ()
rbrAt⇒pin (apiBF l′ d′ sendBFStartBatch)   a ()
rbrAt⇒pin (apiBF l′ d′ sendBFNoBlocks)     a ()
rbrAt⇒pin (apiBF l′ d′ sendBFBlock)        a ()
rbrAt⇒pin (apiBF l′ d′ sendBFBatchDone)    a ()
rbrAt⇒pin (apiBF l′ d′ recvBFBlock)        a ()
rbrAt⇒pin (apiCS  _ _ _) a ()
rbrAt⇒pin (apiKA  _ _ _) a ()
rbrAt⇒pin (apiTS  _ _ _) a ()
rbrAt⇒pin (apiLN  _ _ _) a ()
rbrAt⇒pin (apiLF  _ _ _) a ()
rbrAt⇒pin (done   _ _ _) a ()
rbrAt⇒pin (input  _ _ _) a ()
rbrAt⇒pin (output _ _ _) a ()
rbrAt⇒pin (sndmsg _ _ _) a ()
rbrAt⇒pin (rcvmsg _ _ _) a ()
rbrAt⇒pin (tx     _ _ _) a ()
rbrAt⇒pin (sndack _ _ _) a ()
rbrAt⇒pin (rcvack _ _ _) a ()
rbrAt⇒pin (ack    _ _ _) a ()
rbrAt⇒pin (break  _)     a ()

------------------------------------------------------------------------
-- §1c′  THE `sendBFStartBatch` LABEL PIN, (T2) — the `pp5` arm's own.
--
-- §1c's twin at the produce driver's OTHER server-facing tag, and it is the twin
-- §1c's own note predicted ("T2's `sendBFStartBatch` twin is this block with the tag
-- and the carrier changed").  The carrier IS changed: `ApiBFCar sendBFStartBatch` is
-- `⊤` (`Net.agda:95`), so the decoder carries the KEY only and there is no value to
-- recover — which makes the `Set`-valued pin a `Maybe (Link × Dir)` equation.
--
-- Only the `ApiHasLink` direction of the OUT map is built: the `pp5` landing's
-- consumers need the fired LINK (to refute the co-leg arms of the cone), never the
-- `Set₁` label equation back.
------------------------------------------------------------------------

-- the Event-level decoder of a `sendBFStartBatch` observation: its key
SbData : Event → Maybe (Link × Dir)
SbData (evLabel _ (apiBF l₀ d₀ sendBFStartBatch) x) = just (l₀ , d₀)
SbData _                                            = nothing

-- "the fired observation IS `apiBF l d sendBFStartBatch`", `Set`-valued
SbAt : (l : Link) (d : Dir) {X : Set 0ℓ} → Net_Api Payload X → X → Set
SbAt l d {X} e a = SbData (evLabel X e a) ≡ just (l , d)

-- IN: the `Set₁` label pin gives the `Set`-valued one by one `cong`
pin⇒sbAt : (l : Link) (d : Dir) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
           (u : ApiBFCar sendBFStartBatch)
         → evLabel X e a ≡ evLabel (ApiBFCar sendBFStartBatch) (apiBF l d sendBFStartBatch) u
         → SbAt l d e a
pin⇒sbAt l d e a u lbl = cong SbData lbl

-- OUT: an observation whose `SbData` is `just` at the key was fired at that LINK
sbAt⇒ahl : {l : Link} {d : Dir} {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
         → SbAt l d e a → ApiHasLink l e
sbAt⇒ahl (apiBF l₀ d₀ sendBFStartBatch)   a refl = ahlBF
sbAt⇒ahl (apiBF l₀ d₀ sendBFRequestRange) a ()
sbAt⇒ahl (apiBF l₀ d₀ sendBFClientDone)   a ()
sbAt⇒ahl (apiBF l₀ d₀ sendBFNoBlocks)     a ()
sbAt⇒ahl (apiBF l₀ d₀ sendBFBlock)        a ()
sbAt⇒ahl (apiBF l₀ d₀ sendBFBatchDone)    a ()
sbAt⇒ahl (apiBF l₀ d₀ recvBFBlock)        a ()
sbAt⇒ahl (apiBF l₀ d₀ reqBFRange)         a ()
sbAt⇒ahl (apiCS  _ _ _) a ()
sbAt⇒ahl (apiKA  _ _ _) a ()
sbAt⇒ahl (apiTS  _ _ _) a ()
sbAt⇒ahl (apiLN  _ _ _) a ()
sbAt⇒ahl (apiLF  _ _ _) a ()
sbAt⇒ahl (done   _ _ _) a ()
sbAt⇒ahl (input  _ _ _) a ()
sbAt⇒ahl (output _ _ _) a ()
sbAt⇒ahl (sndmsg _ _ _) a ()
sbAt⇒ahl (rcvmsg _ _ _) a ()
sbAt⇒ahl (tx     _ _ _) a ()
sbAt⇒ahl (sndack _ _ _) a ()
sbAt⇒ahl (rcvack _ _ _) a ()
sbAt⇒ahl (ack    _ _ _) a ()
sbAt⇒ahl (break  _)     a ()

------------------------------------------------------------------------
-- §1c⁵  (T10) THE `sendBFBatchDone` LABEL PIN — the `pp6` landing's own.
--
-- *** KEEP IN SYNC WITH §1c′'s `SbData`/`SbAt`/`pin⇒sbAt` BLOCK ABOVE, PART BY
-- PART. ***  This is that block with the TAG changed and nothing else: the carrier
-- `ApiBFCar sendBFBatchDone` is `⊤` exactly as `sendBFStartBatch`'s is, so the
-- decoder reports the KEY only and the `Set`-valued pin is a `Maybe (Link × Dir)`
-- equation.  The fourth instance of the same three-part shape.
--
-- *** ONE DECLARED DEVIATION: the OUT map (`sbAt⇒ahl`'s twin) IS NOT BUILT. ***
-- Its twenty-two-clause enumeration exists to give the co-leg arms of the cone a
-- fired LINK; the `pp6` landing's only consumer is node A's OWN firing leg (the
-- co-leg's producer AND its up server are both fixed there, so `visLeaves-fix`
-- answers it), so nothing would read the map.  Build it at the first consumer that
-- needs the link, not before.
------------------------------------------------------------------------

-- the Event-level decoder of a `sendBFBatchDone` observation: its key
BdData : Event → Maybe (Link × Dir)
BdData (evLabel _ (apiBF l₀ d₀ sendBFBatchDone) x) = just (l₀ , d₀)
BdData _                                           = nothing

-- "the fired observation IS `apiBF l d sendBFBatchDone`", `Set`-valued
BdAt : (l : Link) (d : Dir) {X : Set 0ℓ} → Net_Api Payload X → X → Set
BdAt l d {X} e a = BdData (evLabel X e a) ≡ just (l , d)

-- IN: the `Set₁` label pin gives the `Set`-valued one by one `cong`
pin⇒bdAt : (l : Link) (d : Dir) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
           (u : ApiBFCar sendBFBatchDone)
         → evLabel X e a ≡ evLabel (ApiBFCar sendBFBatchDone) (apiBF l d sendBFBatchDone) u
         → BdAt l d e a
pin⇒bdAt l d e a u lbl = cong BdData lbl


------------------------------------------------------------------------
-- §1c″  THE `reqCSRequestNext` LABEL PIN, (T5) — the `pp1` arm's own.
--
-- §1c′'s twin at the produce driver's FIRST event, and the third instance of the
-- same three-part block (decoder, `Set`-valued pin, the two maps).  The carrier is
-- `ApiCSCar reqCSRequestNext`, which carries nothing the landing needs, so the
-- decoder reports the KEY only — a `Maybe (Link × Dir)` equation, exactly like
-- `SbData`'s.
--
-- The OUT map is `ApiHasLink`-only, for `SbAt`'s reason: the `pp1` landing's
-- consumers need the fired LINK, to refute the landing on the arm of the cone where
-- the relay fired on its UP link.  Note the tag dispatch it needs INSIDE the `apiCS`
-- shape: the decoder matches the tag as a CONSTRUCTOR, so the thirteen sibling tags
-- are thirteen absurd clauses — the same shape §2b′'s producers have.
------------------------------------------------------------------------

-- the Event-level decoder of a `reqCSRequestNext` observation: its key
CsrData : Event → Maybe (Link × Dir)
CsrData (evLabel _ (apiCS l₀ d₀ reqCSRequestNext) x) = just (l₀ , d₀)
CsrData _                                            = nothing

-- "the fired observation IS `apiCS l d reqCSRequestNext`", `Set`-valued
CsrAt : (l : Link) (d : Dir) {X : Set 0ℓ} → Net_Api Payload X → X → Set
CsrAt l d {X} e a = CsrData (evLabel X e a) ≡ just (l , d)

-- IN: the `Set₁` label pin gives the `Set`-valued one by one `cong`
pin⇒csrAt : (l : Link) (d : Dir) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
            (u : ApiCSCar reqCSRequestNext)
          → evLabel X e a ≡ evLabel (ApiCSCar reqCSRequestNext) (apiCS l d reqCSRequestNext) u
          → CsrAt l d e a
pin⇒csrAt l d e a u lbl = cong CsrData lbl

-- *** (T11h) THE THREE OUT MAPS' SHARPENED TARGET, AND WHY IT IS ONE TYPE AND NOT
-- THREE THIRTY-CLAUSE MAPS. ***  `ApiHasLink l e` is what the three `⇒ahl` maps below
-- returned, and `ahlBF` inhabits it too — so a consumer holding one cannot say the
-- fired FAMILY is ChainSync, which is exactly what the BF row facts' catch-all
-- degeneration needs (`SrvApiRowP`/`CliApiRowP` are label-DIRECTED, so at an `apiCS`
-- label they ARE the fixity equation).  Sharpening the three maps' TARGET costs one
-- token per map; adding a second thirty-clause enumeration per pin would have cost
-- ≈96 lines for the same fact.  `ApiHasLink` is recovered by one clause below, so no
-- existing consumer of the three maps changes shape.
data ApiCSAt (l : Link) : {X : Set 0ℓ} → Net_Api Payload X → Set₁ where
  acsCS : ∀ {d m} → ApiCSAt l (apiCS l d m)

-- the LINK, which is all the three maps' original consumers wanted
acsAt⇒ahl : {l : Link} {X : Set 0ℓ} {e : Net_Api Payload X} → ApiCSAt l e → ApiHasLink l e
acsAt⇒ahl acsCS = ahlCS

-- OUT: an observation whose `CsrData` is `just` at the key was fired at that LINK, and
-- in the ChainSync FAMILY
csrAt⇒acs : {l : Link} {d : Dir} {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
          → CsrAt l d e a → ApiCSAt l e
csrAt⇒acs (apiCS l₀ d₀ reqCSRequestNext) a refl = acsCS
csrAt⇒acs (apiCS l₀ d₀ sendCSRequestNext) a ()
csrAt⇒acs (apiCS l₀ d₀ sendCSFindIntersect) a ()
csrAt⇒acs (apiCS l₀ d₀ sendCSDone) a ()
csrAt⇒acs (apiCS l₀ d₀ sendCSAwaitReply) a ()
csrAt⇒acs (apiCS l₀ d₀ sendCSRollForward) a ()
csrAt⇒acs (apiCS l₀ d₀ sendCSRollBackward) a ()
csrAt⇒acs (apiCS l₀ d₀ sendCSIntersectFound) a ()
csrAt⇒acs (apiCS l₀ d₀ sendCSIntersectNotFound) a ()
csrAt⇒acs (apiCS l₀ d₀ recvCSRollforward) a ()
csrAt⇒acs (apiCS l₀ d₀ recvCSRollback) a ()
csrAt⇒acs (apiCS l₀ d₀ recvCSIntersectFound) a ()
csrAt⇒acs (apiCS l₀ d₀ recvCSIntersectNotFound) a ()
csrAt⇒acs (apiCS l₀ d₀ reqCSFindIntersect) a ()
csrAt⇒acs (apiBF  _ _ _) a ()
csrAt⇒acs (apiKA  _ _ _) a ()
csrAt⇒acs (apiTS  _ _ _) a ()
csrAt⇒acs (apiLN  _ _ _) a ()
csrAt⇒acs (apiLF  _ _ _) a ()
csrAt⇒acs (done   _ _ _) a ()
csrAt⇒acs (input  _ _ _) a ()
csrAt⇒acs (output _ _ _) a ()
csrAt⇒acs (sndmsg _ _ _) a ()
csrAt⇒acs (rcvmsg _ _ _) a ()
csrAt⇒acs (tx     _ _ _) a ()
csrAt⇒acs (sndack _ _ _) a ()
csrAt⇒acs (rcvack _ _ _) a ()
csrAt⇒acs (ack    _ _ _) a ()
csrAt⇒acs (break  _)     a ()

------------------------------------------------------------------------
-- §1c‴  THE `sendCSAwaitReply` LABEL PIN, (T6d) — the `pp2` arm's own.
--
-- §1c″'s twin at the produce driver's SECOND event, and the fourth instance of the
-- same block.  `ApiCSCar sendCSAwaitReply` is `⊤` (`Net.agda:118`), exactly like
-- `reqCSRequestNext`'s, so the decoder reports the KEY only and the `Set`-valued pin
-- is a `Maybe (Link × Dir)` equation.
--
-- The OUT map is `ApiHasLink`-only, for §1c″'s reason: the `pp2` landing's consumers
-- need the fired LINK, to refute the landing on the arm of the cone where the relay
-- fired on its UP link.  The `pin⇒` map of §1c′/§1c″ is DELIBERATELY not mirrored: it
-- has no consumer at either sibling and none here — the `pp1`/`pp2` anchors produce
-- the `Set`-valued pin directly (`prod-a01-anchor`, `prod-a12-anchor`) — so a fourth
-- copy would be dead code.
------------------------------------------------------------------------

-- the Event-level decoder of a `sendCSAwaitReply` observation: its key
CsaData : Event → Maybe (Link × Dir)
CsaData (evLabel _ (apiCS l₀ d₀ sendCSAwaitReply) x) = just (l₀ , d₀)
CsaData _                                            = nothing

-- "the fired observation IS `apiCS l d sendCSAwaitReply`", `Set`-valued
CsaAt : (l : Link) (d : Dir) {X : Set 0ℓ} → Net_Api Payload X → X → Set
CsaAt l d {X} e a = CsaData (evLabel X e a) ≡ just (l , d)

-- OUT: an observation whose `CsaData` is `just` at the key was fired at that LINK, and
-- in the ChainSync FAMILY (T11h's sharpened target — see §1c″)
csaAt⇒acs : {l : Link} {d : Dir} {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
          → CsaAt l d e a → ApiCSAt l e
csaAt⇒acs (apiCS l₀ d₀ sendCSAwaitReply) a refl = acsCS
csaAt⇒acs (apiCS l₀ d₀ sendCSRequestNext) a ()
csaAt⇒acs (apiCS l₀ d₀ sendCSFindIntersect) a ()
csaAt⇒acs (apiCS l₀ d₀ sendCSDone) a ()
csaAt⇒acs (apiCS l₀ d₀ sendCSRollForward) a ()
csaAt⇒acs (apiCS l₀ d₀ sendCSRollBackward) a ()
csaAt⇒acs (apiCS l₀ d₀ sendCSIntersectFound) a ()
csaAt⇒acs (apiCS l₀ d₀ sendCSIntersectNotFound) a ()
csaAt⇒acs (apiCS l₀ d₀ recvCSRollforward) a ()
csaAt⇒acs (apiCS l₀ d₀ recvCSRollback) a ()
csaAt⇒acs (apiCS l₀ d₀ recvCSIntersectFound) a ()
csaAt⇒acs (apiCS l₀ d₀ recvCSIntersectNotFound) a ()
csaAt⇒acs (apiCS l₀ d₀ reqCSRequestNext) a ()
csaAt⇒acs (apiCS l₀ d₀ reqCSFindIntersect) a ()
csaAt⇒acs (apiBF  _ _ _) a ()
csaAt⇒acs (apiKA  _ _ _) a ()
csaAt⇒acs (apiTS  _ _ _) a ()
csaAt⇒acs (apiLN  _ _ _) a ()
csaAt⇒acs (apiLF  _ _ _) a ()
csaAt⇒acs (done   _ _ _) a ()
csaAt⇒acs (input  _ _ _) a ()
csaAt⇒acs (output _ _ _) a ()
csaAt⇒acs (sndmsg _ _ _) a ()
csaAt⇒acs (rcvmsg _ _ _) a ()
csaAt⇒acs (tx     _ _ _) a ()
csaAt⇒acs (sndack _ _ _) a ()
csaAt⇒acs (rcvack _ _ _) a ()
csaAt⇒acs (ack    _ _ _) a ()
csaAt⇒acs (break  _)     a ()

------------------------------------------------------------------------
-- §1c⁶  (T11b) THE `sendCSRollForward` LABEL PIN — the `pp3` arm's own, and the
-- LAST of the produce-side family.
--
-- *** KEEP IN SYNC WITH §1c‴'s `CsaData`/`CsaAt`/`csaAt⇒acs` BLOCK ABOVE, PART BY
-- PART. ***  That block with the TAG changed and nothing else.  `ApiCSCar
-- sendCSRollForward` is `Header × Tip` (`Net.agda:119`) and NOT `⊤` — but the
-- decoder reports the KEY only for §1c⁗(i)'s reason: the value never has to travel,
-- because T11b's per-key pin `LiveCSRow.cssRfwLands` is universally quantified over
-- it and names it in its own CONCLUSION (`q′ ≡ csWrf v`).
--
-- The OUT map is `ApiHasLink`-only, for §1c″/§1c‴'s reason: the `pp3` landing's
-- consumers need the fired LINK, to refute the landing on the arm of the cone where
-- the relay fired on its UP link.  The `pin⇒` map is NOT mirrored, for §1c‴'s reason
-- — `prod-a23-anchor` produces the `Set`-valued pin directly.
------------------------------------------------------------------------

-- the Event-level decoder of a `sendCSRollForward` observation: its key
CsfwData : Event → Maybe (Link × Dir)
CsfwData (evLabel _ (apiCS l₀ d₀ sendCSRollForward) x) = just (l₀ , d₀)
CsfwData _                                             = nothing

-- "the fired observation IS `apiCS l d sendCSRollForward`", `Set`-valued
CsfwAt : (l : Link) (d : Dir) {X : Set 0ℓ} → Net_Api Payload X → X → Set
CsfwAt l d {X} e a = CsfwData (evLabel X e a) ≡ just (l , d)

-- OUT: an observation whose `CsfwData` is `just` at the key was fired at that LINK, and
-- in the ChainSync FAMILY (T11h's sharpened target — see §1c″)
csfwAt⇒acs : {l : Link} {d : Dir} {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
           → CsfwAt l d e a → ApiCSAt l e
csfwAt⇒acs (apiCS l₀ d₀ sendCSRollForward) a refl = acsCS
csfwAt⇒acs (apiCS l₀ d₀ sendCSRequestNext) a ()
csfwAt⇒acs (apiCS l₀ d₀ sendCSFindIntersect) a ()
csfwAt⇒acs (apiCS l₀ d₀ sendCSDone) a ()
csfwAt⇒acs (apiCS l₀ d₀ sendCSAwaitReply) a ()
csfwAt⇒acs (apiCS l₀ d₀ sendCSRollBackward) a ()
csfwAt⇒acs (apiCS l₀ d₀ sendCSIntersectFound) a ()
csfwAt⇒acs (apiCS l₀ d₀ sendCSIntersectNotFound) a ()
csfwAt⇒acs (apiCS l₀ d₀ recvCSRollforward) a ()
csfwAt⇒acs (apiCS l₀ d₀ recvCSRollback) a ()
csfwAt⇒acs (apiCS l₀ d₀ recvCSIntersectFound) a ()
csfwAt⇒acs (apiCS l₀ d₀ recvCSIntersectNotFound) a ()
csfwAt⇒acs (apiCS l₀ d₀ reqCSRequestNext) a ()
csfwAt⇒acs (apiCS l₀ d₀ reqCSFindIntersect) a ()
csfwAt⇒acs (apiBF  _ _ _) a ()
csfwAt⇒acs (apiKA  _ _ _) a ()
csfwAt⇒acs (apiTS  _ _ _) a ()
csfwAt⇒acs (apiLN  _ _ _) a ()
csfwAt⇒acs (apiLF  _ _ _) a ()
csfwAt⇒acs (done   _ _ _) a ()
csfwAt⇒acs (input  _ _ _) a ()
csfwAt⇒acs (output _ _ _) a ()
csfwAt⇒acs (sndmsg _ _ _) a ()
csfwAt⇒acs (rcvmsg _ _ _) a ()
csfwAt⇒acs (tx     _ _ _) a ()
csfwAt⇒acs (sndack _ _ _) a ()
csfwAt⇒acs (rcvack _ _ _) a ()
csfwAt⇒acs (ack    _ _ _) a ()
csfwAt⇒acs (break  _)     a ()

------------------------------------------------------------------------
-- §1c⁷  (T11d) THE `sendBFRequestRange` LABEL PIN — node D's `cp2 → cp3` hop's own,
-- and the LAST of the family.
--
-- *** KEEP IN SYNC WITH §1c′'s `SbData`/`SbAt` BLOCK, PART BY PART *** — with ONE
-- difference, and it is the same one `RbbAt` has: the carrier is NOT `⊤`
-- (`ApiBFCar sendBFRequestRange` is `ChainRange`) and the VALUE HAS TO TRAVEL,
-- because `bfCnxt`'s only `sendBFRequestRange` row names it in its TARGET
-- (`bcWrr r`, `NodeSpecs:519-521`).  So the decoder reports the key AND the range,
-- exactly as `RbbData` reports the key and the block.
--
-- *** THE OUT MAP IS NOT BUILT, and the deviation is declared (§1c⁵'s precedent). ***
-- Its twenty-two-clause enumeration exists to give a co-leg arm a fired LINK; this
-- pin's only consumer is NODE D's own firing leg (`bfCliDrvAdj-of`'s `c23` clause,
-- `LiveDrvBFD`), where the link is the leg's own.  Build it at the first consumer
-- that needs the link, not before.
------------------------------------------------------------------------

-- the Event-level decoder of a `sendBFRequestRange` observation: its key AND range
BrrData : Event → Maybe (Link × Dir × ChainRange)
BrrData (evLabel _ (apiBF l₀ d₀ sendBFRequestRange) r) = just (l₀ , d₀ , r)
BrrData _                                              = nothing

-- "the fired observation IS `apiBF l d sendBFRequestRange` at range `r`"
BrrAt : (l : Link) (d : Dir) (r : ChainRange) {X : Set 0ℓ}
      → Net_Api Payload X → X → Set
BrrAt l d r {X} e a = BrrData (evLabel X e a) ≡ just (l , d , r)

-- IN: the `Set₁` label pin gives the `Set`-valued one by one `cong`
pin⇒brrAt : (l : Link) (d : Dir) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
            (r : ChainRange)
          → evLabel X e a ≡ evLabel ChainRange (apiBF l d sendBFRequestRange) r
          → BrrAt l d r e a
pin⇒brrAt l d e a r lbl = cong BrrData lbl

-- the ONLY consumer adjacency leaving the delivering phase `cp3` lands at `cp4`
consAdv-cp3-cp4 : {x y : ConsPh} → ConsAdv x y → x ≡ cp3 → y ≡ cp4
consAdv-cp3-cp4 c01 ()
consAdv-cp3-cp4 c12 ()
consAdv-cp3-cp4 c23 ()
consAdv-cp3-cp4 c34 _ = refl
consAdv-cp3-cp4 c45 ()
consAdv-cp3-cp4 c56 ()

------------------------------------------------------------------------
-- §1c⁗  THE `recvCSRollforward` LABEL PIN, (T7) — the `cp5` chain's own, and the
-- FIRST of these blocks on the CONSUME driver's side.
--
-- §1c‴'s twin at the consume driver's FIRST event, and the fifth instance of the same
-- block.  Two things differ from all four predecessors and both were priced as
-- "dearness" by the T6d review (§8 counts 1 and 2); ONE of them turned out to cost
-- nothing here, and the record should say which:
--
--   (i) *** THE CARRIER IS NOT `⊤`. ***  `ApiCSCar recvCSRollforward` is `Header × Tip`
--       (`Net.agda:123`), where `reqCSRequestNext`'s and `sendCSAwaitReply`'s are both
--       `⊤` (`:118`, `:127`).  That is real, and it is why the driver's `cp1` row is an
--       INPUT prefix (`SysNode.decCons:936-937`, `apiCS l d recvCSRollforward ⟶
--       consume-k l d`) rather than an output one.  But the decoder below still reports
--       the KEY ONLY, exactly like `CsaData`'s: the value never has to travel, because
--       the table's own value gate is discharged INSIDE T5's per-key pin
--       `LiveCSRow.cscRfwLands` (`:1271-1276`, the `v ≟ ht` split, `no` ⇒
--       `nothing-absurd`), and that pin is universally quantified over the value.  So
--       the "dearer `prod-a34`/`decProd-pp5-sbbAt` shape" the calibration predicted is
--       NOT needed and this block is `CsaData`'s verbatim modulo the tag.  *** Do not
--       re-derive an existential-value pin here: it would be dead weight. ***
--
--   (ii) *** THE SOURCE POSITION IS PARAMETERISED. ***  `csCnxt`'s only
--       `recvCSRollforward` row leaves `ccArf ht` — a CONSTRUCTOR APPLICATION, not a
--       bare position, unlike `csCanAwait`'s and `csAreq`'s.  That too is already paid
--       for by `cscRfwLands`, whose `ccArf ht` clause binds `ht` and gates on it; the
--       pin and the landed form below never mention the source position at all.
--
-- The OUT map is `ApiHasLink`-only, for §1c″/§1c‴'s reason, and the direction of use is
-- MIRRORED: the `cp5` chain's landing is refuted on the arm where the relay fired on
-- its DOWN link (its peer is the UP-hop client), where the four predecessors were
-- refuted on the arm where it fired on its UP link.
------------------------------------------------------------------------

-- the Event-level decoder of a `recvCSRollforward` observation: its key
CsfData : Event → Maybe (Link × Dir)
CsfData (evLabel _ (apiCS l₀ d₀ recvCSRollforward) x) = just (l₀ , d₀)
CsfData _                                             = nothing

-- "the fired observation IS `apiCS l d recvCSRollforward`", `Set`-valued
CsfAt : (l : Link) (d : Dir) {X : Set 0ℓ} → Net_Api Payload X → X → Set
CsfAt l d {X} e a = CsfData (evLabel X e a) ≡ just (l , d)

-- OUT: an observation whose `CsfData` is `just` at the key was fired at that LINK
csfAt⇒ahl : {l : Link} {d : Dir} {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
          → CsfAt l d e a → ApiHasLink l e
csfAt⇒ahl (apiCS l₀ d₀ recvCSRollforward) a refl = ahlCS
csfAt⇒ahl (apiCS l₀ d₀ sendCSRequestNext) a ()
csfAt⇒ahl (apiCS l₀ d₀ sendCSFindIntersect) a ()
csfAt⇒ahl (apiCS l₀ d₀ sendCSDone) a ()
csfAt⇒ahl (apiCS l₀ d₀ sendCSAwaitReply) a ()
csfAt⇒ahl (apiCS l₀ d₀ sendCSRollForward) a ()
csfAt⇒ahl (apiCS l₀ d₀ sendCSRollBackward) a ()
csfAt⇒ahl (apiCS l₀ d₀ sendCSIntersectFound) a ()
csfAt⇒ahl (apiCS l₀ d₀ sendCSIntersectNotFound) a ()
csfAt⇒ahl (apiCS l₀ d₀ recvCSRollback) a ()
csfAt⇒ahl (apiCS l₀ d₀ recvCSIntersectFound) a ()
csfAt⇒ahl (apiCS l₀ d₀ recvCSIntersectNotFound) a ()
csfAt⇒ahl (apiCS l₀ d₀ reqCSRequestNext) a ()
csfAt⇒ahl (apiCS l₀ d₀ reqCSFindIntersect) a ()
csfAt⇒ahl (apiBF  _ _ _) a ()
csfAt⇒ahl (apiKA  _ _ _) a ()
csfAt⇒ahl (apiTS  _ _ _) a ()
csfAt⇒ahl (apiLN  _ _ _) a ()
csfAt⇒ahl (apiLF  _ _ _) a ()
csfAt⇒ahl (done   _ _ _) a ()
csfAt⇒ahl (input  _ _ _) a ()
csfAt⇒ahl (output _ _ _) a ()
csfAt⇒ahl (sndmsg _ _ _) a ()
csfAt⇒ahl (rcvmsg _ _ _) a ()
csfAt⇒ahl (tx     _ _ _) a ()
csfAt⇒ahl (sndack _ _ _) a ()
csfAt⇒ahl (rcvack _ _ _) a ()
csfAt⇒ahl (ack    _ _ _) a ()
csfAt⇒ahl (break  _)     a ()

------------------------------------------------------------------------
-- §1d  THE CHANNEL-GENERIC `apiBF` PIN, (T7) — and why it is ONE block and not
-- three tag-specific ones.
--
-- The `cp5` chain has FOUR funded sub-phases and only the FIRST of them (`cp2`) is a
-- LANDING: the relay's `cp2 → cp3 → cp4 → cp5` hops fire `sendBFRequestRange`,
-- `recvBFBlock` and `sendBFClientDone` (`SysNode.decCons:938-957`), all three of them
-- BlockFetch api events, and none of them touches the leg's UP-hop CS CLIENT at all.
-- So the three carrying arms need exactly one fact — "the fired label is an `apiBF`
-- one, therefore the CS client is FIXED" — and that fact does not care WHICH BF tag
-- fired.  A tag-specific decoder per hop (§1c's shape, ~30 lines each) would triple
-- the block for no content, so the decoder below matches the TAG AS A WILDCARD and one
-- OUT map serves all three hops.
--
-- *** WHY THE OUT MAP IS THE FIXITY AND NOT `ApiHasLink`. ***  `LiveCSRow.CScApiRowP`
-- is LABEL-directed and at a VARIABLE event it is stuck, so a consumer holding one
-- cannot case on it — the banked reason §2b′ states its own facts with the pin as a
-- HYPOTHESIS.  Here the whole content of the fact is the label's CHANNEL, so instead of
-- a bundle slot the map below discharges it in one place, at the point where the
-- constructor is matched: at `apiBF _ _ _` the fact reduces to its catch-all clause
-- (`LiveCSRow:1116`), which IS the fixity.  Cheaper than a bundle slot and it needs no
-- new `BundleApiEvo` component.
--
-- *** AND WHY NO `ApiHasLink` MAP IS BUILT. ***  The three carrying arms are answered
-- by `refl` on the arm where the relay fired on its DOWN link (the UP-hop client is
-- LITERAL in that successor), so nothing has to be refuted BY LINK there — unlike the
-- `cp2` landing, which is why §1c⁗ does have one.  A `bfAt⇒ahl` here would be dead.
------------------------------------------------------------------------

-- the Event-level decoder of ANY `apiBF` observation: its key.  The tag is a WILDCARD
-- — this is the one label decoder in the file that is tag-generic, and the note above
-- says why that is sound for its three consumers
BfKey : Event → Maybe (Link × Dir)
BfKey (evLabel _ (apiBF l₀ d₀ _) x) = just (l₀ , d₀)
BfKey _                             = nothing

-- "the fired observation is SOME `apiBF l d _`", `Set`-valued
BfAt : (l : Link) (d : Dir) {X : Set 0ℓ} → Net_Api Payload X → X → Set
BfAt l d {X} e a = BfKey (evLabel X e a) ≡ just (l , d)

-- OUT: at an `apiBF` label a CS CLIENT's label-directed api fact IS its fixity, so the
-- pin turns the cone's row slot into the equation the three carrying arms want
bfAt⇒cscFix : {l : Link} {d : Dir} (k : Link) (kd : Dir) (pos pos′ : CScPos)
              {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
            → BfAt l d e a → CScApiRowP k kd pos pos′ e a → pos ≡ pos′
bfAt⇒cscFix k kd pos pos′ (apiBF  _ _ _) a refl h = h
bfAt⇒cscFix k kd pos pos′ (apiCS  _ _ _) a () _
bfAt⇒cscFix k kd pos pos′ (apiKA  _ _ _) a () _
bfAt⇒cscFix k kd pos pos′ (apiTS  _ _ _) a () _
bfAt⇒cscFix k kd pos pos′ (apiLN  _ _ _) a () _
bfAt⇒cscFix k kd pos pos′ (apiLF  _ _ _) a () _
bfAt⇒cscFix k kd pos pos′ (done   _ _ _) a () _
bfAt⇒cscFix k kd pos pos′ (input  _ _ _) a () _
bfAt⇒cscFix k kd pos pos′ (output _ _ _) a () _
bfAt⇒cscFix k kd pos pos′ (sndmsg _ _ _) a () _
bfAt⇒cscFix k kd pos pos′ (rcvmsg _ _ _) a () _
bfAt⇒cscFix k kd pos pos′ (tx     _ _ _) a () _
bfAt⇒cscFix k kd pos pos′ (sndack _ _ _) a () _
bfAt⇒cscFix k kd pos pos′ (rcvack _ _ _) a () _
bfAt⇒cscFix k kd pos pos′ (ack    _ _ _) a () _
bfAt⇒cscFix k kd pos pos′ (break  _)     a () _

------------------------------------------------------------------------
-- §2  THE STRENGTHENED PER-PEER api FACTS.
--
-- The CLIENT fact keeps the frozen `(BFcHasBlk bfc′ → ⊥)` and adds "the fired
-- label was not a `sendBFBlock`" — free, because no BF CLIENT position has a
-- `sendBFBlock` row at all.  That extra conjunct is what refutes the
-- server-FIXED arm at the producer's own hop (leaf 7 / leaf 9).
--
-- The SERVER fact has THREE components: the PREDECESSOR was not holding
-- (leaf 6 — `bsBlk1` has no api row), the frozen successor classification in
-- `Set`-valued form, and the producer-site POSITIVE answer "a `sendBFBlock` at
-- this slot's own key lands the sent block here" (leaves 7 and 9).
------------------------------------------------------------------------

-- the frozen successor classification, `Set`-valued (`BfsSucc`'s image)
SrvSuccA : (l : Link) (d : Dir) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
           (q : BFsPos) → Set
SrvSuccA l d e a q =
  (BFsHasBlk q → ⊥) ⊎ (Σ[ b″ ∈ Block ] SbbAt l d b″ e a × (q ≡ bsBlk1 b″))

-- THE PRODUCER-SITE POSITIVE ANSWER: a `sendBFBlock` at the slot's OWN key lands
-- exactly the sent block in this slot.  (`bsBlk1`'s two entry rows are the
-- streaming heads' `sendBFBlock`; every other position has no such row.)
SrvLands : (l : Link) (d : Dir) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
           (q : BFsPos) → Set
SrvLands l d e a q = (b″ : Block) → SbbAt l d b″ e a → q ≡ bsBlk1 b″

-- the api SERVER fact, as `BFsDecodeP`/`absBundleBF-ev-io-evo` want it
SrvApiSf : (l : Link) (d : Dir) (bfs : BFsPos) {X : Set 0ℓ}
           (e : Net_Api Payload X) (a : X) (q : BFsPos) → Set
SrvApiSf l d bfs e a q =
  (BFsHasBlk bfs → ⊥) × SrvSuccA l d e a q × SrvLands l d e a q

-- the api CLIENT fact: the frozen ¬-block successor PLUS "this was no `sendBFBlock`"
CliApiCf : {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) (q : BFcPos) → Set
CliApiCf {X} e a q = (BFcHasBlk q → ⊥) × (IsSBB (evLabel X e a) → ⊥)

-- the `Set`-valued successor classification is the frozen `BfsSucc`
srvSuccA⇒bfsSucc : (l : Link) (d : Dir) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
                   (q : BFsPos) → SrvSuccA l d e a q → BfsSucc l d q e a
srvSuccA⇒bfsSucc l d q (inj₁ nb) = inj₁ nb
srvSuccA⇒bfsSucc l d {e = e} {a} q (inj₂ (b″ , sd , eq)) =
  inj₂ (b″ , proj₂ (proj₂ (sbbAt⇒pin e a sd)) , eq)

------------------------------------------------------------------------
-- (2b) *** THE FIRED COARSE ROW ON THE api AXIS (grant #8). ***  The per-peer
-- fact the `ChanLeg` join's VISIBLE arm consumes: the peer is FIXED, or its coarse
-- table fired at the api label and the fact IS the row `LiveChanInv`'s §4b
-- producers turn into a `SrvApiAdj`/`CliApiAdj`.
--
-- NO ownership premise is needed here, unlike the io axis: an api leaves the CELL
-- alone, so a hop whose two peers both stayed fixed is simply FRAMED, and a hop
-- where both moved COMPOSES (`LiveChanInv.chan-bothApi`).  At every label that is
-- not a BF api the fact degenerates to fixity — a BF peer has no row there at all.
------------------------------------------------------------------------

-- the BF CLIENT's api-axis adjacency fact
CliApiRowP : (k : Link) (kd : Dir) (bfc bfc′ : BFcPos)
             {X : Set 0ℓ} → Net_Api Payload X → X → Set
CliApiRowP k kd bfc bfc′ (apiBF l₀ d₀ m) v =
  (bfc ≡ bfc′) ⊎ CliApiRow k kd l₀ d₀ bfc bfc′ m v
CliApiRowP k kd bfc bfc′ _ _ = bfc ≡ bfc′

-- the fired row ALONE, label-directed (the fired peer's arm of the facts below)
CliApiRowAt : (k : Link) (kd : Dir) (bfc bfc′ : BFcPos)
              {X : Set 0ℓ} → Net_Api Payload X → X → Set
CliApiRowAt k kd bfc bfc′ (apiBF l₀ d₀ m) v = CliApiRow k kd l₀ d₀ bfc bfc′ m v
CliApiRowAt k kd bfc bfc′ _ _ = bfc ≡ bfc′

-- … the server's, on both of its api-axis channels
SrvApiRowAt : (k : Link) (kd : Dir) (bfs bfs′ : BFsPos)
              {X : Set 0ℓ} → Net_Api Payload X → X → Set
SrvApiRowAt k kd bfs bfs′ (apiBF l₀ d₀ m) v = SrvApiRow k kd l₀ d₀ bfs bfs′ m v
SrvApiRowAt k kd bfs bfs′ (done l₀ d₀ N2N_BlockFetch) v = SrvDoneRow k kd l₀ d₀ bfs bfs′ v
SrvApiRowAt k kd bfs bfs′ _ _ = bfs ≡ bfs′

-- … and the BF SERVER's (its table also has the twelfth, `done`, row)
SrvApiRowP : (k : Link) (kd : Dir) (bfs bfs′ : BFsPos)
             {X : Set 0ℓ} → Net_Api Payload X → X → Set
SrvApiRowP k kd bfs bfs′ (apiBF l₀ d₀ m) v =
  (bfs ≡ bfs′) ⊎ SrvApiRow k kd l₀ d₀ bfs bfs′ m v
SrvApiRowP k kd bfs bfs′ (done l₀ d₀ N2N_BlockFetch) v =
  (bfs ≡ bfs′) ⊎ SrvDoneRow k kd l₀ d₀ bfs bfs′ v
SrvApiRowP k kd bfs bfs′ _ _ = bfs ≡ bfs′

-- (grant #8) a peer that did NOT move satisfies its adjacency fact at EVERY label
-- — the label dispatch is unavoidable, since the fact itself is label-directed
srvApiRow-fix : (k : Link) (kd : Dir) (bfs : BFsPos)
                {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) → SrvApiRowP k kd bfs bfs e a
srvApiRow-fix k kd bfs (apiBF _ _ _) a = inj₁ refl
srvApiRow-fix k kd bfs (done _ _ N2N_BlockFetch)   a = inj₁ refl
srvApiRow-fix k kd bfs (done _ _ N2N_ChainSync)    a = refl
srvApiRow-fix k kd bfs (done _ _ N2N_KeepAlive)    a = refl
srvApiRow-fix k kd bfs (done _ _ N2N_TxSubmission) a = refl
srvApiRow-fix k kd bfs (done _ _ N2N_LeiosNotify)  a = refl
srvApiRow-fix k kd bfs (done _ _ N2N_LeiosFetch)   a = refl
srvApiRow-fix k kd bfs (input  _ _ _) a = refl
srvApiRow-fix k kd bfs (output _ _ _) a = refl
srvApiRow-fix k kd bfs (apiCS _ _ _) a = refl
srvApiRow-fix k kd bfs (apiKA _ _ _) a = refl
srvApiRow-fix k kd bfs (apiTS _ _ _) a = refl
srvApiRow-fix k kd bfs (apiLN _ _ _) a = refl
srvApiRow-fix k kd bfs (apiLF _ _ _) a = refl
srvApiRow-fix k kd bfs (sndmsg _ _ _) a = refl
srvApiRow-fix k kd bfs (rcvmsg _ _ _) a = refl
srvApiRow-fix k kd bfs (tx     _ _ _) a = refl
srvApiRow-fix k kd bfs (sndack _ _ _) a = refl
srvApiRow-fix k kd bfs (rcvack _ _ _) a = refl
srvApiRow-fix k kd bfs (ack    _ _ _) a = refl
srvApiRow-fix k kd bfs (break  _)     a = refl

-- … the client twin
cliApiRow-fix : (k : Link) (kd : Dir) (bfc : BFcPos)
                {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) → CliApiRowP k kd bfc bfc e a
cliApiRow-fix k kd bfc (apiBF _ _ _) a = inj₁ refl
cliApiRow-fix k kd bfc (done _ _ _) a = refl
cliApiRow-fix k kd bfc (input  _ _ _) a = refl
cliApiRow-fix k kd bfc (output _ _ _) a = refl
cliApiRow-fix k kd bfc (apiCS _ _ _) a = refl
cliApiRow-fix k kd bfc (apiKA _ _ _) a = refl
cliApiRow-fix k kd bfc (apiTS _ _ _) a = refl
cliApiRow-fix k kd bfc (apiLN _ _ _) a = refl
cliApiRow-fix k kd bfc (apiLF _ _ _) a = refl
cliApiRow-fix k kd bfc (sndmsg _ _ _) a = refl
cliApiRow-fix k kd bfc (rcvmsg _ _ _) a = refl
cliApiRow-fix k kd bfc (tx     _ _ _) a = refl
cliApiRow-fix k kd bfc (sndack _ _ _) a = refl
cliApiRow-fix k kd bfc (rcvack _ _ _) a = refl
cliApiRow-fix k kd bfc (ack    _ _ _) a = refl
cliApiRow-fix k kd bfc (break  _)     a = refl

-- *** (T11h) THE DEGENERATION, AT THE SERVER. ***  At a ChainSync-family label the BF
-- server's row fact has no row at all — `SrvApiRowP`'s catch-all clause IS the fixity
-- equation — so the `⊎` collapses by pattern matching on the family witness alone.
-- `LiveDrvBFD` §0(4)'s `srvRowP-apiCS` states the same fact at an EXPLICIT
-- `apiCS l₀ d₀ m`; this one is its `ApiCSAt` form, which is what a consumer holding a
-- label PIN (rather than a matched constructor) can use.  Spent three times, at
-- `dnSrvPre-dn`'s `pp1`/`pp2`/`pp3` clauses.
-- *** (T12) THE CLIENT TWIN, `acsAt⇒cliFix`, IS DELETED — it was never spent. ***  It
-- was written for the client's fixity and then STRANDED by the route T11h actually
-- took: `CliApiRowP` cannot supply that fixity where it is needed (§8 (i-b)'s trap at
-- the other peer), so node D's dn BF-client fixity became `deNodeDBD`/`-CD`'s THIRD
-- component instead.  The T11h report said "both peers" in one place and explained the
-- abandonment in another; the tree now says only what is true.  If the client form is
-- ever wanted back it is four lines, the exact mirror of the server's above.
acsAt⇒srvFix : {l : Link} (k : Link) (kd : Dir) (bfs bfs′ : BFsPos)
               {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
             → ApiCSAt l e → SrvApiRowP k kd bfs bfs′ e a → bfs ≡ bfs′
acsAt⇒srvFix k kd bfs bfs′ acsCS h = h

------------------------------------------------------------------------
-- (2b′)  *** THE SERVER'S GENUINE OWN-KEY ROW (T1 / S1). ***  What the `⊎` above
-- cannot supply, and the one new peer fact the BF driver-tail coupling needs.
--
-- `SrvApiRowP`'s FIXITY arm is a real possibility at a BF api label — it is what
-- the bundle reports when the CLIENT is the firing peer — so a consumer that has
-- to know the server MOVED cannot use it.  At an `apiBF` on the server's OWN
-- direction, though, the client CANNOT be the firing peer: its table is gated on
-- `cl` and `cl ≢ sv`.  So the fact below is a theorem at every clause of §4's
-- dispatcher, and it is stated with the label pin as a HYPOTHESIS rather than by
-- dispatching on the label — which is what lets a consumer holding a VARIABLE
-- event use it at all (`SrvApiRowP` at a variable `e` is stuck).
------------------------------------------------------------------------

-- the BF SERVER's fired row at its OWN key, `reqBFRange`-pinned
SrvReqRow : (l : Link) (sv : Dir) (bfs bfs′ : BFsPos) {X : Set 0ℓ}
            (e : Net_Api Payload X) (a : X) → Set
SrvReqRow l sv bfs bfs′ {X} e a =
  (r : ChainRange) → RbrAt l sv r e a → SrvApiRow l sv l sv bfs bfs′ reqBFRange r

-- the FIRED server's answer: at the pinned tag the row IS its own, with both key
-- equations matched and the value read off the pin.  The tag dispatch is
-- unavoidable — `RbrData` matches the tag as a CONSTRUCTOR, so at a variable tag
-- the hypothesis does not reduce.
srvReqRow-of : (l : Link) (sv : Dir) (l′ : Link) (d′ : Dir) (m : ApiBFTag) (a : ApiBFCar m)
               (bfs bfs′ : BFsPos)
             → SrvApiRow l sv l′ d′ bfs bfs′ m a
             → SrvReqRow l sv bfs bfs′ (apiBF l′ d′ m) a
srvReqRow-of l sv l′ d′ sendBFRequestRange a bfs bfs′ row r rbr = ⊥-elim (nothing-absurd rbr)
srvReqRow-of l sv l′ d′ sendBFClientDone   a bfs bfs′ row r rbr = ⊥-elim (nothing-absurd rbr)
srvReqRow-of l sv l′ d′ sendBFStartBatch   a bfs bfs′ row r rbr = ⊥-elim (nothing-absurd rbr)
srvReqRow-of l sv l′ d′ sendBFNoBlocks     a bfs bfs′ row r rbr = ⊥-elim (nothing-absurd rbr)
srvReqRow-of l sv l′ d′ sendBFBlock        a bfs bfs′ row r rbr = ⊥-elim (nothing-absurd rbr)
srvReqRow-of l sv l′ d′ sendBFBatchDone    a bfs bfs′ row r rbr = ⊥-elim (nothing-absurd rbr)
srvReqRow-of l sv l′ d′ recvBFBlock        a bfs bfs′ row r rbr = ⊥-elim (nothing-absurd rbr)
srvReqRow-of l sv l′ d′ reqBFRange a bfs bfs′ (refl , refl , eq) r rbr
  with just-injective rbr
... | refl = refl , refl , eq

-- … and the answer when the CLIENT is the firing peer: the client's own row
-- carries `d′ ≡ cl` while the pin says `d′ ≡ sv`, so `cl ≢ sv` refutes that case
-- outright.  (The server slot IS untouched there, and its own-key row would be
-- FALSE — which is exactly why the `⊎` above cannot serve S1.)
srvReqRow-cli : (l : Link) (cl sv : Dir) → cl ≢ sv
              → (l′ : Link) (d′ : Dir) (m : ApiBFTag) (a : ApiBFCar m)
                (bfc bfc′ : BFcPos) (bfs : BFsPos)
              → CliApiRow l cl l′ d′ bfc bfc′ m a
              → SrvReqRow l sv bfs bfs (apiBF l′ d′ m) a
srvReqRow-cli l cl sv ne l′ d′ sendBFRequestRange a bfc bfc′ bfs row r rbr = ⊥-elim (nothing-absurd rbr)
srvReqRow-cli l cl sv ne l′ d′ sendBFClientDone   a bfc bfc′ bfs row r rbr = ⊥-elim (nothing-absurd rbr)
srvReqRow-cli l cl sv ne l′ d′ sendBFStartBatch   a bfc bfc′ bfs row r rbr = ⊥-elim (nothing-absurd rbr)
srvReqRow-cli l cl sv ne l′ d′ sendBFNoBlocks     a bfc bfc′ bfs row r rbr = ⊥-elim (nothing-absurd rbr)
srvReqRow-cli l cl sv ne l′ d′ sendBFBlock        a bfc bfc′ bfs row r rbr = ⊥-elim (nothing-absurd rbr)
srvReqRow-cli l cl sv ne l′ d′ sendBFBatchDone    a bfc bfc′ bfs row r rbr = ⊥-elim (nothing-absurd rbr)
srvReqRow-cli l cl sv ne l′ d′ recvBFBlock        a bfc bfc′ bfs row r rbr = ⊥-elim (nothing-absurd rbr)
srvReqRow-cli l cl sv ne l′ d′ reqBFRange a bfc bfc′ bfs (refl , refl , _) r rbr
  with just-injective rbr
... | refl = ⊥-elim (ne refl)

-- *** (T2) THE SAME FACT AT THE `sendBFStartBatch` ROW, IN ITS LANDED FORM. ***
-- `pp5`'s arm does not need the row as a row — it needs where the row LANDS — so
-- this states the landing and keeps the table reading here, once, instead of at the
-- consumer.  `bfSnxt`'s only `sendBFStartBatch` row is `bsBusy → bsWsb`
-- (`NodeSpecs:604-605`, i.e. `ceqBFs03`), so a fire at the server's own key out of
-- `bsBusy` lands at `bsWsb` and nowhere else.
SrvSbLand : (l : Link) (sv : Dir) (bfs bfs′ : BFsPos) {X : Set 0ℓ}
            (e : Net_Api Payload X) (a : X) → Set
SrvSbLand l sv bfs bfs′ e a =
  SbAt l sv e a → coarsenBFs bfs ≡ NS.bsBusy → coarsenBFs bfs′ ≡ NS.bsWsb

-- the FIRED server's answer: at the pinned tag the row is its own, and `ceqBFs03`
-- identifies its target.  The tag dispatch is unavoidable for §2b′'s reason —
-- `SbData` matches the tag as a CONSTRUCTOR, so at a variable tag the pin is stuck.
srvSbLand-of : (l : Link) (sv : Dir) (l₀ : Link) (d₀ : Dir) (m : ApiBFTag) (a : ApiBFCar m)
               (bfs bfs′ : BFsPos)
             → SrvApiRow l sv l₀ d₀ bfs bfs′ m a
             → SrvSbLand l sv bfs bfs′ (apiBF l₀ d₀ m) a
srvSbLand-of l sv l₀ d₀ sendBFRequestRange a bfs bfs′ row sb bsy = ⊥-elim (nothing-absurd sb)
srvSbLand-of l sv l₀ d₀ sendBFClientDone   a bfs bfs′ row sb bsy = ⊥-elim (nothing-absurd sb)
srvSbLand-of l sv l₀ d₀ sendBFNoBlocks     a bfs bfs′ row sb bsy = ⊥-elim (nothing-absurd sb)
srvSbLand-of l sv l₀ d₀ sendBFBlock        a bfs bfs′ row sb bsy = ⊥-elim (nothing-absurd sb)
srvSbLand-of l sv l₀ d₀ sendBFBatchDone    a bfs bfs′ row sb bsy = ⊥-elim (nothing-absurd sb)
srvSbLand-of l sv l₀ d₀ recvBFBlock        a bfs bfs′ row sb bsy = ⊥-elim (nothing-absurd sb)
srvSbLand-of l sv l₀ d₀ reqBFRange         a bfs bfs′ row sb bsy = ⊥-elim (nothing-absurd sb)
srvSbLand-of l sv l₀ d₀ sendBFStartBatch a bfs bfs′ (refl , refl , eq) sb bsy =
  just-injective
    (trans (sym (subst (λ z → NS.bfSnxt l sv z (ApiBFCar sendBFStartBatch
                                               , apiBF l sv sendBFStartBatch) a
                             ≡ just (coarsenBFs bfs′))
                       bsy eq))
           (ceqBFs03 {a} l sv))

-- … and the answer when the CLIENT is the firing peer: its own row carries
-- `d₀ ≡ cl` while the pin says `d₀ ≡ sv`, so `cl ≢ sv` refutes that case outright
srvSbLand-cli : (l : Link) (cl sv : Dir) → cl ≢ sv
              → (l₀ : Link) (d₀ : Dir) (m : ApiBFTag) (a : ApiBFCar m)
                (bfc bfc′ : BFcPos) (bfs : BFsPos)
              → CliApiRow l cl l₀ d₀ bfc bfc′ m a
              → SrvSbLand l sv bfs bfs (apiBF l₀ d₀ m) a
srvSbLand-cli l cl sv ne l₀ d₀ sendBFRequestRange a bfc bfc′ bfs row sb bsy = ⊥-elim (nothing-absurd sb)
srvSbLand-cli l cl sv ne l₀ d₀ sendBFClientDone   a bfc bfc′ bfs row sb bsy = ⊥-elim (nothing-absurd sb)
srvSbLand-cli l cl sv ne l₀ d₀ sendBFNoBlocks     a bfc bfc′ bfs row sb bsy = ⊥-elim (nothing-absurd sb)
srvSbLand-cli l cl sv ne l₀ d₀ sendBFBlock        a bfc bfc′ bfs row sb bsy = ⊥-elim (nothing-absurd sb)
srvSbLand-cli l cl sv ne l₀ d₀ sendBFBatchDone    a bfc bfc′ bfs row sb bsy = ⊥-elim (nothing-absurd sb)
srvSbLand-cli l cl sv ne l₀ d₀ recvBFBlock        a bfc bfc′ bfs row sb bsy = ⊥-elim (nothing-absurd sb)
srvSbLand-cli l cl sv ne l₀ d₀ reqBFRange         a bfc bfc′ bfs row sb bsy = ⊥-elim (nothing-absurd sb)
srvSbLand-cli l cl sv ne l₀ d₀ sendBFStartBatch a bfc bfc′ bfs (refl , refl , _) sb bsy
  with just-injective sb
... | refl = ⊥-elim (ne refl)

------------------------------------------------------------------------
-- §2b′⁺  (T10) THE SERVER's `sendBFBatchDone` LANDING — §2b′'s THIRD member.
--
-- *** KEEP IN SYNC WITH `SrvSbLand`/`srvSbLand-of`/`srvSbLand-cli` DIRECTLY ABOVE,
-- CLAUSE BY CLAUSE. ***  This is that trio with the tag moved one row along the
-- server's own table and the two positions changed — `bfSnxt`'s only
-- `sendBFBatchDone` row is `bsStream → bsWbd` (`NodeSpecs:625-627`, i.e.
-- `ceqBFs06`), so a fire at the server's own key out of `bsStream` lands at `bsWbd`
-- and nowhere else.  The eight-clause tag dispatch is unavoidable for §2b′'s reason
-- (`BdData` matches the tag as a CONSTRUCTOR, so at a variable tag the pin is stuck)
-- and the `sendBFStartBatch` clause here is the mirror image of the
-- `sendBFBatchDone` clause there — the two families cross at exactly one place each.
--
-- *** WHY IT EXISTS, in one sentence: `SrvApiRowP`'s FIXITY arm is the case node A's
-- up-hop BF coupling must exclude at the `pp6 → pp7` crossing, and only the bundle
-- knows which peer fired. ***  That is `SrvSbLand`'s own justification at the relay's
-- `pp4 → pp5`; this is the same obligation at the fourth node.
--
-- MERGED-FIELD CHECK (the design pass, done and recorded): this is NOT a second
-- field reporting the same fact as `SrvSbLand`.  The two are indexed at DISJOINT
-- tags, and a `Σ`-component reporting "the landing at whichever tag fired" is not
-- formable — the tag is matched as a constructor, so one component per tag is the
-- only shape that reduces.  The combination the pair admits and no producer creates
-- (both landings genuine at one label) is uninhabited by that disjointness.
------------------------------------------------------------------------

-- the server's `sendBFBatchDone` row exists at `bsStream` AND NOWHERE ELSE, so a
-- fired row pins its own SOURCE: every other position falls to `bfSnxt`'s catch-all
-- and answers `nothing`.  Stated on the ABSTRACT position (never a `with` on
-- `coarsenBFs bfs`, the campaign's `blkA`-module rule)
bdRow⇒stream : ∀ {a} (l : Link) (d : Dir) (q q′ : NS.BFsPos)
             → NS.bfSnxt l d q (ApiBFCar sendBFBatchDone , apiBF l d sendBFBatchDone) a
               ≡ just q′
             → q ≡ NS.bsStream
bdRow⇒stream l d NS.bsIdle      q′ ()
bdRow⇒stream l d (NS.bsAreq r)  q′ ()
bdRow⇒stream l d NS.bsBusy      q′ ()
bdRow⇒stream l d NS.bsDdone     q′ ()
bdRow⇒stream l d NS.bsWsb       q′ ()
bdRow⇒stream l d NS.bsStream    q′ _ = refl
bdRow⇒stream l d NS.bsWnb       q′ ()
bdRow⇒stream l d (NS.bsWblk b)  q′ ()
bdRow⇒stream l d NS.bsWbd       q′ ()
bdRow⇒stream l d NS.bsTerm      q′ ()

-- the LANDED form: a `sendBFBatchDone` at the server's own key comes OUT of
-- `bsStream` and lands at `bsWbd`.
--
-- *** IT REPORTS THE PAIR, AND THE SOURCE HALF IS THE LOAD-BEARING ONE. ***  A
-- consumer that only learns the TARGET still cannot preserve a coupling across the
-- crossing: it has to refute the states in which the driver fires the batch-done
-- with its server somewhere else, and `bdRow⇒stream` is exactly that refutation,
-- read off the table rather than assumed.  `SrvSbLand`'s hypothesis-form was enough
-- for `pp5` because the `pp5` arm already HOLDS its source position (the coupling's
-- own antecedent); node A's up-hop coupling does not
SrvBdLand : (l : Link) (sv : Dir) (bfs bfs′ : BFsPos) {X : Set 0ℓ}
            (e : Net_Api Payload X) (a : X) → Set
SrvBdLand l sv bfs bfs′ e a =
  BdAt l sv e a → (coarsenBFs bfs ≡ NS.bsStream) × (coarsenBFs bfs′ ≡ NS.bsWbd)

-- the FIRED server's answer: at the pinned tag the row is its own, and `ceqBFs06`
-- identifies its target
srvBdLand-of : (l : Link) (sv : Dir) (l₀ : Link) (d₀ : Dir) (m : ApiBFTag) (a : ApiBFCar m)
               (bfs bfs′ : BFsPos)
             → SrvApiRow l sv l₀ d₀ bfs bfs′ m a
             → SrvBdLand l sv bfs bfs′ (apiBF l₀ d₀ m) a
srvBdLand-of l sv l₀ d₀ sendBFRequestRange a bfs bfs′ row bd = ⊥-elim (nothing-absurd bd)
srvBdLand-of l sv l₀ d₀ sendBFClientDone   a bfs bfs′ row bd = ⊥-elim (nothing-absurd bd)
srvBdLand-of l sv l₀ d₀ sendBFNoBlocks     a bfs bfs′ row bd = ⊥-elim (nothing-absurd bd)
srvBdLand-of l sv l₀ d₀ sendBFBlock        a bfs bfs′ row bd = ⊥-elim (nothing-absurd bd)
srvBdLand-of l sv l₀ d₀ sendBFStartBatch   a bfs bfs′ row bd = ⊥-elim (nothing-absurd bd)
srvBdLand-of l sv l₀ d₀ recvBFBlock        a bfs bfs′ row bd = ⊥-elim (nothing-absurd bd)
srvBdLand-of l sv l₀ d₀ reqBFRange         a bfs bfs′ row bd = ⊥-elim (nothing-absurd bd)
srvBdLand-of l sv l₀ d₀ sendBFBatchDone a bfs bfs′ (refl , refl , eq) bd =
    str
  , just-injective
      (trans (sym (subst (λ z → NS.bfSnxt l sv z (ApiBFCar sendBFBatchDone
                                                 , apiBF l sv sendBFBatchDone) a
                               ≡ just (coarsenBFs bfs′))
                         str eq))
             (ceqBFs06 {a} l sv))
  where
  str : coarsenBFs bfs ≡ NS.bsStream
  str = bdRow⇒stream l sv (coarsenBFs bfs) (coarsenBFs bfs′) eq

-- … and the answer when the CLIENT is the firing peer: its own row carries
-- `d₀ ≡ cl` while the pin says `d₀ ≡ sv`, so `cl ≢ sv` refutes that case outright
srvBdLand-cli : (l : Link) (cl sv : Dir) → cl ≢ sv
              → (l₀ : Link) (d₀ : Dir) (m : ApiBFTag) (a : ApiBFCar m)
                (bfc bfc′ : BFcPos) (bfs : BFsPos)
              → CliApiRow l cl l₀ d₀ bfc bfc′ m a
              → SrvBdLand l sv bfs bfs (apiBF l₀ d₀ m) a
srvBdLand-cli l cl sv ne l₀ d₀ sendBFRequestRange a bfc bfc′ bfs row bd = ⊥-elim (nothing-absurd bd)
srvBdLand-cli l cl sv ne l₀ d₀ sendBFClientDone   a bfc bfc′ bfs row bd = ⊥-elim (nothing-absurd bd)
srvBdLand-cli l cl sv ne l₀ d₀ sendBFNoBlocks     a bfc bfc′ bfs row bd = ⊥-elim (nothing-absurd bd)
srvBdLand-cli l cl sv ne l₀ d₀ sendBFBlock        a bfc bfc′ bfs row bd = ⊥-elim (nothing-absurd bd)
srvBdLand-cli l cl sv ne l₀ d₀ sendBFStartBatch   a bfc bfc′ bfs row bd = ⊥-elim (nothing-absurd bd)
srvBdLand-cli l cl sv ne l₀ d₀ recvBFBlock        a bfc bfc′ bfs row bd = ⊥-elim (nothing-absurd bd)
srvBdLand-cli l cl sv ne l₀ d₀ reqBFRange         a bfc bfc′ bfs row bd = ⊥-elim (nothing-absurd bd)
srvBdLand-cli l cl sv ne l₀ d₀ sendBFBatchDone a bfc bfc′ bfs (refl , refl , _) bd
  with just-injective bd
... | refl = ⊥-elim (ne refl)

------------------------------------------------------------------------
-- §2b′⁶  (T10) THE CLIENT's `recvBFBlock` LANDING — §2b′'s FOURTH member, and the
-- first on the CLIENT side of the BlockFetch axis.
--
-- *** KEEP IN SYNC WITH §2b′⁺'s trio DIRECTLY ABOVE, CLAUSE BY CLAUSE. ***  That is
-- this trio with the peer role swapped: `bfCnxt`'s only `recvBFBlock` row is
-- `bcAblk b → bcStream` (`NodeSpecs:552-555`, i.e. `ceqBFc10`), so a delivery at the
-- client's own key out of `bcAblk b` lands at `bcStream` and nowhere else.
--
-- *** WHY IT TAKES ITS SOURCE AS A HYPOTHESIS where `SrvBdLand` DERIVES one. ***
-- `bfCnxt`'s `bcAblk` row is gated on the carried VALUE (`x ≟ b`), so at a variable
-- carrier the table application is STUCK and no source dispatch reduces — where
-- `bfSnxt`'s `sendBFBatchDone` row is value-free and `bdRow⇒stream` could read the
-- source off it.  The hypothesis costs the consumer nothing: the relay's own peel
-- already holds the source (`PipeValFill.bundle-recv-cliPos`, which is what the
-- `WUpGate` component is built from), so the pin is passed, not proved twice.
--
-- *** WHY IT EXISTS: *** `CliApiRowP`'s FIXITY arm is the case the `cp4` client
-- REGION must exclude at its own entering step — "the relay fired `recvBFBlock` and
-- its client stayed where it was" — and only the bundle knows which peer fired.
------------------------------------------------------------------------

-- the LANDED form: a `recvBFBlock` at the client's own key, out of `bcAblk b`, puts
-- it at `bcStream`
CliRecvLand : (l : Link) (cl : Dir) (bfc bfc′ : BFcPos) {X : Set 0ℓ}
              (e : Net_Api Payload X) (a : X) → Set
CliRecvLand l cl bfc bfc′ e a =
  (b : Block₃) → RbbAt l cl b e a → coarsenBFc bfc ≡ NS.bcAblk b
  → coarsenBFc bfc′ ≡ NS.bcStream

-- the FIRED client's answer: at the pinned tag the row is its own, and `ceqBFc10`
-- identifies its target
cliRecvLand-of : (l : Link) (cl : Dir) (l₀ : Link) (d₀ : Dir) (m : ApiBFTag) (a : ApiBFCar m)
                 (bfc bfc′ : BFcPos)
               → CliApiRow l cl l₀ d₀ bfc bfc′ m a
               → CliRecvLand l cl bfc bfc′ (apiBF l₀ d₀ m) a
cliRecvLand-of l cl l₀ d₀ sendBFRequestRange a bfc bfc′ row b rb = ⊥-elim (nothing-absurd rb)
cliRecvLand-of l cl l₀ d₀ sendBFClientDone   a bfc bfc′ row b rb = ⊥-elim (nothing-absurd rb)
cliRecvLand-of l cl l₀ d₀ sendBFNoBlocks     a bfc bfc′ row b rb = ⊥-elim (nothing-absurd rb)
cliRecvLand-of l cl l₀ d₀ sendBFBlock        a bfc bfc′ row b rb = ⊥-elim (nothing-absurd rb)
cliRecvLand-of l cl l₀ d₀ sendBFStartBatch   a bfc bfc′ row b rb = ⊥-elim (nothing-absurd rb)
cliRecvLand-of l cl l₀ d₀ sendBFBatchDone    a bfc bfc′ row b rb = ⊥-elim (nothing-absurd rb)
cliRecvLand-of l cl l₀ d₀ reqBFRange         a bfc bfc′ row b rb = ⊥-elim (nothing-absurd rb)
cliRecvLand-of l cl l₀ d₀ recvBFBlock a bfc bfc′ (refl , refl , eq) b rb src
  with just-injective rb
... | refl =
      just-injective
        (trans (sym (subst (λ z → NS.bfCnxt l cl z (ApiBFCar recvBFBlock
                                                   , apiBF l cl recvBFBlock) a
                                 ≡ just (coarsenBFc bfc′))
                           src eq))
               (ceqBFc10 {a} l cl))

-- no `bfSnxt` row answers a `recvBFBlock` at ANY position — the tag falls to the
-- server table's catch-all — but the catch-all only fires once the POSITION is a
-- constructor, so the refutation is a ten-clause dispatch and not a `()` (measured:
-- `[UnequalTerms] … != nothing` at the variable position)
rbbSrv-⊥ : ∀ {a} (l : Link) (d : Dir) (q q′ : NS.BFsPos)
         → NS.bfSnxt l d q (ApiBFCar recvBFBlock , apiBF l d recvBFBlock) a ≡ just q′
         → ⊥
rbbSrv-⊥ l d NS.bsIdle      q′ ()
rbbSrv-⊥ l d (NS.bsAreq r)  q′ ()
rbbSrv-⊥ l d NS.bsBusy      q′ ()
rbbSrv-⊥ l d NS.bsDdone     q′ ()
rbbSrv-⊥ l d NS.bsWsb       q′ ()
rbbSrv-⊥ l d NS.bsStream    q′ ()
rbbSrv-⊥ l d NS.bsWnb       q′ ()
rbbSrv-⊥ l d (NS.bsWblk b)  q′ ()
rbbSrv-⊥ l d NS.bsWbd       q′ ()
rbbSrv-⊥ l d NS.bsTerm      q′ ()

-- … and the answer when the SERVER is the firing peer: its own row's equation is the
-- one `rbbSrv-⊥` refutes, so the case is closed outright
cliRecvLand-srv : (l : Link) (cl sv : Dir)
                  (l₀ : Link) (d₀ : Dir) (m : ApiBFTag) (a : ApiBFCar m)
                  (bfc : BFcPos) (bfs bfs′ : BFsPos)
                → SrvApiRow l sv l₀ d₀ bfs bfs′ m a
                → CliRecvLand l cl bfc bfc (apiBF l₀ d₀ m) a
cliRecvLand-srv l cl sv l₀ d₀ sendBFRequestRange a bfc bfs bfs′ row b rb = ⊥-elim (nothing-absurd rb)
cliRecvLand-srv l cl sv l₀ d₀ sendBFClientDone   a bfc bfs bfs′ row b rb = ⊥-elim (nothing-absurd rb)
cliRecvLand-srv l cl sv l₀ d₀ sendBFNoBlocks     a bfc bfs bfs′ row b rb = ⊥-elim (nothing-absurd rb)
cliRecvLand-srv l cl sv l₀ d₀ sendBFBlock        a bfc bfs bfs′ row b rb = ⊥-elim (nothing-absurd rb)
cliRecvLand-srv l cl sv l₀ d₀ sendBFStartBatch   a bfc bfs bfs′ row b rb = ⊥-elim (nothing-absurd rb)
cliRecvLand-srv l cl sv l₀ d₀ sendBFBatchDone    a bfc bfs bfs′ row b rb = ⊥-elim (nothing-absurd rb)
cliRecvLand-srv l cl sv l₀ d₀ reqBFRange         a bfc bfs bfs′ row b rb = ⊥-elim (nothing-absurd rb)
cliRecvLand-srv l cl sv l₀ d₀ recvBFBlock a bfc bfs bfs′ (refl , refl , eq) b rb src =
  ⊥-elim (rbbSrv-⊥ l sv (coarsenBFs bfs) (coarsenBFs bfs′) eq)


------------------------------------------------------------------------
-- §2b″  *** (T5) THE CS SERVER'S `reqCSRequestNext` LANDING. ***  The exact twin of
-- §2b′'s `SrvSbLand` on the ChainSync axis, and it exists for the identical reason:
-- `CSsApiRowP`'s FIXITY arm is the case the `pp1` arm of the coupling must exclude
-- (a server that did not move cannot be at `csCanAwait` for any reason the consumer
-- holds), and only the bundle knows which peer fired.
--
-- The conclusion is the LANDING rather than the row, like `SrvSbLand`'s: the arm
-- needs where the row goes, and keeping the table reading here — in T5's own per-key
-- pin `LiveCSRow.cssReqLands`, `csSnxt`'s ONLY `reqCSRequestNext` row
-- (`NodeSpecs:428-430`) — keeps it out of the consumer.  Unlike `SrvSbLand` it needs
-- NO source-position antecedent: the pin plus the row determine the target outright.
------------------------------------------------------------------------

-- the CS SERVER's fired row at its OWN key, in landed form
CssReqLand : (l : Link) (sv : Dir) (css css′ : CSsPos) {X : Set 0ℓ}
             (e : Net_Api Payload X) (a : X) → Set
CssReqLand l sv css css′ e a = CsrAt l sv e a → coarsenCSs css′ ≡ NS.csCanAwait

-- the FIRED server's answer: the pin identifies the tag AND the key, and the per-key
-- pin reads the landing off the row.  The tag dispatch is unavoidable for §2b′'s
-- reason — `CsrData` matches the tag as a CONSTRUCTOR.
cssReqLand-of : (l : Link) (sv : Dir) (l₀ : Link) (d₀ : Dir) (m : ApiCSTag)
                (a : ApiCSCar m) (css css′ : CSsPos)
              → CSsRow l sv (apiCS l₀ d₀ m) a css css′
              → CssReqLand l sv css css′ (apiCS l₀ d₀ m) a
cssReqLand-of l sv l₀ d₀ sendCSRequestNext a css css′ row p = ⊥-elim (nothing-absurd p)
cssReqLand-of l sv l₀ d₀ sendCSFindIntersect a css css′ row p = ⊥-elim (nothing-absurd p)
cssReqLand-of l sv l₀ d₀ sendCSDone a css css′ row p = ⊥-elim (nothing-absurd p)
cssReqLand-of l sv l₀ d₀ sendCSAwaitReply a css css′ row p = ⊥-elim (nothing-absurd p)
cssReqLand-of l sv l₀ d₀ sendCSRollForward a css css′ row p = ⊥-elim (nothing-absurd p)
cssReqLand-of l sv l₀ d₀ sendCSRollBackward a css css′ row p = ⊥-elim (nothing-absurd p)
cssReqLand-of l sv l₀ d₀ sendCSIntersectFound a css css′ row p = ⊥-elim (nothing-absurd p)
cssReqLand-of l sv l₀ d₀ sendCSIntersectNotFound a css css′ row p = ⊥-elim (nothing-absurd p)
cssReqLand-of l sv l₀ d₀ recvCSRollforward a css css′ row p = ⊥-elim (nothing-absurd p)
cssReqLand-of l sv l₀ d₀ recvCSRollback a css css′ row p = ⊥-elim (nothing-absurd p)
cssReqLand-of l sv l₀ d₀ recvCSIntersectFound a css css′ row p = ⊥-elim (nothing-absurd p)
cssReqLand-of l sv l₀ d₀ recvCSIntersectNotFound a css css′ row p = ⊥-elim (nothing-absurd p)
cssReqLand-of l sv l₀ d₀ reqCSFindIntersect a css css′ row p = ⊥-elim (nothing-absurd p)
cssReqLand-of l sv l₀ d₀ reqCSRequestNext a css css′ row p
  with just-injective p
... | refl = cssReqLands l sv (coarsenCSs css) a (coarsenCSs css′) row

-- … and the answer when the CS CLIENT is the firing peer: its own row carries
-- `d₀ ≡ cl` (recovered by `LiveCSRow.cscRow-key`) while the pin says `d₀ ≡ sv`, so
-- `cl ≢ sv` refutes that case outright — `srvReqRow-cli`'s argument at the CS axis
cssReqLand-cli : (l : Link) (cl sv : Dir) → cl ≢ sv
               → (l₀ : Link) (d₀ : Dir) (m : ApiCSTag) (a : ApiCSCar m)
                 (csc csc′ : CScPos) (css : CSsPos)
               → CScRow l cl (apiCS l₀ d₀ m) a csc csc′
               → CssReqLand l sv css css (apiCS l₀ d₀ m) a
cssReqLand-cli l cl sv ne l₀ d₀ sendCSRequestNext a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssReqLand-cli l cl sv ne l₀ d₀ sendCSFindIntersect a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssReqLand-cli l cl sv ne l₀ d₀ sendCSDone a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssReqLand-cli l cl sv ne l₀ d₀ sendCSAwaitReply a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssReqLand-cli l cl sv ne l₀ d₀ sendCSRollForward a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssReqLand-cli l cl sv ne l₀ d₀ sendCSRollBackward a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssReqLand-cli l cl sv ne l₀ d₀ sendCSIntersectFound a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssReqLand-cli l cl sv ne l₀ d₀ sendCSIntersectNotFound a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssReqLand-cli l cl sv ne l₀ d₀ recvCSRollforward a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssReqLand-cli l cl sv ne l₀ d₀ recvCSRollback a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssReqLand-cli l cl sv ne l₀ d₀ recvCSIntersectFound a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssReqLand-cli l cl sv ne l₀ d₀ recvCSIntersectNotFound a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssReqLand-cli l cl sv ne l₀ d₀ reqCSFindIntersect a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssReqLand-cli l cl sv ne l₀ d₀ reqCSRequestNext a csc csc′ css row p
  with just-injective p
... | refl =
      ⊥-elim (ne (sym (proj₂ (cscRow-key l cl (coarsenCSc csc)
                                (CS.apiCSev l sv reqCSRequestNext) row))))

------------------------------------------------------------------------
-- §2b‴  *** (T6d) THE CS SERVER'S `sendCSAwaitReply` LANDING. ***  §2b″'s twin at
-- the produce driver's SECOND event, and it exists for §2b″'s reason: `CSsApiRowP`'s
-- FIXITY arm is the case the `pp2` arm of the coupling must exclude, and only the
-- bundle knows which peer fired.
--
-- The conclusion is again the LANDING rather than the row, and the table reading is
-- again kept at T6's own per-key pin (`LiveCSRow.cssAwaitLands`, `csSnxt`'s ONLY
-- `sendCSAwaitReply` row, `NodeSpecs:445-446`).  Like §2b″'s and unlike `SrvSbLand`'s
-- it needs NO source-position antecedent: the pin plus the row determine the target
-- outright, because `csCanAwait` is the only position with such a row.
--
-- *** WHY THE TARGET IS `csWar` AND NOT `csMust`. ***  The `pp2` clause of the
-- coupling is a REGION `{csWar, csMust}` (`LiveDrvBF` §1) — the api step that enters
-- `pp2` lands the server at the region's ENTRY, and only the server's own wire-send
-- (an io hop past the api one) carries it on to `csMust`.  This landing is the entry;
-- `LiveCSRow` §4c's four io facts are what keep the region closed after it.
------------------------------------------------------------------------

-- the CS SERVER's fired row at its OWN key, in `sendCSAwaitReply`-landed form
CssAwLand : (l : Link) (sv : Dir) (css css′ : CSsPos) {X : Set 0ℓ}
            (e : Net_Api Payload X) (a : X) → Set
CssAwLand l sv css css′ e a = CsaAt l sv e a → coarsenCSs css′ ≡ NS.csWar

-- the FIRED server's answer: the pin identifies the tag AND the key, and the per-key
-- pin reads the landing off the row.  The tag dispatch is unavoidable for §2b′'s
-- reason — `CsaData` matches the tag as a CONSTRUCTOR.
cssAwLand-of : (l : Link) (sv : Dir) (l₀ : Link) (d₀ : Dir) (m : ApiCSTag)
               (a : ApiCSCar m) (css css′ : CSsPos)
             → CSsRow l sv (apiCS l₀ d₀ m) a css css′
             → CssAwLand l sv css css′ (apiCS l₀ d₀ m) a
cssAwLand-of l sv l₀ d₀ sendCSRequestNext a css css′ row p = ⊥-elim (nothing-absurd p)
cssAwLand-of l sv l₀ d₀ sendCSFindIntersect a css css′ row p = ⊥-elim (nothing-absurd p)
cssAwLand-of l sv l₀ d₀ sendCSDone a css css′ row p = ⊥-elim (nothing-absurd p)
cssAwLand-of l sv l₀ d₀ sendCSRollForward a css css′ row p = ⊥-elim (nothing-absurd p)
cssAwLand-of l sv l₀ d₀ sendCSRollBackward a css css′ row p = ⊥-elim (nothing-absurd p)
cssAwLand-of l sv l₀ d₀ sendCSIntersectFound a css css′ row p = ⊥-elim (nothing-absurd p)
cssAwLand-of l sv l₀ d₀ sendCSIntersectNotFound a css css′ row p = ⊥-elim (nothing-absurd p)
cssAwLand-of l sv l₀ d₀ recvCSRollforward a css css′ row p = ⊥-elim (nothing-absurd p)
cssAwLand-of l sv l₀ d₀ recvCSRollback a css css′ row p = ⊥-elim (nothing-absurd p)
cssAwLand-of l sv l₀ d₀ recvCSIntersectFound a css css′ row p = ⊥-elim (nothing-absurd p)
cssAwLand-of l sv l₀ d₀ recvCSIntersectNotFound a css css′ row p = ⊥-elim (nothing-absurd p)
cssAwLand-of l sv l₀ d₀ reqCSRequestNext a css css′ row p = ⊥-elim (nothing-absurd p)
cssAwLand-of l sv l₀ d₀ reqCSFindIntersect a css css′ row p = ⊥-elim (nothing-absurd p)
cssAwLand-of l sv l₀ d₀ sendCSAwaitReply a css css′ row p
  with just-injective p
... | refl = cssAwaitLands l sv (coarsenCSs css) a (coarsenCSs css′) row

-- … and the answer when the CS CLIENT is the firing peer: §2b″'s argument at the
-- other tag — its own row carries `d₀ ≡ cl` (recovered by `LiveCSRow.cscRow-key`)
-- while the pin says `d₀ ≡ sv`, so `cl ≢ sv` refutes that case outright
cssAwLand-cli : (l : Link) (cl sv : Dir) → cl ≢ sv
              → (l₀ : Link) (d₀ : Dir) (m : ApiCSTag) (a : ApiCSCar m)
                (csc csc′ : CScPos) (css : CSsPos)
              → CScRow l cl (apiCS l₀ d₀ m) a csc csc′
              → CssAwLand l sv css css (apiCS l₀ d₀ m) a
cssAwLand-cli l cl sv ne l₀ d₀ sendCSRequestNext a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssAwLand-cli l cl sv ne l₀ d₀ sendCSFindIntersect a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssAwLand-cli l cl sv ne l₀ d₀ sendCSDone a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssAwLand-cli l cl sv ne l₀ d₀ sendCSRollForward a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssAwLand-cli l cl sv ne l₀ d₀ sendCSRollBackward a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssAwLand-cli l cl sv ne l₀ d₀ sendCSIntersectFound a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssAwLand-cli l cl sv ne l₀ d₀ sendCSIntersectNotFound a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssAwLand-cli l cl sv ne l₀ d₀ recvCSRollforward a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssAwLand-cli l cl sv ne l₀ d₀ recvCSRollback a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssAwLand-cli l cl sv ne l₀ d₀ recvCSIntersectFound a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssAwLand-cli l cl sv ne l₀ d₀ recvCSIntersectNotFound a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssAwLand-cli l cl sv ne l₀ d₀ reqCSRequestNext a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssAwLand-cli l cl sv ne l₀ d₀ reqCSFindIntersect a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssAwLand-cli l cl sv ne l₀ d₀ sendCSAwaitReply a csc csc′ css row p
  with just-injective p
... | refl =
      ⊥-elim (ne (sym (proj₂ (cscRow-key l cl (coarsenCSc csc)
                                (CS.apiCSev l sv sendCSAwaitReply) row))))

------------------------------------------------------------------------
-- §2b⁶  *** (T11b) THE CS SERVER'S `sendCSRollForward` LANDING — the `pp3` one, and
-- the THIRD member of `DnCsDrv`'s landing arm. ***  §2b‴'s block at the produce
-- driver's THIRD event, and it exists for §2b‴'s reason: `CSsApiRowP`'s FIXITY arm is
-- the case §6h's field 1 must exclude across `pp2 → pp3` (a server that did NOT move
-- is still at `csWar` or `csMust`, neither of which is in the `pp3` region), and only
-- the bundle knows which peer fired.
--
-- The conclusion is again the LANDING and not the row, and the table reading is again
-- kept at the per-key pin (`LiveCSRow.cssRfwLands`).  Like §2b″/§2b‴ it needs NO
-- source-position antecedent — but for a DIFFERENT reason, and this is the one place
-- the family differs: the tag has TWO rows (`csCanAwait` and `csMust`) rather than
-- one, and they agree because both land at `csWrf` of the FIRED VALUE.  So the
-- conclusion is EXISTENTIAL in the `Header × Tip` pair: the pin names the value, but
-- the landed form is stated at a generic label where the value is not in scope.
------------------------------------------------------------------------

-- the CS SERVER's fired row at its OWN key, in `sendCSRollForward`-landed form
CssRfwLand : (l : Link) (sv : Dir) (css css′ : CSsPos) {X : Set 0ℓ}
             (e : Net_Api Payload X) (a : X) → Set
CssRfwLand l sv css css′ e a =
  -- the Σ domain is spelled `ApiCSCar sendCSRollForward` rather than `Header × Tip`
  -- (which they definitionally are, `Net.agda:119`) because this module imports
  -- neither name — the tag's own carrier is always in scope
  CsfwAt l sv e a → Σ[ ht ∈ ApiCSCar sendCSRollForward ] coarsenCSs css′ ≡ NS.csWrf ht

-- the FIRED server's answer: the pin identifies the tag AND the key, and the per-key
-- pin reads the landing off the row.  The tag dispatch is unavoidable for §2b′'s
-- reason — `CsfwData` matches the tag as a CONSTRUCTOR.
cssRfwLand-of : (l : Link) (sv : Dir) (l₀ : Link) (d₀ : Dir) (m : ApiCSTag)
                (a : ApiCSCar m) (css css′ : CSsPos)
              → CSsRow l sv (apiCS l₀ d₀ m) a css css′
              → CssRfwLand l sv css css′ (apiCS l₀ d₀ m) a
cssRfwLand-of l sv l₀ d₀ sendCSRequestNext a css css′ row p = ⊥-elim (nothing-absurd p)
cssRfwLand-of l sv l₀ d₀ sendCSFindIntersect a css css′ row p = ⊥-elim (nothing-absurd p)
cssRfwLand-of l sv l₀ d₀ sendCSDone a css css′ row p = ⊥-elim (nothing-absurd p)
cssRfwLand-of l sv l₀ d₀ sendCSAwaitReply a css css′ row p = ⊥-elim (nothing-absurd p)
cssRfwLand-of l sv l₀ d₀ sendCSRollBackward a css css′ row p = ⊥-elim (nothing-absurd p)
cssRfwLand-of l sv l₀ d₀ sendCSIntersectFound a css css′ row p = ⊥-elim (nothing-absurd p)
cssRfwLand-of l sv l₀ d₀ sendCSIntersectNotFound a css css′ row p = ⊥-elim (nothing-absurd p)
cssRfwLand-of l sv l₀ d₀ recvCSRollforward a css css′ row p = ⊥-elim (nothing-absurd p)
cssRfwLand-of l sv l₀ d₀ recvCSRollback a css css′ row p = ⊥-elim (nothing-absurd p)
cssRfwLand-of l sv l₀ d₀ recvCSIntersectFound a css css′ row p = ⊥-elim (nothing-absurd p)
cssRfwLand-of l sv l₀ d₀ recvCSIntersectNotFound a css css′ row p = ⊥-elim (nothing-absurd p)
cssRfwLand-of l sv l₀ d₀ reqCSRequestNext a css css′ row p = ⊥-elim (nothing-absurd p)
cssRfwLand-of l sv l₀ d₀ reqCSFindIntersect a css css′ row p = ⊥-elim (nothing-absurd p)
cssRfwLand-of l sv l₀ d₀ sendCSRollForward a css css′ row p
  with just-injective p
... | refl = a , cssRfwLands l sv (coarsenCSs css) a (coarsenCSs css′) row

-- … and the answer when the CS CLIENT is the firing peer: §2b″'s argument at the
-- fourth tag — its own row carries `d₀ ≡ cl` (recovered by `LiveCSRow.cscRow-key`)
-- while the pin says `d₀ ≡ sv`, so `cl ≢ sv` refutes that case outright
cssRfwLand-cli : (l : Link) (cl sv : Dir) → cl ≢ sv
               → (l₀ : Link) (d₀ : Dir) (m : ApiCSTag) (a : ApiCSCar m)
                 (csc csc′ : CScPos) (css : CSsPos)
               → CScRow l cl (apiCS l₀ d₀ m) a csc csc′
               → CssRfwLand l sv css css (apiCS l₀ d₀ m) a
cssRfwLand-cli l cl sv ne l₀ d₀ sendCSRequestNext a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssRfwLand-cli l cl sv ne l₀ d₀ sendCSFindIntersect a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssRfwLand-cli l cl sv ne l₀ d₀ sendCSDone a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssRfwLand-cli l cl sv ne l₀ d₀ sendCSAwaitReply a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssRfwLand-cli l cl sv ne l₀ d₀ sendCSRollBackward a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssRfwLand-cli l cl sv ne l₀ d₀ sendCSIntersectFound a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssRfwLand-cli l cl sv ne l₀ d₀ sendCSIntersectNotFound a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssRfwLand-cli l cl sv ne l₀ d₀ recvCSRollforward a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssRfwLand-cli l cl sv ne l₀ d₀ recvCSRollback a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssRfwLand-cli l cl sv ne l₀ d₀ recvCSIntersectFound a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssRfwLand-cli l cl sv ne l₀ d₀ recvCSIntersectNotFound a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssRfwLand-cli l cl sv ne l₀ d₀ reqCSRequestNext a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssRfwLand-cli l cl sv ne l₀ d₀ reqCSFindIntersect a csc csc′ css row p = ⊥-elim (nothing-absurd p)
cssRfwLand-cli l cl sv ne l₀ d₀ sendCSRollForward a csc csc′ css row p
  with just-injective p
... | refl =
      ⊥-elim (ne (sym (proj₂ (cscRow-key l cl (coarsenCSc csc)
                                (CS.apiCSev l sv sendCSRollForward) row))))

------------------------------------------------------------------------
-- §2b⁷  *** (T11d) THE BF CLIENT'S `sendBFRequestRange` LANDING — `CliRecvLand`'s
-- twin one tag over, and the ONE bundle fact node D's BlockFetch api class cannot
-- do without. ***
--
-- *** WHY IT EXISTS, and it is `LiveDrvBFD` §0(6)'s own hazard. ***  `bfFresh-cliApi`'s
-- `cp2 → cp3` arm needs the successor client inside `PhCli cp3` = `CliPostBF`, which
-- excludes `bcIdle` where the record's own client region `CliFreshBF` ADMITS it.  So
-- on `CliApiRowP`'s FIXITY arm the successor state is `(cp3 , bcIdle)` — unreachable,
-- because node D's driver fired `sendBFRequestRange` and its own client had to
-- co-fire, but not EXCLUDED by anything hop-local.  *** Only the bundle knows which
-- peer fired, so the sharpening has to be produced here. ***  (T11d checked and closed
-- three alternatives: weakening `PhCli cp3` is FALSE by T9 §4 — `(bsIdle , empty ,
-- bcIdle)` IS `chanInv-init`, so the exclusion is necessarily LEG-level; the cell's
-- own correlation is antecedent-`bcBusy`; and the token constrains node D's PHASE,
-- not its BF client.)
--
-- THE CONCLUSION IS THE EDGE — both endpoints — and not just the target, because
-- `BFCliDrvAdj`'s `dbReq` constructor FIXES its source at `bcIdle`.  `cscReqEdge`'s
-- shape on the BlockFetch axis, and the table reading is kept HERE in `bfcReqEdge`
-- rather than in the consumer.
------------------------------------------------------------------------

-- *** THE PER-KEY EDGE PIN. ***  `bfCnxt`'s ONLY `sendBFRequestRange` row is at
-- `bcIdle` and lands at `bcWrr` of the FIRED RANGE (`NodeSpecs:519-521`), so a fired
-- row at the client's own key names BOTH endpoints.  Total on `BFcPos` (seven
-- clauses, no catch-all) for §4b's reason: an omitted position would make a real row
-- vacuous
bfcReqEdge : (l : Link) (d : Dir) (q : NS.BFcPos) (v : ApiBFCar sendBFRequestRange)
             (q′ : NS.BFcPos)
           → NS.bfCnxt l d q (ApiBFCar sendBFRequestRange
                             , apiBF l d sendBFRequestRange) v
             ≡ just q′
           → (q ≡ NS.bcIdle) × (q′ ≡ NS.bcWrr v)
bfcReqEdge l d (NS.bcWrr r)  v q′ eq = ⊥-elim (nothing-absurd eq)
bfcReqEdge l d NS.bcBusy     v q′ eq = ⊥-elim (nothing-absurd eq)
bfcReqEdge l d NS.bcWcd      v q′ eq = ⊥-elim (nothing-absurd eq)
bfcReqEdge l d NS.bcStream   v q′ eq = ⊥-elim (nothing-absurd eq)
bfcReqEdge l d (NS.bcAblk b) v q′ eq = ⊥-elim (nothing-absurd eq)
bfcReqEdge l d NS.bcTerm     v q′ eq = ⊥-elim (nothing-absurd eq)
bfcReqEdge l d NS.bcIdle     v q′ eq with l ≟ l | d ≟ d
... | no ¬p    | _        = ⊥-elim (¬p refl)
... | yes refl | no ¬q    = ⊥-elim (¬q refl)
... | yes refl | yes refl = refl , sym (just-injective eq)

-- the LANDED form: a `sendBFRequestRange` at the client's own key runs `bcIdle` to
-- `bcWrr r`
CliReqLand : (l : Link) (cl : Dir) (bfc bfc′ : BFcPos) {X : Set 0ℓ}
             (e : Net_Api Payload X) (a : X) → Set
CliReqLand l cl bfc bfc′ e a =
  (r : ChainRange) → BrrAt l cl r e a
  → (coarsenBFc bfc ≡ NS.bcIdle) × (coarsenBFc bfc′ ≡ NS.bcWrr r)

-- the FIRED client's answer: the pin identifies the tag, the key AND the range, and
-- the per-key pin reads the edge off the row
cliReqLand-of : (l : Link) (cl : Dir) (l₀ : Link) (d₀ : Dir) (m : ApiBFTag)
                (a : ApiBFCar m) (bfc bfc′ : BFcPos)
              → CliApiRow l cl l₀ d₀ bfc bfc′ m a
              → CliReqLand l cl bfc bfc′ (apiBF l₀ d₀ m) a
cliReqLand-of l cl l₀ d₀ sendBFClientDone a bfc bfc′ row r rb = ⊥-elim (nothing-absurd rb)
cliReqLand-of l cl l₀ d₀ sendBFNoBlocks   a bfc bfc′ row r rb = ⊥-elim (nothing-absurd rb)
cliReqLand-of l cl l₀ d₀ sendBFBlock      a bfc bfc′ row r rb = ⊥-elim (nothing-absurd rb)
cliReqLand-of l cl l₀ d₀ sendBFStartBatch a bfc bfc′ row r rb = ⊥-elim (nothing-absurd rb)
cliReqLand-of l cl l₀ d₀ sendBFBatchDone  a bfc bfc′ row r rb = ⊥-elim (nothing-absurd rb)
cliReqLand-of l cl l₀ d₀ reqBFRange       a bfc bfc′ row r rb = ⊥-elim (nothing-absurd rb)
cliReqLand-of l cl l₀ d₀ recvBFBlock      a bfc bfc′ row r rb = ⊥-elim (nothing-absurd rb)
cliReqLand-of l cl l₀ d₀ sendBFRequestRange a bfc bfc′ (refl , refl , eq) r rb
  with just-injective rb
... | refl = bfcReqEdge l cl (coarsenBFc bfc) a (coarsenBFc bfc′) eq

-- no `bfSnxt` row answers a `sendBFRequestRange` at ANY position — the tag falls to
-- the server table's catch-all, and the catch-all only fires once the POSITION is a
-- constructor, so this is `rbbSrv-⊥`'s ten-clause dispatch and not a `()`
brrSrv-⊥ : ∀ {a} (l : Link) (d : Dir) (q q′ : NS.BFsPos)
         → NS.bfSnxt l d q (ApiBFCar sendBFRequestRange
                           , apiBF l d sendBFRequestRange) a ≡ just q′
         → ⊥
brrSrv-⊥ l d NS.bsIdle      q′ ()
brrSrv-⊥ l d (NS.bsAreq r)  q′ ()
brrSrv-⊥ l d NS.bsBusy      q′ ()
brrSrv-⊥ l d NS.bsDdone     q′ ()
brrSrv-⊥ l d NS.bsWsb       q′ ()
brrSrv-⊥ l d NS.bsStream    q′ ()
brrSrv-⊥ l d NS.bsWnb       q′ ()
brrSrv-⊥ l d (NS.bsWblk b)  q′ ()
brrSrv-⊥ l d NS.bsWbd       q′ ()
brrSrv-⊥ l d NS.bsTerm      q′ ()

-- … and the answer when the SERVER is the firing peer: its own row's equation is the
-- one `brrSrv-⊥` refutes, so the case is closed outright.  *** THIS CLAUSE IS WHY THE
-- SHARPENING IS TRUE: *** the BF server has no `sendBFRequestRange` row at all, so a
-- bundle that fired one moved its CLIENT
cliReqLand-srv : (l : Link) (cl sv : Dir)
                 (l₀ : Link) (d₀ : Dir) (m : ApiBFTag) (a : ApiBFCar m)
                 (bfc : BFcPos) (bfs bfs′ : BFsPos)
               → SrvApiRow l sv l₀ d₀ bfs bfs′ m a
               → CliReqLand l cl bfc bfc (apiBF l₀ d₀ m) a
cliReqLand-srv l cl sv l₀ d₀ sendBFClientDone a bfc bfs bfs′ row r rb = ⊥-elim (nothing-absurd rb)
cliReqLand-srv l cl sv l₀ d₀ sendBFNoBlocks   a bfc bfs bfs′ row r rb = ⊥-elim (nothing-absurd rb)
cliReqLand-srv l cl sv l₀ d₀ sendBFBlock      a bfc bfs bfs′ row r rb = ⊥-elim (nothing-absurd rb)
cliReqLand-srv l cl sv l₀ d₀ sendBFStartBatch a bfc bfs bfs′ row r rb = ⊥-elim (nothing-absurd rb)
cliReqLand-srv l cl sv l₀ d₀ sendBFBatchDone  a bfc bfs bfs′ row r rb = ⊥-elim (nothing-absurd rb)
cliReqLand-srv l cl sv l₀ d₀ reqBFRange       a bfc bfs bfs′ row r rb = ⊥-elim (nothing-absurd rb)
cliReqLand-srv l cl sv l₀ d₀ recvBFBlock      a bfc bfs bfs′ row r rb = ⊥-elim (nothing-absurd rb)
cliReqLand-srv l cl sv l₀ d₀ sendBFRequestRange a bfc bfs bfs′ (refl , refl , eq) r rb =
  ⊥-elim (brrSrv-⊥ l sv (coarsenBFs bfs) (coarsenBFs bfs′) eq)

------------------------------------------------------------------------
-- §2b⁗  *** (T7) THE CS CLIENT'S `recvCSRollforward` LANDING — §2b‴ WITH THE
-- POLARITY SWAPPED. ***
--
-- The `cp5` chain's entering step is the relay's own `cp1 → cp2` hop, and its peer is
-- the leg's UP-hop CS CLIENT, not a server.  So this is §2b‴'s block with the two peers
-- exchanged: the working clause is the one where the CLIENT fired (`-cli`, using T5's
-- per-key pin `LiveCSRow.cscRfwLands`), and the one that REFUTES is the one where the
-- SERVER fired (`-srv`, by `cl ≢ sv` off `LiveCSRow.cssRow-key`).  In §2b″/§2b‴ those
-- roles are the other way round, and the suffixes are named after the FIRING peer in
-- both — so `-cli` is the real one here and the vacuous one there.  *** A sync sweep
-- that assumes `-of` is always the working clause will read this block backwards. ***
--
-- The conclusion is again the LANDING and not the row, and the table reading is again
-- kept at the per-key pin — `csCnxt`'s only `recvCSRollforward` row is
-- `ccArf ht → ccIdle` (`NodeSpecs:361-365`), so a fire at the client's own key lands at
-- `ccIdle` whatever the source position and whatever the payload was.  Like §2b″/§2b‴
-- and unlike `SrvSbLand` it needs NO source-position antecedent; unlike all three it
-- also needs no value antecedent, because the pin quantifies the value (§1c⁗ (i)).
--
-- *** WHY THE FIXITY ARM MUST BE EXCLUDED HERE TOO. ***  `CScApiRowP`'s fixity arm is
-- what the bundle reports when a DIFFERENT peer of the same bundle fired, and a client
-- that did not move cannot be at `ccIdle` for any reason the `cp2` arm holds.  Only the
-- bundle knows which peer fired, so the fact has to be assembled there.
--
-- *** FALSIFICATION F46 (T7) — THE TAG AND ITS CARRIER PAIRING ARE LOAD-BEARING, AND
-- THIS IS THE MUTATION THAT SAYS SO. ***  Move `cscRfLand-cli`'s WORKING clause from
-- `recvCSRollforward` to `recvCSRollback` and give `recvCSRollforward` the vacuous body
-- instead — arity-preserving, both tags in scope, and the mutation an author would
-- actually make, because `csCnxt`'s `ccArb pt` row lands at `ccIdle` TOO
-- (`NodeSpecs:366-370`) so the sibling tag looks interchangeable.
-- *** RED ***: `:1322.86-87: [UnequalTerms] (just (l₀ , d₀)) != nothing of type (Maybe
-- (Link × Dir)) … when checking that the expression p has type nothing ≡ just _x`,
-- EXIT=42 — *** the mutant reported `:1322`, before this header's own prose grew ABOVE
-- the clause list it describes (the mutated clause now sits ~23 lines later); the COLUMN
-- (86, the position of `p` in a 14-clause list of uniform LHS length) is exact, and F12
-- declares the same drift in its own text at `LiveRelayCS` §7. ***
-- So the two tags are NOT interchangeable: `CsfData` pins `recvCSRollforward`,
-- so the vacuous body is unavailable there, and the working body is unavailable at
-- `recvCSRollback` because its own row is a `Point × Tip` one that `cscRfwLands` does not
-- state.  *** The `Header × Tip` carrier travels with the TAG, not with the landing
-- position — which is exactly the "value gate" the T6d calibration flagged, machine-
-- checked here rather than argued. ***  (And it is why the other three `recvCS*` keys are
-- deliberately NOT built: `LiveCSRow` §4b's own note gives the reachability reason, and
-- this falsification gives the type-level one for why a fourth copy would be needed
-- rather than a re-use.)
------------------------------------------------------------------------

-- the CS CLIENT's fired row at its OWN key, in `recvCSRollforward`-landed form
CscRfLand : (l : Link) (cl : Dir) (csc csc′ : CScPos) {X : Set 0ℓ}
            (e : Net_Api Payload X) (a : X) → Set
CscRfLand l cl csc csc′ e a = CsfAt l cl e a → coarsenCSc csc′ ≡ NS.ccIdle

-- the FIRED CLIENT's answer — *** THIS is the working clause of the block. ***  The pin
-- identifies the tag AND the key, and T5's per-key pin reads the landing off the row
-- (its own `v ≟ ht` gate is what makes the `Header × Tip` carrier free here).  The tag
-- dispatch is unavoidable for §2b′'s reason — `CsfData` matches the tag as a CONSTRUCTOR.
cscRfLand-cli : (l : Link) (cl : Dir) (l₀ : Link) (d₀ : Dir) (m : ApiCSTag)
                (a : ApiCSCar m) (csc csc′ : CScPos)
              → CScRow l cl (apiCS l₀ d₀ m) a csc csc′
              → CscRfLand l cl csc csc′ (apiCS l₀ d₀ m) a
cscRfLand-cli l cl l₀ d₀ sendCSRequestNext a csc csc′ row p = ⊥-elim (nothing-absurd p)
cscRfLand-cli l cl l₀ d₀ sendCSFindIntersect a csc csc′ row p = ⊥-elim (nothing-absurd p)
cscRfLand-cli l cl l₀ d₀ sendCSDone a csc csc′ row p = ⊥-elim (nothing-absurd p)
cscRfLand-cli l cl l₀ d₀ sendCSAwaitReply a csc csc′ row p = ⊥-elim (nothing-absurd p)
cscRfLand-cli l cl l₀ d₀ sendCSRollForward a csc csc′ row p = ⊥-elim (nothing-absurd p)
cscRfLand-cli l cl l₀ d₀ sendCSRollBackward a csc csc′ row p = ⊥-elim (nothing-absurd p)
cscRfLand-cli l cl l₀ d₀ sendCSIntersectFound a csc csc′ row p = ⊥-elim (nothing-absurd p)
cscRfLand-cli l cl l₀ d₀ sendCSIntersectNotFound a csc csc′ row p = ⊥-elim (nothing-absurd p)
cscRfLand-cli l cl l₀ d₀ recvCSRollback a csc csc′ row p = ⊥-elim (nothing-absurd p)
cscRfLand-cli l cl l₀ d₀ recvCSIntersectFound a csc csc′ row p = ⊥-elim (nothing-absurd p)
cscRfLand-cli l cl l₀ d₀ recvCSIntersectNotFound a csc csc′ row p = ⊥-elim (nothing-absurd p)
cscRfLand-cli l cl l₀ d₀ reqCSRequestNext a csc csc′ row p = ⊥-elim (nothing-absurd p)
cscRfLand-cli l cl l₀ d₀ reqCSFindIntersect a csc csc′ row p = ⊥-elim (nothing-absurd p)
cscRfLand-cli l cl l₀ d₀ recvCSRollforward a csc csc′ row p
  with just-injective p
... | refl = cscRfwLands l cl (coarsenCSc csc) a (coarsenCSc csc′) row

-- … and the answer when the CS SERVER is the firing peer: §2b″'s argument with the two
-- peers exchanged — the server's own row carries `d₀ ≡ sv` (recovered by
-- `LiveCSRow.cssRow-key`) while the pin says `d₀ ≡ cl`, so `cl ≢ sv` refutes that case
-- outright and the CLIENT slot is untouched
cscRfLand-srv : (l : Link) (cl sv : Dir) → cl ≢ sv
              → (l₀ : Link) (d₀ : Dir) (m : ApiCSTag) (a : ApiCSCar m)
                (csc : CScPos) (css css′ : CSsPos)
              → CSsRow l sv (apiCS l₀ d₀ m) a css css′
              → CscRfLand l cl csc csc (apiCS l₀ d₀ m) a
cscRfLand-srv l cl sv ne l₀ d₀ sendCSRequestNext a csc css css′ row p = ⊥-elim (nothing-absurd p)
cscRfLand-srv l cl sv ne l₀ d₀ sendCSFindIntersect a csc css css′ row p = ⊥-elim (nothing-absurd p)
cscRfLand-srv l cl sv ne l₀ d₀ sendCSDone a csc css css′ row p = ⊥-elim (nothing-absurd p)
cscRfLand-srv l cl sv ne l₀ d₀ sendCSAwaitReply a csc css css′ row p = ⊥-elim (nothing-absurd p)
cscRfLand-srv l cl sv ne l₀ d₀ sendCSRollForward a csc css css′ row p = ⊥-elim (nothing-absurd p)
cscRfLand-srv l cl sv ne l₀ d₀ sendCSRollBackward a csc css css′ row p = ⊥-elim (nothing-absurd p)
cscRfLand-srv l cl sv ne l₀ d₀ sendCSIntersectFound a csc css css′ row p = ⊥-elim (nothing-absurd p)
cscRfLand-srv l cl sv ne l₀ d₀ sendCSIntersectNotFound a csc css css′ row p = ⊥-elim (nothing-absurd p)
cscRfLand-srv l cl sv ne l₀ d₀ recvCSRollback a csc css css′ row p = ⊥-elim (nothing-absurd p)
cscRfLand-srv l cl sv ne l₀ d₀ recvCSIntersectFound a csc css css′ row p = ⊥-elim (nothing-absurd p)
cscRfLand-srv l cl sv ne l₀ d₀ recvCSIntersectNotFound a csc css css′ row p = ⊥-elim (nothing-absurd p)
cscRfLand-srv l cl sv ne l₀ d₀ reqCSRequestNext a csc css css′ row p = ⊥-elim (nothing-absurd p)
cscRfLand-srv l cl sv ne l₀ d₀ reqCSFindIntersect a csc css css′ row p = ⊥-elim (nothing-absurd p)
cscRfLand-srv l cl sv ne l₀ d₀ recvCSRollforward a csc css css′ row p
  with just-injective p
... | refl =
      ⊥-elim (ne (proj₂ (cssRow-key l sv (coarsenCSs css)
                          (CS.apiCSev l cl recvCSRollforward) row)))

-- … and conversely (this is the direction the frozen decode supplies)
bfsSucc⇒srvSuccA : (l : Link) (d : Dir) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
                   (q : BFsPos) → BfsSucc l d q e a → SrvSuccA l d e a q
bfsSucc⇒srvSuccA l d q (inj₁ nb) = inj₁ nb
bfsSucc⇒srvSuccA l d {e = e} {a} q (inj₂ (b″ , lbl , eq)) =
  inj₂ (b″ , pin⇒sbbAt l d b″ e a lbl , eq)

------------------------------------------------------------------------
-- §2b⁵  *** (T8c-ii) THE CS CLIENT FIRED — THE SHARPENING, AND THE ONLY BLOCK OF
-- THIS FAMILY WHOSE CONCLUSION IS THE ROW ITSELF RATHER THAN A LANDING. ***
--
-- *** WHAT IT IS FOR. ***  `BundleApiEvo`'s CS-client slot (§4's fifteenth
-- component, `CScApiRowP`) is a DISJUNCTION — fixity or a genuine row — and its
-- fixity arm is what the bundle reports when a DIFFERENT peer of the same bundle
-- fired.  `LiveDrvCSD`'s joint node-D adjacency `CliDrvAdj` cannot be produced at
-- ONE combination, `(ConsAdv cp0 cp1 , that fixity arm)`: node D's driver fires
-- `sendCSRequestNext` and its own client at `ccIdle` MUST co-fire, but "the client
-- co-fired" is a BUNDLE-level fact and neither the fired label nor the driver's step
-- supplies it.  This block supplies it: at an `apiCS` label ON THE CLIENT'S OWN KEY
-- the client's fact is the genuine ROW, full stop.
--
-- *** WHY IT IS TRUE, AND WHERE THE ARGUMENT COMES FROM. ***  `absBundleCS-ev-prod⁺`
-- has exactly TWO arms and the client's component is a genuine row in the first
-- (`bcscEB⁺`, the client fired) and `inj₁ refl` in the second (`bcssEB⁺`, the SERVER
-- fired).  So the fixity arm is inhabited EXACTLY when the server fired — and a
-- server's own row carries `d₀ ≡ sv` (`LiveCSRow.cssRow-key`) while the pin below
-- says `d₀ ≡ cl`, so `cl ≢ sv` refutes it outright.  *** That is verbatim the
-- argument §2b⁗'s `cscRfLand-srv` runs, at the same polarity: the CLIENT-fired arm
-- is the working one and the SERVER-fired arm is the vacuous one. ***
--
-- *** WHY THE PIN IS TAG-GENERIC (and this is what makes the block ~20 lines and
-- not ~200). ***  §1c…§1c⁗'s four decoders each pin ONE tag, because their
-- conclusions are per-tag LANDINGS read off a per-key pin.  This block's conclusion
-- is the row itself, which `LiveCSRow.CScRow` states EVENT-GENERICALLY — so the
-- decoder matches the tag as a WILDCARD (§1d's `BfKey` idiom, one channel over) and
-- neither producer needs a tag dispatch at all.  *** Do not "complete" this block
-- with a fourteen-clause per-tag list: there is nothing per-tag in it. ***
--
-- *** AND NO `ApiHasLink` OUT MAP IS BUILT — deliberately. ***  §1c⁗ has one because
-- its consumer must refute a SIBLING LINK; this block's consumers never do, because
-- the threading carries it in the standing FIXITY-OR-FIRED shape and every non-firing
-- leg and non-firing node answers with the fixity half (`LiveLegApiExpose`'s
-- `deCsCliFired*`).  A `csAt⇒ahl` here would be dead weight — §1d's own note, at the
-- other channel.
------------------------------------------------------------------------

-- the Event-level decoder of ANY `apiCS` observation: its key.  The TAG is a
-- WILDCARD — the second tag-generic decoder in the file, and §1d's note says why
-- that is sound for a consumer that only needs the KEY
CsKey : Event → Maybe (Link × Dir)
CsKey (evLabel _ (apiCS l₀ d₀ _) x) = just (l₀ , d₀)
CsKey _                             = nothing

-- "the fired observation is SOME `apiCS l d _`", `Set`-valued
CsAt : (l : Link) (d : Dir) {X : Set 0ℓ} → Net_Api Payload X → X → Set
CsAt l d {X} e a = CsKey (evLabel X e a) ≡ just (l , d)

-- the CS CLIENT's GENUINE fired row at its own key, as an implication off the pin.
-- At any label that is not an `apiCS` at `(l , cl)` the pin is `nothing ≡ just _`
-- and the fact is vacuous, so this ONE definition serves all twenty-eight labels
CscCliFired : (l : Link) (cl : Dir) (csc csc′ : CScPos) {X : Set 0ℓ}
              (e : Net_Api Payload X) (a : X) → Set
CscCliFired l cl csc csc′ e a = CsAt l cl e a → CScRow l cl e a csc csc′

-- the FIRED CLIENT's answer — *** THIS is the working clause. ***  The row it
-- already carries IS the conclusion, so the pin is discarded and no table is read
cscCliFired-cli : (l : Link) (cl : Dir) (l₀ : Link) (d₀ : Dir) (m : ApiCSTag)
                  (a : ApiCSCar m) (csc csc′ : CScPos)
                → CScRow l cl (apiCS l₀ d₀ m) a csc csc′
                → CscCliFired l cl csc csc′ (apiCS l₀ d₀ m) a
cscCliFired-cli l cl l₀ d₀ m a csc csc′ row _ = row

-- … and the answer when the CS SERVER is the firing peer: the DIRECTION CLASH.  The
-- server's own row carries `d₀ ≡ sv` and the pin says `d₀ ≡ cl`, so `cl ≢ sv` closes
-- it — and the client slot is untouched, which is why the two position arguments of
-- the conclusion are the SAME `csc`
cscCliFired-srv : (l : Link) (cl sv : Dir) → cl ≢ sv
                → (l₀ : Link) (d₀ : Dir) (m : ApiCSTag) (a : ApiCSCar m)
                  (csc : CScPos) (css css′ : CSsPos)
                → CSsRow l sv (apiCS l₀ d₀ m) a css css′
                → CscCliFired l cl csc csc (apiCS l₀ d₀ m) a
cscCliFired-srv l cl sv ne l₀ d₀ m a csc css css′ row p
  with just-injective p
... | refl =
      ⊥-elim (ne (proj₂ (cssRow-key l sv (coarsenCSs css)
                          (CS.apiCSev l cl m) row)))

------------------------------------------------------------------------
-- §3  THE FOUR DECODE PACKAGES, at the ⁺ facts.
--
-- The two ¬-block PREDECESSOR dispatches are one line per position: only
-- `bsBlk1` has a non-trivial case, and there the FROZEN table refutation applies
-- unchanged (a holding server offers no api at all).  The client's "this was no
-- `sendBFBlock`" is the same shape at the `sendBFBlock` TAG (no BF-client
-- position has such a row), and free at the other seven tags where `IsSBB`
-- already reduces to `⊥`.  The producer-site `SrvLands` needs the fired slot's
-- own decode at the `sendBFBlock` tag, which is `ksSbb`: the two STREAMING heads
-- fire (bodies re-derived from `decBFs-apiBF-succ⁺`'s own two clauses) and the
-- other twelve positions refute.
------------------------------------------------------------------------

-- a HOLDING BF server has NO api row (`bsBlk1` offers only the io wire WRITE),
-- so a server slot that fired an api was not holding — leaf 6's whole content
decBFs-apiBF-nb : (l : Link) (d : Dir) (bfs : BFsPos)
    {l′ : Link} {d′ : Dir} {m : ApiBFTag} {a : ApiBFCar m} {M : NetProc}
  → absBFs l d bfs ─[ ev (evl (evLabel (ApiBFCar m) (ιBF (BF.apiBFev l′ d′ m)) a)) ]─► M
  → BFsHasBlk bfs → ⊥
decBFs-apiBF-nb l d (bsHead _)   step ()
decBFs-apiBF-nb l d (bsSil _)    step ()
decBFs-apiBF-nb l d (bsReq1 _)   step ()
decBFs-apiBF-nb l d bsDone1      step ()
decBFs-apiBF-nb l d bsStart1     step ()
decBFs-apiBF-nb l d bsNoBlk1     step ()
decBFs-apiBF-nb l d bsBatchDone1 step ()
decBFs-apiBF-nb l d (bsBlk1 b)   step _
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- the same for the `doneBF` channel
decBFs-doneBF-nb : (l : Link) (d : Dir) (bfs : BFsPos)
    {l′ : Link} {d′ : Dir} {a : _} {M : NetProc}
  → absBFs l d bfs ─[ ev (evl (evLabel _ (ιBF (BF.doneBF l′ d′)) a)) ]─► M
  → BFsHasBlk bfs → ⊥
decBFs-doneBF-nb l d (bsHead _)   step ()
decBFs-doneBF-nb l d (bsSil _)    step ()
decBFs-doneBF-nb l d (bsReq1 _)   step ()
decBFs-doneBF-nb l d bsDone1      step ()
decBFs-doneBF-nb l d bsStart1     step ()
decBFs-doneBF-nb l d bsNoBlk1     step ()
decBFs-doneBF-nb l d bsBatchDone1 step ()
decBFs-doneBF-nb l d (bsBlk1 b)   step _
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- NO BF CLIENT POSITION HAS A `sendBFBlock` ROW — this is what refutes the
-- server-FIXED arm at the producer's own hop (leaves 7 and 9)
decBFc-apiBF-notSbb : (l : Link) (d : Dir) (bfc : BFcPos)
    {l′ : Link} {d′ : Dir} {m : ApiBFTag} {a : ApiBFCar m} {M : NetProc}
  → absBFc l d bfc ─[ ev (evl (evLabel (ApiBFCar m) (ιBF (BF.apiBFev l′ d′ m)) a)) ]─► M
  → IsSBB (evLabel (ApiBFCar m) (ιBF (BF.apiBFev l′ d′ m)) a) → ⊥
decBFc-apiBF-notSbb l d bfc {m = sendBFRequestRange} step ()
decBFc-apiBF-notSbb l d bfc {m = sendBFClientDone}   step ()
decBFc-apiBF-notSbb l d bfc {m = sendBFStartBatch}   step ()
decBFc-apiBF-notSbb l d bfc {m = sendBFNoBlocks}     step ()
decBFc-apiBF-notSbb l d bfc {m = sendBFBatchDone}    step ()
decBFc-apiBF-notSbb l d bfc {m = recvBFBlock}        step ()
decBFc-apiBF-notSbb l d bfc {m = reqBFRange}         step ()
decBFc-apiBF-notSbb l d (bcHead BF.stIdle) {m = sendBFBlock} step _
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-notSbb l d (bcHead BF.stBusy) {m = sendBFBlock} step _
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-notSbb l d (bcHead BF.stStreaming) {m = sendBFBlock} step _
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-notSbb l d (bcHead BF.stDone) {m = sendBFBlock} step _
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-notSbb l d (bcSil BF.stIdle) {m = sendBFBlock} step _
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-notSbb l d (bcSil BF.stBusy) {m = sendBFBlock} step _
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-notSbb l d (bcSil BF.stStreaming) {m = sendBFBlock} step _
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-notSbb l d (bcSil BF.stDone) {m = sendBFBlock} step _
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-notSbb l d (bcReq1 r) {m = sendBFBlock} step _
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-notSbb l d bcDone1 {m = sendBFBlock} step _
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc bcDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-notSbb l d (bcBlk1 b) {m = sendBFBlock} step _
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- the SERVER decode at the `sendBFBlock` TAG, re-derived so the fired slot
-- reports `SrvLands`: the two STREAMING heads enter `bsBlk1` of the sent block,
-- every other position has no such row
ksSbb : (l : Link) (d : Dir) (bfs : BFsPos) {l′ : Link} {d′ : Dir} {a : Block}
      → BFsDecodeP l d bfs
          (λ z → SrvApiSf l d bfs (apiBF l′ d′ sendBFBlock) a z
                 × SrvApiRow l d l′ d′ bfs z sendBFBlock a)
          (BF.apiBFev l′ d′ sendBFBlock) a
ksSbb l d (bsHead BF.stStreaming) {l′} {d′} {a} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stStreaming)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl =
        bsBlk1 a
      , wev τ*-refl (SIL6.RFBF.renameMap-ev-fwd (bfs-fire-blk l d a)) τ*-refl
      , mkMbfs l d (bsBlk1 a) Meq (just-injective (sym ceq))
      , ((λ ()) , inj₂ (a , refl , refl) , (λ b″ sd → cong bsBlk1 (sbbAt-inj refl sd)))
      , (refl , refl , trans ceq (cong just (just-injective (sym ceq))))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _     | _    = ⊥-elim (nothing-absurd ceq)
ksSbb l d (bsSil BF.stStreaming) {l′} {d′} {a} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stStreaming)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl =
        bsBlk1 a
      , wev (τ*-step (decBFs-sil-step l d BF.stStreaming) τ*-refl)
            (SIL6.RFBF.renameMap-ev-fwd (bfs-fire-blk l d a)) τ*-refl
      , mkMbfs l d (bsBlk1 a) Meq (just-injective (sym ceq))
      , ((λ ()) , inj₂ (a , refl , refl) , (λ b″ sd → cong bsBlk1 (sbbAt-inj refl sd)))
      , (refl , refl , trans ceq (cong just (just-injective (sym ceq))))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _     | _    = ⊥-elim (nothing-absurd ceq)
ksSbb l d (bsHead BF.stIdle) step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ksSbb l d (bsHead BF.stBusy) step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ksSbb l d (bsHead BF.stDone) step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ksSbb l d (bsSil BF.stIdle) step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ksSbb l d (bsSil BF.stBusy) step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ksSbb l d (bsSil BF.stDone) step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ksSbb l d (bsReq1 r) step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ksSbb l d bsDone1 step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs bsDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ksSbb l d bsStart1 step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs bsStart1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ksSbb l d bsNoBlk1 step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs bsNoBlk1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ksSbb l d (bsBlk1 b) step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ksSbb l d bsBatchDone1 step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs bsBatchDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- the SERVER package on the api channel: `ksSbb` at the `sendBFBlock` tag, the
-- frozen decode plus the two free facts at the other seven
ksApi : (l : Link) (d : Dir) (bfs : BFsPos)
        {l′ : Link} {d′ : Dir} {m : ApiBFTag} {a : ApiBFCar m}
      → BFsDecodeP l d bfs
          (λ z → SrvApiSf l d bfs (apiBF l′ d′ m) a z × SrvApiRow l d l′ d′ bfs z m a)
          (BF.apiBFev l′ d′ m) a
ksApi l d bfs {m = sendBFBlock} step = ksSbb l d bfs step
ksApi l d bfs {m = sendBFRequestRange} step =
  let (bfs′ , run , Meq , bsucc , row) = decBFs-apiBF-succ-row⁺ l d bfs step
  in bfs′ , run , Meq
   , ((decBFs-apiBF-nb l d bfs step , bfsSucc⇒srvSuccA l d bfs′ bsucc , (λ b″ ()))
     , row)
ksApi l d bfs {m = sendBFClientDone} step =
  let (bfs′ , run , Meq , bsucc , row) = decBFs-apiBF-succ-row⁺ l d bfs step
  in bfs′ , run , Meq
   , ((decBFs-apiBF-nb l d bfs step , bfsSucc⇒srvSuccA l d bfs′ bsucc , (λ b″ ()))
     , row)
ksApi l d bfs {m = sendBFStartBatch} step =
  let (bfs′ , run , Meq , bsucc , row) = decBFs-apiBF-succ-row⁺ l d bfs step
  in bfs′ , run , Meq
   , ((decBFs-apiBF-nb l d bfs step , bfsSucc⇒srvSuccA l d bfs′ bsucc , (λ b″ ()))
     , row)
ksApi l d bfs {m = sendBFNoBlocks} step =
  let (bfs′ , run , Meq , bsucc , row) = decBFs-apiBF-succ-row⁺ l d bfs step
  in bfs′ , run , Meq
   , ((decBFs-apiBF-nb l d bfs step , bfsSucc⇒srvSuccA l d bfs′ bsucc , (λ b″ ()))
     , row)
ksApi l d bfs {m = sendBFBatchDone} step =
  let (bfs′ , run , Meq , bsucc , row) = decBFs-apiBF-succ-row⁺ l d bfs step
  in bfs′ , run , Meq
   , ((decBFs-apiBF-nb l d bfs step , bfsSucc⇒srvSuccA l d bfs′ bsucc , (λ b″ ()))
     , row)
ksApi l d bfs {m = recvBFBlock} step =
  let (bfs′ , run , Meq , bsucc , row) = decBFs-apiBF-succ-row⁺ l d bfs step
  in bfs′ , run , Meq
   , ((decBFs-apiBF-nb l d bfs step , bfsSucc⇒srvSuccA l d bfs′ bsucc , (λ b″ ()))
     , row)
ksApi l d bfs {m = reqBFRange} step =
  let (bfs′ , run , Meq , bsucc , row) = decBFs-apiBF-succ-row⁺ l d bfs step
  in bfs′ , run , Meq
   , ((decBFs-apiBF-nb l d bfs step , bfsSucc⇒srvSuccA l d bfs′ bsucc , (λ b″ ()))
     , row)

-- the SERVER package on the `doneBF` channel (`SrvLands` is vacuous: a `done`
-- observation is no `sendBFBlock`)
ksDone : (l : Link) (d : Dir) (bfs : BFsPos) {l′ : Link} {d′ : Dir} {a : _}
       → BFsDecodeP l d bfs
           (λ z → SrvApiSf l d bfs (done l′ d′ N2N_BlockFetch) a z
                  × SrvDoneRow l d l′ d′ bfs z a)
           (BF.doneBF l′ d′) a
ksDone l d bfs step =
  let (bfs′ , run , Meq , bsucc , row) = decBFs-doneBF-succ-row⁺ l d bfs step
  in bfs′ , run , Meq
   , ((decBFs-doneBF-nb l d bfs step , bfsSucc⇒srvSuccA l d bfs′ bsucc , (λ b″ ()))
     , row)

-- the CLIENT package on the api channel
kcApi : (l : Link) (d : Dir) (bfc : BFcPos)
        {l′ : Link} {d′ : Dir} {m : ApiBFTag} {a : ApiBFCar m}
      → BFcDecodeP l d bfc
          (λ z → CliApiCf (apiBF l′ d′ m) a z × CliApiRow l d l′ d′ bfc z m a)
          (BF.apiBFev l′ d′ m) a
kcApi l d bfc step =
  let (bfc′ , run , Meq , ¬blk , row) = decBFc-apiBF-succ-row⁺ l d bfc step
  in bfc′ , run , Meq
   , ((¬blk , decBFc-apiBF-notSbb l d bfc step) , row)

-- the CLIENT package on the `doneBF` channel: a BF client never offers `doneBF`
kcDone : (l : Link) (d : Dir) (bfc : BFcPos) {l′ : Link} {d′ : Dir} {a : _}
       → BFcDecodeP l d bfc
           (λ z → CliApiCf (done l′ d′ N2N_BlockFetch) a z × (bfc ≡ z))
           (BF.doneBF l′ d′) a
kcDone l d bfc step = ⊥-elim (decBFc-doneBF-absurd l d bfc step)

------------------------------------------------------------------------
-- §4  THE ⁺ api BUNDLE DISPATCHER — `PipeBundleEvo.absBundleG-api-evo`'s
-- twenty-seven clauses at the ⁺ facts, in Σ form (so no datatype has to be
-- declared beside `BundleGEvR⁺`).  The five non-BF channels keep BOTH BF slots
-- LITERAL, and their labels are no `sendBFBlock`, so the server arm is
-- `inj₁ (refl , λ ())`; the two BF clauses route the fired peer through §3.
------------------------------------------------------------------------

-- the api bundle inversion at the ⁺ per-peer facts
BundleApiEvo : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) (Bd′ : NetProc) → Set₁
BundleApiEvo l cl sv csc css bfc bfs ip {X} e a Bd′ =
  Σ[ csc′ ∈ CScPos ] Σ[ css′ ∈ CSsPos ] Σ[ bfc′ ∈ BFcPos ] Σ[ bfs′ ∈ BFsPos ]
  Σ[ ip′ ∈ InertPos ]
      (Bd′ ≡ absBundleG l cl sv csc′ css′ bfc′ bfs′ ip′)
    × (bundleG l cl sv csc css bfc bfs ip
         ═[ ev (evl (evLabel X e a)) ]═► bundleG l cl sv csc′ css′ bfc′ bfs′ ip′)
    × ((bfc ≡ bfc′) ⊎ (BFcHasBlk bfc′ → ⊥))
    × ((((bfs ≡ bfs′) × (IsSBB (evLabel X e a) → ⊥)))
       ⊎ ((BFsHasBlk bfs → ⊥) × SrvSuccA l sv e a bfs′ × SrvLands l sv e a bfs′))
    -- (P5) grant #6, TRAILING: the KA-client freeze is preserved.  Conditional on
    -- `IsApiCSBF` because the four inert-api labels DO move their own peer and are
    -- refuted one level up (`LiveLegAssembly:1027-1034`) rather than here — at
    -- `kcClient` the client's table really does have the two `apiKA` rows.
    × (IsApiCSBF e → KAcAtHead ip → KAcAtHead ip′)
    -- (grant #8) … and, TRAILING behind that, the two BF peers' fired ROWS — the
    -- `ChanLeg` join's visible arm reads its adjacency off exactly these
    × CliApiRowP l cl bfc bfc′ e a
    × SrvApiRowP l sv bfs bfs′ e a
    -- (T1 / S1) TRAILING behind those: the SERVER's GENUINE own-key row, in
    -- `reqBFRange`-pinned form (§2b′).  Strictly stronger than the `⊎` above at
    -- that one label, and it is the fact the BF driver-tail coupling's api arm
    -- needs: `⊎`'s fixity arm is exactly the case S1 must exclude, and only the
    -- bundle knows which peer fired.
    × SrvReqRow l sv bfs bfs′ e a
    -- (T2) TRAILING behind that: the SAME fact at the driver's OTHER server-facing
    -- tag, in landed form (§2b′'s `SrvSbLand`).  The `pp5` arm of the coupling reads
    -- its successor position off exactly this slot, and for the same reason the
    -- `reqBFRange` one exists: the `⊎`'s fixity arm is the case the arm must exclude.
    × SrvSbLand l sv bfs bfs′ e a
    -- (T4) TRAILING behind those, and APPENDED rather than inserted (an insertion
    -- before the BF twins would be exactly the type-DUPLICATING shift the T3b review
    -- named as this task's hazard): the two CS peers' api-axis adjacency facts.  At
    -- the two CS labels these are the rows the ⁺ CS bundle peel recovers; at every
    -- other label the CS peers are untouched and the fact degenerates to fixity.
    × CScApiRowP l cl csc csc′ e a
    × CSsApiRowP l sv css css′ e a
    -- (T5) TRAILING behind those, and appended for the same reason: the CS SERVER's
    -- own-key row in LANDED form (§2b″).  Strictly stronger than the `⊎` above at the
    -- ONE label `apiCS l sv reqCSRequestNext`, and it is the fact the CS driver-tail
    -- coupling's `pp1` arm needs — `⊎`'s fixity arm is exactly the case that arm must
    -- exclude, and only the bundle knows which peer fired.
    × CssReqLand l sv css css′ e a
    -- (T6d) TRAILING behind that, and appended for the same reason: the SAME fact at
    -- the produce driver's OTHER CS-server-facing tag, in landed form (§2b‴).  The
    -- `pp2` arm of the coupling reads the region's ENTRY off exactly this slot, and
    -- the `⊎`'s fixity arm is again the case that arm must exclude.
    × CssAwLand l sv css css′ e a
    -- (T7) TRAILING behind that, and appended for the same reason: the CS CLIENT's
    -- own-key row in landed form (§2b⁗) — the FIRST slot of this family on the client
    -- side, and the one the `cp5` chain's ENTERING step reads.  It is the ONLY new
    -- bundle component the `cp5` chain needs: its other three sub-phases fire `apiBF`
    -- labels, at which the CS client's existing row slot above already reduces to
    -- fixity (§1d's `bfAt⇒cscFix` does that reduction at the consumer).
    × CscRfLand l cl csc csc′ e a
    -- (T8c-ii) TRAILING behind that, and appended for the same reason: §2b⁵'s
    -- SHARPENING of the CS-client slot above — at an `apiCS` label on the client's
    -- OWN key its fact is the GENUINE ROW and not the disjunction.  This is the
    -- TWENTIETH component and the LAST; `LiveDrvCSD`'s `CliDrvAdj` is unproducible at
    -- `(ConsAdv cp0 cp1 , the disjunction's fixity arm)` without it, and the fixity
    -- arm is exactly the case node D's api carry must exclude.  *** A reader that
    -- ends its Σ pattern on a NON-wildcard must re-cut here (the banked Σ-append
    -- trap, seventh sighting — §7/§8's two relay-node peels are the two that did). ***
    × CscCliFired l cl csc csc′ e a
    -- (T10) TRAILING behind that, and appended for the same reason as every slot
    -- since (T1): §2b′⁺'s `sendBFBatchDone` LANDING.  This is the TWENTY-FIRST
    -- component and the `SrvSbLand` slot's third sibling — node A's up-hop BF
    -- coupling reads its `pp6 → pp7` crossing off exactly this slot, and the row
    -- disjunction's FIXITY arm is again the case that arm must exclude.
    -- *** A reader that ends its Σ pattern on a NON-wildcard must re-cut here (the
    -- banked Σ-append trap, EIGHTH sighting). ***
    × SrvBdLand l sv bfs bfs′ e a
    -- (T10) TRAILING behind that: §2b′⁶'s `recvBFBlock` landing, at the CLIENT.  The
    -- TWENTY-SECOND component, and the last of the family: the `cp4` client region's
    -- ENTERING step is exactly this row, and `CliApiRowP`'s fixity arm is the case it
    -- must exclude.  *** A reader that ends its Σ pattern on a NON-wildcard must
    -- re-cut here (the banked Σ-append trap, NINTH sighting). ***
    × CliRecvLand l cl bfc bfc′ e a
    -- (T11b) TRAILING behind that: §2b⁶'s `sendCSRollForward` landing, at the CS
    -- SERVER.  The TWENTY-THIRD component and the LAST: `DnRfwC`'s server field
    -- cannot cross `pp2 → pp3` without it, and `CSsApiRowP`'s fixity arm is again
    -- the case that crossing must exclude.  *** A reader that ends its Σ pattern on
    -- a NON-wildcard must re-cut here (the banked Σ-append trap, TENTH sighting). ***
    × CssRfwLand l sv css css′ e a
    -- (T11d) TRAILING behind that: §2b⁷'s `sendBFRequestRange` landing, at the BF
    -- CLIENT.  The TWENTY-FOURTH component and the last: node D's own BlockFetch api
    -- class cannot cross `cp2 → cp3` without it (`CliApiRowP`'s fixity arm leaves the
    -- `(cp3 , bcIdle)` state `LiveDrvBFD` §0(6) names as its hazard), and only the
    -- bundle knows which peer fired.  *** A reader that ends its Σ pattern on a
    -- NON-wildcard must re-cut here (the banked Σ-append trap, ELEVENTH sighting). ***
    × CliReqLand l cl bfc bfc′ e a

-- fold the ⁺ BF cascade's two arms into the Σ form
bfEvRio→api : {l : Link} {cl sv : Dir} {csc : CScPos} {css : CSsPos}
    {bfc : BFcPos} {bfs : BFsPos} {ip : InertPos}
    {X : Set 0ℓ} {e : Net_Api Payload X} {e₁ : BF.BFEv X} {a : X} {Bd′ : NetProc}
  -- (T1) the two directions' disequality, for §2b′'s client-fired refutation.  It
  -- is the dispatcher's own parameter, so this is a pure in-place widening with one
  -- call site.
  → cl ≢ sv
  → e ≡ ιBF e₁
  -- (grant #8) both callbacks now report their fired ROW beside the ⁺ fact, and the
  -- row is what this fold puts in `BundleApiEvo`'s two trailing slots
  → BundleBFEvRio l cl sv csc css bfc bfs ip
      (λ z → CliApiCf e a z × CliApiRowAt l cl bfc z e a)
      (λ z → SrvApiSf l sv bfs e a z × SrvApiRowAt l sv bfs z e a) e₁ a Bd′
  → BundleApiEvo l cl sv csc css bfc bfs ip e a Bd′
-- (grant #8) the fold CASES ON THE CHANNEL, and it has to: `CliApiRowP`/
-- `SrvApiRowP` are LABEL-directed, so at a variable `e₁` they are stuck and no
-- `inj₂` typechecks (measured: `[UnequalTerms] (_A ⊎ _B) !=< CliApiRowP …`).  With
-- the constructor matched they reduce — to the ⊎ on the peer's own api channel and
-- to bare fixity on the other three, where the callback's row IS that fixity.
bfEvRio→api {csc = csc} {css} {bfc} {bfs} {ip} {e₁ = BF.apiBFev l′ d′ m} ne refl
            (bioCli bfc′ eq run ((¬blk , ¬sbb) , row)) =
  csc , css , bfc′ , bfs , ip , eq , run , inj₂ ¬blk , inj₁ (refl , ¬sbb) , (λ _ h → h)
  -- the CLIENT fired: its row travels, the server slot is literal
  , inj₂ row , inj₁ refl
  -- (T1) … and the server's own-key row is REFUTED from the client's own `d′ ≡ cl`.
  -- The four PEER positions are passed explicitly: `coarsenBFs`/`coarsenBFc` are not
  -- injective, so a `_` there is left as an unsolvable constraint (measured:
  -- `[UnsolvedConstraints] coarsenBFs _bfs′ = coarsenBFs bfs′`).
  , srvReqRow-cli _ _ _ ne _ _ m _ bfc bfc′ bfs row
  , srvSbLand-cli _ _ _ ne _ _ m _ bfc bfc′ bfs row , refl , refl , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , srvBdLand-cli _ _ _ ne _ _ m _ bfc bfc′ bfs row , cliRecvLand-of _ _ _ _ m _ bfc bfc′ row , (λ p → ⊥-elim (nothing-absurd p))
  -- (T11d) the CLIENT fired, so §2b⁷'s landing is its OWN row read at the request tag
  , cliReqLand-of _ _ _ _ m _ bfc bfc′ row
bfEvRio→api {csc = csc} {css} {bfc} {bfs} {ip} {e₁ = BF.apiBFev l′ d′ m} ne refl
            (bioSrv bfs′ eq run (sf , row)) =
  csc , css , bfc , bfs′ , ip , eq , run , inj₁ refl , inj₂ sf , (λ _ h → h)
  , inj₁ refl , inj₂ row
  -- (T1) the SERVER fired: its own-key row IS the fired one (the two positions
  -- explicit, for the same non-injectivity reason as the client arm)
  , srvReqRow-of _ _ _ _ m _ bfs bfs′ row
  , srvSbLand-of _ _ _ _ m _ bfs bfs′ row , refl , refl , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , srvBdLand-of _ _ _ _ m _ bfs bfs′ row , cliRecvLand-srv _ _ _ _ _ m _ bfc bfs bfs′ row , (λ p → ⊥-elim (nothing-absurd p))
  -- (T11d) … and the SERVER fired is §2b⁷'s VACUOUS case, and the clause that makes
  -- the sharpening TRUE: a BF server has no `sendBFRequestRange` row at all
  , cliReqLand-srv _ _ _ _ _ m _ bfc bfs bfs′ row
bfEvRio→api {csc = csc} {css} {bfc} {bfs} {ip} {e₁ = BF.doneBF l′ d′} ne refl
            (bioCli bfc′ eq run ((¬blk , ¬sbb) , row)) =
  csc , css , bfc′ , bfs , ip , eq , run , inj₂ ¬blk , inj₁ (refl , ¬sbb) , (λ _ h → h)
  -- a BF client has no `doneBF` row at all, so its "row" is the fixity itself
  , row , inj₁ refl
  -- (T1) `done` is no `apiBF`: the pin itself is absurd
  , (λ r rbr → ⊥-elim (nothing-absurd rbr)) , (λ sb bsy → ⊥-elim (nothing-absurd sb)) , refl , refl , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ bd → ⊥-elim (nothing-absurd bd)) , (λ b rb _ → ⊥-elim (nothing-absurd rb)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ r rb → ⊥-elim (nothing-absurd rb))
bfEvRio→api {csc = csc} {css} {bfc} {bfs} {ip} {e₁ = BF.doneBF l′ d′} ne refl
            (bioSrv bfs′ eq run (sf , row)) =
  csc , css , bfc , bfs′ , ip , eq , run , inj₁ refl , inj₂ sf , (λ _ h → h)
  , refl , inj₂ row
  , (λ r rbr → ⊥-elim (nothing-absurd rbr)) , (λ sb bsy → ⊥-elim (nothing-absurd sb)) , refl , refl , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ bd → ⊥-elim (nothing-absurd bd)) , (λ b rb _ → ⊥-elim (nothing-absurd rb)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ r rb → ⊥-elim (nothing-absurd rb))
bfEvRio→api {csc = csc} {css} {bfc} {bfs} {ip} {e₁ = BF.sendBF l′ d′} ne refl
            (bioCli bfc′ eq run ((¬blk , ¬sbb) , row)) =
  csc , css , bfc′ , bfs , ip , eq , run , inj₂ ¬blk , inj₁ (refl , ¬sbb) , (λ _ h → h)
  , row , refl
  , (λ r rbr → ⊥-elim (nothing-absurd rbr)) , (λ sb bsy → ⊥-elim (nothing-absurd sb)) , refl , refl , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ bd → ⊥-elim (nothing-absurd bd)) , (λ b rb _ → ⊥-elim (nothing-absurd rb)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ r rb → ⊥-elim (nothing-absurd rb))
bfEvRio→api {csc = csc} {css} {bfc} {bfs} {ip} {e₁ = BF.sendBF l′ d′} ne refl
            (bioSrv bfs′ eq run (sf , row)) =
  csc , css , bfc , bfs′ , ip , eq , run , inj₁ refl , inj₂ sf , (λ _ h → h)
  , refl , row
  , (λ r rbr → ⊥-elim (nothing-absurd rbr)) , (λ sb bsy → ⊥-elim (nothing-absurd sb)) , refl , refl , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ bd → ⊥-elim (nothing-absurd bd)) , (λ b rb _ → ⊥-elim (nothing-absurd rb)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ r rb → ⊥-elim (nothing-absurd rb))
bfEvRio→api {csc = csc} {css} {bfc} {bfs} {ip} {e₁ = BF.receiveBF l′ d′} ne refl
            (bioCli bfc′ eq run ((¬blk , ¬sbb) , row)) =
  csc , css , bfc′ , bfs , ip , eq , run , inj₂ ¬blk , inj₁ (refl , ¬sbb) , (λ _ h → h)
  , row , refl
  , (λ r rbr → ⊥-elim (nothing-absurd rbr)) , (λ sb bsy → ⊥-elim (nothing-absurd sb)) , refl , refl , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ bd → ⊥-elim (nothing-absurd bd)) , (λ b rb _ → ⊥-elim (nothing-absurd rb)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ r rb → ⊥-elim (nothing-absurd rb))
bfEvRio→api {csc = csc} {css} {bfc} {bfs} {ip} {e₁ = BF.receiveBF l′ d′} ne refl
            (bioSrv bfs′ eq run (sf , row)) =
  csc , css , bfc , bfs′ , ip , eq , run , inj₁ refl , inj₂ sf , (λ _ h → h)
  , refl , row
  , (λ r rbr → ⊥-elim (nothing-absurd rbr)) , (λ sb bsy → ⊥-elim (nothing-absurd sb)) , refl , refl , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ bd → ⊥-elim (nothing-absurd bd)) , (λ b rb _ → ⊥-elim (nothing-absurd rb)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ r rb → ⊥-elim (nothing-absurd rb))

-- the ⁺ api dispatcher
absBundleG-api-evo⁺ : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → apiES .mem (X , e) a
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → BundleApiEvo l cl sv csc css bfc bfs ip e a Bd′
absBundleG-api-evo⁺ l cl sv cl≢sv csc css bfc bfs ip {e = apiCS l′ d′ m} apimem step
  with absBundleCS-ev-prod⁺ l cl sv cl≢sv csc css bfc bfs ip {e₁ = CS.apiCSev l′ d′ m} step
-- (T4) the CS CLIENT fired: its recovered row travels in the client slot and the
-- server slot is literal; the two BF slots and the freeze are untouched as before
... | bcscEB⁺ csc′ eq run row = csc′ , css , bfc , bfs , ip , eq , run , inj₁ refl , inj₁ (refl , λ ()) , (λ _ h → h) , refl , refl , (λ r rbr → ⊥-elim (nothing-absurd rbr)) , (λ sb bsy → ⊥-elim (nothing-absurd sb)) , cscApiRowP-api l cl l′ d′ m _ csc csc′ row , inj₁ refl
      -- (T5) the CS CLIENT fired, so a `reqCSRequestNext` pin is refuted by the
      -- client's OWN direction (§2b″)
      , cssReqLand-cli l cl sv cl≢sv l′ d′ m _ csc csc′ css row
      -- (T6d) … and a `sendCSAwaitReply` pin by the same argument (§2b‴)
      , cssAwLand-cli l cl sv cl≢sv l′ d′ m _ csc csc′ css row
      -- (T7) … and the CLIENT fired is exactly the WORKING case of §2b⁗: its own-key
      -- row IS the `recvCSRollforward` landing (the polarity opposite to the two lines
      -- above — see §2b⁗'s header before syncing this block)
      , cscRfLand-cli l cl l′ d′ m _ csc csc′ row
      -- (T8c-ii) … and §2b⁵'s sharpening, on the SAME polarity as §2b⁗'s: the CLIENT
      -- fired, so its own recovered row IS the fact and the pin is discarded
      , cscCliFired-cli l cl l′ d′ m _ csc csc′ row , (λ bd → ⊥-elim (nothing-absurd bd)) , (λ b rb _ → ⊥-elim (nothing-absurd rb))
      -- (T11b) … and §2b⁶'s landing on §2b‴'s polarity: the CLIENT fired, so a
      -- `sendCSRollForward` pin at the SERVER's key is refuted by the direction clash
      , cssRfwLand-cli l cl sv cl≢sv l′ d′ m _ csc csc′ css row
      -- (T11d) … and §2b⁷ is VACUOUS at an `apiCS` label: the BF client has no row
      -- there at all, so the request pin is absurd
      , (λ r rb → ⊥-elim (nothing-absurd rb))
-- … and the CS SERVER fired: the mirror
... | bcssEB⁺ css′ eq run row = csc , css′ , bfc , bfs , ip , eq , run , inj₁ refl , inj₁ (refl , λ ()) , (λ _ h → h) , refl , refl , (λ r rbr → ⊥-elim (nothing-absurd rbr)) , (λ sb bsy → ⊥-elim (nothing-absurd sb)) , inj₁ refl , cssApiRowP-api l sv l′ d′ m _ css css′ row
      -- (T5) … and the SERVER fired: its own-key row IS the landing (§2b″)
      , cssReqLand-of l sv l′ d′ m _ css css′ row
      -- (T6d) … and the same row read at the OTHER tag's landing (§2b‴)
      , cssAwLand-of l sv l′ d′ m _ css css′ row
      -- (T7) … and for §2b⁗ the SERVER fired is the VACUOUS case: its row's own
      -- direction is `sv` while a `recvCSRollforward` pin says `cl`, and `cl ≢ sv`
      , cscRfLand-srv l cl sv cl≢sv l′ d′ m _ csc css css′ row
      -- (T8c-ii) … and §2b⁵ is VACUOUS on this arm, by the very same direction clash:
      -- *** this clause is WHY the sharpening is true. ***  The client's slot is
      -- literal here, so a pin at the client's own key contradicts the server's row
      , cscCliFired-srv l cl sv cl≢sv l′ d′ m _ csc css css′ row , (λ bd → ⊥-elim (nothing-absurd bd)) , (λ b rb _ → ⊥-elim (nothing-absurd rb))
      -- (T11b) … and the SERVER fired is §2b⁶'s WORKING clause: its own-key row IS
      -- the `sendCSRollForward` landing, read at the third tag of the family
      , cssRfwLand-of l sv l′ d′ m _ css css′ row
      -- (T11d) … and §2b⁷ is VACUOUS at an `apiCS` label: the BF client has no row
      -- there at all, so the request pin is absurd
      , (λ r rb → ⊥-elim (nothing-absurd rb))
absBundleG-api-evo⁺ l cl sv cl≢sv csc css bfc bfs ip {e = apiBF l′ d′ m} apimem step =
  bfEvRio→api cl≢sv refl
    (absBundleBF-ev-io-evo l cl sv cl≢sv csc css bfc bfs ip
       (λ z → CliApiCf (apiBF l′ d′ m) _ z × CliApiRow l cl l′ d′ bfc z m _)
       (λ z → SrvApiSf l sv bfs (apiBF l′ d′ m) _ z × SrvApiRow l sv l′ d′ bfs z m _)
       {e₁ = BF.apiBFev l′ d′ m} (kcApi l cl bfc) (ksApi l sv bfs) step)
absBundleG-api-evo⁺ l cl sv cl≢sv csc css bfc bfs ip {e = apiKA l′ d′ m} apimem step
  with absBundleKA-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = KA.apiKAev l′ d′ m} step
... | bkacEB kac′ eq run = csc , css , bfc , bfs , record ip { kac = kac′ } , eq , run , inj₁ refl , inj₁ (refl , λ ()) , (λ ()) , refl , refl , (λ r rbr → ⊥-elim (nothing-absurd rbr)) , (λ sb bsy → ⊥-elim (nothing-absurd sb)) , refl , refl , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ bd → ⊥-elim (nothing-absurd bd)) , (λ b rb _ → ⊥-elim (nothing-absurd rb)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ r rb → ⊥-elim (nothing-absurd rb))
... | bkasEB kas′ eq run = csc , css , bfc , bfs , record ip { kas = kas′ } , eq , run , inj₁ refl , inj₁ (refl , λ ()) , (λ _ h → h) , refl , refl , (λ r rbr → ⊥-elim (nothing-absurd rbr)) , (λ sb bsy → ⊥-elim (nothing-absurd sb)) , refl , refl , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ bd → ⊥-elim (nothing-absurd bd)) , (λ b rb _ → ⊥-elim (nothing-absurd rb)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ r rb → ⊥-elim (nothing-absurd rb))
absBundleG-api-evo⁺ l cl sv cl≢sv csc css bfc bfs ip {e = apiTS l′ d′ m} apimem step
  with absBundleTS-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = TS.apiTSev l′ d′ m} step
... | btscEB tsc′ eq run = csc , css , bfc , bfs , record ip { tsc = tsc′ } , eq , run , inj₁ refl , inj₁ (refl , λ ()) , (λ _ h → h) , refl , refl , (λ r rbr → ⊥-elim (nothing-absurd rbr)) , (λ sb bsy → ⊥-elim (nothing-absurd sb)) , refl , refl , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ bd → ⊥-elim (nothing-absurd bd)) , (λ b rb _ → ⊥-elim (nothing-absurd rb)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ r rb → ⊥-elim (nothing-absurd rb))
... | btssEB tss′ eq run = csc , css , bfc , bfs , record ip { tss = tss′ } , eq , run , inj₁ refl , inj₁ (refl , λ ()) , (λ _ h → h) , refl , refl , (λ r rbr → ⊥-elim (nothing-absurd rbr)) , (λ sb bsy → ⊥-elim (nothing-absurd sb)) , refl , refl , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ bd → ⊥-elim (nothing-absurd bd)) , (λ b rb _ → ⊥-elim (nothing-absurd rb)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ r rb → ⊥-elim (nothing-absurd rb))
absBundleG-api-evo⁺ l cl sv cl≢sv csc css bfc bfs ip {e = apiLN l′ d′ m} apimem step
  with absBundleLN-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = LN.apiLNev l′ d′ m} step
... | blncEB lnc′ eq run = csc , css , bfc , bfs , record ip { lnc = lnc′ } , eq , run , inj₁ refl , inj₁ (refl , λ ()) , (λ _ h → h) , refl , refl , (λ r rbr → ⊥-elim (nothing-absurd rbr)) , (λ sb bsy → ⊥-elim (nothing-absurd sb)) , refl , refl , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ bd → ⊥-elim (nothing-absurd bd)) , (λ b rb _ → ⊥-elim (nothing-absurd rb)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ r rb → ⊥-elim (nothing-absurd rb))
... | blnsEB lns′ eq run = csc , css , bfc , bfs , record ip { lns = lns′ } , eq , run , inj₁ refl , inj₁ (refl , λ ()) , (λ _ h → h) , refl , refl , (λ r rbr → ⊥-elim (nothing-absurd rbr)) , (λ sb bsy → ⊥-elim (nothing-absurd sb)) , refl , refl , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ bd → ⊥-elim (nothing-absurd bd)) , (λ b rb _ → ⊥-elim (nothing-absurd rb)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ r rb → ⊥-elim (nothing-absurd rb))
absBundleG-api-evo⁺ l cl sv cl≢sv csc css bfc bfs ip {e = apiLF l′ d′ m} apimem step
  with absBundleLF-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = LF.apiLFev l′ d′ m} step
... | blfcEB lfc′ eq run = csc , css , bfc , bfs , record ip { lfc = lfc′ } , eq , run , inj₁ refl , inj₁ (refl , λ ()) , (λ _ h → h) , refl , refl , (λ r rbr → ⊥-elim (nothing-absurd rbr)) , (λ sb bsy → ⊥-elim (nothing-absurd sb)) , refl , refl , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ bd → ⊥-elim (nothing-absurd bd)) , (λ b rb _ → ⊥-elim (nothing-absurd rb)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ r rb → ⊥-elim (nothing-absurd rb))
... | blfsEB lfs′ eq run = csc , css , bfc , bfs , record ip { lfs = lfs′ } , eq , run , inj₁ refl , inj₁ (refl , λ ()) , (λ _ h → h) , refl , refl , (λ r rbr → ⊥-elim (nothing-absurd rbr)) , (λ sb bsy → ⊥-elim (nothing-absurd sb)) , refl , refl , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ bd → ⊥-elim (nothing-absurd bd)) , (λ b rb _ → ⊥-elim (nothing-absurd rb)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ r rb → ⊥-elim (nothing-absurd rb))
absBundleG-api-evo⁺ l cl sv cl≢sv csc css bfc bfs ip {e = done l′ d′ N2N_ChainSync} apimem step
  with absBundleCS-ev-prod⁺ l cl sv cl≢sv csc css bfc bfs ip {e₁ = CS.doneCS l′ d′} step
-- (T4) the `doneCS` channel: a CS CLIENT has no `done` row at all, so the client
-- arm's recovered row is one no consumer can take; the SERVER's `csDdone → csTerm`
-- row is the genuine one
... | bcscEB⁺ csc′ eq run row = csc′ , css , bfc , bfs , ip , eq , run , inj₁ refl , inj₁ (refl , λ ()) , (λ _ h → h) , refl , refl , (λ r rbr → ⊥-elim (nothing-absurd rbr)) , (λ sb bsy → ⊥-elim (nothing-absurd sb)) , cscApiRowP-done l cl l′ d′ _ csc csc′ row , inj₁ refl , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ bd → ⊥-elim (nothing-absurd bd)) , (λ b rb _ → ⊥-elim (nothing-absurd rb)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ r rb → ⊥-elim (nothing-absurd rb))
... | bcssEB⁺ css′ eq run row = csc , css′ , bfc , bfs , ip , eq , run , inj₁ refl , inj₁ (refl , λ ()) , (λ _ h → h) , refl , refl , (λ r rbr → ⊥-elim (nothing-absurd rbr)) , (λ sb bsy → ⊥-elim (nothing-absurd sb)) , inj₁ refl , cssApiRowP-done l sv l′ d′ _ css css′ row , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ bd → ⊥-elim (nothing-absurd bd)) , (λ b rb _ → ⊥-elim (nothing-absurd rb)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ r rb → ⊥-elim (nothing-absurd rb))
absBundleG-api-evo⁺ l cl sv cl≢sv csc css bfc bfs ip {e = done l′ d′ N2N_BlockFetch} apimem step =
  bfEvRio→api cl≢sv refl
    (absBundleBF-ev-io-evo l cl sv cl≢sv csc css bfc bfs ip
       (λ z → CliApiCf (done l′ d′ N2N_BlockFetch) _ z × (bfc ≡ z))
       (λ z → SrvApiSf l sv bfs (done l′ d′ N2N_BlockFetch) _ z
              × SrvDoneRow l sv l′ d′ bfs z _)
       {e₁ = BF.doneBF l′ d′} (kcDone l cl bfc) (ksDone l sv bfs) step)
-- (P5) grant #6: `done … N2N_KeepAlive` is the ONE `IsApiCSBF` label that can
-- move `kac`, so this clause goes through the local split, which is the one
-- inversion that reports the freeze beside the successor it builds
absBundleG-api-evo⁺ l cl sv cl≢sv csc css bfc bfs ip {e = done l′ d′ N2N_KeepAlive} apimem step
  with kaFire l cl sv cl≢sv csc css bfc bfs ip kaW-done step
... | kaFireF ip′ eq run frz = csc , css , bfc , bfs , ip′ , eq , run , inj₁ refl , inj₁ (refl , λ ()) , (λ _ → frz) , refl , refl , (λ r rbr → ⊥-elim (nothing-absurd rbr)) , (λ sb bsy → ⊥-elim (nothing-absurd sb)) , refl , refl , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ bd → ⊥-elim (nothing-absurd bd)) , (λ b rb _ → ⊥-elim (nothing-absurd rb)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ r rb → ⊥-elim (nothing-absurd rb))
absBundleG-api-evo⁺ l cl sv cl≢sv csc css bfc bfs ip {e = done l′ d′ N2N_TxSubmission} apimem step
  with absBundleTS-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = TS.doneTS l′ d′} step
... | btscEB tsc′ eq run = csc , css , bfc , bfs , record ip { tsc = tsc′ } , eq , run , inj₁ refl , inj₁ (refl , λ ()) , (λ _ h → h) , refl , refl , (λ r rbr → ⊥-elim (nothing-absurd rbr)) , (λ sb bsy → ⊥-elim (nothing-absurd sb)) , refl , refl , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ bd → ⊥-elim (nothing-absurd bd)) , (λ b rb _ → ⊥-elim (nothing-absurd rb)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ r rb → ⊥-elim (nothing-absurd rb))
... | btssEB tss′ eq run = csc , css , bfc , bfs , record ip { tss = tss′ } , eq , run , inj₁ refl , inj₁ (refl , λ ()) , (λ _ h → h) , refl , refl , (λ r rbr → ⊥-elim (nothing-absurd rbr)) , (λ sb bsy → ⊥-elim (nothing-absurd sb)) , refl , refl , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ bd → ⊥-elim (nothing-absurd bd)) , (λ b rb _ → ⊥-elim (nothing-absurd rb)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ r rb → ⊥-elim (nothing-absurd rb))
absBundleG-api-evo⁺ l cl sv cl≢sv csc css bfc bfs ip {e = done l′ d′ N2N_LeiosNotify} apimem step
  with absBundleLN-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = LN.doneLN l′ d′} step
... | blncEB lnc′ eq run = csc , css , bfc , bfs , record ip { lnc = lnc′ } , eq , run , inj₁ refl , inj₁ (refl , λ ()) , (λ _ h → h) , refl , refl , (λ r rbr → ⊥-elim (nothing-absurd rbr)) , (λ sb bsy → ⊥-elim (nothing-absurd sb)) , refl , refl , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ bd → ⊥-elim (nothing-absurd bd)) , (λ b rb _ → ⊥-elim (nothing-absurd rb)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ r rb → ⊥-elim (nothing-absurd rb))
... | blnsEB lns′ eq run = csc , css , bfc , bfs , record ip { lns = lns′ } , eq , run , inj₁ refl , inj₁ (refl , λ ()) , (λ _ h → h) , refl , refl , (λ r rbr → ⊥-elim (nothing-absurd rbr)) , (λ sb bsy → ⊥-elim (nothing-absurd sb)) , refl , refl , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ bd → ⊥-elim (nothing-absurd bd)) , (λ b rb _ → ⊥-elim (nothing-absurd rb)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ r rb → ⊥-elim (nothing-absurd rb))
absBundleG-api-evo⁺ l cl sv cl≢sv csc css bfc bfs ip {e = done l′ d′ N2N_LeiosFetch} apimem step
  with absBundleLF-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = LF.doneLF l′ d′} step
... | blfcEB lfc′ eq run = csc , css , bfc , bfs , record ip { lfc = lfc′ } , eq , run , inj₁ refl , inj₁ (refl , λ ()) , (λ _ h → h) , refl , refl , (λ r rbr → ⊥-elim (nothing-absurd rbr)) , (λ sb bsy → ⊥-elim (nothing-absurd sb)) , refl , refl , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ bd → ⊥-elim (nothing-absurd bd)) , (λ b rb _ → ⊥-elim (nothing-absurd rb)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ r rb → ⊥-elim (nothing-absurd rb))
... | blfsEB lfs′ eq run = csc , css , bfc , bfs , record ip { lfs = lfs′ } , eq , run , inj₁ refl , inj₁ (refl , λ ()) , (λ _ h → h) , refl , refl , (λ r rbr → ⊥-elim (nothing-absurd rbr)) , (λ sb bsy → ⊥-elim (nothing-absurd sb)) , refl , refl , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ bd → ⊥-elim (nothing-absurd bd)) , (λ b rb _ → ⊥-elim (nothing-absurd rb)) , (λ p → ⊥-elim (nothing-absurd p)) , (λ r rb → ⊥-elim (nothing-absurd rb))
absBundleG-api-evo⁺ l cl sv cl≢sv csc css bfc bfs ip {e = input  _ _ _} apimem step = ⊥-elim apimem
absBundleG-api-evo⁺ l cl sv cl≢sv csc css bfc bfs ip {e = output _ _ _} apimem step = ⊥-elim apimem
absBundleG-api-evo⁺ l cl sv cl≢sv csc css bfc bfs ip {e = sndmsg _ _ _} apimem step = ⊥-elim apimem
absBundleG-api-evo⁺ l cl sv cl≢sv csc css bfc bfs ip {e = rcvmsg _ _ _} apimem step = ⊥-elim apimem
absBundleG-api-evo⁺ l cl sv cl≢sv csc css bfc bfs ip {e = tx     _ _ _} apimem step = ⊥-elim apimem
absBundleG-api-evo⁺ l cl sv cl≢sv csc css bfc bfs ip {e = sndack _ _ _} apimem step = ⊥-elim apimem
absBundleG-api-evo⁺ l cl sv cl≢sv csc css bfc bfs ip {e = rcvack _ _ _} apimem step = ⊥-elim apimem
absBundleG-api-evo⁺ l cl sv cl≢sv csc css bfc bfs ip {e = ack    _ _ _} apimem step = ⊥-elim apimem
absBundleG-api-evo⁺ l cl sv cl≢sv csc css bfc bfs ip {e = break  _}     apimem step = ⊥-elim apimem

------------------------------------------------------------------------
-- §5  NODE A — the ⁺ re-mirror of `PipeNodeAEvo`'s two link peels and its
-- dispatcher.  Node A owns BOTH legs' UPSTREAM BF servers (`upSrv legBD =
-- bfS-AB`, `upSrv legCD = bfS-AC`), so this is where leaf 6's up half and
-- LEAF 7 (`ProdNotSent → ProdSent → the up server holds blkA`) are discharged.
--
-- HOW LEAF 7 CLOSES.  The `a56` crossing is the ONLY producer adjacency out of a
-- not-sent phase into a sent one (`padv-cross-pp5`), so the driver's step is at
-- `pp5`, whose single row is `apiBF l hi sendBFBlock ! blk` — `decProd-pp5-sbbAt`
-- reads the whole pin off it.  That refutes the bundle's server-FIXED arm through
-- the CLIENT's `IsSBB → ⊥` (no BF client has a `sendBFBlock` row) and feeds the
-- fired arm's `SrvLands` on the other side.
------------------------------------------------------------------------

-- the ONLY producer adjacency leaving a NOT-SENT phase for a SENT one is `a56`
padv-cross-pp5 : {pp pp′ : ProdPh} → ProdAdv pp pp′ → ProdNotSent pp → ProdSent pp′ → pp ≡ pp5
padv-cross-pp5 a01 _ ()
padv-cross-pp5 a12 _ ()
padv-cross-pp5 a23 _ ()
padv-cross-pp5 a34 _ ()
padv-cross-pp5 a45 _ ()
padv-cross-pp5 a56 _ _ = refl
padv-cross-pp5 a67 () _
padv-cross-pp5 a78 () _
padv-cross-pp5 a89 () _

-- a produce driver at `pp5` has ONE row, `apiBF l d sendBFBlock ! blk`, so a fire
-- out of it pins the whole observation (key AND block)
decProd-pp5-sbbAt : (l : Link) (d : Dir) (blk : Block)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → SN.decProd l d blk pp5 ─[ ev (evl (evLabel X e a)) ]─► M
  → SbbAt l d blk e a
decProd-pp5-sbbAt l d blk {X} {e} {a} (sVis refl br)
  with Net_Api-≟ {Payload} (Block , apiBF l d sendBFBlock) (X , e)
... | no  ¬q   = ⊥-elim (nothing-absurd br)
... | yes refl with a ≟ blk
...   | no  _  = ⊥-elim (nothing-absurd br)
...   | yes q  = cong (λ z → just (l , d , z)) q

-- (T10) … and a produce driver at `pp6` has ONE row too, `apiBF l d
-- sendBFBatchDone ! U.tt`, so a fire out of it pins the KEY.  `decProd-pp5-sbbAt`'s
-- twin one sub-phase along; the carrier is `⊤`, so unlike `pp5`'s there is no value
-- to recover and the pin is `BdAt`'s `Maybe (Link × Dir)` equation
decProd-pp6-bdAt : (l : Link) (d : Dir) (blk : Block)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → SN.decProd l d blk pp6 ─[ ev (evl (evLabel X e a)) ]─► M
  → BdAt l d e a
decProd-pp6-bdAt l d blk {X} {e} {a} (sVis refl br)
  with Net_Api-≟ {Payload} (ApiBFCar sendBFBatchDone , apiBF l d sendBFBatchDone) (X , e)
... | no  ¬q   = ⊥-elim (nothing-absurd br)
... | yes refl = refl

-- (T10) node A's producer has FIRED its batch-done (`pp7` on).  The region is
-- ENTERED by the single crossing `a67` and never left, which is what makes the
-- coupling below preservable
ProdDone : ProdPh → Set
ProdDone pp0 = ⊥
ProdDone pp1 = ⊥
ProdDone pp2 = ⊥
ProdDone pp3 = ⊥
ProdDone pp4 = ⊥
ProdDone pp5 = ⊥
ProdDone pp6 = ⊥
ProdDone pp7 = ⊤
ProdDone pp8 = ⊤
ProdDone pp9 = ⊤

-- … and the server region its complement owns: the four positions BETWEEN the
-- request's api pick-up and the batch-done wire-send.  *** io-CLOSED on the way IN
-- (`bsWsb`/`bsWblk`'s wire-sends land INSIDE it, and no wire-READ lands in it at
-- all), which is why `bsAreq` is deliberately OUT: the server's own read of a
-- request would otherwise be an entry the io class cannot refute ***
SrvBatch : NS.BFsPos → Set
SrvBatch NS.bsIdle      = ⊥
SrvBatch (NS.bsAreq r)  = ⊥
SrvBatch NS.bsBusy      = ⊤
SrvBatch NS.bsDdone     = ⊥
SrvBatch NS.bsWsb       = ⊤
SrvBatch NS.bsStream    = ⊤
SrvBatch NS.bsWnb       = ⊥
SrvBatch (NS.bsWblk b)  = ⊤
SrvBatch NS.bsWbd       = ⊥
SrvBatch NS.bsTerm      = ⊥

-- (T10) a produce driver at `pp7` fires `done l d N2N_ChainSync`, at which the BF
-- server's api fact DEGENERATES TO FIXITY (`SrvApiRowP`'s catch-all: the label is on
-- the other channel).  This is the `decProd-pp6-bdAt` shape with the conclusion
-- taken already-APPLIED, because the fixity is what the consumer wants
decProd-pp7-fix : (l : Link) (d : Dir) (blk : Block) (bfs bfs′ : BFsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → SN.decProd l d blk pp7 ─[ ev (evl (evLabel X e a)) ]─► M
  → SrvApiRowP l d bfs bfs′ e a → bfs ≡ bfs′
decProd-pp7-fix l d blk bfs bfs′ {X} {e} {a} (sVis refl br) row
  with Net_Api-≟ {Payload} (⊤₀ , done l d N2N_ChainSync) (X , e)
... | no  ¬q   = ⊥-elim (nothing-absurd br)
... | yes refl = row

-- the server's `done` row exists at `bsDdone` and lands at `bsTerm`, so a fired
-- `done` row pins its TARGET.  `bdRow⇒stream`'s shape at the twelfth row
doneRow⇒term : ∀ {a} (l : Link) (d : Dir) (q q′ : NS.BFsPos)
             → NS.bfSnxt l d q (⊤₀ , done l d N2N_BlockFetch) a ≡ just q′
             → q′ ≡ NS.bsTerm
doneRow⇒term l d NS.bsIdle      q′ ()
doneRow⇒term l d (NS.bsAreq r)  q′ ()
doneRow⇒term l d NS.bsBusy      q′ ()
doneRow⇒term l d NS.bsDdone     q′ eq
  rewrite ≟-yes-refl l | ≟-yes-refl d = sym (just-injective eq)
doneRow⇒term l d NS.bsWsb       q′ ()
doneRow⇒term l d NS.bsStream    q′ ()
doneRow⇒term l d NS.bsWnb       q′ ()
doneRow⇒term l d (NS.bsWblk b)  q′ ()
doneRow⇒term l d NS.bsWbd       q′ ()
doneRow⇒term l d NS.bsTerm      q′ ()

-- … and one at `pp8` fires `done l d N2N_BlockFetch`, at which the server's fact is
-- the `done` ROW or fixity — and the row's target is `bsTerm`, which is OUTSIDE
-- `SrvBatch`, so either way the batch region is not entered
decProd-pp8-out : (l : Link) (d : Dir) (blk : Block) (bfs bfs′ : BFsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → SN.decProd l d blk pp8 ─[ ev (evl (evLabel X e a)) ]─► M
  → SrvApiRowP l d bfs bfs′ e a
  → SrvBatch (coarsenBFs bfs′) → SrvBatch (coarsenBFs bfs)
decProd-pp8-out l d blk bfs bfs′ {X} {e} {a} (sVis refl br) row hb
  with Net_Api-≟ {Payload} (⊤₀ , done l d N2N_BlockFetch) (X , e)
... | no  ¬q   = ⊥-elim (nothing-absurd br)
... | yes refl with row
...   | inj₁ eq   = subst (λ z → SrvBatch (coarsenBFs z)) (sym eq) hb
...   | inj₂ (refl , refl , drow) =
        ⊥-elim (subst SrvBatch
                  (doneRow⇒term l d (coarsenBFs bfs) (coarsenBFs bfs′) drow) hb)

-- *** (T10) THE BATCH-REGION KEEP, by a dispatch on the producer's OWN advance. ***
-- Once node A has fired its batch-done, an api step cannot move its up BF server
-- back INTO the batch region: the seven crossings at or below `pp6` have `ProdDone`
-- uninhabited at their SOURCE, and the two above it fire `done` labels at which the
-- server is fixed (`pp7`, the ChainSync done) or lands at `bsTerm` (`pp8`).
--
-- *** THIS IS THE FACT NO ROW DISJUNCTION CAN GIVE, and the reason it lives here:
-- *** the case it must exclude is "the server's api row fired while node A's driver
-- did not", which is impossible in the model (an api event is a node-local
-- `∥⇘ apiES ⇙` sync) and invisible to `SrvApiRowP`, whose fixity arm admits it.  The
-- driver's own STEP is what refutes it, and `ldProd` projects that step away one
-- layer up — the T8c-0 finding, fourth instance
srvBatchKeep-up : (l : Link) (bfs bfs′ : BFsPos) (pp pp′ : ProdPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → SN.decProd l hi blkA pp ─[ ev (evl (evLabel X e a)) ]─► M
  → ProdAdv pp pp′
  → SrvApiRowP l hi bfs bfs′ e a
  → ProdDone pp → SrvBatch (coarsenBFs bfs′) → SrvBatch (coarsenBFs bfs)
srvBatchKeep-up l bfs bfs′ pp pp′ st a01 row ()
srvBatchKeep-up l bfs bfs′ pp pp′ st a12 row ()
srvBatchKeep-up l bfs bfs′ pp pp′ st a23 row ()
srvBatchKeep-up l bfs bfs′ pp pp′ st a34 row ()
srvBatchKeep-up l bfs bfs′ pp pp′ st a45 row ()
srvBatchKeep-up l bfs bfs′ pp pp′ st a56 row ()
srvBatchKeep-up l bfs bfs′ pp pp′ st a67 row ()
srvBatchKeep-up l bfs bfs′ pp pp′ st a78 row _ hb =
  subst (λ z → SrvBatch (coarsenBFs z))
        (sym (decProd-pp7-fix l hi blkA bfs bfs′ st row)) hb
srvBatchKeep-up l bfs bfs′ pp pp′ st a89 row _ hb =
  decProd-pp8-out l hi blkA bfs bfs′ st row hb

-- the leg's UPSTREAM server facts across node A's own api step: the frozen
-- `SrvEvoUp` arm, the RAW `SrvValEvo` witness, leaf 6's PREDECESSOR keep and
-- LEAF 7's producer hand-over
SrvUpFacts : (l : Link) (bfs bfs′ : BFsPos) (pp pp′ : ProdPh)
             {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) → Set₁
SrvUpFacts l bfs bfs′ pp pp′ e a =
    ((bfs ≡ bfs′) ⊎ ((BFsHasBlk bfs′ → ⊥) ⊎ ProdSent pp′))
  × ((bfs ≡ bfs′) ⊎ BfsSucc l hi bfs′ e a)
  × ((bfs ≡ bfs′) ⊎ (BFsHasBlk bfs → ⊥))
  × (ProdNotSent pp → ProdSent pp′ → bfs′ ≡ bsBlk1 blkA)
  -- SESSION-55 (`LiveTokenExcl` P3): the SOURCE-PHASE field.  A step that makes
  -- the leg's up server HOLD is node A's own `sendBFBlock`, so the co-firing
  -- producer is at `pp5` and has NOT yet sent.
  × ((BFsHasBlk bfs → ⊥) → BFsHasBlk bfs′ → ProdNotSent pp)
  -- (P7) SESSION-56: the GENERIC producer LANDING, kept instead of being
  -- projected into the `blkA`-specialised crossing-gated fourth component.  On
  -- the FIRED arm it is the bundle's own `SrvLands`; on the server-FIXED arm the
  -- `IsSBB → ⊥` conjunct makes it vacuous.  Without it the cone's `ldFix`-shaped
  -- arms cannot be told apart from the producing one at the successor.
  × SrvLands l hi e a bfs′
  -- *** (T10) THE `pp6` LANDING, ALREADY APPLIED. ***  The seventh component, and
  -- the ONE fact node A's up-hop BF coupling cannot get from the row disjunction:
  -- at `pp6` the driver's own step IS the `sendBFBatchDone` fire, so a server that
  -- was streaming is at `bsWbd` after it.  Applied here rather than exported raw
  -- because the driver STEP is what turns the phase into the label pin and `ldProd`
  -- projects that step away one layer up (the T8c-0 finding, third instance)
  × (pp ≡ pp6 → (coarsenBFs bfs ≡ NS.bsStream) × (coarsenBFs bfs′ ≡ NS.bsWbd))
  -- *** (T10) … and the BATCH-REGION KEEP, the eighth component. ***  With the
  -- seventh it is the whole api class of node A's up-hop BF coupling: the seventh
  -- closes the ONE crossing that leaves the batch, this one closes every step that
  -- is already past it
  × (ProdDone pp → SrvBatch (coarsenBFs bfs′) → SrvBatch (coarsenBFs bfs))

-- (P3) the up SOURCE-PHASE answer.  The bundle's server-FIXED arm makes the
-- hypotheses contradictory; on the FIRED arm the successor's own classification
-- names the `sendBFBlock` observation, and `decProd-sbb-pp5` reads the driver's
-- phase off it (`ProdNotSent pp5` is `⊤`).  It cannot be done downstream: `ldProd`
-- projects the driver STEP away.
srvGain-up : (l : Link) (bfs bfs′ : BFsPos) (pp : ProdPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → SN.decProd l hi blkA pp ─[ ev (evl (evLabel X e a)) ]─► M
  → (((bfs ≡ bfs′) × (IsSBB (evLabel X e a) → ⊥))
     ⊎ ((BFsHasBlk bfs → ⊥) × SrvSuccA l hi e a bfs′ × SrvLands l hi e a bfs′))
  → (BFsHasBlk bfs → ⊥) → BFsHasBlk bfs′ → ProdNotSent pp
srvGain-up l bfs bfs′ pp st (inj₁ (eq , _)) ¬h h =
  ⊥-elim (¬h (subst BFsHasBlk (sym eq) h))
srvGain-up l bfs bfs′ pp st (inj₂ (_ , inj₁ nb , _)) ¬h h = ⊥-elim (nb h)
srvGain-up l bfs bfs′ pp {e = e} {a} st (inj₂ (_ , inj₂ (b″ , sd , _) , _)) ¬h h =
  subst ProdNotSent
    (sym (decProd-sbb-pp5 l hi blkA pp st (proj₁ (sbbAt⇒pin e a sd)))) tt

-- assemble `SrvUpFacts` from the ⁺ bundle's server component and the co-firing
-- produce driver's own step
srvUp-of : (l : Link) (bfs bfs′ : BFsPos) (pp pp′ : ProdPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → SN.decProd l hi blkA pp ─[ ev (evl (evLabel X e a)) ]─► M
  → ProdAdv pp pp′
  → (((bfs ≡ bfs′) × (IsSBB (evLabel X e a) → ⊥))
     ⊎ ((BFsHasBlk bfs → ⊥) × SrvSuccA l hi e a bfs′ × SrvLands l hi e a bfs′))
  -- (T10) … and the bundle's own `sendBFBatchDone` landing slot, which is what the
  -- seventh component is: BOTH arms answer it the same way, because the fact is the
  -- BUNDLE's and the arms only differ in which peer fired
  → SrvBdLand l hi bfs bfs′ e a
  -- (T10) … and the server's own api-row fact, which the keep dispatches on
  → SrvApiRowP l hi bfs bfs′ e a
  → SrvUpFacts l bfs bfs′ pp pp′ e a
srvUp-of l bfs bfs′ pp pp′ {e = e} {a} st padv (inj₁ (eq , ¬sbb)) bdl srow =
    srvEvo⇒up l bfs bfs′ pp pp′ st padv (inj₁ eq) , inj₁ eq , inj₁ eq
  , (λ hn hs → ⊥-elim (¬sbb (proj₁ (sbbAt⇒pin e a
       (decProd-pp5-sbbAt l hi blkA
         (subst (λ ph → SN.decProd l hi blkA ph ─[ ev (evl (evLabel _ e a)) ]─► _)
                (padv-cross-pp5 padv hn hs) st))))))
  , srvGain-up l bfs bfs′ pp st (inj₁ (eq , ¬sbb))
  -- (P7) the server-FIXED arm carries "this was no `sendBFBlock`", so the
  -- generic landing is vacuous at every block
  , (λ b″ sd → ⊥-elim (¬sbb (proj₁ (sbbAt⇒pin e a sd))))
  -- (T10) … and the `pp6` landing is the BUNDLE's slot, read through the driver's
  -- own step: at `pp6` that step IS the `sendBFBatchDone` fire
  , (λ h6 → bdl (decProd-pp6-bdAt l hi blkA
                    (subst (λ ph → SN.decProd l hi blkA ph
                                     ─[ ev (evl (evLabel _ e a)) ]─► _) h6 st)))
  -- (T10) … and the keep, straight off §2b′⁺'s dispatch
  , srvBatchKeep-up l bfs bfs′ pp pp′ st padv srow
srvUp-of l bfs bfs′ pp pp′ {e = e} {a} st padv (inj₂ (nb , succ , lands)) bdl srow =
    srvEvo⇒up l bfs bfs′ pp pp′ st padv (inj₂ (srvSuccA⇒bfsSucc l hi bfs′ succ))
  , inj₂ (srvSuccA⇒bfsSucc l hi bfs′ succ) , inj₂ nb
  , (λ hn hs → lands blkA
       (decProd-pp5-sbbAt l hi blkA
         (subst (λ ph → SN.decProd l hi blkA ph ─[ ev (evl (evLabel _ e a)) ]─► _)
                (padv-cross-pp5 padv hn hs) st)))
  , srvGain-up l bfs bfs′ pp st (inj₂ (nb , succ , lands))
  -- (P7) the FIRED arm's landing travels unchanged
  , lands
  -- (T10) … and the `pp6` landing, exactly as on the fixed arm
  , (λ h6 → bdl (decProd-pp6-bdAt l hi blkA
                    (subst (λ ph → SN.decProd l hi blkA ph
                                     ─[ ev (evl (evLabel _ e a)) ]─► _) h6 st)))
  -- (T10) … and the keep, straight off §2b′⁺'s dispatch
  , srvBatchKeep-up l bfs bfs′ pp pp′ st padv srow

-- node A's two bundle faces, named so the peels below stay readable
bunA-AB : SN.NodeStateA → NetProc
bunA-AB na = absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na)
                        (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)

bunA-AC : SN.NodeStateA → NetProc
bunA-AC na = absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na)
                        (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)

-- node A's ⁺ api peel result: successor node, run, and — per FIRING leg — the
-- genuine `ProdAdv`, the other producer's fixity, the firing leg's `SrvUpFacts`,
-- the other leg's server fixity and (P7, session-56) the FIRED LINK PIN — the
-- witness the two peels below already take as an argument and used only
-- internally.  It is what refutes the CO-leg's producer landing at the cone: an
-- `ApiHasLink linkAB e` and an `ApiHasLink linkAC e` cannot both hold.
NodeAApiEvo : (na : SN.NodeStateA) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
              (M : NetProc) → Set₁
NodeAApiEvo na {X} e a M =
  Σ[ na′ ∈ SN.NodeStateA ] (M ≡ absNodeA na′)
    × (SN.decNodeA na ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeA na′)
    × ( ( ProdAdv (SN.NodeStateA.prod-AB na) (SN.NodeStateA.prod-AB na′)
          × (SN.NodeStateA.prod-AC na′ ≡ SN.NodeStateA.prod-AC na)
          × SrvUpFacts linkAB (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.bfS-AB na′)
                       (SN.NodeStateA.prod-AB na) (SN.NodeStateA.prod-AB na′) e a
          × (SN.NodeStateA.bfS-AC na ≡ SN.NodeStateA.bfS-AC na′)
          × ApiHasLink linkAB e )
      ⊎ ( ProdAdv (SN.NodeStateA.prod-AC na) (SN.NodeStateA.prod-AC na′)
          × (SN.NodeStateA.prod-AB na′ ≡ SN.NodeStateA.prod-AB na)
          × SrvUpFacts linkAC (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.bfS-AC na′)
                       (SN.NodeStateA.prod-AC na) (SN.NodeStateA.prod-AC na′) e a
          × (SN.NodeStateA.bfS-AB na ≡ SN.NodeStateA.bfS-AB na′)
          × ApiHasLink linkAC e ) )
    -- (grant #8) TRAILING: node A's two tracked BF servers' fired ROWS — the two
    -- legs' UP servers, which is what the `ChanUp` join's visible arm consumes
    × SrvApiRowP linkAB hi (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.bfS-AB na′) e a
    × SrvApiRowP linkAC hi (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.bfS-AC na′) e a
    -- (T6c, grant #12) TRAILING behind those: node A's two UP-hop CS SERVERS' rows.
    -- Node A's bundles are `absBundleG l lo hi`, so the up hop's CS SERVER is A's at
    -- its `sv` — which is why the CS join needed a node-A slot at all, and why the
    -- row was already in `BundleApiEvo`'s fifteenth slot waiting to be threaded.
    × CSsApiRowP linkAB hi (SN.NodeStateA.csS-AB na) (SN.NodeStateA.csS-AB na′) e a
    × CSsApiRowP linkAC hi (SN.NodeStateA.csS-AC na) (SN.NodeStateA.csS-AC na′) e a

-- firing link = linkAB (leg BD)
nodeA-api-AB-evo⁺ : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
                    {B₁ D₁AB : NetProc}
  → apiES .mem (X , e) a
  → (bunA-AB na ⦀ bunA-AC na) ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ─[ ev (evl (evLabel X e a)) ]─► D₁AB
  → ApiHasLink linkAB e
  → NodeAApiEvo na e a
      (B₁ ∥⇘ apiES ⇙ (D₁AB ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)))
nodeA-api-AB-evo⁺ na {X} {e} {a} apimem bStep sDAB ahl
  with prodAdv-of linkAB hi blkA (SN.NodeStateA.prod-AB na) sDAB
... | pp′ , refl , padv
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (bunA-AB na) (bunA-AC na) bStep
...   | PEA.evSync () _ _
...   | PEA.evR _ sBAC = ⊥-elim (absBundleG-api-no linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) ahl linkAB≢linkAC apimem (_ , sBAC))
...   | PEA.evBoth _ _ sBAC = ⊥-elim (absBundleG-api-no linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) ahl linkAB≢linkAC apimem (_ , sBAC))
...   | PEA.evL _ sBAB
      with absBundleG-api-evo⁺ linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) apimem sBAB
...     | csc′ , css′ , bfc′ , bfs′ , ip′ , eq , run , _ , srvE , _ , _ , srvRow , _ , _ , _ , cssRow , _ , _ , _ , _ , bdl , _ =
          SN.mkNodeA csc′ css′ bfc′ bfs′ pp′ (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) ip′ (SN.NodeStateA.inert-AC na)
        , cong (λ z → (z ⦀ bunA-AC na) ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA pp′ ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na))) eq
        , ∥⇘⇙-wev-sync apiES _ _ apimem
            (⦀-wev-L _ _ (noOffer→viewV _ (bundleG-api-no linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) ahl linkAB≢linkAC apimem)) run)
            (ev→wev (⦀-ev-L (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na)) _ sDAB (noOffer→viewV _ (drvA-AC-no na ahl))))
        , inj₁ (padv , refl
               , srvUp-of linkAB (SN.NodeStateA.bfS-AB na) bfs′ (SN.NodeStateA.prod-AB na) pp′ sDAB padv srvE bdl srvRow
               , refl , ahl)
        -- (grant #8) AB fired, so its row is the bundle's; AC is a LITERAL
        , srvRow , srvApiRow-fix linkAC hi (SN.NodeStateA.bfS-AC na) e a
        -- (T6c, grant #12) … and the same for A's two CS servers
        , cssRow , cssApiRow-fix linkAC hi (SN.NodeStateA.csS-AC na) e a

-- firing link = linkAC (leg CD), the mirror
nodeA-api-AC-evo⁺ : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
                    {B₁ D₁AC : NetProc}
  → apiES .mem (X , e) a
  → (bunA-AB na ⦀ bunA-AC na) ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na) ─[ ev (evl (evLabel X e a)) ]─► D₁AC
  → ApiHasLink linkAC e
  → NodeAApiEvo na e a
      (B₁ ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ D₁AC))
nodeA-api-AC-evo⁺ na {X} {e} {a} apimem bStep sDAC ahl
  with prodAdv-of linkAC hi blkA (SN.NodeStateA.prod-AC na) sDAC
... | pp′ , refl , padv
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (bunA-AB na) (bunA-AC na) bStep
...   | PEA.evSync () _ _
...   | PEA.evL _ sBAB = ⊥-elim (absBundleG-api-no linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ahl (λ q → linkAB≢linkAC (sym q)) apimem (_ , sBAB))
...   | PEA.evBoth _ sBAB _ = ⊥-elim (absBundleG-api-no linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ahl (λ q → linkAB≢linkAC (sym q)) apimem (_ , sBAB))
...   | PEA.evR _ sBAC
      with absBundleG-api-evo⁺ linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) apimem sBAC
...     | csc′ , css′ , bfc′ , bfs′ , ip′ , eq , run , _ , srvE , _ , _ , srvRow , _ , _ , _ , cssRow , _ , _ , _ , _ , bdl , _ =
          SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na) csc′ css′ bfc′ bfs′ pp′ (SN.NodeStateA.inert-AB na) ip′
        , cong (λ z → (bunA-AB na ⦀ z) ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA pp′)) eq
        , ∥⇘⇙-wev-sync apiES _ _ apimem
            (⦀-wev-R _ _ (noOffer→viewV _ (bundleG-api-no linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ahl (λ q → linkAB≢linkAC (sym q)) apimem)) run)
            (ev→wev (⦀-ev-R _ (SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)) sDAC (noOffer→viewV _ (drvA-AB-no na ahl))))
        , inj₂ (padv , refl
               , srvUp-of linkAC (SN.NodeStateA.bfS-AC na) bfs′ (SN.NodeStateA.prod-AC na) pp′ sDAC padv srvE bdl srvRow
               , refl , ahl)
        -- (grant #8) the mirror
        , srvApiRow-fix linkAB hi (SN.NodeStateA.bfS-AB na) e a , srvRow
        -- (T6c, grant #12) … and the CS mirror
        , cssApiRow-fix linkAB hi (SN.NodeStateA.csS-AB na) e a , cssRow

-- node-A api inversion: dispatch on which produce driver fired
nodeA-ev-api-evo⁺ : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
                    {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeA na ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeAApiEvo na e a M
nodeA-ev-api-evo⁺ na {X} {e} {a} apimem step
  with SStep.reflect-node-api (bunA-AB na ⦀ bunA-AC na)
         (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na))
           (SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)) dStep
... | PEA.evSync () _ _
... | PEA.evL _ sDAB = nodeA-api-AB-evo⁺ na apimem bStep sDAB (decProd-ev-link linkAB hi blkA (SN.NodeStateA.prod-AB na) sDAB)
... | PEA.evR _ sDAC = nodeA-api-AC-evo⁺ na apimem bStep sDAC (decProd-ev-link linkAC hi blkA (SN.NodeStateA.prod-AC na) sDAC)
... | PEA.evBoth _ sDAB sDAC = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (decProd-ev-link linkAB hi blkA (SN.NodeStateA.prod-AB na) sDAB)
                     (decProd-ev-link linkAC hi blkA (SN.NodeStateA.prod-AC na) sDAC)))

------------------------------------------------------------------------
-- §6  THE RELAY CLASSIFIER, ⁺.  A mirror of `PipeValRelay.cpStepKindL-of⁺`'s
-- eight clauses with an EIGHTH component appended: a step that CROSSES from the
-- holding region into the FORWARDED one is the produce arm's `pp5 → pp6` hop,
-- whose `!` pins the observation to the relay's OWN recorded block.  That is
-- LEAF 9's positive content, and it has to be produced HERE because
-- `RelayStepKind` is phase-only: one layer up, `rFwd` is type-formable from any
-- holding source, so the crossing cannot be located from `rk` alone.
--
-- Mirrored rather than appended in place: `cpStepKindL-of⁺` is a base module, and
-- the mirror is eight clauses whose seven existing components are copied verbatim
-- (every refutation, anchor and inversion is imported).  Owner grant #3 stays
-- unexercised and no base module is touched BY THIS SLICE.  (Scope note, task-4b:
-- LATER slices of this file's own campaign DID touch two base modules — grant #8 on
-- `PipeBundleEvo` and grant #7 on the io decodes / `PipeNodeIoEvo` — so read the
-- sentence above as being about the `cpStepKindL-of⁺` mirror only, not about the
-- file.)
------------------------------------------------------------------------

-- the ONLY produce-arm adjacency leaving the HOLDING region for the FORWARDED one
padv-cross-fwd : {b : Block₃} {pp pp′ : ProdPh} → ProdAdv pp pp′
               → RelayHas (producing b pp) → RelayFwd (producing b pp′) → pp ≡ pp5
padv-cross-fwd a01 _ ()
padv-cross-fwd a12 _ ()
padv-cross-fwd a23 _ ()
padv-cross-fwd a34 _ ()
padv-cross-fwd a45 _ ()
padv-cross-fwd a56 _ _ = refl
padv-cross-fwd a67 () _
padv-cross-fwd a78 () _
padv-cross-fwd a89 () _

-- the `a01` hand-off out of `cp6` lands on `pp1`, which is NOT forwarded
padv-pp0-notFwd : {b : Block₃} {q : ProdPh} → ProdAdv pp0 q → RelayFwd (producing b q) → ⊥
padv-pp0-notFwd a01 ()

-- (T1) the ONLY produce adjacency LANDING at `pp4` is `a34`
padv-into-pp4 : {pp pp′ : ProdPh} → ProdAdv pp pp′ → pp′ ≡ pp4 → pp ≡ pp3
padv-into-pp4 a01 ()
padv-into-pp4 a12 ()
padv-into-pp4 a23 ()
padv-into-pp4 a34 _ = refl
padv-into-pp4 a45 ()
padv-into-pp4 a56 ()
padv-into-pp4 a67 ()
padv-into-pp4 a78 ()
padv-into-pp4 a89 ()

-- (T2) the ONLY produce adjacency LANDING at `pp5` is `a45`
padv-into-pp5 : {pp pp′ : ProdPh} → ProdAdv pp pp′ → pp′ ≡ pp5 → pp ≡ pp4
padv-into-pp5 a01 ()
padv-into-pp5 a12 ()
padv-into-pp5 a23 ()
padv-into-pp5 a34 ()
padv-into-pp5 a45 _ = refl
padv-into-pp5 a56 ()
padv-into-pp5 a67 ()
padv-into-pp5 a78 ()
padv-into-pp5 a89 ()

-- (T5) the ONLY produce adjacency LANDING at `pp1` is `a01` — so a step that lands
-- the driver at `pp1` fired `pp0`'s single row, whatever the source looked like
padv-into-pp1 : {pp pp′ : ProdPh} → ProdAdv pp pp′ → pp′ ≡ pp1 → pp ≡ pp0
padv-into-pp1 a01 _ = refl
padv-into-pp1 a12 ()
padv-into-pp1 a23 ()
padv-into-pp1 a34 ()
padv-into-pp1 a45 ()
padv-into-pp1 a56 ()
padv-into-pp1 a67 ()
padv-into-pp1 a78 ()
padv-into-pp1 a89 ()

-- (T6d) the ONLY produce adjacency LANDING at `pp2` is `a12` — so a step that lands
-- the driver at `pp2` fired `pp1`'s single row, whatever the source looked like
padv-into-pp2 : {pp pp′ : ProdPh} → ProdAdv pp pp′ → pp′ ≡ pp2 → pp ≡ pp1
padv-into-pp2 a01 ()
padv-into-pp2 a12 _ = refl
padv-into-pp2 a23 ()
padv-into-pp2 a34 ()
padv-into-pp2 a45 ()
padv-into-pp2 a56 ()
padv-into-pp2 a67 ()
padv-into-pp2 a78 ()
padv-into-pp2 a89 ()

-- (T11b) the ONLY produce adjacency LANDING at `pp3` is `a23` — so a step that lands
-- the driver at `pp3` fired `pp2`'s single row.  `padv-into-pp2`'s clause set one
-- event on
padv-into-pp3 : {pp pp′ : ProdPh} → ProdAdv pp pp′ → pp′ ≡ pp3 → pp ≡ pp2
padv-into-pp3 a01 ()
padv-into-pp3 a12 ()
padv-into-pp3 a23 _ = refl
padv-into-pp3 a34 ()
padv-into-pp3 a45 ()
padv-into-pp3 a56 ()
padv-into-pp3 a67 ()
padv-into-pp3 a78 ()
padv-into-pp3 a89 ()

-- (T1) the produce phase of a `producing` relay phase is determined
producing-inj : {b b′ : Block₃} {pp pp′ : ProdPh} → producing b pp ≡ producing b′ pp′ → pp ≡ pp′
producing-inj refl = refl

-- (T1) a produce driver at `pp3` has ONE row, `apiBF l d reqBFRange ⟶ …`, so a fire
-- out of it pins the whole observation (key AND range).  Same shape as
-- `decProd-pp5-sbbAt`; the difference is that `pp3`'s head is an INPUT prefix, so
-- there is no `≟` gate on the value and the range is the one RECEIVED.
prod-a34-anchor : (l : Link) (d : Dir) (blk : Block₃)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → SN.decProd l d blk pp3 ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ r ∈ ChainRange ] (evLabel X e a ≡ evLabel ChainRange (apiBF l d reqBFRange) r)
prod-a34-anchor l d blk {X} {e} {a} (sVis refl br)
  with Net_Api-≟ {Payload} (ChainRange , apiBF l d reqBFRange) (X , e)
... | no  _    = ⊥-elim (nothing-absurd br)
... | yes refl = a , refl

-- (T2) a produce driver at `pp4` has ONE row, `apiBF l d sendBFStartBatch ! U.tt`,
-- so a fire out of it pins the observation to that key and tag.  Same shape as
-- `prod-a34-anchor`; the difference is that `pp4`'s head is an OUTPUT prefix, and no
-- value gate is read at all — the pin is stated at the fired value itself, which is
-- all the `pp5` landing needs (`ApiBFCar sendBFStartBatch` is `⊤`).
prod-a45-anchor : (l : Link) (d : Dir) (blk : Block₃)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → SN.decProd l d blk pp4 ─[ ev (evl (evLabel X e a)) ]─► M
  → SbAt l d e a
prod-a45-anchor l d blk {X} {e} {a} (sVis refl br)
  with Net_Api-≟ {Payload} (ApiBFCar sendBFStartBatch , apiBF l d sendBFStartBatch) (X , e)
... | no  _    = ⊥-elim (nothing-absurd br)
... | yes refl = refl

-- (T5) a produce driver at `pp0` has ONE row — `produce`'s own head,
-- `apiCS l d reqCSRequestNext ⟶₀ …` (`FourNodeDiamond:201-202`) — so a fire out of it
-- pins the observation to that key and tag.  `prod-a45-anchor`'s shape at the chain's
-- FIRST event; the carrier is `ApiCSCar reqCSRequestNext` and no value gate is read,
-- so the pin is stated at the fired value itself.
prod-a01-anchor : (l : Link) (d : Dir) (blk : Block₃)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → SN.decProd l d blk pp0 ─[ ev (evl (evLabel X e a)) ]─► M
  → CsrAt l d e a
prod-a01-anchor l d blk {X} {e} {a} (sVis refl br)
  with Net_Api-≟ {Payload} (ApiCSCar reqCSRequestNext , apiCS l d reqCSRequestNext) (X , e)
... | no  _    = ⊥-elim (nothing-absurd br)
... | yes refl = refl

-- (T6d) a produce driver at `pp1` has ONE row — `apiCS l d sendCSAwaitReply ⟶₀ …`
-- (`SysNode.decProd:801-807`) — so a fire out of it pins the observation to that key
-- and tag.  `prod-a01-anchor`'s shape one event later; the carrier is
-- `ApiCSCar sendCSAwaitReply` (`⊤`) and no value gate is read, so the pin is stated
-- at the fired value itself.
prod-a12-anchor : (l : Link) (d : Dir) (blk : Block₃)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → SN.decProd l d blk pp1 ─[ ev (evl (evLabel X e a)) ]─► M
  → CsaAt l d e a
prod-a12-anchor l d blk {X} {e} {a} (sVis refl br)
  with Net_Api-≟ {Payload} (ApiCSCar sendCSAwaitReply , apiCS l d sendCSAwaitReply) (X , e)
... | no  _    = ⊥-elim (nothing-absurd br)
... | yes refl = refl

-- (T11b) a produce driver at `pp2` has ONE row — `apiCS l d sendCSRollForward !
-- (header blk , tip blk) ⟶ …` (`SysNode.decProd:808-812`) — so a fire out of it pins
-- the observation to that key and tag.  `prod-a12-anchor`'s shape one event later,
-- and `prod-a45-anchor`'s in kind: the head is an OUTPUT prefix, so its offer map has
-- a SECOND gate on the value — never reached, because once `Net_Api-≟` answers
-- `yes refl` the KEY equation the pin states is already `refl`
prod-a23-anchor : (l : Link) (d : Dir) (blk : Block₃)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → SN.decProd l d blk pp2 ─[ ev (evl (evLabel X e a)) ]─► M
  → CsfwAt l d e a
prod-a23-anchor l d blk {X} {e} {a} (sVis refl br)
  with Net_Api-≟ {Payload} (ApiCSCar sendCSRollForward , apiCS l d sendCSRollForward) (X , e)
... | no  _    = ⊥-elim (nothing-absurd br)
... | yes refl = refl

-- *** (T7) THE THREE CONSUME-SIDE ANCHORS, AND WHY THEY ARE LOCAL. ***  The four
-- anchors above are all PRODUCE-side (`decProd`); the `cp5` chain lives on the CONSUME
-- driver, whose only existing anchor is `cons-c34-anchor` — and that one sits in
-- `LTL/Walk/WalkDAnchor` (`:201-210`) because `PipeValRelay` consumes it too.  The three
-- below have no consumer outside this file, so they are built HERE and **no owner grant
-- is involved**: re-derived at this round rather than relayed, `prod-a01-anchor`,
-- `prod-a12-anchor`, `prod-a34-anchor` and `prod-a45-anchor` are all local to this
-- module already, so a local `cons-*` anchor breaks no rule and touches no base module.
--
-- Each is `prod-a45-anchor`'s four lines with the driver, the phase and the tag changed.
-- The three heads are, from `SysNode.decCons` (`:936-957`):
--   `cp1` = `apiCS l d recvCSRollforward ⟶ consume-k l d`               (INPUT prefix)
--   `cp2` = `apiBF l d sendBFRequestRange ! (chainRange …) ⟶ …`        (OUTPUT prefix)
--   `cp4` = `apiBF l d sendBFClientDone ! U.tt ⟶ …`                    (OUTPUT prefix)
-- None of them reports the SUCCESSOR process, unlike `cons-c34-anchor`: the classifier's
-- clauses already get their successors from `consAdv-of`, and the `cp5` chain needs the
-- LABEL only.  `cp3`'s hop reuses `cons-c34-anchor` and converts its `Set₁` label
-- equation with one `cong BfKey`, so this block is three anchors and not four.

-- the consume driver's `cp1 → cp2` hop: the key and tag of the CS-client sync
cons-c12-anchor : (l : Link) (d : Dir) (b : Block₃)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃}
  → SN.decCons l d b cp1 ─[ ev (evl (evLabel X e a)) ]─► M
  → CsfAt l d e a
cons-c12-anchor l d b {X} {e} {a} (sVis refl br)
  with Net_Api-≟ {Payload} (ApiCSCar recvCSRollforward , apiCS l d recvCSRollforward) (X , e)
... | no  _    = ⊥-elim (nothing-absurd br)
... | yes refl = refl

-- *** (A, cellCp3) THE TWO PRE-REQUEST HEADS' OWN ANCHORS, STATED AS THE UP-HOP BF
-- CLIENT's FIXITY rather than as a label pin. ***  `cons-c12-anchor` above hands back
-- `CsfAt`, a `Maybe` equation, and `csfAt⇒ahl` turns that into `ApiHasLink` — which
-- `ahlBF` also inhabits, so it does NOT say the family is ChainSync and the row does
-- not reduce (T11g's measured "each pin wants one more thirty-clause OUT map").  Here
-- the consumer wants ONLY the fixity, so the head inversion spends its own `refl`
-- directly on `CliApiRowP`'s CATCH-ALL: at an `apiCS` label a BF peer has no row at
-- all and the fact IS `bfc ≡ bfc′`.  The row's KEY is left free (`k`/`kd`): the
-- catch-all does not read it
cons-c01-cliFix : (l : Link) (d : Dir) (b : Block₃) (k : Link) (kd : Dir)
                  (bfc bfc′ : BFcPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃}
  → SN.decCons l d b cp0 ─[ ev (evl (evLabel X e a)) ]─► M
  → CliApiRowP k kd bfc bfc′ e a → bfc ≡ bfc′
cons-c01-cliFix l d b k kd bfc bfc′ {X} {e} {a} (sVis refl br) rowP
  with Net_Api-≟ {Payload} (ApiCSCar sendCSRequestNext , apiCS l d sendCSRequestNext) (X , e)
... | no  _    = ⊥-elim (nothing-absurd br)
... | yes refl = rowP

-- … and the `cp1` head's, the same four lines at the other ChainSync tag
cons-c12-cliFix : (l : Link) (d : Dir) (b : Block₃) (k : Link) (kd : Dir)
                  (bfc bfc′ : BFcPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃}
  → SN.decCons l d b cp1 ─[ ev (evl (evLabel X e a)) ]─► M
  → CliApiRowP k kd bfc bfc′ e a → bfc ≡ bfc′
cons-c12-cliFix l d b k kd bfc bfc′ {X} {e} {a} (sVis refl br) rowP
  with Net_Api-≟ {Payload} (ApiCSCar recvCSRollforward , apiCS l d recvCSRollforward) (X , e)
... | no  _    = ⊥-elim (nothing-absurd br)
... | yes refl = rowP

-- … the `cp2 → cp3` hop: the first of the three BlockFetch carrying hops
cons-c23-anchor : (l : Link) (d : Dir) (b : Block₃)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃}
  → SN.decCons l d b cp2 ─[ ev (evl (evLabel X e a)) ]─► M
  → BfAt l d e a
cons-c23-anchor l d b {X} {e} {a} (sVis refl br)
  with Net_Api-≟ {Payload} (ApiBFCar sendBFRequestRange , apiBF l d sendBFRequestRange) (X , e)
... | no  _    = ⊥-elim (nothing-absurd br)
... | yes refl = refl

-- (T11d) … the SAME hop with its VALUE, which `cons-c23-anchor`'s channel-generic
-- `BfAt` drops.  `bfCnxt`'s `sendBFRequestRange` row names the range in its target,
-- so node D's own api class needs the range and not just the channel — and the head
-- is an OUTPUT prefix, so its offer map has a second gate on the value that is never
-- read (`prod-a45-anchor`'s note): the pin is stated at the FIRED value
cons-c23-anchor⁺ : (l : Link) (d : Dir) (b : Block₃)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃}
  → SN.decCons l d b cp2 ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ r ∈ ChainRange ] BrrAt l d r e a
cons-c23-anchor⁺ l d b {X} {e} {a} (sVis refl br)
  with Net_Api-≟ {Payload} (ChainRange , apiBF l d sendBFRequestRange) (X , e)
... | no  _    = ⊥-elim (nothing-absurd br)
... | yes refl = a , refl

-- … and the `cp4 → cp5` hop, the last one before the sub-phase the residual names
cons-c45-anchor : (l : Link) (d : Dir) (b : Block₃)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃}
  → SN.decCons l d b cp4 ─[ ev (evl (evLabel X e a)) ]─► M
  → BfAt l d e a
cons-c45-anchor l d b {X} {e} {a} (sVis refl br)
  with Net_Api-≟ {Payload} (ApiBFCar sendBFClientDone , apiBF l d sendBFClientDone) (X , e)
... | no  _    = ⊥-elim (nothing-absurd br)
... | yes refl = refl

-- LEAF 9's shape at a relay driver: crossing into the forwarded region pins the
-- observation to the relay's own recorded block
RelaySbb : (l₂ : Link) (x x′ : CPPh) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) → Set
RelaySbb l₂ x x′ e a =
  RelayHas x → RelayFwd x′ → Σ[ b″ ∈ Block ] SbbAt l₂ hi b″ e a × RelayAt b″ x

-- *** (T8c-0) THE RELAY DRIVER's OWN PHASE ADVANCE, as this module's classifier
-- answers it — the LANDING-class fact the cone had and did not carry out. ***
--
-- WHY IT LIVES HERE AND NOT DOWNSTREAM.  `RelayStepKind` (the class bundle the four
-- arm records report) provably CANNOT determine this: `RelayStepKind (producing b pp1)
-- (producing b pp0)` is inhabited — `RelayHas` is `⊤` at both, `RelayPre`/`RelayFwd`
-- `⊥` at both — so any consumer needing to separate `pp0` from `pp1` is stuck, and a
-- region-guarded invariant on the relay's phase needs exactly that separation
-- (`LiveDrvCSD` §5e records the four machine-checked refutations).  The determining
-- fact is the driver's STEP, which only this module holds; so the ADVANCE is extracted
-- here, beside `cpStepKindQ-of⁺`'s own answer, and travels as its eighteenth
-- component.
--
-- *** KEEP IN SYNC — `SysNode.decCP:1038-1039`, `WalkMeasure.ConsAdv:274-280` /
-- `ProdAdv:250-259`, and the `cp6` clause of `cpStepKindQ-of⁺` below. ***  NOT
-- `WalkMeasure.CPAdv`: `CPAdv`'s `cpB` is a MEASURE-level hop landing at `pp0`, which
-- no VISIBLE step ever does — the `Ret b >>= produce l₂ hi` collapse fires `produce`'s
-- head on the DOWN link and lands at `producing _ pp1`.  An omitted row makes a
-- downstream class vacuous for a step that really exists.
data RelayAdv : CPPh → CPPh → Set where
  raCons : (b b′ : Block₃) (c c′ : ConsPh) → ConsAdv c c′
         → RelayAdv (consuming b c) (consuming b′ c′)
  raCp6  : (b : Block₃) → RelayAdv (consuming b cp6) (producing b pp1)
  raProd : (b : Block₃) (q q′ : ProdPh) → ProdAdv q q′
         → RelayAdv (producing b q) (producing b q′)

-- *** (T10) A RELAY HOP THAT LANDS AT `cp4` CAME OUT OF `cp3`. ***  `ConsAdv`'s six
-- rows run `cp0 → … → cp6`, so the `cp4` landing has exactly one predecessor — which
-- is what turns the `cp4` client region's ENTERING step into `WUpGate`'s own
-- antecedent at the relay's peel
relayAdv-cp4 : {x x′ : CPPh} (bb : Block₃) → RelayAdv x x′ → x′ ≡ consuming bb cp4
             → Σ[ b ∈ Block₃ ] (x ≡ consuming b cp3)
relayAdv-cp4 bb (raCons b b′ cp0 cp1 c01) ()
relayAdv-cp4 bb (raCons b b′ cp1 cp2 c12) ()
relayAdv-cp4 bb (raCons b b′ cp2 cp3 c23) ()
relayAdv-cp4 bb (raCons b b′ cp3 cp4 c34) refl = b , refl
relayAdv-cp4 bb (raCons b b′ cp4 cp5 c45) ()
relayAdv-cp4 bb (raCons b b′ cp5 cp6 c56) ()
relayAdv-cp4 bb (raCp6 b) ()
relayAdv-cp4 bb (raProd b q q′ padv) ()

-- *** (T10) THE BLOCKFETCH TWIN OF `UpCsDrv`: what a visible api step does to the
-- PAIR (relay driver phase, the leg's UP-hop BF CLIENT). ***  The `cp4` client
-- region reads BOTH of its arms — the fixity carries it across every step at which
-- the relay did not move, and the landing ESTABLISHES it at the one step that enters
-- the region's own sub-phase.
--
-- *** THE SECOND ARM IS A LANDING AND NOT A ROW, for `DnSbLand`'s reason: *** the
-- consumer needs where the row GOES, and keeping the table reading at the bundle
-- (§2b′⁶) is what lets the relay's peel state it already-applied.  ONE arm and not
-- four (unlike `UpCsDrv`'s): the BF client's region is entered at exactly one
-- sub-phase, where the CS client's chain had three carrying hops behind its landing.
-- *** (A, cellCp3) THE RELAY's PRE-REQUEST CONSUME REGION — the three sub-phases
-- BEFORE its up-hop `sendBFRequestRange`. ***  A total dispatch on the relay's phase,
-- so a new sub-phase is a coverage error here; `⊥` everywhere else, including `cp3`,
-- which is where the window's own conclusion sits.  This is the guard of the `cellCp3`
-- window's UP factor and it is LIVE at exactly the positions the premise is stated at
-- (`LiveLegInv:430-431`'s `AtPos l lpUpCell`, whose `RelayPre` enumerates
-- `cp0`/`cp1`/`cp2`/`cp3` — the first three are inside, and `cp3` is the goal)
--
-- (F109  *** THE REGION's UPPER EDGE IS AT `cp2` AND NOT AT `cp3`, and one sub-phase
--      of slack is enough to break it. ***)  set the `cp3` clause to `⊤` — the
--      "obvious" widening, since `cp3` is the window's own conclusion.
--      *** RED ***: `LiveLegApiCone.agda:3334.1-38: [ShouldBeEmpty] UpPre (consuming
--      b′ … cp3) should be empty, but that's not obvious to me … when checking the
--      clause left hand side relayAdv-pre (raCons b b′ _ _ c23) ()`, EXIT=42 — at the
--      REGION-ENTRY lemma, before the producer is even reached: `cp2 → cp3` is the hop
--      that fires `sendBFRequestRange`, so a region containing `cp3` is not entered
--      only from inside itself and the client is NOT fixed across its own request.
--      Reverted by string inversion.
UpPre : CPPh → Set
UpPre (consuming _ cp0) = ⊤
UpPre (consuming _ cp1) = ⊤
UpPre (consuming _ cp2) = ⊤
UpPre (consuming _ cp3) = ⊥
UpPre (consuming _ cp4) = ⊥
UpPre (consuming _ cp5) = ⊥
UpPre (consuming _ cp6) = ⊥
UpPre (producing _ _)   = ⊥

-- … and the region is entered ONLY from inside itself: `ConsAdv`'s six rows land at
-- `cp1 … cp6`, so `cp1` comes out of `cp0` and `cp2` out of `cp1`, and NOTHING lands
-- at `cp0` at all (`RelayAdv` has no row with that target — the relay's loop re-entry
-- is not a visible step, see this datatype's header).  So a hop whose TARGET is in the
-- region has its SOURCE in the region too, which is what lets the carried clause be
-- instantiated at the source state
relayAdv-pre : {x x′ : CPPh} → RelayAdv x x′ → UpPre x′ → UpPre x
relayAdv-pre (raCons b b′ _ _ c01) _  = tt
relayAdv-pre (raCons b b′ _ _ c12) _  = tt
relayAdv-pre (raCons b b′ _ _ c23) ()
relayAdv-pre (raCons b b′ _ _ c34) ()
relayAdv-pre (raCons b b′ _ _ c45) ()
relayAdv-pre (raCons b b′ _ _ c56) ()
relayAdv-pre (raCp6 b)             ()
relayAdv-pre (raProd b q q′ padv)  ()

UpBfDrv : (bfc bfc′ : BFcPos) (x x′ : CPPh) → Set
UpBfDrv bfc bfc′ x x′ =
  ( ((x ≡ x′) × (bfc ≡ bfc′))
    ⊎ ((b : Block₃) → x′ ≡ consuming b cp4
       → (coarsenBFc bfc′ ≡ NS.bcStream) × BFcHasBlk bfc) )
  -- *** (A, cellCp3) TRAILING, AND A `×` RATHER THAN A THIRD `⊎` ARM: THE PRE-REQUEST
  -- HOPS' CLIENT FIXITY, source-and-target. ***  The two arms above cannot state it:
  -- the fixity arm is a CONJUNCTION with the relay's own phase equation, and the `cp0
  -- → cp1` / `cp1 → cp2` hops MOVE the phase.  Reported at the FINE positions (T11h's
  -- rule) and stated SOURCE-AND-TARGET (T10's) so the consumer needs no `RelayAdv` of
  -- its own — every producer holds one and `relayAdv-pre` is one application.
  -- *** SHARPENING THIS SLOT rather than appending a twenty-fifth `BundleApiEvo`
  -- component is what keeps the record at 24 slots: the enumeration the new fact needs
  -- is the one this slot's producers already perform (T11h's banked law). ***
  × (UpPre x′ → (bfc ≡ bfc′) × UpPre x)

-- … and its ANSWER AT A FIXED NODE, named once so the ten fixity fill sites do not
-- have to be re-cut the next time this slot grows
upBfDrv-fix : (q : BFcPos) (x : CPPh) → UpBfDrv q q x x
upBfDrv-fix q x = inj₁ (refl , refl) , (λ pre → refl , pre)

-- *** (A, cellCp3) THE RELAY-SIDE PRODUCER OF THAT COMPONENT — `bfCliDrvAdj-of`'s
-- `c01`/`c12` argument at the RELAY's decoder instead of node D's. ***  Six of the
-- eight relay advances are refuted by the TARGET (their successor is outside the
-- region); the two that survive fire `apiCS` heads, at which the up-hop BF client's
-- row IS its fixity.  The `>>= produce` bind is crossed by `bind-ev-inv` exactly as
-- `cpStepKindQ-of⁺`'s own clauses cross it
--
-- (F110  *** THE BUNDLE's FIRED ROW IS LOAD-BEARING — the fixity is NOT provable by
--      fiat at the producer. ***)  feed the AB arm `cliApiRow-fix linkAB hi (bfC-AB
--      nb) e a` in place of the bundle's own `cliRow`, i.e. assert the client did not
--      move instead of reading the row that says so.
--      *** RED ***: `LiveLegApiCone.agda:4233.16-69: [UnequalTerms] SN.bfC-AB nb !=
--      bfc′ of type BFcPos … when checking that the expression cliApiRow-fix linkAB hi
--      (NodeStateB.bfC-AB nb) e a has type CliApiRowP linkAB hi (SN.bfC-AB nb) bfc′ e
--      a`, EXIT=42 — the peel's successor position `bfc′` is what the row relates the
--      source to, and only the BUNDLE knows it.  Reverted by string inversion.
upBfPre-relay : (l₁ l₂ : Link) (bfc bfc′ : BFcPos) (x x′ : CPPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → SN.decCP l₁ l₂ x ─[ ev (evl (evLabel X e a)) ]─► M
  → RelayAdv x x′ → CliApiRowP l₁ hi bfc bfc′ e a
  → UpPre x′ → (bfc ≡ bfc′) × UpPre x
upBfPre-relay l₁ l₂ bfc bfc′ _ _ step (raCons b b′ _ _ c01) rowP _
  with bind-ev-inv (λ z → produce l₂ hi z) (SN.decCons l₁ hi b cp0) refl step
... | _ , sc , refl = cons-c01-cliFix l₁ hi b l₁ hi bfc bfc′ sc rowP , tt
upBfPre-relay l₁ l₂ bfc bfc′ _ _ step (raCons b b′ _ _ c12) rowP _
  with bind-ev-inv (λ z → produce l₂ hi z) (SN.decCons l₁ hi b cp1) refl step
... | _ , sc , refl = cons-c12-cliFix l₁ hi b l₁ hi bfc bfc′ sc rowP , tt
upBfPre-relay l₁ l₂ bfc bfc′ _ _ step (raCons b b′ _ _ c23) rowP ()
upBfPre-relay l₁ l₂ bfc bfc′ _ _ step (raCons b b′ _ _ c34) rowP ()
upBfPre-relay l₁ l₂ bfc bfc′ _ _ step (raCons b b′ _ _ c45) rowP ()
upBfPre-relay l₁ l₂ bfc bfc′ _ _ step (raCons b b′ _ _ c56) rowP ()
upBfPre-relay l₁ l₂ bfc bfc′ _ _ step (raCp6 b)             rowP ()
upBfPre-relay l₁ l₂ bfc bfc′ _ _ step (raProd b q q′ padv)  rowP ()

-- *** (T8c-iii) NO PRODUCE HOP LANDS AT `pp0`. ***  `ProdAdv`'s nine rows run
-- `pp0 → pp1 → … → pp9`, so a produce advance's successor is never the region's one
-- producing member.  This is the half of §7's structural finding that the freshness
-- guard needs stated as data rather than as prose
prodAdv-nz : {q q′ : ProdPh} → ProdAdv q q′ → q′ ≡ pp0 → ⊥
prodAdv-nz a01 ()
prodAdv-nz a12 ()
prodAdv-nz a23 ()
prodAdv-nz a34 ()
prodAdv-nz a45 ()
prodAdv-nz a56 ()
prodAdv-nz a67 ()
prodAdv-nz a78 ()
prodAdv-nz a89 ()

-- the relay classifier with LEAF 9 appended as an eighth component
cpStepKindQ-of⁺ : (l₁ l₂ : Link) (x : CPPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → SN.decCP l₁ l₂ x ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ x′ ∈ CPPh ] (M ≡ SN.decCP l₁ l₂ x′) × RelayStepKind x x′
      × (((RelayPre x × RelayHas x′) ⊎ (Σ[ b ∈ Block₃ ] x ≡ consuming b cp3))
         → Σ[ b″ ∈ Block₃ ]
             (evLabel X e a ≡ evLabel Block₃ (apiBF l₁ hi recvBFBlock) b″)
           × (x′ ≡ consuming b″ cp4))
      × (IsSBB (evLabel X e a) → RelayFwd x′)
      × ((RelayPre x → ⊥) → RelayValOK x → RelayValOK x′)
      × ((RelayPre x → ⊥) → (bb : Block₃) → RelayAt bb x → RelayAt bb x′)
      × RelaySbb l₂ x x′ e a
      -- SESSION-55 (P3): the relay's own SOURCE phase.  A `sendBFBlock` fire out
      -- of a relay driver is the produce arm's `pp5` row, and `RelayHas` holds of
      -- the whole producing-pre-send region — the mirror of the fifth component,
      -- which reads the SUCCESSOR off the same `decProd-sbb-pp5`.
      × (IsSBB (evLabel X e a) → RelayHas x)
      -- (T1 / S1) A TENTH: THE `pp3 → pp4` LABEL, read off the SUCCESSOR.  `a34` is
      -- the only produce adjacency landing at `pp4` (`padv-into-pp4`) and `pp3`'s
      -- single row is `apiBF l₂ hi reqBFRange` (`prod-a34-anchor`), so an advance
      -- that LANDS the driver at `producing bb pp4` identifies the fired observation
      -- completely.  Stated off `x′`, like the fourth component's `x′ ≡ consuming b″
      -- cp4`, because the successor side is the one S1's api arm holds: it reads the
      -- relay's position in `s′` off the invariant's own antecedent.  A pure
      -- ADDITION at the END of the `Σ`: every consumer gains one binder.
      × ((bb : Block₃) → x′ ≡ producing bb pp4 → Σ[ r ∈ ChainRange ] RbrAt l₂ hi r e a)
      -- (T2) AN ELEVENTH: THE `pp4 → pp5` LABEL, and the SOURCE phase with it.
      -- `a45` is the only produce adjacency landing at `pp5` (`padv-into-pp5`) and
      -- `pp4`'s single row is `apiBF l₂ hi sendBFStartBatch` (`prod-a45-anchor`), so
      -- an advance that LANDS the driver at `producing bb pp5` identifies the fired
      -- observation completely — AND says the driver was at `pp4` before it, which is
      -- what lets the `pp5` arm of the coupling read the `pp4` clause it carries.
      -- The source block stays EXISTENTIAL on purpose: the arm quantifies the block,
      -- so identifying it would be work nobody buys.  A pure ADDITION at the END.
      × ((bb : Block₃) → x′ ≡ producing bb pp5
         → Σ[ b′ ∈ Block₃ ] (x ≡ producing b′ pp4) × SbAt l₂ hi e a)
      -- (T5) A TWELFTH: THE `pp0 → pp1` LABEL, read off the SUCCESSOR.  `a01` is the
      -- only produce adjacency landing at `pp1` (`padv-into-pp1`) and `pp0`'s single
      -- row is `apiCS l₂ hi reqCSRequestNext` (`prod-a01-anchor`), so an advance that
      -- LANDS the driver at `producing bb pp1` identifies the fired observation
      -- completely.  Unlike the eleventh it needs NO source phase: the CS server's
      -- landing is determined by the row alone (§2b″).  A pure ADDITION at the END.
      × ((bb : Block₃) → x′ ≡ producing bb pp1 → CsrAt l₂ hi e a)
      -- (T6d) A THIRTEENTH: THE `pp1 → pp2` LABEL, read off the SUCCESSOR.  `a12` is
      -- the only produce adjacency landing at `pp2` (`padv-into-pp2`) and `pp1`'s
      -- single row is `apiCS l₂ hi sendCSAwaitReply` (`prod-a12-anchor`), so an
      -- advance that LANDS the driver at `producing bb pp2` identifies the fired
      -- observation completely.  Like the twelfth and unlike the eleventh it needs NO
      -- source phase: the CS server's landing is determined by the row alone (§2b‴).
      -- A pure ADDITION at the END.
      × ((bb : Block₃) → x′ ≡ producing bb pp2 → CsaAt l₂ hi e a)
      -- (T7) A FOURTEENTH: THE `cp1 → cp2` LABEL, read off the SUCCESSOR — and the
      -- FIRST component of this family stated at the CONSUME link `l₁`, because the
      -- `cp5` chain's peer is the leg's UP-hop CS CLIENT.  `cp1`'s single row is
      -- `apiCS l₁ hi recvCSRollforward` (`cons-c12-anchor`), so an advance that LANDS
      -- the driver at `consuming bb cp2` identifies the fired observation completely.
      -- Like the twelfth and thirteenth it needs NO source phase: the client's landing
      -- is determined by the row alone (§2b⁗).
      × ((bb : Block₃) → x′ ≡ consuming bb cp2 → CsfAt l₁ hi e a)
      -- (T7) A FIFTEENTH, SIXTEENTH and SEVENTEENTH: THE THREE CARRYING HOPS
      -- `cp2 → cp3 → cp4 → cp5`, each with its SOURCE PHASE.
      --
      -- *** WHY THESE THREE NEED THE SOURCE AND THE FOURTEENTH DOES NOT. ***  `cp2` is
      -- the chain's LANDING — the step that puts the up client at `ccIdle` — so the row
      -- alone settles it.  The other three sub-phases are reached by BlockFetch api
      -- events that do not touch the CS client at all, so their arms prove `ccIdle` at
      -- `s′` from `ccIdle` at `s`, and that means instantiating the carried clause at
      -- the driver's phase in `s`: the `DnSbLand` situation (eleventh component), and
      -- the freedom BOTH landed CS landings enjoyed is exactly what the `cp5` chain
      -- gives up.  The source BLOCK stays EXISTENTIAL for the eleventh's reason.
      --
      -- *** AND WHY THE SOURCE IS FREE HERE ANYWAY. ***  This dispatch is total on `x`,
      -- so in the clause that answers each of the three the source phase is a LITERAL
      -- pattern — no inversion lemma, no `consAdv-into-cpN` sibling of `padv-into-pp2`.
      -- The label is the channel-generic `BfAt` (§1d) for all three: the arms need only
      -- "the fired label is an `apiBF` one", never which tag.
      × ((bb : Block₃) → x′ ≡ consuming bb cp3
         → Σ[ b′ ∈ Block₃ ] (x ≡ consuming b′ cp2) × BfAt l₁ hi e a)
      × ((bb : Block₃) → x′ ≡ consuming bb cp4
         → Σ[ b′ ∈ Block₃ ] (x ≡ consuming b′ cp3) × BfAt l₁ hi e a)
      × ((bb : Block₃) → x′ ≡ consuming bb cp5
         → Σ[ b′ ∈ Block₃ ] (x ≡ consuming b′ cp4) × BfAt l₁ hi e a)
      -- *** (T8c-0) AN EIGHTEENTH: THE RELAY's OWN PHASE ADVANCE, single-sourced with
      -- `x′`. ***  Every other component of this Σ is a CONSEQUENCE of the step; this
      -- one is the step's own shape, and it is here rather than re-extracted downstream
      -- so that `x′` cannot drift between two dispatches.  A pure ADDITION at the END.
      × RelayAdv x x′
    -- *** (T8c-iii) TRAILING, APPENDED: WHICH LINK THE HOP FIRED ON, correlated with
    -- the hop itself. ***  The api carry's relay branch needs "the DOWN-hop CS server
    -- is fixed across an UP-link relay hop", and neither `RelayAdv` nor `DnCsDrv`'s
    -- landing half says it: `RelayAdv`'s `raCons` carries no link, and the landings are
    -- conditionals on the successor phase that are vacuous at a consume hop.  The
    -- correlation can only be produced HERE, where the hop and the label are known at
    -- the same time — a consumer holding the two separately hits exactly the
    -- impossible-combination trap §8 (i-b) records.  The dichotomy is §7's own
    -- structural finding: an UP-link hop fires on `l₁`, and every other hop lands
    -- OUTSIDE the freshness region (`producing b q` with `q ≢ pp0`)
    × (ApiHasLink l₁ e
       ⊎ (Σ[ bb ∈ Block₃ ] Σ[ qq ∈ ProdPh ]
            (x′ ≡ producing bb qq) × (qq ≡ pp0 → ⊥)))
    -- *** (T11b) A TWENTIETH, TRAILING AND APPENDED: THE `pp2 → pp3` LABEL, read off
    -- the SUCCESSOR. ***  `a23` is the only produce adjacency landing at `pp3`
    -- (`padv-into-pp3`) and `pp2`'s single row is `apiCS l₂ hi sendCSRollForward`
    -- (`prod-a23-anchor`), so an advance that LANDS the driver at `producing bb pp3`
    -- identifies the fired observation completely.  The twelfth and thirteenth
    -- component's shape at the produce driver's THIRD event, and like them it needs NO
    -- source phase: the CS server's landing is determined by the row alone (§2b⁶).
    -- *** A reader that ends its Σ pattern on a NON-wildcard must re-cut (the four
    -- relay-node peels in §7/§8 all end on `lnkR`). ***
    × ((bb : Block₃) → x′ ≡ producing bb pp3 → CsfwAt l₂ hi e a)
cpStepKindQ-of⁺ l₁ l₂ (consuming b cp0) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (SN.decCons l₁ hi b cp0) refl step
... | _ , sc , refl with consAdv-of l₁ hi b cp0 sc
...   | b′ , _ , refl , c01 = consuming b′ cp1 , refl , consAdv→rk c01 , (λ { (inj₁ (_ , hHas)) → ⊥-elim hHas ; (inj₂ (_ , ())) })
                            , (λ sbb → ⊥-elim (decCons-sbb-⊥ l₁ hi b cp0 sc sbb))
                            , (λ _ _ → tt)
                            , (λ nPre _ _ → ⊥-elim (nPre tt))
                            , (λ _ ())
                            , (λ sbb → ⊥-elim (decCons-sbb-⊥ l₁ hi b cp0 sc sbb))
                            , (λ bb ())
                            , (λ bb ())
                            , (λ bb ())
                            , (λ bb ())
                            -- (T7) `c01` lands at `cp1`, so none of the chain's four
                            , (λ bb ())
                            , (λ bb ())
                            , (λ bb ())
                            , (λ bb ())
                            , raCons b b′ _ _ c01
                            , inj₁ (decCons-ev-link l₁ hi b cp0 sc)
                            , (λ bb ())
cpStepKindQ-of⁺ l₁ l₂ (consuming b cp1) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (SN.decCons l₁ hi b cp1) refl step
... | _ , sc , refl with consAdv-of l₁ hi b cp1 sc
...   | b′ , _ , refl , c12 = consuming b′ cp2 , refl , consAdv→rk c12 , (λ { (inj₁ (_ , hHas)) → ⊥-elim hHas ; (inj₂ (_ , ())) })
                            , (λ sbb → ⊥-elim (decCons-sbb-⊥ l₁ hi b cp1 sc sbb))
                            , (λ _ _ → tt)
                            , (λ nPre _ _ → ⊥-elim (nPre tt))
                            , (λ _ ())
                            , (λ sbb → ⊥-elim (decCons-sbb-⊥ l₁ hi b cp1 sc sbb))
                            , (λ bb ())
                            , (λ bb ())
                            , (λ bb ())
                            , (λ bb ())
                            -- (T7) THE `cp5` CHAIN'S LANDING: `c12` is the only consume
                            -- adjacency into `cp2`, and this clause IS it, so the anchor
                            -- reads the key and tag straight off `cp1`'s single row
                            , (λ bb eq → cons-c12-anchor l₁ hi b sc)
                            -- … and it is none of the three CARRYING hops
                            , (λ bb ())
                            , (λ bb ())
                            , (λ bb ())
                            , raCons b b′ _ _ c12
                            , inj₁ (decCons-ev-link l₁ hi b cp1 sc)
                            , (λ bb ())
cpStepKindQ-of⁺ l₁ l₂ (consuming b cp2) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (SN.decCons l₁ hi b cp2) refl step
... | _ , sc , refl with consAdv-of l₁ hi b cp2 sc
...   | b′ , _ , refl , c23 = consuming b′ cp3 , refl , consAdv→rk c23 , (λ { (inj₁ (_ , hHas)) → ⊥-elim hHas ; (inj₂ (_ , ())) })
                            , (λ sbb → ⊥-elim (decCons-sbb-⊥ l₁ hi b cp2 sc sbb))
                            , (λ _ _ → tt)
                            , (λ nPre _ _ → ⊥-elim (nPre tt))
                            , (λ _ ())
                            , (λ sbb → ⊥-elim (decCons-sbb-⊥ l₁ hi b cp2 sc sbb))
                            , (λ bb ())
                            , (λ bb ())
                            , (λ bb ())
                            , (λ bb ())
                            -- (T7) not the landing …
                            , (λ bb ())
                            -- … but the FIRST carrying hop, and the source phase is the
                            -- clause's own LITERAL pattern
                            , (λ bb eq → b , refl , cons-c23-anchor l₁ hi b sc)
                            , (λ bb ())
                            , (λ bb ())
                            , raCons b b′ _ _ c23
                            , inj₁ (decCons-ev-link l₁ hi b cp2 sc)
                            , (λ bb ())
cpStepKindQ-of⁺ l₁ l₂ (consuming b cp3) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (SN.decCons l₁ hi b cp3) refl step
... | _ , sc , refl with cons-c34-anchor l₁ hi b sc
...   | b″ , lbl , refl = consuming b″ cp4 , refl , consAdv→rk c34
                        , (λ _ → b″ , lbl , refl)
                        , (λ sbb → ⊥-elim (decCons-sbb-⊥ l₁ hi b cp3 sc sbb))
                        , (λ nPre _ → ⊥-elim (nPre tt))
                        , (λ nPre _ _ → ⊥-elim (nPre tt))
                        , (λ _ ())
                        , (λ sbb → ⊥-elim (decCons-sbb-⊥ l₁ hi b cp3 sc sbb))
                        , (λ bb ())
                        , (λ bb ())
                        , (λ bb ())
                        , (λ bb ())
                        -- (T7) not the landing, and not the FIRST carrying hop …
                        , (λ bb ())
                        , (λ bb ())
                        -- … but the SECOND, which is the one hop of the three that
                        -- already had an anchor: `cons-c34-anchor`'s `Set₁` label
                        -- equation becomes the channel-generic `BfAt` by one `cong`
                        , (λ bb eq → b , refl , cong BfKey lbl)
                        , (λ bb ())
                        , raCons b b″ _ _ c34
                        , inj₁ (decCons-ev-link l₁ hi b cp3 sc)
                        , (λ bb ())
cpStepKindQ-of⁺ l₁ l₂ (consuming b cp4) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (SN.decCons l₁ hi b cp4) refl step
... | _ , sc , refl = consuming b cp5
                    , cong (λ z → z >>= (λ b′ → produce l₂ hi b′)) (output-ev-inv sc)
                    , consAdv→rk c45 , (λ { (inj₁ (hPre , _)) → ⊥-elim hPre ; (inj₂ (_ , ())) })
                    , (λ sbb → ⊥-elim (decCons-sbb-⊥ l₁ hi b cp4 sc sbb))
                    , (λ _ h → h)
                    , (λ _ _ h → h)
                    , (λ _ ())
                    , (λ sbb → ⊥-elim (decCons-sbb-⊥ l₁ hi b cp4 sc sbb))
                    , (λ bb ())
                    , (λ bb ())
                    , (λ bb ())
                    , (λ bb ())
                    -- (T7) the THIRD and last carrying hop — the one that lands the
                    -- driver at the sub-phase `LiveRelayCS.CSAt`'s residual names
                    , (λ bb ())
                    , (λ bb ())
                    , (λ bb ())
                    , (λ bb eq → b , refl , cons-c45-anchor l₁ hi b sc)
                    , raCons b b _ _ c45
                    , inj₁ (decCons-ev-link l₁ hi b cp4 sc)
                    , (λ bb ())
cpStepKindQ-of⁺ l₁ l₂ (consuming b cp5) step
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (SN.decCons l₁ hi b cp5) refl step
... | _ , sc , refl = consuming b cp6
                    , cong (λ z → z >>= (λ b′ → produce l₂ hi b′))
                           (proj₂ (proj₂ (⟶₀-ev-inv sc)))
                    , consAdv→rk c56 , (λ { (inj₁ (hPre , _)) → ⊥-elim hPre ; (inj₂ (_ , ())) })
                    , (λ sbb → ⊥-elim (decCons-sbb-⊥ l₁ hi b cp5 sc sbb))
                    , (λ _ h → h)
                    , (λ _ _ h → h)
                    , (λ _ ())
                    , (λ sbb → ⊥-elim (decCons-sbb-⊥ l₁ hi b cp5 sc sbb))
                    , (λ bb ())
                    , (λ bb ())
                    , (λ bb ())
                    , (λ bb ())
                    -- (T7) `c56` lands at `cp6`, past the whole chain
                    , (λ bb ())
                    , (λ bb ())
                    , (λ bb ())
                    , (λ bb ())
                    , raCons b b _ _ c56
                    , inj₁ (decCons-ev-link l₁ hi b cp5 sc)
                    , (λ bb ())
cpStepKindQ-of⁺ l₁ l₂ (consuming b cp6) step
  with prodAdv-of l₂ hi b pp0 (step-fcong refl step)
... | _ , refl , a01 = producing b pp1 , refl
                     , rMove (λ ()) (λ _ → tt) (λ ()) (λ { (() , _) })
                     , (λ { (inj₁ (hPre , _)) → ⊥-elim hPre ; (inj₂ (_ , ())) })
                     , (λ sbb → ⊥-elim (pp0≢pp5 (decProd-sbb-pp5 l₂ hi b pp0 (step-fcong refl step) sbb)))
                     , (λ _ h → h)
                     , (λ _ _ h → h)
                     , (λ _ hF → ⊥-elim (padv-pp0-notFwd {b = b} a01 hF))
                     , (λ sbb → ⊥-elim (pp0≢pp5 (decProd-sbb-pp5 l₂ hi b pp0 (step-fcong refl step) sbb)))
                     , (λ bb ())
                     , (λ bb ())
                     -- (T5) THE HAND-OFF IS THE `pp1` LANDING: `cp6`'s step IS `pp0`'s
                     -- own row, so the anchor reads the label straight off it
                     , (λ bb eq → prod-a01-anchor l₂ hi b (step-fcong refl step))
                     -- (T6d) … and it is NOT a `pp2` landing: `a01` lands at `pp1`
                     , (λ bb ())
                     -- (T7) the hand-off leaves the consume chain for good, so none of
                     -- the four `consuming` components can be taken here
                     , (λ bb ())
                     , (λ bb ())
                     , (λ bb ())
                     , (λ bb ())
                     , raCp6 b
                     , inj₂ (b , pp1 , refl , λ ())
                     , (λ bb ())
cpStepKindQ-of⁺ l₁ l₂ (producing b pp) {X} {e} {a} step with prodAdv-of l₂ hi b pp step
... | pp′ , refl , pa = producing b pp′ , refl , prodAdv→rk pa , (λ { (inj₁ (hPre , _)) → ⊥-elim hPre ; (inj₂ (_ , ())) })
                      , (λ sbb → padv-pp5-fwd
                          (subst (λ q → ProdAdv q pp′)
                                 (decProd-sbb-pp5 l₂ hi b pp step sbb) pa))
                      , (λ _ h → h)
                      , (λ _ _ h → h)
                      , (λ hH hF → b
                          , decProd-pp5-sbbAt l₂ hi b
                              (subst (λ q → SN.decProd l₂ hi b q ─[ ev (evl (evLabel X e a)) ]─► _)
                                     (padv-cross-fwd {b = b} pa hH hF) step)
                          , refl)
                      , (λ sbb → subst (λ q → RelayHas (producing b q))
                                       (sym (decProd-sbb-pp5 l₂ hi b pp step sbb)) tt)
                      -- (T1) the landing pins the source phase to `pp3` and the
                      -- anchor reads the range off `pp3`'s single row
                      , (λ bb eq →
                           let pin = prod-a34-anchor l₂ hi b
                                       (subst (λ q → SN.decProd l₂ hi b q
                                                     ─[ ev (evl (evLabel X e a)) ]─► _)
                                              (padv-into-pp4 pa (producing-inj eq)) step)
                           in  proj₁ pin
                             , pin⇒rbrAt l₂ hi (proj₁ pin) e a (proj₂ pin))
                      -- (T2) the landing pins the source phase to `pp4`, and `pp4`'s
                      -- own anchor reads the tag off its single row
                      , (λ bb eq →
                           let src = padv-into-pp5 pa (producing-inj eq)
                           in  b , cong (producing b) src
                             , prod-a45-anchor l₂ hi b
                                 (subst (λ q → SN.decProd l₂ hi b q
                                               ─[ ev (evl (evLabel X e a)) ]─► _)
                                        src step))
                      -- (T5) the `pp1` landing pins the source phase to `pp0` and
                      -- `pp0`'s own anchor reads the key and tag off its single row
                      , (λ bb eq →
                           prod-a01-anchor l₂ hi b
                             (subst (λ q → SN.decProd l₂ hi b q
                                           ─[ ev (evl (evLabel X e a)) ]─► _)
                                    (padv-into-pp1 pa (producing-inj eq)) step))
                      -- (T6d) … and the `pp2` landing pins it to `pp1`, whose own
                      -- anchor reads the key and tag off ITS single row
                      , (λ bb eq →
                           prod-a12-anchor l₂ hi b
                             (subst (λ q → SN.decProd l₂ hi b q
                                           ─[ ev (evl (evLabel X e a)) ]─► _)
                                    (padv-into-pp2 pa (producing-inj eq)) step))
                      -- (T7) the produce arm never re-enters the consume chain, so all
                      -- four of the `cp5` chain's components are refuted by the SHAPE of
                      -- the successor (`producing` against `consuming`) and need no
                      -- adjacency lemma at all
                      , (λ bb ())
                      , (λ bb ())
                      , (λ bb ())
                      , (λ bb ())
                      , raProd b _ _ pa
                      , inj₂ (b , _ , refl , prodAdv-nz pa)
                      -- (T11b) … and the `pp3` landing pins the source phase to
                      -- `pp2`, whose own anchor reads the key and tag off ITS single
                      -- row
                      , (λ bb eq →
                           prod-a23-anchor l₂ hi b
                             (subst (λ q → SN.decProd l₂ hi b q
                                           ─[ ev (evl (evLabel X e a)) ]─► _)
                                    (padv-into-pp3 pa (producing-inj eq)) step))

------------------------------------------------------------------------
-- §7  THE TWO RELAY NODES, ⁺.  Node B owns `dnSrv legBD = bfS-BD`, node C owns
-- `dnSrv legCD = bfS-CD`, so this is where leaf 6's DOWN half and LEAF 9 land.
------------------------------------------------------------------------

-- the leg's DOWNSTREAM server facts across the relay node's own api step
SrvDnFacts : (l : Link) (bfs bfs′ : BFsPos) (x x′ : CPPh)
             {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) → Set₁
SrvDnFacts l bfs bfs′ x x′ {X} e a =
    ((bfs ≡ bfs′) ⊎ ((BFsHasBlk bfs′ → ⊥) ⊎ RelayFwd x′))
  × ((bfs ≡ bfs′) ⊎ BfsSucc l hi bfs′ e a)
  × ((bfs ≡ bfs′) ⊎ (BFsHasBlk bfs → ⊥))
  × (RelayHas x → RelayFwd x′ → (bb : Block₃) → RelayAt bb x → bfs′ ≡ bsBlk1 bb)
  -- SESSION-55 (`LiveTokenExcl` P3): the SOURCE-PHASE field, downstream.  A step
  -- that makes the leg's dn server HOLD is the relay's own forward, so the relay
  -- was still HOLDING before it.
  × ((BFsHasBlk bfs → ⊥) → BFsHasBlk bfs′ → RelayHas x)

-- (P3) the dn SOURCE-PHASE answer, the mirror of `srvGain-up`: the fired arm's
-- successor classification names the `sendBFBlock`, and the relay classifier's own
-- NINTH component reads the driver's source region off it
srvGain-dn : (l : Link) (bfs bfs′ : BFsPos) (x : CPPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → (IsSBB (evLabel X e a) → RelayHas x)
  → (((bfs ≡ bfs′) × (IsSBB (evLabel X e a) → ⊥))
     ⊎ ((BFsHasBlk bfs → ⊥) × SrvSuccA l hi e a bfs′ × SrvLands l hi e a bfs′))
  → (BFsHasBlk bfs → ⊥) → BFsHasBlk bfs′ → RelayHas x
srvGain-dn l bfs bfs′ x hasR (inj₁ (eq , _)) ¬h h =
  ⊥-elim (¬h (subst BFsHasBlk (sym eq) h))
srvGain-dn l bfs bfs′ x hasR (inj₂ (_ , inj₁ nb , _)) ¬h h = ⊥-elim (nb h)
srvGain-dn l bfs bfs′ x {e = e} {a} hasR (inj₂ (_ , inj₂ (b″ , sd , _) , _)) ¬h h =
  hasR (proj₁ (sbbAt⇒pin e a sd))

-- assemble `SrvDnFacts` at the FIRED produce bundle
srvDn-of : (l : Link) (bfs bfs′ : BFsPos) (x x′ : CPPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → (IsSBB (evLabel X e a) → RelayFwd x′)
  → (IsSBB (evLabel X e a) → RelayHas x)
  → RelaySbb l x x′ e a
  → (((bfs ≡ bfs′) × (IsSBB (evLabel X e a) → ⊥))
     ⊎ ((BFsHasBlk bfs → ⊥) × SrvSuccA l hi e a bfs′ × SrvLands l hi e a bfs′))
  → SrvDnFacts l bfs bfs′ x x′ e a
srvDn-of l bfs bfs′ x x′ {e = e} {a} fwdR hasR sbb8 (inj₁ (eq , ¬sbb)) =
    srvEvo⇒fwd {l = l} {e = e} {a = a} bfs bfs′ x′ fwdR (inj₁ eq) , inj₁ eq , inj₁ eq
  , (λ hH hF bb rat → ⊥-elim (¬sbb (proj₁ (sbbAt⇒pin e a (proj₁ (proj₂ (sbb8 hH hF)))))))
  , srvGain-dn l bfs bfs′ x hasR (inj₁ (eq , ¬sbb))
srvDn-of l bfs bfs′ x x′ {e = e} {a} fwdR hasR sbb8 (inj₂ (nb , succ , lands)) =
    srvEvo⇒fwd {l = l} {e = e} {a = a} bfs bfs′ x′ fwdR (inj₂ (srvSuccA⇒bfsSucc l hi bfs′ succ))
  , inj₂ (srvSuccA⇒bfsSucc l hi bfs′ succ) , inj₂ nb
  , (λ hH hF bb rat →
       let (b″ , sd , rat″) = sbb8 hH hF
       in subst (λ z → bfs′ ≡ bsBlk1 z)
                (trans (sym (relayAt⇒eq b″ x rat″)) (relayAt⇒eq bb x rat))
                (lands b″ sd))
  , srvGain-dn l bfs bfs′ x hasR (inj₂ (nb , succ , lands))

-- the leg's DOWNSTREAM server facts when the relay node fired on its CONSUME
-- link: the produce bundle is untouched, and LEAF 9 is refuted by the LINK (a
-- crossing would pin the observation to the produce link)
srvDn-fix : (l₁ l₂ : Link) (bfs : BFsPos) (x x′ : CPPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → l₁ ≢ l₂ → ApiHasLink l₁ e
  → (IsSBB (evLabel X e a) → RelayFwd x′)
  → RelaySbb l₂ x x′ e a
  → SrvDnFacts l₂ bfs bfs x x′ e a
srvDn-fix l₁ l₂ bfs x x′ {e = e} {a} ne ahl fwdR sbb8 =
    inj₁ refl , inj₁ refl , inj₁ refl
  , (λ hH hF bb rat → ⊥-elim (ne (apiLink-inj ahl
      (proj₁ (proj₂ (sbbAt⇒pin e a (proj₁ (proj₂ (sbb8 hH hF)))))))))
  , (λ ¬h h → ⊥-elim (¬h h))

-- node B's two bundle faces
bunB-AB : SN.NodeStateB → NetProc
bunB-AB nb = absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb)
                        (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)

bunB-BD : SN.NodeStateB → NetProc
bunB-BD nb = absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb)
                        (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)

-- node C's two bundle faces
bunC-AC : SN.NodeStateC → NetProc
bunC-AC nc = absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc)
                        (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)

bunC-CD : SN.NodeStateC → NetProc
bunC-CD nc = absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc)
                        (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)

-- (T1 / S1) the leg's DOWN-hop server against the relay driver's OWN phase, at the
-- relay node's own fields: a step that LANDS the driver at `producing bb pp4` leaves
-- the down server holding the GENUINE `reqBFRange` row at its own key.
--
-- *** WHY THIS AND NOT `SrvApiRowP`. ***  That slot's FIXITY arm is exactly the case
-- S1 must exclude — the relay entering `pp4` fired `reqBFRange` at the down key, so
-- its server MOVED — and only the bundle knows which peer fired.  Assembling it
-- needs the relay classifier's TENTH component (the label) AND §2b′'s bundle slot
-- (the genuine row) at ONE AND THE SAME successor, so it has to be built here: one
-- layer up, a second peel would land at a different existential.
DnReqLand : (l : Link) (bfs bfs′ : BFsPos) (x′ : CPPh) → Set
DnReqLand l bfs bfs′ x′ =
  (bb : Block₃) → x′ ≡ producing bb pp4
  → Σ[ r ∈ ChainRange ] SrvApiRow l hi l hi bfs bfs′ reqBFRange r

-- (T2 / S1) … and the leg's DOWN-hop server against the driver's `pp5` sub-phase:
-- a step that LANDS the driver at `producing bb pp5` came out of `pp4` and moved the
-- down server from `bsBusy` to `bsWsb`.
--
-- *** WHY THE SOURCE PHASE TRAVELS WITH IT. ***  `pp5`'s clause of the coupling is a
-- REGION, and the arm proves the region at `s′` from the `pp4` EQUATION at `s` — so
-- it needs the source phase, and only the driver's own classifier knows it
-- (`cpStepKindQ-of⁺`'s eleventh component).  The block is existential for the reason
-- given there.  The server implication is stated rather than applied because the
-- source position is the invariant's own antecedent, not the cone's.
DnSbLand : (l : Link) (bfs bfs′ : BFsPos) (x x′ : CPPh) → Set
DnSbLand l bfs bfs′ x x′ =
  (bb : Block₃) → x′ ≡ producing bb pp5
  → Σ[ b′ ∈ Block₃ ] (x ≡ producing b′ pp4)
      × (coarsenBFs bfs ≡ NS.bsBusy → coarsenBFs bfs′ ≡ NS.bsWsb)

-- *** (T11h) THE RELAY SUB-PHASES AT OR PAST ITS DOWN `reqBFRange` EMIT *** — the
-- complement of `LiveDrvBFD.RelayFreshBF` on the producing phases, stated HERE because
-- the cone cannot see downstream and the peel arms are where the phase is a literal.
--
-- *** KEEP IN SYNC WITH `LiveDrvBFD.RelayFreshBF` (`:241-252`). ***  The two are the
-- same eleven-way dispatch with opposite polarity, duplicated because this module is
-- UPSTREAM and cannot import the region.  A change to either extent must touch both.
-- *** THE DRIFT IS MACHINE-CAUGHT: *** `LiveDrvBFD.pastAreq-⊮` (`:324-335`) is
-- exhaustive on `ProdPh` in BOTH polarities, so a flip here alone kills one of its
-- patterns and `LiveDrvBFD` goes RED.  (T12 added this banner: the fact was
-- cross-referenced in prose at both ends but the campaign's own grep target — the
-- literal `KEEP IN SYNC` — matched neither site.)
PastAreq : ProdPh → Set
PastAreq pp0 = ⊥
PastAreq pp1 = ⊥
PastAreq pp2 = ⊥
PastAreq pp3 = ⊥
PastAreq pp4 = ⊤
PastAreq pp5 = ⊤
PastAreq pp6 = ⊤
PastAreq pp7 = ⊤
PastAreq pp8 = ⊤
PastAreq pp9 = ⊤

-- *** (T11h) THE ONE COMBINATION `DnSrvDrv`'s TWO LANDINGS LEAVE OPEN — and it is §8
-- (i-b)'s defect at the BlockFetch server. ***  `DnReqLand`/`DnSbLand` are conditionals
-- on the SUCCESSOR being `pp4`/`pp5`, so both are vacuous at the relay's three
-- IN-REGION produce hops (`a01`/`a12`/`a23`) — exactly where a BF freshness region
-- guarded on the relay's phase needs the down server's fixity.  The dichotomy the peel
-- arms can actually supply: either the server is FIXED (the hop fired an `apiCS` label,
-- where the row fact degenerates — `acsAt⇒srvFix` — or the hop fired at the UP key and
-- node B's DOWN bundle is a literal), or the relay LANDED past its own emit, where the
-- guard makes the obligation vacuous.  Stated at POSITIONS, like `DnReqLand`, so node
-- B's and node C's peels carry it directly
DnSrvPre : (bfs bfs′ : BFsPos) (x′ : CPPh) → Set
DnSrvPre bfs bfs′ x′ =
    (bfs ≡ bfs′)
  ⊎ (Σ[ bb ∈ Block₃ ] Σ[ qq ∈ ProdPh ] (x′ ≡ producing bb qq) × PastAreq qq)


-- *** (T11h) THE DOWN-LINK RELAY HOP's OWN ANSWER TO `DnSrvPre`, SHARED BY BOTH RELAY
-- NODES. ***  The classifier's nineteenth component is refuted on its UP arm by the
-- fired LINK, and then the SUCCESSOR's sub-phase decides: the three in-region produce
-- hops each carry a label PIN whose family is ChainSync (the twelfth, thirteenth and
-- twentieth components), so the bundle's own server row DEGENERATES to its fixity; every
-- later sub-phase is PAST the relay's own `reqBFRange` emit, where the guard is vacuous.
dnSrvPre-dn : (l₁ l₂ : Link) (bfs bfs′ : BFsPos) (x′ : CPPh)
    {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
  → ApiHasLink l₂ e → (l₁ ≡ l₂ → ⊥)
  → SrvApiRowP l₂ hi bfs bfs′ e a
  → (ApiHasLink l₁ e
     ⊎ (Σ[ bb ∈ Block₃ ] Σ[ qq ∈ ProdPh ] (x′ ≡ producing bb qq) × (qq ≡ pp0 → ⊥)))
  → ((bb : Block₃) → x′ ≡ producing bb pp1 → CsrAt l₂ hi e a)
  → ((bb : Block₃) → x′ ≡ producing bb pp2 → CsaAt l₂ hi e a)
  → ((bb : Block₃) → x′ ≡ producing bb pp3 → CsfwAt l₂ hi e a)
  → DnSrvPre bfs bfs′ x′
dnSrvPre-dn l₁ l₂ bfs bfs′ x′ e a ahl ne srow (inj₁ ahl₁) csr csa csfw =
  ⊥-elim (ne (apiLink-inj ahl₁ ahl))
dnSrvPre-dn l₁ l₂ bfs bfs′ x′ e a ahl ne srow (inj₂ (bb , pp0 , peq , nz)) csr csa csfw =
  ⊥-elim (nz refl)
dnSrvPre-dn l₁ l₂ bfs bfs′ x′ e a ahl ne srow (inj₂ (bb , pp1 , peq , _)) csr csa csfw =
  inj₁ (acsAt⇒srvFix l₂ hi bfs bfs′ (csrAt⇒acs e a (csr bb peq)) srow)
dnSrvPre-dn l₁ l₂ bfs bfs′ x′ e a ahl ne srow (inj₂ (bb , pp2 , peq , _)) csr csa csfw =
  inj₁ (acsAt⇒srvFix l₂ hi bfs bfs′ (csaAt⇒acs e a (csa bb peq)) srow)
dnSrvPre-dn l₁ l₂ bfs bfs′ x′ e a ahl ne srow (inj₂ (bb , pp3 , peq , _)) csr csa csfw =
  inj₁ (acsAt⇒srvFix l₂ hi bfs bfs′ (csfwAt⇒acs e a (csfw bb peq)) srow)
dnSrvPre-dn l₁ l₂ bfs bfs′ x′ e a ahl ne srow (inj₂ (bb , pp4 , peq , _)) csr csa csfw =
  inj₂ (bb , pp4 , peq , tt)
dnSrvPre-dn l₁ l₂ bfs bfs′ x′ e a ahl ne srow (inj₂ (bb , pp5 , peq , _)) csr csa csfw =
  inj₂ (bb , pp5 , peq , tt)
dnSrvPre-dn l₁ l₂ bfs bfs′ x′ e a ahl ne srow (inj₂ (bb , pp6 , peq , _)) csr csa csfw =
  inj₂ (bb , pp6 , peq , tt)
dnSrvPre-dn l₁ l₂ bfs bfs′ x′ e a ahl ne srow (inj₂ (bb , pp7 , peq , _)) csr csa csfw =
  inj₂ (bb , pp7 , peq , tt)
dnSrvPre-dn l₁ l₂ bfs bfs′ x′ e a ahl ne srow (inj₂ (bb , pp8 , peq , _)) csr csa csfw =
  inj₂ (bb , pp8 , peq , tt)
dnSrvPre-dn l₁ l₂ bfs bfs′ x′ e a ahl ne srow (inj₂ (bb , pp9 , peq , _)) csr csa csfw =
  inj₂ (bb , pp9 , peq , tt)


-- (T5) … and the leg's DOWN-hop CS SERVER against the driver's `pp1` sub-phase: a
-- step that LANDS the driver at `producing bb pp1` leaves that server AT
-- `csCanAwait`.  The landing is stated already-APPLIED (the position, not the row),
-- because §2b″ does the table reading at the bundle and the `pp1` arm needs nothing
-- else — there is no source-position antecedent, unlike `DnSbLand`'s.
DnCsReqLand : (l : Link) (css css′ : CSsPos) (x′ : CPPh) → Set
DnCsReqLand l css css′ x′ =
  (bb : Block₃) → x′ ≡ producing bb pp1 → coarsenCSs css′ ≡ NS.csCanAwait

-- (T6d) … and the SECOND CS landing, at the driver's `pp2` sub-phase: a step that
-- LANDS the driver at `producing bb pp2` leaves that server at `csWar`, the `pp2`
-- REGION's entry.  `DnCsReqLand`'s shape at the next event, already-APPLIED for the
-- same reason (§2b‴ does the table reading at the bundle) and — unlike `DnSbLand`'s
-- BF twin — with NO source-phase antecedent, because the CS landing is determined by
-- the row alone.  The `pp2` clause of the coupling is a region, but its ENTRY is a
-- position, so nothing existential travels here either.
--
-- *** FALSIFICATION F41 (T6d) — THE PHASE IS LOAD-BEARING. ***  Restating this at
-- `producing bb pp3` (a wrong-PHASE report, arity-preserving) goes RED at the cone's
-- own producer, `:2428.55-57: [UnequalTerms] pp3 != pp2 of type ProdPh … when checking
-- that the expression eq has type x′ ≡ producing bb pp2`, EXIT=42 — because the
-- THIRTEENTH classifier component is pinned at `pp2` by `padv-into-pp2`, so the two
-- halves of the landing cannot drift apart silently.  (F42 at `LiveDrvBF` §6 guards
-- the region this establishes; F43 at `LiveRelayCS` §7 guards its discharge.)
DnCsAwLand : (l : Link) (css css′ : CSsPos) (x′ : CPPh) → Set
DnCsAwLand l css css′ x′ =
  (bb : Block₃) → x′ ≡ producing bb pp2 → coarsenCSs css′ ≡ NS.csWar

-- (T11b) … and the THIRD CS landing, at the driver's `pp3` sub-phase: a step that
-- LANDS the driver at `producing bb pp3` leaves that server at `csWrf ht`, the `pp3`
-- REGION's entry.  `DnCsAwLand`'s shape at the next event, already-APPLIED for the
-- same reason (§2b⁶ does the table reading at the bundle) and with NO source-phase
-- antecedent — but for §2b⁶'s own reason, not `DnCsAwLand`'s: the tag has TWO table
-- rows and they AGREE, both landing at `csWrf` of the fired value.
--
-- *** WHY IT IS EXISTENTIAL WHERE ITS TWO SIBLINGS ARE POSITIONS. ***  `csWrf` is a
-- CONSTRUCTOR APPLICATION (`NodeSpecs:401`), and the `Header × Tip` it carries is the
-- value the relay's own driver emitted — which no consumer of this landing quantifies
-- over.  So the pair travels existentially, exactly as `DnSbLand`'s source block does.
--
-- *** FALSIFICATION F100 (T11b) — THE PHASE IS LOAD-BEARING, exactly as F41 records
-- it for the `pp2` sibling. ***  Restating this at `producing bb pp2` (a wrong-PHASE
-- report, arity-preserving) goes RED at the cone's own producer:
-- `:3822.57-59: [UnequalTerms] pp2 != pp3 of type ProdPh … when checking that the
-- expression eq has type x′ ≡ producing bb pp3`, EXIT=42 — because the TWENTIETH
-- classifier component is pinned at `pp3` by `padv-into-pp3`, so the two halves of
-- the landing cannot drift apart silently.  Reverted by string inversion,
-- `git status` clean after.  (F41 is the same mutation at `pp2`, F44 at `cp2`.)
DnCsRfwLand : (l : Link) (css css′ : CSsPos) (x′ : CPPh) → Set
DnCsRfwLand l css css′ x′ =
  (bb : Block₃) → x′ ≡ producing bb pp3
  → Σ[ ht ∈ ApiCSCar sendCSRollForward ] coarsenCSs css′ ≡ NS.csWrf ht

-- *** (T7) THE `cp5` CHAIN'S LANDING, AT THE LEG'S UP-HOP CS CLIENT. ***  A step that
-- LANDS the driver at `consuming bb cp2` leaves that client AT `ccIdle`.  `DnCsReqLand`'s
-- shape with the hop and the peer ROLE swapped — the chain's peer is the relay's own CS
-- CLIENT on its UP link, where all four landed CS/BF landings watch a DOWN-hop server —
-- and already-APPLIED for `DnCsReqLand`'s reason: §2b⁗ does the table reading at the
-- bundle, and the `cp2` landing carries no source-phase antecedent because the row alone
-- determines the target.
--
-- *** FALSIFICATION F44 (T7) — THE PHASE IS LOAD-BEARING, AS AT `pp2`. ***  Restating
-- this at `consuming bb cp3` (a wrong-PHASE report, arity-preserving) goes RED at the
-- cone's own producer: `:2869.38-40: [UnequalTerms] cp3 != cp2 of type ConsPh … when
-- checking that the expression eq has type x′ ≡ consuming bb cp2`, EXIT=42 — *** the
-- mutant reported `:2869`, before this record's own prose grew ABOVE the site it
-- describes; the COLUMNS (38-40) are exact, and F12 declares the same drift in its own
-- text at `LiveRelayCS` §7 *** — because the
-- FOURTEENTH classifier component is pinned at `cp2` by
-- the `cp1` clause's own literal pattern, so the two halves of the landing cannot drift
-- apart silently.  (F41 is the same mutation at `pp2`; F45 guards the carrying hops, F46
-- the tag/carrier pairing at §2b⁗ and F47 the discharge.)
UpCsRfLand : (l : Link) (csc csc′ : CScPos) (x′ : CPPh) → Set
UpCsRfLand l csc csc′ x′ =
  (bb : Block₃) → x′ ≡ consuming bb cp2 → coarsenCSc csc′ ≡ NS.ccIdle

-- *** (T7) … AND ONE CARRYING HOP OF THE CHAIN, PHASE-PARAMETRIC. ***  A step that lands
-- the driver at `consuming bb c′` came out of `c` and left the up client WHERE IT WAS.
-- Three instances serve the chain (`cp2→cp3`, `cp3→cp4`, `cp4→cp5`); ONE definition
-- rather than three, because the two phases are the only thing that varies and the
-- conclusion is the same fixity.
--
-- *** WHY THE SOURCE PHASE TRAVELS. ***  `DnSbLand`'s reason exactly: the arm proves the
-- position at `s′` from the position at `s`, so it needs to instantiate the carried
-- clause, and only the driver's own classifier knows which sub-phase that is.  The source
-- BLOCK is existential because `cp3`'s hop REBINDS it (`decCons`'s `recvBFBlock`
-- continuation) and no arm of the chain mentions it.
UpCsStep : (c c′ : ConsPh) (csc csc′ : CScPos) (x x′ : CPPh) → Set
UpCsStep c c′ csc csc′ x x′ =
  (bb : Block₃) → x′ ≡ consuming bb c′
  → Σ[ b′ ∈ Block₃ ] (x ≡ consuming b′ c) × (csc ≡ csc′)

-- the WIDENED `ldRelay` receive gate (slice D's shape), at a relay node's fields
WUpGate : (x x′ : CPPh) (bfc : BFcPos) → Set
WUpGate x x′ bfc =
  ((RelayPre x × RelayHas x′) ⊎ (Σ[ b ∈ Block₃ ] x ≡ consuming b cp3))
  → BFcHasBlk bfc × (Σ[ bc ∈ Block₃ ] (bfc ≡ bcBlk1 bc) × (x′ ≡ consuming bc cp4))

-- node B's ⁺ api peel result (`NodeBDrv`'s fields, with the leg's DOWNSTREAM
-- server facts in place of the two frozen server components)
NodeBApiEvo : (nb : SN.NodeStateB) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
              (M : NetProc) → Set₁
NodeBApiEvo nb {X} e a M =
  Σ[ nb′ ∈ SN.NodeStateB ] (M ≡ absNodeB nb′)
    × (SN.decNodeB nb ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeB nb′)
    × RelayStepKind (SN.NodeStateB.cp-B nb) (SN.NodeStateB.cp-B nb′)
    × ((SN.NodeStateB.bfC-AB nb ≡ SN.NodeStateB.bfC-AB nb′)
       ⊎ (BFcHasBlk (SN.NodeStateB.bfC-AB nb′) → ⊥))
    × WUpGate (SN.NodeStateB.cp-B nb) (SN.NodeStateB.cp-B nb′) (SN.NodeStateB.bfC-AB nb)
    × SrvDnFacts linkBD (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.bfS-BD nb′)
                 (SN.NodeStateB.cp-B nb) (SN.NodeStateB.cp-B nb′) e a
    × ((RelayPre (SN.NodeStateB.cp-B nb) → ⊥)
       → RelayValOK (SN.NodeStateB.cp-B nb) → RelayValOK (SN.NodeStateB.cp-B nb′))
    × ((RelayPre (SN.NodeStateB.cp-B nb) → ⊥) → (bb : Block₃)
       → RelayAt bb (SN.NodeStateB.cp-B nb) → RelayAt bb (SN.NodeStateB.cp-B nb′))
    -- (P5) grant #6, TRAILING: node B's link-AB KA-client freeze is preserved.
    -- Node B is the ONLY node whose report is needed — the three other nodes are
    -- LITERAL in the api successors (`LiveLegApiExpose.driverExpose⁺`'s arms), so their bundles'
    -- answers are the identity.
    × (IsApiCSBF e → KAcAtHead (SN.NodeStateB.inert-AB nb)
                   → KAcAtHead (SN.NodeStateB.inert-AB nb′))
    -- (grant #8) TRAILING: node B's two tracked BF peers' fired ROWS — leg BD's UP
    -- CLIENT (the relay's own, on link AB) and its DOWN SERVER
    × CliApiRowP linkAB hi (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfC-AB nb′) e a
    × SrvApiRowP linkBD hi (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.bfS-BD nb′) e a
    -- (T1) TRAILING behind those: the `pp4` LANDING at leg BD's down hop
    × DnReqLand linkBD (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.bfS-BD nb′)
                (SN.NodeStateB.cp-B nb′)
    -- (T2) … and the `pp5` one, at the same hop and the same successor
    × DnSbLand linkBD (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.bfS-BD nb′)
               (SN.NodeStateB.cp-B nb) (SN.NodeStateB.cp-B nb′)
    -- (T4) TRAILING behind those, APPENDED: node B's two tracked CS peers' api-axis
    -- adjacency facts — leg BD's UP-hop CS CLIENT (node B's own, on link AB, the
    -- `cp5` slot) and its DOWN-hop CS SERVER (link BD, the `pp1`/`pp2` slot).
    × CScApiRowP linkAB hi (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csC-AB nb′) e a
    × CSsApiRowP linkBD hi (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.csS-BD nb′) e a
    -- (T5) TRAILING behind those: the `pp1` LANDING at leg BD's down-hop CS SERVER
    × DnCsReqLand linkBD (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.csS-BD nb′)
                  (SN.NodeStateB.cp-B nb′)
    -- (T6d) … and the `pp2` one, at the same hop and the same successor
    × DnCsAwLand linkBD (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.csS-BD nb′)
                 (SN.NodeStateB.cp-B nb′)
    -- (T7) TRAILING behind those, APPENDED for the T4 reason: the `cp5` chain at leg
    -- BD's UP-hop CS CLIENT (node B's own, on link AB).  FOUR components — the `cp2`
    -- LANDING and the three carrying hops — because only the first sub-phase is a
    -- landing (see `UpCsDrv`'s header)
    × UpCsRfLand linkAB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csC-AB nb′)
                 (SN.NodeStateB.cp-B nb′)
    × UpCsStep cp2 cp3 (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csC-AB nb′)
               (SN.NodeStateB.cp-B nb) (SN.NodeStateB.cp-B nb′)
    × UpCsStep cp3 cp4 (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csC-AB nb′)
               (SN.NodeStateB.cp-B nb) (SN.NodeStateB.cp-B nb′)
    × UpCsStep cp4 cp5 (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csC-AB nb′)
               (SN.NodeStateB.cp-B nb) (SN.NodeStateB.cp-B nb′)
    -- *** (T8c-0) TRAILING, APPENDED: the relay driver's own PHASE ADVANCE. ***  The
    -- arm's `RelayStepKind` provably cannot determine it (see `RelayAdv`'s header), and
    -- a region-guarded invariant on the relay's phase needs exactly what it cannot say.
    -- Carried in the SAME arm as everything else for the standing reason: one relay step
    -- is one driver advance.
    × RelayAdv (SN.NodeStateB.cp-B nb) (SN.NodeStateB.cp-B nb′)
    -- *** (T8c-iii) TRAILING, APPENDED — the classifier's nineteenth component carried
    -- out: WHICH LINK this relay hop fired on, correlated with the hop.  See the
    -- classifier for why the correlation cannot be re-made downstream. ***
    × (ApiHasLink linkAB e
       ⊎ (Σ[ bb ∈ Block₃ ] Σ[ qq ∈ ProdPh ]
            (SN.NodeStateB.cp-B nb′ ≡ producing bb qq) × (qq ≡ pp0 → ⊥)))
    -- *** (T10) TRAILING, APPENDED: the leg's UP-hop BF CLIENT against the relay's
    -- own phase — the `cp4` client region's whole api class.  Stated at the node
    -- FIELDS (like `DnCsDrv`/`UpCsDrv`) so the consumer's per-leg selector is what
    -- makes the two forms convertible
    × UpBfDrv (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfC-AB nb′)
              (SN.NodeStateB.cp-B nb) (SN.NodeStateB.cp-B nb′)
    -- (T11b) TRAILING, APPENDED for the T4 reason: the `pp3` LANDING at leg BD's
    -- down-hop CS SERVER — `DnCsDrv`'s third landing member.  Appended rather than
    -- placed beside its two siblings for the standing reason: an insertion is the
    -- type-DUPLICATING shift the T3b review named, and the consumer re-assembles the
    -- triple from three named binders anyway
    × DnCsRfwLand linkBD (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.csS-BD nb′)
                  (SN.NodeStateB.cp-B nb′)
    -- *** (T11h) TRAILING, APPENDED: THE DOWN-HOP BF SERVER AT THE RELAY's THREE
    -- IN-REGION PRODUCE HOPS *** — `DnSrvDrv`'s new third member, and the one fact its
    -- two landings cannot state (see `DnSrvPre`).  Appended rather than placed beside
    -- the BF landings for the standing Σ reason
    × DnSrvPre (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.bfS-BD nb′) (SN.NodeStateB.cp-B nb′)

-- firing link = linkAB (node B's CONSUME leg, LEFT bundle)
nodeB-api-AB-evo⁺ : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
                    {B₁ D₁ : NetProc}
  → apiES .mem (X , e) a
  → (bunB-AB nb ⦀ bunB-BD nb) ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb) ─[ ev (evl (evLabel X e a)) ]─► D₁
  → ApiHasLink linkAB e
  → NodeBApiEvo nb e a (B₁ ∥⇘ apiES ⇙ D₁)
nodeB-api-AB-evo⁺ nb {X} {e} {a} apimem bStep dStep ahl
  with cpStepKindQ-of⁺ linkAB linkBD (SN.NodeStateB.cp-B nb) dStep
-- (T7) four more binders: `cpStepKindQ-of⁺` grew the `cp5` chain's landing and its
-- three carrying hops (components fourteen to seventeen)
... | x′ , refl , rk , lblR , fwdR , rval , blkR , sbb8 , hasR , reqR , sbR , csrR , csaR
    , csfR , c3R , c4R , c5R , raR , lnkR
    -- (T11b) one more binder: the classifier grew the `pp3` landing's LABEL PIN as
    -- its TWENTIETH component, and this reader ended on a NON-wildcard
    , csfwR
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (bunB-AB nb) (bunB-BD nb) bStep
...   | PEA.evSync () _ _
...   | PEA.evR _ sBBD = ⊥-elim (absBundleG-api-no linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) ahl linkAB≢linkBD apimem (_ , sBBD))
...   | PEA.evBoth _ _ sBBD = ⊥-elim (absBundleG-api-no linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) ahl linkAB≢linkBD apimem (_ , sBBD))
...   | PEA.evL _ sBAB
      with absBundleG-api-evo⁺ linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) apimem sBAB
-- (T7) re-cut to BIND the fourteenth component: this arm's bundle IS the leg's UP one,
-- so §2b⁗'s client landing is exactly the `cp2` LANDING the `cp5` chain enters at.
-- (T8c-ii) … and re-cut AGAIN, by one trailing `_`, because §2b⁵'s sharpening was
-- appended as the twentieth component and this reader ended on a NON-wildcard.  The
-- fact itself is node D's business, not this relay's — the banked Σ-append trap
...     | csc′ , css′ , bfc′ , bfs′ , ip′ , eq , run , cliE , _ , frz , cliRow , _ , _ , _ , cscRow , _ , _ , _ , cscRfl , _ , _ , recvLand , _ , _ =
          SN.mkNodeB csc′ css′ bfc′ bfs′ (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) x′ ip′ (SN.NodeStateB.inert-BD nb)
        , cong (λ z → (z ⦀ bunB-BD nb) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD x′) eq
        , ∥⇘⇙-wev-sync apiES _ _ apimem
            (⦀-wev-L _ _ (noOffer→viewV _ (bundleG-api-no linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) ahl linkAB≢linkBD apimem)) run)
            (ev→wev dStep)
        , rk , cliE
        , (λ w → bundle-recvBFBlock-forces-src linkAB hi lo (λ ())
                   (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
                   (subst (λ z → bunB-AB nb ─[ ev (evl z) ]─► _) (proj₁ (proj₂ (lblR w))) sBAB)
               , proj₁ (lblR w)
               , bundle-recv-cliPos linkAB hi lo (λ ())
                   (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
                   (subst (λ z → bunB-AB nb ─[ ev (evl z) ]─► _) (proj₁ (proj₂ (lblR w))) sBAB)
               , proj₂ (proj₂ (lblR w)))
        , srvDn-fix linkAB linkBD (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) x′ linkAB≢linkBD ahl fwdR sbb8
        , rval , blkR
        -- grant #6: the AB bundle IS the fired one, so its answer is the bundle's
        , frz
        -- (grant #8) AB fired ⇒ the UP client's row is the bundle's; the DOWN
        -- server sits in the untouched BD bundle
        , cliRow , srvApiRow-fix linkBD hi (SN.NodeStateB.bfS-BD nb) e a
        -- (T1) AB fired, so a `pp4` landing is refuted by the LINK: `reqBFRange`
        -- would have been fired at the DOWN key
        , (λ bb eq → ⊥-elim (linkAB≢linkBD
             (apiLink-inj ahl (proj₁ (rbrAt⇒pin e a (proj₂ (reqR bb eq)))))))
        -- (T2) … and a `pp5` landing likewise: `sendBFStartBatch` would have been
        -- fired at the DOWN key
        , (λ bb eq → ⊥-elim (linkAB≢linkBD
             (apiLink-inj ahl (sbAt⇒ahl e a (proj₂ (proj₂ (sbR bb eq)))))))
        -- (T4) AB fired ⇒ the UP CS CLIENT's row is the bundle's; the DOWN CS
        -- SERVER sits in the untouched BD bundle
        , cscRow , cssApiRow-fix linkBD hi (SN.NodeStateB.csS-BD nb) e a
        -- (T5) AB fired, so a `pp1` landing is refuted by the LINK:
        -- `reqCSRequestNext` would have been fired at the DOWN key
        , (λ bb eq → ⊥-elim (linkAB≢linkBD
             (apiLink-inj ahl (acsAt⇒ahl (csrAt⇒acs e a (csrR bb eq))))))
        -- (T6d) … and a `pp2` landing likewise: `sendCSAwaitReply` would have been
        -- fired at the DOWN key
        , (λ bb eq → ⊥-elim (linkAB≢linkBD
             (apiLink-inj ahl (acsAt⇒ahl (csaAt⇒acs e a (csaR bb eq))))))
        -- (T7) AB fired, and THIS bundle is the leg's UP one — so unlike the four
        -- landings above, the `cp5` chain's arms CARRY here.  The `cp2` landing is
        -- §2b⁗'s slot at the classifier's own pin; the three hops are the client's
        -- FIXITY at an `apiBF` label, which §1d reads off the bundle's row slot
        , (λ bb eq → cscRfl (csfR bb eq))
        , (λ bb eq → proj₁ (c3R bb eq) , proj₁ (proj₂ (c3R bb eq))
                   , bfAt⇒cscFix linkAB hi (SN.NodeStateB.csC-AB nb) csc′ e a
                       (proj₂ (proj₂ (c3R bb eq))) cscRow)
        , (λ bb eq → proj₁ (c4R bb eq) , proj₁ (proj₂ (c4R bb eq))
                   , bfAt⇒cscFix linkAB hi (SN.NodeStateB.csC-AB nb) csc′ e a
                       (proj₂ (proj₂ (c4R bb eq))) cscRow)
        , (λ bb eq → proj₁ (c5R bb eq) , proj₁ (proj₂ (c5R bb eq))
                   , bfAt⇒cscFix linkAB hi (SN.NodeStateB.csC-AB nb) csc′ e a
                       (proj₂ (proj₂ (c5R bb eq))) cscRow)
                       , raR
                       , lnkR
        -- *** (T10) AB fired, and THIS bundle is the leg's UP one — so the `cp4`
        -- landing CARRIES here.  The classifier's advance says a `cp4` landing came
        -- out of `cp3`, which is `WUpGate`'s own antecedent; the gate hands back the
        -- delivered block and the label pin; the bundle's own `recvBFBlock` landing
        -- (§2b′⁶) turns that pin plus the source position into the successor's
        , ( inj₂ (λ bb heq →
              let w   = inj₂ (proj₁ (relayAdv-cp4 bb raR heq)
                             , proj₂ (relayAdv-cp4 bb raR heq))
                  lbl = proj₁ (proj₂ (lblR w))
                  bc  = proj₁ (lblR w)
                  src = bundle-recv-cliPos linkAB hi lo (λ ())
                          (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb)
                          (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
                          (SN.NodeStateB.inert-AB nb)
                          (subst (λ z → bunB-AB nb ─[ ev (evl z) ]─► _) lbl sBAB)
              in  recvLand bc (rpin⇒rbbAt linkAB hi bc e a lbl) (cong coarsenBFc src)
                , subst BFcHasBlk (sym src) tt)
          -- *** (A, cellCp3) … and the PRE-REQUEST component: AB fired, so this arm's
          -- `dStep` IS the relay's own hop and `cliRow` its up client's row ***
          , upBfPre-relay linkAB linkBD (SN.NodeStateB.bfC-AB nb) bfc′
              (SN.NodeStateB.cp-B nb) x′ dStep raR cliRow )
        -- (T11b) AB fired, so the `pp3` landing is refuted by the LINK, exactly as
        -- the `pp1` and `pp2` ones are: `sendCSRollForward` would have been fired
        -- at the DOWN key
        , (λ bb eq → ⊥-elim (linkAB≢linkBD
             (apiLink-inj ahl (acsAt⇒ahl (csfwAt⇒acs e a (csfwR bb eq))))))
        -- (T11h) AB/AC fired, so the DOWN bundle — where the leg's dn BF SERVER lives —
        -- is a LITERAL: the new third member is `refl`
        , inj₁ refl

-- firing link = linkBD (node B's PRODUCE leg, RIGHT bundle)
nodeB-api-BD-evo⁺ : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
                    {B₁ D₁ : NetProc}
  → apiES .mem (X , e) a
  → (bunB-AB nb ⦀ bunB-BD nb) ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb) ─[ ev (evl (evLabel X e a)) ]─► D₁
  → ApiHasLink linkBD e
  → NodeBApiEvo nb e a (B₁ ∥⇘ apiES ⇙ D₁)
nodeB-api-BD-evo⁺ nb {X} {e} {a} apimem bStep dStep ahl
  with cpStepKindQ-of⁺ linkAB linkBD (SN.NodeStateB.cp-B nb) dStep
-- (T7) four more binders: `cpStepKindQ-of⁺` grew the `cp5` chain's landing and its
-- three carrying hops (components fourteen to seventeen)
... | x′ , refl , rk , lblR , fwdR , rval , blkR , sbb8 , hasR , reqR , sbR , csrR , csaR
    , csfR , c3R , c4R , c5R , raR , lnkR
    -- (T11b) one more binder: the classifier grew the `pp3` landing's LABEL PIN as
    -- its TWENTIETH component, and this reader ended on a NON-wildcard
    , csfwR
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (bunB-AB nb) (bunB-BD nb) bStep
...   | PEA.evSync () _ _
...   | PEA.evL _ sBAB = ⊥-elim (absBundleG-api-no linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ahl (λ q → linkAB≢linkBD (sym q)) apimem (_ , sBAB))
...   | PEA.evBoth _ sBAB _ = ⊥-elim (absBundleG-api-no linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ahl (λ q → linkAB≢linkBD (sym q)) apimem (_ , sBAB))
...   | PEA.evR _ sBBD
      with absBundleG-api-evo⁺ linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) apimem sBBD
-- (T7) re-cut with one trailing `_`: this reader ended on a NON-wildcard and
-- `BundleApiEvo` grew a FOURTEENTH component (§2b⁗'s client landing), which this arm
-- does not want — the bundle peeled here is the leg's DOWN one, whose CS client is
-- node D's, not the relay's UP-hop one.  (The banked Σ-append trap, fourth sighting.)
...     | csc′ , css′ , bfc′ , bfs′ , ip′ , eq , run , _ , srvE , _ , _ , srvRow , srvReq , srvSb , _ , cssRow , cssReq , cssAw , _ , _ , _ , _ , cssRfw , _ =
          SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) csc′ css′ bfc′ bfs′ x′ (SN.NodeStateB.inert-AB nb) ip′
        , cong (λ z → (bunB-AB nb ⦀ z) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD x′) eq
        , ∥⇘⇙-wev-sync apiES _ _ apimem
            (⦀-wev-R _ _ (noOffer→viewV _ (bundleG-api-no linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ahl (λ q → linkAB≢linkBD (sym q)) apimem)) run)
            (ev→wev dStep)
        , rk , inj₁ refl
        , (λ w → ⊥-elim (absBundleG-api-no linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) ahlBF linkAB≢linkBD tt
                   (_ , subst (λ z → bunB-BD nb ─[ ev (evl z) ]─► _) (proj₁ (proj₂ (lblR w))) sBBD)))
        , srvDn-of linkBD (SN.NodeStateB.bfS-BD nb) bfs′ (SN.NodeStateB.cp-B nb) x′ fwdR hasR sbb8 srvE
        , rval , blkR
        -- grant #6: BD fired, so node B's AB bundle is a LITERAL
        , (λ _ h → h)
        -- (grant #8) … and so is the UP client; the DOWN server's row is the bundle's
        , cliApiRow-fix linkAB hi (SN.NodeStateB.bfC-AB nb) e a , srvRow
        -- (T1) BD fired: the classifier's label and the bundle's own-key row, at the
        -- SAME successor
        , (λ bb eq → proj₁ (reqR bb eq)
                   , srvReq (proj₁ (reqR bb eq)) (proj₂ (reqR bb eq)))
        -- (T2) … and the `pp5` landing: the classifier's source phase and its label,
        -- the bundle's own-key landing at the same successor
        , (λ bb eq → proj₁ (sbR bb eq)
                   , proj₁ (proj₂ (sbR bb eq))
                   , srvSb (proj₂ (proj₂ (sbR bb eq))))
        -- (T4) BD fired ⇒ the DOWN CS SERVER's row is the bundle's; the UP CS
        -- CLIENT is in the untouched AB bundle
        , cscApiRow-fix linkAB hi (SN.NodeStateB.csC-AB nb) e a , cssRow
        -- (T5) BD fired: the classifier's label pin feeds the bundle's own-key
        -- LANDING, and the pair IS the `pp1` arm's antecedent
        , (λ bb eq → cssReq (csrR bb eq))
        -- (T6d) … and the `pp2` pin feeds the OTHER tag's landing, at the same
        -- successor — the region's ENTRY
        , (λ bb eq → cssAw (csaR bb eq))
        -- (T7) BD fired, so node B's AB bundle — which is where the leg's UP-hop CS
        -- CLIENT lives — is a LITERAL: the three carrying hops ride on `refl`, and the
        -- `cp2` LANDING is refuted by the fired LINK, `recvCSRollforward` having to be
        -- fired at the UP key.  *** The polarity is the MIRROR of the four lines above:
        -- there the UP-link arm refutes and the DOWN-link arm carries. ***
        , (λ bb eq → ⊥-elim (linkAB≢linkBD
             (sym (apiLink-inj ahl (csfAt⇒ahl e a (csfR bb eq))))))
        , (λ bb eq → proj₁ (c3R bb eq) , proj₁ (proj₂ (c3R bb eq)) , refl)
        , (λ bb eq → proj₁ (c4R bb eq) , proj₁ (proj₂ (c4R bb eq)) , refl)
        , (λ bb eq → proj₁ (c5R bb eq) , proj₁ (proj₂ (c5R bb eq)) , refl)
        , raR
        , lnkR
        -- (T10) BD fired, so a `cp4` landing is refuted by the LINK: `recvBFBlock`
        -- would have been fired at the UP key (the four landings above's shape)
        , ( inj₂ (λ bb heq →
              let w   = inj₂ (proj₁ (relayAdv-cp4 bb raR heq)
                             , proj₂ (relayAdv-cp4 bb raR heq))
                  lbl = proj₁ (proj₂ (lblR w))
                  bc  = proj₁ (lblR w)
              in  ⊥-elim (linkAB≢linkBD
                    (apiLink-inj (proj₁ (proj₂ (rbbAt⇒pin e a
                                   (rpin⇒rbbAt linkAB hi bc e a lbl)))) ahl)))
          -- *** (A, cellCp3) BD fired, so the AB bundle is a LITERAL and the client's
          -- fixity is `refl`; the source's region membership is the advance's ***
          , (λ pre → refl , relayAdv-pre raR pre) )
        -- (T11b) BD fired, so the `pp3` landing CARRIES here: the classifier's own
        -- pin feeds the bundle's third own-key landing
        , (λ bb eq → cssRfw (csfwR bb eq))
        -- (T11h) BD fired: the new third member is the shared DOWN-link dispatch — the
        -- three in-region produce hops degenerate the bundle's own server row through
        -- their label PINS, and every later hop is past the relay's own emit
        , dnSrvPre-dn linkAB linkBD (SN.NodeStateB.bfS-BD nb) bfs′ x′ e a ahl linkAB≢linkBD srvRow lnkR csrR csaR csfwR

-- node-B api inversion
nodeB-ev-api-evo⁺ : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
                    {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeB nb ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeBApiEvo nb e a M
nodeB-ev-api-evo⁺ nb {X} {e} {a} apimem step
  with SStep.reflect-node-api (bunB-AB nb ⦀ bunB-BD nb)
         (SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb)) apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with decCP-ev-link linkAB linkBD (SN.NodeStateB.cp-B nb) dStep
... | inj₁ ahl = nodeB-api-AB-evo⁺ nb apimem bStep dStep ahl
... | inj₂ ahl = nodeB-api-BD-evo⁺ nb apimem bStep dStep ahl

-- node C's ⁺ api peel result (the mirror: links AC / CD)
NodeCApiEvo : (nc : SN.NodeStateC) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
              (M : NetProc) → Set₁
NodeCApiEvo nc {X} e a M =
  Σ[ nc′ ∈ SN.NodeStateC ] (M ≡ absNodeC nc′)
    × (SN.decNodeC nc ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeC nc′)
    × RelayStepKind (SN.NodeStateC.cp-C nc) (SN.NodeStateC.cp-C nc′)
    × ((SN.NodeStateC.bfC-AC nc ≡ SN.NodeStateC.bfC-AC nc′)
       ⊎ (BFcHasBlk (SN.NodeStateC.bfC-AC nc′) → ⊥))
    × WUpGate (SN.NodeStateC.cp-C nc) (SN.NodeStateC.cp-C nc′) (SN.NodeStateC.bfC-AC nc)
    × SrvDnFacts linkCD (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.bfS-CD nc′)
                 (SN.NodeStateC.cp-C nc) (SN.NodeStateC.cp-C nc′) e a
    × ((RelayPre (SN.NodeStateC.cp-C nc) → ⊥)
       → RelayValOK (SN.NodeStateC.cp-C nc) → RelayValOK (SN.NodeStateC.cp-C nc′))
    × ((RelayPre (SN.NodeStateC.cp-C nc) → ⊥) → (bb : Block₃)
       → RelayAt bb (SN.NodeStateC.cp-C nc) → RelayAt bb (SN.NodeStateC.cp-C nc′))
    -- (grant #8) TRAILING: node C's two tracked BF peers' fired ROWS — leg CD's UP
    -- CLIENT (the relay's own, on link AC) and its DOWN SERVER
    × CliApiRowP linkAC hi (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfC-AC nc′) e a
    × SrvApiRowP linkCD hi (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.bfS-CD nc′) e a
    -- (T1) TRAILING behind those: the `pp4` LANDING at leg CD's down hop
    × DnReqLand linkCD (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.bfS-CD nc′)
                (SN.NodeStateC.cp-C nc′)
    -- (T2) … and the `pp5` one, at the same hop and the same successor
    × DnSbLand linkCD (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.bfS-CD nc′)
               (SN.NodeStateC.cp-C nc) (SN.NodeStateC.cp-C nc′)
    -- (T4) the mirror at node C: leg CD's UP-hop CS CLIENT (link AC) and its
    -- DOWN-hop CS SERVER (link CD)
    × CScApiRowP linkAC hi (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csC-AC nc′) e a
    × CSsApiRowP linkCD hi (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.csS-CD nc′) e a
    -- (T5) TRAILING behind those: the `pp1` LANDING at leg CD's down-hop CS SERVER
    × DnCsReqLand linkCD (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.csS-CD nc′)
                  (SN.NodeStateC.cp-C nc′)
    -- (T6d) … and the `pp2` one, at the same hop and the same successor
    × DnCsAwLand linkCD (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.csS-CD nc′)
                 (SN.NodeStateC.cp-C nc′)
    -- (T7) … and the mirror at node C: the `cp5` chain at leg CD's UP-hop CS CLIENT
    -- (link AC), four components for `NodeBApiEvo`'s reason
    × UpCsRfLand linkAC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csC-AC nc′)
                 (SN.NodeStateC.cp-C nc′)
    × UpCsStep cp2 cp3 (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csC-AC nc′)
               (SN.NodeStateC.cp-C nc) (SN.NodeStateC.cp-C nc′)
    × UpCsStep cp3 cp4 (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csC-AC nc′)
               (SN.NodeStateC.cp-C nc) (SN.NodeStateC.cp-C nc′)
    × UpCsStep cp4 cp5 (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csC-AC nc′)
               (SN.NodeStateC.cp-C nc) (SN.NodeStateC.cp-C nc′)
    -- *** (T8c-0) TRAILING, APPENDED — node B's twin. ***
    × RelayAdv (SN.NodeStateC.cp-C nc) (SN.NodeStateC.cp-C nc′)
    -- *** (T8c-iii) TRAILING, APPENDED — the classifier's nineteenth component carried
    -- out: WHICH LINK this relay hop fired on, correlated with the hop.  See the
    -- classifier for why the correlation cannot be re-made downstream. ***
    × (ApiHasLink linkAC e
       ⊎ (Σ[ bb ∈ Block₃ ] Σ[ qq ∈ ProdPh ]
            (SN.NodeStateC.cp-C nc′ ≡ producing bb qq) × (qq ≡ pp0 → ⊥)))
    -- (T10) … and node C's own, the mirror
    × UpBfDrv (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfC-AC nc′)
              (SN.NodeStateC.cp-C nc) (SN.NodeStateC.cp-C nc′)
    -- (T11b) TRAILING, APPENDED: node B's slot's mirror — the `pp3` LANDING at leg
    -- CD's down-hop CS SERVER
    × DnCsRfwLand linkCD (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.csS-CD nc′)
                  (SN.NodeStateC.cp-C nc′)
    -- *** (T11h) TRAILING, APPENDED: THE DOWN-HOP BF SERVER AT THE RELAY's THREE
    -- IN-REGION PRODUCE HOPS *** — `DnSrvDrv`'s new third member, and the one fact its
    -- two landings cannot state (see `DnSrvPre`).  Appended rather than placed beside
    -- the BF landings for the standing Σ reason
    × DnSrvPre (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.bfS-CD nc′) (SN.NodeStateC.cp-C nc′)

-- firing link = linkAC (node C's CONSUME leg, LEFT bundle)
nodeC-api-AC-evo⁺ : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
                    {B₁ D₁ : NetProc}
  → apiES .mem (X , e) a
  → (bunC-AC nc ⦀ bunC-CD nc) ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc) ─[ ev (evl (evLabel X e a)) ]─► D₁
  → ApiHasLink linkAC e
  → NodeCApiEvo nc e a (B₁ ∥⇘ apiES ⇙ D₁)
nodeC-api-AC-evo⁺ nc {X} {e} {a} apimem bStep dStep ahl
  with cpStepKindQ-of⁺ linkAC linkCD (SN.NodeStateC.cp-C nc) dStep
-- (T7) four more binders: `cpStepKindQ-of⁺` grew the `cp5` chain's landing and its
-- three carrying hops (components fourteen to seventeen)
... | x′ , refl , rk , lblR , fwdR , rval , blkR , sbb8 , hasR , reqR , sbR , csrR , csaR
    , csfR , c3R , c4R , c5R , raR , lnkR
    -- (T11b) one more binder: the classifier grew the `pp3` landing's LABEL PIN as
    -- its TWENTIETH component, and this reader ended on a NON-wildcard
    , csfwR
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (bunC-AC nc) (bunC-CD nc) bStep
...   | PEA.evSync () _ _
...   | PEA.evR _ sBCD = ⊥-elim (absBundleG-api-no linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) ahl linkAC≢linkCD apimem (_ , sBCD))
...   | PEA.evBoth _ _ sBCD = ⊥-elim (absBundleG-api-no linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) ahl linkAC≢linkCD apimem (_ , sBCD))
...   | PEA.evL _ sBAC
      with absBundleG-api-evo⁺ linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) apimem sBAC
-- (T7) re-cut to BIND the fourteenth component, node B's arm's reason exactly
-- (T8c-ii) … and re-cut again by one trailing `_`, node B's arm's reason exactly
...     | csc′ , css′ , bfc′ , bfs′ , ip′ , eq , run , cliE , _ , _ , cliRow , _ , _ , _ , cscRow , _ , _ , _ , cscRfl , _ , _ , recvLand , _ , _ =
          SN.mkNodeC csc′ css′ bfc′ bfs′ (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) x′ ip′ (SN.NodeStateC.inert-CD nc)
        , cong (λ z → (z ⦀ bunC-CD nc) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD x′) eq
        , ∥⇘⇙-wev-sync apiES _ _ apimem
            (⦀-wev-L _ _ (noOffer→viewV _ (bundleG-api-no linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) ahl linkAC≢linkCD apimem)) run)
            (ev→wev dStep)
        , rk , cliE
        , (λ w → bundle-recvBFBlock-forces-src linkAC hi lo (λ ())
                   (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
                   (subst (λ z → bunC-AC nc ─[ ev (evl z) ]─► _) (proj₁ (proj₂ (lblR w))) sBAC)
               , proj₁ (lblR w)
               , bundle-recv-cliPos linkAC hi lo (λ ())
                   (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
                   (subst (λ z → bunC-AC nc ─[ ev (evl z) ]─► _) (proj₁ (proj₂ (lblR w))) sBAC)
               , proj₂ (proj₂ (lblR w)))
        , srvDn-fix linkAC linkCD (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) x′ linkAC≢linkCD ahl fwdR sbb8
        , rval , blkR
        -- (grant #8) AC fired ⇒ the UP client's row is the bundle's, the DOWN
        -- server is in the untouched CD bundle
        , cliRow , srvApiRow-fix linkCD hi (SN.NodeStateC.bfS-CD nc) e a
        -- (T1) the mirror: AC fired, so a `pp4` landing is refuted by the LINK
        , (λ bb eq → ⊥-elim (linkAC≢linkCD
             (apiLink-inj ahl (proj₁ (rbrAt⇒pin e a (proj₂ (reqR bb eq)))))))
        -- (T2) … and a `pp5` landing likewise
        , (λ bb eq → ⊥-elim (linkAC≢linkCD
             (apiLink-inj ahl (sbAt⇒ahl e a (proj₂ (proj₂ (sbR bb eq)))))))
        -- (T4) AC fired ⇒ the UP CS CLIENT's row is the bundle's; the DOWN CS
        -- SERVER is in the untouched CD bundle
        , cscRow , cssApiRow-fix linkCD hi (SN.NodeStateC.csS-CD nc) e a
        -- (T5) AC fired: the `pp1` landing is refuted by the LINK
        , (λ bb eq → ⊥-elim (linkAC≢linkCD
             (apiLink-inj ahl (acsAt⇒ahl (csrAt⇒acs e a (csrR bb eq))))))
        -- (T6d) … and so is the `pp2` one
        , (λ bb eq → ⊥-elim (linkAC≢linkCD
             (apiLink-inj ahl (acsAt⇒ahl (csaAt⇒acs e a (csaR bb eq))))))
        -- (T7) AC fired, and THIS bundle is the leg's UP one, so the `cp5` chain's four
        -- arms CARRY here — node B's own arm's reasons exactly
        , (λ bb eq → cscRfl (csfR bb eq))
        , (λ bb eq → proj₁ (c3R bb eq) , proj₁ (proj₂ (c3R bb eq))
                   , bfAt⇒cscFix linkAC hi (SN.NodeStateC.csC-AC nc) csc′ e a
                       (proj₂ (proj₂ (c3R bb eq))) cscRow)
        , (λ bb eq → proj₁ (c4R bb eq) , proj₁ (proj₂ (c4R bb eq))
                   , bfAt⇒cscFix linkAC hi (SN.NodeStateC.csC-AC nc) csc′ e a
                       (proj₂ (proj₂ (c4R bb eq))) cscRow)
        , (λ bb eq → proj₁ (c5R bb eq) , proj₁ (proj₂ (c5R bb eq))
                   , bfAt⇒cscFix linkAC hi (SN.NodeStateC.csC-AC nc) csc′ e a
                       (proj₂ (proj₂ (c5R bb eq))) cscRow)
                       , raR
                       , lnkR
        -- (T10) AC fired, and THIS bundle is the leg's UP one — node B's AB arm's
        -- landing, at node C's own fields
        , ( inj₂ (λ bb heq →
              let w   = inj₂ (proj₁ (relayAdv-cp4 bb raR heq)
                             , proj₂ (relayAdv-cp4 bb raR heq))
                  lbl = proj₁ (proj₂ (lblR w))
                  bc  = proj₁ (lblR w)
                  src = bundle-recv-cliPos linkAC hi lo (λ ())
                          (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc)
                          (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
                          (SN.NodeStateC.inert-AC nc)
                          (subst (λ z → bunC-AC nc ─[ ev (evl z) ]─► _) lbl sBAC)
              in  recvLand bc (rpin⇒rbbAt linkAC hi bc e a lbl) (cong coarsenBFc src)
                , subst BFcHasBlk (sym src) tt)
          -- (A, cellCp3) … node B's AB arm's pre-request component, at node C's fields
          , upBfPre-relay linkAC linkCD (SN.NodeStateC.bfC-AC nc) bfc′
              (SN.NodeStateC.cp-C nc) x′ dStep raR cliRow )
        -- (T11b) AC fired, so the `pp3` landing is refuted by the LINK, exactly as
        -- the `pp1` and `pp2` ones are
        , (λ bb eq → ⊥-elim (linkAC≢linkCD
             (apiLink-inj ahl (acsAt⇒ahl (csfwAt⇒acs e a (csfwR bb eq))))))
        -- (T11h) AB/AC fired, so the DOWN bundle — where the leg's dn BF SERVER lives —
        -- is a LITERAL: the new third member is `refl`
        , inj₁ refl

-- firing link = linkCD (node C's PRODUCE leg, RIGHT bundle)
nodeC-api-CD-evo⁺ : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
                    {B₁ D₁ : NetProc}
  → apiES .mem (X , e) a
  → (bunC-AC nc ⦀ bunC-CD nc) ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc) ─[ ev (evl (evLabel X e a)) ]─► D₁
  → ApiHasLink linkCD e
  → NodeCApiEvo nc e a (B₁ ∥⇘ apiES ⇙ D₁)
nodeC-api-CD-evo⁺ nc {X} {e} {a} apimem bStep dStep ahl
  with cpStepKindQ-of⁺ linkAC linkCD (SN.NodeStateC.cp-C nc) dStep
-- (T7) four more binders: `cpStepKindQ-of⁺` grew the `cp5` chain's landing and its
-- three carrying hops (components fourteen to seventeen)
... | x′ , refl , rk , lblR , fwdR , rval , blkR , sbb8 , hasR , reqR , sbR , csrR , csaR
    , csfR , c3R , c4R , c5R , raR , lnkR
    -- (T11b) one more binder: the classifier grew the `pp3` landing's LABEL PIN as
    -- its TWENTIETH component, and this reader ended on a NON-wildcard
    , csfwR
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (bunC-AC nc) (bunC-CD nc) bStep
...   | PEA.evSync () _ _
...   | PEA.evL _ sBAC = ⊥-elim (absBundleG-api-no linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ahl (λ q → linkAC≢linkCD (sym q)) apimem (_ , sBAC))
...   | PEA.evBoth _ sBAC _ = ⊥-elim (absBundleG-api-no linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ahl (λ q → linkAC≢linkCD (sym q)) apimem (_ , sBAC))
...   | PEA.evR _ sBCD
      with absBundleG-api-evo⁺ linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) apimem sBCD
-- (T7) re-cut with one trailing `_`: this reader ended on a NON-wildcard and
-- `BundleApiEvo` grew a FOURTEENTH component (§2b⁗'s client landing), which this arm
-- does not want — the bundle peeled here is the leg's DOWN one, whose CS client is
-- node D's, not the relay's UP-hop one.  (The banked Σ-append trap, fourth sighting.)
...     | csc′ , css′ , bfc′ , bfs′ , ip′ , eq , run , _ , srvE , _ , _ , srvRow , srvReq , srvSb , _ , cssRow , cssReq , cssAw , _ , _ , _ , _ , cssRfw , _ =
          SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) csc′ css′ bfc′ bfs′ x′ (SN.NodeStateC.inert-AC nc) ip′
        , cong (λ z → (bunC-AC nc ⦀ z) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD x′) eq
        , ∥⇘⇙-wev-sync apiES _ _ apimem
            (⦀-wev-R _ _ (noOffer→viewV _ (bundleG-api-no linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ahl (λ q → linkAC≢linkCD (sym q)) apimem)) run)
            (ev→wev dStep)
        , rk , inj₁ refl
        , (λ w → ⊥-elim (absBundleG-api-no linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) ahlBF linkAC≢linkCD tt
                   (_ , subst (λ z → bunC-CD nc ─[ ev (evl z) ]─► _) (proj₁ (proj₂ (lblR w))) sBCD)))
        , srvDn-of linkCD (SN.NodeStateC.bfS-CD nc) bfs′ (SN.NodeStateC.cp-C nc) x′ fwdR hasR sbb8 srvE
        , rval , blkR
        -- (grant #8) the mirror
        , cliApiRow-fix linkAC hi (SN.NodeStateC.bfC-AC nc) e a , srvRow
        -- (T1) CD fired: the mirror of node B's own-key answer
        , (λ bb eq → proj₁ (reqR bb eq)
                   , srvReq (proj₁ (reqR bb eq)) (proj₂ (reqR bb eq)))
        -- (T2) … and the `pp5` landing at leg CD's own hop
        , (λ bb eq → proj₁ (sbR bb eq)
                   , proj₁ (proj₂ (sbR bb eq))
                   , srvSb (proj₂ (proj₂ (sbR bb eq))))
        -- (T4) CD fired ⇒ the DOWN CS SERVER's row is the bundle's; the UP CS
        -- CLIENT is in the untouched AC bundle
        , cscApiRow-fix linkAC hi (SN.NodeStateC.csC-AC nc) e a , cssRow
        -- (T5) CD fired: the label pin feeds the bundle's own-key LANDING
        , (λ bb eq → cssReq (csrR bb eq))
        -- (T6d) … and the `pp2` pin the other tag's, at the same successor
        , (λ bb eq → cssAw (csaR bb eq))
        -- (T7) CD fired, so node C's AC bundle is a LITERAL — the mirror of node B's
        -- down-link arm, and the same polarity note applies
        , (λ bb eq → ⊥-elim (linkAC≢linkCD
             (sym (apiLink-inj ahl (csfAt⇒ahl e a (csfR bb eq))))))
        , (λ bb eq → proj₁ (c3R bb eq) , proj₁ (proj₂ (c3R bb eq)) , refl)
        , (λ bb eq → proj₁ (c4R bb eq) , proj₁ (proj₂ (c4R bb eq)) , refl)
        , (λ bb eq → proj₁ (c5R bb eq) , proj₁ (proj₂ (c5R bb eq)) , refl)
        , raR
        , lnkR
        -- (T10) CD fired, so a `cp4` landing is refuted by the LINK
        , ( inj₂ (λ bb heq →
              let w   = inj₂ (proj₁ (relayAdv-cp4 bb raR heq)
                             , proj₂ (relayAdv-cp4 bb raR heq))
                  lbl = proj₁ (proj₂ (lblR w))
                  bc  = proj₁ (lblR w)
              in  ⊥-elim (linkAC≢linkCD
                    (apiLink-inj (proj₁ (proj₂ (rbbAt⇒pin e a
                                   (rpin⇒rbbAt linkAC hi bc e a lbl)))) ahl)))
          -- (A, cellCp3) CD fired: node B's BD arm's answer, at node C's slots
          , (λ pre → refl , relayAdv-pre raR pre) )
        -- (T11b) BD/CD fired, so the `pp3` landing CARRIES here: the classifier's
        -- own pin feeds the bundle's third own-key landing
        , (λ bb eq → cssRfw (csfwR bb eq))
        -- (T11h) CD fired: node B's arm's dispatch, at node C's slots
        , dnSrvPre-dn linkAC linkCD (SN.NodeStateC.bfS-CD nc) bfs′ x′ e a ahl linkAC≢linkCD srvRow lnkR csrR csaR csfwR

-- node-C api inversion
nodeC-ev-api-evo⁺ : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
                    {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeC nc ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeCApiEvo nc e a M
nodeC-ev-api-evo⁺ nc {X} {e} {a} apimem step
  with SStep.reflect-node-api (bunC-AC nc ⦀ bunC-CD nc)
         (SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc)) apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with decCP-ev-link linkAC linkCD (SN.NodeStateC.cp-C nc) dStep
... | inj₁ ahl = nodeC-api-AC-evo⁺ nc apimem bStep dStep ahl
... | inj₂ ahl = nodeC-api-CD-evo⁺ nc apimem bStep dStep ahl

-- (T1 / S1) what a visible api step does to the PAIR (relay driver phase, the leg's
-- DOWN-hop BF server) — the fact S1's api arm consumes, and the only shape in which
-- the whole-nodes cone can report it.
--
-- EITHER neither moved — the event fired at another node, and then the relay's own
-- record is a LITERAL in the successor, so both equations are `refl` — OR the relay
-- node itself fired, and then the `pp4` LANDING carries the down server's genuine
-- own-key row.  The second arm also covers the relay firing on its own UP link,
-- where the phase moves but the landing is refuted by the fired LINK.
--
-- *** WHY THE DISJUNCTION AND NOT THE LANDING ALONE. ***  At a step that moves
-- NEITHER, S1 has to FRAME, and framing needs the two fixities; the landing says
-- nothing there (the invariant's own antecedent is what supplies the position).  And
-- why not the two fixities alone: the relay's own sync moves both.
-- (T5) the CS twin of `DnSrvDrv`, at EXPLICIT positions and phases rather than at a
-- leg: the CS slot accessor `LiveRelayOpen.dnCSs` lives ABOVE this module (the cone
-- is in its closure, so importing it back is a cycle), and the consumer's own
-- selector maps the leg to these two node fields — which is exactly what makes the
-- two forms convertible once the leg is a constructor.
-- *** (T6d) THE SECOND ARM IS NOW A PAIR, exactly as `DnSrvDrv`'s is. ***  One relay
-- step is one driver advance, so whichever of the two funded CS sub-phases it lands
-- at, the arm that reports it is this one — and the `pp2` region has to be
-- ESTABLISHED at its entering step for the same reason `pp1`'s position does.
-- *** (T11b) THE SECOND ARM IS NOW A TRIPLE. ***  One relay step is one driver
-- advance, so whichever of the THREE funded CS sub-phases it lands at, the arm that
-- reports it is this one — and the `pp3` region has to be ESTABLISHED at its entering
-- step for the same reason the `pp2` one does.  *** A reader that ends its landing-arm
-- pattern on a NON-wildcard must re-cut (`LiveDrvBF.drvCS-api-at2` did). ***
--
-- *** (T11c) AND A FOURTH MEMBER: THE RELAY's OWN ADVANCE, MERGED IN — the §8 (i-b)
-- IMPOSSIBLE-COMBINATION trap, closed the banked way. ***  The landing arm is
-- produced exactly when the relay node FIRED, so its driver advanced; but until this
-- member the TYPE did not say so, and a consumer holding the landing arm beside a
-- SEPARATELY-reported `RelayAdv`-or-fixity had a combination it could not refute.
-- (T11b's §6i(c) records where that bites: at `producing _ pp3` the landing gives the
-- successor server `csWrf ht` while a `relayOf l s ≡ relayOf l s′` puts the SOURCE at
-- `pp3` too, whose own server region admits `csIdle` — and then the `csWrf`
-- correlation's antecedent has nothing to read.)
--
-- *** THE MEMBER IS FREE AND THAT IS WHY IT IS HERE RATHER THAN DOWNSTREAM. ***  It is
-- assembled where the OTHER three are — `LiveLegApiExpose`'s two relay-fires arms —
-- and the classifier's EIGHTEENTH component (`raB`/`raC`) is already bound in the same
-- reader at the same node fields.  Four one-word additions and no cone producer moves.
-- T8c-iii banked the rule: *** merge the correlation into ONE field; do not ask a
-- consumer to refute the combination. ***
--
-- (F103  *** THE MEMBER's ORIENTATION IS LOAD-BEARING. ***)  swap it to
--      `RelayAdv x′ x` (arity-preserving; the member set is untouched).  *** RED ***:
--      `LiveLegApiExpose.agda:1253.60-63: [UnequalTerms] SN.cp-B (nB s) != SN.cp-B nb′
--      of type CPPh … when checking that the expression raB has type RelayAdv
--      (SN.cp-B nb′) (SN.cp-B (nB s))`, EXIT=42 — the assembly's own `raB` is the
--      classifier's advance at (source , successor) and nothing else fits, so a
--      consumer reading the member as an advance cannot be handed its reverse.
--      Reverted by string inversion, `git status` clean after.
--      *** AND THE HONEST LEDGER ENTRY BESIDE IT: the member is a PARKED INTERFACE —
--      both existing readers (`LiveDrvBF.drvCS-api-at`/`-at2`) absorb it in a trailing
--      wildcard, so it has no CONSUMER until the carry lands.  F103 guards its
--      ASSEMBLY, which is what exists to be guarded; the consumer's own guard is owed
--      at the carry, not here. ***
DnCsDrv : (l : Link) (css css′ : CSsPos) (x x′ : CPPh) → Set
DnCsDrv l css css′ x x′ =
    ((x ≡ x′) × (css ≡ css′))
  ⊎ (DnCsReqLand l css css′ x′ × DnCsAwLand l css css′ x′
     × DnCsRfwLand l css css′ x′ × RelayAdv x x′)

-- *** (T7) THE UP-HOP MIRROR: what a visible api step does to the PAIR (relay driver
-- phase, the leg's UP-hop CS CLIENT). ***  `DnCsDrv`'s shape at the other hop and the
-- other peer role, and the arm the `cp5` chain's four api halves consume.
--
-- EITHER neither moved — the event fired at another node, and then the relay's own
-- record is a LITERAL in the successor, so both equations are `refl` — OR the relay node
-- itself fired, and then the second arm's FOUR facts cover its whole consume chain: the
-- `cp2` LANDING plus the three carrying hops.  The second arm also covers the relay
-- firing on its DOWN link, where the phase moves but the landing is refuted by the fired
-- LINK and the three hops answer with `refl` (the UP client is untouched there).
--
-- *** THE POLARITY OF THE REFUTATION IS THE MIRROR OF `DnCsDrv`'s, AND THAT IS THE ONE
-- THING A SYNC SWEEP MUST NOT COPY BLIND. ***  `DnCsReqLand`/`DnCsAwLand` are refuted on
-- the arm where the relay fired on its UP link and carried on the arm where it fired on
-- its DOWN one; here it is the other way round.  Both are the same argument — "the pin
-- names a link, and `apiLink-inj` against the fired link closes the case" — applied at
-- the hop the peer actually lives on.
--
-- *** WHY FOUR FACTS AND NOT ONE. ***  Only the FIRST sub-phase of the chain is a
-- landing; the other three are carried across BlockFetch api events by the client's
-- FIXITY, and fixity plus a source phase is a different statement from a landing.  One
-- relay step is one driver advance, so all four travel in the arm that reports it —
-- `DnSrvDrv`'s and `DnCsDrv`'s own rule, at four components instead of two.
UpCsDrv : (l : Link) (csc csc′ : CScPos) (x x′ : CPPh) → Set
UpCsDrv l csc csc′ x x′ =
    ((x ≡ x′) × (csc ≡ csc′))
  ⊎ (UpCsRfLand l csc csc′ x′
     × UpCsStep cp2 cp3 csc csc′ x x′
     × UpCsStep cp3 cp4 csc csc′ x x′
     × UpCsStep cp4 cp5 csc csc′ x x′)

DnSrvDrv : (l : TwoLegs) (s s′ : SysState) → Set
DnSrvDrv l s s′ =
    ((relayOf l s ≡ relayOf l s′) × (dnSrv l s ≡ dnSrv l s′))
  ⊎ (DnReqLand (dnLink l) (dnSrv l s) (dnSrv l s′) (relayOf l s′)
     -- (T2) the SECOND landing travels in the same arm: one relay step is one
     -- driver advance, so whichever of the two sub-phases it lands at, the arm that
     -- reports it is this one
     × DnSbLand (dnLink l) (dnSrv l s) (dnSrv l s′) (relayOf l s) (relayOf l s′)
     -- (T11h) … and the third member, for the reason `DnSrvPre` records: the two
     -- landings say NOTHING at the relay's three in-region produce hops
     × DnSrvPre (dnSrv l s) (dnSrv l s′) (relayOf l s′))
