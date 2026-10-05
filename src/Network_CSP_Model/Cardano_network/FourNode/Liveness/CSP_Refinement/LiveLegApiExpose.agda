{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — THE ⁺ WHOLE-NODES api EXPOSURE
-- (`Praos.LiveLegApiExpose`), T3b's split of `LiveLegApiCone`.
--
-- WHY THIS MODULE EXISTS — WHERE THE CUT IS, AND WHY THERE.  `LiveLegApiCone`
-- had grown to eleven sections and 2,083 code lines (2,051 at T2's fix round, plus
-- T3b's record conversion; both figures re-derived here, not relayed), and T4 is
-- about to add the CS row layer to the same object.  The split left 1,489 code
-- lines in the cone and 707 here (both re-derived at the T3b fix round: the 1,492
-- first reported predated the five dead cone-side imports being pruned, and the 747
-- predated this module's own import prune).  T4 has since threaded the CS rows
-- through both halves, so the CURRENT figures are **1,502** and **734** — computed
-- from the T4 diff (+13 and +27 code lines), not re-quoted; no definition moved and
-- no section changed hands.  The seam taken is the one the file's own dependency
-- direction already had:
--
--   *  `LiveLegApiCone` (§1-§7, RETAINED there) is the PER-PEER, UP-HOP cone —
--      the four label pins, the strengthened per-peer api facts, the four decode
--      packages, the ⁺ bundle dispatcher, node A's peel, the relay classifier and
--      the two relay nodes' peels, plus the row types (`SrvApiRowP`/`CliApiRowP`,
--      `SrvReqRow`, `SrvSbLand`, `DnReqLand`/`DnSbLand`/`DnSrvDrv`) every layer
--      above quotes.  Nothing in it mentions the whole-nodes report.
--
--   *  THIS module is the ASSEMBLY: §8 (node D's ⁺ re-mirror — the layer T1 and
--      T2 grew, and the only one that reports the DOWN-hop client rows), §9 (the
--      api-side leaf record `VisLeaves⁺` and the whole-nodes report
--      `DriverExposed⁺`/`driverExpose⁺`), §9a/§9b (the two landings) and §10/§11
--      (the three per-leg selectors).
--
-- The cut is therefore ONE-DIRECTIONAL by construction — the assembly consumes
-- the cone and the cone never mentions the assembly — and it was the placement T4
-- needed.  What T4 actually did (this sentence corrects the split's guess, which had
-- the dependency the wrong way round): the CS row layer went into a fresh SIBLING,
-- `LiveCSRow`, which the CONE imports — one layer BELOW the cone, naming no cone
-- object — while the trailing CS slots it threads are fields of the record HERE
-- (`deCSRowsBD`/`deCSRowsCD`).  Each half was opened for its own two-slot append and
-- nothing else.
--
-- *** ZERO PROOF CONTENT MOVED. *** Every definition below is byte-identical to
-- its `LiveLegApiCone` original at commit `05441c3`; only the module header and
-- the import list are new.  The import list was copied whole at the split and
-- PRUNED at T3b's fix round to what this half actually names: 109 dead `using`
-- entries dropped, 18 imports removed outright (11 whose entire list was dead,
-- plus the six protocol aliases `CS`/`BF`/`KA`/`TS`/`LN`/`LF` and `NodeSpecs as
-- NS`, all of which are consumed only in the cone half).  Header comments whose
-- subject was dropped went with it.  `DnSrvDrv` stayed BEHIND in the cone (it is row
-- machinery, and `LiveDrvBF` reads it) so that no consumer of the cone had to
-- start importing this module.
--
-- TWO KNOWN QUIRKS, recorded so they are not mistaken for transcription later:
--
--   *  (M-6) `DriverExposed⁺` DECLARES its sort as `Set₁`, where the `Σ` it replaces had
--      its level INFERRED.  This is the one type-level line of the conversion that is not
--      a mechanical transcription.  It is harmless — no consumer states the sort — but if
--      a future field forces a higher level, this is the line to change.
--
--   *  (M-7) `LiveChanJoin:923-926` binds LEG-keyed locals over LINK-keyed fields
--      (`rowsBD = deRowsAB de`, `rowsCD = deRowsAC de`): leg `legBD`'s UP hop is link
--      `AB`, leg `legCD`'s is link `AC`.  That is correct and faithful to the old
--      positional binding, but it is the exact confusion falsification F22 used, so it is
--      named here rather than left to be rediscovered.  A rename to
--      `rowsUpBD`/`rowsUpCD` would remove it; that is a CODE change and was not taken.
--
-- Base modules touched: NONE.  No postulate/hole/meta.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Unit.Polymorphic using ( ⊤; tt )
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
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegApiExpose
  (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using
  ( p; apiES; linkAB; linkAC; linkBD; linkCD; produce )
open import CSP.Examples.Cardano_network.Base using
  ( lo; hi; N2N_ChainSync; N2N_BlockFetch; N2N_KeepAlive; N2N_TxSubmission
  ; N2N_LeiosNotify; N2N_LeiosFetch )
open import CSP.Examples.Cardano_network.Net p using
  ( Net_Api; Net_Api-≟; Link; apiBF; done; recvBFBlock )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( Block )
open import CSP.Examples.Cardano_network.Data p using
  ( Payload )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; EventSet; viewV )
open EventSet using ( mem )
open Op using () renaming ( ∅ES to ∅ESa )
open Op using ( _>>=_; Skip )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using
  ( _─[_]─►_; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using
  ( _═[_]═►_ )

import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload}) as PEA

import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep
open SStep using ( NetProc; absBFc; absBFs; absBundleG
                 ; absNodeA; absNodeB; absNodeC; absNodeD; absNodesOf; nodesOf
                 ; coarsenBFc; coarsenBFs; decBFc-sil-step; decBFs-sil-step
                 ; reflect-node-api; apiSync; ⦀-ev-L; ⦀-ev-R )
-- (T10) the COARSE server positions the `pp6` landing field names
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.NodeSpecs blkA as NS
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
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA using
  ( SysState; mkSys; med; nA; nB; nC; nD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA using
  ( ApiHasLink; apiLink-inj; decConsD-ev-link; IsApiCSBF )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysRoute blkA using
  ( absNodeA-fp; absNodeB-fp; absNodeC-fp; absNodeD-fp; nodeB-no-when-A
  ; nodeC-no-when-A; nodeD-no-when-A; nodeC-no-when-B; nodeD-no-when-B
  ; nodeD-no-when-C; absNodeB-no-when-A; absNodeC-no-when-A
  ; absNodeD-no-when-A; absNodeC-no-when-B; absNodeD-no-when-B
  -- (P8): a `recvBFBlock` is a CONSUMER-role event, and the roles are disjoint
  ; absNodeD-no-when-C
  ; prod≢cons )
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
  ; absBundleLN-ev-prod; absBundleLF-ev-prod
  -- §8 (task 5): the two node-D co-leg consume-driver no-offer refutations, for
  -- the ⁺ re-mirror of node D's api peel
  ; drvD-BD-no; drvD-CD-no )

open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkMeasure blkA using
  ( ConsAdv )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA using
  ( TwoLegs; legBD; legCD; phOf; linkOf; InCp03; cblkOf )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkDAnchor blkA using
  ( consDAdv-of⁺; ConsHeld )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA using
  ( prodOf; relayOf; dnClient; RelayHas; RelayFwd; ConsRecv; ProdSent
  ; ProdNotSent; BFcHasBlk; prodSent-notSent-⊥ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA using
  ( upSrv; dnSrv; UpSrvEvo; DnSrvEvo )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeProdFire blkA using
  ( linkAB≢linkCD; linkAC≢linkBD; nodeB-link; nodeB-sbb-AB-⊥; nodeC-link
  ; nodeC-sbb-AC-⊥
  -- (P8): `evl` injectivity, for transporting the `recvBFBlock` decode along a
  -- fired-label equality
  ; nodeD-link )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValFill blkA using
  ( bundle-recv-cliPos )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValRelay blkA using
  ( RelayAt )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleRecv blkA using
  ( bundle-recvBFBlock-forces-src )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleEvo blkA using
  ( BFsHasBlk )
-- (P5) grant #6: the frozen KA client and the ONE KA inversion that reports its
-- freeze.  The api class needs it because `done l d N2N_KeepAlive` IS `IsApiCSBF`
-- (`SysOracle:1949` — `aicDone` at ANY channel) and its bundle clause moves `kac`.
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveKAFrozen blkA using
  ( KAcAtHead )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeEvDriverCone blkA using
  ( upLinkOf; LegDriverStep; ldProd; ldRelay; ldCons
  -- ASSEMBLY slice A1: the VALUE step data beside the driver step, so ONE peel
  -- of `driverExpose⁺` serves every premise of `LiveLegStep`'s visible arm
  ; ldFix
  ; LegValStep
  -- §8 (task 5): the receive-crossing source pin, reused by the ⁺ node-D mirror
  ; lvStep
  ; consAdv-recv-src )

-- (T4) the ChainSync ROW layer: the two CS-axis api-adjacency facts and their
-- fixity dispatchers.  Only these four names are needed here — the recovery
-- machinery itself is consumed inside the cone's ⁺ bundle dispatcher.
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveCSRow blkA
  using ( CScApiRowP; CSsApiRowP; cscApiRow-fix; cssApiRow-fix )

-- §1-§7: the per-peer up-hop cone this assembly is built on (the label pins, the
-- ⁺ per-peer facts, the decode packages, the bundle dispatcher, node A's peel,
-- the relay classifier, the two relay nodes' peels and the row types)
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegApiCone blkA

------------------------------------------------------------------------
-- §8  NODE D — the ⁺ re-mirror of `PipeEvDriverCone`'s node-D consume peel.
--
-- *** WHY THIS EXISTS: IT IS THE GRANT-FREE `chanDn` ROUTE. ***  Node D holds no
-- leg BF SERVER, which is why §5-§7 above could leave its peel frozen — but it
-- holds BOTH legs' DOWN-HOP BF CLIENTS (`PipeInv.dnClient legBD = bfC-BD`,
-- `dnClient legCD = bfC-CD`), and the frozen `NodeDDrv` reports only
-- `(fixed) ⊎ (¬holding successor)` about the very client it moves.  That disjunct
-- kills the `CliHoldA` escape but never establishes `CliAcceptsA`, and every
-- `ChanInv` clause puts the client in a CONSEQUENT, so `LiveChanJoin`'s visible
-- arm cannot carry the DOWN hop's invariant across a node-D api from it.  Nor can a
-- SECOND peel be added beside the frozen one: `absNodeD` is not injective (the
-- shape measured at `SysStep:1156-1162`), so the second peel's successor cannot be
-- identified with the first's.
--
-- *** AND IT NEEDS NO BASE EDIT. ***  The obstruction is one layer deeper than the
-- peel — `NodeDDrv`'s client slot is fed verbatim from
-- `PipeBundleEvo.BundleGEvR⁺`'s own client slot (`bgEB⁺`, the weak slot inside
-- `:940-946`, the client slot `:944`), and widening THAT would touch a datatype matched at 28 sites in
-- three modules.  But grant #8 already made the api DECODES report the fired
-- coarse row (`decBFc-apiBF-succ-row⁺`), and §4's `absBundleG-api-evo⁺` already
-- routes it out of the bundle layer, BYPASSING `BundleGEvR⁺` entirely.  So node D
-- gets exactly the treatment nodes A, B and C got: its peel is re-mirrored at the
-- ⁺ dispatcher.  Every frozen ingredient is reused verbatim — the consume
-- classifier `consDAdv-of⁺`, the receive source pin `consAdv-recv-src`, the two
-- bundle label readers, the weak-run tower and the co-leg refutations; ONLY the
-- bundle call changes, and the record gains two trailing client rows.
--
-- *** KEEP IN SYNC WITH `LTL/Value/PipeEvDriverCone.NodeDDrv` (`:203-260`) AND ITS
-- TWO PRODUCERS (`:263-345`), FIELD BY FIELD. ***  Anchors re-derived by grep in
-- this round.  `NodeDApiEvo`'s field list IS `NodeDDrv`'s, in the same order, with
-- exactly TWO TRAILING additions per constructor (leg BD's and leg CD's down-hop
-- client rows, in that order regardless of which link fired).  The two producers
-- are `nodeD-api-BD-drv` / `nodeD-api-CD-drv` with `absBundleG-api-evo` replaced by
-- `absBundleG-api-evo⁺` and the two rows appended, and the dispatcher is
-- `nodeD-ev-api-drv` (`:348-373`) TRANSCRIBED VERBATIM — its span belongs in this
-- marker too (final-review M-2), since a change to its four-way
-- `reflect-node-api`/`Par-ev-elim` dispatch rots the mirror exactly as a field-list
-- change does.  If `NodeDDrv`'s FIELD LIST changes, this mirror rots silently.
------------------------------------------------------------------------

-- node D's ⁺ api peel result: the frozen `NodeDDrv`'s two constructors with the
-- two down-hop CLIENT ROWS appended
data NodeDApiEvo (nd : SN.NodeStateD) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                 (M : NetProc) : Set₁ where
  ndaBD : (nd′ : SN.NodeStateD) → M ≡ absNodeD nd′
        → SN.decNodeD nd ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeD nd′
        → ConsAdv (cph (SN.NodeStateD.cons-BD nd)) (cph (SN.NodeStateD.cons-BD nd′))
        → SN.NodeStateD.cons-CD nd′ ≡ SN.NodeStateD.cons-CD nd
        → SN.NodeStateD.bfC-CD nd′ ≡ SN.NodeStateD.bfC-CD nd
        -- SESSION-40 ANCHOR: `b″` is the block the SUCCESSOR slot records
        → (cph (SN.NodeStateD.cons-BD nd) ≡ cp3
           → Σ[ b″ ∈ Block₃ ]
               (evLabel X e a ≡ evLabel Block₃ (apiBF linkBD hi recvBFBlock) b″)
             × (cblk (SN.NodeStateD.cons-BD nd′) ≡ b″)
             -- SESSION-41: and the CO-FIRING client held exactly that block
             × (SN.NodeStateD.bfC-BD nd ≡ bcBlk1 b″))
        → ((SN.NodeStateD.bfC-BD nd ≡ SN.NodeStateD.bfC-BD nd′)
           ⊎ (BFcHasBlk (SN.NodeStateD.bfC-BD nd′) → ⊥))
        → (InCp03 (cph (SN.NodeStateD.cons-BD nd))
           → ConsRecv (cph (SN.NodeStateD.cons-BD nd′))
           → BFcHasBlk (SN.NodeStateD.bfC-BD nd))
        -- SESSION-51: PAST the receive the recorded block is FIXED
        → (ConsHeld (cph (SN.NodeStateD.cons-BD nd))
           → cblk (SN.NodeStateD.cons-BD nd′) ≡ cblk (SN.NodeStateD.cons-BD nd))
        -- SESSION-56 (owner grant #5, (P8)): the firing consume-driver step itself
        → (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd)
             ─[ ev (evl (evLabel X e a)) ]─►
             SN.decConsD linkBD (SN.NodeStateD.cons-BD nd′))
        -- (grant #8, CALLED DIRECTLY) TRAILING: the two DOWN-hop clients' fired
        -- ROWS.  Link BD's is the fired bundle's own; link CD's peer is literal.
        → CliApiRowP linkBD hi (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfC-BD nd′) e a
        → CliApiRowP linkCD hi (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfC-CD nd′) e a
        -- (T6c, grant #12) TRAILING: node D's two DOWN-hop CS CLIENTS' rows.  D's
        -- bundles are `absBundleG l hi lo`, so the down hop's CS CLIENT is D's at its
        -- `cl` — the peer `ChanCSDn`'s `ccPre` is about.
        → CScApiRowP linkBD hi (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csC-BD nd′) e a
        → CScApiRowP linkCD hi (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csC-CD nd′) e a
        -- *** (T8c-iii) TRAILING behind those: `LiveLegApiCone` §2b⁵'s SHARPENING on
        -- the FIRING leg, PLAIN, plus the CO-leg's CS-client FIXITY as an equation.
        -- ***  (T8c-ii shipped both as fixity-or-fired disjunctions; T8c-iii found the
        -- disjunction unusable at the consumer and the *unconditional* form UNPROVABLE
        -- — see the note at `DriverExposed⁺.deNodeDBD` for both, and for why this
        -- asymmetric pair is the shape that works.)  The firing leg's bundle supplies
        -- the sharpening as its twentieth component; the co-leg's client slot is
        -- LITERAL in this successor, so its equation is `refl`.
        → CscCliFired linkBD hi (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csC-BD nd′) e a
        → SN.NodeStateD.csC-CD nd′ ≡ SN.NodeStateD.csC-CD nd
        -- *** (T11e) TRAILING: §2b⁷'s `sendBFRequestRange` LANDING at node D's OWN BF
        -- client, on the FIRING leg. ***  `LiveDrvBFD` §2c's `c23` clause cannot cross
        -- `cp2 → cp3` without it — `CliApiRowP`'s fixity arm leaves the successor at
        -- `(cp3 , bcIdle)`, §0(6)'s hazard — and only the bundle knows which peer
        -- fired.  Per-CONSTRUCTOR, like `CscCliFired` above: at a leg whose bundle is
        -- LITERAL the landing is not provable at all (a fixed client cannot be both
        -- `bcIdle` and `bcWrr r`), so it rides the firing leg and nothing else
        → CliReqLand linkBD hi (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfC-BD nd′) e a
        → NodeDApiEvo nd e a M
  ndaCD : (nd′ : SN.NodeStateD) → M ≡ absNodeD nd′
        → SN.decNodeD nd ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeD nd′
        → ConsAdv (cph (SN.NodeStateD.cons-CD nd)) (cph (SN.NodeStateD.cons-CD nd′))
        → SN.NodeStateD.cons-BD nd′ ≡ SN.NodeStateD.cons-BD nd
        → SN.NodeStateD.bfC-BD nd′ ≡ SN.NodeStateD.bfC-BD nd
        -- SESSION-40 ANCHOR (mirror)
        → (cph (SN.NodeStateD.cons-CD nd) ≡ cp3
           → Σ[ b″ ∈ Block₃ ]
               (evLabel X e a ≡ evLabel Block₃ (apiBF linkCD hi recvBFBlock) b″)
             × (cblk (SN.NodeStateD.cons-CD nd′) ≡ b″)
             -- SESSION-41 (mirror)
             × (SN.NodeStateD.bfC-CD nd ≡ bcBlk1 b″))
        → ((SN.NodeStateD.bfC-CD nd ≡ SN.NodeStateD.bfC-CD nd′)
           ⊎ (BFcHasBlk (SN.NodeStateD.bfC-CD nd′) → ⊥))
        → (InCp03 (cph (SN.NodeStateD.cons-CD nd))
           → ConsRecv (cph (SN.NodeStateD.cons-CD nd′))
           → BFcHasBlk (SN.NodeStateD.bfC-CD nd))
        -- SESSION-51 (mirror)
        → (ConsHeld (cph (SN.NodeStateD.cons-CD nd))
           → cblk (SN.NodeStateD.cons-CD nd′) ≡ cblk (SN.NodeStateD.cons-CD nd))
        -- SESSION-56 (owner grant #5, (P8)) — the mirror of the BD field
        → (SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)
             ─[ ev (evl (evLabel X e a)) ]─►
             SN.decConsD linkCD (SN.NodeStateD.cons-CD nd′))
        -- (grant #8) TRAILING, in the SAME leg order: link BD's peer is literal
        -- here, link CD's row is the fired bundle's
        → CliApiRowP linkBD hi (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfC-BD nd′) e a
        → CliApiRowP linkCD hi (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfC-CD nd′) e a
        -- (T6c, grant #12) TRAILING, in the SAME leg order
        → CScApiRowP linkBD hi (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csC-BD nd′) e a
        → CScApiRowP linkCD hi (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csC-CD nd′) e a
        -- (T8c-iii) TRAILING — the `ndaBD` pair's mirror: the FIRING leg is CD here,
        -- so the sharpening is CD's and the fixity equation is BD's
        → CscCliFired linkCD hi (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csC-CD nd′) e a
        → SN.NodeStateD.csC-BD nd′ ≡ SN.NodeStateD.csC-BD nd
        -- (T11e) … node C's leg's mirror
        → CliReqLand linkCD hi (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfC-CD nd′) e a
        → NodeDApiEvo nd e a M

-- firing link = linkBD: cons-BD advances (genuine), cons-CD/bfC-CD literal
nodeD-api-BD-evo⁺ : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
                    {B₁ D₁BD : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
     ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ─[ ev (evl (evLabel X e a)) ]─► D₁BD
  → ApiHasLink linkBD e
  → NodeDApiEvo nd e a (B₁ ∥⇘ apiES ⇙ (D₁BD ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)))
nodeD-api-BD-evo⁺ nd {X} {e} {a} apimem bStep sDBD ahl
  with consDAdv-of⁺ linkBD (SN.NodeStateD.cons-BD nd) sDBD
... | b′ , cp′ , refl , cadv , lblv , cfix
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
           (absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) bStep
...   | PEA.evSync () _ _
...   | PEA.evR _ sBCD = ⊥-elim (absBundleG-api-no linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) ahl linkBD≢linkCD apimem (_ , sBCD))
...   | PEA.evBoth _ _ sBCD = ⊥-elim (absBundleG-api-no linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) ahl linkBD≢linkCD apimem (_ , sBCD))
...   | PEA.evL _ sBBD
      with absBundleG-api-evo⁺ linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) apimem sBBD
-- (T8c-ii) re-cut to BIND the TWENTIETH component: the bundle peeled here is node D's
-- OWN down-hop one, so §2b⁵'s sharpening is exactly the fact node D's api carry needs
-- *** (T10) RE-CUT: `BundleApiEvo` grew a TWENTY-FIRST component (§2b′⁺'s
-- `sendBFBatchDone` landing) and this reader ends on a NON-wildcard, so it takes one
-- more binder — the banked Σ-append trap, EIGHTH sighting ***
-- (T11e) re-cut once more, spelling positions 21-23 so the TWENTY-FOURTH (§2b⁷'s
-- request landing) can be bound: this bundle is node D's OWN, so the landing is the
-- fact its BlockFetch api class needs.  The banked Σ-append trap, TWELFTH sighting
...     | csc′ , css′ , bfc′ , bfs′ , ip′ , eq , run , cliE , _ , _ , cliRow , _ , _ , _ , cscRow , _ , _ , _ , _ , cscFired , _ , _ , _ , reqLand =
          ndaBD (SN.mkNodeD csc′ css′ bfc′ bfs′ (consD b′ cp′) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) ip′ (SN.NodeStateD.inert-CD nd))
            (cong (λ z → (z ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) ∥⇘ apiES ⇙ (SN.decConsD linkBD (consD b′ cp′) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))) eq)
            (∥⇘⇙-wev-sync apiES _ _ apimem
               (⦀-wev-L _ _ (noOffer→viewV _ (bundleG-api-no linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) ahl linkBD≢linkCD apimem)) run)
               (ev→wev (⦀-ev-L (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd)) _ sDBD (noOffer→viewV _ (drvD-CD-no nd ahl)))))
            -- SESSION-40: the anchored classifier pins the label at `b′`, and
            -- `nd′`'s BD slot IS `consD b′ cp′`, so the successor conjunct is `refl`
            cadv refl refl (λ hcp → b′ , lblv hcp , refl ,
               bundle-recv-cliPos linkBD hi lo (λ ())
                 (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
                 (subst (λ z → absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ─[ ev (evl z) ]─► _)
                        (lblv hcp) sBBD))
            cliE
            (λ hPre hRecv →
               bundle-recvBFBlock-forces-src linkBD hi lo (λ ())
                 (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
                 (subst (λ z → absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ─[ ev (evl z) ]─► _)
                        (lblv (consAdv-recv-src cadv hPre hRecv)) sBBD))
            cfix
            -- SESSION-56: the driver step, carried instead of dropped
            sDBD
            -- (grant #8) BD fired ⇒ its client's row is the bundle's; node D's CD
            -- client sits in the untouched CD bundle
            cliRow (cliApiRow-fix linkCD hi (SN.NodeStateD.bfC-CD nd) e a)
            -- (T6c, grant #12) BD fired at `hi lo`, so the bundle's own CS-CLIENT row
            -- IS the tracked down-hop slot's; the CD bundle is untouched
            cscRow (cscApiRow-fix linkCD hi (SN.NodeStateD.csC-CD nd) e a)
            -- (T8c-iii) … §2b⁵'s sharpening on the FIRING leg, and the co-leg's own
            -- client slot is a LITERAL in this successor, so its fixity is `refl`
            cscFired refl
            -- (T11e) §2b⁷'s landing, off this bundle's own twenty-fourth slot
            reqLand

-- firing link = linkCD: cons-CD advances (genuine), cons-BD/bfC-BD literal
nodeD-api-CD-evo⁺ : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
                    {B₁ D₁CD : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
     ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decConsD linkCD (SN.NodeStateD.cons-CD nd) ─[ ev (evl (evLabel X e a)) ]─► D₁CD
  → ApiHasLink linkCD e
  → NodeDApiEvo nd e a (B₁ ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ D₁CD))
nodeD-api-CD-evo⁺ nd {X} {e} {a} apimem bStep sDCD ahl
  with consDAdv-of⁺ linkCD (SN.NodeStateD.cons-CD nd) sDCD
... | b′ , cp′ , refl , cadv , lblv , cfix
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
           (absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) bStep
...   | PEA.evSync () _ _
...   | PEA.evL _ sBBD = ⊥-elim (absBundleG-api-no linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ahl (λ q → linkBD≢linkCD (sym q)) apimem (_ , sBBD))
...   | PEA.evBoth _ sBBD _ = ⊥-elim (absBundleG-api-no linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ahl (λ q → linkBD≢linkCD (sym q)) apimem (_ , sBBD))
...   | PEA.evR _ sBCD
      with absBundleG-api-evo⁺ linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) apimem sBCD
-- (T8c-ii) re-cut to BIND the twentieth component, the BD site's reason exactly
-- *** (T10) RE-CUT: `BundleApiEvo` grew a TWENTY-FIRST component (§2b′⁺'s
-- `sendBFBatchDone` landing) and this reader ends on a NON-wildcard, so it takes one
-- more binder — the banked Σ-append trap, EIGHTH sighting ***
-- (T11e) re-cut once more, spelling positions 21-23 so the TWENTY-FOURTH (§2b⁷'s
-- request landing) can be bound: this bundle is node D's OWN, so the landing is the
-- fact its BlockFetch api class needs.  The banked Σ-append trap, TWELFTH sighting
...     | csc′ , css′ , bfc′ , bfs′ , ip′ , eq , run , cliE , _ , _ , cliRow , _ , _ , _ , cscRow , _ , _ , _ , _ , cscFired , _ , _ , _ , reqLand =
          ndaCD (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd) csc′ css′ bfc′ bfs′ (consD b′ cp′) (SN.NodeStateD.inert-BD nd) ip′)
            (cong (λ z → (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ⦀ z) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (consD b′ cp′))) eq)
            (∥⇘⇙-wev-sync apiES _ _ apimem
               (⦀-wev-R _ _ (noOffer→viewV _ (bundleG-api-no linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ahl (λ q → linkBD≢linkCD (sym q)) apimem)) run)
               (ev→wev (⦀-ev-R _ (SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)) sDCD (noOffer→viewV _ (drvD-BD-no nd ahl)))))
            -- SESSION-40 anchor (mirror of the BD site)
            cadv refl refl (λ hcp → b′ , lblv hcp , refl ,
               bundle-recv-cliPos linkCD hi lo (λ ())
                 (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)
                 (subst (λ z → absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) ─[ ev (evl z) ]─► _)
                        (lblv hcp) sBCD))
            cliE
            (λ hPre hRecv →
               bundle-recvBFBlock-forces-src linkCD hi lo (λ ())
                 (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)
                 (subst (λ z → absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) ─[ ev (evl z) ]─► _)
                        (lblv (consAdv-recv-src cadv hPre hRecv)) sBCD))
            cfix
            -- SESSION-56: the driver step, carried instead of dropped
            sDCD
            -- (grant #8) CD fired ⇒ node D's BD client is literal and its CD
            -- client's row is the bundle's
            (cliApiRow-fix linkBD hi (SN.NodeStateD.bfC-BD nd) e a) cliRow
            -- (T6c, grant #12) the CD mirror
            (cscApiRow-fix linkBD hi (SN.NodeStateD.csC-BD nd) e a) cscRow
            -- (T8c-iii) … the CD mirror
            cscFired refl
            -- (T11e) … and §2b⁷'s landing, likewise
            reqLand

-- node-D api inversion, ⁺ (`nodeD-ev-api-drv`'s dispatch verbatim)
nodeD-ev-api-evo⁺ : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
                    {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeD nd ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeDApiEvo nd e a M
nodeD-ev-api-evo⁺ nd {X} {e} {a} apimem step
  with SStep.reflect-node-api
         (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
          ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
         (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd)) (SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)) dStep
... | PEA.evSync () _ _
... | PEA.evL _ sDBD = nodeD-api-BD-evo⁺ nd apimem bStep sDBD (decConsD-ev-link linkBD (SN.NodeStateD.cons-BD nd) sDBD)
... | PEA.evR _ sDCD = nodeD-api-CD-evo⁺ nd apimem bStep sDCD (decConsD-ev-link linkCD (SN.NodeStateD.cons-CD nd) sDCD)
... | PEA.evBoth _ sDBD sDCD = ⊥-elim (linkBD≢linkCD
        (apiLink-inj (decConsD-ev-link linkBD (SN.NodeStateD.cons-BD nd) sDBD)
                     (decConsD-ev-link linkCD (SN.NodeStateD.cons-CD nd) sDCD)))

------------------------------------------------------------------------
-- §9  THE api-SIDE LEAF RECORD, DISCHARGED, AND THE ⁺ VISIBLE CONE.
--
-- `VisLeaves⁺` carries exactly `LiveLegStep`'s four `VisLeaves` field TYPES —
-- leaf 6 once per leg end, leaf 7, leaf 9 — with leaf 9 stated through the
-- PREDICATE `RelayAt` and never the projection-like accessor `relayBlk`
-- (`PipeValRelay`'s banked Agda 2.8 ICE rule).  `driverExpose⁺` is the frozen
-- `PipeEvDriverCone.driverExpose` re-mirrored at the ⁺ node peels — ALL FOUR of
-- them, node D's included since §8.  Node D holds no leg BF server, so both legs'
-- `VisLeaves⁺` are entirely fixed on that branch; what its branch DOES report is
-- the two down-hop client rows.
------------------------------------------------------------------------

-- `RelayHas` and `RelayFwd` are DISJOINT: a fixed relay cannot be both
relayHas-fwd-⊥ : (r : CPPh) → RelayHas r → RelayFwd r → ⊥
relayHas-fwd-⊥ (consuming _ cp0) () _
relayHas-fwd-⊥ (consuming _ cp1) () _
relayHas-fwd-⊥ (consuming _ cp2) () _
relayHas-fwd-⊥ (consuming _ cp3) () _
relayHas-fwd-⊥ (consuming _ cp4) _ ()
relayHas-fwd-⊥ (consuming _ cp5) _ ()
relayHas-fwd-⊥ (consuming _ cp6) _ ()
relayHas-fwd-⊥ (producing _ pp0) _ ()
relayHas-fwd-⊥ (producing _ pp1) _ ()
relayHas-fwd-⊥ (producing _ pp2) _ ()
relayHas-fwd-⊥ (producing _ pp3) _ ()
relayHas-fwd-⊥ (producing _ pp4) _ ()
relayHas-fwd-⊥ (producing _ pp5) _ ()
relayHas-fwd-⊥ (producing _ pp6) () _
relayHas-fwd-⊥ (producing _ pp7) () _
relayHas-fwd-⊥ (producing _ pp8) () _
relayHas-fwd-⊥ (producing _ pp9) () _

-- the four api-side step facts the visible arm needs, now PROVED per step
record VisLeaves⁺ (l : TwoLegs) (s s′ : SysState) : Set where
  constructor visLeaves⁺
  field
    vUpSrvKeep : (upSrv l s ≡ upSrv l s′) ⊎ (BFsHasBlk (upSrv l s) → ⊥)
    vDnSrvKeep : (dnSrv l s ≡ dnSrv l s′) ⊎ (BFsHasBlk (dnSrv l s) → ⊥)
    vProdSend  : ProdNotSent (prodOf l s) → ProdSent (prodOf l s′)
               → upSrv l s′ ≡ bsBlk1 blkA
    vRelayFwd⁺ : (b : Block₃) → RelayAt b (relayOf l s) → RelayHas (relayOf l s)
               → RelayFwd (relayOf l s′) → dnSrv l s′ ≡ bsBlk1 b
    -- SESSION-55 (`LiveTokenExcl` P3): the two SOURCE-PHASE fields, beside
    -- `vProdSend`/`vRelayFwd⁺` whose CONSEQUENT halves they complete.  A visible
    -- step that makes a leg server GAIN a block IS that end's own hand-over, so
    -- its source phase is named: node A's producer has NOT yet sent, the relay is
    -- still HOLDING.  These are what let the exclusions refute every other
    -- occupancy from the source phase's own coupling.
    vUpSrvGain : (BFsHasBlk (upSrv l s) → ⊥) → BFsHasBlk (upSrv l s′)
               → ProdNotSent (prodOf l s)
    vDnSrvGain : (BFsHasBlk (dnSrv l s) → ⊥) → BFsHasBlk (dnSrv l s′)
               → RelayHas (relayOf l s)
    -- *** (T10) THE `pp6` LANDING — `vProdSend`'s twin one crossing along, and the
    -- ONE fact node A's up-hop BF coupling cannot get from the row disjunction. ***
    -- The `pp6 → pp7` step is node A's own `sendBFBatchDone` api sync, so a server
    -- that was streaming is at `bsWbd` after it.  The "the driver MOVED" antecedent
    -- is what makes the untouched-leg arms answer: at a FIXED producer the two
    -- phases are equal and the hypothesis is contradictory (`visLeaves-fix` below),
    -- which is the same device `vProdSend` uses through `ProdNotSent`/`ProdSent`
    vProdBd    : prodOf l s ≡ SN.pp6 → (prodOf l s′ ≡ SN.pp6 → ⊥)
               → (coarsenBFs (upSrv l s) ≡ NS.bsStream)
                 × (coarsenBFs (upSrv l s′) ≡ NS.bsWbd)
    -- *** (T10) … AND THE BATCH-REGION KEEP BESIDE IT. ***  The two are one object
    -- in use — the pair closes the ONE crossing that leaves the batch, the keep
    -- closes every step already past it — and they are two FIELDS only because
    -- their antecedents are disjoint phase regions (`≡ pp6` against `ProdDone`), so
    -- no producer can create a combination the pair admits (the merged-field pass,
    -- recorded)
    vUpDone    : ProdDone (prodOf l s) → SrvBatch (coarsenBFs (upSrv l s′))
               → SrvBatch (coarsenBFs (upSrv l s))
open VisLeaves⁺ public

-- the leg is UNTOUCHED by the firing node: both servers fixed, and both
-- hand-over facts vacuous (a fixed producer cannot cross not-sent → sent, a
-- fixed relay cannot be holding AND forwarded)
visLeaves-fix : (l : TwoLegs) (s s′ : SysState)
  → upSrv l s ≡ upSrv l s′ → dnSrv l s ≡ dnSrv l s′
  → prodOf l s ≡ prodOf l s′ → relayOf l s ≡ relayOf l s′
  → VisLeaves⁺ l s s′
visLeaves-fix l s s′ ue de pe re = visLeaves⁺ (inj₁ ue) (inj₁ de)
  (λ hn hs → ⊥-elim (prodSent-notSent-⊥ (prodOf l s) (subst ProdSent (sym pe) hs) hn))
  (λ b rat hH hF → ⊥-elim (relayHas-fwd-⊥ (relayOf l s) hH (subst RelayFwd (sym re) hF)))
  (λ ¬h h → ⊥-elim (¬h (subst BFsHasBlk (sym ue) h)))
  (λ ¬h h → ⊥-elim (¬h (subst BFsHasBlk (sym de) h)))
  -- (T10) a FIXED producer cannot have left `pp6`
  (λ h6 ¬h6 → ⊥-elim (¬h6 (trans (sym pe) h6)))
  -- (T10) the leg's up server is FIXED here, so the keep is a transport
  (λ _ hb → subst (λ z → SrvBatch (coarsenBFs z)) (sym ue) hb)

------------------------------------------------------------------------
-- §9a  *** (P7) THE PRODUCER LANDING AT THE CONE'S OWN SUCCESSOR. ***
--
-- `LiveFSim`'s (P7) asks, at the cone's own existential successor, for "the
-- kept `sendBFBlock` on the leg's UP key put the sent block in that leg's up BF
-- server".  Generically (the cone quantifies over `(e , a)`) that is exactly
-- `SrvLands (upLinkOf l) hi e a (upSrv l s′)` — the fact `srvUp-of` built and
-- dropped, now kept as `SrvUpFacts`' seventh component and re-exported here as
-- a per-leg slot of `driverExpose⁺`.
--
-- Node A's two arms take it from that component (firing leg) and refute it from
-- the new fired-link pin (co-leg).  The other four arms are VACUOUS: no node but
-- A fires a `sendBFBlock` on `linkAB`/`linkAC` at all, and the three helpers
-- below say so from the banked `PipeProdFire` refutations — one per node, cased
-- on the leg, with the successor server slot left implicit because the
-- conclusion is never reached.
------------------------------------------------------------------------

-- (P7) leg `l`'s PRODUCER LANDING at the successor: a `sendBFBlock` at the leg's
-- UP key lands exactly the sent block in that leg's upstream BF server
LegProdLands : (l : TwoLegs) (s′ : SysState) {X : Set 0ℓ}
               (e : Net_Api Payload X) (a : X) → Set
LegProdLands l s′ e a = SrvLands (upLinkOf l) hi e a (upSrv l s′)

-- node B fired: on `linkAB` it hosts the CONSUME leg (never a `sendBFBlock`),
-- and its produce leg is `linkBD` — neither of node A's up keys, so both legs'
-- producer landings are vacuous
prodLands-B : (nb : SN.NodeStateB) (l : TwoLegs) {X : Set 0ℓ} {e : Net_Api Payload X}
              {a : X} {M : NetProc} {q : BFsPos}
            → apiES .mem (X , e) a
            → absNodeB nb ─[ ev (evl (evLabel X e a)) ]─► M
            → SrvLands (upLinkOf l) hi e a q
prodLands-B nb legBD {e = e} {a} apimem st b″ sd with sbbAt⇒pin e a sd
... | sbb , ahl , _ = ⊥-elim (nodeB-sbb-AB-⊥ nb apimem st sbb ahl)
prodLands-B nb legCD {e = e} {a} apimem st b″ sd with sbbAt⇒pin e a sd
... | sbb , ahl , _ with nodeB-link nb apimem st
...   | inj₁ ahlAB = ⊥-elim (linkAB≢linkAC (apiLink-inj ahlAB ahl))
...   | inj₂ ahlBD = ⊥-elim (linkAC≢linkBD (sym (apiLink-inj ahlBD ahl)))

-- node C fired: the mirror (`linkAC` is its consume leg, `linkCD` its produce)
prodLands-C : (nc : SN.NodeStateC) (l : TwoLegs) {X : Set 0ℓ} {e : Net_Api Payload X}
              {a : X} {M : NetProc} {q : BFsPos}
            → apiES .mem (X , e) a
            → absNodeC nc ─[ ev (evl (evLabel X e a)) ]─► M
            → SrvLands (upLinkOf l) hi e a q
prodLands-C nc legBD {e = e} {a} apimem st b″ sd with sbbAt⇒pin e a sd
... | sbb , ahl , _ with nodeC-link nc apimem st
...   | inj₁ ahlAC = ⊥-elim (linkAB≢linkAC (sym (apiLink-inj ahlAC ahl)))
...   | inj₂ ahlCD = ⊥-elim (linkAB≢linkCD (sym (apiLink-inj ahlCD ahl)))
prodLands-C nc legCD {e = e} {a} apimem st b″ sd with sbbAt⇒pin e a sd
... | sbb , ahl , _ = ⊥-elim (nodeC-sbb-AC-⊥ nc apimem st sbb ahl)

-- node D fired: its two api links are `linkBD`/`linkCD`, neither of them an up
-- key, so the link pin alone refutes both legs
prodLands-D : (nd : SN.NodeStateD) (l : TwoLegs) {X : Set 0ℓ} {e : Net_Api Payload X}
              {a : X} {M : NetProc} {q : BFsPos}
            → apiES .mem (X , e) a
            → absNodeD nd ─[ ev (evl (evLabel X e a)) ]─► M
            → SrvLands (upLinkOf l) hi e a q
prodLands-D nd legBD {e = e} {a} apimem st b″ sd with sbbAt⇒pin e a sd
... | sbb , ahl , _ with nodeD-link nd apimem st
...   | inj₁ ahlBD = ⊥-elim (linkAB≢linkBD (sym (apiLink-inj ahlBD ahl)))
...   | inj₂ ahlCD = ⊥-elim (linkAB≢linkCD (sym (apiLink-inj ahlCD ahl)))
prodLands-D nd legCD {e = e} {a} apimem st b″ sd with sbbAt⇒pin e a sd
... | sbb , ahl , _ with nodeD-link nd apimem st
...   | inj₁ ahlBD = ⊥-elim (linkAC≢linkBD (sym (apiLink-inj ahlBD ahl)))
...   | inj₂ ahlCD = ⊥-elim (linkAC≢linkCD (sym (apiLink-inj ahlCD ahl)))

------------------------------------------------------------------------
-- §9b  *** (P8) THE CONSUMER LANDING AT THE CONE'S OWN SUCCESSOR. ***
--
-- `LiveFSim`'s (P8) asks, at the cone's own successor, for "the kept
-- `recvBFBlock` on the leg's own key was TAKEN by that leg's cell, and the block
-- it carried is the one the cell now records".  Stated here as `phOf l s′ ≡ cp4`
-- (the flag reader `pastRecv` is one `cong` above this module, and keeping it out
-- avoids importing the coupling into the cone) plus the block equation.
--
-- Node D's own arms get it from THREE facts, all now in hand: the granted driver
-- step re-opens the `cp3` gate (`decConsD-rbb-cp3`), `ldCons`' existing `ConsAdv`
-- then forces `cp4` (`consAdv-cp3-cp4`), and the SESSION-40 anchor names the
-- recorded block, tied to the label's by `rbbAt-inj`.  The CO-leg is refuted by
-- the fired link the same driver step yields — the case the gate report found
-- provably undecidable from the projected fields alone.  The other four arms are
-- VACUOUS: nodes A/B/C are producer-role or consume on non-delivery keys.
------------------------------------------------------------------------

-- (P8) leg `l`'s CONSUMER LANDING at the successor: a `recvBFBlock` at the leg's
-- own key crossed that leg's cell past the receive and left the block recorded
LegRecvLands : (l : TwoLegs) (s′ : SysState) {X : Set 0ℓ}
               (e : Net_Api Payload X) (a : X) → Set
LegRecvLands l s′ e a = (b : Block) → RbbAt (linkOf l) hi b e a
                      → (phOf l s′ ≡ cp4) × (cblkOf l s′ ≡ b)

-- node A fired: every api event node A can fire is PRODUCER-role, and a
-- `recvBFBlock` is consumer-role — so both legs' landings are vacuous
-- (`s′` is EXPLICIT: it occurs in `LegRecvLands` only under `phOf`/`cblkOf`, so
-- unification cannot solve it from the expected type)
recvLands-A : (na : SN.NodeStateA) (l : TwoLegs) (s′ : SysState)
              {X : Set 0ℓ} {e : Net_Api Payload X}
              {a : X} {M : NetProc}
            → apiES .mem (X , e) a
            → absNodeA na ─[ ev (evl (evLabel X e a)) ]─► M
            → LegRecvLands l s′ e a
recvLands-A na l s′ {e = e} {a} apimem st b rb =
  ⊥-elim (prod≢cons (proj₁ (absNodeA-fp na apimem st))
                    (proj₁ (rbbAt⇒pin e a rb)))

-- node B fired: as a CONSUMER it is on `linkAB` (neither delivery key), and on
-- `linkBD` it is the PRODUCER — either branch refutes the landing
recvLands-B : (nb : SN.NodeStateB) (l : TwoLegs) (s′ : SysState)
              {X : Set 0ℓ} {e : Net_Api Payload X}
              {a : X} {M : NetProc}
            → apiES .mem (X , e) a
            → absNodeB nb ─[ ev (evl (evLabel X e a)) ]─► M
            → LegRecvLands l s′ e a
recvLands-B nb legBD s′ {e = e} {a} apimem st b rb with rbbAt⇒pin e a rb
... | aic , ahl , _ with absNodeB-fp nb apimem st
...   | inj₁ (_ , ahlAB) = ⊥-elim (linkAB≢linkBD (apiLink-inj ahlAB ahl))
...   | inj₂ (aip , _)   = ⊥-elim (prod≢cons aip aic)
recvLands-B nb legCD s′ {e = e} {a} apimem st b rb with rbbAt⇒pin e a rb
... | aic , ahl , _ with absNodeB-fp nb apimem st
...   | inj₁ (_ , ahlAB) = ⊥-elim (linkAB≢linkCD (apiLink-inj ahlAB ahl))
...   | inj₂ (aip , _)   = ⊥-elim (prod≢cons aip aic)

-- node C fired: the mirror (`linkAC` consume, `linkCD` produce)
recvLands-C : (nc : SN.NodeStateC) (l : TwoLegs) (s′ : SysState)
              {X : Set 0ℓ} {e : Net_Api Payload X}
              {a : X} {M : NetProc}
            → apiES .mem (X , e) a
            → absNodeC nc ─[ ev (evl (evLabel X e a)) ]─► M
            → LegRecvLands l s′ e a
recvLands-C nc legBD s′ {e = e} {a} apimem st b rb with rbbAt⇒pin e a rb
... | aic , ahl , _ with absNodeC-fp nc apimem st
...   | inj₁ (_ , ahlAC) = ⊥-elim (linkAC≢linkBD (apiLink-inj ahlAC ahl))
...   | inj₂ (aip , _)   = ⊥-elim (prod≢cons aip aic)
recvLands-C nc legCD s′ {e = e} {a} apimem st b rb with rbbAt⇒pin e a rb
... | aic , ahl , _ with absNodeC-fp nc apimem st
...   | inj₁ (_ , ahlAC) = ⊥-elim (linkAC≢linkCD (apiLink-inj ahlAC ahl))
...   | inj₂ (aip , _)   = ⊥-elim (prod≢cons aip aic)


-- (T3b) the ⁺ whole-nodes visible cone's REPORT, as a record with NAMED FIELDS.
--
-- *** WHY A RECORD AND NOT THE POSITIONAL `Σ` IT REPLACES. ***  The report grew
-- to twenty-three slots by APPENDING (grant #6's freeze, grant #8's up-hop rows,
-- task 5's down-hop rows, T1's driver pairs), and every one of the twelve reading
-- sites bound it by POSITION behind a trailing wildcard.  Appending was therefore
-- safe, but an INSERTION shifted every binder after it while the wildcard absorbed
-- the tail, so the mistake surfaced — if at all — far from where it was made, and
-- was INVISIBLE outright wherever two adjacent slots had convertible types.
-- (T3b measured this rather than repeating it: the review that booked the debt said
-- "undetectable at eleven of twelve"; the honest statement is that the `Σ` was silent
-- CONDITIONALLY on adjacent-slot type coincidence, and non-local always.  The T3b
-- REVIEW then exhausted all 22 adjacencies of the 23-slot `Σ` and found NO convertible
-- pair — so a pure shift was never silent, and silence needed a type-DUPLICATING
-- insertion.  That shape is exactly T4's: a CS `VisLeaves⁺`- or CS row-pair-typed slot
-- placed before its BF twin.  Do not read the narrowing as "the `Σ` was safe".)
--
-- *** WHAT THE RECORD BUYS, AND WHAT IT DOES NOT. ***  It buys (i) UNCONDITIONALITY —
-- every wrong-field read is a type error SOMEWHERE, with no type-coincidence escape and
-- no wildcard able to absorb a shift — and (ii) a by-NAME audit trail at the read site,
-- so the intended slot is on the page.  It does NOT buy error LOCALITY: falsification
-- F22, run in THIS record form, mutated `LiveChanJoin:924` and was reported at `:941`,
-- seventeen lines away inside the `_`-typed `rowsUp` selector — the same non-locality
-- the `Σ` had.  Locality fails wherever the value passes through an inferred-type
-- helper.  Nor does it close an unsoundness: a mis-bound PROOF slot still has to
-- discharge the consumer's stated goal, so the only slot whose mis-binding changes
-- meaning at unchanged type is the DATA slot `deSucc` — position 1, never shifted by an
-- append, and pinned by `LiveFSim` §D's two probes.
--
-- The `Σ` had one property this loses — a reader could take a positional PREFIX without
-- naming the tail — which is exactly the property that made the mis-bind absorbable, so
-- it is given up deliberately.
--
-- ASSEMBLY slice A1: the two `LegValStep`s are LATE FIELDS, exactly as the frozen
-- `PipeEvDriverCone.driverExpose` appends them (session-51), and from the very
-- same witnesses — node A's `upRaw` is the ⁺ `SrvUpFacts`' second component (the
-- RAW `SrvValEvo`), node B/C's `dnRaw`/`rvalB`/`rvalC` are the ⁺ `SrvDnFacts`'
-- second component and the relay classifier's value map, and node D's `cfixD` is
-- the frozen peel's own recorded-block fixity.  WITHOUT them the wiring of
-- `LiveLegStep`'s visible arm is IMPOSSIBLE from this cone: that arm needs a
-- `LegValStep` beside the `LegDriverStep`, and a second peel (of the frozen
-- `driverExpose`) would land at a DIFFERENT existential successor.
record DriverExposed⁺ (s : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                      (M : NetProc) : Set₁ where
  constructor mkDrvExp⁺
  field
    -- the cone's OWN existential successor: the term every downstream
    -- successor-identity coupling names (`LiveFSim` §D's two `refl` tripwires)
    deSucc  : SysState
    deMed   : med s ≡ med deSucc
    deProc  : M ≡ absNodesOf deSucc
    deRun   : nodesOf s ═[ ev (evl (evLabel X e a)) ]═► nodesOf deSucc
    -- the two legs' driver steps
    deLdBD  : LegDriverStep legBD s deSucc e a
    deLdCD  : LegDriverStep legCD s deSucc e a
    -- the two legs' server evolutions, up hop and down hop
    deSrvBD : UpSrvEvo legBD s deSucc × DnSrvEvo legBD s deSucc
    deSrvCD : UpSrvEvo legCD s deSucc × DnSrvEvo legCD s deSucc
    -- the api-side leaf record, PROVED per leg
    deVlBD  : VisLeaves⁺ legBD s deSucc
    deVlCD  : VisLeaves⁺ legCD s deSucc
    -- the two legs' value steps (ASSEMBLY slice A1)
    deLvBD  : LegValStep legBD s deSucc e a
    deLvCD  : LegValStep legCD s deSucc e a
    -- (P7) §9a: the two producer LANDINGS at this very successor
    dePlBD  : LegProdLands legBD deSucc e a
    dePlCD  : LegProdLands legCD deSucc e a
    -- (P8) §9b: and the two consumer LANDINGS
    deRlBD  : LegRecvLands legBD deSucc e a
    deRlCD  : LegRecvLands legCD deSucc e a
    -- (P5) grant #6: node B's link-AB KA-client freeze.  Only node B's bundle
    -- needs a report: in the three other arms the successor's `nB` is LITERAL,
    -- so the answer is the identity.
    deFrzB  : IsApiCSBF e → KAcAtHead (SN.NodeStateB.inert-AB (nB s))
                          → KAcAtHead (SN.NodeStateB.inert-AB (nB deSucc))
    -- (grant #8) each leg's UP-HOP adjacency rows — the hop's server (node A's)
    -- and its client (the relay's).  This is what the `ChanUp` join's VISIBLE arm
    -- consumes.
    deRowsAB : SrvApiRowP linkAB hi (SN.NodeStateA.bfS-AB (nA s)) (SN.NodeStateA.bfS-AB (nA deSucc)) e a
               × CliApiRowP linkAB hi (SN.NodeStateB.bfC-AB (nB s)) (SN.NodeStateB.bfC-AB (nB deSucc)) e a
    deRowsAC : SrvApiRowP linkAC hi (SN.NodeStateA.bfS-AC (nA s)) (SN.NodeStateA.bfS-AC (nA deSucc)) e a
               × CliApiRowP linkAC hi (SN.NodeStateC.bfC-AC (nC s)) (SN.NodeStateC.bfC-AC (nC deSucc)) e a
    -- (task 5, grant-free) each leg's DOWN-HOP adjacency rows — the hop's server
    -- (the relay's own, already reported by §7's node-B/C peels) and its client
    -- (node D's, from §8's ⁺ re-mirror, which calls the grant-#8 row reporter
    -- DIRECTLY instead of the un-widened `BundleGEvR⁺`).  This is what the
    -- `ChanDn` join's VISIBLE arm consumes.
    deRowsBD : SrvApiRowP linkBD hi (SN.NodeStateB.bfS-BD (nB s)) (SN.NodeStateB.bfS-BD (nB deSucc)) e a
               × CliApiRowP linkBD hi (SN.NodeStateD.bfC-BD (nD s)) (SN.NodeStateD.bfC-BD (nD deSucc)) e a
    deRowsCD : SrvApiRowP linkCD hi (SN.NodeStateC.bfS-CD (nC s)) (SN.NodeStateC.bfS-CD (nC deSucc)) e a
               × CliApiRowP linkCD hi (SN.NodeStateD.bfC-CD (nD s)) (SN.NodeStateD.bfC-CD (nD deSucc)) e a
    -- (T1 / S1) each leg's driver-phase / down-server pair across this step.  This
    -- is what the BF driver-tail coupling's api arm reads, and the reason it must
    -- be reported HERE is that the two fixity equations are only available where
    -- the successor's node records are LITERAL.
    deDnDrvBD : DnSrvDrv legBD s deSucc
    deDnDrvCD : DnSrvDrv legCD s deSucc
    -- (T4) each leg's CS-axis adjacency facts across this step: the leg's UP-hop CS
    -- CLIENT (the relay's own, on the leg's UP link — the `cp5` slot) and its DOWN-hop
    -- CS SERVER (the relay's own, on the leg's DOWN link — the `pp1`/`pp2` slot).
    -- APPENDED, not inserted: a CS row-pair slot placed before its BF twin
    -- (`deRowsAB`…) is precisely the type-DUPLICATING insertion the T3b review named
    -- as this task's hazard, and the record makes a wrong-field read a type error
    -- rather than a silent shift.  Both peers live on the RELAY node, so three of the
    -- four arms answer with the fixity and only the relay's own arm carries a row.
    deCSRowsBD : CScApiRowP linkAB hi (SN.NodeStateB.csC-AB (nB s)) (SN.NodeStateB.csC-AB (nB deSucc)) e a
                 × CSsApiRowP linkBD hi (SN.NodeStateB.csS-BD (nB s)) (SN.NodeStateB.csS-BD (nB deSucc)) e a
    deCSRowsCD : CScApiRowP linkAC hi (SN.NodeStateC.csC-AC (nC s)) (SN.NodeStateC.csC-AC (nC deSucc)) e a
                 × CSsApiRowP linkCD hi (SN.NodeStateC.csS-CD (nC s)) (SN.NodeStateC.csS-CD (nC deSucc)) e a
    -- (T5) each leg's `pp1` LANDING at its DOWN-hop CS SERVER, in T1's own
    -- fixity-or-landing shape — and since (T6d) the landing half is the PAIR
    -- `DnCsReqLand × DnCsAwLand`, the `pp1` position beside the `pp2` region's entry,
    -- exactly as `DnSrvDrv`'s landing half is the pair `DnReqLand × DnSbLand`.  No new
    -- field: one relay step is one driver advance, so both landings live in the arm
    -- that reports it.  APPENDED behind the T4 rows for the T4 reason, and
    -- stated at the node fields rather than at the leg because `DnCsDrv` is — the cone
    -- cannot see `LiveRelayOpen.dnCSs` without an import cycle, and the consumer's
    -- per-leg selector is what makes the two forms convertible.
    deCsDrvBD : DnCsDrv linkBD (SN.NodeStateB.csS-BD (nB s)) (SN.NodeStateB.csS-BD (nB deSucc))
                        (SN.NodeStateB.cp-B (nB s)) (SN.NodeStateB.cp-B (nB deSucc))
    deCsDrvCD : DnCsDrv linkCD (SN.NodeStateC.csS-CD (nC s)) (SN.NodeStateC.csS-CD (nC deSucc))
                        (SN.NodeStateC.cp-C (nC s)) (SN.NodeStateC.cp-C (nC deSucc))
    -- (T6c, grant #12) each leg's UP-hop CS SERVER (node A's) and DOWN-hop CS CLIENT
    -- (node D's) — the two api slots the ChainSync channel invariant's JOIN was
    -- missing.  Both were already carried by EVERY bundle's `BundleApiEvo`
    -- (`LiveLegApiCone:1275-1276`) at every label; only the threading was absent, so
    -- unlike the io half this needed no grant.  APPENDED behind the T4/T5 rows for
    -- the T4 reason.
    deCSUpSrvBD : CSsApiRowP linkAB hi (SN.NodeStateA.csS-AB (nA s)) (SN.NodeStateA.csS-AB (nA deSucc)) e a
    deCSUpSrvCD : CSsApiRowP linkAC hi (SN.NodeStateA.csS-AC (nA s)) (SN.NodeStateA.csS-AC (nA deSucc)) e a
    deCSDnCliBD : CScApiRowP linkBD hi (SN.NodeStateD.csC-BD (nD s)) (SN.NodeStateD.csC-BD (nD deSucc)) e a
    deCSDnCliCD : CScApiRowP linkCD hi (SN.NodeStateD.csC-CD (nD s)) (SN.NodeStateD.csC-CD (nD deSucc)) e a
    -- (T7) each leg's `cp5` CHAIN at its UP-hop CS CLIENT, in T1's own
    -- fixity-or-landing shape — and the landing half is the FOUR-tuple
    -- `UpCsRfLand × UpCsStep cp2 cp3 × UpCsStep cp3 cp4 × UpCsStep cp4 cp5`, because
    -- only the chain's FIRST sub-phase is a landing and the other three are carried by
    -- the client's fixity across BlockFetch api events (`LiveLegApiCone.UpCsDrv`'s
    -- header says why, and why the refutation polarity is the MIRROR of `deCsDrv*`'s).
    -- No new record beyond these two fields: one relay step is one driver advance, so
    -- all four facts live in the arm that reports it.  APPENDED behind the T6c rows for
    -- the T4 reason, and stated at the node fields because `UpCsDrv` is — the cone
    -- cannot see `LiveRelayOpen.upCSc` without an import cycle, and the consumer's
    -- per-leg selector is what makes the two forms convertible.
    deUpCsDrvBD : UpCsDrv linkAB (SN.NodeStateB.csC-AB (nB s)) (SN.NodeStateB.csC-AB (nB deSucc))
                          (SN.NodeStateB.cp-B (nB s)) (SN.NodeStateB.cp-B (nB deSucc))
    deUpCsDrvCD : UpCsDrv linkAC (SN.NodeStateC.csC-AC (nC s)) (SN.NodeStateC.csC-AC (nC deSucc))
                          (SN.NodeStateC.cp-C (nC s)) (SN.NodeStateC.cp-C (nC deSucc))
    -- *** (T8c-0) THE TWO LANDING-CLASS FACTS THE CONE HELD AND DID NOT CARRY OUT. ***
    -- Both are the SAME kind of gap and both cost one field: the determining datum is
    -- the firing driver's own STEP, the cone binds it at its four `dStep` sites and at
    -- node D's two, and every field above is an already-APPLIED consequence — so a
    -- consumer that needs the step's SHAPE (rather than one of its consequences) had
    -- nothing to read.  APPENDED behind the T7 pair for the T4 reason.
    --
    -- (1) each leg's RELAY driver phase ADVANCE, in the standing fixity-or-fired shape.
    -- `deLdBD`/`deLdCD`'s `RelayStepKind` provably CANNOT determine it — it is inhabited
    -- at `(producing b pp1 , producing b pp0)`, which is no advance at all — so any
    -- consumer separating `pp0` from `pp1` was stuck (`LiveDrvCSD` §5e's four
    -- machine-checked refutations).  Off `cpStepKindQ-of⁺`'s new EIGHTEENTH component,
    -- so `x′` is single-sourced with the classifier's own answer.
    deRelayAdvBD : (SN.NodeStateB.cp-B (nB s) ≡ SN.NodeStateB.cp-B (nB deSucc))
                   ⊎ RelayAdv (SN.NodeStateB.cp-B (nB s)) (SN.NodeStateB.cp-B (nB deSucc))
    deRelayAdvCD : (SN.NodeStateC.cp-C (nC s) ≡ SN.NodeStateC.cp-C (nC deSucc))
                   ⊎ RelayAdv (SN.NodeStateC.cp-C (nC s)) (SN.NodeStateC.cp-C (nC deSucc))
    -- (2) each leg's NODE-D consume driver STEP.  This one needed no new cone work at
    -- all: `NodeDApiEvo`'s two constructors have carried it since grant #5 (the
    -- SESSION-56 field) and only the threading was absent.  With it a consumer can pin
    -- the FIRED LABEL per phase — which is what `ConsAdv` plus a label-directed peer row
    -- provably cannot do (`LiveDrvCSD` §5e's probes B1/B2).
    --
    -- *** THE GUARDS ON THIS THREADING LIVE AT `LiveDrvCSD` §7c *** — F64 (a wrong-ARM
    -- relay field, red at the `inj₁ refl` left on the other leg) and F65 (a wrong-LEG
    -- node-D step).  They mutate `driverExpose⁺`'s arms below but are recorded where the
    -- threaded facts are CONSUMED, so a reader arriving here is pointed there.
    -- *** (T8c-iii) NODE D's WHOLE LEG ACROSS THIS STEP, AS ONE FIELD PER LEG —
    -- the shape that replaced T8c-ii's two, and the reason is a REFUTATION. ***
    --
    -- T8c-ii shipped these as two separate fixity-or-fired disjunctions
    -- (`deConsStepBD` for the driver's step, `deCsCliBD` for `LiveLegApiCone` §2b⁵'s
    -- sharpening).  BOTH earlier shapes are wrong, and the record of why is worth more
    -- than the field:
    --
    --   · TWO INDEPENDENT DISJUNCTIONS ARE UNUSABLE AT THE CONSUMER.  At node D's
    --     `cp0 → cp1` hop the api carry holds the driver's step (so the driver moved)
    --     and must produce `CliAt cp1 (dnCScC l s′)`; if the sharpening's field reads
    --     `inj₁`, the client is reported FIXED at `ccIdle` while its own driver fired
    --     `sendCSRequestNext` — exactly the state the sharpening exists to exclude, so
    --     excluding it needs the sharpening.  CIRCULAR.  `deCSDnCliBD`'s own
    --     disjunction has the same defect at the same hop, so it is no escape, and
    --     neither is `DrvCliD`'s `cp0` clause (that gives the SOURCE `ccIdle`, which is
    --     what makes the successor unusable rather than what refutes it).
    --   · AND AN UNCONDITIONAL `CscCliFired` IS NOT MERELY DEARER — IT IS FALSE.
    --     `CsAt` is tag-GENERIC, and node B's own CS SERVER sits at the SAME KEY as
    --     node D's CS client: node B's BD bundle is `absBundleG linkBD lo hi`
    --     (`SysStep:770`) so its server's key is `(linkBD , hi)`, and node D's is
    --     `absBundleG linkBD hi lo` (`:781`) so its client's key is `(linkBD , hi)`
    --     TOO.  When node B's server fires `apiCS linkBD hi reqCSRequestNext`
    --     (`NodeSpecs.csSnxt:428`) the pin HOLDS, node D's client is untouched, and
    --     `csCnxt` has no `reqCSRequestNext` row at all — so the demanded row does not
    --     exist.  Scoping the pin to the client's own TAGS would restore truth (the two
    --     peers' `apiCS` tag sets are disjoint — `sendCSRequestNext` occurs only in
    --     `csCnxt`), but then the four non-node-D arms must refute a tag-scoped pin at
    --     a key they SHARE, which needs a per-node tag-refusal family nobody has.
    --
    -- *** SO THE DICHOTOMY THE RECORD SHOULD EXPRESS IS THE TRUE ONE: either node D's
    -- leg is ENTIRELY untouched — driver AND client — or node D fired it, and then the
    -- step and the sharpening travel TOGETHER. ***  Every arm can supply that: the four
    -- non-node-D arms have node D's whole record literal (`inj₁ (refl , refl)`), and
    -- node D's own two arms have the step and the bundle's twentieth component on the
    -- firing leg and a literal record on the co-leg.  No OUT map, no tag scoping, no
    -- impossible combination — and the consumer's dispatch is total on the pair.
    --
    -- APPENDED in the T8c-0 pair's place, for the T4 reason.  *** THE GUARDS ON THIS
    -- FIELD LIVE AT `LiveDrvCSD` §7c/§7d/§7e *** (F64, F65, F68 and F74).
    --
    -- *** (T8c-iii, round 3) THE FIXITY HALF CARRIES THE PHASE EQUATION, NOT THE SLOT's.
    -- ***  The carry is LEG-STATED (`phOf l s ≡ phOf l s′`) and the slot equation is a
    -- `ConsDPh` one, so a leg selector cannot convert between them at a VARIABLE leg
    -- (measured: `[UnequalTerms] ConsDPh != ConsPh`).  The producers pay one `cong cph`;
    -- F74's projection guard is unaffected, because the co-leg's own projection is still
    -- what appears under the `cong`.
    -- *** (T11h) THE FIXITY HALF CARRIES THE dn BF CLIENT TOO. ***  A BF freshness
    -- region guarded on the RELAY's phase reads node D's BF client at every arm where
    -- node D did not fire, and `deRowsBD`'s `CliApiRowP` is a `⊎` that cannot say it:
    -- the impossible-combination trap §8 (i-b) records, at node D's own peer.  Free at
    -- every producer — the four non-node-D arms have node D's record LITERAL and node
    -- D's own two arms already report the CO-LEG's client fixity (`ndaBD`'s sixth field)
    deNodeDBD : ((cph (SN.NodeStateD.cons-BD (nD s)) ≡ cph (SN.NodeStateD.cons-BD (nD deSucc)))
                 × (SN.NodeStateD.csC-BD (nD s) ≡ SN.NodeStateD.csC-BD (nD deSucc))
                 × (SN.NodeStateD.bfC-BD (nD s) ≡ SN.NodeStateD.bfC-BD (nD deSucc)))
                ⊎ ((SN.decConsD linkBD (SN.NodeStateD.cons-BD (nD s))
                      ─[ ev (evl (evLabel X e a)) ]─►
                      SN.decConsD linkBD (SN.NodeStateD.cons-BD (nD deSucc)))
                   -- (T8c-iii, round 3) … and the hop's own PHASE PAIR beside the step.
                   -- The api carry needs `ConsAdv` at the STATE's pair to feed
                   -- `LiveDrvCSD.cliDrvAdj-of`, and recovering it from the step instead
                   -- would need `decConsD` injectivity; `NodeDApiEvo`'s third field IS
                   -- this adjacency, so it travels rather than being re-derived
                   × ConsAdv (cph (SN.NodeStateD.cons-BD (nD s))) (cph (SN.NodeStateD.cons-BD (nD deSucc)))
                   × CscCliFired linkBD hi (SN.NodeStateD.csC-BD (nD s))
                       (SN.NodeStateD.csC-BD (nD deSucc)) e a
                   -- *** (T11e) … and the TWO facts node D's BlockFetch api class
                   -- needs, both riding this arm because both are about the leg that
                   -- FIRED: *** §2b⁷'s request landing, and the `cp3` ANCHOR's source
                   -- at COARSE positions (`NodeDApiEvo`'s sixth field, `cong`-ed here
                   -- so the consumer reads a position and not a `bcBlk1`)
                   × CliReqLand linkBD hi (SN.NodeStateD.bfC-BD (nD s))
                       (SN.NodeStateD.bfC-BD (nD deSucc)) e a
                   × (cph (SN.NodeStateD.cons-BD (nD s)) ≡ cp3
                      → Σ[ b″ ∈ Block₃ ]
                          (coarsenBFc (SN.NodeStateD.bfC-BD (nD s)) ≡ NS.bcAblk b″)))
    -- *** (T11h) THE FIXITY HALF CARRIES THE dn BF CLIENT TOO. ***  A BF freshness
    -- region guarded on the RELAY's phase reads node D's BF client at every arm where
    -- node D did not fire, and `deRowsBD`'s `CliApiRowP` is a `⊎` that cannot say it:
    -- the impossible-combination trap §8 (i-b) records, at node D's own peer.  Free at
    -- every producer — the four non-node-D arms have node D's record LITERAL and node
    -- D's own two arms already report the CO-LEG's client fixity (`ndaBD`'s sixth field)
    deNodeDCD : ((cph (SN.NodeStateD.cons-CD (nD s)) ≡ cph (SN.NodeStateD.cons-CD (nD deSucc)))
                 × (SN.NodeStateD.csC-CD (nD s) ≡ SN.NodeStateD.csC-CD (nD deSucc))
                 × (SN.NodeStateD.bfC-CD (nD s) ≡ SN.NodeStateD.bfC-CD (nD deSucc)))
                ⊎ ((SN.decConsD linkCD (SN.NodeStateD.cons-CD (nD s))
                      ─[ ev (evl (evLabel X e a)) ]─►
                      SN.decConsD linkCD (SN.NodeStateD.cons-CD (nD deSucc)))
                   -- (T8c-iii, round 3) … and the hop's own PHASE PAIR beside the step.
                   -- The api carry needs `ConsAdv` at the STATE's pair to feed
                   -- `LiveDrvCSD.cliDrvAdj-of`, and recovering it from the step instead
                   -- would need `decConsD` injectivity; `NodeDApiEvo`'s third field IS
                   -- this adjacency, so it travels rather than being re-derived
                   × ConsAdv (cph (SN.NodeStateD.cons-CD (nD s))) (cph (SN.NodeStateD.cons-CD (nD deSucc)))
                   × CscCliFired linkCD hi (SN.NodeStateD.csC-CD (nD s))
                       (SN.NodeStateD.csC-CD (nD deSucc)) e a
                   -- *** (T11e) … and the TWO facts node D's BlockFetch api class
                   -- needs, both riding this arm because both are about the leg that
                   -- FIRED: *** §2b⁷'s request landing, and the `cp3` ANCHOR's source
                   -- at COARSE positions (`NodeDApiEvo`'s sixth field, `cong`-ed here
                   -- so the consumer reads a position and not a `bcBlk1`)
                   × CliReqLand linkCD hi (SN.NodeStateD.bfC-CD (nD s))
                       (SN.NodeStateD.bfC-CD (nD deSucc)) e a
                   × (cph (SN.NodeStateD.cons-CD (nD s)) ≡ cp3
                      → Σ[ b″ ∈ Block₃ ]
                          (coarsenBFc (SN.NodeStateD.bfC-CD (nD s)) ≡ NS.bcAblk b″)))
    -- *** (T8c-iii) EACH RELAY's OWN LEG ACROSS THIS STEP — the node-D pair's twin at
    -- the other peer, and it exists for exactly the same reason. ***  The api carry's
    -- relay branch needs "the DOWN-hop CS SERVER is fixed across an UP-link relay hop",
    -- and nothing already in this record says it: `deCsDrv*`'s fixity half is that very
    -- pair but its landing half is two conditionals on the SUCCESSOR phase, both vacuous
    -- at a consume hop, so the datum is absent exactly where it is needed — and the
    -- offending combination (relay phase fixed, dn CS server moved by `saReq`) is
    -- IMPOSSIBLE in every arm yet PERMITTED by a record that reports the two separately.
    -- That is §8 (i-b)'s defect one peer over, so the cure is the same: report the TRUE
    -- dichotomy in ONE field.
    --
    -- Either the relay's phase AND its down CS server are both FIXED (every arm in which
    -- the relay node did not fire), or the relay fired and then — `LiveLegApiCone`'s
    -- classifier having correlated the hop with the label — the fired label is on the
    -- leg's UP link (so the DOWN bundle, hence the dn CS server, is untouched and its
    -- api row is refutable BY LINK) or the successor is `producing bb qq` with
    -- `qq ≢ pp0`, i.e. OUTSIDE the freshness region, where the guard makes the whole
    -- obligation vacuous.  *** The correlation is produced at the classifier and cannot
    -- be re-made here — see its nineteenth component. ***
    deRelayBD : ((SN.NodeStateB.cp-B (nB s) ≡ SN.NodeStateB.cp-B (nB deSucc))
                 × (SN.NodeStateB.csS-BD (nB s) ≡ SN.NodeStateB.csS-BD (nB deSucc)))
                ⊎ (ApiHasLink linkAB e
                   ⊎ (Σ[ bb ∈ Block₃ ] Σ[ qq ∈ SN.ProdPh ]
                        (SN.NodeStateB.cp-B (nB deSucc) ≡ SN.producing bb qq)
                        × (qq ≡ SN.pp0 → ⊥)))
    deRelayCD : ((SN.NodeStateC.cp-C (nC s) ≡ SN.NodeStateC.cp-C (nC deSucc))
                 × (SN.NodeStateC.csS-CD (nC s) ≡ SN.NodeStateC.csS-CD (nC deSucc)))
                ⊎ (ApiHasLink linkAC e
                   ⊎ (Σ[ bb ∈ Block₃ ] Σ[ qq ∈ SN.ProdPh ]
                        (SN.NodeStateC.cp-C (nC deSucc) ≡ SN.producing bb qq)
                        × (qq ≡ SN.pp0 → ⊥)))
    -- *** (T10) TRAILING, APPENDED for the T4 reason: each leg's UP-hop BF CLIENT
    -- against its relay's own phase — `UpCsDrv`'s BlockFetch twin, and the `cp4`
    -- client region's whole api class.  Stated at the node fields, like `deUpCsDrv*`
    -- and `deCsDrv*`, so the consumer's per-leg selector converts the two forms
    deUpBfBD : UpBfDrv (SN.NodeStateB.bfC-AB (nB s)) (SN.NodeStateB.bfC-AB (nB deSucc))
                       (SN.NodeStateB.cp-B (nB s)) (SN.NodeStateB.cp-B (nB deSucc))
    deUpBfCD : UpBfDrv (SN.NodeStateC.bfC-AC (nC s)) (SN.NodeStateC.bfC-AC (nC deSucc))
                       (SN.NodeStateC.cp-C (nC s)) (SN.NodeStateC.cp-C (nC deSucc))
open DriverExposed⁺ public

-- the ⁺ whole-nodes visible cone: `driverExpose` plus both legs' `VisLeaves⁺`
driverExpose⁺ : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → DriverExposed⁺ s e a M
driverExpose⁺ s apimem nodesStep
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (absNodeA (nA s)) (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s))) nodesStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sA sRest = ⊥-elim (SStep.⦀-noOffer (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s))
        (absNodeB-no-when-A (nB s) apimem (absNodeA-fp (nA s) apimem sA))
        (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
          (absNodeC-no-when-A (nC s) apimem (absNodeA-fp (nA s) apimem sA))
          (absNodeD-no-when-A (nD s) apimem (absNodeA-fp (nA s) apimem sA))) (_ , sRest))
... | PEA.evL _ sA with nodeA-ev-api-evo⁺ (nA s) apimem sA
...   | na′ , Meq , weakRunA , inj₁ (padv , pACeq , (upEvo , upRaw , up6 , up7 , upG , upL , upBd , upKeep) , sACeq , ahlA) , rowAB , rowAC , cssRowAB , cssRowAC =
        record
          { deSucc  = mkSys (med s) na′ (nB s) (nC s) (nD s)
          ; deMed   = refl
          ; deProc  = cong (λ z → z ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) Meq
          ; deRun   = ⦀-wev-L (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
              (noOffer→viewV _ (SStep.⦀-noOffer (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
                 (nodeB-no-when-A (nB s) apimem (absNodeA-fp (nA s) apimem sA))
                 (SStep.⦀-noOffer (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                    (nodeC-no-when-A (nC s) apimem (absNodeA-fp (nA s) apimem sA))
                    (nodeD-no-when-A (nD s) apimem (absNodeA-fp (nA s) apimem sA)))))
              weakRunA
          ; deLdBD  = ldProd padv refl refl refl refl refl refl
          ; deLdCD  = ldFix (sym pACeq) refl refl refl refl refl refl
          ; deSrvBD = (upEvo , inj₁ refl)
          ; deSrvCD = (inj₁ sACeq , inj₁ refl)
          ; deVlBD  = visLeaves⁺ up6 (inj₁ refl) up7
              (λ b rat hH hF → ⊥-elim (relayHas-fwd-⊥ _ hH hF))
              upG (λ ¬h h → ⊥-elim (¬h h))
              -- (T10) the FIRING leg's `pp6` landing is `SrvUpFacts`' seventh
              -- component, already applied at the driver's own step
              (λ h6 _ → upBd h6)
              -- (T10) … and the keep is `SrvUpFacts`' eighth component
              upKeep
          ; deVlCD  = visLeaves-fix legCD s (mkSys (med s) na′ (nB s) (nC s) (nD s)) sACeq refl (sym pACeq) refl
          ; deLvBD  = lvStep upRaw (inj₁ refl) (λ _ h → h) (λ _ → refl)
          ; deLvCD  = lvStep (inj₁ sACeq) (inj₁ refl) (λ _ h → h) (λ _ → refl)
          -- (P7) the FIRING leg's landing is the kept `SrvUpFacts` component; the
          -- CO-leg's is refuted by the fired-link pin (`linkAB ≢ linkAC`)
          ; dePlBD  = upL
          ; dePlCD  = λ b″ sd → ⊥-elim (linkAB≢linkAC
              (apiLink-inj ahlA (proj₁ (proj₂ (sbbAt⇒pin _ _ sd)))))
          -- (P8) node A is producer-role: no delivery lands on either leg
          ; deRlBD  = recvLands-A (nA s) legBD (mkSys (med s) na′ (nB s) (nC s) (nD s)) apimem sA
          ; deRlCD  = recvLands-A (nA s) legCD (mkSys (med s) na′ (nB s) (nC s) (nD s)) apimem sA
          -- (P5) node A fired: node B is a LITERAL in this successor
          ; deFrzB  = λ _ h → h
          -- (grant #8) A fired, so both UP SERVERS' rows are A's own and both UP
          -- CLIENTS (nodes B and C) are literal
          ; deRowsAB = (rowAB , cliApiRow-fix linkAB hi (SN.NodeStateB.bfC-AB (nB s)) _ _)
          ; deRowsAC = (rowAC , cliApiRow-fix linkAC hi (SN.NodeStateC.bfC-AC (nC s)) _ _)
          -- (task 5) … and all four DOWN-hop peers (nodes B, C and D) are literal
          ; deRowsBD = (srvApiRow-fix linkBD hi (SN.NodeStateB.bfS-BD (nB s)) _ _
                       , cliApiRow-fix linkBD hi (SN.NodeStateD.bfC-BD (nD s)) _ _)
          ; deRowsCD = (srvApiRow-fix linkCD hi (SN.NodeStateC.bfS-CD (nC s)) _ _
                       , cliApiRow-fix linkCD hi (SN.NodeStateD.bfC-CD (nD s)) _ _)
          -- (T1) node A fired: both relays' records are LITERAL, so neither leg's
          -- driver phase nor its down server moved
          ; deDnDrvBD = inj₁ (refl , refl)
          ; deDnDrvCD = inj₁ (refl , refl)
          -- (T4) leg BD's CS peers are node B's; this arm leaves them literal
          ; deCSRowsBD = (cscApiRow-fix linkAB hi (SN.NodeStateB.csC-AB (nB s)) _ _
                        , cssApiRow-fix linkBD hi (SN.NodeStateB.csS-BD (nB s)) _ _)
          ; deCSRowsCD = (cscApiRow-fix linkAC hi (SN.NodeStateC.csC-AC (nC s)) _ _
                        , cssApiRow-fix linkCD hi (SN.NodeStateC.csS-CD (nC s)) _ _)
          -- (T5) neither relay's driver phase moved, so both `pp1` landings ride as
          -- the fixity pair
          ; deCsDrvBD = inj₁ (refl , refl)
          ; deCsDrvCD = inj₁ (refl , refl)
          -- (T6c, grant #12) node A's two UP-hop CS servers and node D's two DOWN-hop CS clients
          ; deCSUpSrvBD = cssRowAB
          ; deCSUpSrvCD = cssRowAC
          ; deCSDnCliBD = cscApiRow-fix linkBD hi (SN.NodeStateD.csC-BD (nD s)) _ _
          ; deCSDnCliCD = cscApiRow-fix linkCD hi (SN.NodeStateD.csC-CD (nD s)) _ _
          -- (T7) node A fired: both relays' records are LITERAL, so neither leg's
          -- driver phase nor its UP-hop CS client moved
          ; deUpCsDrvBD = inj₁ (refl , refl)
          ; deUpCsDrvCD = inj₁ (refl , refl)
          -- (T8c-0) the two threaded landing facts
          ; deRelayAdvBD = inj₁ refl
          ; deRelayAdvCD = inj₁ refl
            -- (T8c-iii) node D did not fire here, so its WHOLE record is literal in
            -- this successor — driver slot and CS client alike
          ; deNodeDBD = inj₁ (refl , refl , refl)
          ; deNodeDCD = inj₁ (refl , refl , refl)
            -- (T8c-iii) … and likewise for whichever relay did not fire; the arm that
            -- DID fire overrides its own line below
          ; deRelayBD = inj₁ (refl , refl)
          ; deRelayCD = inj₁ (refl , refl)
          -- (T10) neither relay fired here, so both up BF clients and both relay
          -- phases are LITERAL in this successor
          ; deUpBfBD = upBfDrv-fix _ _
          ; deUpBfCD = upBfDrv-fix _ _
          }
...   | na′ , Meq , weakRunA , inj₂ (padv , pABeq , (upEvo , upRaw , up6 , up7 , upG , upL , upBd , upKeep) , sABeq , ahlA) , rowAB , rowAC , cssRowAB , cssRowAC =
        record
          { deSucc  = mkSys (med s) na′ (nB s) (nC s) (nD s)
          ; deMed   = refl
          ; deProc  = cong (λ z → z ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) Meq
          ; deRun   = ⦀-wev-L (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
              (noOffer→viewV _ (SStep.⦀-noOffer (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
                 (nodeB-no-when-A (nB s) apimem (absNodeA-fp (nA s) apimem sA))
                 (SStep.⦀-noOffer (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                    (nodeC-no-when-A (nC s) apimem (absNodeA-fp (nA s) apimem sA))
                    (nodeD-no-when-A (nD s) apimem (absNodeA-fp (nA s) apimem sA)))))
              weakRunA
          ; deLdBD  = ldFix (sym pABeq) refl refl refl refl refl refl
          ; deLdCD  = ldProd padv refl refl refl refl refl refl
          ; deSrvBD = (inj₁ sABeq , inj₁ refl)
          ; deSrvCD = (upEvo , inj₁ refl)
          ; deVlBD  = visLeaves-fix legBD s (mkSys (med s) na′ (nB s) (nC s) (nD s)) sABeq refl (sym pABeq) refl
          ; deVlCD  = visLeaves⁺ up6 (inj₁ refl) up7
              (λ b rat hH hF → ⊥-elim (relayHas-fwd-⊥ _ hH hF))
              upG (λ ¬h h → ⊥-elim (¬h h))
              -- (T10) … the same at leg CD
              (λ h6 _ → upBd h6)
              -- (T10) … and the keep is `SrvUpFacts`' eighth component
              upKeep
          ; deLvBD  = lvStep (inj₁ sABeq) (inj₁ refl) (λ _ h → h) (λ _ → refl)
          ; deLvCD  = lvStep upRaw (inj₁ refl) (λ _ h → h) (λ _ → refl)
          -- (P7) the mirror: BD is now the co-leg, CD the firing one
          ; dePlBD  = λ b″ sd → ⊥-elim (linkAB≢linkAC
              (sym (apiLink-inj ahlA (proj₁ (proj₂ (sbbAt⇒pin _ _ sd))))))
          ; dePlCD  = upL
          -- (P8) node A is producer-role: no delivery lands on either leg
          ; deRlBD  = recvLands-A (nA s) legBD (mkSys (med s) na′ (nB s) (nC s) (nD s)) apimem sA
          ; deRlCD  = recvLands-A (nA s) legCD (mkSys (med s) na′ (nB s) (nC s) (nD s)) apimem sA
          -- (P5) node A fired: node B is a LITERAL in this successor
          ; deFrzB  = λ _ h → h
          -- (grant #8) A fired, so both UP SERVERS' rows are A's own and both UP
          -- CLIENTS (nodes B and C) are literal
          ; deRowsAB = (rowAB , cliApiRow-fix linkAB hi (SN.NodeStateB.bfC-AB (nB s)) _ _)
          ; deRowsAC = (rowAC , cliApiRow-fix linkAC hi (SN.NodeStateC.bfC-AC (nC s)) _ _)
          -- (task 5) … and all four DOWN-hop peers (nodes B, C and D) are literal
          ; deRowsBD = (srvApiRow-fix linkBD hi (SN.NodeStateB.bfS-BD (nB s)) _ _
                       , cliApiRow-fix linkBD hi (SN.NodeStateD.bfC-BD (nD s)) _ _)
          ; deRowsCD = (srvApiRow-fix linkCD hi (SN.NodeStateC.bfS-CD (nC s)) _ _
                       , cliApiRow-fix linkCD hi (SN.NodeStateD.bfC-CD (nD s)) _ _)
          -- (T1) the mirror: node A fired, both relays literal
          ; deDnDrvBD = inj₁ (refl , refl)
          ; deDnDrvCD = inj₁ (refl , refl)
          -- (T4) leg BD's CS peers are node B's; this arm leaves them literal
          ; deCSRowsBD = (cscApiRow-fix linkAB hi (SN.NodeStateB.csC-AB (nB s)) _ _
                        , cssApiRow-fix linkBD hi (SN.NodeStateB.csS-BD (nB s)) _ _)
          ; deCSRowsCD = (cscApiRow-fix linkAC hi (SN.NodeStateC.csC-AC (nC s)) _ _
                        , cssApiRow-fix linkCD hi (SN.NodeStateC.csS-CD (nC s)) _ _)
          -- (T5) neither relay's driver phase moved, so both `pp1` landings ride as
          -- the fixity pair
          ; deCsDrvBD = inj₁ (refl , refl)
          ; deCsDrvCD = inj₁ (refl , refl)
          -- (T6c, grant #12) node A's two UP-hop CS servers and node D's two DOWN-hop CS clients
          ; deCSUpSrvBD = cssRowAB
          ; deCSUpSrvCD = cssRowAC
          ; deCSDnCliBD = cscApiRow-fix linkBD hi (SN.NodeStateD.csC-BD (nD s)) _ _
          ; deCSDnCliCD = cscApiRow-fix linkCD hi (SN.NodeStateD.csC-CD (nD s)) _ _
          -- (T7) node A fired: both relays' records are LITERAL, so neither leg's
          -- driver phase nor its UP-hop CS client moved
          ; deUpCsDrvBD = inj₁ (refl , refl)
          ; deUpCsDrvCD = inj₁ (refl , refl)
          -- (T8c-0) the two threaded landing facts
          ; deRelayAdvBD = inj₁ refl
          ; deRelayAdvCD = inj₁ refl
            -- (T8c-iii) node D did not fire here, so its WHOLE record is literal in
            -- this successor — driver slot and CS client alike
          ; deNodeDBD = inj₁ (refl , refl , refl)
          ; deNodeDCD = inj₁ (refl , refl , refl)
            -- (T8c-iii) … and likewise for whichever relay did not fire; the arm that
            -- DID fire overrides its own line below
          ; deRelayBD = inj₁ (refl , refl)
          ; deRelayCD = inj₁ (refl , refl)
          -- (T10) neither relay fired here, so both up BF clients and both relay
          -- phases are LITERAL in this successor
          ; deUpBfBD = upBfDrv-fix _ _
          ; deUpBfCD = upBfDrv-fix _ _
          }
driverExpose⁺ s apimem nodesStep | PEA.evR _ sRest
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s)) sRest
... | PEA.evSync () _ _
... | PEA.evBoth _ sB sCD = ⊥-elim (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
        (absNodeC-no-when-B (nC s) apimem (absNodeB-fp (nB s) apimem sB))
        (absNodeD-no-when-B (nD s) apimem (absNodeB-fp (nB s) apimem sB)) (_ , sCD))
... | PEA.evL _ sB with nodeB-ev-api-evo⁺ (nB s) apimem sB
-- (T7) four more binders: `NodeBApiEvo` grew the `cp5` chain's landing and its three
-- carrying hops.  This reader ended on a NON-wildcard, so it is re-cut rather than
-- absorbing them — the banked Σ-append trap, fifth sighting
...   | nb′ , Meq , weakRunB , rk , cliE , wUp , (dnEvo , dnRaw , dn6 , dn9 , dnG) , rvalB , blkRB , frzB , cliRowAB , srvRowBD , dnReqB , dnSbB , cscRowAB , cssRowBD , dnCsB , dnCsAwB
      , upCsB , upCs3B , upCs4B , upCs5B , raB , lnkB , upBfB
      -- (T11b) one more binder: `NodeBApiEvo` grew the `pp3` LANDING as its last
      -- component and this reader ended on a NON-wildcard
      -- (T11h) one more binder: `NodeBApiEvo` grew `DnSrvPre` as its last component
      , dnCsRfwB , dnPreB =
        record
          { deSucc  = mkSys (med s) (nA s) nb′ (nC s) (nD s)
          ; deMed   = refl
          ; deProc  = cong (λ z → absNodeA (nA s) ⦀ (z ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) Meq
          ; deRun   = ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
              (noOffer→viewV _ (nodeA-no-when-B (nA s) apimem (absNodeB-fp (nB s) apimem sB)))
              (⦀-wev-L (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
                 (noOffer→viewV _ (SStep.⦀-noOffer (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                    (nodeC-no-when-B (nC s) apimem (absNodeB-fp (nB s) apimem sB))
                    (nodeD-no-when-B (nD s) apimem (absNodeB-fp (nB s) apimem sB))))
                 weakRunB)
          ; deLdBD  = ldRelay rk refl refl refl refl refl cliE wUp blkRB
          ; deLdCD  = ldFix refl refl refl refl refl refl refl
          ; deSrvBD = (inj₁ refl , dnEvo)
          ; deSrvCD = (inj₁ refl , inj₁ refl)
          ; deVlBD  = visLeaves⁺ (inj₁ refl) dn6
              (λ hn hs → ⊥-elim (prodSent-notSent-⊥ _ hs hn))
              (λ b rat hH hF → dn9 hH hF b rat)
              (λ ¬h h → ⊥-elim (¬h h)) dnG
              -- (T10) the RELAY fired, so node A's record is LITERAL in the
              -- successor and its producer phase is the same term: the "moved"
              -- antecedent is contradictory
              (λ h6 ¬h6 → ⊥-elim (¬h6 h6))
              -- (T10) node A's record is LITERAL in the successor, so its up server
              -- is the same term and the keep is the identity
              (λ _ hb → hb)
          ; deVlCD  = visLeaves-fix legCD s (mkSys (med s) (nA s) nb′ (nC s) (nD s)) refl refl refl refl
          ; deLvBD  = lvStep (inj₁ refl) dnRaw rvalB (λ _ → refl)
          ; deLvCD  = lvStep (inj₁ refl) (inj₁ refl) (λ _ h → h) (λ _ → refl)
          -- (P7) node B fires on neither up key
          ; dePlBD  = prodLands-B (nB s) legBD apimem sB
          ; dePlCD  = prodLands-B (nB s) legCD apimem sB
          -- (P8) and on neither delivery key
          ; deRlBD  = recvLands-B (nB s) legBD (mkSys (med s) (nA s) nb′ (nC s) (nD s)) apimem sB
          ; deRlCD  = recvLands-B (nB s) legCD (mkSys (med s) (nA s) nb′ (nC s) (nD s)) apimem sB
          -- (P5) node B fired: THE one arm that needs the node peel's own answer
          ; deFrzB  = frzB
          -- (grant #8) B fired: leg BD's UP CLIENT is B's own (its row), both UP
          -- SERVERS are node A's and literal, and leg CD's up client is node C's
          ; deRowsAB = (srvApiRow-fix linkAB hi (SN.NodeStateA.bfS-AB (nA s)) _ _ , cliRowAB)
          ; deRowsAC = (srvApiRow-fix linkAC hi (SN.NodeStateA.bfS-AC (nA s)) _ _
                       , cliApiRow-fix linkAC hi (SN.NodeStateC.bfC-AC (nC s)) _ _)
          -- (task 5) B fired: leg BD's DOWN SERVER is B's own (its row); its down
          -- client is node D's and literal, and leg CD's down hop is nodes C/D — both
          -- literal
          ; deRowsBD = (srvRowBD , cliApiRow-fix linkBD hi (SN.NodeStateD.bfC-BD (nD s)) _ _)
          ; deRowsCD = (srvApiRow-fix linkCD hi (SN.NodeStateC.bfS-CD (nC s)) _ _
                       , cliApiRow-fix linkCD hi (SN.NodeStateD.bfC-CD (nD s)) _ _)
          -- (T1) B fired: leg BD's landing is node B's own peel; leg CD's relay
          -- (node C) is a LITERAL
          ; deDnDrvBD = inj₂ (dnReqB , dnSbB , dnPreB)
          ; deDnDrvCD = inj₁ (refl , refl)
          -- (T4) B fired: leg BD's CS rows are node B's own peel's; leg CD's
          -- relay (node C) is a LITERAL
          ; deCSRowsBD = (cscRowAB , cssRowBD)
          ; deCSRowsCD = (cscApiRow-fix linkAC hi (SN.NodeStateC.csC-AC (nC s)) _ _
                        , cssApiRow-fix linkCD hi (SN.NodeStateC.csS-CD (nC s)) _ _)
          -- (T5)/(T6d) B fired: leg BD's `pp1` and `pp2` landings are node B's own
          -- peel's; node C is a LITERAL, so leg CD rides the fixity pair
          -- (T11c) … and the relay's own ADVANCE as the landing arm's fourth member:
          -- `raB` is the classifier's eighteenth component, already bound above at the
          -- same node fields (the S8 (i-b) merge)
          ; deCsDrvBD = inj₂ (dnCsB , dnCsAwB , dnCsRfwB , raB)
          ; deCsDrvCD = inj₁ (refl , refl)
          -- (T6c, grant #12) node A's two UP-hop CS servers and node D's two DOWN-hop CS clients
          ; deCSUpSrvBD = cssApiRow-fix linkAB hi (SN.NodeStateA.csS-AB (nA s)) _ _
          ; deCSUpSrvCD = cssApiRow-fix linkAC hi (SN.NodeStateA.csS-AC (nA s)) _ _
          ; deCSDnCliBD = cscApiRow-fix linkBD hi (SN.NodeStateD.csC-BD (nD s)) _ _
          ; deCSDnCliCD = cscApiRow-fix linkCD hi (SN.NodeStateD.csC-CD (nD s)) _ _
          -- (T7) B fired: leg BD's `cp5` chain is node B's own peel's four facts; node
          -- C is a LITERAL, so leg CD rides the fixity pair
          ; deUpCsDrvBD = inj₂ (upCsB , upCs3B , upCs4B , upCs5B)
          ; deUpCsDrvCD = inj₁ (refl , refl)
          -- (T8c-0) the two threaded landing facts
          ; deRelayAdvBD = inj₂ raB
          ; deRelayAdvCD = inj₁ refl
            -- (T8c-iii) node D did not fire here, so its WHOLE record is literal in
            -- this successor — driver slot and CS client alike
          ; deNodeDBD = inj₁ (refl , refl , refl)
          ; deNodeDCD = inj₁ (refl , refl , refl)
            -- (T8c-iii) … and likewise for whichever relay did not fire; the arm that
            -- DID fire overrides its own line below
          ; deRelayBD = inj₂ lnkB
          -- (T10) node B fired: its own arm carries, node C's record is literal
          ; deUpBfBD = upBfB
          ; deUpBfCD = upBfDrv-fix _ _
          ; deRelayCD = inj₁ (refl , refl)
          }
driverExpose⁺ s apimem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absNodeC (nC s)) (absNodeD (nD s)) sCD
... | PEA.evSync () _ _
... | PEA.evBoth _ sC sD = ⊥-elim (absNodeD-no-when-C (nD s) apimem (absNodeC-fp (nC s) apimem sC) (_ , sD))
... | PEA.evL _ sC with nodeC-ev-api-evo⁺ (nC s) apimem sC
-- (T7) … and node C's mirror, re-cut for the same reason
...   | nc′ , Meq , weakRunC , rk , cliE , wUp , (dnEvo , dnRaw , dn6 , dn9 , dnG) , rvalC , blkRC , cliRowAC , srvRowCD , dnReqC , dnSbC , cscRowAC , cssRowCD , dnCsC , dnCsAwC
      , upCsC , upCs3C , upCs4C , upCs5C , raC , lnkC , upBfC
      -- (T11b) node C's mirror, re-cut for the same reason
      -- (T11h) one more binder: `NodeCApiEvo` grew `DnSrvPre` as its last component
      , dnCsRfwC , dnPreC =
        record
          { deSucc  = mkSys (med s) (nA s) (nB s) nc′ (nD s)
          ; deMed   = refl
          ; deProc  = cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (z ⦀ absNodeD (nD s)))) Meq
          ; deRun   = ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
              (noOffer→viewV _ (nodeA-no-when-C (nA s) apimem (absNodeC-fp (nC s) apimem sC)))
              (⦀-wev-R (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
                 (noOffer→viewV _ (nodeB-no-when-C (nB s) apimem (absNodeC-fp (nC s) apimem sC)))
                 (⦀-wev-L (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                    (noOffer→viewV _ (nodeD-no-when-C (nD s) apimem (absNodeC-fp (nC s) apimem sC)))
                    weakRunC))
          ; deLdBD  = ldFix refl refl refl refl refl refl refl
          ; deLdCD  = ldRelay rk refl refl refl refl refl cliE wUp blkRC
          ; deSrvBD = (inj₁ refl , inj₁ refl)
          ; deSrvCD = (inj₁ refl , dnEvo)
          ; deVlBD  = visLeaves-fix legBD s (mkSys (med s) (nA s) (nB s) nc′ (nD s)) refl refl refl refl
          ; deVlCD  = visLeaves⁺ (inj₁ refl) dn6
              (λ hn hs → ⊥-elim (prodSent-notSent-⊥ _ hs hn))
              (λ b rat hH hF → dn9 hH hF b rat)
              (λ ¬h h → ⊥-elim (¬h h)) dnG
              -- (T10) the RELAY fired, so node A's record is LITERAL in the
              -- successor and its producer phase is the same term: the "moved"
              -- antecedent is contradictory
              (λ h6 ¬h6 → ⊥-elim (¬h6 h6))
              -- (T10) node A's record is LITERAL in the successor, so its up server
              -- is the same term and the keep is the identity
              (λ _ hb → hb)
          ; deLvBD  = lvStep (inj₁ refl) (inj₁ refl) (λ _ h → h) (λ _ → refl)
          ; deLvCD  = lvStep (inj₁ refl) dnRaw rvalC (λ _ → refl)
          -- (P7) node C fires on neither up key
          ; dePlBD  = prodLands-C (nC s) legBD apimem sC
          ; dePlCD  = prodLands-C (nC s) legCD apimem sC
          -- (P8) and on neither delivery key
          ; deRlBD  = recvLands-C (nC s) legBD (mkSys (med s) (nA s) (nB s) nc′ (nD s)) apimem sC
          ; deRlCD  = recvLands-C (nC s) legCD (mkSys (med s) (nA s) (nB s) nc′ (nD s)) apimem sC
          -- (P5) node C fired: node B is a LITERAL in this successor
          ; deFrzB  = λ _ h → h
          -- (grant #8) C fired: leg CD's UP CLIENT is C's own (its row), both UP
          -- SERVERS are node A's and literal, and leg BD's up client is node B's
          ; deRowsAB = (srvApiRow-fix linkAB hi (SN.NodeStateA.bfS-AB (nA s)) _ _
                       , cliApiRow-fix linkAB hi (SN.NodeStateB.bfC-AB (nB s)) _ _)
          ; deRowsAC = (srvApiRow-fix linkAC hi (SN.NodeStateA.bfS-AC (nA s)) _ _ , cliRowAC)
          -- (task 5) C fired: leg CD's DOWN SERVER is C's own (its row); leg BD's down
          -- hop is nodes B/D and node D is literal on both legs
          ; deRowsBD = (srvApiRow-fix linkBD hi (SN.NodeStateB.bfS-BD (nB s)) _ _
                       , cliApiRow-fix linkBD hi (SN.NodeStateD.bfC-BD (nD s)) _ _)
          ; deRowsCD = (srvRowCD , cliApiRow-fix linkCD hi (SN.NodeStateD.bfC-CD (nD s)) _ _)
          -- (T1) C fired: the mirror
          ; deDnDrvBD = inj₁ (refl , refl)
          ; deDnDrvCD = inj₂ (dnReqC , dnSbC , dnPreC)
          -- (T4) C fired: the mirror
          -- (T4) leg BD's CS peers are node B's; this arm leaves them literal
          ; deCSRowsBD = (cscApiRow-fix linkAB hi (SN.NodeStateB.csC-AB (nB s)) _ _
                        , cssApiRow-fix linkBD hi (SN.NodeStateB.csS-BD (nB s)) _ _)
          ; deCSRowsCD = (cscRowAC , cssRowCD)
          -- (T5)/(T6d) C fired: the mirror, both landings
          ; deCsDrvBD = inj₁ (refl , refl)
          -- (T11c) … node C's mirror, off `raC`
          ; deCsDrvCD = inj₂ (dnCsC , dnCsAwC , dnCsRfwC , raC)
          -- (T6c, grant #12) node A's two UP-hop CS servers and node D's two DOWN-hop CS clients
          ; deCSUpSrvBD = cssApiRow-fix linkAB hi (SN.NodeStateA.csS-AB (nA s)) _ _
          ; deCSUpSrvCD = cssApiRow-fix linkAC hi (SN.NodeStateA.csS-AC (nA s)) _ _
          ; deCSDnCliBD = cscApiRow-fix linkBD hi (SN.NodeStateD.csC-BD (nD s)) _ _
          ; deCSDnCliCD = cscApiRow-fix linkCD hi (SN.NodeStateD.csC-CD (nD s)) _ _
          -- (T7) C fired: the mirror of node B's arm
          ; deUpCsDrvBD = inj₁ (refl , refl)
          ; deUpCsDrvCD = inj₂ (upCsC , upCs3C , upCs4C , upCs5C)
          -- (T8c-0) the two threaded landing facts
          ; deRelayAdvBD = inj₁ refl
          ; deRelayAdvCD = inj₂ raC
            -- (T8c-iii) node D did not fire here, so its WHOLE record is literal in
            -- this successor — driver slot and CS client alike
          ; deNodeDBD = inj₁ (refl , refl , refl)
          ; deNodeDCD = inj₁ (refl , refl , refl)
            -- (T8c-iii) … and likewise for whichever relay did not fire; the arm that
            -- DID fire overrides its own line below
          ; deRelayBD = inj₁ (refl , refl)
          ; deRelayCD = inj₂ lnkC
          -- (T10) node C fired: its own arm carries, node B's record is literal
          ; deUpBfBD = upBfDrv-fix _ _
          ; deUpBfCD = upBfC
          }
driverExpose⁺ s apimem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD | PEA.evR _ sD
    with nodeD-ev-api-evo⁺ (nD s) apimem sD
... | ndaBD nd′ Meq weakRunD cadv cCDeq bfcCDeq lblD dnEvo wDn cfixD drvD cliRowBD cliRowCD cscRowBD cscRowCD cscFire cscFixCo reqLandD =
        record
          { deSucc  = mkSys (med s) (nA s) (nB s) (nC s) nd′
          ; deMed   = refl
          ; deProc  = cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ z))) Meq
          ; deRun   = ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
              (noOffer→viewV _ (nodeA-no-when-D (nA s) apimem (absNodeD-fp (nD s) apimem sD)))
              (⦀-wev-R (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
                 (noOffer→viewV _ (nodeB-no-when-D (nB s) apimem (absNodeD-fp (nD s) apimem sD)))
                 (⦀-wev-R (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                    (noOffer→viewV _ (nodeC-no-when-D (nC s) apimem (absNodeD-fp (nD s) apimem sD)))
                    weakRunD))
          ; deLdBD  = ldCons cadv lblD refl refl refl refl refl dnEvo wDn
          ; deLdCD  = ldFix refl refl (cong cph (sym cCDeq)) refl refl refl (sym bfcCDeq)
          ; deSrvBD = (inj₁ refl , inj₁ refl)
          ; deSrvCD = (inj₁ refl , inj₁ refl)
          ; deVlBD  = visLeaves-fix legBD s (mkSys (med s) (nA s) (nB s) (nC s) nd′) refl refl refl refl
          ; deVlCD  = visLeaves-fix legCD s (mkSys (med s) (nA s) (nB s) (nC s) nd′) refl refl refl refl
          ; deLvBD  = lvStep (inj₁ refl) (inj₁ refl) (λ _ h → h) cfixD
          ; deLvCD  = lvStep (inj₁ refl) (inj₁ refl) (λ _ h → h) (λ _ → cong cblk cCDeq)
          -- (P7) node D fires on neither up key
          ; dePlBD  = prodLands-D (nD s) legBD apimem sD
          ; dePlCD  = prodLands-D (nD s) legCD apimem sD
          -- (P8) THE FIRING LEG: the granted driver step re-opens the `cp3` gate,
          -- `cadv` forces `cp4`, and the anchor's block IS the label's
          ; deRlBD  = λ b rb →
              let gate = decConsD-rbb-cp3 linkBD (SN.NodeStateD.cons-BD (nD s)) drvD rb
                  anc  = lblD gate
              in  consAdv-cp3-cp4 cadv gate
                , trans (proj₁ (proj₂ (proj₂ anc)))
                        (rbbAt-inj (rpin⇒rbbAt linkBD hi (proj₁ anc) _ _
                                      (proj₁ (proj₂ anc))) rb)
          -- (P8) THE CO-LEG: the fired link is `linkBD`, not `linkCD`
          ; deRlCD  = λ b rb → ⊥-elim (linkBD≢linkCD
              (apiLink-inj (decConsD-ev-link linkBD (SN.NodeStateD.cons-BD (nD s)) drvD)
                           (proj₁ (proj₂ (rbbAt⇒pin _ _ rb)))))
          -- (P5) node D fired: node B is a LITERAL in this successor
          ; deFrzB  = λ _ h → h
          -- (grant #8) D fired: ALL FOUR up-hop peers (nodes A, B and C) are literal
          ; deRowsAB = (srvApiRow-fix linkAB hi (SN.NodeStateA.bfS-AB (nA s)) _ _
                       , cliApiRow-fix linkAB hi (SN.NodeStateB.bfC-AB (nB s)) _ _)
          ; deRowsAC = (srvApiRow-fix linkAC hi (SN.NodeStateA.bfS-AC (nA s)) _ _
                       , cliApiRow-fix linkAC hi (SN.NodeStateC.bfC-AC (nC s)) _ _)
          -- (task 5) … and so are BOTH DOWN SERVERS (the relays'); the two DOWN
          -- CLIENTS are node D's own, and §8's peel reports BOTH rows on either arm
          ; deRowsBD = (srvApiRow-fix linkBD hi (SN.NodeStateB.bfS-BD (nB s)) _ _ , cliRowBD)
          ; deRowsCD = (srvApiRow-fix linkCD hi (SN.NodeStateC.bfS-CD (nC s)) _ _ , cliRowCD)
          -- (T1) node D fired: both relays' records are LITERAL
          ; deDnDrvBD = inj₁ (refl , refl)
          ; deDnDrvCD = inj₁ (refl , refl)
          -- (T4) leg BD's CS peers are node B's; this arm leaves them literal
          ; deCSRowsBD = (cscApiRow-fix linkAB hi (SN.NodeStateB.csC-AB (nB s)) _ _
                        , cssApiRow-fix linkBD hi (SN.NodeStateB.csS-BD (nB s)) _ _)
          ; deCSRowsCD = (cscApiRow-fix linkAC hi (SN.NodeStateC.csC-AC (nC s)) _ _
                        , cssApiRow-fix linkCD hi (SN.NodeStateC.csS-CD (nC s)) _ _)
          -- (T5) neither relay's driver phase moved, so both `pp1` landings ride as
          -- the fixity pair
          ; deCsDrvBD = inj₁ (refl , refl)
          ; deCsDrvCD = inj₁ (refl , refl)
          -- (T6c, grant #12) node A's two UP-hop CS servers and node D's two DOWN-hop CS clients
          ; deCSUpSrvBD = cssApiRow-fix linkAB hi (SN.NodeStateA.csS-AB (nA s)) _ _
          ; deCSUpSrvCD = cssApiRow-fix linkAC hi (SN.NodeStateA.csS-AC (nA s)) _ _
          ; deCSDnCliBD = cscRowBD
          ; deCSDnCliCD = cscRowCD
          -- (T7) node D fired: both relays' records are LITERAL, node A's arm's reason
          ; deUpCsDrvBD = inj₁ (refl , refl)
          ; deUpCsDrvCD = inj₁ (refl , refl)
          -- (T8c-0) the two threaded landing facts
          ; deRelayAdvBD = inj₁ refl
          ; deRelayAdvCD = inj₁ refl
            -- (T8c-iii) leg BD FIRED: its step and the sharpening travel together;
            -- leg CD is untouched, both slots
          ; deNodeDBD = inj₂ (drvD , cadv , cscFire , reqLandD
                             , (λ h → proj₁ (lblD h)
                                     , cong coarsenBFc
                                         (proj₂ (proj₂ (proj₂ (lblD h))))))
          ; deNodeDCD = inj₁ (cong cph (sym cCDeq) , sym cscFixCo , sym bfcCDeq)
            -- (T8c-iii) node D fired, so BOTH relays' records are literal
          ; deRelayBD = inj₁ (refl , refl)
          ; deRelayCD = inj₁ (refl , refl)
          -- (T10) neither relay fired here, so both up BF clients and both relay
          -- phases are LITERAL in this successor
          ; deUpBfBD = upBfDrv-fix _ _
          ; deUpBfCD = upBfDrv-fix _ _
          }
... | ndaCD nd′ Meq weakRunD cadv cBDeq bfcBDeq lblD dnEvo wDn cfixD drvD cliRowBD cliRowCD cscRowBD cscRowCD cscFire cscFixCo reqLandD =
        record
          { deSucc  = mkSys (med s) (nA s) (nB s) (nC s) nd′
          ; deMed   = refl
          ; deProc  = cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ z))) Meq
          ; deRun   = ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
              (noOffer→viewV _ (nodeA-no-when-D (nA s) apimem (absNodeD-fp (nD s) apimem sD)))
              (⦀-wev-R (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
                 (noOffer→viewV _ (nodeB-no-when-D (nB s) apimem (absNodeD-fp (nD s) apimem sD)))
                 (⦀-wev-R (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                    (noOffer→viewV _ (nodeC-no-when-D (nC s) apimem (absNodeD-fp (nD s) apimem sD)))
                    weakRunD))
          ; deLdBD  = ldFix refl refl (cong cph (sym cBDeq)) refl refl refl (sym bfcBDeq)
          ; deLdCD  = ldCons cadv lblD refl refl refl refl refl dnEvo wDn
          ; deSrvBD = (inj₁ refl , inj₁ refl)
          ; deSrvCD = (inj₁ refl , inj₁ refl)
          ; deVlBD  = visLeaves-fix legBD s (mkSys (med s) (nA s) (nB s) (nC s) nd′) refl refl refl refl
          ; deVlCD  = visLeaves-fix legCD s (mkSys (med s) (nA s) (nB s) (nC s) nd′) refl refl refl refl
          ; deLvBD  = lvStep (inj₁ refl) (inj₁ refl) (λ _ h → h) (λ _ → cong cblk cBDeq)
          ; deLvCD  = lvStep (inj₁ refl) (inj₁ refl) (λ _ h → h) cfixD
          -- (P7) node D fires on neither up key
          ; dePlBD  = prodLands-D (nD s) legBD apimem sD
          ; dePlCD  = prodLands-D (nD s) legCD apimem sD
          -- (P8) THE CO-LEG: the fired link is `linkCD`, not `linkBD`
          ; deRlBD  = λ b rb → ⊥-elim (linkBD≢linkCD
              (sym (apiLink-inj (decConsD-ev-link linkCD (SN.NodeStateD.cons-CD (nD s)) drvD)
                                (proj₁ (proj₂ (rbbAt⇒pin _ _ rb))))))
          -- (P8) THE FIRING LEG (the mirror)
          ; deRlCD  = λ b rb →
              let gate = decConsD-rbb-cp3 linkCD (SN.NodeStateD.cons-CD (nD s)) drvD rb
                  anc  = lblD gate
              in  consAdv-cp3-cp4 cadv gate
                , trans (proj₁ (proj₂ (proj₂ anc)))
                        (rbbAt-inj (rpin⇒rbbAt linkCD hi (proj₁ anc) _ _
                                      (proj₁ (proj₂ anc))) rb)
          -- (P5) node D fired: node B is a LITERAL in this successor
          ; deFrzB  = λ _ h → h
          -- (grant #8) D fired: ALL FOUR up-hop peers (nodes A, B and C) are literal
          ; deRowsAB = (srvApiRow-fix linkAB hi (SN.NodeStateA.bfS-AB (nA s)) _ _
                       , cliApiRow-fix linkAB hi (SN.NodeStateB.bfC-AB (nB s)) _ _)
          ; deRowsAC = (srvApiRow-fix linkAC hi (SN.NodeStateA.bfS-AC (nA s)) _ _
                       , cliApiRow-fix linkAC hi (SN.NodeStateC.bfC-AC (nC s)) _ _)
          -- (task 5) … and so are BOTH DOWN SERVERS (the relays'); the two DOWN
          -- CLIENTS are node D's own, and §8's peel reports BOTH rows on either arm
          ; deRowsBD = (srvApiRow-fix linkBD hi (SN.NodeStateB.bfS-BD (nB s)) _ _ , cliRowBD)
          ; deRowsCD = (srvApiRow-fix linkCD hi (SN.NodeStateC.bfS-CD (nC s)) _ _ , cliRowCD)
          -- (T1) node D fired: both relays' records are LITERAL
          ; deDnDrvBD = inj₁ (refl , refl)
          ; deDnDrvCD = inj₁ (refl , refl)
          -- (T4) leg BD's CS peers are node B's; this arm leaves them literal
          ; deCSRowsBD = (cscApiRow-fix linkAB hi (SN.NodeStateB.csC-AB (nB s)) _ _
                        , cssApiRow-fix linkBD hi (SN.NodeStateB.csS-BD (nB s)) _ _)
          ; deCSRowsCD = (cscApiRow-fix linkAC hi (SN.NodeStateC.csC-AC (nC s)) _ _
                        , cssApiRow-fix linkCD hi (SN.NodeStateC.csS-CD (nC s)) _ _)
          -- (T5) neither relay's driver phase moved, so both `pp1` landings ride as
          -- the fixity pair
          ; deCsDrvBD = inj₁ (refl , refl)
          ; deCsDrvCD = inj₁ (refl , refl)
          -- (T6c, grant #12) node A's two UP-hop CS servers and node D's two DOWN-hop CS clients
          ; deCSUpSrvBD = cssApiRow-fix linkAB hi (SN.NodeStateA.csS-AB (nA s)) _ _
          ; deCSUpSrvCD = cssApiRow-fix linkAC hi (SN.NodeStateA.csS-AC (nA s)) _ _
          ; deCSDnCliBD = cscRowBD
          ; deCSDnCliCD = cscRowCD
          -- (T7) node D fired: both relays' records are LITERAL, node A's arm's reason
          ; deUpCsDrvBD = inj₁ (refl , refl)
          ; deUpCsDrvCD = inj₁ (refl , refl)
          -- (T8c-0) the two threaded landing facts
          ; deRelayAdvBD = inj₁ refl
          ; deRelayAdvCD = inj₁ refl
            -- (T8c-iii) the CD mirror
          ; deNodeDBD = inj₁ (cong cph (sym cBDeq) , sym cscFixCo , sym bfcBDeq)
          ; deNodeDCD = inj₂ (drvD , cadv , cscFire , reqLandD
                             , (λ h → proj₁ (lblD h)
                                     , cong coarsenBFc
                                         (proj₂ (proj₂ (proj₂ (lblD h))))))
            -- (T8c-iii) node D fired, so BOTH relays' records are literal
          ; deRelayBD = inj₁ (refl , refl)
          ; deRelayCD = inj₁ (refl , refl)
          -- (T10) neither relay fired here, so both up BF clients and both relay
          -- phases are LITERAL in this successor
          ; deUpBfBD = upBfDrv-fix _ _
          ; deUpBfCD = upBfDrv-fix _ _
          }

------------------------------------------------------------------------
-- §10  ONE LEG'S SLICE OF THE ⁺ CONE (ASSEMBLY slice A1).
--
-- `driverExpose⁺` reports BOTH legs; every consumer works one leg at a time, so
-- this is the leg selector — the ⁺ analogue of `PipeEvStep`'s
-- `pickLeg`/`pickLegSrv`/`pickLegVal` trio, done once for all four families in
-- ONE clause per leg so a single peel is shared and the successor `s′` is THE
-- SAME for the driver step, the server evolutions, the value data and the PROVED
-- `VisLeaves⁺`.  This is what makes the `VisLeaves` premise of `LiveLegStep`'s
-- visible arm DERIVED rather than assumed: a consumer that peels here has all
-- four in hand at one and the same existential successor.
------------------------------------------------------------------------

-- leg `l`'s own slice of the ⁺ visible cone, from a SINGLE peel
driverExpose⁺-at : (l : TwoLegs) (s : SysState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ s′ ∈ SysState ] (med s ≡ med s′) × (M ≡ absNodesOf s′)
      × (nodesOf s ═[ ev (evl (evLabel X e a)) ]═► nodesOf s′)
      × LegDriverStep l s s′ e a
      × (UpSrvEvo l s s′ × DnSrvEvo l s s′)
      × VisLeaves⁺ l s s′ × LegValStep l s s′ e a
driverExpose⁺-at legBD s apimem step =
  let de = driverExpose⁺ s apimem step
  in  deSucc de , deMed de , deProc de , deRun de , deLdBD de , deSrvBD de , deVlBD de , deLvBD de
driverExpose⁺-at legCD s apimem step =
  let de = driverExpose⁺ s apimem step
  in  deSucc de , deMed de , deProc de , deRun de , deLdCD de , deSrvCD de , deVlCD de , deLvCD de

------------------------------------------------------------------------
-- §11  *** (P7) THE PREMISE, AT THE CONE. ***  The per-leg selector for the new
-- landing slot.  It is stated at `deSucc (driverExpose⁺ …)` — the very term
-- `LiveFSim`'s premise names — so the composition downstream is definitional.
------------------------------------------------------------------------

-- leg `l`'s producer landing, out of the SAME single peel `deSucc` reads
driverExpose⁺-prodLands : (l : TwoLegs) (s : SysState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → (apimem : apiES .mem (X , e) a)
  → (step : absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M)
  → LegProdLands l (deSucc (driverExpose⁺ s apimem step)) e a
driverExpose⁺-prodLands legBD s apimem step = dePlBD (driverExpose⁺ s apimem step)
driverExpose⁺-prodLands legCD s apimem step = dePlCD (driverExpose⁺ s apimem step)

-- leg `l`'s consumer landing, out of that same single peel
driverExpose⁺-recvLands : (l : TwoLegs) (s : SysState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → (apimem : apiES .mem (X , e) a)
  → (step : absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M)
  → LegRecvLands l (deSucc (driverExpose⁺ s apimem step)) e a
driverExpose⁺-recvLands legBD s apimem step = deRlBD (driverExpose⁺ s apimem step)
driverExpose⁺-recvLands legCD s apimem step = deRlCD (driverExpose⁺ s apimem step)