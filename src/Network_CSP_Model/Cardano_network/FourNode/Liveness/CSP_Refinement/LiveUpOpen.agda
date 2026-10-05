{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- (T10) THE UP-HOP BLOCKFETCH STABILITY REFUTATIONS — `LiveUpOpen`, the
-- `cp4` arm's whole io/api side, and the module that finally builds
-- `nodes-offer-A`.
--
-- *** WHAT THIS MODULE IS FOR. ***  `LiveRelayOpen` §7's `cp4` entry is the
-- tree's own inventory of the arm, and it names one enabled move the tree could
-- not construct:
--
--     "`bcStream` is the gate verdict's H22 row, whose enabled move is NODE A's
--      `apiBF up hi sendBFBatchDone` syncing with A's up BF server at `bsStream`
--      — i.e. it needs `upSrv ≡ bsStream` AND `prodOf ≡ pp6`, plus a node-A
--      four-node lift.  *** `nodes-offer-A` EXISTS NOWHERE IN THE TREE. ***"
--
-- §2 builds it, §3-§4 build the arm it feeds, and §6 composes the whole leaf:
-- *** a stable configuration cannot have the leg's UP BlockFetch client at
-- `bcStream`, *** given the hop's channel invariant and ONE cross-node fact —
-- "if node A's up BF server is streaming then node A's driver is at `pp6`".
-- That fact is the arm's single remaining obligation and it is a HYPOTHESIS
-- here, so this module is premise-free and closed.
--
-- *** WHY THE CLIENT-ANTECEDENT CHANNEL CLAUSE IS WHAT DRIVES §6. ***  Every
-- clause of `ChanInv` before (T10) is server- or cell-antecedent, so at a
-- streaming client facing a server OUTSIDE `SrvStr` the invariant said nothing
-- at all — and that is precisely the leaf's configuration.  `cvBd` (the (T10)
-- seventh clause) splits it two ways: the server is still streaming, or its
-- `MsgBatchDone` is in the cell unread.  §6 is the dispatch on that split, and
-- every one of its five leaves is an ENABLED MOVE:
--
--   · the `MsgBatchDone` unread in the cell   ⇒ the CLIENT's own wire-read
--     (`ceqBFc06`, rung 1 of §5, on `LiveChanRead.cellFull-up-⊥`'s ladder);
--   · a `MsgBlock` unread in the cell         ⇒ the same, at the block row;
--   · the cell DRAINING                       ⇒ the medium's own τ;
--   · the cell EMPTY, server at `bsWblk b`    ⇒ the SERVER's block wire-send;
--   · the cell EMPTY, server at `bsWbd`       ⇒ its `MsgBatchDone` wire-send
--     (`ceqBFs12`, rung 1 of §5);
--   · the cell EMPTY, server at `bsStream`    ⇒ *** NODE A's api SYNC, §4. ***
--
-- The two io ladders the T9 verification priced as "UP-hop io ladders that do
-- not exist" are RUNG 1 ONLY: `LiveIoIntro`'s `srvInNodes-A-AB`/`-A-AC` (server
-- WRITE) and `LiveChanRead.cellFull-up-⊥` (client READ) are already payload- and
-- target-generic at node A's own up link, so each new position costs one banked
-- `ceq*` instance and nothing else.  That is the measurement this module
-- contributes to the campaign's ladder-density record.
--
-- No postulate, no hole, no `mutual`, no `with` in anything whose type mentions
-- an imported `blkA`-parameterised predicate — every dispatch is on an EXPLICIT
-- argument (the campaign's `blkA`-module rule).
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Bool using ( false )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Unit.Polymorphic using ( ⊤; tt )
import Data.Unit as U
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Maybe using ( just )
open import Relation.Nullary using ( ¬_ )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; subst )

open import Class.DecEq using ( DecEq; _≟_ )
open import Class.DecEq.Instances using ( DecEq-Fin )

open import Process_Trees using ( PTree; ExtI; isStable )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveUpOpen
  (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; apiES; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; Net_Api-≟; Link; apiBF; input; output
        ; sendBFBatchDone )
open import CSP.Examples.Cardano_network.Data p
  using ( Payload; blockFetch; MessageBlockFetch; MsgBatchDone; MsgBlock )
open import CSP.Examples.Cardano_network.Base
  using ( Dir; lo; hi; N2N_BlockFetch; Mode )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( Time; Length )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )
import CSP.Examples.Cardano_network.BlockFetch p as BF

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∖_; _⦀_; viewV; EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( ev; evl; evLabel; _─[_]─►_; sVis )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; med; nA; nB; nC; nD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( CopyPhase; broken; phase; empty; full; draining )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using ( ProdPh; pp0; pp1; pp2; pp3; pp4; pp5; pp6; pp7; pp8; pp9
              ; decProd )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.NodeSpecs blkA as NS
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep
open SStep using ( NetProc; IoOffers; ⦀-ev-L; ⦀-ev-R; ⦀-noOffer
                 ; lift-api-node-ev
                 ; absBFs; absBundleG; absNodeA; absNodeB; absNodeC; absNodeD
                 ; absNodesOf; coarsenBFc; coarsenBFs )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( RState; radec; toSys )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA
  using ( ApiHasLink; ahlBF; IsApiCSBF; aicBF )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_PeerEvCSBF blkA
  using ( aBFs; ceqBFs06; ceqBFs12; ceqBFc06 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_TauCore blkA
  using ( ≟-yes-refl )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_GapBDisj blkA
  using ( noOffer→viewV )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_RouteKaTs blkA
  using ( absBundle-BFs-ev )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysRoute blkA
  using ( ApiIsProd; aipBFdone
        ; absNodeB-no-when-A; absNodeC-no-when-A; absNodeD-no-when-A )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink blkA
  using ( linkAB≢linkAC )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink6 blkA
  using ( absBundleG-api-no; drvA-AB-no; drvA-AC-no )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( prodOf; cellUp; upClient; BFcHasBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA
  using ( upSrv )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValFill blkA
  using ( blkPayload )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeFillSource blkA
  using ( upLink )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.Spec
  using ( hidden )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveStableOffer blkA
  using ( hiddenMove-⊥; apiNodes-whole )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveIoIntro blkA
  using ( medDrainτ; bfs-in-step; srvInNodes-A-AB; srvInNodes-A-AC )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveChanInv blkA
  using ( ChanUp; SrvStr; CliStrA; CliBusyA; ChanStr; CellQuiet; FullMsg
        ; cvStr; cvBd; bdPayload; streamAcceptsBlkM )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveChanRead blkA
  using ( cellFull-up-⊥; CliAcceptsA )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveSrvOpen blkA
  using ( medτMove-⊥; srvSendMove-at-⊥ )
-- (T10) §8's acceptance probe reads the BUILT cone field, qualified
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegApiCone blkA as LAC

------------------------------------------------------------------------
-- §1  THE LEG WRAPPERS.  Three one-liners that turn a VARIABLE leg into the
-- literal link and literal node slot the banked kits are stated at.  Every
-- lemma below that touches the medium or the nodes goes through one of them,
-- which is what lets §6 stay leg-GENERIC where `LiveSrvOpen` §2 had to split
-- (its arms name `cellUp legBD` directly; these three do not).
------------------------------------------------------------------------

-- the leg's UP cell IS the medium phase the io kits name — convertible only
-- once the leg is a constructor, exactly as `LiveRelayCS.dnCSs-is-of` is
cellUp-is : (l : TwoLegs) (s : SysState)
          → cellUp l s ≡ phase (med s) (upLink l) hi N2N_BlockFetch
cellUp-is legBD s = refl
cellUp-is legCD s = refl

-- … and the nodes-side io intro at node A's own up server, per leg (rungs 2-4
-- of the WRITE ladder, banked and payload/target-generic)
srvInNodes-A : (l : TwoLegs) (s : SysState) (x : Payload) (bfs′ : SN.BFsPos)
             → absBFs (upLink l) hi (upSrv l s)
                 ─[ ev (evl (evLabel Payload (input (upLink l) hi N2N_BlockFetch) x)) ]─►
               absBFs (upLink l) hi bfs′
             → IoOffers (absNodesOf s) (input (upLink l) hi N2N_BlockFetch) x
srvInNodes-A legBD s x bfs′ st = srvInNodes-A-AB s x bfs′ st
srvInNodes-A legCD s x bfs′ st = srvInNodes-A-AC s x bfs′ st

------------------------------------------------------------------------
-- §2  *** `nodes-offer-A` — THE FOUR-NODE LIFT THE TREE DID NOT HAVE. ***
--
-- Node A is the FIRST of the four `⦀` operands, so the ladder is ONE `⦀-ev-L`
-- and one nested refusal group; and the three sibling refusals are the
-- fingerprint family's node-A row (`SysRoute:2042-2064`), keyed on
-- "a PRODUCER-role api event on one of node A's two links".  Node B and node C
-- refuse by role-or-link, node D by role alone (it never produces).
--
-- The shape is `LiveDrvCSD.nodes-offer-D`'s at the other end of the `⦀` nest,
-- and its fingerprint is the mirror image: node D's is a CONSUMER tag on a D
-- link, node A's a PRODUCER tag on an A link.
------------------------------------------------------------------------

nodes-offer-A : (s : SysState) {X : Set 0ℓ} {ee : Net_Api Payload X} {a : X}
  → apiES .mem (X , ee) a
  → ApiIsProd ee × (ApiHasLink linkAB ee ⊎ ApiHasLink linkAC ee)
  → IoOffers (absNodeA (nA s)) ee a
  → IoOffers (absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) ee a
nodes-offer-A s am fp (M , st) =
    _
  , ⦀-ev-L _ _ st
      (noOffer→viewV _
        (⦀-noOffer _ _ (absNodeB-no-when-A (nB s) am fp)
          (⦀-noOffer _ _ (absNodeC-no-when-A (nC s) am fp)
                         (absNodeD-no-when-A (nD s) am fp))))

------------------------------------------------------------------------
-- §3  THE TWO NODE-A SYNC KITS.  `LiveDrvCSD` §2's shape at node A: its two
-- bundles sit on different sides of BOTH of its `⦀`s (the bundle pair AND the
-- produce-driver pair), so link AB is `⦀-ev-L` twice and link AC `⦀-ev-R`
-- twice.  Each kit is generic in the event, the value and the bundle successor.
------------------------------------------------------------------------

-- LINK AB (node A's LEFT bundle at `(lo, hi)` and its LEFT produce driver)
syncA-AB : (r : RState) {X : Set 0ℓ} {ee : Net_Api Payload X} {a : X} {B′ : NetProc}
  → IsApiCSBF ee → ApiHasLink linkAB ee → ApiIsProd ee
  → mem (hidden blkA) (X , ee) a → (ioES .mem (X , ee) a → ⊥)
  → apiES .mem (X , ee) a
  → absBundleG linkAB lo hi
      (SN.NodeStateA.csC-AB (nA (toSys r))) (SN.NodeStateA.csS-AB (nA (toSys r)))
      (SN.NodeStateA.bfC-AB (nA (toSys r))) (SN.NodeStateA.bfS-AB (nA (toSys r)))
      (SN.NodeStateA.inert-AB (nA (toSys r)))
      ─[ ev (evl (evLabel X ee a)) ]─► B′
  → IoOffers (decProd linkAB hi blkA (SN.NodeStateA.prod-AB (nA (toSys r)))) ee a
  → isStable (radec r ∖ hidden blkA) → ⊥
syncA-AB r aic ahl aiprod hid ¬io am bstep dOff sta =
  hiddenMove-⊥ r hid
    (apiNodes-whole r aic ¬io
      (nodes-offer-A (toSys r) am (aiprod , inj₁ ahl)
        ( _
        , lift-api-node-ev _ _ am
            (⦀-ev-L _ _ bstep
              (noOffer→viewV _
                (absBundleG-api-no linkAC lo hi
                   (SN.NodeStateA.csC-AC (nA (toSys r))) (SN.NodeStateA.csS-AC (nA (toSys r)))
                   (SN.NodeStateA.bfC-AC (nA (toSys r))) (SN.NodeStateA.bfS-AC (nA (toSys r)))
                   (SN.NodeStateA.inert-AC (nA (toSys r)))
                   ahl linkAB≢linkAC am)))
            (⦀-ev-L _ _ (proj₂ dOff)
              (noOffer→viewV _ (drvA-AC-no (nA (toSys r)) ahl))))))
    sta

-- LINK AC (both node-A operands are the RIGHT ones, and the sibling pins are
-- the `linkAB` ones)
syncA-AC : (r : RState) {X : Set 0ℓ} {ee : Net_Api Payload X} {a : X} {B′ : NetProc}
  → IsApiCSBF ee → ApiHasLink linkAC ee → ApiIsProd ee
  → mem (hidden blkA) (X , ee) a → (ioES .mem (X , ee) a → ⊥)
  → apiES .mem (X , ee) a
  → absBundleG linkAC lo hi
      (SN.NodeStateA.csC-AC (nA (toSys r))) (SN.NodeStateA.csS-AC (nA (toSys r)))
      (SN.NodeStateA.bfC-AC (nA (toSys r))) (SN.NodeStateA.bfS-AC (nA (toSys r)))
      (SN.NodeStateA.inert-AC (nA (toSys r)))
      ─[ ev (evl (evLabel X ee a)) ]─► B′
  → IoOffers (decProd linkAC hi blkA (SN.NodeStateA.prod-AC (nA (toSys r)))) ee a
  → isStable (radec r ∖ hidden blkA) → ⊥
syncA-AC r aic ahl aiprod hid ¬io am bstep dOff sta =
  hiddenMove-⊥ r hid
    (apiNodes-whole r aic ¬io
      (nodes-offer-A (toSys r) am (aiprod , inj₂ ahl)
        ( _
        , lift-api-node-ev _ _ am
            (⦀-ev-R _ _ bstep
              (noOffer→viewV _
                (absBundleG-api-no linkAB lo hi
                   (SN.NodeStateA.csC-AB (nA (toSys r))) (SN.NodeStateA.csS-AB (nA (toSys r)))
                   (SN.NodeStateA.bfC-AB (nA (toSys r))) (SN.NodeStateA.bfS-AB (nA (toSys r)))
                   (SN.NodeStateA.inert-AB (nA (toSys r)))
                   ahl (λ q → linkAB≢linkAC (sym q)) am)))
            (⦀-ev-R _ _ (proj₂ dOff)
              (noOffer→viewV _ (drvA-AB-no (nA (toSys r)) ahl))))))
    sta

------------------------------------------------------------------------
-- §4  *** THE NODE-A ARM: `pp6` × `bsStream` IS NOT STABLE. ***
--
-- The two offers, then the two kits.  The PEER offer is `LiveRelayOpen` §2's
-- shape at `ceqBFs06` (`bfSnxt bsStream … sendBFBatchDone ≡ just bsWbd`), the
-- DRIVER offer is its §3's at `decProd`'s `pp6` clause (`SysNode:826-827`,
-- whose head IS `apiBF l d sendBFBatchDone ! U.tt`).
--
-- The hidden-ness side condition is `refl`: `keptB`'s only two non-`break`
-- clauses are `sendBFBlock` and `recvBFBlock`, so this event falls to its
-- catch-all with no link, dir or block test consulted.
------------------------------------------------------------------------

-- the up BF SERVER at a position coarsening to `bsStream` offers node A's
-- `sendBFBatchDone` (`bfSnxt bsStream`, `NodeSpecs:625-627`)
peer-A-bd : (i : Link) (d : Dir) (q : SN.BFsPos)
          → coarsenBFs q ≡ NS.bsStream
          → absBFs i d q ─[ ev (evl (evLabel U.⊤ (apiBF i d sendBFBatchDone) U.tt)) ]─►
            absBFs i d SN.bsBatchDone1
peer-A-bd i d q pin =
  aBFs i d q SN.bsBatchDone1
    (subst (λ z → NS.bfSfin z ≡ false) (sym pin) refl)
    (subst (λ z → NS.bfSnxt i d z (U.⊤ , apiBF i d sendBFBatchDone) U.tt
                  ≡ just NS.bsWbd)
           (sym pin) (ceqBFs06 i d))

-- … and node A's produce driver at `pp6` offers the same event (the prefix's
-- own offer map, with `≟-yes-refl` unsticking the link comparison inside
-- `Net_Api-≟`; the carried value is `U.tt`, so nothing else needs unsticking)
prodVis-pp6 : (i : Link) (b : Block₃)
  → viewV (PTree.force (decProd i hi b pp6)) (U.⊤ , apiBF i hi sendBFBatchDone) U.tt
    ≡ just (decProd i hi b pp7)
prodVis-pp6 i b rewrite ≟-yes-refl i = refl

prodA-offer-pp6 : (i : Link) (b : Block₃)
                → IoOffers (decProd i hi b pp6) (apiBF i hi sendBFBatchDone) U.tt
prodA-offer-pp6 i b = _ , sVis refl (prodVis-pp6 i b)

-- *** THE ARM. ***  Node A's driver at `pp6` and its up BF server at `bsStream`
-- are an ENABLED api sync, so the configuration is not stable.  Two hypotheses
-- and nothing else: no `broken`, no channel invariant, no token — exactly
-- `LiveRelayOpen` §5's nine arms' shape, at the fourth node.
arm-A-pp6 : (l : TwoLegs) (r : RState)
          → prodOf l (toSys r) ≡ pp6
          → coarsenBFs (upSrv l (toSys r)) ≡ NS.bsStream
          → isStable (radec r ∖ hidden blkA) → ⊥
arm-A-pp6 legBD r hpp pin sta =
  syncA-AB r aicBF ahlBF aipBFdone refl (λ ()) tt
    (absBundle-BFs-ev linkAB lo hi
       (SN.NodeStateA.csC-AB (nA (toSys r))) (SN.NodeStateA.csS-AB (nA (toSys r)))
       (SN.NodeStateA.bfC-AB (nA (toSys r))) (SN.NodeStateA.bfS-AB (nA (toSys r)))
       (SN.NodeStateA.inert-AB (nA (toSys r)))
       {e₁ = BF.apiBFev linkAB hi sendBFBatchDone} {qbs′ = SN.bsBatchDone1} (λ ()) refl
       (peer-A-bd linkAB hi (SN.NodeStateA.bfS-AB (nA (toSys r))) pin))
    (subst (λ y → IoOffers (decProd linkAB hi blkA y) (apiBF linkAB hi sendBFBatchDone) U.tt)
           (sym hpp) (prodA-offer-pp6 linkAB blkA))
    sta
arm-A-pp6 legCD r hpp pin sta =
  syncA-AC r aicBF ahlBF aipBFdone refl (λ ()) tt
    (absBundle-BFs-ev linkAC lo hi
       (SN.NodeStateA.csC-AC (nA (toSys r))) (SN.NodeStateA.csS-AC (nA (toSys r)))
       (SN.NodeStateA.bfC-AC (nA (toSys r))) (SN.NodeStateA.bfS-AC (nA (toSys r)))
       (SN.NodeStateA.inert-AC (nA (toSys r)))
       {e₁ = BF.apiBFev linkAC hi sendBFBatchDone} {qbs′ = SN.bsBatchDone1} (λ ()) refl
       (peer-A-bd linkAC hi (SN.NodeStateA.bfS-AC (nA (toSys r))) pin))
    (subst (λ y → IoOffers (decProd linkAC hi blkA y) (apiBF linkAC hi sendBFBatchDone) U.tt)
           (sym hpp) (prodA-offer-pp6 linkAC blkA))
    sta

------------------------------------------------------------------------
-- §5  THE TWO NEW io RUNG-1s — the ONLY new io material the arm needs.
--
-- Both ladders' rungs 2-4 are banked and generic; what a new POSITION costs is
-- one `ceq*` instance apiece.  (The T9 verification measured the same thing on
-- the ChainSync axis and found 22 lines; this is the BlockFetch confirmation.)
------------------------------------------------------------------------

-- the up server at `bsWbd` offers the wire-send of its `MsgBatchDone`
-- (`ceqBFs12`) — `bfs-in-step`'s twin at the batch's END rather than its block
bfs-in-step-bd : (i : Link) (d : Dir) (q : SN.BFsPos)
               → coarsenBFs q ≡ NS.bsWbd
               → absBFs i d q
                   ─[ ev (evl (evLabel Payload (input i d N2N_BlockFetch) bdPayload)) ]─►
                 absBFs i d (SN.bsHead BF.stIdle)
bfs-in-step-bd i d q pin =
  aBFs i d q (SN.bsHead BF.stIdle)
    (subst (λ z → NS.bfSfin z ≡ false) (sym pin) refl)
    (subst (λ z → NS.bfSnxt i d z (Payload , input i d N2N_BlockFetch) bdPayload
                  ≡ just NS.bsIdle)
           (sym pin) (ceqBFs12 i d))

-- … and the client at `bcStream` ACCEPTS that message's delivery (`ceqBFc06`,
-- lenient in `(time , mode , length)` exactly as the cell's own witness is)
streamAcceptsBdM : (i : Link) (t : Time) (md : Mode) (ln : Length)
                 → CliAcceptsA i hi NS.bcStream (t , md , ln , blockFetch MsgBatchDone)
streamAcceptsBdM i t md ln = NS.bcIdle , ceqBFc06 {t} {md} {ln} i hi

------------------------------------------------------------------------
-- §6  *** THE LEAF: A STABLE CONFIGURATION HAS NO STREAMING UP CLIENT. ***
--
-- The one cross-node fact is a HYPOTHESIS (`pin6`), so this lemma is closed and
-- premise-free; supplying `pin6` is the `cp4` arm's whole remaining obligation
-- and it is an invariant question, not an io one.
------------------------------------------------------------------------

-- the streaming region's three members, as an explicit disjunction to dispatch
-- on (the `cliStr⇒eq` shape at the server's side; total, no catch-all)
srvStr-cases : (q : NS.BFsPos) → SrvStr q
             → (q ≡ NS.bsStream)
               ⊎ (Σ[ b ∈ Block₃ ] (q ≡ NS.bsWblk b))
               ⊎ (q ≡ NS.bsWbd)
srvStr-cases NS.bsIdle      ()
srvStr-cases (NS.bsAreq r)  ()
srvStr-cases NS.bsBusy      ()
srvStr-cases NS.bsDdone     ()
srvStr-cases NS.bsWsb       ()
srvStr-cases NS.bsStream    _ = inj₁ refl
srvStr-cases NS.bsWnb       ()
srvStr-cases (NS.bsWblk b)  _ = inj₂ (inj₁ (b , refl))
srvStr-cases NS.bsWbd       _ = inj₂ (inj₂ refl)
srvStr-cases NS.bsTerm      ()

-- *** THE LEAF. ***
upStream-⊥ : (l : TwoLegs) (r : RState)
           → broken (med (toSys r)) (upLink l) ≡ false
           → ChanUp l (toSys r)
           -- the ONE cross-node fact: a streaming up server pins node A's driver
           → (coarsenBFs (upSrv l (toSys r)) ≡ NS.bsStream → prodOf l (toSys r) ≡ pp6)
           → coarsenBFc (upClient l (toSys r)) ≡ NS.bcStream
           → isStable (radec r ∖ hidden blkA) → ⊥
upStream-⊥ l r hbrk ivU pin6 hcli sta =
  arms (cvBd ivU (subst CliStrA (sym hcli) tt))
  where
  -- the cell, at the medium form the io kits want
  hcell : cellUp l (toSys r) ≡ phase (med (toSys r)) (upLink l) hi N2N_BlockFetch
  hcell = cellUp-is l (toSys r)
  -- the EMPTY-cell dispatch, on the server's own three streaming positions
  emptyArms : cellUp l (toSys r) ≡ empty
            → (coarsenBFs (upSrv l (toSys r)) ≡ NS.bsStream)
              ⊎ (Σ[ b ∈ Block₃ ] (coarsenBFs (upSrv l (toSys r)) ≡ NS.bsWblk b))
              ⊎ (coarsenBFs (upSrv l (toSys r)) ≡ NS.bsWbd)
            → ⊥
  emptyArms he (inj₁ hs) = arm-A-pp6 l r (pin6 hs) hs sta
  emptyArms he (inj₂ (inj₁ (b , hs))) =
    srvSendMove-at-⊥ r (upLink l) (blkPayload b) hbrk (trans (sym hcell) he)
      (srvInNodes-A l (toSys r) (blkPayload b) (SN.bsHead BF.stStreaming)
        (bfs-in-step (upLink l) hi (upSrv l (toSys r)) b hs))
      sta
  emptyArms he (inj₂ (inj₂ hs)) =
    srvSendMove-at-⊥ r (upLink l) bdPayload hbrk (trans (sym hcell) he)
      (srvInNodes-A l (toSys r) bdPayload (SN.bsHead BF.stIdle)
        (bfs-in-step-bd (upLink l) hi (upSrv l (toSys r)) hs))
      sta
  -- … and the QUIET-cell dispatch it sits inside
  quietArms : SrvStr (coarsenBFs (upSrv l (toSys r))) → CellQuiet (cellUp l (toSys r)) → ⊥
  quietArms hstr (inj₁ he) =
    emptyArms he (srvStr-cases (coarsenBFs (upSrv l (toSys r))) hstr)
  quietArms hstr (inj₂ (inj₁ (x , hd))) =
    medτMove-⊥ r (medDrainτ (med (toSys r)) (upLink l) x hbrk (trans (sym hcell) hd)) sta
  quietArms hstr (inj₂ (inj₂ (b , t , md , ln , hf))) =
    cellFull-up-⊥ l r (t , md , ln , blockFetch (MsgBlock b)) hbrk hf
      (subst (λ z → CliAcceptsA (upLink l) hi z (t , md , ln , blockFetch (MsgBlock b)))
             (sym hcli) (streamAcceptsBlkM (upLink l) t md ln b))
      sta
  -- the streaming-server arm: the awaiting disjunct is refuted by the client's
  -- own position, so only the quiet one survives
  strArms : SrvStr (coarsenBFs (upSrv l (toSys r)))
          → ChanStr (cellUp l (toSys r)) (coarsenBFc (upClient l (toSys r))) → ⊥
  strArms hstr (inj₁ (_ , hbusy)) = subst CliBusyA hcli hbusy
  strArms hstr (inj₂ (hq , _))    = quietArms hstr hq
  -- THE SPLIT the (T10) client-antecedent clause hands out
  arms : SrvStr (coarsenBFs (upSrv l (toSys r)))
         ⊎ FullMsg (cellUp l (toSys r)) MsgBatchDone → ⊥
  arms (inj₁ hstr) = strArms hstr (cvStr ivU hstr)
  arms (inj₂ (t , md , ln , hf)) =
    cellFull-up-⊥ l r (t , md , ln , blockFetch MsgBatchDone) hbrk hf
      (subst (λ z → CliAcceptsA (upLink l) hi z (t , md , ln , blockFetch MsgBatchDone))
             (sym hcli) (streamAcceptsBdM (upLink l) t md ln))
      sta

------------------------------------------------------------------------
-- §7  THE MODULE's FALSIFICATION — ONE, at its own novelty (the node-A arm).
--
-- (F87  THE `pp6` PIN IS LOAD-BEARING, AND IT IS THE DRIVER's SIDE THAT CARRIES
--      IT)  `prodVis-pp6`'s statement re-aimed at `pp5` — the sub-phase one hop
--      EARLIER, where node A's produce driver is still offering `sendBFBlock`.
--      Arity-preserving (same event, same value, same successor), and it is the
--      mutation a reader who thinks "node A is in its batch, so the batch-done
--      offer must be live" would not catch.
--      *** RED ***: `LiveUpOpen.agda:301.40-44: [UnequalTerms] Data.Maybe.nothing
--      != just (Prefix … (done i hi N2N_ChainSync) …)`, EXIT=42.  **The error
--      exhibits both sides of the pin**: the offer map at `pp5` answers `nothing`
--      for `sendBFBatchDone`, and the `just` it is compared against is `pp7`'s own
--      continuation — i.e. the event is offered at `pp6` and NOWHERE earlier, which
--      is precisely why `upStream-⊥` needs `prodOf ≡ pp6` and not merely
--      `ProdSent`.  Re-aiming note: F87 dies if `decProd`'s `pp5` clause ever stops
--      leading with `sendBFBlock`.
--
-- No second guard is owed here: §2's lift, §3's kits and §4's arm are ONE family
-- (the node-A api sync), §5's two rung-1s are instances of two banked families
-- whose guards are `LiveIoIntro`'s and `LiveChanRead`'s, and §6 is a dispatch with
-- no new construction of its own.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §8  (T10) *** WHAT THE `cp4` ARM STILL OWES, AS TYPES. ***
--
-- The `LiveTokenExcl` §1b precedent: an obligation a task could not fund is
-- STATED here — type-checked, named, and with the machine-check that it is exactly
-- what the discharge needs — rather than described in a report.  Nothing in this
-- module depends on any of it; §6's leaf and `LiveDrvBFA.upBd⇒pp6` are complete
-- without it.
--
-- *** THE ARM's SHAPE AT THE DISCHARGE SITE. ***  `LiveRelayCS.coAt-split-at`'s
-- `cp4` clause has to produce `coarsenBFc (upClient l s) ≡ NS.bcIdle`.  With §6 and
-- `LiveDrvBFA` in hand, the ONLY thing between the two is a REGION: the client's
-- seven positions, minus the two that are already answered.  `bcIdle` IS the
-- conclusion, `bcStream` is §6's leaf — and the other five are neither refutable by
-- stability nor derivable from any landed invariant:
--
--   · `bcBusy` — `LiveRelayCS.chanInv-idle-busy` is the machine-checked witness
--     that `(bsIdle , empty , bcBusy)` satisfies the channel invariant and has no
--     enabled move; the same shape answers `bcWrr r`, `bcWcd` and `bcTerm`;
--   · `bcAblk b` — its ONE surviving configuration is an unread `MsgBatchDone` in
--     the cell (every other one falls to §6's own five leaves plus the carried
--     `NoTwoTokens`), and that configuration is REACHABLE at `cp3` — the relay's
--     driver has not yet taken the block — so no channel-level clause can exclude
--     it.  It is excluded at `cp4` and only there.
--
-- *** SO THE ARM's LAST OBJECT IS A RELAY-PHASE-GUARDED CLIENT REGION, AND ITS ONE
-- UNBUILT INGREDIENT IS A LANDING. ***  Establishment at the entering step is FREE
-- from facts the cone already carries (`LegDriverStep.ldRelay`'s `wUp` field gives
-- `upClient l s ≡ bcBlk1 bc` and `relayOf l s′ ≡ consuming bc cp4`; `NoTwoTokens`'
-- `nUpSrvCli`/`nUpCellCli` give the two companions at that same state, because the
-- client HOLDS there) — EXCEPT for the target's own position, which needs the
-- relay's own `recvBFBlock` crossing to be pinned.  That is `LiveLegApiCone.UpCsDrv`'s
-- twin on the BlockFetch axis, and it is the last cone component the campaign owes.
------------------------------------------------------------------------

-- PARKED (T11): the relay's UP-hop BF client region at `cp4` — `{bcIdle, bcStream}`,
-- with the two companions that make it preservable (no block in node A's server, no
-- unread block in the up cell).  §6's leaf consumes the FIRST component and the
-- other two exist to carry it across the io class
UpCliReg : NS.BFcPos → Set
UpCliReg NS.bcIdle      = ⊤
UpCliReg (NS.bcWrr r)   = ⊥
UpCliReg NS.bcBusy      = ⊥
UpCliReg NS.bcWcd       = ⊥
UpCliReg NS.bcStream    = ⊤
UpCliReg (NS.bcAblk b)  = ⊥
UpCliReg NS.bcTerm      = ⊥

-- … and the two positions it leaves are exactly the arm's two answered ones: the
-- conclusion and §6's leaf.  A machine check, not a comment
upCliReg-cases : (q : NS.BFcPos) → UpCliReg q
               → (q ≡ NS.bcIdle) ⊎ (q ≡ NS.bcStream)
upCliReg-cases NS.bcIdle      _  = inj₁ refl
upCliReg-cases (NS.bcWrr r)   ()
upCliReg-cases NS.bcBusy      ()
upCliReg-cases NS.bcWcd       ()
upCliReg-cases NS.bcStream    _  = inj₂ refl
upCliReg-cases (NS.bcAblk b)  ()
upCliReg-cases NS.bcTerm      ()

-- *** (T10, SAME TASK) THE PARKED INGREDIENT IS NO LONGER PARKED — `UpBfDrv` IS
-- BUILT, at `LiveLegApiCone` §2b′⁶ and the relay's own two peels, and exported as
-- `LiveLegApiExpose.deUpBfBD`/`deUpBfCD`. ***  The statement below is the ACCEPTANCE
-- PROBE the controller asked for: `upBfDrv⇒reg` is re-pointed at the REAL cone type,
-- so if the built field ever drifts from what the region's establishment wants, THIS
-- lemma stops typechecking.  (The landing arm reports the PAIR — the target's
-- position AND the source's holding — because the region's two companion fields are
-- established from the source's holding through `NoTwoTokens`, and asking the cone
-- for it there costs one `subst`: the "state it source-and-target" lesson, applied
-- the second time in this task.)
upBfDrv⇒reg : (bfc bfc′ : SN.BFcPos) (x x′ : SN.CPPh) (b : Block₃)
            → LAC.UpBfDrv bfc bfc′ x x′ → x′ ≡ SN.consuming b SN.cp4
            → (x ≡ x′) ⊎ (UpCliReg (coarsenBFc bfc′) × BFcHasBlk bfc)
-- (A, cellCp3) re-cut by one `proj₁`: the cone slot gained a trailing PRE-REQUEST
-- component (a `×`, not a third `⊎` arm), which the `cp4` region does not read
upBfDrv⇒reg bfc bfc′ x x′ b (inj₁ (xeq , _) , _) _   = inj₁ xeq
upBfDrv⇒reg bfc bfc′ x x′ b (inj₂ land      , _) heq =
  inj₂ ( subst UpCliReg (sym (proj₁ (land b heq))) tt
       , proj₂ (land b heq) )
