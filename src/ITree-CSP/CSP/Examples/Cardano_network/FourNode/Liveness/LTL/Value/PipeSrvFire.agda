{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the io NODE cone with SERVER identification
-- (`Praos.PipeSrvFire`): the F1 blocker of the session-28 frontier.
--
-- `PipeFillSource.blockFill-forces-srv` says: a BF SERVER that fires the
-- cell-filling io `input _ _ N2N_BlockFetch ! pl` with a BLOCK payload must
-- already hold the block (`BFsHasBlk bfs`).  It is stated at ONE peer.  To use
-- it in the io `TauStep` the peer that actually fired must be identified with
-- the leg's own `PipeSrvInv.upSrv` / `dnSrv`, and
-- `PipeNodeFix.top-nodes-io-abs-client-cls` cannot do that — it returns the six
-- driver fixities + `AllClientClass` and NO server slot.
--
-- THIS module supplies the identification, in the strongest form the consumer
-- can use: from a WHOLE-NODES io step labelled `input l′ hi N2N_BlockFetch`
-- with a block payload it names the unique BF server that can have fired it.
--
-- The key model fact (checked against the `NodeSpecs.bfSnxt`/`bfCnxt` tables,
-- per the session-28 method mandate) is that on a link `l` the BF peers at
-- direction `hi` are: the SERVER of the bundle whose `sv ≡ hi`, and the CLIENT
-- of the bundle whose `cl ≡ hi`.  The client's only two wire-sends carry
-- `MsgRequestRange` / `MsgClientDone` (`blockFill-forces-cli` below), so a
-- BLOCK-carrying `input l hi …` can only come from a `sv ≡ hi` server.  In the
-- four-node diamond there is exactly ONE such server per link:
--
--     AB ↦ nodeA.bfS-AB  (= upSrv legBD)      BD ↦ nodeB.bfS-BD  (= dnSrv legBD)
--     AC ↦ nodeA.bfS-AC  (= upSrv legCD)      CD ↦ nodeC.bfS-CD  (= dnSrv legCD)
--
-- so `nodes-blockfill-hi` returns precisely the four `SrvCoupled` antecedents,
-- and the two leg bridges `fill-up-nodes` / `fill-dn-nodes` discharge the io
-- `TauStep`'s FILL case outright (`ProdSent` / `RelayFwd`).
--
-- Proof shape: NO cascade re-mirror.  The bundle-level step
-- (`bundle-blkfill-srv`) is by CONTRADICTION against a 12-peer `⦀-noOffer`
-- composition (the ten non-BF peers by the frozen `abs*-noBF` family, the BF
-- client by `blockFill-forces-cli`, the BF server by `blockFill-forces-srv`
-- resp. `absBFs-ev-dir`), which is ~12 lines instead of a 70-line peel.
--
-- Imported by nothing yet.  No postulate/hole/meta.  Base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
import Data.Unit as U
open import Relation.Nullary using ( ¬_; Dec; yes; no )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; subst )

open import Class.DecEq using ( DecEq; _≟_ )
import Class.DecEq.Instances as DecEqI

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvFire (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; apiES; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p
open import CSP.Examples.Cardano_network.Base
  using ( Dir; lo; hi; N2N_BlockFetch; FromInitiator )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; Net_Api-≟; Link; input )
open import CSP.Examples.Cardano_network.Data p
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )
open import CSP.Examples.Cardano_network.NetworkPar p using ( ιBF )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; EventSet )
  renaming ( ∅ES to ∅ESa )
open EventSet using ( mem )

import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload}) as PEA

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )

import CSP.Examples.Cardano_network.BlockFetch p as BF

import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep
open SStep using ( NetProc; IoOffers; ⦀-noOffer
                 ; absBundleG; absNodeA; absNodeB; absNodeC; absNodeD; absNodesOf
                 ; absBFc; absBFs; coarsenBFc )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using ( BFcPos; BFsPos
              ; bcHead; bcReq1; bcDone1; bcBlk1; bcSil
              ; bsHead; bsReq1; bsDone1; bsStart1; bsNoBlk1; bsBlk1; bsBatchDone1; bsSil
              ; CScPos; CSsPos; InertPos; tsc; tss; kac; kas; lnc; lns; lfc; lfs
              ; decProd; decConsD; decCP )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA
  using ( io⇒¬api; apiLink-inj; ApiHasLink; ahlIn )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( tableSpec-ev-inv; nothing-absurd )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_RouteLnLf blkA
  using ( absKAc-noBF; absKAs-noBF; absCSc-noBF; absCSs-noBF
        ; absTSc-noBF; absTSs-noBF; absLNc-noBF; absLNs-noBF
        ; absLFc-noBF; absLFs-noBF )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink blkA
  using ( nodeA-drv-io-no; nodeB-drv-io-no; nodeC-drv-io-no; nodeD-drv-io-no
        ; linkAB≢linkAC; linkAB≢linkBD; linkAC≢linkCD; linkBD≢linkCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink2 blkA
  using ( lo≢hi )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink3 blkA
  using ( absBundleG-io-ahl; absGroupA-io-no; absGroupB-io-no
        ; absNodeC-io-fp; absNodeD-io-no-when-C )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink5 blkA
  using ( Tbfc )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink6 blkA
  using ( absBFs-ev-dir )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; nA; nB; nC; nD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( prodOf; relayOf; ProdSent; RelayFwd )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleEvo blkA
  using ( BFsHasBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA
  using ( SrvCoupled; upSrv; dnSrv )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeFillSource blkA
  using ( PlIsBlk; blockFill-forces-srv; upLink; dnLink )

------------------------------------------------------------------------
-- (0) The BF CLIENT never wire-sends a block — the client twin of
-- `PipeFillSource.blockFill-forces-srv`.  `bfCnxt` offers `input _ _ BF` at
-- exactly two positions (`bcWrr r` / `bcWcd`), whose payloads are
-- `MsgRequestRange r` / `MsgClientDone`; every other position has an empty
-- `nxt` on that channel.
------------------------------------------------------------------------

-- firing the cell-filling io out of a BF client is never a BLOCK send
blockFill-forces-cli :
    (l : Link) (d : Dir) (bfc : BFcPos)
    {l′ : Link} {d′ : Dir} {pl : Payload} {M : NetProc}
  → absBFc l d bfc ─[ ev (evl (evLabel Payload (input l′ d′ N2N_BlockFetch) pl)) ]─► M
  → PlIsBlk pl → ⊥
-- the two wire-send positions DO fire this io, but never with a block
blockFill-forces-cli l d (bcReq1 r) {l′} {d′} {pl} step blk
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcReq1 r)) step
... | q′ , ceq , _ with l′ ≟ l | d′ ≟ d
...   | no  _    | _     = nothing-absurd ceq
...   | yes refl | no  _ = nothing-absurd ceq
...   | yes refl | yes refl
      with pl ≟ (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r))
...     | no  _   = nothing-absurd ceq
...     | yes peq = subst PlIsBlk peq blk
blockFill-forces-cli l d bcDone1 {l′} {d′} {pl} step blk
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc bcDone1) step
... | q′ , ceq , _ with l′ ≟ l | d′ ≟ d
...   | no  _    | _     = nothing-absurd ceq
...   | yes refl | no  _ = nothing-absurd ceq
...   | yes refl | yes refl
      with pl ≟ (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone)
...     | no  _   = nothing-absurd ceq
...     | yes peq = subst PlIsBlk peq blk
-- every remaining position offers NO io on the BlockFetch input channel
blockFill-forces-cli l d (bcHead BF.stIdle) step blk
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , _ = nothing-absurd ceq
blockFill-forces-cli l d (bcHead BF.stBusy) step blk
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , _ = nothing-absurd ceq
blockFill-forces-cli l d (bcHead BF.stStreaming) step blk
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , _ = nothing-absurd ceq
blockFill-forces-cli l d (bcHead BF.stDone) step blk
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stDone)) step
... | q′ , ceq , _ = nothing-absurd ceq
blockFill-forces-cli l d (bcBlk1 b) step blk
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , _ = nothing-absurd ceq
blockFill-forces-cli l d (bcSil BF.stIdle) step blk
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stIdle)) step
... | q′ , ceq , _ = nothing-absurd ceq
blockFill-forces-cli l d (bcSil BF.stBusy) step blk
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stBusy)) step
... | q′ , ceq , _ = nothing-absurd ceq
blockFill-forces-cli l d (bcSil BF.stStreaming) step blk
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stStreaming)) step
... | q′ , ceq , _ = nothing-absurd ceq
blockFill-forces-cli l d (bcSil BF.stDone) step blk
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stDone)) step
... | q′ , ceq , _ = nothing-absurd ceq

------------------------------------------------------------------------
-- (1) The 12-peer bundle no-offer for a BF-image event, parametric in the two
-- BF peers' own no-offers (the ten inert/CS peers are frozen `abs*-noBF`).
------------------------------------------------------------------------

-- a bundle offers a BF event only if one of its two BF peers does
bundleG-io-no-BF : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X}
  → ¬ IoOffers (absBFc l cl bfc) (ιBF e₁) a
  → ¬ IoOffers (absBFs l sv bfs) (ιBF e₁) a
  → ¬ IoOffers (absBundleG l cl sv csc css bfc bfs ip) (ιBF e₁) a
bundleG-io-no-BF l cl sv csc css bfc bfs ip {X} {e₁} {a} ncl nsv =
  ⦀-noOffer _ _ (absKAc-noBF l cl (kac ip) e₁)
   (⦀-noOffer _ _ (absKAs-noBF l sv (kas ip) e₁)
    (⦀-noOffer _ _ (absCSc-noBF l cl csc e₁)
     (⦀-noOffer _ _ (absCSs-noBF l sv css e₁)
      (⦀-noOffer _ _ ncl
       (⦀-noOffer _ _ nsv
        (⦀-noOffer _ _ (absTSc-noBF l cl (tsc ip) e₁)
         (⦀-noOffer _ _ (absTSs-noBF l sv (tss ip) e₁)
          (⦀-noOffer _ _ (absLNc-noBF l cl (lnc ip) e₁)
           (⦀-noOffer _ _ (absLNs-noBF l sv (lns ip) e₁)
            (⦀-noOffer _ _ (absLFc-noBF l cl (lfc ip) e₁)
                           (absLFs-noBF l sv (lfs ip) e₁)))))))))))

------------------------------------------------------------------------
-- (2) THE BUNDLE-LEVEL IDENTIFICATION.  A block-carrying cell fill out of a
-- whole bundle pins the event direction to the bundle's SERVER side and forces
-- that server to hold the block.
------------------------------------------------------------------------

-- decide the server's block-holding predicate (`bsBlk1` is the only holder)
bfsHasBlk? : (bfs : BFsPos) → BFsHasBlk bfs ⊎ (BFsHasBlk bfs → ⊥)
bfsHasBlk? (bsHead _)   = inj₂ (λ ())
bfsHasBlk? (bsReq1 _)   = inj₂ (λ ())
bfsHasBlk? bsDone1      = inj₂ (λ ())
bfsHasBlk? bsStart1     = inj₂ (λ ())
bfsHasBlk? bsNoBlk1     = inj₂ (λ ())
bfsHasBlk? (bsBlk1 _)   = inj₁ tt
bfsHasBlk? bsBatchDone1 = inj₂ (λ ())
bfsHasBlk? (bsSil _)    = inj₂ (λ ())

-- `with`-free driver of `bundle-blkfill-srv` (the two decisions are ARGUMENTS,
-- so no goal is `with`-normalised — see the parameterisation hazard note)
bundle-blkfill-srv′ : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {l′ : Link} {d′ : Dir} {pl : Payload} {Bd′ : NetProc}
  → Dec (d′ ≡ sv) → BFsHasBlk bfs ⊎ (BFsHasBlk bfs → ⊥)
  → absBundleG l cl sv csc css bfc bfs ip
      ─[ ev (evl (evLabel Payload (input l′ d′ N2N_BlockFetch) pl)) ]─► Bd′
  → PlIsBlk pl
  → (d′ ≡ sv) × BFsHasBlk bfs
bundle-blkfill-srv′ l cl sv csc css bfc bfs ip {l′} {d′} (no d≢) hb step blk =
  ⊥-elim (bundleG-io-no-BF l cl sv csc css bfc bfs ip {e₁ = BF.sendBF l′ d′}
            (λ o → blockFill-forces-cli l cl bfc (proj₂ o) blk)
            (λ o → d≢ (absBFs-ev-dir l sv bfs {e₁ = BF.sendBF l′ d′} (proj₂ o)))
            (_ , step))
bundle-blkfill-srv′ l cl sv csc css bfc bfs ip (yes refl) (inj₁ h) step blk = refl , h
bundle-blkfill-srv′ l cl sv csc css bfc bfs ip {l′} {d′} (yes refl) (inj₂ ¬h) step blk =
  ⊥-elim (bundleG-io-no-BF l cl sv csc css bfc bfs ip {e₁ = BF.sendBF l′ d′}
            (λ o → blockFill-forces-cli l cl bfc (proj₂ o) blk)
            (λ o → ¬h (blockFill-forces-srv l sv bfs (proj₂ o) blk))
            (_ , step))

-- a BLOCK-carrying `input _ _ N2N_BlockFetch` out of a bundle came from the
-- bundle's SERVER, so the event direction is `sv` and the server holds a block
bundle-blkfill-srv : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {l′ : Link} {d′ : Dir} {pl : Payload} {Bd′ : NetProc}
  → absBundleG l cl sv csc css bfc bfs ip
      ─[ ev (evl (evLabel Payload (input l′ d′ N2N_BlockFetch) pl)) ]─► Bd′
  → PlIsBlk pl
  → (d′ ≡ sv) × BFsHasBlk bfs
bundle-blkfill-srv l cl sv csc css bfc bfs ip {l′} {d′} step blk =
  bundle-blkfill-srv′ l cl sv csc css bfc bfs ip (d′ ≟ sv) (bfsHasBlk? bfs) step blk

------------------------------------------------------------------------
-- (3) THE PER-NODE cones.  Each node is `(bundle ⦀ bundle) ∥⇘ apiES ⇙ drivers`;
-- the drivers are api-only (`nodeX-drv-io-no`) and the two bundles carry
-- DISTINCT links, so an io fire lands in exactly one bundle.  A `hi`-directed
-- BLOCK fill then hits the bundle whose `sv ≡ hi` (the other bundle's server
-- sits at `lo`, refuted by `lo≢hi`).
------------------------------------------------------------------------

-- node A hosts BOTH `sv ≡ hi` upstream servers (`bfS-AB`, `bfS-AC`)
nodeA-blockfill-hi : (na : SN.NodeStateA)
    {l′ : Link} {pl : Payload} {M : NetProc}
  → absNodeA na ─[ ev (evl (evLabel Payload (input l′ hi N2N_BlockFetch) pl)) ]─► M
  → PlIsBlk pl
  → ((l′ ≡ linkAB) × BFsHasBlk (SN.NodeStateA.bfS-AB na))
  ⊎ ((l′ ≡ linkAC) × BFsHasBlk (SN.NodeStateA.bfS-AC na))
nodeA-blockfill-hi na {l′} {pl} step blk
  with PEA.Par-ev-elim apiES (λ _ _ → tt)
         (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
          ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
         (decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ decProd linkAC hi blkA (SN.NodeStateA.prod-AC na))
         step
... | PEA.evSync amem _ _ = ⊥-elim (io⇒¬api {Payload} {input l′ hi N2N_BlockFetch} {pl} tt amem)
... | PEA.evR _ sD      = ⊥-elim (nodeA-drv-io-no na tt (_ , sD))
... | PEA.evBoth _ _ sD = ⊥-elim (nodeA-drv-io-no na tt (_ , sD))
... | PEA.evL _ sB
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
           (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
           sB
...   | PEA.evSync () _ _
...   | PEA.evBoth _ sBAB sBAC = ⊥-elim (linkAB≢linkAC
          (apiLink-inj (absBundleG-io-ahl linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) tt sBAB)
                       (absBundleG-io-ahl linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) tt sBAC)))
...   | PEA.evL _ sBAB = inj₁
          ( apiLink-inj ahlIn (absBundleG-io-ahl linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) tt sBAB)
          , proj₂ (bundle-blkfill-srv linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) sBAB blk) )
...   | PEA.evR _ sBAC = inj₂
          ( apiLink-inj ahlIn (absBundleG-io-ahl linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) tt sBAC)
          , proj₂ (bundle-blkfill-srv linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) sBAC blk) )

-- node B hosts ONE `sv ≡ hi` server (`bfS-BD`); its AB bundle serves at `lo`
nodeB-blockfill-hi : (nb : SN.NodeStateB)
    {l′ : Link} {pl : Payload} {M : NetProc}
  → absNodeB nb ─[ ev (evl (evLabel Payload (input l′ hi N2N_BlockFetch) pl)) ]─► M
  → PlIsBlk pl
  → (l′ ≡ linkBD) × BFsHasBlk (SN.NodeStateB.bfS-BD nb)
nodeB-blockfill-hi nb {l′} {pl} step blk
  with PEA.Par-ev-elim apiES (λ _ _ → tt)
         (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
          ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
         (decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
         step
... | PEA.evSync amem _ _ = ⊥-elim (io⇒¬api {Payload} {input l′ hi N2N_BlockFetch} {pl} tt amem)
... | PEA.evR _ sD      = ⊥-elim (nodeB-drv-io-no nb tt (_ , sD))
... | PEA.evBoth _ _ sD = ⊥-elim (nodeB-drv-io-no nb tt (_ , sD))
... | PEA.evL _ sB
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb))
           (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
           sB
...   | PEA.evSync () _ _
...   | PEA.evBoth _ sBAB sBBD = ⊥-elim (linkAB≢linkBD
          (apiLink-inj (absBundleG-io-ahl linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) tt sBAB)
                       (absBundleG-io-ahl linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) tt sBBD)))
...   | PEA.evL _ sBAB = ⊥-elim (lo≢hi (sym (proj₁
          (bundle-blkfill-srv linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) sBAB blk))))
...   | PEA.evR _ sBBD =
          ( apiLink-inj ahlIn (absBundleG-io-ahl linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) tt sBBD)
          , proj₂ (bundle-blkfill-srv linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) sBBD blk) )

-- node C mirrors node B (`bfS-CD` at `hi`, `bfS-AC` at `lo`)
nodeC-blockfill-hi : (nc : SN.NodeStateC)
    {l′ : Link} {pl : Payload} {M : NetProc}
  → absNodeC nc ─[ ev (evl (evLabel Payload (input l′ hi N2N_BlockFetch) pl)) ]─► M
  → PlIsBlk pl
  → (l′ ≡ linkCD) × BFsHasBlk (SN.NodeStateC.bfS-CD nc)
nodeC-blockfill-hi nc {l′} {pl} step blk
  with PEA.Par-ev-elim apiES (λ _ _ → tt)
         (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
          ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
         (decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
         step
... | PEA.evSync amem _ _ = ⊥-elim (io⇒¬api {Payload} {input l′ hi N2N_BlockFetch} {pl} tt amem)
... | PEA.evR _ sD      = ⊥-elim (nodeC-drv-io-no nc tt (_ , sD))
... | PEA.evBoth _ _ sD = ⊥-elim (nodeC-drv-io-no nc tt (_ , sD))
... | PEA.evL _ sB
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc))
           (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
           sB
...   | PEA.evSync () _ _
...   | PEA.evBoth _ sBAC sBCD = ⊥-elim (linkAC≢linkCD
          (apiLink-inj (absBundleG-io-ahl linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) tt sBAC)
                       (absBundleG-io-ahl linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) tt sBCD)))
...   | PEA.evL _ sBAC = ⊥-elim (lo≢hi (sym (proj₁
          (bundle-blkfill-srv linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) sBAC blk))))
...   | PEA.evR _ sBCD =
          ( apiLink-inj ahlIn (absBundleG-io-ahl linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) tt sBCD)
          , proj₂ (bundle-blkfill-srv linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) sBCD blk) )

-- node D hosts NO `sv ≡ hi` BF server: it can never block-fill on `hi`
nodeD-blockfill-hi : (nd : SN.NodeStateD)
    {l′ : Link} {pl : Payload} {M : NetProc}
  → absNodeD nd ─[ ev (evl (evLabel Payload (input l′ hi N2N_BlockFetch) pl)) ]─► M
  → PlIsBlk pl → ⊥
nodeD-blockfill-hi nd {l′} {pl} step blk
  with PEA.Par-ev-elim apiES (λ _ _ → tt)
         (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
          ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
         (decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ decConsD linkCD (SN.NodeStateD.cons-CD nd))
         step
... | PEA.evSync amem _ _ = io⇒¬api {Payload} {input l′ hi N2N_BlockFetch} {pl} tt amem
... | PEA.evR _ sD      = nodeD-drv-io-no nd tt (_ , sD)
... | PEA.evBoth _ _ sD = nodeD-drv-io-no nd tt (_ , sD)
... | PEA.evL _ sB
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
           (absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
           sB
...   | PEA.evSync () _ _
...   | PEA.evBoth _ sBBD sBCD = linkBD≢linkCD
          (apiLink-inj (absBundleG-io-ahl linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) tt sBBD)
                       (absBundleG-io-ahl linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) tt sBCD))
...   | PEA.evL _ sBBD = lo≢hi (sym (proj₁
          (bundle-blkfill-srv linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) sBBD blk)))
...   | PEA.evR _ sBCD = lo≢hi (sym (proj₁
          (bundle-blkfill-srv linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) sBCD blk)))

------------------------------------------------------------------------
-- (4) THE WHOLE-NODES SERVER CONE.  Exactly the four `SrvCoupled` antecedents,
-- keyed by the fired link — the server slot `PipeNodeFix.top-nodes-io-abs-
-- client-cls` is missing.
------------------------------------------------------------------------

-- the four `sv ≡ hi` BF servers of the diamond, keyed by their link
SrvHit : SysState → Link → Set
SrvHit s l′ =
    ((l′ ≡ linkAB) × BFsHasBlk (SN.NodeStateA.bfS-AB (nA s)))
  ⊎ ((l′ ≡ linkAC) × BFsHasBlk (SN.NodeStateA.bfS-AC (nA s)))
  ⊎ ((l′ ≡ linkBD) × BFsHasBlk (SN.NodeStateB.bfS-BD (nB s)))
  ⊎ ((l′ ≡ linkCD) × BFsHasBlk (SN.NodeStateC.bfS-CD (nC s)))

-- a whole-nodes BLOCK fill on the `hi` channel forces THE server of that link
nodes-blockfill-hi : (s : SysState) {l′ : Link} {pl : Payload} {M : NetProc}
  → absNodesOf s ─[ ev (evl (evLabel Payload (input l′ hi N2N_BlockFetch) pl)) ]─► M
  → PlIsBlk pl → SrvHit s l′
nodes-blockfill-hi s {l′} {pl} step blk
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (absNodeA (nA s)) (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s))) step
... | PEA.evSync () _ _
... | PEA.evBoth _ sA sRest = ⊥-elim (absGroupA-io-no (nA s) (nB s) (nC s) (nD s) tt sA (_ , sRest))
... | PEA.evL _ sA with nodeA-blockfill-hi (nA s) sA blk
...   | inj₁ q = inj₁ q
...   | inj₂ q = inj₂ (inj₁ q)
nodes-blockfill-hi s {l′} {pl} step blk | PEA.evR _ sRest
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s)) sRest
... | PEA.evSync () _ _
... | PEA.evBoth _ sB sCD = ⊥-elim (absGroupB-io-no (nB s) (nC s) (nD s) tt sB (_ , sCD))
... | PEA.evL _ sB  = inj₂ (inj₂ (inj₁ (nodeB-blockfill-hi (nB s) sB blk)))
nodes-blockfill-hi s {l′} {pl} step blk | PEA.evR _ sRest | PEA.evR _ sCD
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absNodeC (nC s)) (absNodeD (nD s)) sCD
... | PEA.evSync () _ _
... | PEA.evBoth _ sC sD = ⊥-elim (absNodeD-io-no-when-C (nD s) {Payload} {input l′ hi N2N_BlockFetch} {pl} tt
                                    (absNodeC-io-fp (nC s) {Payload} {input l′ hi N2N_BlockFetch} {pl} tt sC) (_ , sD))
... | PEA.evL _ sC = inj₂ (inj₂ (inj₂ (nodeC-blockfill-hi (nC s) sC blk)))
... | PEA.evR _ sD = ⊥-elim (nodeD-blockfill-hi (nD s) sD blk)

------------------------------------------------------------------------
-- (5) THE TWO LEG BRIDGES — the io `TauStep`'s FILL case, discharged.  The
-- leg's own cell key `(upLink l , hi)` / `(dnLink l , hi)` selects its own
-- server out of `SrvHit`, and `PipeSrvInv.SrvCoupled` converts holding into
-- `ProdSent` / `RelayFwd`.
------------------------------------------------------------------------

-- select the leg's UPSTREAM server out of a `SrvHit` at the leg's up link
-- (the three wrong-link disjuncts die on the `Fin numLinks` literals)
srvHit-up : (l : TwoLegs) (s : SysState) → SrvHit s (upLink l) → BFsHasBlk (upSrv l s)
srvHit-up legBD s (inj₁ (_ , h))               = h
srvHit-up legBD s (inj₂ (inj₁ ()))
srvHit-up legBD s (inj₂ (inj₂ (inj₁ ())))
srvHit-up legBD s (inj₂ (inj₂ (inj₂ ())))
srvHit-up legCD s (inj₁ ())
srvHit-up legCD s (inj₂ (inj₁ (_ , h)))        = h
srvHit-up legCD s (inj₂ (inj₂ (inj₁ ())))
srvHit-up legCD s (inj₂ (inj₂ (inj₂ ())))

-- select the leg's DOWNSTREAM server out of a `SrvHit` at the leg's down link
srvHit-dn : (l : TwoLegs) (s : SysState) → SrvHit s (dnLink l) → BFsHasBlk (dnSrv l s)
srvHit-dn legBD s (inj₁ ())
srvHit-dn legBD s (inj₂ (inj₁ ()))
srvHit-dn legBD s (inj₂ (inj₂ (inj₁ (_ , h)))) = h
srvHit-dn legBD s (inj₂ (inj₂ (inj₂ ())))
srvHit-dn legCD s (inj₁ ())
srvHit-dn legCD s (inj₂ (inj₁ ()))
srvHit-dn legCD s (inj₂ (inj₂ (inj₁ ())))
srvHit-dn legCD s (inj₂ (inj₂ (inj₂ (_ , h)))) = h

-- a whole-nodes BLOCK fill of the leg's UPSTREAM cell forces the producer SENT
fill-up-nodes : (l : TwoLegs) (s : SysState) {pl : Payload} {M : NetProc}
  → absNodesOf s ─[ ev (evl (evLabel Payload (input (upLink l) hi N2N_BlockFetch) pl)) ]─► M
  → PlIsBlk pl → SrvCoupled l s → ProdSent (prodOf l s)
fill-up-nodes l s step blk (uc , _) = uc (srvHit-up l s (nodes-blockfill-hi s step blk))

-- a whole-nodes BLOCK fill of the leg's DOWNSTREAM cell forces the relay FORWARDED
fill-dn-nodes : (l : TwoLegs) (s : SysState) {pl : Payload} {M : NetProc}
  → absNodesOf s ─[ ev (evl (evLabel Payload (input (dnLink l) hi N2N_BlockFetch) pl)) ]─► M
  → PlIsBlk pl → SrvCoupled l s → RelayFwd (relayOf l s)
fill-dn-nodes l s step blk (_ , dc) = dc (srvHit-dn l s (nodes-blockfill-hi s step blk))
