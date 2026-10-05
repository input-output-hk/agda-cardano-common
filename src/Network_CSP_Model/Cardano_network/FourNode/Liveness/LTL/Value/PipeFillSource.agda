{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the CELL-FILL io-SOURCE witness
-- (`Praos.PipeFillSource`), the correct replacement for the (false, see
-- `Praos.PipeCellFalse`) session-≤27 `FillSource` obligation.
--
-- After the session-28 payload refinement of `PipeInv.CellHasBlk`, a leg cell's
-- coupling antecedent fires only when the cell holds a BlockFetch `MsgBlock`.
-- The io that puts a `MsgBlock` into the cell is the BF SERVER's wire-send
-- `input l d N2N_BlockFetch ! (…, blockFetch (MsgBlock b))`, and the abstract
-- server table offers that exact io at EXACTLY ONE position — `bsBlk1 b`
-- (abstract `bsWblk b`), the state the server enters only from the api
-- `sendBFBlock`.  So a block-carrying fill FORCES `BFsHasBlk` of the sending
-- server, which is precisely the antecedent of `PipeSrvInv.SrvCoupled`.
--
-- This is the server twin of `PipeRecvSource.recvBFBlock-forces-src` (which
-- does the same job for the api receive at the BF CLIENT) and it is proved the
-- same way: a single offer-inversion case split over the concrete `BFsPos`,
-- with every non-`bsBlk1` position refuted by the abstract `nxt` table being
-- `nothing` on the io channel (the three OTHER wire-send positions `bsWsb` /
-- `bsWnb` / `bsWbd` are refuted instead by their payload, which is
-- `MsgStartBatch` / `MsgNoBlocks` / `MsgBatchDone` — not a block).
--
-- The two `fill-*-source` bridges then compose it with `SrvCoupled` to deliver
-- exactly what the io `TauStep`'s FILL case consumes: `ProdSent` upstream /
-- `RelayFwd` downstream.  What remains for the io `TauStep` is the io NODE cone
-- extended with SERVER slots (so the firing peer is identified with the leg's
-- own `upSrv`/`dnSrv`) — see the session report.
--
-- LIGHT (one offer-inversion case split; imports the R2 BF-server table
-- machinery + `PipeInv`/`PipeSrvInv`).  No postulate/hole/meta.  Base modules
-- READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Product using ( Σ; _×_; _,_; proj₁; proj₂ )
open import Relation.Nullary using ( yes; no )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; subst )

open import Class.DecEq using ( DecEq; _≟_ )
import Class.DecEq.Instances as DecEqI

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeFillSource (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p
open import CSP.Examples.Cardano_network.Base
  using ( Dir; hi; N2N_BlockFetch; FromResponder )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Link; input )
open import CSP.Examples.Cardano_network.Data p

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )

import CSP.Examples.Cardano_network.BlockFetch p as BF

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA using
  ( BFsPos; bsHead; bsReq1; bsDone1; bsStart1; bsNoBlk1; bsBlk1; bsBatchDone1; bsSil )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA using
  ( NetProc; absBFs; coarsenBFs )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA using
  ( tableSpec-ev-inv; nothing-absurd )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink5 blkA using ( Tbfs )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA using ( SysState )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( CellHasBlk; prodOf; relayOf; ProdSent; RelayFwd )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleEvo blkA
  using ( BFsHasBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA
  using ( SrvCoupled; upSrv; dnSrv )

------------------------------------------------------------------------
-- The wire-payload block predicate (definitionally `CellHasBlk` at a `full`
-- cell, so a fill's payload fact and the cell's coupling antecedent agree).
------------------------------------------------------------------------

-- the wire payload carries a BlockFetch `MsgBlock`
PlIsBlk : Payload → Set
PlIsBlk pl = CellHasBlk (SM.full pl)
  where import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA as SM

------------------------------------------------------------------------
-- THE WITNESS: a BLOCK-carrying cell FILL forces the sending BF server to have
-- been at `bsBlk1` — enabledness on the abstract server table `Tbfs`.
------------------------------------------------------------------------

-- firing the cell-filling io `input _ _ N2N_BlockFetch ! pl` out of a BF server
-- at source phase `bfs`, with a BLOCK payload, forces `BFsHasBlk bfs`
blockFill-forces-srv :
    (l : Link) (d : Dir) (bfs : BFsPos)
    {l′ : Link} {d′ : Dir} {pl : Payload} {M : NetProc}
  → absBFs l d bfs ─[ ev (evl (evLabel Payload (input l′ d′ N2N_BlockFetch) pl)) ]─► M
  → PlIsBlk pl
  → BFsHasBlk bfs
-- the ONLY has-block position: `BFsHasBlk (bsBlk1 b) = ⊤`
blockFill-forces-srv l d (bsBlk1 b) step blk = tt
-- the three OTHER wire-send positions DO fire this io, but never with a block
blockFill-forces-srv l d bsStart1 {l′} {d′} {pl} step blk
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs bsStart1) step
... | q′ , ceq , _ with l′ ≟ l | d′ ≟ d
...   | no  _    | _     = ⊥-elim (nothing-absurd ceq)
...   | yes refl | no  _ = ⊥-elim (nothing-absurd ceq)
...   | yes refl | yes refl
      with pl ≟ (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch)
...     | no  _    = ⊥-elim (nothing-absurd ceq)
...     | yes peq  = ⊥-elim (subst PlIsBlk peq blk)
blockFill-forces-srv l d bsNoBlk1 {l′} {d′} {pl} step blk
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs bsNoBlk1) step
... | q′ , ceq , _ with l′ ≟ l | d′ ≟ d
...   | no  _    | _     = ⊥-elim (nothing-absurd ceq)
...   | yes refl | no  _ = ⊥-elim (nothing-absurd ceq)
...   | yes refl | yes refl
      with pl ≟ (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks)
...     | no  _    = ⊥-elim (nothing-absurd ceq)
...     | yes peq  = ⊥-elim (subst PlIsBlk peq blk)
blockFill-forces-srv l d bsBatchDone1 {l′} {d′} {pl} step blk
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs bsBatchDone1) step
... | q′ , ceq , _ with l′ ≟ l | d′ ≟ d
...   | no  _    | _     = ⊥-elim (nothing-absurd ceq)
...   | yes refl | no  _ = ⊥-elim (nothing-absurd ceq)
...   | yes refl | yes refl
      with pl ≟ (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone)
...     | no  _    = ⊥-elim (nothing-absurd ceq)
...     | yes peq  = ⊥-elim (subst PlIsBlk peq blk)
-- every remaining position offers NO io on the BlockFetch input channel
blockFill-forces-srv l d (bsHead BF.stIdle) step blk
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , _ = ⊥-elim (nothing-absurd ceq)
blockFill-forces-srv l d (bsHead BF.stBusy) step blk
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stBusy)) step
... | q′ , ceq , _ = ⊥-elim (nothing-absurd ceq)
blockFill-forces-srv l d (bsHead BF.stStreaming) step blk
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stStreaming)) step
... | q′ , ceq , _ = ⊥-elim (nothing-absurd ceq)
blockFill-forces-srv l d (bsHead BF.stDone) step blk
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stDone)) step
... | q′ , ceq , _ = ⊥-elim (nothing-absurd ceq)
blockFill-forces-srv l d (bsReq1 r) step blk
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsReq1 r)) step
... | q′ , ceq , _ = ⊥-elim (nothing-absurd ceq)
blockFill-forces-srv l d bsDone1 step blk
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs bsDone1) step
... | q′ , ceq , _ = ⊥-elim (nothing-absurd ceq)
blockFill-forces-srv l d (bsSil BF.stIdle) step blk
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stIdle)) step
... | q′ , ceq , _ = ⊥-elim (nothing-absurd ceq)
blockFill-forces-srv l d (bsSil BF.stBusy) step blk
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stBusy)) step
... | q′ , ceq , _ = ⊥-elim (nothing-absurd ceq)
blockFill-forces-srv l d (bsSil BF.stStreaming) step blk
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stStreaming)) step
... | q′ , ceq , _ = ⊥-elim (nothing-absurd ceq)
blockFill-forces-srv l d (bsSil BF.stDone) step blk
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stDone)) step
... | q′ , ceq , _ = ⊥-elim (nothing-absurd ceq)

------------------------------------------------------------------------
-- The two per-leg BRIDGES: the block-fill witness composed with the server
-- coupling.  These are exactly the two io-source facts `PipeIoHandoff`'s
-- `pipeInv⁺-up-fill` / `-dn-fill` take as their premise.
------------------------------------------------------------------------

-- the leg's UPSTREAM sending link (node A → relay)
upLink : TwoLegs → Link
upLink legBD = linkAB
upLink legCD = linkAC

-- the leg's DOWNSTREAM sending link (relay → node D)
dnLink : TwoLegs → Link
dnLink legBD = linkBD
dnLink legCD = linkCD

-- a BLOCK fill of the leg's UPSTREAM cell by the leg's OWN upstream server
-- forces the producer to have SENT
fill-up-source : (l : TwoLegs) (s : SysState)
    {l′ : Link} {d′ : Dir} {pl : Payload} {M : NetProc}
  → absBFs (upLink l) hi (upSrv l s)
      ─[ ev (evl (evLabel Payload (input l′ d′ N2N_BlockFetch) pl)) ]─► M
  → PlIsBlk pl → SrvCoupled l s → ProdSent (prodOf l s)
fill-up-source l s step blk (uc , _) =
  uc (blockFill-forces-srv (upLink l) hi (upSrv l s) step blk)

-- a BLOCK fill of the leg's DOWNSTREAM cell by the leg's OWN downstream server
-- forces the relay to have FORWARDED
fill-dn-source : (l : TwoLegs) (s : SysState)
    {l′ : Link} {d′ : Dir} {pl : Payload} {M : NetProc}
  → absBFs (dnLink l) hi (dnSrv l s)
      ─[ ev (evl (evLabel Payload (input l′ d′ N2N_BlockFetch) pl)) ]─► M
  → PlIsBlk pl → SrvCoupled l s → RelayFwd (relayOf l s)
fill-dn-source l s step blk (_ , dc) =
  dc (blockFill-forces-srv (dnLink l) hi (dnSrv l s) step blk)
