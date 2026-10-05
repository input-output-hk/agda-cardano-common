{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the non-`recvBFBlock` consume SUCCESSOR-PHASE witness
-- (`Praos.PipeConsumeSource`).  DUAL of `PipeRecvSource`.
--
-- The `-move` boundary of `PipeEvDriver.pres-relay`/`pres-cons` — the TWO
-- visible BF-client consume moves `sendBFRequestRange` (`cp2→cp3`) and
-- `sendBFClientDone` (`cp4→cp5`), which the relay's / consumer's OWN BF client
-- fires WITH the driver — needs the SUCCESSOR-non-block premise
-- `¬ BFcHasBlk (upClient/dnClient l s′)`.  THIS leaf discharges the node-local
-- half by ENABLEDNESS: a `sendBFRequestRange` / `sendBFClientDone` fire out of a
-- BF client (offered ONLY at `bcHead stIdle` / `bcSil stIdle`, i.e. the abstract
-- `bcIdle` head) lands at `bcReq1` / `bcDone1` respectively — both ¬-block
-- (`BFcHasBlk = ⊥`).  Every other source phase is refuted by the same
-- `nothing-absurd` offer inversion the R2 core `decBFc-ev-prod-abs` uses.
--
-- Mirror of `recvBFBlock-forces-src` (source-phase) and the two enabled cases of
-- `SysIoLink5.bfc-hstep` (successor decode), but with the `¬ BFcHasBlk`
-- conclusion the `-move` gate consumes.
--
-- LIGHT (one offer-inversion case split per event).  No postulate/hole/meta.
-- Base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_ )
open import Data.Maybe using ( just; nothing )
open import Data.Maybe.Properties using ( just-injective )
open import Relation.Nullary using ( yes; no )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Archive.PipeConsumeSource (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p
open import CSP.Examples.Cardano_network.Base
open import CSP.Examples.Cardano_network.Data p
open import CSP.Examples.Cardano_network.Net p using
  ( Net_Api; Link; sendBFRequestRange; sendBFClientDone )
open import Class.DecEq using ( _≟_ )
import Class.DecEq.Instances as DecEqI

open import CSP.Examples.Cardano_network.NetworkPar p using ( ιBF )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )

import CSP.Examples.Cardano_network.BlockFetch p as BF

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA using
  ( BFcPos; bcHead; bcReq1; bcDone1; bcBlk1; bcSil )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA using
  ( NetProc; absBFc; coarsenBFc )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA using
  ( tableSpec-ev-inv; nothing-absurd )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink5 blkA using
  ( Tbfc; mkMbfc )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA using
  ( BFcHasBlk )

------------------------------------------------------------------------
-- `sendBFRequestRange` fire: lands at `bcReq1 a` (¬-block).
------------------------------------------------------------------------

-- firing `apiBFev … sendBFRequestRange` from `absBFc l d bfc` lands at a
-- successor `bfc′` with `M ≡ absBFc l d bfc′` and `¬ BFcHasBlk bfc′`
sendBFRequestRange-nonBlock :
    (l : Link) (d : Dir) (bfc : BFcPos)
    {l′ : Link} {d′ : Dir} {a : _} {M : NetProc}
  → absBFc l d bfc ─[ ev (evl (evLabel _ (ιBF (BF.apiBFev l′ d′ sendBFRequestRange)) a)) ]─► M
  → Σ[ bfc′ ∈ BFcPos ] (M ≡ absBFc l d bfc′) × (BFcHasBlk bfc′ → ⊥)
-- the ONLY enabled source: the idle head — lands at `bcReq1 a`
sendBFRequestRange-nonBlock l d (bcHead BF.stIdle) {l′} {d′} {a} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl = bcReq1 a , mkMbfc l d (bcReq1 a) Meq (just-injective (sym ceq)) , λ ()
...   | yes refl | no _  = ⊥-elim (nothing-absurd ceq)
...   | no _     | _     = ⊥-elim (nothing-absurd ceq)
sendBFRequestRange-nonBlock l d (bcSil BF.stIdle) {l′} {d′} {a} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stIdle)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl = bcReq1 a , mkMbfc l d (bcReq1 a) Meq (just-injective (sym ceq)) , λ ()
...   | yes refl | no _  = ⊥-elim (nothing-absurd ceq)
...   | no _     | _     = ⊥-elim (nothing-absurd ceq)
-- every other source: the abstract `nxt` at `sendBFRequestRange` is `nothing`
sendBFRequestRange-nonBlock l d (bcHead BF.stBusy) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
sendBFRequestRange-nonBlock l d (bcHead BF.stStreaming) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
sendBFRequestRange-nonBlock l d (bcHead BF.stDone) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
sendBFRequestRange-nonBlock l d (bcReq1 r) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
sendBFRequestRange-nonBlock l d bcDone1 step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc bcDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
sendBFRequestRange-nonBlock l d (bcBlk1 b) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
sendBFRequestRange-nonBlock l d (bcSil BF.stBusy) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
sendBFRequestRange-nonBlock l d (bcSil BF.stStreaming) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
sendBFRequestRange-nonBlock l d (bcSil BF.stDone) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

------------------------------------------------------------------------
-- `sendBFClientDone` fire: lands at `bcDone1` (¬-block).
------------------------------------------------------------------------

-- firing `apiBFev … sendBFClientDone` from `absBFc l d bfc` lands at a successor
-- `bfc′` with `M ≡ absBFc l d bfc′` and `¬ BFcHasBlk bfc′`
sendBFClientDone-nonBlock :
    (l : Link) (d : Dir) (bfc : BFcPos)
    {l′ : Link} {d′ : Dir} {a : _} {M : NetProc}
  → absBFc l d bfc ─[ ev (evl (evLabel _ (ιBF (BF.apiBFev l′ d′ sendBFClientDone)) a)) ]─► M
  → Σ[ bfc′ ∈ BFcPos ] (M ≡ absBFc l d bfc′) × (BFcHasBlk bfc′ → ⊥)
-- the ONLY enabled source: the idle head — lands at `bcDone1`
sendBFClientDone-nonBlock l d (bcHead BF.stIdle) {l′} {d′} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl = bcDone1 , mkMbfc l d bcDone1 Meq (just-injective (sym ceq)) , λ ()
...   | yes refl | no _  = ⊥-elim (nothing-absurd ceq)
...   | no _     | _     = ⊥-elim (nothing-absurd ceq)
sendBFClientDone-nonBlock l d (bcSil BF.stIdle) {l′} {d′} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stIdle)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl = bcDone1 , mkMbfc l d bcDone1 Meq (just-injective (sym ceq)) , λ ()
...   | yes refl | no _  = ⊥-elim (nothing-absurd ceq)
...   | no _     | _     = ⊥-elim (nothing-absurd ceq)
-- every other source: the abstract `nxt` at `sendBFClientDone` is `nothing`
sendBFClientDone-nonBlock l d (bcHead BF.stBusy) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
sendBFClientDone-nonBlock l d (bcHead BF.stStreaming) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
sendBFClientDone-nonBlock l d (bcHead BF.stDone) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
sendBFClientDone-nonBlock l d (bcReq1 r) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
sendBFClientDone-nonBlock l d bcDone1 step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc bcDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
sendBFClientDone-nonBlock l d (bcBlk1 b) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
sendBFClientDone-nonBlock l d (bcSil BF.stBusy) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
sendBFClientDone-nonBlock l d (bcSil BF.stStreaming) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
sendBFClientDone-nonBlock l d (bcSil BF.stDone) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
