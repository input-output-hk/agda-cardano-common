{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the receive-coupling SOURCE-PHASE witness
-- (`Praos.PipeRecvSource`).
--
-- `PipeEvDriver.pres-relay`/`pres-cons` isolate the two `recvBFBlock`
-- receive-boundary crossings behind the guarded hypotheses `wUp`/`wDn` :
-- "the receiving driver's local BF CLIENT peer HELD the block (`BFcHasBlk`,
-- i.e. was at `bcBlk1`) at the moment it fired `recvBFBlock`".
--
-- THIS module discharges the NODE-LOCAL half of that obligation: it shows the
-- source phase is FORCED by the event's ENABLEDNESS.  A BF client offers the
-- api event `apiBFev … recvBFBlock` at EXACTLY ONE phase — `bcBlk1 b`
-- (`SysNode.decBFc-src`; the abstract table `Tbfc` gives `nxt … recvBFBlock`
-- as `just` only at `bcAblk`).  So a fired `recvBFBlock` transition out of a BF
-- client at source phase `bfc` (`absBFc l d bfc`) forces `BFcHasBlk bfc`: every
-- other phase is refuted by the SAME `nothing-absurd` inversion the R2 core
-- `decBFc-ev-prod-abs` already uses — and `bfc` is a CONCRETE parameter of that
-- inversion (NOT an opaque successor `nd′`), so the source phase is directly
-- pattern-available.  The `recvBFBlock`-only offer inversion therefore gives
-- `wUp`/`wDn`'s `BFcHasBlk (upClient/dnClient l s)` for free, once the api node
-- cone identifies the fired client with leg-`l`'s upstream/downstream client.
--
-- LIGHT (a single offer-inversion case split; imports only the R2 BF-client
-- table machinery + `PipeInv.BFcHasBlk`).  No postulate/hole/meta.  Base
-- modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Product using ( Σ; _×_; _,_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeRecvSource (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Link; recvBFBlock )
open import CSP.Examples.Cardano_network.NetworkPar p using ( ιBF )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using ( Dir )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )

import CSP.Examples.Cardano_network.BlockFetch p as BF

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode blkA using
  ( BFcPos; bcHead; bcReq1; bcDone1; bcBlk1; bcSil )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep blkA using
  ( NetProc; absBFc; coarsenBFc )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_NodeTauEv blkA using
  ( tableSpec-ev-inv; nothing-absurd )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysIoLink5 blkA using ( Tbfc )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeInv blkA using ( BFcHasBlk )

------------------------------------------------------------------------
-- The witness: a `recvBFBlock` fire out of a BF client at source phase `bfc`
-- FORCES `BFcHasBlk bfc` (the client held the block).  Enabledness — the api
-- `recvBFBlock` offer exists only at `bcBlk1`; every other source phase refutes.
------------------------------------------------------------------------

-- firing `apiBFev … recvBFBlock` from `absBFc l d bfc` forces the source phase
-- to be `bcBlk1` (`BFcHasBlk bfc`)
recvBFBlock-forces-src :
    (l : Link) (d : Dir) (bfc : BFcPos)
    {l′ : Link} {d′ : Dir} {a : _} {M : NetProc}
  → absBFc l d bfc ─[ ev (evl (evLabel _ (ιBF (BF.apiBFev l′ d′ recvBFBlock)) a)) ]─► M
  → BFcHasBlk bfc
-- the ONLY has-block phase: the offer succeeds, and `BFcHasBlk (bcBlk1 b) = ⊤`
recvBFBlock-forces-src l d (bcBlk1 b) step = tt
-- every other phase: the abstract table `nxt` at `recvBFBlock` is `nothing`
recvBFBlock-forces-src l d (bcHead BF.stIdle) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
recvBFBlock-forces-src l d (bcHead BF.stBusy) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
recvBFBlock-forces-src l d (bcHead BF.stStreaming) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
recvBFBlock-forces-src l d (bcHead BF.stDone) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
recvBFBlock-forces-src l d (bcReq1 r) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
recvBFBlock-forces-src l d bcDone1 step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc bcDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
recvBFBlock-forces-src l d (bcSil BF.stIdle) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
recvBFBlock-forces-src l d (bcSil BF.stBusy) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
recvBFBlock-forces-src l d (bcSil BF.stStreaming) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
recvBFBlock-forces-src l d (bcSil BF.stDone) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
