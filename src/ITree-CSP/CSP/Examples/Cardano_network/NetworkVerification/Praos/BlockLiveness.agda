{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — THE UNPARAMETERISED ENDPOINT: `BlockLiveness⁺`
-- (`Praos.BlockLiveness`).
--
-- Every module under `Praos/` is a `(blkA : Block₃)`-parameterised module,
-- so `Praos.BlockLivenessProof blkA` proves the headline only AT that one
-- produced block: `blockLiveness⁺ : BlockLiveness⁺At blkA`.
--
-- This module closes the outer quantifier.  It is UNPARAMETERISED: it binds
-- `blkA` universally inside a closed statement and hands out
--
--   blockLiveness⁺ : BlockLiveness⁺
--                  = ∀ (blkA : Block₃) → BlockLiveness⁺At blkA
--
-- i.e. node A may be configured to produce ANY block, and for EVERY block `b`
-- a `producedA b` on a confined trace is followed by `arrivedD b`.
--
-- The two scaffold premises `wprog` (weak progress / enabledness) and `pcone`
-- (pending causal cone) are UNCHANGED — they are simply re-stated with a
-- leading `∀ (blkA : Block₃)`, which is exactly what the ∀-closure needs.
-- `tprog` is already discharged upstream (`Praos.TProg`, via the one
-- sanctioned `dne`).
--
-- 0 postulate/hole/meta.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤ )
open import Relation.Binary.PropositionalEquality using ( _≡_ )

open import Process_Trees using ( ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; Block₃ )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamondLiveness
  using ( producedA; BlockLiveness⁺ )

open import Semantics.LTL.WTrace
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( WTrace; frameOf )
open import Semantics.LTL.Fairness
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( WEnabled )

-- the `Praos` modules are imported UNAPPLIED, so their `blkA` parameter
-- shows up as an explicit first argument and can be bound by the `∀ blkA`
-- of the premises below
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysReach as SR
import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkPr as WP
import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkEnabled as WE
import CSP.Examples.Cardano_network.NetworkVerification.Praos.BlockLivenessProof as BLP

module CSP.Examples.Cardano_network.NetworkVerification.Praos.BlockLiveness where

------------------------------------------------------------------------
-- THE ∀-CLOSURE — `BlockLiveness⁺` modulo the ONE remaining scaffold premise,
-- itself universally quantified over A's produced block.  (`pcone`, the
-- pipeline-provenance premise, was DISCHARGED in SESSION-33 and is gone.)
------------------------------------------------------------------------

module _
  (wprog : ∀ (blkA : Block₃) (b : Block₃) (r : SR.RState blkA)
         → WP.Pr blkA b r
         → WEnabled (WE.IntactApiClass blkA b) (SR.radec blkA r))
  where

  -- R3/R4 HEADLINE at FULL generality: A may be configured to produce ANY
  -- block; the per-`blkA` proof is `Praos.BlockLivenessProof blkA`
  blockLiveness⁺ : BlockLiveness⁺
  blockLiveness⁺ blkA = BLP.blockLiveness⁺ blkA (wprog blkA)
