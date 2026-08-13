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
-- SESSION-34: `blockLiveness⁺` is UNCONDITIONAL — NO premise module remains.
-- All three former scaffold premises are discharged: `tprog` (`TProg`, the
-- one sanctioned `dne`), `pcone` (SESSION-33, `PipeLocate.locate`), and
-- `wprog` (SESSION-34, the break-liveness walk: on a confined trace the
-- protected group's links never break, and an unbroken link's `△ break`
-- offer refutes every terminal frame — `WalkBrkFire`/`WalkBrkLift`/
-- `WalkUnbLocate`/`WalkDeliverB`/`WalkEngineB`).
--
-- 0 postulate/hole/meta.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( Block₃ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Spec
  using ( BlockLiveness⁺ )

-- the per-`blkA` proof, imported UNAPPLIED so its parameter is bound by the
-- ∀-closure below
import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.BlockLivenessProof as BLP

module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.BlockLiveness where

------------------------------------------------------------------------
-- THE ∀-CLOSURE — `BlockLiveness⁺`, UNCONDITIONAL.
------------------------------------------------------------------------

-- R3/R4 HEADLINE at FULL generality: A may be configured to produce ANY
-- block; the per-`blkA` proof is `Praos.BlockLivenessProof blkA`
blockLiveness⁺ : BlockLiveness⁺
blockLiveness⁺ blkA = BLP.blockLiveness⁺ blkA
