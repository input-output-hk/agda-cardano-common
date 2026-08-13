{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the WALK ASSEMBLY (`Praos.AbstractLive`).
--
-- Feeds `Walk.abstractLive` its ONE remaining slot, the positive walk
-- `walkPos`, to obtain the R3 target
--
--   abstractLive : ∀ b → abstractSystem ⊨ᵂ respondsAtoD b.
--
-- SESSION-34: the LAST scaffold premise `wprog` is DISCHARGED — `walkPos`
-- is now `WalkEngineB.walkPosB`, whose per-side descent runs
-- `WalkDeliverB.deliverB` (terminal frames refuted by the UNBROKEN-LINK
-- break offer carried in `Unb`, not by an enabledness premise) from
-- `WalkUnbLocate.locateU` (`PipeLocate.locate` + the confined-group `Unb`
-- fold, glued by the decode transport).  NO premise module remains.
-- (`pcone` went in SESSION-33 the same way — `PipeLocate.locate` replaced
-- `WalkLocate`'s premise; `tprog` is discharged in `TProg` via the one
-- sanctioned `dne`.)
--
-- 0-postulate/hole/meta.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤ )
open import Data.Nat using ( ℕ )
open import Data.Sum using ( _⊎_ )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.AbstractLive (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; Block₃ )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.AbstractSystem blkA
  using ( abstractSystem )

open import Semantics.LTL.Traces_Based
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( atom; ¬_; F_ )
open import Semantics.LTL.WTrace
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( WTrace; ⟦_⟧ᵂ; drop; _⊨ᵂ_ )

open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Spec
  using ( producedA; arrivedD; brkG1; brkG2; respondsAtoD )

import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.Walk blkA as W
open W using ( G⁺ᵂ )
-- SESSION-34: `wprog` is DISCHARGED — the walk comes premise-free from the
-- side-fixed engine (`WalkEngineB`), which packages `WalkDeliverB.deliverB`
-- and `WalkUnbLocate.locateU`.
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkEngineB blkA
  using ( walkPosB )

------------------------------------------------------------------------
-- The positive walk — UNCONDITIONAL (no scaffold premise).
------------------------------------------------------------------------

-- the premise-free positive walk (the `Walk.walkPos` slot, filled)
walkPos : (b : Block₃) (tr : WTrace (⊤ {0ℓ}) abstractSystem)
        → (G⁺ᵂ (¬ atom brkG1) tr ⊎ G⁺ᵂ (¬ atom brkG2) tr)
        → ∀ n → ⟦ atom (producedA b) ⟧ᵂ (drop n tr)
        → ⟦ F_ (atom (arrivedD b)) ⟧ᵂ (drop n tr)
walkPos = walkPosB

------------------------------------------------------------------------
-- R3 TARGET: the abstract system classically satisfies `respondsAtoD`.
------------------------------------------------------------------------

-- the R3 headline, now premise-free
abstractLive : (b : Block₃) → abstractSystem ⊨ᵂ respondsAtoD b
abstractLive = W.abstractLive walkPos
