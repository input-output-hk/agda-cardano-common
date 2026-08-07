{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the WALK ASSEMBLY (`Praos.AbstractLive`).
--
-- Instantiates `WalkEngine.walkPosFrom` with the four now-green ingredients
--   · the whole-trace measure `Walk.μTot`,
--   · the leg-tagged pending invariant `WalkPr.Pr`,
--   · the total per-step reflector `WalkDeliver.deliver`, and
--   · the start-reachability `WalkLocate.locate`
-- to obtain the positive walk `walkPos`, then feeds it to `Walk.abstractLive`
-- to obtain the R3 target
--
--   abstractLive : ∀ b → abstractSystem ⊨ᵂ respondsAtoD b.
--
-- The two heavy per-state hypotheses are carried here as the MODULE PREMISES
-- `wprog` (the weak-progress / enabledness premise `WalkDeliver` consumes) and
-- `pcone` (the pending causal-cone premise `WalkLocate` consumes) — scaffolding
-- discharged in a later endgame (A′ for `wprog`, the oracle-scale pipeline
-- provenance cone for `pcone`).  Everything else is discharged here, green,
-- 0-postulate/hole/meta.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤ )
open import Data.Nat using ( ℕ )
open import Data.Product using ( Σ; Σ-syntax; _,_; _×_ )
open import Data.Sum using ( _⊎_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.AbstractLive (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; Block₃ )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysReach blkA
  using ( NetProc; RState; radec; toSys )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.AbstractSystem blkA
  using ( abstractSystem )

open import Semantics.LTL.Traces_Based
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( atom; ¬_; F_ )
open import Semantics.LTL.WTrace
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( WTrace; ⟦_⟧ᵂ; drop; dropIdx; frameOf; _⊨ᵂ_ )
open import Semantics.LTL.Fairness
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( WEnabled )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamondLiveness
  using ( producedA; arrivedD; brkG1; brkG2; respondsAtoD )

import CSP.Examples.Cardano_network.NetworkVerification.Praos.Walk blkA as W
open W
  using ( μTot; G⁺ᵂ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkEngine blkA
  using ( walkPosFrom )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkPr blkA
  using ( Pr )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkEnabled blkA
  using ( IntactApiClass )
import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkDeliver blkA as WD
-- SESSION-33: `pcone` is DISCHARGED — `locate` now comes from the constructive
-- pipeline walk (`PipeLocate`), not from `WalkLocate`'s premise module.
import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeLocate blkA as PL

------------------------------------------------------------------------
-- The ONE remaining scaffold premise, carried EXACTLY as `WalkDeliver` takes
-- it.  (`pcone` was the second; SESSION-33 discharged it — `PipeLocate.locate`
-- inhabits `WalkLocate.locate`'s type constructively, from the product
-- pipeline walk `PipeInvProd.pipeInvS-along-walk′` + the τ-run producer
-- fixity (E1) + the producer-offer `pp5` inversion (E2) + `pipeInvS⇒Pr`.)
------------------------------------------------------------------------

module _
  (wprog : (b : Block₃) (r : RState) → Pr b r → WEnabled (IntactApiClass b) (radec r))
  where

  ------------------------------------------------------------------------
  -- The positive walk (the `walkPosFrom` instance).
  ------------------------------------------------------------------------

  walkPos : (b : Block₃) (tr : WTrace (⊤ {0ℓ}) abstractSystem)
          → (G⁺ᵂ (¬ atom brkG1) tr ⊎ G⁺ᵂ (¬ atom brkG2) tr)
          → ∀ n → ⟦ atom (producedA b) ⟧ᵂ (drop n tr)
          → ⟦ F_ (atom (arrivedD b)) ⟧ᵂ (drop n tr)
  walkPos = walkPosFrom μTot Pr (λ b → WD.deliver b (wprog b)) PL.locate

  ------------------------------------------------------------------------
  -- R3 TARGET: the abstract system classically satisfies `respondsAtoD`.
  ------------------------------------------------------------------------

  abstractLive : (b : Block₃) → abstractSystem ⊨ᵂ respondsAtoD b
  abstractLive = W.abstractLive walkPos
