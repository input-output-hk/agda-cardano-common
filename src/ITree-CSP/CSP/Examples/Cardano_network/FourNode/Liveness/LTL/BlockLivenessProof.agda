{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — THE END-TO-END SPINE: `BlockLiveness⁺`
-- (`Praos.BlockLivenessProof`).
--
-- Assembles the R4 transport seam that turns the abstract-system liveness
-- walk into the concrete `systemBroken` headline:
--
--   abstractLive  : ∀ b → abstractSystem ⊨ᵂ respondsAtoD b   (AbstractLive)
--   sysBisim      : systemBroken ≈DR abstractSystem          (SysBisim, R2)
--   realAbs       : Realisableᴿ abstractSystem               (RealAbs, mod tprog)
--   ────────────────────────────────────────────────── ⊨-DRWB-invariantᴿ→
--   systemBroken ⊨ᵂ respondsAtoD b
--   ────────────────────────────────────────────────── ⊨ᵂ⇒⊨ (TraceBridge)
--   systemBroken ⊨ respondsAtoD b
--   ────────────────────────────────────────────────── descent-⊨ (ClassicalDescent)
--   BlockLiveness⁺
--
-- `⊨-DRWB-invariantᴿ→` transports FROM `t₁ = abstractSystem` (whence
-- `Realisableᴿ abstractSystem` on the SOURCE side) TO `t₂ = systemBroken`, so
-- the bisim argument is `drbisim-sym sysBisim : abstractSystem ≈DR
-- systemBroken`.  `respondsAtoD-BS` (the `BisimStable` certificate, reproduced
-- below) is the third argument.
--
-- The result is `BlockLiveness⁺` GREEN with NO scaffold premise: `wprog`
-- (SESSION-34, break-liveness walk), `pcone` (SESSION-33, `PipeLocate`) and
-- `tprog` (`TProg`, the one sanctioned `dne`) are all discharged.
-- `arrivedD` is payload-agnostic on this branch (the sanctioned `a≡b`-drop).
-- 0 postulate/hole/meta; the ONE sanctioned `dne` lives upstream in
-- `respondsᵂ-intro`/`descent-⊨`, none is added here.
------------------------------------------------------------------------

open import Level using ( 0ℓ; Level )
open import Data.Unit.Polymorphic using ( ⊤ )
open import Data.Nat using ( ℕ )
open import Data.Sum using ( _⊎_ )
open import Data.Product using ( _×_; _,_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.BlockLivenessProof (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; Block₃ )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; apiBF; break; sendBFBlock; recvBFBlock )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( evl; evLabel )
open import Semantics.DRBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( drbisim-sym )

open import Semantics.LTL.Traces_Based
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( Frame; FramePred; LTLᵗ; atom; ¬_; _∧_; X_; _U_; _∨_; _⇒_; F_; G_ )
open import Semantics.LTL.FrameSim
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( FrameSim; BisimStable; bs-⊤; bs-atom; bs-¬; bs-∧; bs-X; bs-U )
open import Semantics.LTL.WBisimInvariantR
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( ⊨-DRWB-invariantᴿ→ )
open import Semantics.LTL.TraceBridge
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( ⊨ᵂ⇒⊨ )
open import Semantics.LTL.ClassicalDescent
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( descent-⊨ )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamondBroken
  using ( systemBroken )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Spec
  using ( producedA; arrivedD; brkG1; brkG2; confined; respondsAtoD; BlockLiveness⁺At )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.AbstractSystem blkA
  using ( abstractSystem )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysBisim blkA
  using ( sysBisim )

open import Semantics.LTL.WTrace
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( WTrace; frameOf; _⊨ᵂ_ )

import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.RealAbs blkA as RA
import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.AbstractLive blkA as AL
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.TProg blkA
  using ( tprog )

------------------------------------------------------------------------
-- `BisimStable (respondsAtoD b)` — the third argument of the transport.
-- Every liveness atom inspects only the frame's EVENT (never the state slot),
-- so a `FrameSim` (which forces the events equal) transports it by `refl`;
-- `BisimStable` then lifts through the derived operators.  (Self-contained
-- reproduction — the `LivenessSpike` harvest runs `--allow-unsolved-metas`.)
------------------------------------------------------------------------

-- `producedA` is bisim-stable (reads only the `apiBF … sendBFBlock` event)
producedA-BS : ∀ b → BisimStable (atom (producedA b))
producedA-BS b = bs-atom stab
  where
    stab : ∀ {fr₁ fr₂ : Frame (⊤ {0ℓ})}
         → FrameSim fr₁ fr₂ → producedA b fr₁ → producedA b fr₂
    stab {Frame.step _ (evl (evLabel _ (apiBF l d sendBFBlock) a))}
         {Frame.step _ _} (refl , _) q = q

-- `arrivedD` is bisim-stable (reads only the `apiBF … recvBFBlock` event)
arrivedD-BS : ∀ b → BisimStable (atom (arrivedD b))
arrivedD-BS b = bs-atom stab
  where
    stab : ∀ {fr₁ fr₂ : Frame (⊤ {0ℓ})}
         → FrameSim fr₁ fr₂ → arrivedD b fr₁ → arrivedD b fr₂
    stab {Frame.step _ (evl (evLabel _ (apiBF l d recvBFBlock) a))}
         {Frame.step _ _} (refl , _) q = q

-- `brkG1` is bisim-stable (reads only the `break` event)
brkG1-BS : BisimStable (atom brkG1)
brkG1-BS = bs-atom stab
  where
    stab : ∀ {fr₁ fr₂ : Frame (⊤ {0ℓ})}
         → FrameSim fr₁ fr₂ → brkG1 fr₁ → brkG1 fr₂
    stab {Frame.step _ (evl (evLabel _ (break l) _))}
         {Frame.step _ _} (refl , _) q = q

-- `brkG2` is bisim-stable (reads only the `break` event)
brkG2-BS : BisimStable (atom brkG2)
brkG2-BS = bs-atom stab
  where
    stab : ∀ {fr₁ fr₂ : Frame (⊤ {0ℓ})}
         → FrameSim fr₁ fr₂ → brkG2 fr₁ → brkG2 fr₂
    stab {Frame.step _ (evl (evLabel _ (break l) _))}
         {Frame.step _ _} (refl , _) q = q

-- `BisimStable` closure under the derived operators (definitional unfolds)
bs-F : ∀ {ℓa} {φ : LTLᵗ ℓa (⊤ {0ℓ})} → BisimStable φ → BisimStable (F φ)
bs-F bφ = bs-U bs-⊤ bφ

bs-G : ∀ {ℓa} {φ : LTLᵗ ℓa (⊤ {0ℓ})} → BisimStable φ → BisimStable (G φ)
bs-G bφ = bs-¬ (bs-U bs-⊤ (bs-¬ bφ))

bs-∨ : ∀ {ℓa} {φ ψ : LTLᵗ ℓa (⊤ {0ℓ})}
     → BisimStable φ → BisimStable ψ → BisimStable (φ ∨ ψ)
bs-∨ bφ bψ = bs-¬ (bs-∧ (bs-¬ bφ) (bs-¬ bψ))

bs-⇒ : ∀ {ℓa} {φ ψ : LTLᵗ ℓa (⊤ {0ℓ})}
     → BisimStable φ → BisimStable ψ → BisimStable (φ ⇒ ψ)
bs-⇒ bφ bψ = bs-∨ (bs-¬ bφ) bψ

-- `confined = G(¬ brkG1) ∨ G(¬ brkG2)` is bisim-stable
confined-BS : BisimStable confined
confined-BS = bs-∨ (bs-G (bs-¬ brkG1-BS)) (bs-G (bs-¬ brkG2-BS))

-- CAPSTONE: the whole `respondsAtoD b` formula is bisim-stable
respondsAtoD-BS : ∀ b → BisimStable (respondsAtoD b)
respondsAtoD-BS b =
  bs-⇒ confined-BS
       (bs-G (bs-⇒ (producedA-BS b) (bs-F (arrivedD-BS b))))

------------------------------------------------------------------------
-- THE SPINE — `BlockLiveness⁺`, PREMISE-FREE.  (`wprog` was discharged in
-- SESSION-34 — `AbstractLive` now runs the break-liveness walk from
-- `WalkEngineB`/`WalkDeliverB`/`WalkUnbLocate`; `pcone` went in SESSION-33
-- via `PipeLocate.locate`; `tprog` is `Praos.TProg` via the one sanctioned
-- `dne`.)
------------------------------------------------------------------------

-- systemBroken ⊨ᵂ respondsAtoD b — the ≈DR transport of the abstract walk
broken-⊨ᵂ : (b : Block₃) → systemBroken blkA ⊨ᵂ respondsAtoD b
broken-⊨ᵂ b =
  ⊨-DRWB-invariantᴿ→ (RA.realAbs tprog) (drbisim-sym sysBisim)
    (respondsAtoD-BS b) (AL.abstractLive b)

-- R3/R4 HEADLINE: the broken diamond's positive block-liveness AT this
-- module's produced block `blkA` (the ∀-closure over `blkA` is
-- `BlockLiveness⁺`, discharged by the unparameterised endpoint module)
blockLiveness⁺ : BlockLiveness⁺At blkA
blockLiveness⁺ b =
  descent-⊨ {ψ₁ = ¬ atom brkG1} {ψ₂ = ¬ atom brkG2}
            {p = atom (producedA b)} {q = atom (arrivedD b)}
            (⊨ᵂ⇒⊨ {φ = respondsAtoD b} (broken-⊨ᵂ b))
