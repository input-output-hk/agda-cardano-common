{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the AMBUSH CHECK for the strengthened `arrivedD`
-- (`Praos.PipeValArrived`), SESSION-36 step (vi) pre-flight.
--
-- `BlockLivenessProof.arrivedD-BS : ∀ b → BisimStable (atom (arrivedD b))` is
-- the third argument of the ≈DR transport, and it must be RE-PROVED once
-- `arrivedD` regains its `a ≡ b` conjunct.  Editing
-- `FourNodeDiamondLiveness.lagda.md` to find that out costs a ~9-30 min
-- closure rebuild, so the check is done HERE, against a VERBATIM LOCAL COPY of
-- the strengthened predicate — the `PipeCellFalse` method, used positively.
--
-- VERDICT: **NO AMBUSH.**  `bs-atom stab` goes through with the SAME proof
-- term, `q = q`.  The reason is structural: `FrameSim` between two `step`
-- frames carries a `refl` identifying the WHOLE observation `evLabel X e a` —
-- carrier, event AND carried value — so the two frames' `arrivedD⁺ b` types are
-- literally the same type.  Any frame predicate that reads only the event
-- transports, whatever it says about the carried value.  (`producedA` already
-- HAS the value conjunct and its `producedA-BS` is the same one-liner, which is
-- the independent confirmation.)
--
-- `arrivedD⁺` below is the strengthened predicate exactly as it will read in
-- `FourNodeDiamondLiveness` — it is a local copy, so this module stays green
-- both before and after that edit lands.
--
-- Imported by nothing (a gate leaf).  No postulate/hole/meta.  Base modules
-- READ-ONLY — in particular `FourNodeDiamondLiveness` is NOT touched here.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤ )
open import Data.Empty using ( ⊥ )
open import Data.Product using ( _×_; _,_ )
open import Data.Sum using ( _⊎_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Evidence.PipeValArrived (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; Block₃; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Base using ( hi )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; apiBF; recvBFBlock )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( evl; evLabel )
open import Semantics.LTL.Traces_Based
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( Frame; FramePred; atom )
open import Semantics.LTL.FrameSim
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( FrameSim; BisimStable; bs-atom )

------------------------------------------------------------------------
-- The STRENGTHENED atom, verbatim as it will read in
-- `FourNodeDiamondLiveness` — `arrivedD` with the `a ≡ b` conjunct restored,
-- so that it matches `producedA`'s shape exactly.
------------------------------------------------------------------------

-- D's BF client receives THE block `b`: apiBF recvBFBlock at hi on BD or CD,
-- carrying `b` itself (the session-35/36 target predicate)
arrivedD⁺ : Block₃ → FramePred 0ℓ (⊤ {0ℓ})
arrivedD⁺ b (Frame.step _ (evl (evLabel _ (apiBF l d recvBFBlock) a))) =
  ((l ≡ linkBD) ⊎ (l ≡ linkCD)) × (d ≡ hi) × (a ≡ b)
arrivedD⁺ _ _ = ⊥

------------------------------------------------------------------------
-- THE CHECK.  The bisim-stability proof is UNCHANGED — same `bs-atom stab`,
-- same `q = q` body — because `FrameSim`'s head `refl` identifies the whole
-- observation, value included.
------------------------------------------------------------------------

-- the strengthened `arrivedD` is still bisim-stable, by the SAME proof term
arrivedD⁺-BS : ∀ b → BisimStable (atom (arrivedD⁺ b))
arrivedD⁺-BS b = bs-atom stab
  where
    stab : ∀ {fr₁ fr₂ : Frame (⊤ {0ℓ})}
         → FrameSim fr₁ fr₂ → arrivedD⁺ b fr₁ → arrivedD⁺ b fr₂
    stab {Frame.step _ (evl (evLabel _ (apiBF l d recvBFBlock) a))}
         {Frame.step _ _} (refl , _) q = q
