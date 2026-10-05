{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the PENDING invariant `Pr` and its PRESERVATION
-- (`Praos.WalkPr`).
--
-- `deliver`'s successor branch needs a "still-pending" invariant preserved
-- across every non-delivering step.  `Pr b r` is LEG-TAGGED single-pending:
-- SOME specific D-consumer leg (`legBD` = `cons-BD`, or `legCD` = `cons-CD`)
-- is still pre-`recvBFBlock` (`cp0..cp3`).  This REPLACES the earlier
-- CONJUNCTION (both consumers pending), which was UNSOUND — the two delivery
-- legs are independent, so a reachable `confined` state can have one leg
-- delivered while the other's producer is still offering.  It is block-blind
-- (`b` unread), sound, and preserved across every step EXCEPT when the
-- TRACKED leg makes the delivering `recvBFBlock@D` (`cp3 → cp4` `c34`) hop —
-- which is exactly `arrivedD` on that leg.
--
-- `Pr-step` TRACKS the witnessed leg `c`: it turns a
-- `WalkDExpose.DReport (toSys r)(toSys r′)` into EITHER `Pr b r′` with the
-- SAME leg `c` (a step that does not deliver leg `c`), OR a `DeliverSig`
-- (leg `c` advanced `cp3 → cp4` via `recvBFBlock`, carrying its link
-- `linkOf c ∈ {linkBD,linkCD}`, dir `hi`, received block `b″`, and the pinned
-- label eq).  Pure case analysis on `ConsAdv` under the `cp0..cp3`
-- precondition (the out-of-range `c45`/`c56` are killed by the precondition).
--
-- LIGHT (no SysBisim cone); no postulate/hole/meta.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Product using ( _×_; _,_; Σ; Σ-syntax )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; trans; cong )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; Block₃; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Link; apiBF; recvBFBlock )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using ( hi )
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( evLabel )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; nD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( RState; toSys )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN
  using ( ConsPh; cp0; cp1; cp2; cp3; cp4; cp5; cp6; cph; cblk; cons-BD; cons-CD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkMeasure blkA
  using ( ConsAdv; c01; c12; c23; c34; c45; c56 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkDExpose blkA
  using ( DReport; dFix; dBD; dCD )

-- the D-consume phase of nD on link BD / CD (a `ConsPh`)
phBD : SysState → ConsPh
phBD s = cph (SN.NodeStateD.cons-BD (nD s))
phCD : SysState → ConsPh
phCD s = cph (SN.NodeStateD.cons-CD (nD s))

------------------------------------------------------------------------
-- `InCp03 c` — the phase `c` is pre-`recvBFBlock` (`cp0..cp3`).
------------------------------------------------------------------------

InCp03 : ConsPh → Set
InCp03 cp0 = ⊤
InCp03 cp1 = ⊤
InCp03 cp2 = ⊤
InCp03 cp3 = ⊤
InCp03 cp4 = ⊥
InCp03 cp5 = ⊥
InCp03 cp6 = ⊥

------------------------------------------------------------------------
-- `TwoLegs` — the two independent D-delivery legs.  `phOf`/`linkOf` read a
-- leg's D-consume phase and its BD/CD link.
------------------------------------------------------------------------

-- the two D-consumer legs: `legBD` = `cons-BD`, `legCD` = `cons-CD`
data TwoLegs : Set where
  legBD legCD : TwoLegs

-- the D-consume phase of the leg on a state
phOf : TwoLegs → SysState → ConsPh
phOf legBD = phBD
phOf legCD = phCD

-- the link of a leg
linkOf : TwoLegs → Link
linkOf legBD = linkBD
linkOf legCD = linkCD

------------------------------------------------------------------------
-- The pending invariant: SOME specific D-consumer leg is pre-`recvBFBlock`.
-- Leg-tagged single-pending (NOT the unsound conjunction).  Block-blind (`b`
-- is not read; the block-value is threaded separately).
------------------------------------------------------------------------

Pr : Block₃ → RState → Set
Pr _ r = Σ[ leg ∈ TwoLegs ] InCp03 (phOf leg (toSys r))

------------------------------------------------------------------------
-- `DeliverSig r r′ e a` — the delivering signal for a tracked leg `c`: the
-- fired event is pinned to `apiBF (linkOf c) hi recvBFBlock` (dir `hi`),
-- carrying the received block `b″`, and leg `c` advanced `cp3 → cp4`.  This
-- is everything `deliver` needs to build `arrivedD` for leg `c`.
------------------------------------------------------------------------

-- the block the leg's node-D consume slot has RECORDED (SESSION-36: this is
-- the tie-point the delivering label's `b″` is anchored to)
cblkOf : TwoLegs → SysState → Block₃
cblkOf legBD s = cblk (SN.NodeStateD.cons-BD (nD s))
cblkOf legCD s = cblk (SN.NodeStateD.cons-CD (nD s))

DeliverSig : (r r′ : RState) {X : Set 0ℓ} → Net_Api Payload X → X → Set₁
DeliverSig r r′ {X} e a =
  Σ[ c ∈ TwoLegs ]
    ( phOf c (toSys r) ≡ cp3 × phOf c (toSys r′) ≡ cp4
    × Σ[ b″ ∈ Block₃ ]
        (evLabel X e a ≡ evLabel Block₃ (apiBF (linkOf c) hi recvBFBlock) b″)
      × (cblkOf c (toSys r′) ≡ b″) )

------------------------------------------------------------------------
-- Preservation (tracking the witnessed leg): a `DReport` step either keeps
-- `Pr` with the SAME leg, or is a `DeliverSig` (the tracked leg made the
-- delivering `cp3 → cp4` = `recvBFBlock@D` = `arrivedD` hop).
------------------------------------------------------------------------

-- a single-consumer advance under the `cp0..cp3` precondition stays in
-- `cp0..cp3` OR is the `c34` delivering hop (`cp3 → cp4`)
consAdv-cp03 : {c c′ : ConsPh} → InCp03 c → ConsAdv c c′
             → InCp03 c′ ⊎ (c ≡ cp3 × c′ ≡ cp4)
consAdv-cp03 hc c01 = inj₁ tt
consAdv-cp03 hc c12 = inj₁ tt
consAdv-cp03 hc c23 = inj₁ tt
consAdv-cp03 hc c34 = inj₂ (refl , refl)
consAdv-cp03 () c45
consAdv-cp03 () c56

-- transport `InCp03` back along a fixed `cons-*` field equality
subst-in : {x y : SN.ConsDPh} → x ≡ y → InCp03 (cph y) → InCp03 (cph x)
subst-in refl h = h

Pr-step : (b : Block₃) {r r′ : RState} {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
        → Pr b r → DReport (toSys r) (toSys r′) e a
        → Pr b r′ ⊎ DeliverSig r r′ e a
-- BOTH D-consumers fixed: the tracked leg's phase is unchanged
Pr-step b {r} {r′} (legBD , h) (dFix bfix cfix) = inj₁ (legBD , subst-in bfix h)
Pr-step b {r} {r′} (legCD , h) (dFix bfix cfix) = inj₁ (legCD , subst-in cfix h)
-- D fired on BD: BD advances (case on the TRACKED leg), CD fixed
Pr-step b {r} {r′} (legBD , h) (dBD adv cfix lbl) with consAdv-cp03 h adv
... | inj₁ h′         = inj₁ (legBD , h′)
... | inj₂ (e3 , e4)  = inj₂ (legBD , e3 , e4 , lbl e3)
Pr-step b {r} {r′} (legCD , h) (dBD adv cfix lbl) = inj₁ (legCD , subst-in cfix h)
-- D fired on CD: CD advances (case on the TRACKED leg), BD fixed
Pr-step b {r} {r′} (legCD , h) (dCD adv bfix lbl) with consAdv-cp03 h adv
... | inj₁ h′         = inj₁ (legCD , h′)
... | inj₂ (e3 , e4)  = inj₂ (legCD , e3 , e4 , lbl e3)
Pr-step b {r} {r′} (legBD , h) (dCD adv bfix lbl) = inj₁ (legBD , subst-in bfix h)
