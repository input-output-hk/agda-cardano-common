{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- R3 — the MEDIUM-τ branch of `τreflect` (WalkConv item (m1)+(m2)).
--
-- `τreflect-med` handles an abstract MEDIUM-τ (the `aτ-med` outcome of
-- `classify-absτ`): a medium cell drains `draining x → empty`.  It builds the
-- EXPLICIT reachable successor `r′` (the medium's flipped cell, nodes fixed) and
-- proves `μτ r′ < μτ r`.
--
-- The successor `s′ = mkSys m′ (nA r) (nB r) (nC r) (nD r)` is exposed by
-- `WalkConvTauInv.medium-τ-inv-wt` (which threads the drained cell's coordinates
-- + `phase (med r) i d₀ id₀ ≡ draining x`); reachability is the SAME weak τ run
-- `otauB-med` uses (`lift-med-whole-τ`, closed by `rStepʷ`); the measure drop is
-- `WalkConvMeasure.μτ-med-dec` fed by `WalkConvMedium.medWt-flip` (the medium
-- weight drops by exactly 2, nodes unchanged).  0 postulate/hole/meta.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; _<_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Process_Trees using (PTree; ExtI)

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvMedStep (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟ )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _∖_ )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; τ )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_; τ*-refl; τ*-step; wτ )

-- the concrete/abstract decode + state
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysDecode blkA
  using ( SysState; mkSys; med; nA; nB; nC; nD; ⟦_⟧ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysMedium blkA
  using ( MedState; mkMed; phase; broken; decMed )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep blkA
  using ( absDec; absNodesOf; nodesOf; lift-med-whole-τ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_TauCore blkA
  using ( phase-upd; flipCell )

-- reachable-config foundation
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysReach blkA
  using ( NetProc; RState; mkR; radec; toSys; rdec; reach; Reachable )
open Reachable using ( rStepʷ )

-- the measure + the two class arithmetic facts
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvMeasure blkA
  using ( μτ; μτ-sys; nodesWt; medWt; μτ-med-dec )
-- the medium weight-drop
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvMedium blkA
  using ( medWt-flip )
-- the successor-exposing medium inversion
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvTauInv blkA
  using ( medium-τ-inv-wt )

------------------------------------------------------------------------
-- MEDIUM-τ reflector: an abstract medium τ maps to a reachable successor with
-- strictly smaller `μτ` (medium cell drained draining→empty, −2; nodes fixed).
------------------------------------------------------------------------

τreflect-med : (r : RState) {M M′ : NetProc}
    (ms  : decMed (med (toSys r)) ─[ τ ]─► M′)
    (Meq : M ≡ ((M′ ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (μτ r′ < μτ r)
τreflect-med r {M} {M′} ms Meq with medium-τ-inv-wt (med (toSys r)) ms
... | i , d₀ , id₀ , x , drainEq , M′≡ =
      r′ , Meq′ , μτ-med-dec {N = nodesWt (toSys r)} (medWt-flip (med (toSys r)) i d₀ id₀ x drainEq)
  where
    -- the flipped-cell successor MedState (the exact `m′` medium-τ-inv-wt names)
    m′ : MedState
    m′ = mkMed (phase-upd (phase (med (toSys r))) i (flipCell (phase (med (toSys r)) i) d₀ id₀))
               (broken (med (toSys r)))
    -- the successor SysState (nodes fixed)
    s′ : SysState
    s′ = mkSys m′ (nA (toSys r)) (nB (toSys r)) (nC (toSys r)) (nD (toSys r))
    -- the whole-system weak τ run `rdec r ═[ τ ]═► ⟦ s′ ⟧` (mirrors otauB-med)
    wrun : rdec r ═[ τ ]═► ⟦ s′ ⟧
    wrun = wτ (τ*-step
             (lift-med-whole-τ (decMed (med (toSys r))) (nodesOf (toSys r))
               (subst (λ z → decMed (med (toSys r)) ─[ τ ]─► z) M′≡ ms))
             τ*-refl)
    -- the reachable successor config
    r′ : RState
    r′ = mkR s′ (rStepʷ (reach r) wrun)
    -- `M ≡ radec r′`: rewrite `M′` to `decMed m′` under the ∥⇘⇙/∖ context
    Meq′ : M ≡ radec r′
    Meq′ = trans Meq (cong (λ z → (z ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES) M′≡)
