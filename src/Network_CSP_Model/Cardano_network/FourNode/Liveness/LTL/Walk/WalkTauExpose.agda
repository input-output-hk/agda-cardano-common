{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — τ-NEUTRALITY step-lift WITH D-PHASE FIXITY
-- (`Praos.WalkTauExpose`).
--
-- `WalkTauMu.liftτ*-μ` proves a hidden τ-run is `μTot`-neutral, but discards
-- the fact — established inside `τreflect-med-μ` (nodes literal) and
-- `τreflect-io-μ` (`top-nodes-io-abs-fix`'s six driver equalities) — that nD's
-- two D-consume phases `cons-BD`/`cons-CD` are FIXED across the run.  The
-- Pr-preservation half of `deliver` needs exactly that fixity across the two
-- τ-paddings of `liftReach-ev-μ`.
--
-- `liftτ*-expose` RE-MIRRORS `liftτ*-μ` returning, alongside the reachable
-- successor and the `μTot`-equality, the two fixities
--   `cons-BD (nD (toSys r′)) ≡ cons-BD (nD (toSys r))`  and the CD mirror.
--
-- No postulate/hole/meta.  All base modules stay READ-ONLY.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; _+_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Process_Trees using (PTree; ExtI)

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkTauExpose (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟ )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _∖_; EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; τ; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wev; wτ )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; mkSys; med; nA; nB; nC; nD; ⟦_⟧ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( MedState; mkMed; phase; broken; decMed )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
  using ( absDec; absNodesOf; nodesOf; lift-med-whole-τ
        ; ReflOut; innerτ; hidSync; reflect-absDec-τ
        ; InnerτR; medτ; nodesτ; reflect-inner-τ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( absNodesOf-no-τ; setCell )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysBisim blkA
  using ( lift-io-sync-whole-wτ )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( NetProc; RState; mkR; radec; toSys; rdec; reach; Reachable )
open Reachable using ( rStepʷ )

open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvEvInv blkA
  using ( medium-ev-inv-wt )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvTauInv blkA
  using ( medium-τ-inv-wt )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_TauCore blkA as STC
open STC using ( phase-upd; flipCell )

open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvNodeFix blkA
  using ( top-nodes-io-abs-fix )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.Walk blkA
  using ( μTot; breakBudget )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkMeasure blkA
  using ( μG1; μG2; μG1-cong; μG2-cong )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN

-- shorthand for the two D-consume phase fields of a state's nD node
BD : SysState → _
BD s = SN.NodeStateD.cons-BD (nD s)
CD : SysState → _
CD s = SN.NodeStateD.cons-CD (nD s)

-- the "D-consume phases are fixed" report a τ-neutral step/run carries
DFix : SysState → SysState → Set
DFix r r′ = (BD r′ ≡ BD r) × (CD r′ ≡ CD r)

-- reuse the broken-preserving medium io-event inversion
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkTauMu blkA
  using ( medium-ev-inv-brk )

------------------------------------------------------------------------
-- MEDIUM-τ reflector WITH D-phase fixity (nodes literal ⇒ both fixities refl)
------------------------------------------------------------------------

τreflect-med-expose : (r : RState) {M M′ : NetProc}
    (ms  : decMed (med (toSys r)) ─[ τ ]─► M′)
    (Meq : M ≡ ((M′ ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (μTot (toSys r′) ≡ μTot (toSys r)) × DFix (toSys r) (toSys r′)
τreflect-med-expose r {M} {M′} ms Meq with medium-τ-inv-wt (med (toSys r)) ms
... | i , d₀ , id₀ , x , drainEq , M′≡ = r′ , Meq′ , refl , (refl , refl)
  where
    m′ : MedState
    m′ = mkMed (phase-upd (phase (med (toSys r))) i (flipCell (phase (med (toSys r)) i) d₀ id₀))
               (broken (med (toSys r)))
    s′ : SysState
    s′ = mkSys m′ (nA (toSys r)) (nB (toSys r)) (nC (toSys r)) (nD (toSys r))
    wrun : rdec r ═[ τ ]═► ⟦ s′ ⟧
    wrun = wτ (τ*-step
             (lift-med-whole-τ (decMed (med (toSys r))) (nodesOf (toSys r))
               (subst (λ z → decMed (med (toSys r)) ─[ τ ]─► z) M′≡ ms))
             τ*-refl)
    r′ : RState
    r′ = mkR s′ (rStepʷ (reach r) wrun)
    Meq′ : M ≡ radec r′
    Meq′ = trans Meq (cong (λ z → (z ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES) M′≡)

------------------------------------------------------------------------
-- io-SYNC reflector WITH D-phase fixity (top-nodes-io-abs-fix's edBD/edCD)
------------------------------------------------------------------------

τreflect-io-expose : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M₁ N₁ M : NetProc}
    (iomem : ioES .mem (X , e) a)
    (sM : decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► M₁)
    (sN : absNodesOf (toSys r)   ─[ ev (evl (evLabel X e a)) ]─► N₁)
    (Meq : M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (μTot (toSys r′) ≡ μTot (toSys r)) × DFix (toSys r) (toSys r′)
τreflect-io-expose r {X} {e} {a} {M₁} {N₁} {M} iomem sM sN Meq
    with medium-ev-inv-brk (med (toSys r)) iomem sM
       | top-nodes-io-abs-fix (toSys r) iomem sN
... | m′ , M₁≡ , brkEq | s″ , medEq , N₁≡ , cWeakRun , epAB , epAC , ecpB , ecpC , edBD , edCD =
      r′ , Meq′ , μeq , (sym edBD , sym edCD)
  where
    s′ : SysState
    s′ = mkSys m′ (nA s″) (nB s″) (nC s″) (nD s″)
    medWeak : decMed (med (toSys r)) ═[ ev (evl (evLabel X e a)) ]═► decMed m′
    medWeak = wev τ*-refl
                (subst (λ z → decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► z) M₁≡ sM)
                τ*-refl
    wrun : rdec r ═[ τ ]═► ⟦ s′ ⟧
    wrun = lift-io-sync-whole-wτ (decMed (med (toSys r))) (nodesOf (toSys r)) iomem medWeak cWeakRun
    r′ : RState
    r′ = mkR s′ (rStepʷ (reach r) wrun)
    Meq′ : M ≡ radec r′
    Meq′ = trans Meq (cong₂ (λ mm nn → (mm ∥⇘ ioES ⇙ nn) ∖ ioES) M₁≡ N₁≡)
    μeq : μTot (toSys r′) ≡ μTot (toSys r)
    μeq = cong₂ _+_ (sym (μG1-cong (toSys r) s′ epAB ecpB edBD))
                    (cong₂ _+_ (sym (μG2-cong (toSys r) s′ epAC ecpC edCD)) brkEq)

------------------------------------------------------------------------
-- TOTAL per-τ reflector with D-phase fixity (mirror `τreflect-μ`).
------------------------------------------------------------------------

τreflect-expose : (r : RState) {M : NetProc} → radec r ─[ τ ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (μTot (toSys r′) ≡ μTot (toSys r)) × DFix (toSys r) (toSys r′)
τreflect-expose r step with reflect-absDec-τ (toSys r) step
... | innerτ P′ innerStep Peq
    with reflect-inner-τ (decMed (med (toSys r))) (absNodesOf (toSys r)) innerStep
...   | medτ   M′ ms eqP = τreflect-med-expose r ms (trans Peq (cong (λ z → z ∖ ioES) eqP))
...   | nodesτ N′ ns eqP = ⊥-elim (absNodesOf-no-τ (toSys r) ns)
τreflect-expose r step | hidSync M₁ N₁ iomem sM sN Peq = τreflect-io-expose r iomem sM sN Peq

------------------------------------------------------------------------
-- τ-run lift with `μTot`-neutrality AND D-phase fixity (mirror `liftτ*-μ`).
------------------------------------------------------------------------

liftτ*-expose′ : (r : RState) {start u : NetProc} → start ≡ radec r
          → start ─[τ*]─► u
          → Σ[ r′ ∈ RState ] (u ≡ radec r′) × (μTot (toSys r′) ≡ μTot (toSys r)) × DFix (toSys r) (toSys r′)
liftτ*-expose′ r eq τ*-refl = r , eq , refl , (refl , refl)
liftτ*-expose′ r eq (τ*-step s rest) with τreflect-expose r (subst (λ z → z ─[ τ ]─► _) eq s)
... | r₁ , eq₁ , μ₁ , (bd₁ , cd₁) with liftτ*-expose′ r₁ eq₁ rest
...   | r′ , equ , μ′ , (bd′ , cd′) =
        r′ , equ , trans μ′ μ₁ , (trans bd′ bd₁ , trans cd′ cd₁)

liftτ*-expose : (r : RState) {u : NetProc}
         → radec r ─[τ*]─► u
         → Σ[ r′ ∈ RState ] (u ≡ radec r′) × (μTot (toSys r′) ≡ μTot (toSys r)) × DFix (toSys r) (toSys r′)
liftτ*-expose r = liftτ*-expose′ r refl
