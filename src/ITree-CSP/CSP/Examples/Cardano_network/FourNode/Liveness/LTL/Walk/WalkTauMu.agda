{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the τ-NEUTRALITY step-lift (`Praos.WalkTauMu`).
--
-- `liftReach-ev-μ` (the measure-carrying weak-visible move) needs the two
-- τ-paddings around its strict-`<` visible middle to be `μTot`-NON-INCREASING.
-- Every abstract LTS τ is in fact `μTot`-NEUTRAL:
--   · medτ    — a medium cell drains (`draining x → empty`): nodes literal,
--               broken literal ⇒ `μTot` unchanged by `refl`;
--   · nodesτ  — VACUOUS (`absNodesOf-no-τ`, abstract nodes are react-τ-free);
--   · hidSync — a hidden io-sync: the medium cell fills/drains (`broken`
--               preserved ⇒ break budget fixed) and ONE bundle peer advances
--               while the six group DRIVERS are preserved
--               (`WalkConvNodeFix.top-nodes-io-abs-fix`) ⇒ `μG1`/`μG2` fixed
--               by `μG1-cong`/`μG2-cong` ⇒ `μTot` unchanged.
--
-- `τreflect-μ` dispatches the abstract τ class (mirror `WalkConvNoDiv.τreflect`)
-- returning a reachable successor `r′` with `M ≡ radec r′` AND `μTot (toSys r′)
-- ≡ μTot (toSys r)`; `liftτ*-μ` iterates it over a hidden τ-run (mirror
-- `WalkStepLift.liftτ*`), yielding the `≡` (hence `≤`) padding.
--
-- No postulate/hole/meta.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; _+_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Process_Trees using (PTree; ExtI)

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkTauMu (blkA : Block₃) where

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

-- the concrete/abstract decode + state records
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

-- reachable-config foundation
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( NetProc; RState; mkR; radec; toSys; rdec; reach; Reachable )
open Reachable using ( rStepʷ )

-- the medium io-EVENT inversion (successor components) + the drain τ inversion
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvEvInv blkA
  using ( medium-ev-inv-wt )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvTauInv blkA
  using ( medium-τ-inv-wt )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_TauCore blkA as STC
open STC using ( phase-upd; flipCell )

-- the io-sync DRIVER-FIXITY node cone
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvNodeFix blkA
  using ( top-nodes-io-abs-fix )
-- the whole-trace measure + break budget, and the per-group congruences
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.Walk blkA
  using ( μTot; breakBudget )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkMeasure blkA
  using ( μG1; μG2; μG1-cong; μG2-cong )

------------------------------------------------------------------------
-- BROKEN-preserving medium io-EVENT inversion: the successor `m′` keeps the
-- `broken` flags LITERAL (io only touches a cell phase), so the break budget
-- is preserved (`refl`).
------------------------------------------------------------------------

medium-ev-inv-brk : (m : MedState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → decMed m ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ m′ ∈ MedState ] (M ≡ decMed m′) × (breakBudget m′ ≡ breakBudget m)
medium-ev-inv-brk m iomem step with medium-ev-inv-wt m iomem step
... | i , d₀ , id₀ , np , riseEq , Meq =
      mkMed (phase-upd (phase m) i (setCell (phase m i) d₀ id₀ np)) (broken m) , Meq , refl

------------------------------------------------------------------------
-- MEDIUM-τ NEUTRAL reflector (mirror `WalkConvMedStep.τreflect-med`): the
-- drained-cell successor keeps nodes + broken literal ⇒ `μTot` unchanged (refl).
------------------------------------------------------------------------

τreflect-med-μ : (r : RState) {M M′ : NetProc}
    (ms  : decMed (med (toSys r)) ─[ τ ]─► M′)
    (Meq : M ≡ ((M′ ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (μTot (toSys r′) ≡ μTot (toSys r))
τreflect-med-μ r {M} {M′} ms Meq with medium-τ-inv-wt (med (toSys r)) ms
... | i , d₀ , id₀ , x , drainEq , M′≡ = r′ , Meq′ , refl
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
-- io-SYNC NEUTRAL reflector (mirror `WalkConvNoDiv.τreflect-io`): break budget
-- fixed (`medium-ev-inv-brk`), six drivers fixed (`top-nodes-io-abs-fix`) ⇒
-- `μG1`/`μG2` fixed (`μG1-cong`/`μG2-cong`) ⇒ `μTot` unchanged.
------------------------------------------------------------------------

τreflect-io-μ : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M₁ N₁ M : NetProc}
    (iomem : ioES .mem (X , e) a)
    (sM : decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► M₁)
    (sN : absNodesOf (toSys r)   ─[ ev (evl (evLabel X e a)) ]─► N₁)
    (Meq : M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (μTot (toSys r′) ≡ μTot (toSys r))
τreflect-io-μ r {X} {e} {a} {M₁} {N₁} {M} iomem sM sN Meq
    with medium-ev-inv-brk (med (toSys r)) iomem sM
       | top-nodes-io-abs-fix (toSys r) iomem sN
... | m′ , M₁≡ , brkEq | s″ , medEq , N₁≡ , cWeakRun , epAB , epAC , ecpB , ecpC , edBD , edCD =
      r′ , Meq′ , μeq
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
-- The TOTAL per-τ NEUTRAL reflector (mirror `WalkConvNoDiv.τreflect`).
------------------------------------------------------------------------

τreflect-μ : (r : RState) {M : NetProc} → radec r ─[ τ ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (μTot (toSys r′) ≡ μTot (toSys r))
τreflect-μ r step with reflect-absDec-τ (toSys r) step
... | innerτ P′ innerStep Peq
    with reflect-inner-τ (decMed (med (toSys r))) (absNodesOf (toSys r)) innerStep
...   | medτ   M′ ms eqP = τreflect-med-μ r ms (trans Peq (cong (λ z → z ∖ ioES) eqP))
...   | nodesτ N′ ns eqP = ⊥-elim (absNodesOf-no-τ (toSys r) ns)
τreflect-μ r step | hidSync M₁ N₁ iomem sM sN Peq = τreflect-io-μ r iomem sM sN Peq

------------------------------------------------------------------------
-- τ-run lift with `μTot`-neutrality (mirror `WalkStepLift.liftτ*`): a hidden
-- τ-run lands on a reachable config with the SAME `μTot`.
------------------------------------------------------------------------

-- generalised over the start tree (the termination fix, à la `liftτ*′`)
liftτ*-μ′ : (r : RState) {start u : NetProc} → start ≡ radec r
          → start ─[τ*]─► u
          → Σ[ r′ ∈ RState ] (u ≡ radec r′) × (μTot (toSys r′) ≡ μTot (toSys r))
liftτ*-μ′ r eq τ*-refl = r , eq , refl
liftτ*-μ′ r eq (τ*-step s rest) with τreflect-μ r (subst (λ z → z ─[ τ ]─► _) eq s)
... | r₁ , eq₁ , μ₁ with liftτ*-μ′ r₁ eq₁ rest
...   | r′ , equ , μ′ = r′ , equ , trans μ′ μ₁

liftτ*-μ : (r : RState) {u : NetProc}
         → radec r ─[τ*]─► u
         → Σ[ r′ ∈ RState ] (u ≡ radec r′) × (μTot (toSys r′) ≡ μTot (toSys r))
liftτ*-μ r = liftτ*-μ′ r refl
