{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the COMBINED `PipeReport` (DReport × CellReport)
-- (`Praos.PipeExposeReport`).
--
-- `WalkTauExpose.liftτ*-expose` exposes the nodeD `DFix` across a hidden τ-run;
-- `PipeExposeCell.liftτ*-cell` exposes the whole-medium `AllCellAdv` across the
-- SAME kind of run.  But the two build DIFFERENT reflected successors `r′` (the
-- D-fixity reflector uses `medium-ev-inv-brk`, the cell one `medium-ev-inv-wt`),
-- so their two `r′` chains cannot be reconciled through the non-injective `⟦_⟧`.
--
-- This module rebuilds ONE reflector `τreflect-both` that emits BOTH reports on
-- the SAME `r′`: it uses `medium-ev-inv-wt` (so the medium is the `setCell`
-- form the cell report needs) and reads the D-fixity from the SAME
-- `top-nodes-io-abs-fix` (`edBD`/`edCD`) — which depends only on the NODES, so
-- it is unaffected by the medium choice.  `liftτ*-both` folds both across a
-- τ-run; `liftReach-ev-both` composes a τ-pre, the visible middle
-- (`PipeExposeReach.reach-ev-both`), and a τ-post; `liftReach-pipe` projects the
-- whole-medium report onto the leg cells, yielding `PipeReport l = DReport ×
-- CellReport`, the report `StepEmit` will classify into a `PipeStep⁺`.
--
-- No postulate/hole/meta.  All base modules stay READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Empty using ( ⊥-elim )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; cong₂; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Archive.PipeExposeReport (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; apiES )
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
  using ( NetProc; absNodesOf; nodesOf; lift-med-whole-τ
        ; reflect-absDec-τ; innerτ; hidSync; reflect-inner-τ; medτ; nodesτ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( RState; mkR; radec; toSys; rdec; reach; Reachable )
open Reachable using ( rStepʷ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvTauInv blkA
  using ( medium-τ-inv-wt )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvEvInv blkA
  using ( medium-ev-inv-wt )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvNodeFix blkA
  using ( top-nodes-io-abs-fix )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysBisim blkA
  using ( lift-io-sync-whole-wτ )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_TauCore blkA as STC
open STC using ( phase-upd; flipCell )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( setCell; absNodesOf-no-τ )

-- the two per-component algebras + the leg projection
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Archive.PipeExposeCell blkA
  using ( CellAdv; AllCellAdv; allCellAdv-refl; allCellAdv-trans
        ; cell-drain-read; cell-fill-read; CellReport; allCellAdv⇒CellReport )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkTauExpose blkA
  using ( BD; CD; DFix )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkDExpose blkA
  using ( DReport )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkReachExpose blkA
  using ( compose-DReport )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Archive.PipeExposeReach blkA
  using ( reach-ev-both )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA
  using ( IsApiCSBF )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs )

------------------------------------------------------------------------
-- MEDIUM-τ reflector WITH BOTH reports (nodes literal ⇒ `DFix (refl,refl)`;
-- the drained cell advances by `cDrn`).  Same `r′` as
-- `WalkTauExpose.τreflect-med-expose` / `PipeExposeCell.τreflect-med-cell`.
------------------------------------------------------------------------

τreflect-med-both : (r : RState) {M M′ : NetProc}
    (ms  : decMed (med (toSys r)) ─[ τ ]─► M′)
    (Meq : M ≡ ((M′ ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′)
      × DFix (toSys r) (toSys r′) × AllCellAdv (toSys r) (toSys r′)
τreflect-med-both r {M} {M′} ms Meq with medium-τ-inv-wt (med (toSys r)) ms
... | i , d₀ , id₀ , x , drainEq , M′≡ = r′ , Meq′ , (refl , refl) , report
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
    report : AllCellAdv (toSys r) (toSys r′)
    report kl kd kid = cell-drain-read (med (toSys r)) i d₀ id₀ x drainEq kl kd kid

------------------------------------------------------------------------
-- io-SYNC reflector WITH BOTH reports (RAM-heavy).  Uses `medium-ev-inv-wt`
-- (so the medium is the `setCell` form the cell report needs) and reads `DFix`
-- from the SAME `top-nodes-io-abs-fix`'s `edBD`/`edCD` — node-only, so
-- unaffected by the medium choice.  Same `r′` as `PipeExposeCell.τreflect-io-cell`.
------------------------------------------------------------------------

τreflect-io-both : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M₁ N₁ M : NetProc}
    (iomem : ioES .mem (X , e) a)
    (sM : decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► M₁)
    (sN : absNodesOf (toSys r)   ─[ ev (evl (evLabel X e a)) ]─► N₁)
    (Meq : M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′)
      × DFix (toSys r) (toSys r′) × AllCellAdv (toSys r) (toSys r′)
τreflect-io-both r {X} {e} {a} {M₁} {N₁} {M} iomem sM sN Meq
    with medium-ev-inv-wt (med (toSys r)) iomem sM
       | top-nodes-io-abs-fix (toSys r) iomem sN
... | i , d₀ , id₀ , np , wtEq , M₁≡ | s″ , _ , N₁≡ , cWeakRun , _ , _ , _ , _ , edBD , edCD =
      r′ , Meq′ , (sym edBD , sym edCD) , report
  where
    m′ : MedState
    m′ = mkMed (phase-upd (phase (med (toSys r))) i (setCell (phase (med (toSys r)) i) d₀ id₀ np))
               (broken (med (toSys r)))
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
    report : AllCellAdv (toSys r) (toSys r′)
    report kl kd kid = cell-fill-read (med (toSys r)) i d₀ id₀ np wtEq kl kd kid

------------------------------------------------------------------------
-- TOTAL per-τ reflector with BOTH reports (mirror `τreflect-expose`).
------------------------------------------------------------------------

τreflect-both : (r : RState) {M : NetProc} → radec r ─[ τ ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′)
      × DFix (toSys r) (toSys r′) × AllCellAdv (toSys r) (toSys r′)
τreflect-both r step with reflect-absDec-τ (toSys r) step
... | innerτ P′ innerStep Peq
    with reflect-inner-τ (decMed (med (toSys r))) (absNodesOf (toSys r)) innerStep
...   | medτ   M′ ms eqP = τreflect-med-both r ms (trans Peq (cong (λ z → z ∖ ioES) eqP))
...   | nodesτ N′ ns eqP = ⊥-elim (absNodesOf-no-τ (toSys r) ns)
τreflect-both r step | hidSync M₁ N₁ iomem sM sN Peq = τreflect-io-both r iomem sM sN Peq

------------------------------------------------------------------------
-- τ-run lift with BOTH reports (mirror `liftτ*-expose`): fold `DFix` by `trans`
-- and `AllCellAdv` by pointwise composition.
------------------------------------------------------------------------

liftτ*-both′ : (r : RState) {start u : NetProc} → start ≡ radec r
          → start ─[τ*]─► u
          → Σ[ r′ ∈ RState ] (u ≡ radec r′)
              × DFix (toSys r) (toSys r′) × AllCellAdv (toSys r) (toSys r′)
liftτ*-both′ r eq τ*-refl = r , eq , (refl , refl) , allCellAdv-refl (toSys r)
liftτ*-both′ r eq (τ*-step s rest) with τreflect-both r (subst (λ z → z ─[ τ ]─► _) eq s)
... | r₁ , eq₁ , (bd₁ , cd₁) , acr₁ with liftτ*-both′ r₁ eq₁ rest
...   | r′ , equ , (bd′ , cd′) , acr′ =
        r′ , equ , (trans bd′ bd₁ , trans cd′ cd₁) ,
        allCellAdv-trans (toSys r) (toSys r₁) (toSys r′) acr₁ acr′

liftτ*-both : (r : RState) {u : NetProc}
         → radec r ─[τ*]─► u
         → Σ[ r′ ∈ RState ] (u ≡ radec r′)
             × DFix (toSys r) (toSys r′) × AllCellAdv (toSys r) (toSys r′)
liftτ*-both r = liftτ*-both′ r refl

------------------------------------------------------------------------
-- The weak api move WITH BOTH reports (mirror `liftReach-ev-expose`): compose
-- the τ-pre `DFix`/`AllCellAdv`, the visible-middle `DReport`/`AllCellAdv`, and
-- the τ-post `DFix`/`AllCellAdv` on ONE reflected `r′`.
------------------------------------------------------------------------

liftReach-ev-both : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {t′ : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ═[ ev (evl (evLabel X e a)) ]═► t′
  → Σ[ r′ ∈ RState ] (t′ ≡ radec r′)
      × DReport (toSys r) (toSys r′) e a × AllCellAdv (toSys r) (toSys r′)
liftReach-ev-both r {X} {e} {a} aic apimem (wev pre mid post) with liftτ*-both r pre
... | r₁ , eq₁ , fix₁ , acr₁
    with reach-ev-both r₁ aic apimem
           (subst (λ z → z ─[ ev (evl (evLabel X e a)) ]─► _) eq₁ mid)
...   | r₂ , eq₂ , _ , _ , drep , acrmid
      with liftτ*-both r₂ (subst (λ z → z ─[τ*]─► _) eq₂ post)
...     | r′ , equ , fix₃ , acr₃ =
          r′ , equ ,
          compose-DReport (toSys r) (toSys r₁) (toSys r₂) (toSys r′) fix₁ drep fix₃ ,
          allCellAdv-trans (toSys r) (toSys r₁) (toSys r′) acr₁
            (allCellAdv-trans (toSys r₁) (toSys r₂) (toSys r′) acrmid acr₃)

------------------------------------------------------------------------
-- The combined `PipeReport l` (the plan's `DReport × CellReport`) and its
-- weak-move producer `liftReach-pipe` (the report `StepEmit` will classify).
------------------------------------------------------------------------

-- the CELL+D component of the seven-component leg-`l` report across a weak move
PipeReport : TwoLegs → (s s′ : SysState) {X : Set 0ℓ} → Net_Api Payload X → X → Set₁
PipeReport l s s′ e a = DReport s s′ e a × CellReport l s s′

-- HEADLINE: a weak api-CSBF move exposes the leg-`l` `DReport × CellReport` on
-- one reflected successor `r′`
liftReach-pipe : (l : TwoLegs) (r : RState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {t′ : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ═[ ev (evl (evLabel X e a)) ]═► t′
  → Σ[ r′ ∈ RState ] (t′ ≡ radec r′) × PipeReport l (toSys r) (toSys r′) e a
liftReach-pipe l r aic apimem w with liftReach-ev-both r aic apimem w
... | r′ , eq , drep , acr =
      r′ , eq , (drep , allCellAdv⇒CellReport l (toSys r) (toSys r′) acr)
