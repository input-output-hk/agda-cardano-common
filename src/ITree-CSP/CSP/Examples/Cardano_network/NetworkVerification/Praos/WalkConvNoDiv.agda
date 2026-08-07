{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- R3 — the UNCONDITIONAL τ-convergence `absNoDiv` (WalkConv item (4), CRUX).
--
-- Assembles the per-τ-class reflectors into the well-founded engine
-- `WalkConv.absNoDiv`, yielding
--
--     absNoDiv : (r : RState) → ¬ Diverges (radec r)
--
-- i.e. `abstractSystem` τ-CONVERGES from every reachable config — the ONE
-- obligation R2 left open on the divergence axis (R2's `odiv` was a coinductive
-- transfer, never a `¬ Diverges`).
--
-- `τreflect` dispatches an abstract τ `radec r ─[τ]─► M` (mirror `otauB-impl`):
--   · `reflect-absDec-τ` → `innerτ` (a `∥⇘ ioES ⇙`-internal τ) or `hidSync`
--     (a hidden io-sync);
--   · `innerτ` → `reflect-inner-τ` → `medτ` (MEDIUM-τ, handled by the
--     `WalkConvMedStep.τreflect-med` drain-cell reflector) or `nodesτ`
--     (VACUOUS: `absNodesOf-no-τ` — abstract nodes are native-react τ-free);
--   · `hidSync` → `τreflect-io` below.
-- Each branch returns a reachable successor `r′` with `M ≡ radec r′` AND
-- `μτ r′ < μτ r`; the engine descends on `<`-well-foundedness.
--
-- `τreflect-io` mirrors `SysBisim.otauB-hidSync` (reusing `lift-io-sync-whole-wτ`
-- for reachability), but builds the successor via `mkR s′ …` so `μτ r′` reduces
-- to `μτ-sys s′` DEFINITIONALLY, then supplies the strict drop
-- `μτ-io-dec (top-nodes-io-abs-wt … node drop) (medium-ev-inv-wt′ … cell rise)`.
--
-- No postulate/hole/meta.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Nat using (_<_)
open import Data.Nat.Properties using (≤-reflexive)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Process_Trees using (PTree; ExtI)

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvNoDiv (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟ )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _∖_; EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; τ; ev; evl; evLabel; Diverges )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_; wev; τ*-refl )

-- the concrete/abstract decode + state records
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysDecode blkA
  using ( SysState; mkSys; med; nA; nB; nC; nD; ⟦_⟧ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysMedium blkA
  using ( MedState; decMed )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep blkA
  using ( absDec; absNodesOf; nodesOf
        ; ReflOut; innerτ; hidSync; reflect-absDec-τ
        ; InnerτR; medτ; nodesτ; reflect-inner-τ )
-- the abstract nodes-τ VACUITY + the whole-system io-sync weak lift
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_NodeTauEv blkA
  using ( absNodesOf-no-τ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysBisim blkA
  using ( lift-io-sync-whole-wτ )

-- reachable-config foundation
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysReach blkA
  using ( NetProc; RState; mkR; radec; toSys; rdec; reach; Reachable )
open Reachable using ( rStepʷ )

-- the measure + the io-class arithmetic fact
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvMeasure blkA
  using ( μτ; μτ-sys; nodesWt; medWt; μτ-io-dec )
-- the successor-exposing medium io-EVENT inversion (medium weight +1)
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvEvInv blkA
  using ( medium-ev-inv-wt′ )
-- the node cone weight drop (nodesWt −1 on an io-sync)
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvNodeDrop blkA
  using ( top-nodes-io-abs-wt )
-- the MEDIUM-τ reflector
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvMedStep blkA
  using ( τreflect-med )
-- the well-founded τ-convergence ENGINE (parameterised over μτ + τreflect)
import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConv blkA as WC

------------------------------------------------------------------------
-- io-SYNC reflector: a hidden io-sync maps to a reachable successor with
-- strictly smaller `μτ` (node −1 dominates the medium +1 under the 3· weight).
-- Mirror of `otauB-hidSync`, but the successor is built with `mkR s′ …` so the
-- measure reduces, and the drop is supplied by `μτ-io-dec`.
------------------------------------------------------------------------

τreflect-io : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M₁ N₁ M : NetProc}
    (iomem : ioES .mem (X , e) a)
    (sM : decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► M₁)
    (sN : absNodesOf (toSys r)   ─[ ev (evl (evLabel X e a)) ]─► N₁)
    (Meq : M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (μτ r′ < μτ r)
τreflect-io r {X} {e} {a} {M₁} {N₁} {M} iomem sM sN Meq
    with medium-ev-inv-wt′ (med (toSys r)) iomem sM
       | top-nodes-io-abs-wt (toSys r) iomem sN
... | m′ , M₁≡ , medRise | s″ , medEq , N₁≡ , cWeakRun , nodeDrop =
      r′ , Meq′ ,
      μτ-io-dec {nodesWt s″} {nodesWt (toSys r)} {medWt m′} {medWt (med (toSys r))}
                nodeDrop (≤-reflexive medRise)
  where
    -- the io-sync successor SysState (medium cell filled/drained, one node advanced)
    s′ : SysState
    s′ = mkSys m′ (nA s″) (nB s″) (nC s″) (nD s″)
    -- the medium's WEAK io-event run into `decMed m′`
    medWeak : decMed (med (toSys r)) ═[ ev (evl (evLabel X e a)) ]═► decMed m′
    medWeak = wev τ*-refl
                (subst (λ z → decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► z) M₁≡ sM)
                τ*-refl
    -- the whole-system WEAK τ run `rdec r ═[ τ ]═► ⟦ s′ ⟧` (io hidden by ∖ ioES)
    wrun : rdec r ═[ τ ]═► ⟦ s′ ⟧
    wrun = lift-io-sync-whole-wτ (decMed (med (toSys r))) (nodesOf (toSys r)) iomem medWeak cWeakRun
    -- the reachable successor config (mkR ⇒ `toSys r′ = s′` DEFINITIONALLY)
    r′ : RState
    r′ = mkR s′ (rStepʷ (reach r) wrun)
    -- `M ≡ radec r′`: rewrite `M₁`/`N₁` to `decMed m′`/`absNodesOf s″`
    Meq′ : M ≡ radec r′
    Meq′ = trans Meq (cong₂ (λ mm nn → (mm ∥⇘ ioES ⇙ nn) ∖ ioES) M₁≡ N₁≡)

------------------------------------------------------------------------
-- The TOTAL per-τ reflector: dispatch the abstract τ class (mirror `otauB-impl`).
------------------------------------------------------------------------

τreflect : (r : RState) {M : NetProc} → radec r ─[ τ ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (μτ r′ < μτ r)
τreflect r step with reflect-absDec-τ (toSys r) step
... | innerτ P′ innerStep Peq
    with reflect-inner-τ (decMed (med (toSys r))) (absNodesOf (toSys r)) innerStep
...   | medτ   M′ ms eqP = τreflect-med r ms (trans Peq (cong (λ z → z ∖ ioES) eqP))
...   | nodesτ N′ ns eqP = ⊥-elim (absNodesOf-no-τ (toSys r) ns)
τreflect r step | hidSync M₁ N₁ iomem sM sN Peq = τreflect-io r iomem sM sN Peq

------------------------------------------------------------------------
-- UNCONDITIONAL τ-convergence of `abstractSystem` at every reachable config.
------------------------------------------------------------------------

absNoDiv : (r : RState) → ¬ Diverges (radec r)
absNoDiv = WC.absNoDiv μτ τreflect
