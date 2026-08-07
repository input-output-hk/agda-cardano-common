{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R2 — io-peel layer, PART 4 (ABSTRACT NODE-τ collapse).
--
-- The FUSED node-τ inversions `nodeX-τ-inv-abs`: a concrete NODES τ (a peer
-- loop re-entry `…Sil st → …Head st`) of `decNodeX nX` lands on `decNodeX nX′`
-- AND leaves the ABSTRACT decode UNCHANGED (`absNodeX nX ≡ absNodeX nX′`).  The
-- committed `nodeX-τ-inv` (SysOracle_NodeTauEv) discards the `poseq : peer ≡
-- …Sil st` that `BundleτR` carries, so its `na′` cannot witness the abstract
-- collapse.  Here the 8 `finishX-{L,R}-abs` KEEP `poseq` and emit the collapse
-- eq via `cong (λ q → absNodeX (mkNodeX … q …)) poseq` — refl-convertible
-- because `absX (…Sil st)` and `absX (…Head st)` both reduce to
-- `absX (…Head st)`'s `tableSpec` at `coarsen…St st` (the committed
-- `absXc/s-sil-collapse`, all refl).  This feeds `comove-nodes-τ`'s
-- `absEq : absDec s ≡ absDec s′` (the abstract side matches by ZERO τ).
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.SysIoLink4 (blkA : Block₃) where

open import Level using (0ℓ; Level)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Process_Trees using (PTree; ExtI)

-- links, api alphabet, block payloads
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using
  ( p; apiES; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟ )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using ( Dir; lo; hi )

-- Net_Api operators + the empty sync alphabet + the Par τ-elimination
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_ )
open Op using () renaming (∅ES to ∅ESa)
import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload}) as PEA

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; τ )

-- concrete node decodes + the node states + drivers + bundles + positions
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode blkA as SN
open SN using
  ( NetProc; decNodeA; decNodeB; decNodeC; decNodeD
  ; bundleA; bundleG; decProd; decCP; decConsD
  ; mkInert; tsc; tss; kac; kas; lnc; lns; lfc; lfs
  ; csHead; ssHead; bcHead; bsHead; tcHead; tsHead
  ; kcHead; ksHead; lncHead; lnsHead; lfcHead; lfsHead )

-- abstract node decodes + the per-node τ-reflection
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep blkA using
  ( absNodeA; absNodeB; absNodeC; absNodeD
  ; NodeτR; bundleτ; driverτ; reflect-node-τ )

-- the 12-peer bundle τ-inversion + its result type + the driver τ-freedom
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_NodeTauEv blkA using
  ( BundleτR; bcsc; bcss; bbfc; bbfs; btsc; btss; bkac; bkas; blnc; blns; blfc; blfs
  ; bundle-τ-inv; decProd-no-τ; decCP-no-τ; decConsD-no-τ )

------------------------------------------------------------------------
-- The 8 fused `finishX-{L,R}-abs` + the 4 `nodeX-τ-inv-abs` (generated,
-- byte-mirror of the committed `finishX-{L,R}` / `nodeX-τ-inv` with the
-- abstract-collapse third component added).
------------------------------------------------------------------------

-- fused: finishA-L-abs (also emits the abstract collapse `absNodeA` eq)
finishA-L-abs : (na : SN.NodeStateA) {A′ Bd′ M1 : NetProc}
  → A′ ≡ (Bd′ ∥⇘ apiES ⇙ (decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)))
  → Bd′ ≡ (M1 ⦀ bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
  → BundleτR linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) M1
  → Σ[ na′ ∈ SN.NodeStateA ] (A′ ≡ decNodeA na′) × (absNodeA na ≡ absNodeA na′)
finishA-L-abs na eq eqL (bcsc st poseq refl) rewrite eqL =
  SN.mkNodeA (csHead st) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)  , eq ,
  cong (λ q → absNodeA (SN.mkNodeA q (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na))) poseq
finishA-L-abs na eq eqL (bcss st poseq refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (ssHead st) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)  , eq ,
  cong (λ q → absNodeA (SN.mkNodeA (SN.NodeStateA.csC-AB na) q (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na))) poseq
finishA-L-abs na eq eqL (bbfc st poseq refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (bcHead st) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)  , eq ,
  cong (λ q → absNodeA (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) q (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na))) poseq
finishA-L-abs na eq eqL (bbfs st poseq refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (bsHead st) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)  , eq ,
  cong (λ q → absNodeA (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) q (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na))) poseq
finishA-L-abs na eq eqL (btsc st poseq refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tcHead st) (tss (SN.NodeStateA.inert-AB na)) (kac (SN.NodeStateA.inert-AB na)) (kas (SN.NodeStateA.inert-AB na)) (lnc (SN.NodeStateA.inert-AB na)) (lns (SN.NodeStateA.inert-AB na)) (lfc (SN.NodeStateA.inert-AB na)) (lfs (SN.NodeStateA.inert-AB na))) (SN.NodeStateA.inert-AC na)  , eq ,
  cong (λ q → absNodeA (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert q (tss (SN.NodeStateA.inert-AB na)) (kac (SN.NodeStateA.inert-AB na)) (kas (SN.NodeStateA.inert-AB na)) (lnc (SN.NodeStateA.inert-AB na)) (lns (SN.NodeStateA.inert-AB na)) (lfc (SN.NodeStateA.inert-AB na)) (lfs (SN.NodeStateA.inert-AB na))) (SN.NodeStateA.inert-AC na))) poseq
finishA-L-abs na eq eqL (btss st poseq refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tsc (SN.NodeStateA.inert-AB na)) (tsHead st) (kac (SN.NodeStateA.inert-AB na)) (kas (SN.NodeStateA.inert-AB na)) (lnc (SN.NodeStateA.inert-AB na)) (lns (SN.NodeStateA.inert-AB na)) (lfc (SN.NodeStateA.inert-AB na)) (lfs (SN.NodeStateA.inert-AB na))) (SN.NodeStateA.inert-AC na)  , eq ,
  cong (λ q → absNodeA (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tsc (SN.NodeStateA.inert-AB na)) q (kac (SN.NodeStateA.inert-AB na)) (kas (SN.NodeStateA.inert-AB na)) (lnc (SN.NodeStateA.inert-AB na)) (lns (SN.NodeStateA.inert-AB na)) (lfc (SN.NodeStateA.inert-AB na)) (lfs (SN.NodeStateA.inert-AB na))) (SN.NodeStateA.inert-AC na))) poseq
finishA-L-abs na eq eqL (bkac st poseq refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tsc (SN.NodeStateA.inert-AB na)) (tss (SN.NodeStateA.inert-AB na)) (kcHead st) (kas (SN.NodeStateA.inert-AB na)) (lnc (SN.NodeStateA.inert-AB na)) (lns (SN.NodeStateA.inert-AB na)) (lfc (SN.NodeStateA.inert-AB na)) (lfs (SN.NodeStateA.inert-AB na))) (SN.NodeStateA.inert-AC na)  , eq ,
  cong (λ q → absNodeA (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tsc (SN.NodeStateA.inert-AB na)) (tss (SN.NodeStateA.inert-AB na)) q (kas (SN.NodeStateA.inert-AB na)) (lnc (SN.NodeStateA.inert-AB na)) (lns (SN.NodeStateA.inert-AB na)) (lfc (SN.NodeStateA.inert-AB na)) (lfs (SN.NodeStateA.inert-AB na))) (SN.NodeStateA.inert-AC na))) poseq
finishA-L-abs na eq eqL (bkas st poseq refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tsc (SN.NodeStateA.inert-AB na)) (tss (SN.NodeStateA.inert-AB na)) (kac (SN.NodeStateA.inert-AB na)) (ksHead st) (lnc (SN.NodeStateA.inert-AB na)) (lns (SN.NodeStateA.inert-AB na)) (lfc (SN.NodeStateA.inert-AB na)) (lfs (SN.NodeStateA.inert-AB na))) (SN.NodeStateA.inert-AC na)  , eq ,
  cong (λ q → absNodeA (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tsc (SN.NodeStateA.inert-AB na)) (tss (SN.NodeStateA.inert-AB na)) (kac (SN.NodeStateA.inert-AB na)) q (lnc (SN.NodeStateA.inert-AB na)) (lns (SN.NodeStateA.inert-AB na)) (lfc (SN.NodeStateA.inert-AB na)) (lfs (SN.NodeStateA.inert-AB na))) (SN.NodeStateA.inert-AC na))) poseq
finishA-L-abs na eq eqL (blnc st poseq refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tsc (SN.NodeStateA.inert-AB na)) (tss (SN.NodeStateA.inert-AB na)) (kac (SN.NodeStateA.inert-AB na)) (kas (SN.NodeStateA.inert-AB na)) (lncHead st) (lns (SN.NodeStateA.inert-AB na)) (lfc (SN.NodeStateA.inert-AB na)) (lfs (SN.NodeStateA.inert-AB na))) (SN.NodeStateA.inert-AC na)  , eq ,
  cong (λ q → absNodeA (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tsc (SN.NodeStateA.inert-AB na)) (tss (SN.NodeStateA.inert-AB na)) (kac (SN.NodeStateA.inert-AB na)) (kas (SN.NodeStateA.inert-AB na)) q (lns (SN.NodeStateA.inert-AB na)) (lfc (SN.NodeStateA.inert-AB na)) (lfs (SN.NodeStateA.inert-AB na))) (SN.NodeStateA.inert-AC na))) poseq
finishA-L-abs na eq eqL (blns st poseq refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tsc (SN.NodeStateA.inert-AB na)) (tss (SN.NodeStateA.inert-AB na)) (kac (SN.NodeStateA.inert-AB na)) (kas (SN.NodeStateA.inert-AB na)) (lnc (SN.NodeStateA.inert-AB na)) (lnsHead st) (lfc (SN.NodeStateA.inert-AB na)) (lfs (SN.NodeStateA.inert-AB na))) (SN.NodeStateA.inert-AC na)  , eq ,
  cong (λ q → absNodeA (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tsc (SN.NodeStateA.inert-AB na)) (tss (SN.NodeStateA.inert-AB na)) (kac (SN.NodeStateA.inert-AB na)) (kas (SN.NodeStateA.inert-AB na)) (lnc (SN.NodeStateA.inert-AB na)) q (lfc (SN.NodeStateA.inert-AB na)) (lfs (SN.NodeStateA.inert-AB na))) (SN.NodeStateA.inert-AC na))) poseq
finishA-L-abs na eq eqL (blfc st poseq refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tsc (SN.NodeStateA.inert-AB na)) (tss (SN.NodeStateA.inert-AB na)) (kac (SN.NodeStateA.inert-AB na)) (kas (SN.NodeStateA.inert-AB na)) (lnc (SN.NodeStateA.inert-AB na)) (lns (SN.NodeStateA.inert-AB na)) (lfcHead st) (lfs (SN.NodeStateA.inert-AB na))) (SN.NodeStateA.inert-AC na)  , eq ,
  cong (λ q → absNodeA (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tsc (SN.NodeStateA.inert-AB na)) (tss (SN.NodeStateA.inert-AB na)) (kac (SN.NodeStateA.inert-AB na)) (kas (SN.NodeStateA.inert-AB na)) (lnc (SN.NodeStateA.inert-AB na)) (lns (SN.NodeStateA.inert-AB na)) q (lfs (SN.NodeStateA.inert-AB na))) (SN.NodeStateA.inert-AC na))) poseq
finishA-L-abs na eq eqL (blfs st poseq refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tsc (SN.NodeStateA.inert-AB na)) (tss (SN.NodeStateA.inert-AB na)) (kac (SN.NodeStateA.inert-AB na)) (kas (SN.NodeStateA.inert-AB na)) (lnc (SN.NodeStateA.inert-AB na)) (lns (SN.NodeStateA.inert-AB na)) (lfc (SN.NodeStateA.inert-AB na)) (lfsHead st)) (SN.NodeStateA.inert-AC na)  , eq ,
  cong (λ q → absNodeA (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tsc (SN.NodeStateA.inert-AB na)) (tss (SN.NodeStateA.inert-AB na)) (kac (SN.NodeStateA.inert-AB na)) (kas (SN.NodeStateA.inert-AB na)) (lnc (SN.NodeStateA.inert-AB na)) (lns (SN.NodeStateA.inert-AB na)) (lfc (SN.NodeStateA.inert-AB na)) q) (SN.NodeStateA.inert-AC na))) poseq

-- fused: finishA-R-abs (also emits the abstract collapse `absNodeA` eq)
finishA-R-abs : (na : SN.NodeStateA) {A′ Bd′ M2 : NetProc}
  → A′ ≡ (Bd′ ∥⇘ apiES ⇙ (decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)))
  → Bd′ ≡ (bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ⦀ M2)
  → BundleτR linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) M2
  → Σ[ na′ ∈ SN.NodeStateA ] (A′ ≡ decNodeA na′) × (absNodeA na ≡ absNodeA na′)
finishA-R-abs na eq eqR (bcsc st poseq refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (csHead st) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)  , eq ,
  cong (λ q → absNodeA (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             q (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na))) poseq
finishA-R-abs na eq eqR (bcss st poseq refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (ssHead st) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)  , eq ,
  cong (λ q → absNodeA (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) q (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na))) poseq
finishA-R-abs na eq eqR (bbfc st poseq refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (bcHead st) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)  , eq ,
  cong (λ q → absNodeA (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) q (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na))) poseq
finishA-R-abs na eq eqR (bbfs st poseq refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (bsHead st) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)  , eq ,
  cong (λ q → absNodeA (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) q (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na))) poseq
finishA-R-abs na eq eqR (btsc st poseq refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tcHead st) (tss (SN.NodeStateA.inert-AC na)) (kac (SN.NodeStateA.inert-AC na)) (kas (SN.NodeStateA.inert-AC na)) (lnc (SN.NodeStateA.inert-AC na)) (lns (SN.NodeStateA.inert-AC na)) (lfc (SN.NodeStateA.inert-AC na)) (lfs (SN.NodeStateA.inert-AC na)))  , eq ,
  cong (λ q → absNodeA (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert q (tss (SN.NodeStateA.inert-AC na)) (kac (SN.NodeStateA.inert-AC na)) (kas (SN.NodeStateA.inert-AC na)) (lnc (SN.NodeStateA.inert-AC na)) (lns (SN.NodeStateA.inert-AC na)) (lfc (SN.NodeStateA.inert-AC na)) (lfs (SN.NodeStateA.inert-AC na))))) poseq
finishA-R-abs na eq eqR (btss st poseq refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tsc (SN.NodeStateA.inert-AC na)) (tsHead st) (kac (SN.NodeStateA.inert-AC na)) (kas (SN.NodeStateA.inert-AC na)) (lnc (SN.NodeStateA.inert-AC na)) (lns (SN.NodeStateA.inert-AC na)) (lfc (SN.NodeStateA.inert-AC na)) (lfs (SN.NodeStateA.inert-AC na)))  , eq ,
  cong (λ q → absNodeA (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tsc (SN.NodeStateA.inert-AC na)) q (kac (SN.NodeStateA.inert-AC na)) (kas (SN.NodeStateA.inert-AC na)) (lnc (SN.NodeStateA.inert-AC na)) (lns (SN.NodeStateA.inert-AC na)) (lfc (SN.NodeStateA.inert-AC na)) (lfs (SN.NodeStateA.inert-AC na))))) poseq
finishA-R-abs na eq eqR (bkac st poseq refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tsc (SN.NodeStateA.inert-AC na)) (tss (SN.NodeStateA.inert-AC na)) (kcHead st) (kas (SN.NodeStateA.inert-AC na)) (lnc (SN.NodeStateA.inert-AC na)) (lns (SN.NodeStateA.inert-AC na)) (lfc (SN.NodeStateA.inert-AC na)) (lfs (SN.NodeStateA.inert-AC na)))  , eq ,
  cong (λ q → absNodeA (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tsc (SN.NodeStateA.inert-AC na)) (tss (SN.NodeStateA.inert-AC na)) q (kas (SN.NodeStateA.inert-AC na)) (lnc (SN.NodeStateA.inert-AC na)) (lns (SN.NodeStateA.inert-AC na)) (lfc (SN.NodeStateA.inert-AC na)) (lfs (SN.NodeStateA.inert-AC na))))) poseq
finishA-R-abs na eq eqR (bkas st poseq refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tsc (SN.NodeStateA.inert-AC na)) (tss (SN.NodeStateA.inert-AC na)) (kac (SN.NodeStateA.inert-AC na)) (ksHead st) (lnc (SN.NodeStateA.inert-AC na)) (lns (SN.NodeStateA.inert-AC na)) (lfc (SN.NodeStateA.inert-AC na)) (lfs (SN.NodeStateA.inert-AC na)))  , eq ,
  cong (λ q → absNodeA (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tsc (SN.NodeStateA.inert-AC na)) (tss (SN.NodeStateA.inert-AC na)) (kac (SN.NodeStateA.inert-AC na)) q (lnc (SN.NodeStateA.inert-AC na)) (lns (SN.NodeStateA.inert-AC na)) (lfc (SN.NodeStateA.inert-AC na)) (lfs (SN.NodeStateA.inert-AC na))))) poseq
finishA-R-abs na eq eqR (blnc st poseq refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tsc (SN.NodeStateA.inert-AC na)) (tss (SN.NodeStateA.inert-AC na)) (kac (SN.NodeStateA.inert-AC na)) (kas (SN.NodeStateA.inert-AC na)) (lncHead st) (lns (SN.NodeStateA.inert-AC na)) (lfc (SN.NodeStateA.inert-AC na)) (lfs (SN.NodeStateA.inert-AC na)))  , eq ,
  cong (λ q → absNodeA (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tsc (SN.NodeStateA.inert-AC na)) (tss (SN.NodeStateA.inert-AC na)) (kac (SN.NodeStateA.inert-AC na)) (kas (SN.NodeStateA.inert-AC na)) q (lns (SN.NodeStateA.inert-AC na)) (lfc (SN.NodeStateA.inert-AC na)) (lfs (SN.NodeStateA.inert-AC na))))) poseq
finishA-R-abs na eq eqR (blns st poseq refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tsc (SN.NodeStateA.inert-AC na)) (tss (SN.NodeStateA.inert-AC na)) (kac (SN.NodeStateA.inert-AC na)) (kas (SN.NodeStateA.inert-AC na)) (lnc (SN.NodeStateA.inert-AC na)) (lnsHead st) (lfc (SN.NodeStateA.inert-AC na)) (lfs (SN.NodeStateA.inert-AC na)))  , eq ,
  cong (λ q → absNodeA (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tsc (SN.NodeStateA.inert-AC na)) (tss (SN.NodeStateA.inert-AC na)) (kac (SN.NodeStateA.inert-AC na)) (kas (SN.NodeStateA.inert-AC na)) (lnc (SN.NodeStateA.inert-AC na)) q (lfc (SN.NodeStateA.inert-AC na)) (lfs (SN.NodeStateA.inert-AC na))))) poseq
finishA-R-abs na eq eqR (blfc st poseq refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tsc (SN.NodeStateA.inert-AC na)) (tss (SN.NodeStateA.inert-AC na)) (kac (SN.NodeStateA.inert-AC na)) (kas (SN.NodeStateA.inert-AC na)) (lnc (SN.NodeStateA.inert-AC na)) (lns (SN.NodeStateA.inert-AC na)) (lfcHead st) (lfs (SN.NodeStateA.inert-AC na)))  , eq ,
  cong (λ q → absNodeA (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tsc (SN.NodeStateA.inert-AC na)) (tss (SN.NodeStateA.inert-AC na)) (kac (SN.NodeStateA.inert-AC na)) (kas (SN.NodeStateA.inert-AC na)) (lnc (SN.NodeStateA.inert-AC na)) (lns (SN.NodeStateA.inert-AC na)) q (lfs (SN.NodeStateA.inert-AC na))))) poseq
finishA-R-abs na eq eqR (blfs st poseq refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tsc (SN.NodeStateA.inert-AC na)) (tss (SN.NodeStateA.inert-AC na)) (kac (SN.NodeStateA.inert-AC na)) (kas (SN.NodeStateA.inert-AC na)) (lnc (SN.NodeStateA.inert-AC na)) (lns (SN.NodeStateA.inert-AC na)) (lfc (SN.NodeStateA.inert-AC na)) (lfsHead st))  , eq ,
  cong (λ q → absNodeA (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tsc (SN.NodeStateA.inert-AC na)) (tss (SN.NodeStateA.inert-AC na)) (kac (SN.NodeStateA.inert-AC na)) (kas (SN.NodeStateA.inert-AC na)) (lnc (SN.NodeStateA.inert-AC na)) (lns (SN.NodeStateA.inert-AC na)) (lfc (SN.NodeStateA.inert-AC na)) q))) poseq

-- fused: finishB-L-abs (also emits the abstract collapse `absNodeB` eq)
finishB-L-abs : (nb : SN.NodeStateB) {B′ Bd′ M1 : NetProc}
  → B′ ≡ (Bd′ ∥⇘ apiES ⇙ decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
  → Bd′ ≡ (M1 ⦀ bundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
  → BundleτR linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) M1
  → Σ[ nb′ ∈ SN.NodeStateB ] (B′ ≡ decNodeB nb′) × (absNodeB nb ≡ absNodeB nb′)
finishB-L-abs nb eq eqL (bcsc st poseq refl) rewrite eqL =
  SN.mkNodeB (csHead st) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb)  , eq ,
  cong (λ q → absNodeB (SN.mkNodeB q (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb))) poseq
finishB-L-abs nb eq eqL (bcss st poseq refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (ssHead st) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb)  , eq ,
  cong (λ q → absNodeB (SN.mkNodeB (SN.NodeStateB.csC-AB nb) q (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb))) poseq
finishB-L-abs nb eq eqL (bbfc st poseq refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (bcHead st) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb)  , eq ,
  cong (λ q → absNodeB (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) q (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb))) poseq
finishB-L-abs nb eq eqL (bbfs st poseq refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (bsHead st)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb)  , eq ,
  cong (λ q → absNodeB (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) q
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb))) poseq
finishB-L-abs nb eq eqL (btsc st poseq refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tcHead st) (tss (SN.NodeStateB.inert-AB nb)) (kac (SN.NodeStateB.inert-AB nb)) (kas (SN.NodeStateB.inert-AB nb)) (lnc (SN.NodeStateB.inert-AB nb)) (lns (SN.NodeStateB.inert-AB nb)) (lfc (SN.NodeStateB.inert-AB nb)) (lfs (SN.NodeStateB.inert-AB nb))) (SN.NodeStateB.inert-BD nb)  , eq ,
  cong (λ q → absNodeB (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert q (tss (SN.NodeStateB.inert-AB nb)) (kac (SN.NodeStateB.inert-AB nb)) (kas (SN.NodeStateB.inert-AB nb)) (lnc (SN.NodeStateB.inert-AB nb)) (lns (SN.NodeStateB.inert-AB nb)) (lfc (SN.NodeStateB.inert-AB nb)) (lfs (SN.NodeStateB.inert-AB nb))) (SN.NodeStateB.inert-BD nb))) poseq
finishB-L-abs nb eq eqL (btss st poseq refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tsc (SN.NodeStateB.inert-AB nb)) (tsHead st) (kac (SN.NodeStateB.inert-AB nb)) (kas (SN.NodeStateB.inert-AB nb)) (lnc (SN.NodeStateB.inert-AB nb)) (lns (SN.NodeStateB.inert-AB nb)) (lfc (SN.NodeStateB.inert-AB nb)) (lfs (SN.NodeStateB.inert-AB nb))) (SN.NodeStateB.inert-BD nb)  , eq ,
  cong (λ q → absNodeB (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tsc (SN.NodeStateB.inert-AB nb)) q (kac (SN.NodeStateB.inert-AB nb)) (kas (SN.NodeStateB.inert-AB nb)) (lnc (SN.NodeStateB.inert-AB nb)) (lns (SN.NodeStateB.inert-AB nb)) (lfc (SN.NodeStateB.inert-AB nb)) (lfs (SN.NodeStateB.inert-AB nb))) (SN.NodeStateB.inert-BD nb))) poseq
finishB-L-abs nb eq eqL (bkac st poseq refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tsc (SN.NodeStateB.inert-AB nb)) (tss (SN.NodeStateB.inert-AB nb)) (kcHead st) (kas (SN.NodeStateB.inert-AB nb)) (lnc (SN.NodeStateB.inert-AB nb)) (lns (SN.NodeStateB.inert-AB nb)) (lfc (SN.NodeStateB.inert-AB nb)) (lfs (SN.NodeStateB.inert-AB nb))) (SN.NodeStateB.inert-BD nb)  , eq ,
  cong (λ q → absNodeB (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tsc (SN.NodeStateB.inert-AB nb)) (tss (SN.NodeStateB.inert-AB nb)) q (kas (SN.NodeStateB.inert-AB nb)) (lnc (SN.NodeStateB.inert-AB nb)) (lns (SN.NodeStateB.inert-AB nb)) (lfc (SN.NodeStateB.inert-AB nb)) (lfs (SN.NodeStateB.inert-AB nb))) (SN.NodeStateB.inert-BD nb))) poseq
finishB-L-abs nb eq eqL (bkas st poseq refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tsc (SN.NodeStateB.inert-AB nb)) (tss (SN.NodeStateB.inert-AB nb)) (kac (SN.NodeStateB.inert-AB nb)) (ksHead st) (lnc (SN.NodeStateB.inert-AB nb)) (lns (SN.NodeStateB.inert-AB nb)) (lfc (SN.NodeStateB.inert-AB nb)) (lfs (SN.NodeStateB.inert-AB nb))) (SN.NodeStateB.inert-BD nb)  , eq ,
  cong (λ q → absNodeB (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tsc (SN.NodeStateB.inert-AB nb)) (tss (SN.NodeStateB.inert-AB nb)) (kac (SN.NodeStateB.inert-AB nb)) q (lnc (SN.NodeStateB.inert-AB nb)) (lns (SN.NodeStateB.inert-AB nb)) (lfc (SN.NodeStateB.inert-AB nb)) (lfs (SN.NodeStateB.inert-AB nb))) (SN.NodeStateB.inert-BD nb))) poseq
finishB-L-abs nb eq eqL (blnc st poseq refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tsc (SN.NodeStateB.inert-AB nb)) (tss (SN.NodeStateB.inert-AB nb)) (kac (SN.NodeStateB.inert-AB nb)) (kas (SN.NodeStateB.inert-AB nb)) (lncHead st) (lns (SN.NodeStateB.inert-AB nb)) (lfc (SN.NodeStateB.inert-AB nb)) (lfs (SN.NodeStateB.inert-AB nb))) (SN.NodeStateB.inert-BD nb)  , eq ,
  cong (λ q → absNodeB (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tsc (SN.NodeStateB.inert-AB nb)) (tss (SN.NodeStateB.inert-AB nb)) (kac (SN.NodeStateB.inert-AB nb)) (kas (SN.NodeStateB.inert-AB nb)) q (lns (SN.NodeStateB.inert-AB nb)) (lfc (SN.NodeStateB.inert-AB nb)) (lfs (SN.NodeStateB.inert-AB nb))) (SN.NodeStateB.inert-BD nb))) poseq
finishB-L-abs nb eq eqL (blns st poseq refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tsc (SN.NodeStateB.inert-AB nb)) (tss (SN.NodeStateB.inert-AB nb)) (kac (SN.NodeStateB.inert-AB nb)) (kas (SN.NodeStateB.inert-AB nb)) (lnc (SN.NodeStateB.inert-AB nb)) (lnsHead st) (lfc (SN.NodeStateB.inert-AB nb)) (lfs (SN.NodeStateB.inert-AB nb))) (SN.NodeStateB.inert-BD nb)  , eq ,
  cong (λ q → absNodeB (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tsc (SN.NodeStateB.inert-AB nb)) (tss (SN.NodeStateB.inert-AB nb)) (kac (SN.NodeStateB.inert-AB nb)) (kas (SN.NodeStateB.inert-AB nb)) (lnc (SN.NodeStateB.inert-AB nb)) q (lfc (SN.NodeStateB.inert-AB nb)) (lfs (SN.NodeStateB.inert-AB nb))) (SN.NodeStateB.inert-BD nb))) poseq
finishB-L-abs nb eq eqL (blfc st poseq refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tsc (SN.NodeStateB.inert-AB nb)) (tss (SN.NodeStateB.inert-AB nb)) (kac (SN.NodeStateB.inert-AB nb)) (kas (SN.NodeStateB.inert-AB nb)) (lnc (SN.NodeStateB.inert-AB nb)) (lns (SN.NodeStateB.inert-AB nb)) (lfcHead st) (lfs (SN.NodeStateB.inert-AB nb))) (SN.NodeStateB.inert-BD nb)  , eq ,
  cong (λ q → absNodeB (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tsc (SN.NodeStateB.inert-AB nb)) (tss (SN.NodeStateB.inert-AB nb)) (kac (SN.NodeStateB.inert-AB nb)) (kas (SN.NodeStateB.inert-AB nb)) (lnc (SN.NodeStateB.inert-AB nb)) (lns (SN.NodeStateB.inert-AB nb)) q (lfs (SN.NodeStateB.inert-AB nb))) (SN.NodeStateB.inert-BD nb))) poseq
finishB-L-abs nb eq eqL (blfs st poseq refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tsc (SN.NodeStateB.inert-AB nb)) (tss (SN.NodeStateB.inert-AB nb)) (kac (SN.NodeStateB.inert-AB nb)) (kas (SN.NodeStateB.inert-AB nb)) (lnc (SN.NodeStateB.inert-AB nb)) (lns (SN.NodeStateB.inert-AB nb)) (lfc (SN.NodeStateB.inert-AB nb)) (lfsHead st)) (SN.NodeStateB.inert-BD nb)  , eq ,
  cong (λ q → absNodeB (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tsc (SN.NodeStateB.inert-AB nb)) (tss (SN.NodeStateB.inert-AB nb)) (kac (SN.NodeStateB.inert-AB nb)) (kas (SN.NodeStateB.inert-AB nb)) (lnc (SN.NodeStateB.inert-AB nb)) (lns (SN.NodeStateB.inert-AB nb)) (lfc (SN.NodeStateB.inert-AB nb)) q) (SN.NodeStateB.inert-BD nb))) poseq

-- fused: finishB-R-abs (also emits the abstract collapse `absNodeB` eq)
finishB-R-abs : (nb : SN.NodeStateB) {B′ Bd′ M2 : NetProc}
  → B′ ≡ (Bd′ ∥⇘ apiES ⇙ decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
  → Bd′ ≡ (bundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ⦀ M2)
  → BundleτR linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) M2
  → Σ[ nb′ ∈ SN.NodeStateB ] (B′ ≡ decNodeB nb′) × (absNodeB nb ≡ absNodeB nb′)
finishB-R-abs nb eq eqR (bcsc st poseq refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (csHead st) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb)  , eq ,
  cong (λ q → absNodeB (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             q (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb))) poseq
finishB-R-abs nb eq eqR (bcss st poseq refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (ssHead st) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb)  , eq ,
  cong (λ q → absNodeB (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) q (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb))) poseq
finishB-R-abs nb eq eqR (bbfc st poseq refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (bcHead st) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb)  , eq ,
  cong (λ q → absNodeB (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) q (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb))) poseq
finishB-R-abs nb eq eqR (bbfs st poseq refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (bsHead st) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb)  , eq ,
  cong (λ q → absNodeB (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) q (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb))) poseq
finishB-R-abs nb eq eqR (btsc st poseq refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tcHead st) (tss (SN.NodeStateB.inert-BD nb)) (kac (SN.NodeStateB.inert-BD nb)) (kas (SN.NodeStateB.inert-BD nb)) (lnc (SN.NodeStateB.inert-BD nb)) (lns (SN.NodeStateB.inert-BD nb)) (lfc (SN.NodeStateB.inert-BD nb)) (lfs (SN.NodeStateB.inert-BD nb)))  , eq ,
  cong (λ q → absNodeB (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert q (tss (SN.NodeStateB.inert-BD nb)) (kac (SN.NodeStateB.inert-BD nb)) (kas (SN.NodeStateB.inert-BD nb)) (lnc (SN.NodeStateB.inert-BD nb)) (lns (SN.NodeStateB.inert-BD nb)) (lfc (SN.NodeStateB.inert-BD nb)) (lfs (SN.NodeStateB.inert-BD nb))))) poseq
finishB-R-abs nb eq eqR (btss st poseq refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tsc (SN.NodeStateB.inert-BD nb)) (tsHead st) (kac (SN.NodeStateB.inert-BD nb)) (kas (SN.NodeStateB.inert-BD nb)) (lnc (SN.NodeStateB.inert-BD nb)) (lns (SN.NodeStateB.inert-BD nb)) (lfc (SN.NodeStateB.inert-BD nb)) (lfs (SN.NodeStateB.inert-BD nb)))  , eq ,
  cong (λ q → absNodeB (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tsc (SN.NodeStateB.inert-BD nb)) q (kac (SN.NodeStateB.inert-BD nb)) (kas (SN.NodeStateB.inert-BD nb)) (lnc (SN.NodeStateB.inert-BD nb)) (lns (SN.NodeStateB.inert-BD nb)) (lfc (SN.NodeStateB.inert-BD nb)) (lfs (SN.NodeStateB.inert-BD nb))))) poseq
finishB-R-abs nb eq eqR (bkac st poseq refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tsc (SN.NodeStateB.inert-BD nb)) (tss (SN.NodeStateB.inert-BD nb)) (kcHead st) (kas (SN.NodeStateB.inert-BD nb)) (lnc (SN.NodeStateB.inert-BD nb)) (lns (SN.NodeStateB.inert-BD nb)) (lfc (SN.NodeStateB.inert-BD nb)) (lfs (SN.NodeStateB.inert-BD nb)))  , eq ,
  cong (λ q → absNodeB (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tsc (SN.NodeStateB.inert-BD nb)) (tss (SN.NodeStateB.inert-BD nb)) q (kas (SN.NodeStateB.inert-BD nb)) (lnc (SN.NodeStateB.inert-BD nb)) (lns (SN.NodeStateB.inert-BD nb)) (lfc (SN.NodeStateB.inert-BD nb)) (lfs (SN.NodeStateB.inert-BD nb))))) poseq
finishB-R-abs nb eq eqR (bkas st poseq refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tsc (SN.NodeStateB.inert-BD nb)) (tss (SN.NodeStateB.inert-BD nb)) (kac (SN.NodeStateB.inert-BD nb)) (ksHead st) (lnc (SN.NodeStateB.inert-BD nb)) (lns (SN.NodeStateB.inert-BD nb)) (lfc (SN.NodeStateB.inert-BD nb)) (lfs (SN.NodeStateB.inert-BD nb)))  , eq ,
  cong (λ q → absNodeB (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tsc (SN.NodeStateB.inert-BD nb)) (tss (SN.NodeStateB.inert-BD nb)) (kac (SN.NodeStateB.inert-BD nb)) q (lnc (SN.NodeStateB.inert-BD nb)) (lns (SN.NodeStateB.inert-BD nb)) (lfc (SN.NodeStateB.inert-BD nb)) (lfs (SN.NodeStateB.inert-BD nb))))) poseq
finishB-R-abs nb eq eqR (blnc st poseq refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tsc (SN.NodeStateB.inert-BD nb)) (tss (SN.NodeStateB.inert-BD nb)) (kac (SN.NodeStateB.inert-BD nb)) (kas (SN.NodeStateB.inert-BD nb)) (lncHead st) (lns (SN.NodeStateB.inert-BD nb)) (lfc (SN.NodeStateB.inert-BD nb)) (lfs (SN.NodeStateB.inert-BD nb)))  , eq ,
  cong (λ q → absNodeB (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tsc (SN.NodeStateB.inert-BD nb)) (tss (SN.NodeStateB.inert-BD nb)) (kac (SN.NodeStateB.inert-BD nb)) (kas (SN.NodeStateB.inert-BD nb)) q (lns (SN.NodeStateB.inert-BD nb)) (lfc (SN.NodeStateB.inert-BD nb)) (lfs (SN.NodeStateB.inert-BD nb))))) poseq
finishB-R-abs nb eq eqR (blns st poseq refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tsc (SN.NodeStateB.inert-BD nb)) (tss (SN.NodeStateB.inert-BD nb)) (kac (SN.NodeStateB.inert-BD nb)) (kas (SN.NodeStateB.inert-BD nb)) (lnc (SN.NodeStateB.inert-BD nb)) (lnsHead st) (lfc (SN.NodeStateB.inert-BD nb)) (lfs (SN.NodeStateB.inert-BD nb)))  , eq ,
  cong (λ q → absNodeB (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tsc (SN.NodeStateB.inert-BD nb)) (tss (SN.NodeStateB.inert-BD nb)) (kac (SN.NodeStateB.inert-BD nb)) (kas (SN.NodeStateB.inert-BD nb)) (lnc (SN.NodeStateB.inert-BD nb)) q (lfc (SN.NodeStateB.inert-BD nb)) (lfs (SN.NodeStateB.inert-BD nb))))) poseq
finishB-R-abs nb eq eqR (blfc st poseq refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tsc (SN.NodeStateB.inert-BD nb)) (tss (SN.NodeStateB.inert-BD nb)) (kac (SN.NodeStateB.inert-BD nb)) (kas (SN.NodeStateB.inert-BD nb)) (lnc (SN.NodeStateB.inert-BD nb)) (lns (SN.NodeStateB.inert-BD nb)) (lfcHead st) (lfs (SN.NodeStateB.inert-BD nb)))  , eq ,
  cong (λ q → absNodeB (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tsc (SN.NodeStateB.inert-BD nb)) (tss (SN.NodeStateB.inert-BD nb)) (kac (SN.NodeStateB.inert-BD nb)) (kas (SN.NodeStateB.inert-BD nb)) (lnc (SN.NodeStateB.inert-BD nb)) (lns (SN.NodeStateB.inert-BD nb)) q (lfs (SN.NodeStateB.inert-BD nb))))) poseq
finishB-R-abs nb eq eqR (blfs st poseq refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tsc (SN.NodeStateB.inert-BD nb)) (tss (SN.NodeStateB.inert-BD nb)) (kac (SN.NodeStateB.inert-BD nb)) (kas (SN.NodeStateB.inert-BD nb)) (lnc (SN.NodeStateB.inert-BD nb)) (lns (SN.NodeStateB.inert-BD nb)) (lfc (SN.NodeStateB.inert-BD nb)) (lfsHead st))  , eq ,
  cong (λ q → absNodeB (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tsc (SN.NodeStateB.inert-BD nb)) (tss (SN.NodeStateB.inert-BD nb)) (kac (SN.NodeStateB.inert-BD nb)) (kas (SN.NodeStateB.inert-BD nb)) (lnc (SN.NodeStateB.inert-BD nb)) (lns (SN.NodeStateB.inert-BD nb)) (lfc (SN.NodeStateB.inert-BD nb)) q))) poseq

-- fused: finishC-L-abs (also emits the abstract collapse `absNodeC` eq)
finishC-L-abs : (nc : SN.NodeStateC) {C′ Bd′ M1 : NetProc}
  → C′ ≡ (Bd′ ∥⇘ apiES ⇙ decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
  → Bd′ ≡ (M1 ⦀ bundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
  → BundleτR linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) M1
  → Σ[ nc′ ∈ SN.NodeStateC ] (C′ ≡ decNodeC nc′) × (absNodeC nc ≡ absNodeC nc′)
finishC-L-abs nc eq eqL (bcsc st poseq refl) rewrite eqL =
  SN.mkNodeC (csHead st) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc)  , eq ,
  cong (λ q → absNodeC (SN.mkNodeC q (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc))) poseq
finishC-L-abs nc eq eqL (bcss st poseq refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (ssHead st) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc)  , eq ,
  cong (λ q → absNodeC (SN.mkNodeC (SN.NodeStateC.csC-AC nc) q (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc))) poseq
finishC-L-abs nc eq eqL (bbfc st poseq refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (bcHead st) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc)  , eq ,
  cong (λ q → absNodeC (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) q (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc))) poseq
finishC-L-abs nc eq eqL (bbfs st poseq refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (bsHead st)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc)  , eq ,
  cong (λ q → absNodeC (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) q
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc))) poseq
finishC-L-abs nc eq eqL (btsc st poseq refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tcHead st) (tss (SN.NodeStateC.inert-AC nc)) (kac (SN.NodeStateC.inert-AC nc)) (kas (SN.NodeStateC.inert-AC nc)) (lnc (SN.NodeStateC.inert-AC nc)) (lns (SN.NodeStateC.inert-AC nc)) (lfc (SN.NodeStateC.inert-AC nc)) (lfs (SN.NodeStateC.inert-AC nc))) (SN.NodeStateC.inert-CD nc)  , eq ,
  cong (λ q → absNodeC (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert q (tss (SN.NodeStateC.inert-AC nc)) (kac (SN.NodeStateC.inert-AC nc)) (kas (SN.NodeStateC.inert-AC nc)) (lnc (SN.NodeStateC.inert-AC nc)) (lns (SN.NodeStateC.inert-AC nc)) (lfc (SN.NodeStateC.inert-AC nc)) (lfs (SN.NodeStateC.inert-AC nc))) (SN.NodeStateC.inert-CD nc))) poseq
finishC-L-abs nc eq eqL (btss st poseq refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tsc (SN.NodeStateC.inert-AC nc)) (tsHead st) (kac (SN.NodeStateC.inert-AC nc)) (kas (SN.NodeStateC.inert-AC nc)) (lnc (SN.NodeStateC.inert-AC nc)) (lns (SN.NodeStateC.inert-AC nc)) (lfc (SN.NodeStateC.inert-AC nc)) (lfs (SN.NodeStateC.inert-AC nc))) (SN.NodeStateC.inert-CD nc)  , eq ,
  cong (λ q → absNodeC (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tsc (SN.NodeStateC.inert-AC nc)) q (kac (SN.NodeStateC.inert-AC nc)) (kas (SN.NodeStateC.inert-AC nc)) (lnc (SN.NodeStateC.inert-AC nc)) (lns (SN.NodeStateC.inert-AC nc)) (lfc (SN.NodeStateC.inert-AC nc)) (lfs (SN.NodeStateC.inert-AC nc))) (SN.NodeStateC.inert-CD nc))) poseq
finishC-L-abs nc eq eqL (bkac st poseq refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tsc (SN.NodeStateC.inert-AC nc)) (tss (SN.NodeStateC.inert-AC nc)) (kcHead st) (kas (SN.NodeStateC.inert-AC nc)) (lnc (SN.NodeStateC.inert-AC nc)) (lns (SN.NodeStateC.inert-AC nc)) (lfc (SN.NodeStateC.inert-AC nc)) (lfs (SN.NodeStateC.inert-AC nc))) (SN.NodeStateC.inert-CD nc)  , eq ,
  cong (λ q → absNodeC (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tsc (SN.NodeStateC.inert-AC nc)) (tss (SN.NodeStateC.inert-AC nc)) q (kas (SN.NodeStateC.inert-AC nc)) (lnc (SN.NodeStateC.inert-AC nc)) (lns (SN.NodeStateC.inert-AC nc)) (lfc (SN.NodeStateC.inert-AC nc)) (lfs (SN.NodeStateC.inert-AC nc))) (SN.NodeStateC.inert-CD nc))) poseq
finishC-L-abs nc eq eqL (bkas st poseq refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tsc (SN.NodeStateC.inert-AC nc)) (tss (SN.NodeStateC.inert-AC nc)) (kac (SN.NodeStateC.inert-AC nc)) (ksHead st) (lnc (SN.NodeStateC.inert-AC nc)) (lns (SN.NodeStateC.inert-AC nc)) (lfc (SN.NodeStateC.inert-AC nc)) (lfs (SN.NodeStateC.inert-AC nc))) (SN.NodeStateC.inert-CD nc)  , eq ,
  cong (λ q → absNodeC (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tsc (SN.NodeStateC.inert-AC nc)) (tss (SN.NodeStateC.inert-AC nc)) (kac (SN.NodeStateC.inert-AC nc)) q (lnc (SN.NodeStateC.inert-AC nc)) (lns (SN.NodeStateC.inert-AC nc)) (lfc (SN.NodeStateC.inert-AC nc)) (lfs (SN.NodeStateC.inert-AC nc))) (SN.NodeStateC.inert-CD nc))) poseq
finishC-L-abs nc eq eqL (blnc st poseq refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tsc (SN.NodeStateC.inert-AC nc)) (tss (SN.NodeStateC.inert-AC nc)) (kac (SN.NodeStateC.inert-AC nc)) (kas (SN.NodeStateC.inert-AC nc)) (lncHead st) (lns (SN.NodeStateC.inert-AC nc)) (lfc (SN.NodeStateC.inert-AC nc)) (lfs (SN.NodeStateC.inert-AC nc))) (SN.NodeStateC.inert-CD nc)  , eq ,
  cong (λ q → absNodeC (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tsc (SN.NodeStateC.inert-AC nc)) (tss (SN.NodeStateC.inert-AC nc)) (kac (SN.NodeStateC.inert-AC nc)) (kas (SN.NodeStateC.inert-AC nc)) q (lns (SN.NodeStateC.inert-AC nc)) (lfc (SN.NodeStateC.inert-AC nc)) (lfs (SN.NodeStateC.inert-AC nc))) (SN.NodeStateC.inert-CD nc))) poseq
finishC-L-abs nc eq eqL (blns st poseq refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tsc (SN.NodeStateC.inert-AC nc)) (tss (SN.NodeStateC.inert-AC nc)) (kac (SN.NodeStateC.inert-AC nc)) (kas (SN.NodeStateC.inert-AC nc)) (lnc (SN.NodeStateC.inert-AC nc)) (lnsHead st) (lfc (SN.NodeStateC.inert-AC nc)) (lfs (SN.NodeStateC.inert-AC nc))) (SN.NodeStateC.inert-CD nc)  , eq ,
  cong (λ q → absNodeC (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tsc (SN.NodeStateC.inert-AC nc)) (tss (SN.NodeStateC.inert-AC nc)) (kac (SN.NodeStateC.inert-AC nc)) (kas (SN.NodeStateC.inert-AC nc)) (lnc (SN.NodeStateC.inert-AC nc)) q (lfc (SN.NodeStateC.inert-AC nc)) (lfs (SN.NodeStateC.inert-AC nc))) (SN.NodeStateC.inert-CD nc))) poseq
finishC-L-abs nc eq eqL (blfc st poseq refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tsc (SN.NodeStateC.inert-AC nc)) (tss (SN.NodeStateC.inert-AC nc)) (kac (SN.NodeStateC.inert-AC nc)) (kas (SN.NodeStateC.inert-AC nc)) (lnc (SN.NodeStateC.inert-AC nc)) (lns (SN.NodeStateC.inert-AC nc)) (lfcHead st) (lfs (SN.NodeStateC.inert-AC nc))) (SN.NodeStateC.inert-CD nc)  , eq ,
  cong (λ q → absNodeC (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tsc (SN.NodeStateC.inert-AC nc)) (tss (SN.NodeStateC.inert-AC nc)) (kac (SN.NodeStateC.inert-AC nc)) (kas (SN.NodeStateC.inert-AC nc)) (lnc (SN.NodeStateC.inert-AC nc)) (lns (SN.NodeStateC.inert-AC nc)) q (lfs (SN.NodeStateC.inert-AC nc))) (SN.NodeStateC.inert-CD nc))) poseq
finishC-L-abs nc eq eqL (blfs st poseq refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tsc (SN.NodeStateC.inert-AC nc)) (tss (SN.NodeStateC.inert-AC nc)) (kac (SN.NodeStateC.inert-AC nc)) (kas (SN.NodeStateC.inert-AC nc)) (lnc (SN.NodeStateC.inert-AC nc)) (lns (SN.NodeStateC.inert-AC nc)) (lfc (SN.NodeStateC.inert-AC nc)) (lfsHead st)) (SN.NodeStateC.inert-CD nc)  , eq ,
  cong (λ q → absNodeC (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tsc (SN.NodeStateC.inert-AC nc)) (tss (SN.NodeStateC.inert-AC nc)) (kac (SN.NodeStateC.inert-AC nc)) (kas (SN.NodeStateC.inert-AC nc)) (lnc (SN.NodeStateC.inert-AC nc)) (lns (SN.NodeStateC.inert-AC nc)) (lfc (SN.NodeStateC.inert-AC nc)) q) (SN.NodeStateC.inert-CD nc))) poseq

-- fused: finishC-R-abs (also emits the abstract collapse `absNodeC` eq)
finishC-R-abs : (nc : SN.NodeStateC) {C′ Bd′ M2 : NetProc}
  → C′ ≡ (Bd′ ∥⇘ apiES ⇙ decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
  → Bd′ ≡ (bundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ⦀ M2)
  → BundleτR linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) M2
  → Σ[ nc′ ∈ SN.NodeStateC ] (C′ ≡ decNodeC nc′) × (absNodeC nc ≡ absNodeC nc′)
finishC-R-abs nc eq eqR (bcsc st poseq refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (csHead st) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc)  , eq ,
  cong (λ q → absNodeC (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             q (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc))) poseq
finishC-R-abs nc eq eqR (bcss st poseq refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (ssHead st) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc)  , eq ,
  cong (λ q → absNodeC (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) q (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc))) poseq
finishC-R-abs nc eq eqR (bbfc st poseq refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (bcHead st) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc)  , eq ,
  cong (λ q → absNodeC (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) q (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc))) poseq
finishC-R-abs nc eq eqR (bbfs st poseq refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (bsHead st) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc)  , eq ,
  cong (λ q → absNodeC (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) q (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc))) poseq
finishC-R-abs nc eq eqR (btsc st poseq refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tcHead st) (tss (SN.NodeStateC.inert-CD nc)) (kac (SN.NodeStateC.inert-CD nc)) (kas (SN.NodeStateC.inert-CD nc)) (lnc (SN.NodeStateC.inert-CD nc)) (lns (SN.NodeStateC.inert-CD nc)) (lfc (SN.NodeStateC.inert-CD nc)) (lfs (SN.NodeStateC.inert-CD nc)))  , eq ,
  cong (λ q → absNodeC (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert q (tss (SN.NodeStateC.inert-CD nc)) (kac (SN.NodeStateC.inert-CD nc)) (kas (SN.NodeStateC.inert-CD nc)) (lnc (SN.NodeStateC.inert-CD nc)) (lns (SN.NodeStateC.inert-CD nc)) (lfc (SN.NodeStateC.inert-CD nc)) (lfs (SN.NodeStateC.inert-CD nc))))) poseq
finishC-R-abs nc eq eqR (btss st poseq refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tsc (SN.NodeStateC.inert-CD nc)) (tsHead st) (kac (SN.NodeStateC.inert-CD nc)) (kas (SN.NodeStateC.inert-CD nc)) (lnc (SN.NodeStateC.inert-CD nc)) (lns (SN.NodeStateC.inert-CD nc)) (lfc (SN.NodeStateC.inert-CD nc)) (lfs (SN.NodeStateC.inert-CD nc)))  , eq ,
  cong (λ q → absNodeC (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tsc (SN.NodeStateC.inert-CD nc)) q (kac (SN.NodeStateC.inert-CD nc)) (kas (SN.NodeStateC.inert-CD nc)) (lnc (SN.NodeStateC.inert-CD nc)) (lns (SN.NodeStateC.inert-CD nc)) (lfc (SN.NodeStateC.inert-CD nc)) (lfs (SN.NodeStateC.inert-CD nc))))) poseq
finishC-R-abs nc eq eqR (bkac st poseq refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tsc (SN.NodeStateC.inert-CD nc)) (tss (SN.NodeStateC.inert-CD nc)) (kcHead st) (kas (SN.NodeStateC.inert-CD nc)) (lnc (SN.NodeStateC.inert-CD nc)) (lns (SN.NodeStateC.inert-CD nc)) (lfc (SN.NodeStateC.inert-CD nc)) (lfs (SN.NodeStateC.inert-CD nc)))  , eq ,
  cong (λ q → absNodeC (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tsc (SN.NodeStateC.inert-CD nc)) (tss (SN.NodeStateC.inert-CD nc)) q (kas (SN.NodeStateC.inert-CD nc)) (lnc (SN.NodeStateC.inert-CD nc)) (lns (SN.NodeStateC.inert-CD nc)) (lfc (SN.NodeStateC.inert-CD nc)) (lfs (SN.NodeStateC.inert-CD nc))))) poseq
finishC-R-abs nc eq eqR (bkas st poseq refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tsc (SN.NodeStateC.inert-CD nc)) (tss (SN.NodeStateC.inert-CD nc)) (kac (SN.NodeStateC.inert-CD nc)) (ksHead st) (lnc (SN.NodeStateC.inert-CD nc)) (lns (SN.NodeStateC.inert-CD nc)) (lfc (SN.NodeStateC.inert-CD nc)) (lfs (SN.NodeStateC.inert-CD nc)))  , eq ,
  cong (λ q → absNodeC (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tsc (SN.NodeStateC.inert-CD nc)) (tss (SN.NodeStateC.inert-CD nc)) (kac (SN.NodeStateC.inert-CD nc)) q (lnc (SN.NodeStateC.inert-CD nc)) (lns (SN.NodeStateC.inert-CD nc)) (lfc (SN.NodeStateC.inert-CD nc)) (lfs (SN.NodeStateC.inert-CD nc))))) poseq
finishC-R-abs nc eq eqR (blnc st poseq refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tsc (SN.NodeStateC.inert-CD nc)) (tss (SN.NodeStateC.inert-CD nc)) (kac (SN.NodeStateC.inert-CD nc)) (kas (SN.NodeStateC.inert-CD nc)) (lncHead st) (lns (SN.NodeStateC.inert-CD nc)) (lfc (SN.NodeStateC.inert-CD nc)) (lfs (SN.NodeStateC.inert-CD nc)))  , eq ,
  cong (λ q → absNodeC (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tsc (SN.NodeStateC.inert-CD nc)) (tss (SN.NodeStateC.inert-CD nc)) (kac (SN.NodeStateC.inert-CD nc)) (kas (SN.NodeStateC.inert-CD nc)) q (lns (SN.NodeStateC.inert-CD nc)) (lfc (SN.NodeStateC.inert-CD nc)) (lfs (SN.NodeStateC.inert-CD nc))))) poseq
finishC-R-abs nc eq eqR (blns st poseq refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tsc (SN.NodeStateC.inert-CD nc)) (tss (SN.NodeStateC.inert-CD nc)) (kac (SN.NodeStateC.inert-CD nc)) (kas (SN.NodeStateC.inert-CD nc)) (lnc (SN.NodeStateC.inert-CD nc)) (lnsHead st) (lfc (SN.NodeStateC.inert-CD nc)) (lfs (SN.NodeStateC.inert-CD nc)))  , eq ,
  cong (λ q → absNodeC (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tsc (SN.NodeStateC.inert-CD nc)) (tss (SN.NodeStateC.inert-CD nc)) (kac (SN.NodeStateC.inert-CD nc)) (kas (SN.NodeStateC.inert-CD nc)) (lnc (SN.NodeStateC.inert-CD nc)) q (lfc (SN.NodeStateC.inert-CD nc)) (lfs (SN.NodeStateC.inert-CD nc))))) poseq
finishC-R-abs nc eq eqR (blfc st poseq refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tsc (SN.NodeStateC.inert-CD nc)) (tss (SN.NodeStateC.inert-CD nc)) (kac (SN.NodeStateC.inert-CD nc)) (kas (SN.NodeStateC.inert-CD nc)) (lnc (SN.NodeStateC.inert-CD nc)) (lns (SN.NodeStateC.inert-CD nc)) (lfcHead st) (lfs (SN.NodeStateC.inert-CD nc)))  , eq ,
  cong (λ q → absNodeC (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tsc (SN.NodeStateC.inert-CD nc)) (tss (SN.NodeStateC.inert-CD nc)) (kac (SN.NodeStateC.inert-CD nc)) (kas (SN.NodeStateC.inert-CD nc)) (lnc (SN.NodeStateC.inert-CD nc)) (lns (SN.NodeStateC.inert-CD nc)) q (lfs (SN.NodeStateC.inert-CD nc))))) poseq
finishC-R-abs nc eq eqR (blfs st poseq refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tsc (SN.NodeStateC.inert-CD nc)) (tss (SN.NodeStateC.inert-CD nc)) (kac (SN.NodeStateC.inert-CD nc)) (kas (SN.NodeStateC.inert-CD nc)) (lnc (SN.NodeStateC.inert-CD nc)) (lns (SN.NodeStateC.inert-CD nc)) (lfc (SN.NodeStateC.inert-CD nc)) (lfsHead st))  , eq ,
  cong (λ q → absNodeC (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tsc (SN.NodeStateC.inert-CD nc)) (tss (SN.NodeStateC.inert-CD nc)) (kac (SN.NodeStateC.inert-CD nc)) (kas (SN.NodeStateC.inert-CD nc)) (lnc (SN.NodeStateC.inert-CD nc)) (lns (SN.NodeStateC.inert-CD nc)) (lfc (SN.NodeStateC.inert-CD nc)) q))) poseq

-- fused: finishD-L-abs (also emits the abstract collapse `absNodeD` eq)
finishD-L-abs : (nd : SN.NodeStateD) {D′ Bd′ M1 : NetProc}
  → D′ ≡ (Bd′ ∥⇘ apiES ⇙ (decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ decConsD linkCD (SN.NodeStateD.cons-CD nd)))
  → Bd′ ≡ (M1 ⦀ bundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
  → BundleτR linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) M1
  → Σ[ nd′ ∈ SN.NodeStateD ] (D′ ≡ decNodeD nd′) × (absNodeD nd ≡ absNodeD nd′)
finishD-L-abs nd eq eqL (bcsc st poseq refl) rewrite eqL =
  SN.mkNodeD (csHead st) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd)  , eq ,
  cong (λ q → absNodeD (SN.mkNodeD q (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd))) poseq
finishD-L-abs nd eq eqL (bcss st poseq refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (ssHead st) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd)  , eq ,
  cong (λ q → absNodeD (SN.mkNodeD (SN.NodeStateD.csC-BD nd) q (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd))) poseq
finishD-L-abs nd eq eqL (bbfc st poseq refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (bcHead st) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd)  , eq ,
  cong (λ q → absNodeD (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) q (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd))) poseq
finishD-L-abs nd eq eqL (bbfs st poseq refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (bsHead st) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd)  , eq ,
  cong (λ q → absNodeD (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) q (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd))) poseq
finishD-L-abs nd eq eqL (btsc st poseq refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tcHead st) (tss (SN.NodeStateD.inert-BD nd)) (kac (SN.NodeStateD.inert-BD nd)) (kas (SN.NodeStateD.inert-BD nd)) (lnc (SN.NodeStateD.inert-BD nd)) (lns (SN.NodeStateD.inert-BD nd)) (lfc (SN.NodeStateD.inert-BD nd)) (lfs (SN.NodeStateD.inert-BD nd))) (SN.NodeStateD.inert-CD nd)  , eq ,
  cong (λ q → absNodeD (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert q (tss (SN.NodeStateD.inert-BD nd)) (kac (SN.NodeStateD.inert-BD nd)) (kas (SN.NodeStateD.inert-BD nd)) (lnc (SN.NodeStateD.inert-BD nd)) (lns (SN.NodeStateD.inert-BD nd)) (lfc (SN.NodeStateD.inert-BD nd)) (lfs (SN.NodeStateD.inert-BD nd))) (SN.NodeStateD.inert-CD nd))) poseq
finishD-L-abs nd eq eqL (btss st poseq refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tsc (SN.NodeStateD.inert-BD nd)) (tsHead st) (kac (SN.NodeStateD.inert-BD nd)) (kas (SN.NodeStateD.inert-BD nd)) (lnc (SN.NodeStateD.inert-BD nd)) (lns (SN.NodeStateD.inert-BD nd)) (lfc (SN.NodeStateD.inert-BD nd)) (lfs (SN.NodeStateD.inert-BD nd))) (SN.NodeStateD.inert-CD nd)  , eq ,
  cong (λ q → absNodeD (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tsc (SN.NodeStateD.inert-BD nd)) q (kac (SN.NodeStateD.inert-BD nd)) (kas (SN.NodeStateD.inert-BD nd)) (lnc (SN.NodeStateD.inert-BD nd)) (lns (SN.NodeStateD.inert-BD nd)) (lfc (SN.NodeStateD.inert-BD nd)) (lfs (SN.NodeStateD.inert-BD nd))) (SN.NodeStateD.inert-CD nd))) poseq
finishD-L-abs nd eq eqL (bkac st poseq refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tsc (SN.NodeStateD.inert-BD nd)) (tss (SN.NodeStateD.inert-BD nd)) (kcHead st) (kas (SN.NodeStateD.inert-BD nd)) (lnc (SN.NodeStateD.inert-BD nd)) (lns (SN.NodeStateD.inert-BD nd)) (lfc (SN.NodeStateD.inert-BD nd)) (lfs (SN.NodeStateD.inert-BD nd))) (SN.NodeStateD.inert-CD nd)  , eq ,
  cong (λ q → absNodeD (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tsc (SN.NodeStateD.inert-BD nd)) (tss (SN.NodeStateD.inert-BD nd)) q (kas (SN.NodeStateD.inert-BD nd)) (lnc (SN.NodeStateD.inert-BD nd)) (lns (SN.NodeStateD.inert-BD nd)) (lfc (SN.NodeStateD.inert-BD nd)) (lfs (SN.NodeStateD.inert-BD nd))) (SN.NodeStateD.inert-CD nd))) poseq
finishD-L-abs nd eq eqL (bkas st poseq refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tsc (SN.NodeStateD.inert-BD nd)) (tss (SN.NodeStateD.inert-BD nd)) (kac (SN.NodeStateD.inert-BD nd)) (ksHead st) (lnc (SN.NodeStateD.inert-BD nd)) (lns (SN.NodeStateD.inert-BD nd)) (lfc (SN.NodeStateD.inert-BD nd)) (lfs (SN.NodeStateD.inert-BD nd))) (SN.NodeStateD.inert-CD nd)  , eq ,
  cong (λ q → absNodeD (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tsc (SN.NodeStateD.inert-BD nd)) (tss (SN.NodeStateD.inert-BD nd)) (kac (SN.NodeStateD.inert-BD nd)) q (lnc (SN.NodeStateD.inert-BD nd)) (lns (SN.NodeStateD.inert-BD nd)) (lfc (SN.NodeStateD.inert-BD nd)) (lfs (SN.NodeStateD.inert-BD nd))) (SN.NodeStateD.inert-CD nd))) poseq
finishD-L-abs nd eq eqL (blnc st poseq refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tsc (SN.NodeStateD.inert-BD nd)) (tss (SN.NodeStateD.inert-BD nd)) (kac (SN.NodeStateD.inert-BD nd)) (kas (SN.NodeStateD.inert-BD nd)) (lncHead st) (lns (SN.NodeStateD.inert-BD nd)) (lfc (SN.NodeStateD.inert-BD nd)) (lfs (SN.NodeStateD.inert-BD nd))) (SN.NodeStateD.inert-CD nd)  , eq ,
  cong (λ q → absNodeD (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tsc (SN.NodeStateD.inert-BD nd)) (tss (SN.NodeStateD.inert-BD nd)) (kac (SN.NodeStateD.inert-BD nd)) (kas (SN.NodeStateD.inert-BD nd)) q (lns (SN.NodeStateD.inert-BD nd)) (lfc (SN.NodeStateD.inert-BD nd)) (lfs (SN.NodeStateD.inert-BD nd))) (SN.NodeStateD.inert-CD nd))) poseq
finishD-L-abs nd eq eqL (blns st poseq refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tsc (SN.NodeStateD.inert-BD nd)) (tss (SN.NodeStateD.inert-BD nd)) (kac (SN.NodeStateD.inert-BD nd)) (kas (SN.NodeStateD.inert-BD nd)) (lnc (SN.NodeStateD.inert-BD nd)) (lnsHead st) (lfc (SN.NodeStateD.inert-BD nd)) (lfs (SN.NodeStateD.inert-BD nd))) (SN.NodeStateD.inert-CD nd)  , eq ,
  cong (λ q → absNodeD (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tsc (SN.NodeStateD.inert-BD nd)) (tss (SN.NodeStateD.inert-BD nd)) (kac (SN.NodeStateD.inert-BD nd)) (kas (SN.NodeStateD.inert-BD nd)) (lnc (SN.NodeStateD.inert-BD nd)) q (lfc (SN.NodeStateD.inert-BD nd)) (lfs (SN.NodeStateD.inert-BD nd))) (SN.NodeStateD.inert-CD nd))) poseq
finishD-L-abs nd eq eqL (blfc st poseq refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tsc (SN.NodeStateD.inert-BD nd)) (tss (SN.NodeStateD.inert-BD nd)) (kac (SN.NodeStateD.inert-BD nd)) (kas (SN.NodeStateD.inert-BD nd)) (lnc (SN.NodeStateD.inert-BD nd)) (lns (SN.NodeStateD.inert-BD nd)) (lfcHead st) (lfs (SN.NodeStateD.inert-BD nd))) (SN.NodeStateD.inert-CD nd)  , eq ,
  cong (λ q → absNodeD (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tsc (SN.NodeStateD.inert-BD nd)) (tss (SN.NodeStateD.inert-BD nd)) (kac (SN.NodeStateD.inert-BD nd)) (kas (SN.NodeStateD.inert-BD nd)) (lnc (SN.NodeStateD.inert-BD nd)) (lns (SN.NodeStateD.inert-BD nd)) q (lfs (SN.NodeStateD.inert-BD nd))) (SN.NodeStateD.inert-CD nd))) poseq
finishD-L-abs nd eq eqL (blfs st poseq refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tsc (SN.NodeStateD.inert-BD nd)) (tss (SN.NodeStateD.inert-BD nd)) (kac (SN.NodeStateD.inert-BD nd)) (kas (SN.NodeStateD.inert-BD nd)) (lnc (SN.NodeStateD.inert-BD nd)) (lns (SN.NodeStateD.inert-BD nd)) (lfc (SN.NodeStateD.inert-BD nd)) (lfsHead st)) (SN.NodeStateD.inert-CD nd)  , eq ,
  cong (λ q → absNodeD (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tsc (SN.NodeStateD.inert-BD nd)) (tss (SN.NodeStateD.inert-BD nd)) (kac (SN.NodeStateD.inert-BD nd)) (kas (SN.NodeStateD.inert-BD nd)) (lnc (SN.NodeStateD.inert-BD nd)) (lns (SN.NodeStateD.inert-BD nd)) (lfc (SN.NodeStateD.inert-BD nd)) q) (SN.NodeStateD.inert-CD nd))) poseq

-- fused: finishD-R-abs (also emits the abstract collapse `absNodeD` eq)
finishD-R-abs : (nd : SN.NodeStateD) {D′ Bd′ M2 : NetProc}
  → D′ ≡ (Bd′ ∥⇘ apiES ⇙ (decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ decConsD linkCD (SN.NodeStateD.cons-CD nd)))
  → Bd′ ≡ (bundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ⦀ M2)
  → BundleτR linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) M2
  → Σ[ nd′ ∈ SN.NodeStateD ] (D′ ≡ decNodeD nd′) × (absNodeD nd ≡ absNodeD nd′)
finishD-R-abs nd eq eqR (bcsc st poseq refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (csHead st) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd)  , eq ,
  cong (λ q → absNodeD (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             q (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd))) poseq
finishD-R-abs nd eq eqR (bcss st poseq refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (ssHead st) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd)  , eq ,
  cong (λ q → absNodeD (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) q (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd))) poseq
finishD-R-abs nd eq eqR (bbfc st poseq refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (bcHead st) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd)  , eq ,
  cong (λ q → absNodeD (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) q (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd))) poseq
finishD-R-abs nd eq eqR (bbfs st poseq refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (bsHead st) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd)  , eq ,
  cong (λ q → absNodeD (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) q (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd))) poseq
finishD-R-abs nd eq eqR (btsc st poseq refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tcHead st) (tss (SN.NodeStateD.inert-CD nd)) (kac (SN.NodeStateD.inert-CD nd)) (kas (SN.NodeStateD.inert-CD nd)) (lnc (SN.NodeStateD.inert-CD nd)) (lns (SN.NodeStateD.inert-CD nd)) (lfc (SN.NodeStateD.inert-CD nd)) (lfs (SN.NodeStateD.inert-CD nd)))  , eq ,
  cong (λ q → absNodeD (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert q (tss (SN.NodeStateD.inert-CD nd)) (kac (SN.NodeStateD.inert-CD nd)) (kas (SN.NodeStateD.inert-CD nd)) (lnc (SN.NodeStateD.inert-CD nd)) (lns (SN.NodeStateD.inert-CD nd)) (lfc (SN.NodeStateD.inert-CD nd)) (lfs (SN.NodeStateD.inert-CD nd))))) poseq
finishD-R-abs nd eq eqR (btss st poseq refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tsc (SN.NodeStateD.inert-CD nd)) (tsHead st) (kac (SN.NodeStateD.inert-CD nd)) (kas (SN.NodeStateD.inert-CD nd)) (lnc (SN.NodeStateD.inert-CD nd)) (lns (SN.NodeStateD.inert-CD nd)) (lfc (SN.NodeStateD.inert-CD nd)) (lfs (SN.NodeStateD.inert-CD nd)))  , eq ,
  cong (λ q → absNodeD (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tsc (SN.NodeStateD.inert-CD nd)) q (kac (SN.NodeStateD.inert-CD nd)) (kas (SN.NodeStateD.inert-CD nd)) (lnc (SN.NodeStateD.inert-CD nd)) (lns (SN.NodeStateD.inert-CD nd)) (lfc (SN.NodeStateD.inert-CD nd)) (lfs (SN.NodeStateD.inert-CD nd))))) poseq
finishD-R-abs nd eq eqR (bkac st poseq refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tsc (SN.NodeStateD.inert-CD nd)) (tss (SN.NodeStateD.inert-CD nd)) (kcHead st) (kas (SN.NodeStateD.inert-CD nd)) (lnc (SN.NodeStateD.inert-CD nd)) (lns (SN.NodeStateD.inert-CD nd)) (lfc (SN.NodeStateD.inert-CD nd)) (lfs (SN.NodeStateD.inert-CD nd)))  , eq ,
  cong (λ q → absNodeD (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tsc (SN.NodeStateD.inert-CD nd)) (tss (SN.NodeStateD.inert-CD nd)) q (kas (SN.NodeStateD.inert-CD nd)) (lnc (SN.NodeStateD.inert-CD nd)) (lns (SN.NodeStateD.inert-CD nd)) (lfc (SN.NodeStateD.inert-CD nd)) (lfs (SN.NodeStateD.inert-CD nd))))) poseq
finishD-R-abs nd eq eqR (bkas st poseq refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tsc (SN.NodeStateD.inert-CD nd)) (tss (SN.NodeStateD.inert-CD nd)) (kac (SN.NodeStateD.inert-CD nd)) (ksHead st) (lnc (SN.NodeStateD.inert-CD nd)) (lns (SN.NodeStateD.inert-CD nd)) (lfc (SN.NodeStateD.inert-CD nd)) (lfs (SN.NodeStateD.inert-CD nd)))  , eq ,
  cong (λ q → absNodeD (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tsc (SN.NodeStateD.inert-CD nd)) (tss (SN.NodeStateD.inert-CD nd)) (kac (SN.NodeStateD.inert-CD nd)) q (lnc (SN.NodeStateD.inert-CD nd)) (lns (SN.NodeStateD.inert-CD nd)) (lfc (SN.NodeStateD.inert-CD nd)) (lfs (SN.NodeStateD.inert-CD nd))))) poseq
finishD-R-abs nd eq eqR (blnc st poseq refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tsc (SN.NodeStateD.inert-CD nd)) (tss (SN.NodeStateD.inert-CD nd)) (kac (SN.NodeStateD.inert-CD nd)) (kas (SN.NodeStateD.inert-CD nd)) (lncHead st) (lns (SN.NodeStateD.inert-CD nd)) (lfc (SN.NodeStateD.inert-CD nd)) (lfs (SN.NodeStateD.inert-CD nd)))  , eq ,
  cong (λ q → absNodeD (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tsc (SN.NodeStateD.inert-CD nd)) (tss (SN.NodeStateD.inert-CD nd)) (kac (SN.NodeStateD.inert-CD nd)) (kas (SN.NodeStateD.inert-CD nd)) q (lns (SN.NodeStateD.inert-CD nd)) (lfc (SN.NodeStateD.inert-CD nd)) (lfs (SN.NodeStateD.inert-CD nd))))) poseq
finishD-R-abs nd eq eqR (blns st poseq refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tsc (SN.NodeStateD.inert-CD nd)) (tss (SN.NodeStateD.inert-CD nd)) (kac (SN.NodeStateD.inert-CD nd)) (kas (SN.NodeStateD.inert-CD nd)) (lnc (SN.NodeStateD.inert-CD nd)) (lnsHead st) (lfc (SN.NodeStateD.inert-CD nd)) (lfs (SN.NodeStateD.inert-CD nd)))  , eq ,
  cong (λ q → absNodeD (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tsc (SN.NodeStateD.inert-CD nd)) (tss (SN.NodeStateD.inert-CD nd)) (kac (SN.NodeStateD.inert-CD nd)) (kas (SN.NodeStateD.inert-CD nd)) (lnc (SN.NodeStateD.inert-CD nd)) q (lfc (SN.NodeStateD.inert-CD nd)) (lfs (SN.NodeStateD.inert-CD nd))))) poseq
finishD-R-abs nd eq eqR (blfc st poseq refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tsc (SN.NodeStateD.inert-CD nd)) (tss (SN.NodeStateD.inert-CD nd)) (kac (SN.NodeStateD.inert-CD nd)) (kas (SN.NodeStateD.inert-CD nd)) (lnc (SN.NodeStateD.inert-CD nd)) (lns (SN.NodeStateD.inert-CD nd)) (lfcHead st) (lfs (SN.NodeStateD.inert-CD nd)))  , eq ,
  cong (λ q → absNodeD (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tsc (SN.NodeStateD.inert-CD nd)) (tss (SN.NodeStateD.inert-CD nd)) (kac (SN.NodeStateD.inert-CD nd)) (kas (SN.NodeStateD.inert-CD nd)) (lnc (SN.NodeStateD.inert-CD nd)) (lns (SN.NodeStateD.inert-CD nd)) q (lfs (SN.NodeStateD.inert-CD nd))))) poseq
finishD-R-abs nd eq eqR (blfs st poseq refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tsc (SN.NodeStateD.inert-CD nd)) (tss (SN.NodeStateD.inert-CD nd)) (kac (SN.NodeStateD.inert-CD nd)) (kas (SN.NodeStateD.inert-CD nd)) (lnc (SN.NodeStateD.inert-CD nd)) (lns (SN.NodeStateD.inert-CD nd)) (lfc (SN.NodeStateD.inert-CD nd)) (lfsHead st))  , eq ,
  cong (λ q → absNodeD (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tsc (SN.NodeStateD.inert-CD nd)) (tss (SN.NodeStateD.inert-CD nd)) (kac (SN.NodeStateD.inert-CD nd)) (kas (SN.NodeStateD.inert-CD nd)) (lnc (SN.NodeStateD.inert-CD nd)) (lns (SN.NodeStateD.inert-CD nd)) (lfc (SN.NodeStateD.inert-CD nd)) q))) poseq

-- fused: nodeA-τ-inv-abs (also emits the abstract collapse `absNodeA` eq)
nodeA-τ-inv-abs : (na : SN.NodeStateA) {A′ : NetProc}
  → decNodeA na ─[ τ ]─► A′ → Σ[ na′ ∈ SN.NodeStateA ] (A′ ≡ decNodeA na′) × (absNodeA na ≡ absNodeA na′)
nodeA-τ-inv-abs na step with reflect-node-τ _ _ step
... | driverτ Dr′ ds _
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decProd linkAB hi blkA (SN.NodeStateA.prod-AB na))
           (decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)) ds
...   | PEA.τL _ ps _ = ⊥-elim (decProd-no-τ linkAB hi blkA (SN.NodeStateA.prod-AB na) ps)
...   | PEA.τR _ qs _ = ⊥-elim (decProd-no-τ linkAC hi blkA (SN.NodeStateA.prod-AC na) qs)
nodeA-τ-inv-abs na step | bundleτ Bd′ bs eq
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt)
           (bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)) _ bs
...   | PEA.τL _ s1 eqL = finishA-L-abs na eq eqL
          (bundle-τ-inv linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) s1)
...   | PEA.τR _ s2 eqR = finishA-R-abs na eq eqR
          (bundle-τ-inv linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) s2)

-- fused: nodeB-τ-inv-abs (also emits the abstract collapse `absNodeB` eq)
nodeB-τ-inv-abs : (nb : SN.NodeStateB) {B′ : NetProc}
  → decNodeB nb ─[ τ ]─► B′ → Σ[ nb′ ∈ SN.NodeStateB ] (B′ ≡ decNodeB nb′) × (absNodeB nb ≡ absNodeB nb′)
nodeB-τ-inv-abs nb step with reflect-node-τ _ _ step
... | driverτ Dr′ ds _ = ⊥-elim (decCP-no-τ linkAB linkBD (SN.NodeStateB.cp-B nb) ds)
nodeB-τ-inv-abs nb step | bundleτ Bd′ bs eq
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt)
           (bundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)) _ bs
...   | PEA.τL _ s1 eqL = finishB-L-abs nb eq eqL
          (bundle-τ-inv linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) s1)
...   | PEA.τR _ s2 eqR = finishB-R-abs nb eq eqR
          (bundle-τ-inv linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) s2)

-- fused: nodeC-τ-inv-abs (also emits the abstract collapse `absNodeC` eq)
nodeC-τ-inv-abs : (nc : SN.NodeStateC) {C′ : NetProc}
  → decNodeC nc ─[ τ ]─► C′ → Σ[ nc′ ∈ SN.NodeStateC ] (C′ ≡ decNodeC nc′) × (absNodeC nc ≡ absNodeC nc′)
nodeC-τ-inv-abs nc step with reflect-node-τ _ _ step
... | driverτ Dr′ ds _ = ⊥-elim (decCP-no-τ linkAC linkCD (SN.NodeStateC.cp-C nc) ds)
nodeC-τ-inv-abs nc step | bundleτ Bd′ bs eq
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt)
           (bundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)) _ bs
...   | PEA.τL _ s1 eqL = finishC-L-abs nc eq eqL
          (bundle-τ-inv linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) s1)
...   | PEA.τR _ s2 eqR = finishC-R-abs nc eq eqR
          (bundle-τ-inv linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) s2)

-- fused: nodeD-τ-inv-abs (also emits the abstract collapse `absNodeD` eq)
nodeD-τ-inv-abs : (nd : SN.NodeStateD) {D′ : NetProc}
  → decNodeD nd ─[ τ ]─► D′ → Σ[ nd′ ∈ SN.NodeStateD ] (D′ ≡ decNodeD nd′) × (absNodeD nd ≡ absNodeD nd′)
nodeD-τ-inv-abs nd step with reflect-node-τ _ _ step
... | driverτ Dr′ ds _
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decConsD linkBD (SN.NodeStateD.cons-BD nd))
           (decConsD linkCD (SN.NodeStateD.cons-CD nd)) ds
...   | PEA.τL _ ps _ = ⊥-elim (decConsD-no-τ linkBD (SN.NodeStateD.cons-BD nd) ps)
...   | PEA.τR _ qs _ = ⊥-elim (decConsD-no-τ linkCD (SN.NodeStateD.cons-CD nd) qs)
nodeD-τ-inv-abs nd step | bundleτ Bd′ bs eq
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt)
           (bundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)) _ bs
...   | PEA.τL _ s1 eqL = finishD-L-abs nd eq eqL
          (bundle-τ-inv linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) s1)
...   | PEA.τR _ s2 eqR = finishD-R-abs nd eq eqR
          (bundle-τ-inv linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) s2)
