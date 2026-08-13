{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R2 — the ALL-PEER sil-count measure `μ'` and the μ'-aware
-- node-τ reflection, feeding the forward divergence transfer `odiv→`.
--
-- The existing `μ` (SysStep) counts ONLY the CS/BF peer sils; it carries no
-- weight for the eight INERT peers (TS/KA/LN/LF client+server), which DO have
-- loop-re-entry sils.  So `μ` is NOT well-founded-decreasing on every nodes-τ.
-- Here `μ'` counts a `+1` for EVERY peer sitting at a `…Sil` position, across
-- all twelve peers × two links × four nodes.  Each nodes-τ is a peer loop
-- re-entry `…Sil st → …Head st` (all four `nodeX-τ-…` refute the driver τ), so
-- it drops exactly one peer's weight ⇒ `μ'` strictly decreases (`nodes-τ-μ'↓`).
--
-- The reflection is re-derived here (the frozen `SIL4.nodeX-τ-inv-abs` carries
-- no `μ'` info): a GENERIC `bundle-step` folds a `BundleτR` into (new bundle
-- positions + `bundleG`-eq + abstract-collapse eq + a bundle-measure drop),
-- reused by the four thin `nodeX-τ-μ`.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDiv (blkA : Block₃) where

open import Level using (0ℓ; Level)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.Nat.Properties using (+-monoˡ-<; +-monoʳ-<; n<1+n)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Process_Trees using (PTree; ExtI)

-- links, api alphabet, block payloads
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using
  ( p; apiES; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟; Link )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using ( Dir; lo; hi )

-- Net_Api operators + the empty sync alphabet + the Par τ-elimination
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_ )
open Op using () renaming (∅ES to ∅ESa)
import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload}) as PEA

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; τ )

-- concrete node decodes + states + drivers + bundles + positions
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using
  ( NetProc
  ; NodeStateA; NodeStateB; NodeStateC; NodeStateD
  ; decNodeA; decNodeB; decNodeC; decNodeD
  ; bundleA; bundleG; decProd; decCP; decConsD
  ; InertPos; mkInert; tsc; tss; kac; kas; lnc; lns; lfc; lfs
  ; CScPos; CSsPos; BFcPos; BFsPos; TScPos; TSsPos; KAcPos; KAsPos
  ; LNcPos; LNsPos; LFcPos; LFsPos
  ; csHead; csSil; ssHead; ssSil; bcHead; bcSil; bsHead; bsSil
  ; tcHead; tcSil; tsHead; tsSil; kcHead; kcSil; ksHead; ksSil
  ; lncHead; lncSil; lnsHead; lnsSil; lfcHead; lfcSil; lfsHead; lfsSil )

-- whole-system state + concrete decode
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA using
  ( SysState; mkSys; med; nA; nB; nC; nD )

-- abstract node decodes + abstract bundle + node-τ reflection + CS/BF weights
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA using
  ( nodesOf; absNodesOf
  ; absNodeA; absNodeB; absNodeC; absNodeD; absBundleG
  ; NodeτR; bundleτ; driverτ; reflect-node-τ
  ; NodesτR; nAτ; nBτ; nCτ; nDτ; reflect-nodes-τ
  ; μCSc; μCSs; μBFc; μBFs )

-- the 12-peer bundle τ-inversion + its result type + the driver τ-freedom
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA using
  ( BundleτR; bcsc; bcss; bbfc; bbfs; btsc; btss; bkac; bkas; blnc; blns; blfc; blfs
  ; bundle-τ-inv; decProd-no-τ; decCP-no-τ; decConsD-no-τ )

------------------------------------------------------------------------
-- The eight inert-peer sil weights (`1` at a `…Sil` position, `0` elsewhere).
------------------------------------------------------------------------

μTSc : TScPos → ℕ
μTSc (tcSil _) = 1
μTSc _         = 0

μTSs : TSsPos → ℕ
μTSs (tsSil _) = 1
μTSs _         = 0

μKAc : KAcPos → ℕ
μKAc (kcSil _) = 1
μKAc _         = 0

μKAs : KAsPos → ℕ
μKAs (ksSil _) = 1
μKAs _         = 0

μLNc : LNcPos → ℕ
μLNc (lncSil _) = 1
μLNc _          = 0

μLNs : LNsPos → ℕ
μLNs (lnsSil _) = 1
μLNs _          = 0

μLFc : LFcPos → ℕ
μLFc (lfcSil _) = 1
μLFc _          = 0

μLFs : LFsPos → ℕ
μLFs (lfsSil _) = 1
μLFs _          = 0

-- the eight inert peers' total sil-count for one link (right-nested)
μInert : InertPos → ℕ
μInert ip = μTSc (tsc ip) + (μTSs (tss ip) + (μKAc (kac ip) + (μKAs (kas ip)
          + (μLNc (lnc ip) + (μLNs (lns ip) + (μLFc (lfc ip) + μLFs (lfs ip)))))))

-- one link's twelve-peer sil-count (right-nested; drivers carry no τ ⇒ omitted)
μBun : CScPos → CSsPos → BFcPos → BFsPos → InertPos → ℕ
μBun csc css bfc bfs ip = μCSc csc + (μCSs css + (μBFc bfc + (μBFs bfs + μInert ip)))

-- per-node all-peer sil-count = its two link bundles (no driver contribution)
μ'NodeA : NodeStateA → ℕ
μ'NodeA s = μBun (SN.csC-AB s) (SN.csS-AB s) (SN.bfC-AB s) (SN.bfS-AB s) (SN.inert-AB s)
          + μBun (SN.csC-AC s) (SN.csS-AC s) (SN.bfC-AC s) (SN.bfS-AC s) (SN.inert-AC s)

μ'NodeB : NodeStateB → ℕ
μ'NodeB s = μBun (SN.csC-AB s) (SN.csS-AB s) (SN.bfC-AB s) (SN.bfS-AB s) (SN.inert-AB s)
          + μBun (SN.csC-BD s) (SN.csS-BD s) (SN.bfC-BD s) (SN.bfS-BD s) (SN.inert-BD s)

μ'NodeC : NodeStateC → ℕ
μ'NodeC s = μBun (SN.csC-AC s) (SN.csS-AC s) (SN.bfC-AC s) (SN.bfS-AC s) (SN.inert-AC s)
          + μBun (SN.csC-CD s) (SN.csS-CD s) (SN.bfC-CD s) (SN.bfS-CD s) (SN.inert-CD s)

μ'NodeD : NodeStateD → ℕ
μ'NodeD s = μBun (SN.csC-BD s) (SN.csS-BD s) (SN.bfC-BD s) (SN.bfS-BD s) (SN.inert-BD s)
          + μBun (SN.csC-CD s) (SN.csS-CD s) (SN.bfC-CD s) (SN.bfS-CD s) (SN.inert-CD s)

-- whole-system all-peer sil-count (right-nested over the four nodes)
μ'Sys : SysState → ℕ
μ'Sys s = μ'NodeA (nA s) + (μ'NodeB (nB s) + (μ'NodeC (nC s) + μ'NodeD (nD s)))

------------------------------------------------------------------------
-- The twelve per-slot `μBun`-drop lemmas: moving ONE peer `…Head st ← …Sil st`
-- drops that link's `μBun` by exactly one.  Each peels the fixed right-nested
-- sum down to `0 + R < 1 + R` (`n<1+n`).
------------------------------------------------------------------------

μBun-csc↓ : ∀ st css bfc bfs ip → μBun (csHead st) css bfc bfs ip < μBun (csSil st) css bfc bfs ip
μBun-csc↓ st css bfc bfs ip = n<1+n _

μBun-css↓ : ∀ st csc bfc bfs ip → μBun csc (ssHead st) bfc bfs ip < μBun csc (ssSil st) bfc bfs ip
μBun-css↓ st csc bfc bfs ip = +-monoʳ-< (μCSc csc) (n<1+n _)

μBun-bfc↓ : ∀ st csc css bfs ip → μBun csc css (bcHead st) bfs ip < μBun csc css (bcSil st) bfs ip
μBun-bfc↓ st csc css bfs ip = +-monoʳ-< (μCSc csc) (+-monoʳ-< (μCSs css) (n<1+n _))

μBun-bfs↓ : ∀ st csc css bfc ip → μBun csc css bfc (bsHead st) ip < μBun csc css bfc (bsSil st) ip
μBun-bfs↓ st csc css bfc ip = +-monoʳ-< (μCSc csc) (+-monoʳ-< (μCSs css) (+-monoʳ-< (μBFc bfc) (n<1+n _)))

μBun-tsc↓ : ∀ st csc css bfc bfs tss' kac' kas' lnc' lns' lfc' lfs'
  → μBun csc css bfc bfs (mkInert (tcHead st) tss' kac' kas' lnc' lns' lfc' lfs')
  < μBun csc css bfc bfs (mkInert (tcSil st) tss' kac' kas' lnc' lns' lfc' lfs')
μBun-tsc↓ st csc css bfc bfs tss' kac' kas' lnc' lns' lfc' lfs' =
  +-monoʳ-< (μCSc csc) (+-monoʳ-< (μCSs css) (+-monoʳ-< (μBFc bfc) (+-monoʳ-< (μBFs bfs)
    (n<1+n _))))

μBun-tss↓ : ∀ st csc css bfc bfs tsc' kac' kas' lnc' lns' lfc' lfs'
  → μBun csc css bfc bfs (mkInert tsc' (tsHead st) kac' kas' lnc' lns' lfc' lfs')
  < μBun csc css bfc bfs (mkInert tsc' (tsSil st) kac' kas' lnc' lns' lfc' lfs')
μBun-tss↓ st csc css bfc bfs tsc' kac' kas' lnc' lns' lfc' lfs' =
  +-monoʳ-< (μCSc csc) (+-monoʳ-< (μCSs css) (+-monoʳ-< (μBFc bfc) (+-monoʳ-< (μBFs bfs)
    (+-monoʳ-< (μTSc tsc') (n<1+n _)))))

μBun-kac↓ : ∀ st csc css bfc bfs tsc' tss' kas' lnc' lns' lfc' lfs'
  → μBun csc css bfc bfs (mkInert tsc' tss' (kcHead st) kas' lnc' lns' lfc' lfs')
  < μBun csc css bfc bfs (mkInert tsc' tss' (kcSil st) kas' lnc' lns' lfc' lfs')
μBun-kac↓ st csc css bfc bfs tsc' tss' kas' lnc' lns' lfc' lfs' =
  +-monoʳ-< (μCSc csc) (+-monoʳ-< (μCSs css) (+-monoʳ-< (μBFc bfc) (+-monoʳ-< (μBFs bfs)
    (+-monoʳ-< (μTSc tsc') (+-monoʳ-< (μTSs tss') (n<1+n _))))))

μBun-kas↓ : ∀ st csc css bfc bfs tsc' tss' kac' lnc' lns' lfc' lfs'
  → μBun csc css bfc bfs (mkInert tsc' tss' kac' (ksHead st) lnc' lns' lfc' lfs')
  < μBun csc css bfc bfs (mkInert tsc' tss' kac' (ksSil st) lnc' lns' lfc' lfs')
μBun-kas↓ st csc css bfc bfs tsc' tss' kac' lnc' lns' lfc' lfs' =
  +-monoʳ-< (μCSc csc) (+-monoʳ-< (μCSs css) (+-monoʳ-< (μBFc bfc) (+-monoʳ-< (μBFs bfs)
    (+-monoʳ-< (μTSc tsc') (+-monoʳ-< (μTSs tss') (+-monoʳ-< (μKAc kac') (n<1+n _)))))))

μBun-lnc↓ : ∀ st csc css bfc bfs tsc' tss' kac' kas' lns' lfc' lfs'
  → μBun csc css bfc bfs (mkInert tsc' tss' kac' kas' (lncHead st) lns' lfc' lfs')
  < μBun csc css bfc bfs (mkInert tsc' tss' kac' kas' (lncSil st) lns' lfc' lfs')
μBun-lnc↓ st csc css bfc bfs tsc' tss' kac' kas' lns' lfc' lfs' =
  +-monoʳ-< (μCSc csc) (+-monoʳ-< (μCSs css) (+-monoʳ-< (μBFc bfc) (+-monoʳ-< (μBFs bfs)
    (+-monoʳ-< (μTSc tsc') (+-monoʳ-< (μTSs tss') (+-monoʳ-< (μKAc kac') (+-monoʳ-< (μKAs kas')
      (n<1+n _))))))))

μBun-lns↓ : ∀ st csc css bfc bfs tsc' tss' kac' kas' lnc' lfc' lfs'
  → μBun csc css bfc bfs (mkInert tsc' tss' kac' kas' lnc' (lnsHead st) lfc' lfs')
  < μBun csc css bfc bfs (mkInert tsc' tss' kac' kas' lnc' (lnsSil st) lfc' lfs')
μBun-lns↓ st csc css bfc bfs tsc' tss' kac' kas' lnc' lfc' lfs' =
  +-monoʳ-< (μCSc csc) (+-monoʳ-< (μCSs css) (+-monoʳ-< (μBFc bfc) (+-monoʳ-< (μBFs bfs)
    (+-monoʳ-< (μTSc tsc') (+-monoʳ-< (μTSs tss') (+-monoʳ-< (μKAc kac') (+-monoʳ-< (μKAs kas')
      (+-monoʳ-< (μLNc lnc') (n<1+n _)))))))))

μBun-lfc↓ : ∀ st csc css bfc bfs tsc' tss' kac' kas' lnc' lns' lfs'
  → μBun csc css bfc bfs (mkInert tsc' tss' kac' kas' lnc' lns' (lfcHead st) lfs')
  < μBun csc css bfc bfs (mkInert tsc' tss' kac' kas' lnc' lns' (lfcSil st) lfs')
μBun-lfc↓ st csc css bfc bfs tsc' tss' kac' kas' lnc' lns' lfs' =
  +-monoʳ-< (μCSc csc) (+-monoʳ-< (μCSs css) (+-monoʳ-< (μBFc bfc) (+-monoʳ-< (μBFs bfs)
    (+-monoʳ-< (μTSc tsc') (+-monoʳ-< (μTSs tss') (+-monoʳ-< (μKAc kac') (+-monoʳ-< (μKAs kas')
      (+-monoʳ-< (μLNc lnc') (+-monoʳ-< (μLNs lns') (n<1+n _))))))))))

μBun-lfs↓ : ∀ st csc css bfc bfs tsc' tss' kac' kas' lnc' lns' lfc'
  → μBun csc css bfc bfs (mkInert tsc' tss' kac' kas' lnc' lns' lfc' (lfsHead st))
  < μBun csc css bfc bfs (mkInert tsc' tss' kac' kas' lnc' lns' lfc' (lfsSil st))
μBun-lfs↓ st csc css bfc bfs tsc' tss' kac' kas' lnc' lns' lfc' =
  +-monoʳ-< (μCSc csc) (+-monoʳ-< (μCSs css) (+-monoʳ-< (μBFc bfc) (+-monoʳ-< (μBFs bfs)
    (+-monoʳ-< (μTSc tsc') (+-monoʳ-< (μTSs tss') (+-monoʳ-< (μKAc kac') (+-monoʳ-< (μKAs kas')
      (+-monoʳ-< (μLNc lnc') (+-monoʳ-< (μLNs lns') (+-monoʳ-< (μLFc lfc') (n<1+n _)))))))))))

------------------------------------------------------------------------
-- The GENERIC bundle step: fold a `BundleτR` (one peer `…Sil st → …Head st`)
-- into new bundle positions + `bundleG`-eq + abstract-collapse eq + `μBun` drop.
-- Reused by all eight node-links.
------------------------------------------------------------------------

-- the packaged bundle-step result
BundleStepR : (l : Link) (cl sv : Dir)
    (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    (Bd′ : NetProc) → Set₁
BundleStepR l cl sv csc css bfc bfs ip Bd′ =
  Σ[ csc′ ∈ CScPos ] Σ[ css′ ∈ CSsPos ] Σ[ bfc′ ∈ BFcPos ] Σ[ bfs′ ∈ BFsPos ] Σ[ ip′ ∈ InertPos ]
      (Bd′ ≡ bundleG l cl sv csc′ css′ bfc′ bfs′ ip′)
    × (absBundleG l cl sv csc′ css′ bfc′ bfs′ ip′ ≡ absBundleG l cl sv csc css bfc bfs ip)
    × (μBun csc′ css′ bfc′ bfs′ ip′ < μBun csc css bfc bfs ip)

bundle-step : (l : Link) (cl sv : Dir)
    (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {Bd′ : NetProc}
  → BundleτR l cl sv csc css bfc bfs ip Bd′
  → BundleStepR l cl sv csc css bfc bfs ip Bd′
bundle-step l cl sv csc css bfc bfs ip (bcsc st poseq refl) =
  csHead st , css , bfc , bfs , ip , refl
  , sym (cong (λ z → absBundleG l cl sv z css bfc bfs ip) poseq)
  , subst (λ z → μBun (csHead st) css bfc bfs ip < μBun z css bfc bfs ip) (sym poseq) (μBun-csc↓ st css bfc bfs ip)
bundle-step l cl sv csc css bfc bfs ip (bcss st poseq refl) =
  csc , ssHead st , bfc , bfs , ip , refl
  , sym (cong (λ z → absBundleG l cl sv csc z bfc bfs ip) poseq)
  , subst (λ z → μBun csc (ssHead st) bfc bfs ip < μBun csc z bfc bfs ip) (sym poseq) (μBun-css↓ st csc bfc bfs ip)
bundle-step l cl sv csc css bfc bfs ip (bbfc st poseq refl) =
  csc , css , bcHead st , bfs , ip , refl
  , sym (cong (λ z → absBundleG l cl sv csc css z bfs ip) poseq)
  , subst (λ z → μBun csc css (bcHead st) bfs ip < μBun csc css z bfs ip) (sym poseq) (μBun-bfc↓ st csc css bfs ip)
bundle-step l cl sv csc css bfc bfs ip (bbfs st poseq refl) =
  csc , css , bfc , bsHead st , ip , refl
  , sym (cong (λ z → absBundleG l cl sv csc css bfc z ip) poseq)
  , subst (λ z → μBun csc css bfc (bsHead st) ip < μBun csc css bfc z ip) (sym poseq) (μBun-bfs↓ st csc css bfc ip)
bundle-step l cl sv csc css bfc bfs ip (btsc st poseq refl) =
  csc , css , bfc , bfs , mkInert (tcHead st) (tss ip) (kac ip) (kas ip) (lnc ip) (lns ip) (lfc ip) (lfs ip) , refl
  , sym (cong (λ z → absBundleG l cl sv csc css bfc bfs (mkInert z (tss ip) (kac ip) (kas ip) (lnc ip) (lns ip) (lfc ip) (lfs ip))) poseq)
  , subst (λ z → μBun csc css bfc bfs (mkInert (tcHead st) (tss ip) (kac ip) (kas ip) (lnc ip) (lns ip) (lfc ip) (lfs ip))
              < μBun csc css bfc bfs (mkInert z (tss ip) (kac ip) (kas ip) (lnc ip) (lns ip) (lfc ip) (lfs ip)))
          (sym poseq) (μBun-tsc↓ st csc css bfc bfs (tss ip) (kac ip) (kas ip) (lnc ip) (lns ip) (lfc ip) (lfs ip))
bundle-step l cl sv csc css bfc bfs ip (btss st poseq refl) =
  csc , css , bfc , bfs , mkInert (tsc ip) (tsHead st) (kac ip) (kas ip) (lnc ip) (lns ip) (lfc ip) (lfs ip) , refl
  , sym (cong (λ z → absBundleG l cl sv csc css bfc bfs (mkInert (tsc ip) z (kac ip) (kas ip) (lnc ip) (lns ip) (lfc ip) (lfs ip))) poseq)
  , subst (λ z → μBun csc css bfc bfs (mkInert (tsc ip) (tsHead st) (kac ip) (kas ip) (lnc ip) (lns ip) (lfc ip) (lfs ip))
              < μBun csc css bfc bfs (mkInert (tsc ip) z (kac ip) (kas ip) (lnc ip) (lns ip) (lfc ip) (lfs ip)))
          (sym poseq) (μBun-tss↓ st csc css bfc bfs (tsc ip) (kac ip) (kas ip) (lnc ip) (lns ip) (lfc ip) (lfs ip))
bundle-step l cl sv csc css bfc bfs ip (bkac st poseq refl) =
  csc , css , bfc , bfs , mkInert (tsc ip) (tss ip) (kcHead st) (kas ip) (lnc ip) (lns ip) (lfc ip) (lfs ip) , refl
  , sym (cong (λ z → absBundleG l cl sv csc css bfc bfs (mkInert (tsc ip) (tss ip) z (kas ip) (lnc ip) (lns ip) (lfc ip) (lfs ip))) poseq)
  , subst (λ z → μBun csc css bfc bfs (mkInert (tsc ip) (tss ip) (kcHead st) (kas ip) (lnc ip) (lns ip) (lfc ip) (lfs ip))
              < μBun csc css bfc bfs (mkInert (tsc ip) (tss ip) z (kas ip) (lnc ip) (lns ip) (lfc ip) (lfs ip)))
          (sym poseq) (μBun-kac↓ st csc css bfc bfs (tsc ip) (tss ip) (kas ip) (lnc ip) (lns ip) (lfc ip) (lfs ip))
bundle-step l cl sv csc css bfc bfs ip (bkas st poseq refl) =
  csc , css , bfc , bfs , mkInert (tsc ip) (tss ip) (kac ip) (ksHead st) (lnc ip) (lns ip) (lfc ip) (lfs ip) , refl
  , sym (cong (λ z → absBundleG l cl sv csc css bfc bfs (mkInert (tsc ip) (tss ip) (kac ip) z (lnc ip) (lns ip) (lfc ip) (lfs ip))) poseq)
  , subst (λ z → μBun csc css bfc bfs (mkInert (tsc ip) (tss ip) (kac ip) (ksHead st) (lnc ip) (lns ip) (lfc ip) (lfs ip))
              < μBun csc css bfc bfs (mkInert (tsc ip) (tss ip) (kac ip) z (lnc ip) (lns ip) (lfc ip) (lfs ip)))
          (sym poseq) (μBun-kas↓ st csc css bfc bfs (tsc ip) (tss ip) (kac ip) (lnc ip) (lns ip) (lfc ip) (lfs ip))
bundle-step l cl sv csc css bfc bfs ip (blnc st poseq refl) =
  csc , css , bfc , bfs , mkInert (tsc ip) (tss ip) (kac ip) (kas ip) (lncHead st) (lns ip) (lfc ip) (lfs ip) , refl
  , sym (cong (λ z → absBundleG l cl sv csc css bfc bfs (mkInert (tsc ip) (tss ip) (kac ip) (kas ip) z (lns ip) (lfc ip) (lfs ip))) poseq)
  , subst (λ z → μBun csc css bfc bfs (mkInert (tsc ip) (tss ip) (kac ip) (kas ip) (lncHead st) (lns ip) (lfc ip) (lfs ip))
              < μBun csc css bfc bfs (mkInert (tsc ip) (tss ip) (kac ip) (kas ip) z (lns ip) (lfc ip) (lfs ip)))
          (sym poseq) (μBun-lnc↓ st csc css bfc bfs (tsc ip) (tss ip) (kac ip) (kas ip) (lns ip) (lfc ip) (lfs ip))
bundle-step l cl sv csc css bfc bfs ip (blns st poseq refl) =
  csc , css , bfc , bfs , mkInert (tsc ip) (tss ip) (kac ip) (kas ip) (lnc ip) (lnsHead st) (lfc ip) (lfs ip) , refl
  , sym (cong (λ z → absBundleG l cl sv csc css bfc bfs (mkInert (tsc ip) (tss ip) (kac ip) (kas ip) (lnc ip) z (lfc ip) (lfs ip))) poseq)
  , subst (λ z → μBun csc css bfc bfs (mkInert (tsc ip) (tss ip) (kac ip) (kas ip) (lnc ip) (lnsHead st) (lfc ip) (lfs ip))
              < μBun csc css bfc bfs (mkInert (tsc ip) (tss ip) (kac ip) (kas ip) (lnc ip) z (lfc ip) (lfs ip)))
          (sym poseq) (μBun-lns↓ st csc css bfc bfs (tsc ip) (tss ip) (kac ip) (kas ip) (lnc ip) (lfc ip) (lfs ip))
bundle-step l cl sv csc css bfc bfs ip (blfc st poseq refl) =
  csc , css , bfc , bfs , mkInert (tsc ip) (tss ip) (kac ip) (kas ip) (lnc ip) (lns ip) (lfcHead st) (lfs ip) , refl
  , sym (cong (λ z → absBundleG l cl sv csc css bfc bfs (mkInert (tsc ip) (tss ip) (kac ip) (kas ip) (lnc ip) (lns ip) z (lfs ip))) poseq)
  , subst (λ z → μBun csc css bfc bfs (mkInert (tsc ip) (tss ip) (kac ip) (kas ip) (lnc ip) (lns ip) (lfcHead st) (lfs ip))
              < μBun csc css bfc bfs (mkInert (tsc ip) (tss ip) (kac ip) (kas ip) (lnc ip) (lns ip) z (lfs ip)))
          (sym poseq) (μBun-lfc↓ st csc css bfc bfs (tsc ip) (tss ip) (kac ip) (kas ip) (lnc ip) (lns ip) (lfs ip))
bundle-step l cl sv csc css bfc bfs ip (blfs st poseq refl) =
  csc , css , bfc , bfs , mkInert (tsc ip) (tss ip) (kac ip) (kas ip) (lnc ip) (lns ip) (lfc ip) (lfsHead st) , refl
  , sym (cong (λ z → absBundleG l cl sv csc css bfc bfs (mkInert (tsc ip) (tss ip) (kac ip) (kas ip) (lnc ip) (lns ip) (lfc ip) z)) poseq)
  , subst (λ z → μBun csc css bfc bfs (mkInert (tsc ip) (tss ip) (kac ip) (kas ip) (lnc ip) (lns ip) (lfc ip) (lfsHead st))
              < μBun csc css bfc bfs (mkInert (tsc ip) (tss ip) (kac ip) (kas ip) (lnc ip) (lns ip) (lfc ip) z))
          (sym poseq) (μBun-lfs↓ st csc css bfc bfs (tsc ip) (tss ip) (kac ip) (kas ip) (lnc ip) (lns ip) (lfc ip))

------------------------------------------------------------------------
-- The four μ'-aware node-τ reflections: a nodes-τ is a peer sil (`bundleτ`;
-- the driver τ is refuted), lands on `decNodeX nX′`, leaves the abstract decode
-- UNCHANGED (`absNodeX`), and DROPS `μ'NodeX` by one (via `bundle-step`).
------------------------------------------------------------------------

-- NODE A
nodeA-τ-μ : (na : NodeStateA) {A′ : NetProc}
  → decNodeA na ─[ τ ]─► A′
  → Σ[ na′ ∈ NodeStateA ] (A′ ≡ decNodeA na′) × (absNodeA na ≡ absNodeA na′) × (μ'NodeA na′ < μ'NodeA na)
nodeA-τ-μ na step with reflect-node-τ _ _ step
... | driverτ Dr′ ds _
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decProd linkAB hi blkA (SN.prod-AB na)) (decProd linkAC hi blkA (SN.prod-AC na)) ds
...   | PEA.τL _ ps _ = ⊥-elim (decProd-no-τ linkAB hi blkA (SN.prod-AB na) ps)
...   | PEA.τR _ qs _ = ⊥-elim (decProd-no-τ linkAC hi blkA (SN.prod-AC na) qs)
nodeA-τ-μ na step | bundleτ Bd′ bs eq
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt)
           (bundleA linkAB (SN.csC-AB na) (SN.csS-AB na) (SN.bfC-AB na) (SN.bfS-AB na) (SN.inert-AB na)) _ bs
...   | PEA.τL _ s1 eqL
        with bundle-step linkAB lo hi (SN.csC-AB na) (SN.csS-AB na) (SN.bfC-AB na) (SN.bfS-AB na) (SN.inert-AB na)
               (bundle-τ-inv linkAB lo hi (SN.csC-AB na) (SN.csS-AB na) (SN.bfC-AB na) (SN.bfS-AB na) (SN.inert-AB na) s1)
...     | csc′ , css′ , bfc′ , bfs′ , ip′ , bdeq , abseq , mu =
          SN.mkNodeA csc′ css′ bfc′ bfs′ (SN.prod-AB na) (SN.csC-AC na) (SN.csS-AC na) (SN.bfC-AC na) (SN.bfS-AC na) (SN.prod-AC na) ip′ (SN.inert-AC na)
          , trans eq (cong (λ z → z ∥⇘ apiES ⇙ (decProd linkAB hi blkA (SN.prod-AB na) ⦀ decProd linkAC hi blkA (SN.prod-AC na)))
                        (trans eqL (cong (λ w → w ⦀ bundleA linkAC (SN.csC-AC na) (SN.csS-AC na) (SN.bfC-AC na) (SN.bfS-AC na) (SN.inert-AC na)) bdeq)))
          , cong (λ z → (z ⦀ absBundleG linkAC lo hi (SN.csC-AC na) (SN.csS-AC na) (SN.bfC-AC na) (SN.bfS-AC na) (SN.inert-AC na)) ∥⇘ apiES ⇙ (decProd linkAB hi blkA (SN.prod-AB na) ⦀ decProd linkAC hi blkA (SN.prod-AC na))) (sym abseq)
          , +-monoˡ-< (μBun (SN.csC-AC na) (SN.csS-AC na) (SN.bfC-AC na) (SN.bfS-AC na) (SN.inert-AC na)) mu
nodeA-τ-μ na step | bundleτ Bd′ bs eq | PEA.τR _ s2 eqR
        with bundle-step linkAC lo hi (SN.csC-AC na) (SN.csS-AC na) (SN.bfC-AC na) (SN.bfS-AC na) (SN.inert-AC na)
               (bundle-τ-inv linkAC lo hi (SN.csC-AC na) (SN.csS-AC na) (SN.bfC-AC na) (SN.bfS-AC na) (SN.inert-AC na) s2)
...     | csc′ , css′ , bfc′ , bfs′ , ip′ , bdeq , abseq , mu =
          SN.mkNodeA (SN.csC-AB na) (SN.csS-AB na) (SN.bfC-AB na) (SN.bfS-AB na) (SN.prod-AB na) csc′ css′ bfc′ bfs′ (SN.prod-AC na) (SN.inert-AB na) ip′
          , trans eq (cong (λ z → z ∥⇘ apiES ⇙ (decProd linkAB hi blkA (SN.prod-AB na) ⦀ decProd linkAC hi blkA (SN.prod-AC na)))
                        (trans eqR (cong (λ w → bundleA linkAB (SN.csC-AB na) (SN.csS-AB na) (SN.bfC-AB na) (SN.bfS-AB na) (SN.inert-AB na) ⦀ w) bdeq)))
          , cong (λ z → (absBundleG linkAB lo hi (SN.csC-AB na) (SN.csS-AB na) (SN.bfC-AB na) (SN.bfS-AB na) (SN.inert-AB na) ⦀ z) ∥⇘ apiES ⇙ (decProd linkAB hi blkA (SN.prod-AB na) ⦀ decProd linkAC hi blkA (SN.prod-AC na))) (sym abseq)
          , +-monoʳ-< (μBun (SN.csC-AB na) (SN.csS-AB na) (SN.bfC-AB na) (SN.bfS-AB na) (SN.inert-AB na)) mu

-- NODE B
nodeB-τ-μ : (nb : NodeStateB) {B′ : NetProc}
  → decNodeB nb ─[ τ ]─► B′
  → Σ[ nb′ ∈ NodeStateB ] (B′ ≡ decNodeB nb′) × (absNodeB nb ≡ absNodeB nb′) × (μ'NodeB nb′ < μ'NodeB nb)
nodeB-τ-μ nb step with reflect-node-τ _ _ step
... | driverτ Dr′ ds _ = ⊥-elim (decCP-no-τ linkAB linkBD (SN.cp-B nb) ds)
nodeB-τ-μ nb step | bundleτ Bd′ bs eq
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt)
           (bundleG linkAB hi lo (SN.csC-AB nb) (SN.csS-AB nb) (SN.bfC-AB nb) (SN.bfS-AB nb) (SN.inert-AB nb)) _ bs
...   | PEA.τL _ s1 eqL
        with bundle-step linkAB hi lo (SN.csC-AB nb) (SN.csS-AB nb) (SN.bfC-AB nb) (SN.bfS-AB nb) (SN.inert-AB nb)
               (bundle-τ-inv linkAB hi lo (SN.csC-AB nb) (SN.csS-AB nb) (SN.bfC-AB nb) (SN.bfS-AB nb) (SN.inert-AB nb) s1)
...     | csc′ , css′ , bfc′ , bfs′ , ip′ , bdeq , abseq , mu =
          SN.mkNodeB csc′ css′ bfc′ bfs′ (SN.csC-BD nb) (SN.csS-BD nb) (SN.bfC-BD nb) (SN.bfS-BD nb) (SN.cp-B nb) ip′ (SN.inert-BD nb)
          , trans eq (cong (λ z → z ∥⇘ apiES ⇙ decCP linkAB linkBD (SN.cp-B nb))
                        (trans eqL (cong (λ w → w ⦀ bundleG linkBD lo hi (SN.csC-BD nb) (SN.csS-BD nb) (SN.bfC-BD nb) (SN.bfS-BD nb) (SN.inert-BD nb)) bdeq)))
          , cong (λ z → (z ⦀ absBundleG linkBD lo hi (SN.csC-BD nb) (SN.csS-BD nb) (SN.bfC-BD nb) (SN.bfS-BD nb) (SN.inert-BD nb)) ∥⇘ apiES ⇙ decCP linkAB linkBD (SN.cp-B nb)) (sym abseq)
          , +-monoˡ-< (μBun (SN.csC-BD nb) (SN.csS-BD nb) (SN.bfC-BD nb) (SN.bfS-BD nb) (SN.inert-BD nb)) mu
nodeB-τ-μ nb step | bundleτ Bd′ bs eq | PEA.τR _ s2 eqR
        with bundle-step linkBD lo hi (SN.csC-BD nb) (SN.csS-BD nb) (SN.bfC-BD nb) (SN.bfS-BD nb) (SN.inert-BD nb)
               (bundle-τ-inv linkBD lo hi (SN.csC-BD nb) (SN.csS-BD nb) (SN.bfC-BD nb) (SN.bfS-BD nb) (SN.inert-BD nb) s2)
...     | csc′ , css′ , bfc′ , bfs′ , ip′ , bdeq , abseq , mu =
          SN.mkNodeB (SN.csC-AB nb) (SN.csS-AB nb) (SN.bfC-AB nb) (SN.bfS-AB nb) csc′ css′ bfc′ bfs′ (SN.cp-B nb) (SN.inert-AB nb) ip′
          , trans eq (cong (λ z → z ∥⇘ apiES ⇙ decCP linkAB linkBD (SN.cp-B nb))
                        (trans eqR (cong (λ w → bundleG linkAB hi lo (SN.csC-AB nb) (SN.csS-AB nb) (SN.bfC-AB nb) (SN.bfS-AB nb) (SN.inert-AB nb) ⦀ w) bdeq)))
          , cong (λ z → (absBundleG linkAB hi lo (SN.csC-AB nb) (SN.csS-AB nb) (SN.bfC-AB nb) (SN.bfS-AB nb) (SN.inert-AB nb) ⦀ z) ∥⇘ apiES ⇙ decCP linkAB linkBD (SN.cp-B nb)) (sym abseq)
          , +-monoʳ-< (μBun (SN.csC-AB nb) (SN.csS-AB nb) (SN.bfC-AB nb) (SN.bfS-AB nb) (SN.inert-AB nb)) mu

-- NODE C
nodeC-τ-μ : (nc : NodeStateC) {C′ : NetProc}
  → decNodeC nc ─[ τ ]─► C′
  → Σ[ nc′ ∈ NodeStateC ] (C′ ≡ decNodeC nc′) × (absNodeC nc ≡ absNodeC nc′) × (μ'NodeC nc′ < μ'NodeC nc)
nodeC-τ-μ nc step with reflect-node-τ _ _ step
... | driverτ Dr′ ds _ = ⊥-elim (decCP-no-τ linkAC linkCD (SN.cp-C nc) ds)
nodeC-τ-μ nc step | bundleτ Bd′ bs eq
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt)
           (bundleG linkAC hi lo (SN.csC-AC nc) (SN.csS-AC nc) (SN.bfC-AC nc) (SN.bfS-AC nc) (SN.inert-AC nc)) _ bs
...   | PEA.τL _ s1 eqL
        with bundle-step linkAC hi lo (SN.csC-AC nc) (SN.csS-AC nc) (SN.bfC-AC nc) (SN.bfS-AC nc) (SN.inert-AC nc)
               (bundle-τ-inv linkAC hi lo (SN.csC-AC nc) (SN.csS-AC nc) (SN.bfC-AC nc) (SN.bfS-AC nc) (SN.inert-AC nc) s1)
...     | csc′ , css′ , bfc′ , bfs′ , ip′ , bdeq , abseq , mu =
          SN.mkNodeC csc′ css′ bfc′ bfs′ (SN.csC-CD nc) (SN.csS-CD nc) (SN.bfC-CD nc) (SN.bfS-CD nc) (SN.cp-C nc) ip′ (SN.inert-CD nc)
          , trans eq (cong (λ z → z ∥⇘ apiES ⇙ decCP linkAC linkCD (SN.cp-C nc))
                        (trans eqL (cong (λ w → w ⦀ bundleG linkCD lo hi (SN.csC-CD nc) (SN.csS-CD nc) (SN.bfC-CD nc) (SN.bfS-CD nc) (SN.inert-CD nc)) bdeq)))
          , cong (λ z → (z ⦀ absBundleG linkCD lo hi (SN.csC-CD nc) (SN.csS-CD nc) (SN.bfC-CD nc) (SN.bfS-CD nc) (SN.inert-CD nc)) ∥⇘ apiES ⇙ decCP linkAC linkCD (SN.cp-C nc)) (sym abseq)
          , +-monoˡ-< (μBun (SN.csC-CD nc) (SN.csS-CD nc) (SN.bfC-CD nc) (SN.bfS-CD nc) (SN.inert-CD nc)) mu
nodeC-τ-μ nc step | bundleτ Bd′ bs eq | PEA.τR _ s2 eqR
        with bundle-step linkCD lo hi (SN.csC-CD nc) (SN.csS-CD nc) (SN.bfC-CD nc) (SN.bfS-CD nc) (SN.inert-CD nc)
               (bundle-τ-inv linkCD lo hi (SN.csC-CD nc) (SN.csS-CD nc) (SN.bfC-CD nc) (SN.bfS-CD nc) (SN.inert-CD nc) s2)
...     | csc′ , css′ , bfc′ , bfs′ , ip′ , bdeq , abseq , mu =
          SN.mkNodeC (SN.csC-AC nc) (SN.csS-AC nc) (SN.bfC-AC nc) (SN.bfS-AC nc) csc′ css′ bfc′ bfs′ (SN.cp-C nc) (SN.inert-AC nc) ip′
          , trans eq (cong (λ z → z ∥⇘ apiES ⇙ decCP linkAC linkCD (SN.cp-C nc))
                        (trans eqR (cong (λ w → bundleG linkAC hi lo (SN.csC-AC nc) (SN.csS-AC nc) (SN.bfC-AC nc) (SN.bfS-AC nc) (SN.inert-AC nc) ⦀ w) bdeq)))
          , cong (λ z → (absBundleG linkAC hi lo (SN.csC-AC nc) (SN.csS-AC nc) (SN.bfC-AC nc) (SN.bfS-AC nc) (SN.inert-AC nc) ⦀ z) ∥⇘ apiES ⇙ decCP linkAC linkCD (SN.cp-C nc)) (sym abseq)
          , +-monoʳ-< (μBun (SN.csC-AC nc) (SN.csS-AC nc) (SN.bfC-AC nc) (SN.bfS-AC nc) (SN.inert-AC nc)) mu

-- NODE D
nodeD-τ-μ : (nd : NodeStateD) {D′ : NetProc}
  → decNodeD nd ─[ τ ]─► D′
  → Σ[ nd′ ∈ NodeStateD ] (D′ ≡ decNodeD nd′) × (absNodeD nd ≡ absNodeD nd′) × (μ'NodeD nd′ < μ'NodeD nd)
nodeD-τ-μ nd step with reflect-node-τ _ _ step
... | driverτ Dr′ ds _
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decConsD linkBD (SN.cons-BD nd)) (decConsD linkCD (SN.cons-CD nd)) ds
...   | PEA.τL _ ps _ = ⊥-elim (decConsD-no-τ linkBD (SN.cons-BD nd) ps)
...   | PEA.τR _ qs _ = ⊥-elim (decConsD-no-τ linkCD (SN.cons-CD nd) qs)
nodeD-τ-μ nd step | bundleτ Bd′ bs eq
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt)
           (bundleG linkBD hi lo (SN.csC-BD nd) (SN.csS-BD nd) (SN.bfC-BD nd) (SN.bfS-BD nd) (SN.inert-BD nd)) _ bs
...   | PEA.τL _ s1 eqL
        with bundle-step linkBD hi lo (SN.csC-BD nd) (SN.csS-BD nd) (SN.bfC-BD nd) (SN.bfS-BD nd) (SN.inert-BD nd)
               (bundle-τ-inv linkBD hi lo (SN.csC-BD nd) (SN.csS-BD nd) (SN.bfC-BD nd) (SN.bfS-BD nd) (SN.inert-BD nd) s1)
...     | csc′ , css′ , bfc′ , bfs′ , ip′ , bdeq , abseq , mu =
          SN.mkNodeD csc′ css′ bfc′ bfs′ (SN.cons-BD nd) (SN.csC-CD nd) (SN.csS-CD nd) (SN.bfC-CD nd) (SN.bfS-CD nd) (SN.cons-CD nd) ip′ (SN.inert-CD nd)
          , trans eq (cong (λ z → z ∥⇘ apiES ⇙ (decConsD linkBD (SN.cons-BD nd) ⦀ decConsD linkCD (SN.cons-CD nd)))
                        (trans eqL (cong (λ w → w ⦀ bundleG linkCD hi lo (SN.csC-CD nd) (SN.csS-CD nd) (SN.bfC-CD nd) (SN.bfS-CD nd) (SN.inert-CD nd)) bdeq)))
          , cong (λ z → (z ⦀ absBundleG linkCD hi lo (SN.csC-CD nd) (SN.csS-CD nd) (SN.bfC-CD nd) (SN.bfS-CD nd) (SN.inert-CD nd)) ∥⇘ apiES ⇙ (decConsD linkBD (SN.cons-BD nd) ⦀ decConsD linkCD (SN.cons-CD nd))) (sym abseq)
          , +-monoˡ-< (μBun (SN.csC-CD nd) (SN.csS-CD nd) (SN.bfC-CD nd) (SN.bfS-CD nd) (SN.inert-CD nd)) mu
nodeD-τ-μ nd step | bundleτ Bd′ bs eq | PEA.τR _ s2 eqR
        with bundle-step linkCD hi lo (SN.csC-CD nd) (SN.csS-CD nd) (SN.bfC-CD nd) (SN.bfS-CD nd) (SN.inert-CD nd)
               (bundle-τ-inv linkCD hi lo (SN.csC-CD nd) (SN.csS-CD nd) (SN.bfC-CD nd) (SN.bfS-CD nd) (SN.inert-CD nd) s2)
...     | csc′ , css′ , bfc′ , bfs′ , ip′ , bdeq , abseq , mu =
          SN.mkNodeD (SN.csC-BD nd) (SN.csS-BD nd) (SN.bfC-BD nd) (SN.bfS-BD nd) (SN.cons-BD nd) csc′ css′ bfc′ bfs′ (SN.cons-CD nd) (SN.inert-BD nd) ip′
          , trans eq (cong (λ z → z ∥⇘ apiES ⇙ (decConsD linkBD (SN.cons-BD nd) ⦀ decConsD linkCD (SN.cons-CD nd)))
                        (trans eqR (cong (λ w → bundleG linkBD hi lo (SN.csC-BD nd) (SN.csS-BD nd) (SN.bfC-BD nd) (SN.bfS-BD nd) (SN.inert-BD nd) ⦀ w) bdeq)))
          , cong (λ z → (absBundleG linkBD hi lo (SN.csC-BD nd) (SN.csS-BD nd) (SN.bfC-BD nd) (SN.bfS-BD nd) (SN.inert-BD nd) ⦀ z) ∥⇘ apiES ⇙ (decConsD linkBD (SN.cons-BD nd) ⦀ decConsD linkCD (SN.cons-CD nd))) (sym abseq)
          , +-monoʳ-< (μBun (SN.csC-BD nd) (SN.csS-BD nd) (SN.bfC-BD nd) (SN.bfS-BD nd) (SN.inert-BD nd)) mu

------------------------------------------------------------------------
-- `nodes-τ-μ'↓` — a whole-nodes τ (a peer sil in exactly one node) lands on
-- `nodesOf s′`, leaves `absNodesOf`/`med` UNCHANGED, and strictly drops `μ'Sys`.
------------------------------------------------------------------------

nodes-τ-μ'↓ : (s : SysState) {N′ : NetProc}
  → nodesOf s ─[ τ ]─► N′
  → Σ[ s′ ∈ SysState ] (N′ ≡ nodesOf s′) × (med s ≡ med s′) × (absNodesOf s ≡ absNodesOf s′) × (μ'Sys s′ < μ'Sys s)
nodes-τ-μ'↓ s step
  with reflect-nodes-τ (decNodeA (nA s)) (decNodeB (nB s)) (decNodeC (nC s)) (decNodeD (nD s)) step
... | nAτ A′ as eq with nodeA-τ-μ (nA s) as
...   | na′ , A′≡ , absEq , mu =
        mkSys (med s) na′ (nB s) (nC s) (nD s)
        , trans eq (cong (λ z → z ⦀ (decNodeB (nB s) ⦀ (decNodeC (nC s) ⦀ decNodeD (nD s)))) A′≡)
        , refl
        , cong (λ z → z ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) absEq
        , +-monoˡ-< (μ'NodeB (nB s) + (μ'NodeC (nC s) + μ'NodeD (nD s))) mu
nodes-τ-μ'↓ s step | nBτ B′ bs eq with nodeB-τ-μ (nB s) bs
...   | nb′ , B′≡ , absEq , mu =
        mkSys (med s) (nA s) nb′ (nC s) (nD s)
        , trans eq (cong (λ z → decNodeA (nA s) ⦀ (z ⦀ (decNodeC (nC s) ⦀ decNodeD (nD s)))) B′≡)
        , refl
        , cong (λ z → absNodeA (nA s) ⦀ (z ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) absEq
        , +-monoʳ-< (μ'NodeA (nA s)) (+-monoˡ-< (μ'NodeC (nC s) + μ'NodeD (nD s)) mu)
nodes-τ-μ'↓ s step | nCτ C′ cs eq with nodeC-τ-μ (nC s) cs
...   | nc′ , C′≡ , absEq , mu =
        mkSys (med s) (nA s) (nB s) nc′ (nD s)
        , trans eq (cong (λ z → decNodeA (nA s) ⦀ (decNodeB (nB s) ⦀ (z ⦀ decNodeD (nD s)))) C′≡)
        , refl
        , cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (z ⦀ absNodeD (nD s)))) absEq
        , +-monoʳ-< (μ'NodeA (nA s)) (+-monoʳ-< (μ'NodeB (nB s)) (+-monoˡ-< (μ'NodeD (nD s)) mu))
nodes-τ-μ'↓ s step | nDτ D′ ds eq with nodeD-τ-μ (nD s) ds
...   | nd′ , D′≡ , absEq , mu =
        mkSys (med s) (nA s) (nB s) (nC s) nd′
        , trans eq (cong (λ z → decNodeA (nA s) ⦀ (decNodeB (nB s) ⦀ (decNodeC (nC s) ⦀ z))) D′≡)
        , refl
        , cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ z))) absEq
        , +-monoʳ-< (μ'NodeA (nA s)) (+-monoʳ-< (μ'NodeB (nB s)) (+-monoʳ-< (μ'NodeC (nC s)) mu))
