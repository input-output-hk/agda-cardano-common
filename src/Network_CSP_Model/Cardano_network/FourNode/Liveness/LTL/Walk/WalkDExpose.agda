{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the COMBINED D-PHASE EXPOSURE CONE
-- (`Praos.WalkDExpose`).
--
-- `WalkApiDrop.top-nodes-abs-wt` produces the whole-system successor `s′`
-- and the strict `μTot` drop, but DISCARDS node D's consume-phase
-- relationship into the measure arithmetic.  `deliver`'s successor branch
-- needs the pending invariant `Pr` preserved at `s′`, which is a fact about
-- nD's two D-consume phases — precisely the data the node-D peel
-- (`nodeD-ev-api-abs-wt`, ctors `ndEBawt1`/`ndEBawt2`) already carries as
-- `ConsAdv`/fixity but `top-nodes-abs-wt` throws away.
--
-- `top-nodes-abs-expose` RE-MIRRORS `top-nodes-abs-wt` (same case split,
-- REUSING the four frozen node peels by import) and ADDITIONALLY returns a
-- `DReport s s′` recording how nD's `cons-BD`/`cons-CD` phases relate in the
-- successor:
--   · `dFix` — the firing node is A/B/C, so `nD s′ ≡ nD s` literally ⇒ both
--     D-consume phases are unchanged (`refl`/`refl`);
--   · `dBD` — D fired on link BD: `cons-BD` advances by one `ConsAdv`, `cons-CD`
--     is fixed;
--   · `dCD` — D fired on link CD: the mirror.
--
-- This is the Pr-preservation half of the two flagged gaps; the block-value
-- (arrivedD's `a ≡ b` conjunct) is handled separately in the assembly.  No
-- postulate/hole/meta.  WalkApiDrop / SysIoLink6 stay READ-ONLY.
------------------------------------------------------------------------

open import Data.Nat using ( ℕ; _<_; _+_ )
open import Data.Nat.Properties using ( +-monoˡ-<; +-monoʳ-< )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkDExpose (blkA : Block₃) where

open import Level using (0ℓ)
open import Data.Product using ( _,_; Σ; _×_; Σ-syntax )
open import Data.Unit.Polymorphic using ( tt )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; cong; sym )
open import Data.Empty using ( ⊥-elim )
open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using
  ( p; apiES; linkAB; linkAC; linkBD; linkCD; Block₃ )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟; apiBF; recvBFBlock )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using ( hi )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_ )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; EventSet )
open EventSet using ( mem )
open Op using () renaming ( ∅ES to ∅ESa )

import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep
open SStep using ( NetProc )

import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload}) as PEA

open SStep using
  ( absBundleG; absNodeA; absNodeB; absNodeC; absNodeD )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using
  ( ConsPh; cph; cblk; cons-BD; cons-CD; cp3 )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA using
  ( SysState; mkSys; med; nA; nB; nC; nD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysRoute blkA using
  ( absNodeA-fp; absNodeB-fp; absNodeC-fp; absNodeD-fp
  ; nodeB-no-when-A; nodeC-no-when-A; nodeD-no-when-A; nodeC-no-when-B; nodeD-no-when-B; nodeD-no-when-C
  ; absNodeB-no-when-A; absNodeC-no-when-A; absNodeD-no-when-A; absNodeC-no-when-B; absNodeD-no-when-B; absNodeD-no-when-C )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_RouteLnLf blkA
  using ( noOffer→viewV )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink6 blkA
  using ( ⦀-wev-L; ⦀-wev-R
        ; nodeA-no-when-B; nodeA-no-when-C; nodeA-no-when-D
        ; nodeB-no-when-C; nodeB-no-when-D; nodeC-no-when-D )

-- the driver adjacencies + per-group measure congruences/advances
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkMeasure blkA using
  ( ConsAdv; cpW; prodW; consDW
  ; μG1-cong; μG2-cong
  ; μG1-adv-prod; μG1-adv-cons; μG2-adv-prod; μG2-adv-cons )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.Walk blkA using
  ( μTot; μTot-adv-G1; μTot-adv-G2 )
open SN using
  ( prod-AB; prod-AC; cp-B; cp-C )

-- the four frozen node peels (with their driver-advance / cpW-drop witnesses)
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkApiDrop blkA using
  ( NodeAEvR-abs-wt; naEBawt1; naEBawt2
  ; NodeBEvR-abs-wt; nbEBawt
  ; NodeCEvR-abs-wt; ncEBawt
  ; NodeDEvR-abs-wt; ndEBawt1; ndEBawt2
  ; nodeA-ev-api-abs-wt; nodeB-ev-api-abs-wt; nodeC-ev-api-abs-wt; nodeD-ev-api-abs-wt )

------------------------------------------------------------------------
-- `DReport s s′`: how nD's two D-consume phases relate in the successor.
------------------------------------------------------------------------

-- e-indexed by the fired event `evLabel X e a`: the `dBD`/`dCD` delivering hop
-- carries the label identity `apiBF link{BD,CD} hi recvBFBlock` (`deliver` builds
-- `arrivedD` from it), conditioned on the source D-consume phase being `cp3`.
data DReport (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) : Set₁ where
  -- the firing node was A/B/C, so nD is unchanged ⇒ both consume phases fixed
  dFix : SN.NodeStateD.cons-BD (nD s′) ≡ SN.NodeStateD.cons-BD (nD s)
       → SN.NodeStateD.cons-CD (nD s′) ≡ SN.NodeStateD.cons-CD (nD s)
       → DReport s s′ e a
  -- D fired on link BD (G1): cons-BD advances by one ConsAdv, cons-CD fixed;
  -- if BD-consume was at cp3 the fired event is `apiBF linkBD hi recvBFBlock`
  dBD  : ConsAdv (cph (SN.NodeStateD.cons-BD (nD s))) (cph (SN.NodeStateD.cons-BD (nD s′)))
       → SN.NodeStateD.cons-CD (nD s′) ≡ SN.NodeStateD.cons-CD (nD s)
       -- SESSION-36 ANCHOR: the label's block `b″` IS the block the SUCCESSOR
       -- state records, so a state-side value invariant at `s′` reaches it
       → (cph (SN.NodeStateD.cons-BD (nD s)) ≡ cp3
          → Σ[ b″ ∈ Block₃ ]
              (evLabel X e a ≡ evLabel Block₃ (apiBF linkBD hi recvBFBlock) b″)
            × (cblk (SN.NodeStateD.cons-BD (nD s′)) ≡ b″))
       → DReport s s′ e a
  -- D fired on link CD (G2): cons-CD advances by one ConsAdv, cons-BD fixed;
  -- if CD-consume was at cp3 the fired event is `apiBF linkCD hi recvBFBlock`
  dCD  : ConsAdv (cph (SN.NodeStateD.cons-CD (nD s))) (cph (SN.NodeStateD.cons-CD (nD s′)))
       → SN.NodeStateD.cons-BD (nD s′) ≡ SN.NodeStateD.cons-BD (nD s)
       -- SESSION-36 ANCHOR (mirror of `dBD`'s)
       → (cph (SN.NodeStateD.cons-CD (nD s)) ≡ cp3
          → Σ[ b″ ∈ Block₃ ]
              (evLabel X e a ≡ evLabel Block₃ (apiBF linkCD hi recvBFBlock) b″)
            × (cblk (SN.NodeStateD.cons-CD (nD s′)) ≡ b″))
       → DReport s s′ e a

------------------------------------------------------------------------
-- `top-nodes-abs-expose`: `top-nodes-abs-wt` + the `DReport`.
------------------------------------------------------------------------

top-nodes-abs-expose : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → SStep.absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ s′ ∈ SysState ] (med s ≡ med s′) × (M ≡ SStep.absNodesOf s′)
      × (SStep.nodesOf s ═[ ev (evl (evLabel X e a)) ]═► SStep.nodesOf s′)
      × (μTot s′ < μTot s) × DReport s s′ e a
top-nodes-abs-expose s apimem nodesStep
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (absNodeA (nA s)) (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s))) nodesStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sA sRest = ⊥-elim (SStep.⦀-noOffer (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s))
        (absNodeB-no-when-A (nB s) apimem (absNodeA-fp (nA s) apimem sA))
        (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
          (absNodeC-no-when-A (nC s) apimem (absNodeA-fp (nA s) apimem sA))
          (absNodeD-no-when-A (nD s) apimem (absNodeA-fp (nA s) apimem sA))) (_ , sRest))
... | PEA.evL _ sA with nodeA-ev-api-abs-wt (nA s) apimem sA
...   | naEBawt1 na′ Meq weakRunA padv pACeq =
        mkSys (med s) na′ (nB s) (nC s) (nD s) , refl ,
        cong (λ z → z ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) Meq ,
        wrunA ,
        μTot-adv-G1 s (mkSys (med s) na′ (nB s) (nC s) (nD s))
          (μG1-adv-prod s (mkSys (med s) na′ (nB s) (nC s) (nD s)) padv refl refl)
          (sym (μG2-cong s (mkSys (med s) na′ (nB s) (nC s) (nD s)) (sym pACeq) refl refl))
          refl
        , dFix refl refl
  where
    fpA = absNodeA-fp (nA s) apimem sA
    wrunA = ⦀-wev-L (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
              (noOffer→viewV _ (SStep.⦀-noOffer (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
                 (nodeB-no-when-A (nB s) apimem fpA)
                 (SStep.⦀-noOffer (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                    (nodeC-no-when-A (nC s) apimem fpA) (nodeD-no-when-A (nD s) apimem fpA))))
              weakRunA
...   | naEBawt2 na′ Meq weakRunA padv pABeq =
        mkSys (med s) na′ (nB s) (nC s) (nD s) , refl ,
        cong (λ z → z ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) Meq ,
        wrunA ,
        μTot-adv-G2 s (mkSys (med s) na′ (nB s) (nC s) (nD s))
          (sym (μG1-cong s (mkSys (med s) na′ (nB s) (nC s) (nD s)) (sym pABeq) refl refl))
          (μG2-adv-prod s (mkSys (med s) na′ (nB s) (nC s) (nD s)) padv refl refl)
          refl
        , dFix refl refl
  where
    fpA = absNodeA-fp (nA s) apimem sA
    wrunA = ⦀-wev-L (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
              (noOffer→viewV _ (SStep.⦀-noOffer (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
                 (nodeB-no-when-A (nB s) apimem fpA)
                 (SStep.⦀-noOffer (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                    (nodeC-no-when-A (nC s) apimem fpA) (nodeD-no-when-A (nD s) apimem fpA))))
              weakRunA
top-nodes-abs-expose s apimem nodesStep | PEA.evR _ sRest
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s)) sRest
... | PEA.evSync () _ _
... | PEA.evBoth _ sB sCD = ⊥-elim (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
        (absNodeC-no-when-B (nC s) apimem (absNodeB-fp (nB s) apimem sB))
        (absNodeD-no-when-B (nD s) apimem (absNodeB-fp (nB s) apimem sB)) (_ , sCD))
... | PEA.evL _ sB with nodeB-ev-api-abs-wt (nB s) apimem sB
...   | nbEBawt nb′ Meq weakRunB cpdrop =
        mkSys (med s) (nA s) nb′ (nC s) (nD s) , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (z ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) Meq ,
        ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (nodeA-no-when-B (nA s) apimem fpB))
          (⦀-wev-L (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (noOffer→viewV _ (SStep.⦀-noOffer (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (nodeC-no-when-B (nC s) apimem fpB) (nodeD-no-when-B (nD s) apimem fpB)))
             weakRunB)
        ,
        μTot-adv-G1 s (mkSys (med s) (nA s) nb′ (nC s) (nD s))
          (+-monoʳ-< (prodW (prod-AB (nA s))) (+-monoˡ-< (consDW (cons-BD (nD s))) cpdrop))
          refl refl
        , dFix refl refl
  where fpB = absNodeB-fp (nB s) apimem sB
top-nodes-abs-expose s apimem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absNodeC (nC s)) (absNodeD (nD s)) sCD
... | PEA.evSync () _ _
... | PEA.evBoth _ sC sD = ⊥-elim (absNodeD-no-when-C (nD s) apimem (absNodeC-fp (nC s) apimem sC) (_ , sD))
... | PEA.evL _ sC with nodeC-ev-api-abs-wt (nC s) apimem sC
...   | ncEBawt nc′ Meq weakRunC cpdrop =
        mkSys (med s) (nA s) (nB s) nc′ (nD s) , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (z ⦀ absNodeD (nD s)))) Meq ,
        ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (nodeA-no-when-C (nA s) apimem fpC))
          (⦀-wev-R (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (noOffer→viewV _ (nodeB-no-when-C (nB s) apimem fpC))
             (⦀-wev-L (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (noOffer→viewV _ (nodeD-no-when-C (nD s) apimem fpC))
                weakRunC))
        ,
        μTot-adv-G2 s (mkSys (med s) (nA s) (nB s) nc′ (nD s))
          refl
          (+-monoʳ-< (prodW (prod-AC (nA s))) (+-monoˡ-< (consDW (cons-CD (nD s))) cpdrop))
          refl
        , dFix refl refl
  where fpC = absNodeC-fp (nC s) apimem sC
top-nodes-abs-expose s apimem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD | PEA.evR _ sD
    with nodeD-ev-api-abs-wt (nD s) apimem sD
... | ndEBawt1 nd′ Meq weakRunD cadv cCDeq lblD =
        mkSys (med s) (nA s) (nB s) (nC s) nd′ , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ z))) Meq ,
        wrunD ,
        μTot-adv-G1 s (mkSys (med s) (nA s) (nB s) (nC s) nd′)
          (μG1-adv-cons s (mkSys (med s) (nA s) (nB s) (nC s) nd′) refl refl cadv)
          (sym (μG2-cong s (mkSys (med s) (nA s) (nB s) (nC s) nd′) refl refl (sym cCDeq)))
          refl
        , dBD cadv cCDeq lblD
  where
    fpD = absNodeD-fp (nD s) apimem sD
    wrunD = ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
              (noOffer→viewV _ (nodeA-no-when-D (nA s) apimem fpD))
              (⦀-wev-R (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
                 (noOffer→viewV _ (nodeB-no-when-D (nB s) apimem fpD))
                 (⦀-wev-R (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                    (noOffer→viewV _ (nodeC-no-when-D (nC s) apimem fpD))
                    weakRunD))
... | ndEBawt2 nd′ Meq weakRunD cadv cBDeq lblD =
        mkSys (med s) (nA s) (nB s) (nC s) nd′ , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ z))) Meq ,
        wrunD ,
        μTot-adv-G2 s (mkSys (med s) (nA s) (nB s) (nC s) nd′)
          (sym (μG1-cong s (mkSys (med s) (nA s) (nB s) (nC s) nd′) refl refl (sym cBDeq)))
          (μG2-adv-cons s (mkSys (med s) (nA s) (nB s) (nC s) nd′) refl refl cadv)
          refl
        , dCD cadv cBDeq lblD
  where
    fpD = absNodeD-fp (nD s) apimem sD
    wrunD = ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
              (noOffer→viewV _ (nodeA-no-when-D (nA s) apimem fpD))
              (⦀-wev-R (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
                 (noOffer→viewV _ (nodeB-no-when-D (nB s) apimem fpD))
                 (⦀-wev-R (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                    (noOffer→viewV _ (nodeC-no-when-D (nC s) apimem fpD))
                    weakRunD))
