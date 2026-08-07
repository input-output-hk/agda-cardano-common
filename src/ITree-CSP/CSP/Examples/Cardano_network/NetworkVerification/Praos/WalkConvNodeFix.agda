{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- R3 — the io-sync NODE cone DRIVER-FIXITY re-mirror (top-nodes-io-abs-fix).
--
-- The io-sync analogue of the WEIGHT-DROP cone WalkConvNodeDrop, but
-- instead of a nodesWt drop it exposes that an io-sync leaves EVERY node
-- DRIVER phase (prod-AB/prod-AC/cp-B/cp-C/cons-BD/cons-CD) UNCHANGED, so
-- muG1/muG2 are preserved across a hidden io-sync (liftt*-mu neutrality).
-- Each per-node driver equality is refl (the io leaves build
-- mkNodeX ...peers... (driver = original)); the WORK is the 4x12 dispatch
-- re-mirror.  Reuses absBundleG-io-prod-wt from WalkConvNodeDrop for the
-- bundle successor + weak run (its bundleWt drop field is discarded).
--
-- No postulate/hole/meta.
------------------------------------------------------------------------

open import Data.Nat using ( ℕ; _<_; _+_ )
open import Data.Nat.Properties using ( +-monoˡ-<; +-monoʳ-< )
open import Relation.Binary.PropositionalEquality using ( subst₂ )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvNodeFix (blkA : Block₃) where

open import Level using (0ℓ)
open import Data.Product using ( _,_ )
open import Data.Maybe using ( nothing )
open import Relation.Binary.PropositionalEquality using ( _≡_ )
open import Relation.Nullary using ( ¬_ )
open import Process_Trees using ( PTree; ExtI )

-- re-export PART 5 (all 12 backward production leaves) so downstream imports SysIoLink6
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysIoLink5 blkA public

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using
  ( p; apiES; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟ )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel; τ )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[τ*]─►_; τ*-refl; τ*-step; τ*-trans; _═[_]═►_; wev )

-- the operators used to shape a node (`⦀` interleave, `∥⇘ A ⇙` sync-gated stack)
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; EventSet; viewV )
open EventSet using ( mem )

-- the STRONG single-step intro congruences to fold over
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep blkA as SStep
open SStep using
  ( NetProc; IoOffers
  ; ⦀-τ-L; ⦀-τ-R; ∥⇘⇙-τ-L; ∥⇘⇙-τ-R
  ; ⦀-ev-L; ⦀-ev-R; ∥⇘⇙-ev-sync; ∥⇘⇙-ev-soloL; ∥⇘⇙-ev-soloR )

------------------------------------------------------------------------
-- PART 2 imports — the abstract per-channel BUNDLE inversions produce a
-- concrete WEAK run, so we need: the abstract/concrete bundle builders
-- (`absBundleG`/`bundleG`), the committed leaf production lemmas
-- (`decX-ev-prod-abs`, re-exported through SysIoLink5), the 12-peer peel
-- (`PEA.Par-ev-elim`), and the committed forward-io non-offer / dir
-- machinery (from the SysOracle_RouteLnLf chain — NOT re-exported by the
-- SysIoLink4/5/6 backward chain, so imported directly here).
------------------------------------------------------------------------
open import Data.Empty using ( ⊥-elim )
open import Data.Unit.Polymorphic using ( tt )
open import Relation.Nullary using ( yes; no )
open import Relation.Binary.PropositionalEquality using ( refl; cong; trans; sym; _≢_ )
open import Class.DecEq using ( _≟_ )
open import Data.Product using ( Σ; _×_; Σ-syntax )
open import Data.Sum using ( inj₁; inj₂; _⊎_ )

open import CSP.Examples.Cardano_network.Base using
  ( Dir; lo; hi; N2N_ChainSync; N2N_BlockFetch; N2N_KeepAlive; N2N_TxSubmission; N2N_LeiosNotify; N2N_LeiosFetch )
open import CSP.Examples.Cardano_network.Net p using
  ( Link; input; output; done; break; apiCS; apiBF; apiKA; apiTS; apiLN; apiLF
  ; sndmsg; rcvmsg; tx; sndack; rcvack; ack )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )
import CSP.Examples.Cardano_network.ChainSync p as CS
import CSP.Examples.Cardano_network.BlockFetch p as BF
import CSP.Examples.Cardano_network.KeepAlive p as KA
import CSP.Examples.Cardano_network.TxSubmission p as TS
import CSP.Examples.Cardano_network.LeiosNotify p as LN
import CSP.Examples.Cardano_network.LeiosFetch p as LF
open import CSP.Examples.Cardano_network.NetworkPar p using ( ιCS; ιBF; ιKA; ιTS; ιLN; ιLF )
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode blkA as SN
open SN using
  ( CScPos; CSsPos; BFcPos; BFsPos; KAcPos; KAsPos; TScPos; TSsPos; LNcPos; LNsPos; LFcPos; LFsPos
  ; InertPos; kac; kas; tsc; tss; lnc; lns; lfc; lfs; bundleG
  ; consuming; producing; consD
  ; decKAc; decKAs; decCSc; decCSs; decBFc; decBFs; decTSc; decTSs; decLNc; decLNs; decLFc; decLFs )
open SStep using
  ( absBundleG; absKAc; absKAs; absCSc; absCSs; absBFc; absBFs
  ; absTSc; absTSs; absLNc; absLNs; absLFc; absLFs
  ; absNodeA; absNodeB; absNodeC; absNodeD
  ; coarsenCSc; coarsenCSs; coarsenBFc; coarsenBFs; coarsenKAc; coarsenKAs; coarsenTSc; coarsenTSs
  ; coarsenLNc; coarsenLNs; coarsenLFc; coarsenLFs )
-- node states, decodes and constructors (qualified: SN.decNodeA / SN.mkNodeA / SN.NodeStateA…)
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_NodeTauEv blkA as MSysOracle_NodeTauEv
open MSysOracle_NodeTauEv using
  ( tableSpec-ev-inv; nothing-absurd )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_RouteLnLf blkA using
  ( csEvDir; csCnxt-dir-no; csSnxt-dir-no; noOffer→viewV
  ; csTail-css-noOffer; csTail-bfc-noOffer
  ; decKAc-noOffer; decKAs-noOffer; decCSc-dir-noOffer; decCSs-dir-noOffer
  ; ιKA⁻¹∘ιCS
  ; absKAc-noCS; absKAs-noCS; absBFc-noCS; absBFs-noCS; absTSc-noCS; absTSs-noCS
  ; absLNc-noCS; absLNs-noCS; absLFc-noCS; absLFs-noCS
  ; absCSs-dir-noBoth; absCSc-dir-noBoth
  ; bfEvDir; bfCnxt-dir-no; bfSnxt-dir-no
  ; bfTail-bfs-noOffer; bfTail-tsc-noOffer
  ; decCSc-noBFgen; decCSs-noBFgen; decBFc-dir-noOffer; decBFs-dir-noOffer
  ; ιKA⁻¹∘ιBF
  ; absKAc-noBF; absKAs-noBF; absCSc-noBF; absCSs-noBF; absTSc-noBF; absTSs-noBF
  ; absLNc-noBF; absLNs-noBF; absLFc-noBF; absLFs-noBF
  ; absBFs-dir-noBoth; absBFc-dir-noBoth
  ; kaEvDir; kaCnxt-dir-no; kaSnxt-dir-no
  ; kaTail-kas-noOffer; kaTail-csc-noOffer
  ; decKAc-dir-noOffer; decKAs-dir-noOffer
  ; absCSc-noKA; absCSs-noKA; absBFc-noKA; absBFs-noKA; absTSc-noKA; absTSs-noKA
  ; absLNc-noKA; absLNs-noKA; absLFc-noKA; absLFs-noKA
  ; absKAs-dir-noBoth; absKAc-dir-noBoth
  ; tsEvDir; tsCnxt-dir-no; tsSnxt-dir-no
  ; tsTail-tss-noOffer; tsTail-lnc-noOffer
  ; decTSc-dir-noOffer; decTSs-dir-noOffer
  ; decCSc-noTSgen; decCSs-noTSgen; decBFc-noTSgen; decBFs-noTSgen; ιKA⁻¹∘ιTS
  ; absKAc-noTS; absKAs-noTS; absCSc-noTS; absCSs-noTS; absBFc-noTS; absBFs-noTS
  ; absLNc-noTS; absLNs-noTS; absLFc-noTS; absLFs-noTS
  ; absTSs-dir-noBoth; absTSc-dir-noBoth
  -- LN channel
  ; lnEvDir; lnCnxt-dir-no; lnSnxt-dir-no
  ; lnTail-lns-noOffer; lnTail-lfc-noOffer
  ; decLNc-dir-noOffer; decLNs-dir-noOffer
  ; decCSc-noLNgen; decCSs-noLNgen; decBFc-noLNgen; decBFs-noLNgen
  ; decTSc-noOffer; decTSs-noOffer; ιKA⁻¹∘ιLN; ιTS⁻¹∘ιLN
  ; absKAc-noLN; absKAs-noLN; absCSc-noLN; absCSs-noLN; absBFc-noLN; absBFs-noLN
  ; absTSc-noLN; absTSs-noLN; absLFc-noLN; absLFs-noLN
  ; absLNs-dir-noBoth; absLNc-dir-noBoth
  -- LF channel
  ; lfEvDir; lfCnxt-dir-no; lfSnxt-dir-no
  ; decLFc-dir-noOffer; decLFs-dir-noOffer
  ; decCSc-noLFgen; decCSs-noLFgen; decBFc-noLFgen; decBFs-noLFgen
  ; decLNc-noOffer; decLNs-noOffer; ιKA⁻¹∘ιLF; ιTS⁻¹∘ιLF; ιLN⁻¹∘ιLF
  ; absKAc-noLF; absKAs-noLF; absCSc-noLF; absCSs-noLF; absBFc-noLF; absBFs-noLF
  ; absTSc-noLF; absTSs-noLF; absLNc-noLF; absLNs-noLF
  ; absLFs-dir-noBoth; absLFc-dir-noBoth )
import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload}) as PEA
open Op using () renaming ( ∅ES to ∅ESa )

-- the api-link fingerprint + the committed per-channel concrete bundle io-link
-- pins (CS/BF/KA/TS/LN in SysOracle, LF in SysIoLink); NOT re-exported by the
-- SysIoLink4/5/6 (SysNode/SysStep) chain, so imported directly.
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle blkA as MSysOracle
open MSysOracle using
  ( ApiHasLink; ahlIn; ahlOut; apiLink-inj; io⇒¬api
  ; bundleCS-io-link-in; bundleCS-io-link-out; bundleBF-io-link-in; bundleBF-io-link-out
  ; bundleKA-io-link-in; bundleKA-io-link-out; bundleTS-io-link-in; bundleTS-io-link-out
  ; bundleLN-io-link-in; bundleLN-io-link-out )
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysIoLink blkA as MSysIoLink
open MSysIoLink using
  ( bundleLF-io-link-in; bundleLF-io-link-out
  ; bundleG-io-ahl; absBundleG-io-no
  ; nodeA-drv-io-no; nodeB-drv-io-no; nodeC-drv-io-no; nodeD-drv-io-no
  ; linkAB≢linkAC; linkAB≢linkBD; linkAC≢linkCD; linkBD≢linkCD )
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysIoLink3 blkA as MSysIoLink3
open MSysIoLink3 using
  ( absBundleG-io-ahl )

-- PART-2 (api node peels) machinery: api-link ctors + per-channel bundle api
-- link pins + abstract per-channel link non-offers + driver phase inversions.
-- Not re-exported by the SysNode/SysStep chain, so imported directly.
open MSysOracle using
  ( ahlCS; ahlBF; ahlKA; ahlTS; ahlLN; ahlLF; ahlDone
  ; decProd-ev-link; decConsD-ev-link; decCP-ev-link
  ; bundleCS-ev-link; bundleBF-ev-link; bundleKA-ev-link; bundleTS-ev-link; bundleLN-ev-link
  ; absBundleG-CS-link-noIoOffer; absBundleG-BF-link-noIoOffer )
open MSysIoLink using
  ( bundleLF-ev-link
  ; absBundleG-KA-link-noIoOffer; absBundleG-TS-link-noIoOffer
  ; absBundleG-LN-link-noIoOffer; absBundleG-LF-link-noIoOffer )
open MSysOracle_NodeTauEv using
  ( decProd-ev-inv; ProdEvR; peR
  ; decConsD-ev-inv; ConsDEvR; cdR
  ; decCP-ev-inv; CPEvR; cpR-cons; cpR-prod )

-- PART-2 (top-nodes) machinery: SysState + 4-node fingerprints + FORWARD
-- pairwise/group non-offers (concrete api SysRoute, concrete io SysIoLink2 via
-- SysIoLink3 re-export, abstract io SysIoLink3).  The 6 REVERSE concrete api +
-- 6 REVERSE concrete io non-offers are built below (they had no prior use).
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysDecode blkA using
  ( SysState; mkSys; med; nA; nB; nC; nD )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysRoute blkA using
  ( ApiIsProd; ApiIsCons; prod≢cons
  ; nodeA-fp; nodeB-fp; nodeC-fp; nodeD-fp
  ; absNodeA-fp; absNodeB-fp; absNodeC-fp; absNodeD-fp
  ; nodeB-no-when-A; nodeC-no-when-A; nodeD-no-when-A; nodeC-no-when-B; nodeD-no-when-B; nodeD-no-when-C
  ; absNodeB-no-when-A; absNodeC-no-when-A; absNodeD-no-when-A; absNodeC-no-when-B; absNodeD-no-when-B; absNodeD-no-when-C )
open MSysIoLink3 using
  ( role-clash; lo≢hi; linkAB≢linkCD; linkAC≢linkBD; RoleFP
  ; nodeA-io-fp; nodeB-io-fp; nodeC-io-fp; nodeD-io-fp
  ; nodeB-io-no-when-A; nodeC-io-no-when-A; nodeD-io-no-when-A; nodeC-io-no-when-B; nodeD-io-no-when-B; nodeD-io-no-when-C
  ; absNodeA-io-fp; absNodeB-io-fp; absNodeC-io-fp; absNodeD-io-fp
  ; absNodeB-io-no-when-A; absNodeC-io-no-when-A; absNodeD-io-no-when-A; absNodeC-io-no-when-B; absNodeD-io-no-when-B; absNodeD-io-no-when-C
  ; absGroupA-io-no; absGroupB-io-no )

------------------------------------------------------------------------
-- extra imports: the measure, the arithmetic scaffolding, the io-drop leaves,
-- and the SIL6-DEFINED helpers the re-mirror references.
------------------------------------------------------------------------
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvMeasure blkA
  using ( nodeWtA; nodeWtB; nodeWtC; nodeWtD; nodesWt )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvNodeWt blkA
  using ( bundleWt
        ; bundleWt-CSc-drop; bundleWt-CSs-drop; bundleWt-BFc-drop; bundleWt-BFs-drop
        ; bundleWt-KAc-drop; bundleWt-KAs-drop; bundleWt-TSc-drop; bundleWt-TSs-drop
        ; bundleWt-LNc-drop; bundleWt-LNs-drop; bundleWt-LFc-drop; bundleWt-LFs-drop
        ; nodeWtA-split; nodeWtB-split; nodeWtC-split; nodeWtD-split )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvIoDrop blkA
  using ( decCSc-ev-io-drop; decCSs-ev-io-drop; decBFc-ev-io-drop; decBFs-ev-io-drop
        ; decKAc-ev-io-drop; decKAs-ev-io-drop; decTSc-ev-io-drop; decTSs-ev-io-drop
        ; decLNc-ev-io-drop; decLNs-ev-io-drop; decLFc-ev-io-drop; decLFs-ev-io-drop )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysIoLink6 blkA
  using ( ⦀-wev-L; ⦀-wev-R; ∥⇘⇙-wev-soloL; ∥⇘⇙-wev-sync
        ; absCSc-ev-dir; absCSs-ev-dir; absBFc-ev-dir; absBFs-ev-dir
        ; absKAc-ev-dir; absKAs-ev-dir; absTSc-ev-dir; absTSs-ev-dir
        ; absLNc-ev-dir; absLNs-ev-dir; absLFc-ev-dir; absLFs-ev-dir
        ; bundleG-io-no
        ; nodeA-io-no-when-B; nodeA-io-no-when-C; nodeA-io-no-when-D
        ; nodeB-io-no-when-C; nodeB-io-no-when-D; nodeC-io-no-when-D )

-- reuse the WEIGHT-DROP bundle io-inversion (bundleWt drop field discarded)
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvNodeDrop blkA
  using ( BundleGEvR-abs-wt; bgEBwt; absBundleG-io-prod-wt )

------------------------------------------------------------------------
-- NODE-LEVEL DRIVER-FIXITY records: an io-sync successor node na′ whose
-- group DRIVER phases equal na's (all `refl` — the io leaves preserve them).
------------------------------------------------------------------------

data NodeAEvR-abs-fix (na : SN.NodeStateA) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                  (M : NetProc) : Set₁ where
  naEBafix : (na′ : SN.NodeStateA) → M ≡ absNodeA na′
        → SN.decNodeA na ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeA na′
        → SN.NodeStateA.prod-AB na ≡ SN.NodeStateA.prod-AB na′
        → SN.NodeStateA.prod-AC na ≡ SN.NodeStateA.prod-AC na′
        → NodeAEvR-abs-fix na e a M

data NodeBEvR-abs-fix (nb : SN.NodeStateB) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                  (M : NetProc) : Set₁ where
  nbEBafix : (nb′ : SN.NodeStateB) → M ≡ absNodeB nb′
        → SN.decNodeB nb ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeB nb′
        → SN.NodeStateB.cp-B nb ≡ SN.NodeStateB.cp-B nb′
        → NodeBEvR-abs-fix nb e a M

data NodeCEvR-abs-fix (nc : SN.NodeStateC) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                  (M : NetProc) : Set₁ where
  ncEBafix : (nc′ : SN.NodeStateC) → M ≡ absNodeC nc′
        → SN.decNodeC nc ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeC nc′
        → SN.NodeStateC.cp-C nc ≡ SN.NodeStateC.cp-C nc′
        → NodeCEvR-abs-fix nc e a M

data NodeDEvR-abs-fix (nd : SN.NodeStateD) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                  (M : NetProc) : Set₁ where
  ndEBafix : (nd′ : SN.NodeStateD) → M ≡ absNodeD nd′
        → SN.decNodeD nd ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeD nd′
        → SN.NodeStateD.cons-BD nd ≡ SN.NodeStateD.cons-BD nd′
        → SN.NodeStateD.cons-CD nd ≡ SN.NodeStateD.cons-CD nd′
        → NodeDEvR-abs-fix nd e a M
nodeA-io-AB-abs-fix : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeAEvR-abs-fix na e a ((Bd′ ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)))
nodeA-io-AB-abs-fix na {X} {e} {a} iomem sBAB
  with absBundleG-io-prod-wt linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) iomem sBAB
... | bgEBwt csc′ css′ bfc′ bfs′ ip′ eq run drop =
      naEBafix (SN.mkNodeA csc′ css′ bfc′ bfs′ (SN.NodeStateA.prod-AB na) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) ip′ (SN.NodeStateA.inert-AC na))
        (cong (λ z → (z ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na))) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeA-drv-io-no na iomem))
           (⦀-wev-L _ _
              (noOffer→viewV _ (bundleG-io-no linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)
                 (absBundleG-io-ahl linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) iomem sBAB) linkAB≢linkAC iomem))
              run))
        refl refl

nodeA-io-AC-abs-fix : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeAEvR-abs-fix na e a ((absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ⦀ Bd′) ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)))
nodeA-io-AC-abs-fix na {X} {e} {a} iomem sBAC
  with absBundleG-io-prod-wt linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) iomem sBAC
... | bgEBwt csc′ css′ bfc′ bfs′ ip′ eq run drop =
      naEBafix (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na) csc′ css′ bfc′ bfs′ (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) ip′)
        (cong (λ z → (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ⦀ z) ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na))) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeA-drv-io-no na iomem))
           (⦀-wev-R _ _
              (noOffer→viewV _ (bundleG-io-no linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
                 (absBundleG-io-ahl linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) iomem sBAC) (λ q → linkAB≢linkAC (sym q)) iomem))
              run))
        refl refl

nodeB-io-AB-abs-fix : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeBEvR-abs-fix nb e a ((Bd′ ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
nodeB-io-AB-abs-fix nb {X} {e} {a} iomem sBAB
  with absBundleG-io-prod-wt linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) iomem sBAB
... | bgEBwt csc′ css′ bfc′ bfs′ ip′ eq run drop =
      nbEBafix (SN.mkNodeB csc′ css′ bfc′ bfs′ (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) ip′ (SN.NodeStateB.inert-BD nb))
        (cong (λ z → (z ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb)) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeB-drv-io-no nb iomem))
           (⦀-wev-L _ _
              (noOffer→viewV _ (bundleG-io-no linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)
                 (absBundleG-io-ahl linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) iomem sBAB) linkAB≢linkBD iomem))
              run))
        refl

nodeB-io-BD-abs-fix : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeBEvR-abs-fix nb e a ((absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ⦀ Bd′) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
nodeB-io-BD-abs-fix nb {X} {e} {a} iomem sBBD
  with absBundleG-io-prod-wt linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) iomem sBBD
... | bgEBwt csc′ css′ bfc′ bfs′ ip′ eq run drop =
      nbEBafix (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) csc′ css′ bfc′ bfs′ (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) ip′)
        (cong (λ z → (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ⦀ z) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb)) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeB-drv-io-no nb iomem))
           (⦀-wev-R _ _
              (noOffer→viewV _ (bundleG-io-no linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
                 (absBundleG-io-ahl linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) iomem sBBD) (λ q → linkAB≢linkBD (sym q)) iomem))
              run))
        refl

nodeC-io-AC-abs-fix : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeCEvR-abs-fix nc e a ((Bd′ ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
nodeC-io-AC-abs-fix nc {X} {e} {a} iomem sBAC
  with absBundleG-io-prod-wt linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) iomem sBAC
... | bgEBwt csc′ css′ bfc′ bfs′ ip′ eq run drop =
      ncEBafix (SN.mkNodeC csc′ css′ bfc′ bfs′ (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) ip′ (SN.NodeStateC.inert-CD nc))
        (cong (λ z → (z ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc)) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeC-drv-io-no nc iomem))
           (⦀-wev-L _ _
              (noOffer→viewV _ (bundleG-io-no linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)
                 (absBundleG-io-ahl linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) iomem sBAC) linkAC≢linkCD iomem))
              run))
        refl

nodeC-io-CD-abs-fix : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeCEvR-abs-fix nc e a ((absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ⦀ Bd′) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
nodeC-io-CD-abs-fix nc {X} {e} {a} iomem sBCD
  with absBundleG-io-prod-wt linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) iomem sBCD
... | bgEBwt csc′ css′ bfc′ bfs′ ip′ eq run drop =
      ncEBafix (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) csc′ css′ bfc′ bfs′ (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) ip′)
        (cong (λ z → (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ⦀ z) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc)) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeC-drv-io-no nc iomem))
           (⦀-wev-R _ _
              (noOffer→viewV _ (bundleG-io-no linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
                 (absBundleG-io-ahl linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) iomem sBCD) (λ q → linkAC≢linkCD (sym q)) iomem))
              run))
        refl

nodeD-io-BD-abs-fix : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeDEvR-abs-fix nd e a ((Bd′ ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)))
nodeD-io-BD-abs-fix nd {X} {e} {a} iomem sBBD
  with absBundleG-io-prod-wt linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) iomem sBBD
... | bgEBwt csc′ css′ bfc′ bfs′ ip′ eq run drop =
      ndEBafix (SN.mkNodeD csc′ css′ bfc′ bfs′ (SN.NodeStateD.cons-BD nd) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) ip′ (SN.NodeStateD.inert-CD nd))
        (cong (λ z → (z ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeD-drv-io-no nd iomem))
           (⦀-wev-L _ _
              (noOffer→viewV _ (bundleG-io-no linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)
                 (absBundleG-io-ahl linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) iomem sBBD) linkBD≢linkCD iomem))
              run))
        refl refl

nodeD-io-CD-abs-fix : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeDEvR-abs-fix nd e a ((absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ⦀ Bd′) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)))
nodeD-io-CD-abs-fix nd {X} {e} {a} iomem sBCD
  with absBundleG-io-prod-wt linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) iomem sBCD
... | bgEBwt csc′ css′ bfc′ bfs′ ip′ eq run drop =
      ndEBafix (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd) csc′ css′ bfc′ bfs′ (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) ip′)
        (cong (λ z → (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ⦀ z) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeD-drv-io-no nd iomem))
           (⦀-wev-R _ _
              (noOffer→viewV _ (bundleG-io-no linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
                 (absBundleG-io-ahl linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) iomem sBCD) (λ q → linkBD≢linkCD (sym q)) iomem))
              run))
        refl refl

nodeA-ev-io-abs-fix : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodeA na ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeAEvR-abs-fix na e a M
nodeA-ev-io-abs-fix na {X} {e} {a} iomem step
  with PEA.Par-ev-elim apiES (λ _ _ → tt)
         (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
          ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
         (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na))
         step
... | PEA.evSync amem _ _ = ⊥-elim (io⇒¬api {X} {e} {a} iomem amem)
... | PEA.evR _ sD      = ⊥-elim (nodeA-drv-io-no na iomem (_ , sD))
... | PEA.evBoth _ _ sD = ⊥-elim (nodeA-drv-io-no na iomem (_ , sD))
... | PEA.evL _ sB
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
           (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
           sB
...   | PEA.evSync () _ _
...   | PEA.evBoth _ sBAB sBAC = ⊥-elim (linkAB≢linkAC
          (apiLink-inj (absBundleG-io-ahl linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) iomem sBAB)
                       (absBundleG-io-ahl linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) iomem sBAC)))
...   | PEA.evL _ sBAB = nodeA-io-AB-abs-fix na iomem sBAB
...   | PEA.evR _ sBAC = nodeA-io-AC-abs-fix na iomem sBAC

nodeB-ev-io-abs-fix : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodeB nb ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeBEvR-abs-fix nb e a M
nodeB-ev-io-abs-fix nb {X} {e} {a} iomem step
  with PEA.Par-ev-elim apiES (λ _ _ → tt)
         (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
          ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
         (SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
         step
... | PEA.evSync amem _ _ = ⊥-elim (io⇒¬api {X} {e} {a} iomem amem)
... | PEA.evR _ sD      = ⊥-elim (nodeB-drv-io-no nb iomem (_ , sD))
... | PEA.evBoth _ _ sD = ⊥-elim (nodeB-drv-io-no nb iomem (_ , sD))
... | PEA.evL _ sBb
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb))
           (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
           sBb
...   | PEA.evSync () _ _
...   | PEA.evBoth _ sBAB sBBD = ⊥-elim (linkAB≢linkBD
          (apiLink-inj (absBundleG-io-ahl linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) iomem sBAB)
                       (absBundleG-io-ahl linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) iomem sBBD)))
...   | PEA.evL _ sBAB = nodeB-io-AB-abs-fix nb iomem sBAB
...   | PEA.evR _ sBBD = nodeB-io-BD-abs-fix nb iomem sBBD

nodeC-ev-io-abs-fix : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodeC nc ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeCEvR-abs-fix nc e a M
nodeC-ev-io-abs-fix nc {X} {e} {a} iomem step
  with PEA.Par-ev-elim apiES (λ _ _ → tt)
         (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
          ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
         (SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
         step
... | PEA.evSync amem _ _ = ⊥-elim (io⇒¬api {X} {e} {a} iomem amem)
... | PEA.evR _ sD      = ⊥-elim (nodeC-drv-io-no nc iomem (_ , sD))
... | PEA.evBoth _ _ sD = ⊥-elim (nodeC-drv-io-no nc iomem (_ , sD))
... | PEA.evL _ sBc
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc))
           (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
           sBc
...   | PEA.evSync () _ _
...   | PEA.evBoth _ sBAC sBCD = ⊥-elim (linkAC≢linkCD
          (apiLink-inj (absBundleG-io-ahl linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) iomem sBAC)
                       (absBundleG-io-ahl linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) iomem sBCD)))
...   | PEA.evL _ sBAC = nodeC-io-AC-abs-fix nc iomem sBAC
...   | PEA.evR _ sBCD = nodeC-io-CD-abs-fix nc iomem sBCD

nodeD-ev-io-abs-fix : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodeD nd ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeDEvR-abs-fix nd e a M
nodeD-ev-io-abs-fix nd {X} {e} {a} iomem step
  with PEA.Par-ev-elim apiES (λ _ _ → tt)
         (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
          ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
         (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))
         step
... | PEA.evSync amem _ _ = ⊥-elim (io⇒¬api {X} {e} {a} iomem amem)
... | PEA.evR _ sD      = ⊥-elim (nodeD-drv-io-no nd iomem (_ , sD))
... | PEA.evBoth _ _ sD = ⊥-elim (nodeD-drv-io-no nd iomem (_ , sD))
... | PEA.evL _ sBd
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
           (absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
           sBd
...   | PEA.evSync () _ _
...   | PEA.evBoth _ sBBD sBCD = ⊥-elim (linkBD≢linkCD
          (apiLink-inj (absBundleG-io-ahl linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) iomem sBBD)
                       (absBundleG-io-ahl linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) iomem sBCD)))
...   | PEA.evL _ sBBD = nodeD-io-BD-abs-fix nd iomem sBBD
...   | PEA.evR _ sBCD = nodeD-io-CD-abs-fix nd iomem sBCD

------------------------------------------------------------------------
-- TOP: whole-nodes io-sync driver-fixity — the successor s′ with all six
-- group drivers equal to s's (feeds μG1-cong/μG2-cong in liftτ*-μ).
------------------------------------------------------------------------
top-nodes-io-abs-fix : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → SStep.absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ s′ ∈ SysState ] (med s ≡ med s′) × (M ≡ SStep.absNodesOf s′)
      × (SStep.nodesOf s ═[ ev (evl (evLabel X e a)) ]═► SStep.nodesOf s′)
      × (SN.NodeStateA.prod-AB (nA s) ≡ SN.NodeStateA.prod-AB (nA s′))
      × (SN.NodeStateA.prod-AC (nA s) ≡ SN.NodeStateA.prod-AC (nA s′))
      × (SN.NodeStateB.cp-B (nB s) ≡ SN.NodeStateB.cp-B (nB s′))
      × (SN.NodeStateC.cp-C (nC s) ≡ SN.NodeStateC.cp-C (nC s′))
      × (SN.NodeStateD.cons-BD (nD s) ≡ SN.NodeStateD.cons-BD (nD s′))
      × (SN.NodeStateD.cons-CD (nD s) ≡ SN.NodeStateD.cons-CD (nD s′))
top-nodes-io-abs-fix s iomem nodesStep
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (absNodeA (nA s)) (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s))) nodesStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sA sRest = ⊥-elim (absGroupA-io-no (nA s) (nB s) (nC s) (nD s) iomem sA (_ , sRest))
... | PEA.evL _ sA with nodeA-ev-io-abs-fix (nA s) iomem sA
...   | naEBafix na′ Meq weakRunA epAB epAC =
        mkSys (med s) na′ (nB s) (nC s) (nD s) , refl ,
        cong (λ z → z ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) Meq ,
        ⦀-wev-L (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (SStep.⦀-noOffer (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (nodeB-io-no-when-A (nB s) iomem fpA)
             (SStep.⦀-noOffer (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (nodeC-io-no-when-A (nC s) iomem fpA) (nodeD-io-no-when-A (nD s) iomem fpA))))
          weakRunA
        , epAB , epAC , refl , refl , refl , refl
  where fpA = absNodeA-io-fp (nA s) iomem sA
top-nodes-io-abs-fix s iomem nodesStep | PEA.evR _ sRest
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s)) sRest
... | PEA.evSync () _ _
... | PEA.evBoth _ sB sCD = ⊥-elim (absGroupB-io-no (nB s) (nC s) (nD s) iomem sB (_ , sCD))
... | PEA.evL _ sB with nodeB-ev-io-abs-fix (nB s) iomem sB
...   | nbEBafix nb′ Meq weakRunB ecpB =
        mkSys (med s) (nA s) nb′ (nC s) (nD s) , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (z ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) Meq ,
        ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (nodeA-io-no-when-B (nA s) iomem fpB))
          (⦀-wev-L (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (noOffer→viewV _ (SStep.⦀-noOffer (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (nodeC-io-no-when-B (nC s) iomem fpB) (nodeD-io-no-when-B (nD s) iomem fpB)))
             weakRunB)
        , refl , refl , ecpB , refl , refl , refl
  where fpB = absNodeB-io-fp (nB s) iomem sB
top-nodes-io-abs-fix s iomem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absNodeC (nC s)) (absNodeD (nD s)) sCD
... | PEA.evSync () _ _
... | PEA.evBoth _ sC sD = ⊥-elim (absNodeD-io-no-when-C (nD s) iomem (absNodeC-io-fp (nC s) iomem sC) (_ , sD))
... | PEA.evL _ sC with nodeC-ev-io-abs-fix (nC s) iomem sC
...   | ncEBafix nc′ Meq weakRunC ecpC =
        mkSys (med s) (nA s) (nB s) nc′ (nD s) , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (z ⦀ absNodeD (nD s)))) Meq ,
        ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (nodeA-io-no-when-C (nA s) iomem fpC))
          (⦀-wev-R (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (noOffer→viewV _ (nodeB-io-no-when-C (nB s) iomem fpC))
             (⦀-wev-L (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (noOffer→viewV _ (nodeD-io-no-when-C (nD s) iomem fpC))
                weakRunC))
        , refl , refl , refl , ecpC , refl , refl
  where fpC = absNodeC-io-fp (nC s) iomem sC
top-nodes-io-abs-fix s iomem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD | PEA.evR _ sD
    with nodeD-ev-io-abs-fix (nD s) iomem sD
... | ndEBafix nd′ Meq weakRunD edBD edCD =
        mkSys (med s) (nA s) (nB s) (nC s) nd′ , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ z))) Meq ,
        ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (nodeA-io-no-when-D (nA s) iomem fpD))
          (⦀-wev-R (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (noOffer→viewV _ (nodeB-io-no-when-D (nB s) iomem fpD))
             (⦀-wev-R (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (noOffer→viewV _ (nodeC-io-no-when-D (nC s) iomem fpD))
                weakRunD))
        , refl , refl , refl , refl , edBD , edCD
  where fpD = absNodeD-io-fp (nD s) iomem sD
