{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- R3 — the io-sync NODE cone WEIGHT-DROP re-mirror (WalkConv items (2)-(3)).
--
-- RE-MIRRORS the frozen SysIoLink6 abstract bundle/node io inversion cone,
-- threading the committed per-peer `decXc/Xs-ev-io-drop` leaf drops
-- (`WalkConvIoDrop`) into a whole-`nodesWt` strict decrease.  The frozen
-- `absBundleG-io-prod`/`nodeX-ev-io-abs`/`top-nodes-io-abs` expose the
-- successor OPAQUELY (`bgEB`), so the drop cannot be `with`-harvested — the
-- cone is re-mirrored VERBATIM (SIL6 imported, never edited) with the ONLY
-- changes: the leaf swap (`-ev-prod-abs` → `-ev-io-drop`, threading `iomem`),
-- and the extra `bundleWt`/`nodeWtX` drop field.  The 10-sibling refutations
-- are copied unchanged (`⊥-elim` fits any target).  The bundle drop uses
-- `WalkConvNodeWt.bundleWt-X-drop`; the node lift uses `nodeWtX-split`.
--
-- No postulate/hole/meta.
------------------------------------------------------------------------

open import Data.Nat using ( ℕ; _<_; _+_ )
open import Data.Nat.Properties using ( +-monoˡ-<; +-monoʳ-< )
open import Relation.Binary.PropositionalEquality using ( subst₂ )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvNodeDrop (blkA : Block₃) where

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

------------------------------------------------------------------------
-- unified abstract bundle io-inversion result WITH the `bundleWt` drop.
------------------------------------------------------------------------
data BundleGEvR-abs-wt (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) (Bd′ : NetProc) : Set₁ where
  bgEBwt : (csc′ : CScPos) (css′ : CSsPos) (bfc′ : BFcPos) (bfs′ : BFsPos) (ip′ : InertPos)
       → Bd′ ≡ absBundleG l cl sv csc′ css′ bfc′ bfs′ ip′
       → bundleG l cl sv csc css bfc bfs ip ═[ ev (evl (evLabel X e a)) ]═► bundleG l cl sv csc′ css′ bfc′ bfs′ ip′
       → bundleWt csc′ css′ bfc′ bfs′ ip′ < bundleWt csc css bfc bfs ip
       → BundleGEvR-abs-wt l cl sv csc css bfc bfs ip e a Bd′

finishCSc-ev-abs-wt : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {P′ : NetProc} → cl ≢ sv → ioES .mem (X , ιCS e₁) a
  → absCSc l cl csc ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► P′
  → BundleGEvR-abs-wt l cl sv csc css bfc bfs ip (ιCS e₁) a
      (absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (P′
        ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
        ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
        ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip))))))))))))
finishCSc-ev-abs-wt l cl sv csc css bfc bfs ip {e₁ = e₁} cl≢sv iomem sM with decCSc-ev-io-drop l cl csc iomem sM
... | csc′ , run , Meq , drop =
      bgEBwt csc′ css bfc bfs ip
        (cong (λ z → absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (z
               ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
               ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
               ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip)))))))))))) Meq)
        (⦀-wev-R (decKAc l cl (kac ip)) _
          (noOffer→viewV (decKAc l cl (kac ip)) (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιCS e₁)))
          (⦀-wev-R (decKAs l sv (kas ip)) _
            (noOffer→viewV (decKAs l sv (kas ip)) (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιCS e₁)))
            (⦀-wev-L (decCSc l cl csc) _
              (noOffer→viewV _
                (csTail-css-noOffer l cl sv css bfc bfs ip e₁
                  (λ q → cl≢sv (trans (sym (absCSc-ev-dir l cl csc sM)) q))))
              run)))
        (bundleWt-CSc-drop {csc′} {csc} {css} {bfc} {bfs} {ip} drop)

finishCSs-ev-abs-wt : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {P′ : NetProc} → cl ≢ sv → ioES .mem (X , ιCS e₁) a
  → absCSs l sv css ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► P′
  → BundleGEvR-abs-wt l cl sv csc css bfc bfs ip (ιCS e₁) a
      (absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (P′
        ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
        ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
        ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip))))))))))))
finishCSs-ev-abs-wt l cl sv csc css bfc bfs ip {e₁ = e₁} cl≢sv iomem sM with decCSs-ev-io-drop l sv css iomem sM
... | css′ , run , Meq , drop =
      bgEBwt csc css′ bfc bfs ip
        (cong (λ z → absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (z
               ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
               ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
               ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip)))))))))))) Meq)
        (⦀-wev-R (decKAc l cl (kac ip)) _
          (noOffer→viewV (decKAc l cl (kac ip)) (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιCS e₁)))
          (⦀-wev-R (decKAs l sv (kas ip)) _
            (noOffer→viewV (decKAs l sv (kas ip)) (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιCS e₁)))
            (⦀-wev-R (decCSc l cl csc) _
              (noOffer→viewV (decCSc l cl csc)
                (decCSc-dir-noOffer l cl csc e₁ (λ q → cl≢sv (trans (sym q) (absCSs-ev-dir l sv css sM)))))
              (⦀-wev-L (decCSs l sv css) _
                (noOffer→viewV _ (csTail-bfc-noOffer l cl sv bfc bfs ip e₁))
                run))))
        (bundleWt-CSs-drop {css′} {csc} {css} {bfc} {bfs} {ip} drop)

finishBFc-ev-abs-wt : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {P′ : NetProc} → cl ≢ sv → ioES .mem (X , ιBF e₁) a
  → absBFc l cl bfc ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► P′
  → BundleGEvR-abs-wt l cl sv csc css bfc bfs ip (ιBF e₁) a
      (absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (P′
        ⦀ (absBFs l sv bfs ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
        ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip))))))))))))
finishBFc-ev-abs-wt l cl sv csc css bfc bfs ip {e₁ = e₁} cl≢sv iomem sM with decBFc-ev-io-drop l cl bfc iomem sM
... | bfc′ , run , Meq , drop =
      bgEBwt csc css bfc′ bfs ip
        (cong (λ z → absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (z
               ⦀ (absBFs l sv bfs ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
               ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip)))))))))))) Meq)
        (⦀-wev-R (decKAc l cl (kac ip)) _
          (noOffer→viewV (decKAc l cl (kac ip)) (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιBF e₁)))
          (⦀-wev-R (decKAs l sv (kas ip)) _
            (noOffer→viewV (decKAs l sv (kas ip)) (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιBF e₁)))
            (⦀-wev-R (decCSc l cl csc) _
              (noOffer→viewV (decCSc l cl csc) (decCSc-noBFgen l cl csc e₁))
              (⦀-wev-R (decCSs l sv css) _
                (noOffer→viewV (decCSs l sv css) (decCSs-noBFgen l sv css e₁))
                (⦀-wev-L (decBFc l cl bfc) _
                  (noOffer→viewV _
                    (bfTail-bfs-noOffer l cl sv bfs ip e₁
                      (λ q → cl≢sv (trans (sym (absBFc-ev-dir l cl bfc sM)) q))))
                  run)))))
        (bundleWt-BFc-drop {bfc′} {csc} {css} {bfc} {bfs} {ip} drop)

finishBFs-ev-abs-wt : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {P′ : NetProc} → cl ≢ sv → ioES .mem (X , ιBF e₁) a
  → absBFs l sv bfs ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► P′
  → BundleGEvR-abs-wt l cl sv csc css bfc bfs ip (ιBF e₁) a
      (absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (P′
        ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
        ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip))))))))))))
finishBFs-ev-abs-wt l cl sv csc css bfc bfs ip {e₁ = e₁} cl≢sv iomem sM with decBFs-ev-io-drop l sv bfs iomem sM
... | bfs′ , run , Meq , drop =
      bgEBwt csc css bfc bfs′ ip
        (cong (λ z → absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (z
               ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
               ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip)))))))))))) Meq)
        (⦀-wev-R (decKAc l cl (kac ip)) _
          (noOffer→viewV (decKAc l cl (kac ip)) (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιBF e₁)))
          (⦀-wev-R (decKAs l sv (kas ip)) _
            (noOffer→viewV (decKAs l sv (kas ip)) (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιBF e₁)))
            (⦀-wev-R (decCSc l cl csc) _
              (noOffer→viewV (decCSc l cl csc) (decCSc-noBFgen l cl csc e₁))
              (⦀-wev-R (decCSs l sv css) _
                (noOffer→viewV (decCSs l sv css) (decCSs-noBFgen l sv css e₁))
                (⦀-wev-R (decBFc l cl bfc) _
                  (noOffer→viewV (decBFc l cl bfc)
                    (decBFc-dir-noOffer l cl bfc e₁ (λ q → cl≢sv (trans (sym q) (absBFs-ev-dir l sv bfs sM)))))
                  (⦀-wev-L (decBFs l sv bfs) _
                    (noOffer→viewV _ (bfTail-tsc-noOffer l cl sv ip e₁))
                    run))))))
        (bundleWt-BFs-drop {bfs′} {csc} {css} {bfc} {bfs} {ip} drop)

finishKAc-ev-abs-wt : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {P′ : NetProc} → cl ≢ sv → ioES .mem (X , ιKA e₁) a
  → absKAc l cl (kac ip) ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► P′
  → BundleGEvR-abs-wt l cl sv csc css bfc bfs ip (ιKA e₁) a
      (P′ ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
        ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
        ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip))))))))))))
finishKAc-ev-abs-wt l cl sv csc css bfc bfs ip {e₁ = e₁} cl≢sv iomem sM with decKAc-ev-io-drop l cl (kac ip) iomem sM
... | kac′ , run , Meq , drop =
      bgEBwt csc css bfc bfs (record ip { kac = kac′ })
        (cong (λ z → z ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
               ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
               ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip)))))))))))) Meq)
        (⦀-wev-L (decKAc l cl (kac ip)) _
          (noOffer→viewV _
            (kaTail-kas-noOffer l cl sv csc css bfc bfs ip e₁
              (λ q → cl≢sv (trans (sym (absKAc-ev-dir l cl (kac ip) sM)) q))))
          run)
        (bundleWt-KAc-drop {kac′} {csc} {css} {bfc} {bfs} {ip} drop)

finishKAs-ev-abs-wt : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {P′ : NetProc} → cl ≢ sv → ioES .mem (X , ιKA e₁) a
  → absKAs l sv (kas ip) ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► P′
  → BundleGEvR-abs-wt l cl sv csc css bfc bfs ip (ιKA e₁) a
      (absKAc l cl (kac ip) ⦀ (P′ ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
        ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
        ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip))))))))))))
finishKAs-ev-abs-wt l cl sv csc css bfc bfs ip {e₁ = e₁} cl≢sv iomem sM with decKAs-ev-io-drop l sv (kas ip) iomem sM
... | kas′ , run , Meq , drop =
      bgEBwt csc css bfc bfs (record ip { kas = kas′ })
        (cong (λ z → absKAc l cl (kac ip) ⦀ (z ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
               ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
               ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip)))))))))))) Meq)
        (⦀-wev-R (decKAc l cl (kac ip)) _
          (noOffer→viewV (decKAc l cl (kac ip))
            (decKAc-dir-noOffer l cl (kac ip) e₁ (λ q → cl≢sv (trans (sym q) (absKAs-ev-dir l sv (kas ip) sM)))))
          (⦀-wev-L (decKAs l sv (kas ip)) _
            (noOffer→viewV _ (kaTail-csc-noOffer l cl sv csc css bfc bfs ip e₁))
            run))
        (bundleWt-KAs-drop {kas′} {csc} {css} {bfc} {bfs} {ip} drop)

finishTSc-ev-abs-wt : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {P′ : NetProc} → cl ≢ sv → ioES .mem (X , ιTS e₁) a
  → absTSc l cl (tsc ip) ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► P′
  → BundleGEvR-abs-wt l cl sv csc css bfc bfs ip (ιTS e₁) a
      (absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
        ⦀ (P′ ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
        ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip))))))))))))
finishTSc-ev-abs-wt l cl sv csc css bfc bfs ip {e₁ = e₁} cl≢sv iomem sM with decTSc-ev-io-drop l cl (tsc ip) iomem sM
... | tsc′ , run , Meq , drop =
      bgEBwt csc css bfc bfs (record ip { tsc = tsc′ })
        (cong (λ z → absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
               ⦀ (z ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
               ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip)))))))))))) Meq)
        (⦀-wev-R (decKAc l cl (kac ip)) _ (noOffer→viewV (decKAc l cl (kac ip)) (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιTS e₁)))
          (⦀-wev-R (decKAs l sv (kas ip)) _ (noOffer→viewV (decKAs l sv (kas ip)) (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιTS e₁)))
            (⦀-wev-R (decCSc l cl csc) _ (noOffer→viewV (decCSc l cl csc) (decCSc-noTSgen l cl csc e₁))
              (⦀-wev-R (decCSs l sv css) _ (noOffer→viewV (decCSs l sv css) (decCSs-noTSgen l sv css e₁))
                (⦀-wev-R (decBFc l cl bfc) _ (noOffer→viewV (decBFc l cl bfc) (decBFc-noTSgen l cl bfc e₁))
                  (⦀-wev-R (decBFs l sv bfs) _ (noOffer→viewV (decBFs l sv bfs) (decBFs-noTSgen l sv bfs e₁))
                    (⦀-wev-L (decTSc l cl (tsc ip)) _
                      (noOffer→viewV _ (tsTail-tss-noOffer l cl sv ip e₁ (λ q → cl≢sv (trans (sym (absTSc-ev-dir l cl (tsc ip) sM)) q))))
                      run)))))))

-- fold a TS-server abstract fire into the bundle result (peer #7)
        (bundleWt-TSc-drop {tsc′} {csc} {css} {bfc} {bfs} {ip} drop)

finishTSs-ev-abs-wt : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {P′ : NetProc} → cl ≢ sv → ioES .mem (X , ιTS e₁) a
  → absTSs l sv (tss ip) ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► P′
  → BundleGEvR-abs-wt l cl sv csc css bfc bfs ip (ιTS e₁) a
      (absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
        ⦀ (absTSc l cl (tsc ip) ⦀ (P′ ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
        ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip))))))))))))
finishTSs-ev-abs-wt l cl sv csc css bfc bfs ip {e₁ = e₁} cl≢sv iomem sM with decTSs-ev-io-drop l sv (tss ip) iomem sM
... | tss′ , run , Meq , drop =
      bgEBwt csc css bfc bfs (record ip { tss = tss′ })
        (cong (λ z → absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
               ⦀ (absTSc l cl (tsc ip) ⦀ (z ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
               ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip)))))))))))) Meq)
        (⦀-wev-R (decKAc l cl (kac ip)) _ (noOffer→viewV (decKAc l cl (kac ip)) (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιTS e₁)))
          (⦀-wev-R (decKAs l sv (kas ip)) _ (noOffer→viewV (decKAs l sv (kas ip)) (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιTS e₁)))
            (⦀-wev-R (decCSc l cl csc) _ (noOffer→viewV (decCSc l cl csc) (decCSc-noTSgen l cl csc e₁))
              (⦀-wev-R (decCSs l sv css) _ (noOffer→viewV (decCSs l sv css) (decCSs-noTSgen l sv css e₁))
                (⦀-wev-R (decBFc l cl bfc) _ (noOffer→viewV (decBFc l cl bfc) (decBFc-noTSgen l cl bfc e₁))
                  (⦀-wev-R (decBFs l sv bfs) _ (noOffer→viewV (decBFs l sv bfs) (decBFs-noTSgen l sv bfs e₁))
                    (⦀-wev-R (decTSc l cl (tsc ip)) _
                      (noOffer→viewV (decTSc l cl (tsc ip)) (decTSc-dir-noOffer l cl (tsc ip) e₁ (λ q → cl≢sv (trans (sym q) (absTSs-ev-dir l sv (tss ip) sM)))))
                      (⦀-wev-L (decTSs l sv (tss ip)) _
                        (noOffer→viewV _ (tsTail-lnc-noOffer l cl sv ip e₁))
                        run))))))))

-- 12-peer abstract bundle ev-inversion (TS)
        (bundleWt-TSs-drop {tss′} {csc} {css} {bfc} {bfs} {ip} drop)

finishLNc-ev-abs-wt : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : LN.LNEv X} {a : X} {P′ : NetProc} → cl ≢ sv → ioES .mem (X , ιLN e₁) a
  → absLNc l cl (lnc ip) ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► P′
  → BundleGEvR-abs-wt l cl sv csc css bfc bfs ip (ιLN e₁) a
      (absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
        ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (P′ ⦀ (absLNs l sv (lns ip)
        ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip))))))))))))
finishLNc-ev-abs-wt l cl sv csc css bfc bfs ip {e₁ = e₁} cl≢sv iomem sM with decLNc-ev-io-drop l cl (lnc ip) iomem sM
... | lnc′ , run , Meq , drop =
      bgEBwt csc css bfc bfs (record ip { lnc = lnc′ })
        (cong (λ z → absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
               ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (z ⦀ (absLNs l sv (lns ip)
               ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip)))))))))))) Meq)
        (⦀-wev-R (decKAc l cl (kac ip)) _ (noOffer→viewV (decKAc l cl (kac ip)) (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιLN e₁)))
          (⦀-wev-R (decKAs l sv (kas ip)) _ (noOffer→viewV (decKAs l sv (kas ip)) (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιLN e₁)))
            (⦀-wev-R (decCSc l cl csc) _ (noOffer→viewV (decCSc l cl csc) (decCSc-noLNgen l cl csc e₁))
              (⦀-wev-R (decCSs l sv css) _ (noOffer→viewV (decCSs l sv css) (decCSs-noLNgen l sv css e₁))
                (⦀-wev-R (decBFc l cl bfc) _ (noOffer→viewV (decBFc l cl bfc) (decBFc-noLNgen l cl bfc e₁))
                  (⦀-wev-R (decBFs l sv bfs) _ (noOffer→viewV (decBFs l sv bfs) (decBFs-noLNgen l sv bfs e₁))
                    (⦀-wev-R (decTSc l cl (tsc ip)) _ (noOffer→viewV (decTSc l cl (tsc ip)) (decTSc-noOffer l cl (tsc ip) (ιTS⁻¹∘ιLN e₁)))
                      (⦀-wev-R (decTSs l sv (tss ip)) _ (noOffer→viewV (decTSs l sv (tss ip)) (decTSs-noOffer l sv (tss ip) (ιTS⁻¹∘ιLN e₁)))
                        (⦀-wev-L (decLNc l cl (lnc ip)) _
                          (noOffer→viewV _ (lnTail-lns-noOffer l cl sv ip e₁ (λ q → cl≢sv (trans (sym (absLNc-ev-dir l cl (lnc ip) sM)) q))))
                          run)))))))))

-- fold a LN-server abstract fire into the bundle result (peer #9)
        (bundleWt-LNc-drop {lnc′} {csc} {css} {bfc} {bfs} {ip} drop)

finishLNs-ev-abs-wt : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : LN.LNEv X} {a : X} {P′ : NetProc} → cl ≢ sv → ioES .mem (X , ιLN e₁) a
  → absLNs l sv (lns ip) ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► P′
  → BundleGEvR-abs-wt l cl sv csc css bfc bfs ip (ιLN e₁) a
      (absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
        ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (P′
        ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip))))))))))))
finishLNs-ev-abs-wt l cl sv csc css bfc bfs ip {e₁ = e₁} cl≢sv iomem sM with decLNs-ev-io-drop l sv (lns ip) iomem sM
... | lns′ , run , Meq , drop =
      bgEBwt csc css bfc bfs (record ip { lns = lns′ })
        (cong (λ z → absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
               ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (z
               ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip)))))))))))) Meq)
        (⦀-wev-R (decKAc l cl (kac ip)) _ (noOffer→viewV (decKAc l cl (kac ip)) (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιLN e₁)))
          (⦀-wev-R (decKAs l sv (kas ip)) _ (noOffer→viewV (decKAs l sv (kas ip)) (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιLN e₁)))
            (⦀-wev-R (decCSc l cl csc) _ (noOffer→viewV (decCSc l cl csc) (decCSc-noLNgen l cl csc e₁))
              (⦀-wev-R (decCSs l sv css) _ (noOffer→viewV (decCSs l sv css) (decCSs-noLNgen l sv css e₁))
                (⦀-wev-R (decBFc l cl bfc) _ (noOffer→viewV (decBFc l cl bfc) (decBFc-noLNgen l cl bfc e₁))
                  (⦀-wev-R (decBFs l sv bfs) _ (noOffer→viewV (decBFs l sv bfs) (decBFs-noLNgen l sv bfs e₁))
                    (⦀-wev-R (decTSc l cl (tsc ip)) _ (noOffer→viewV (decTSc l cl (tsc ip)) (decTSc-noOffer l cl (tsc ip) (ιTS⁻¹∘ιLN e₁)))
                      (⦀-wev-R (decTSs l sv (tss ip)) _ (noOffer→viewV (decTSs l sv (tss ip)) (decTSs-noOffer l sv (tss ip) (ιTS⁻¹∘ιLN e₁)))
                        (⦀-wev-R (decLNc l cl (lnc ip)) _ (noOffer→viewV (decLNc l cl (lnc ip)) (decLNc-dir-noOffer l cl (lnc ip) e₁ (λ q → cl≢sv (trans (sym q) (absLNs-ev-dir l sv (lns ip) sM)))))
                          (⦀-wev-L (decLNs l sv (lns ip)) _
                            (noOffer→viewV _ (lnTail-lfc-noOffer l cl sv ip e₁))
                            run))))))))))

-- 12-peer abstract bundle ev-inversion (LN)
        (bundleWt-LNs-drop {lns′} {csc} {css} {bfc} {bfs} {ip} drop)

finishLFc-ev-abs-wt : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : LF.LFEv X} {a : X} {P′ : NetProc} → cl ≢ sv → ioES .mem (X , ιLF e₁) a
  → absLFc l cl (lfc ip) ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► P′
  → BundleGEvR-abs-wt l cl sv csc css bfc bfs ip (ιLF e₁) a
      (absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
        ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
        ⦀ (P′ ⦀ absLFs l sv (lfs ip))))))))))))
finishLFc-ev-abs-wt l cl sv csc css bfc bfs ip {e₁ = e₁} cl≢sv iomem sM with decLFc-ev-io-drop l cl (lfc ip) iomem sM
... | lfc′ , run , Meq , drop =
      bgEBwt csc css bfc bfs (record ip { lfc = lfc′ })
        (cong (λ z → absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
               ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
               ⦀ (z ⦀ absLFs l sv (lfs ip)))))))))))) Meq)
        (⦀-wev-R (decKAc l cl (kac ip)) _ (noOffer→viewV (decKAc l cl (kac ip)) (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιLF e₁)))
          (⦀-wev-R (decKAs l sv (kas ip)) _ (noOffer→viewV (decKAs l sv (kas ip)) (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιLF e₁)))
            (⦀-wev-R (decCSc l cl csc) _ (noOffer→viewV (decCSc l cl csc) (decCSc-noLFgen l cl csc e₁))
              (⦀-wev-R (decCSs l sv css) _ (noOffer→viewV (decCSs l sv css) (decCSs-noLFgen l sv css e₁))
                (⦀-wev-R (decBFc l cl bfc) _ (noOffer→viewV (decBFc l cl bfc) (decBFc-noLFgen l cl bfc e₁))
                  (⦀-wev-R (decBFs l sv bfs) _ (noOffer→viewV (decBFs l sv bfs) (decBFs-noLFgen l sv bfs e₁))
                    (⦀-wev-R (decTSc l cl (tsc ip)) _ (noOffer→viewV (decTSc l cl (tsc ip)) (decTSc-noOffer l cl (tsc ip) (ιTS⁻¹∘ιLF e₁)))
                      (⦀-wev-R (decTSs l sv (tss ip)) _ (noOffer→viewV (decTSs l sv (tss ip)) (decTSs-noOffer l sv (tss ip) (ιTS⁻¹∘ιLF e₁)))
                        (⦀-wev-R (decLNc l cl (lnc ip)) _ (noOffer→viewV (decLNc l cl (lnc ip)) (decLNc-noOffer l cl (lnc ip) (ιLN⁻¹∘ιLF e₁)))
                          (⦀-wev-R (decLNs l sv (lns ip)) _ (noOffer→viewV (decLNs l sv (lns ip)) (decLNs-noOffer l sv (lns ip) (ιLN⁻¹∘ιLF e₁)))
                            (⦀-wev-L (decLFc l cl (lfc ip)) _
                              (noOffer→viewV _ (decLFs-dir-noOffer l sv (lfs ip) e₁ (λ q → cl≢sv (trans (sym (absLFc-ev-dir l cl (lfc ip) sM)) q))))
                              run)))))))))))

-- fold a LF-server abstract fire into the bundle result (peer #11, last)
        (bundleWt-LFc-drop {lfc′} {csc} {css} {bfc} {bfs} {ip} drop)

finishLFs-ev-abs-wt : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : LF.LFEv X} {a : X} {P′ : NetProc} → cl ≢ sv → ioES .mem (X , ιLF e₁) a
  → absLFs l sv (lfs ip) ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► P′
  → BundleGEvR-abs-wt l cl sv csc css bfc bfs ip (ιLF e₁) a
      (absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
        ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
        ⦀ (absLFc l cl (lfc ip) ⦀ P′)))))))))))
finishLFs-ev-abs-wt l cl sv csc css bfc bfs ip {e₁ = e₁} cl≢sv iomem sM with decLFs-ev-io-drop l sv (lfs ip) iomem sM
... | lfs′ , run , Meq , drop =
      bgEBwt csc css bfc bfs (record ip { lfs = lfs′ })
        (cong (λ z → absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
               ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
               ⦀ (absLFc l cl (lfc ip) ⦀ z))))))))))) Meq)
        (⦀-wev-R (decKAc l cl (kac ip)) _ (noOffer→viewV (decKAc l cl (kac ip)) (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιLF e₁)))
          (⦀-wev-R (decKAs l sv (kas ip)) _ (noOffer→viewV (decKAs l sv (kas ip)) (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιLF e₁)))
            (⦀-wev-R (decCSc l cl csc) _ (noOffer→viewV (decCSc l cl csc) (decCSc-noLFgen l cl csc e₁))
              (⦀-wev-R (decCSs l sv css) _ (noOffer→viewV (decCSs l sv css) (decCSs-noLFgen l sv css e₁))
                (⦀-wev-R (decBFc l cl bfc) _ (noOffer→viewV (decBFc l cl bfc) (decBFc-noLFgen l cl bfc e₁))
                  (⦀-wev-R (decBFs l sv bfs) _ (noOffer→viewV (decBFs l sv bfs) (decBFs-noLFgen l sv bfs e₁))
                    (⦀-wev-R (decTSc l cl (tsc ip)) _ (noOffer→viewV (decTSc l cl (tsc ip)) (decTSc-noOffer l cl (tsc ip) (ιTS⁻¹∘ιLF e₁)))
                      (⦀-wev-R (decTSs l sv (tss ip)) _ (noOffer→viewV (decTSs l sv (tss ip)) (decTSs-noOffer l sv (tss ip) (ιTS⁻¹∘ιLF e₁)))
                        (⦀-wev-R (decLNc l cl (lnc ip)) _ (noOffer→viewV (decLNc l cl (lnc ip)) (decLNc-noOffer l cl (lnc ip) (ιLN⁻¹∘ιLF e₁)))
                          (⦀-wev-R (decLNs l sv (lns ip)) _ (noOffer→viewV (decLNs l sv (lns ip)) (decLNs-noOffer l sv (lns ip) (ιLN⁻¹∘ιLF e₁)))
                            (⦀-wev-R (decLFc l cl (lfc ip)) _ (noOffer→viewV (decLFc l cl (lfc ip)) (decLFc-dir-noOffer l cl (lfc ip) e₁ (λ q → cl≢sv (trans (sym q) (absLFs-ev-dir l sv (lfs ip) sM)))))
                              run)))))))))))

-- 12-peer abstract bundle ev-inversion (LF)
        (bundleWt-LFs-drop {lfs′} {csc} {css} {bfc} {bfs} {ip} drop)

absBundleCS-ev-prod-wt : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , ιCS e₁) a
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► Bd′
  → BundleGEvR-abs-wt l cl sv csc css bfc bfs ip (ιCS e₁) a Bd′
absBundleCS-ev-prod-wt l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} iomem step
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAc l cl (kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evL _ sM     = ⊥-elim (absKAc-noCS l cl (kac ip) e₁ (_ , sM))
... | PEA.evBoth _ sM _ = ⊥-elim (absKAc-noCS l cl (kac ip) e₁ (_ , sM))
... | PEA.evR _ q1
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAs l sv (kas ip)) _ q1
...   | PEA.evSync () _ _
...   | PEA.evL _ sM     = ⊥-elim (absKAs-noCS l sv (kas ip) e₁ (_ , sM))
...   | PEA.evBoth _ sM _ = ⊥-elim (absKAs-noCS l sv (kas ip) e₁ (_ , sM))
...   | PEA.evR _ q2
      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSc l cl csc) _ q2
...     | PEA.evSync () _ _
...     | PEA.evL _ sM = finishCSc-ev-abs-wt l cl sv csc css bfc bfs ip cl≢sv iomem sM
...     | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absCSs l sv css) _ (absCSs-dir-noBoth l sv css e₁ (λ q → cl≢sv (trans (sym (absCSc-ev-dir l cl csc sM)) q))) (SStep.⦀-noOffer (absBFc l cl bfc) _ (absBFc-noCS l cl bfc e₁) (SStep.⦀-noOffer (absBFs l sv bfs) _ (absBFs-noCS l sv bfs e₁) (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noCS l cl (tsc ip) e₁) (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noCS l sv (tss ip) e₁) (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noCS l cl (lnc ip) e₁) (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noCS l sv (lns ip) e₁) (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noCS l cl (lfc ip) e₁) (absLFs-noCS l sv (lfs ip) e₁)))))))) (_ , sTail))
...     | PEA.evR _ q3
        with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSs l sv css) _ q3
...       | PEA.evSync () _ _
...       | PEA.evL _ sM = finishCSs-ev-abs-wt l cl sv csc css bfc bfs ip cl≢sv iomem sM
...       | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absBFc l cl bfc) _ (absBFc-noCS l cl bfc e₁) (SStep.⦀-noOffer (absBFs l sv bfs) _ (absBFs-noCS l sv bfs e₁) (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noCS l cl (tsc ip) e₁) (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noCS l sv (tss ip) e₁) (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noCS l cl (lnc ip) e₁) (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noCS l sv (lns ip) e₁) (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noCS l cl (lfc ip) e₁) (absLFs-noCS l sv (lfs ip) e₁))))))) (_ , sTail))
...       | PEA.evR _ q4
          with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFc l cl bfc) _ q4
...         | PEA.evSync () _ _
...         | PEA.evL _ sM     = ⊥-elim (absBFc-noCS l cl bfc e₁ (_ , sM))
...         | PEA.evBoth _ sM _ = ⊥-elim (absBFc-noCS l cl bfc e₁ (_ , sM))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM     = ⊥-elim (absBFs-noCS l sv bfs e₁ (_ , sM))
...           | PEA.evBoth _ sM _ = ⊥-elim (absBFs-noCS l sv bfs e₁ (_ , sM))
...           | PEA.evR _ q6
              with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSc l cl (tsc ip)) _ q6
...             | PEA.evSync () _ _
...             | PEA.evL _ sM     = ⊥-elim (absTSc-noCS l cl (tsc ip) e₁ (_ , sM))
...             | PEA.evBoth _ sM _ = ⊥-elim (absTSc-noCS l cl (tsc ip) e₁ (_ , sM))
...             | PEA.evR _ q7
                with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSs l sv (tss ip)) _ q7
...               | PEA.evSync () _ _
...               | PEA.evL _ sM     = ⊥-elim (absTSs-noCS l sv (tss ip) e₁ (_ , sM))
...               | PEA.evBoth _ sM _ = ⊥-elim (absTSs-noCS l sv (tss ip) e₁ (_ , sM))
...               | PEA.evR _ q8
                  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNc l cl (lnc ip)) _ q8
...                 | PEA.evSync () _ _
...                 | PEA.evL _ sM     = ⊥-elim (absLNc-noCS l cl (lnc ip) e₁ (_ , sM))
...                 | PEA.evBoth _ sM _ = ⊥-elim (absLNc-noCS l cl (lnc ip) e₁ (_ , sM))
...                 | PEA.evR _ q9
                    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNs l sv (lns ip)) _ q9
...                   | PEA.evSync () _ _
...                   | PEA.evL _ sM     = ⊥-elim (absLNs-noCS l sv (lns ip) e₁ (_ , sM))
...                   | PEA.evBoth _ sM _ = ⊥-elim (absLNs-noCS l sv (lns ip) e₁ (_ , sM))
...                   | PEA.evR _ q10
                      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) q10
...                     | PEA.evSync () _ _
...                     | PEA.evL _ sM     = ⊥-elim (absLFc-noCS l cl (lfc ip) e₁ (_ , sM))
...                     | PEA.evBoth _ sM _ = ⊥-elim (absLFc-noCS l cl (lfc ip) e₁ (_ , sM))
...                     | PEA.evR _ qs     = ⊥-elim (absLFs-noCS l sv (lfs ip) e₁ (_ , qs))

absBundleBF-ev-prod-wt : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , ιBF e₁) a
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► Bd′
  → BundleGEvR-abs-wt l cl sv csc css bfc bfs ip (ιBF e₁) a Bd′
absBundleBF-ev-prod-wt l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} iomem step
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAc l cl (kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evL _ sM     = ⊥-elim (absKAc-noBF l cl (kac ip) e₁ (_ , sM))
... | PEA.evBoth _ sM _ = ⊥-elim (absKAc-noBF l cl (kac ip) e₁ (_ , sM))
... | PEA.evR _ q1
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAs l sv (kas ip)) _ q1
...   | PEA.evSync () _ _
...   | PEA.evL _ sM     = ⊥-elim (absKAs-noBF l sv (kas ip) e₁ (_ , sM))
...   | PEA.evBoth _ sM _ = ⊥-elim (absKAs-noBF l sv (kas ip) e₁ (_ , sM))
...   | PEA.evR _ q2
      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSc l cl csc) _ q2
...     | PEA.evSync () _ _
...     | PEA.evL _ sM     = ⊥-elim (absCSc-noBF l cl csc e₁ (_ , sM))
...     | PEA.evBoth _ sM _ = ⊥-elim (absCSc-noBF l cl csc e₁ (_ , sM))
...     | PEA.evR _ q3
        with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSs l sv css) _ q3
...       | PEA.evSync () _ _
...       | PEA.evL _ sM     = ⊥-elim (absCSs-noBF l sv css e₁ (_ , sM))
...       | PEA.evBoth _ sM _ = ⊥-elim (absCSs-noBF l sv css e₁ (_ , sM))
...       | PEA.evR _ q4
          with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFc l cl bfc) _ q4
...         | PEA.evSync () _ _
...         | PEA.evL _ sM = finishBFc-ev-abs-wt l cl sv csc css bfc bfs ip cl≢sv iomem sM
...         | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absBFs l sv bfs) _ (absBFs-dir-noBoth l sv bfs e₁ (λ q → cl≢sv (trans (sym (absBFc-ev-dir l cl bfc sM)) q))) (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noBF l cl (tsc ip) e₁) (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noBF l sv (tss ip) e₁) (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noBF l cl (lnc ip) e₁) (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noBF l sv (lns ip) e₁) (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noBF l cl (lfc ip) e₁) (absLFs-noBF l sv (lfs ip) e₁)))))) (_ , sTail))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM = finishBFs-ev-abs-wt l cl sv csc css bfc bfs ip cl≢sv iomem sM
...           | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noBF l cl (tsc ip) e₁) (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noBF l sv (tss ip) e₁) (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noBF l cl (lnc ip) e₁) (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noBF l sv (lns ip) e₁) (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noBF l cl (lfc ip) e₁) (absLFs-noBF l sv (lfs ip) e₁))))) (_ , sTail))
...           | PEA.evR _ q6
              with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSc l cl (tsc ip)) _ q6
...             | PEA.evSync () _ _
...             | PEA.evL _ sM     = ⊥-elim (absTSc-noBF l cl (tsc ip) e₁ (_ , sM))
...             | PEA.evBoth _ sM _ = ⊥-elim (absTSc-noBF l cl (tsc ip) e₁ (_ , sM))
...             | PEA.evR _ q7
                with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSs l sv (tss ip)) _ q7
...               | PEA.evSync () _ _
...               | PEA.evL _ sM     = ⊥-elim (absTSs-noBF l sv (tss ip) e₁ (_ , sM))
...               | PEA.evBoth _ sM _ = ⊥-elim (absTSs-noBF l sv (tss ip) e₁ (_ , sM))
...               | PEA.evR _ q8
                  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNc l cl (lnc ip)) _ q8
...                 | PEA.evSync () _ _
...                 | PEA.evL _ sM     = ⊥-elim (absLNc-noBF l cl (lnc ip) e₁ (_ , sM))
...                 | PEA.evBoth _ sM _ = ⊥-elim (absLNc-noBF l cl (lnc ip) e₁ (_ , sM))
...                 | PEA.evR _ q9
                    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNs l sv (lns ip)) _ q9
...                   | PEA.evSync () _ _
...                   | PEA.evL _ sM     = ⊥-elim (absLNs-noBF l sv (lns ip) e₁ (_ , sM))
...                   | PEA.evBoth _ sM _ = ⊥-elim (absLNs-noBF l sv (lns ip) e₁ (_ , sM))
...                   | PEA.evR _ q10
                      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) q10
...                     | PEA.evSync () _ _
...                     | PEA.evL _ sM     = ⊥-elim (absLFc-noBF l cl (lfc ip) e₁ (_ , sM))
...                     | PEA.evBoth _ sM _ = ⊥-elim (absLFc-noBF l cl (lfc ip) e₁ (_ , sM))
...                     | PEA.evR _ qs     = ⊥-elim (absLFs-noBF l sv (lfs ip) e₁ (_ , qs))

------------------------------------------------------------------------

absBundleKA-ev-prod-wt : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , ιKA e₁) a
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► Bd′
  → BundleGEvR-abs-wt l cl sv csc css bfc bfs ip (ιKA e₁) a Bd′
absBundleKA-ev-prod-wt l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} iomem step
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAc l cl (kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evL _ sM = finishKAc-ev-abs-wt l cl sv csc css bfc bfs ip cl≢sv iomem sM
... | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absKAs l sv (kas ip)) _ (absKAs-dir-noBoth l sv (kas ip) e₁ (λ q → cl≢sv (trans (sym (absKAc-ev-dir l cl (kac ip) sM)) q))) (SStep.⦀-noOffer (absCSc l cl csc) _ (absCSc-noKA l cl csc e₁) (SStep.⦀-noOffer (absCSs l sv css) _ (absCSs-noKA l sv css e₁) (SStep.⦀-noOffer (absBFc l cl bfc) _ (absBFc-noKA l cl bfc e₁) (SStep.⦀-noOffer (absBFs l sv bfs) _ (absBFs-noKA l sv bfs e₁) (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noKA l cl (tsc ip) e₁) (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noKA l sv (tss ip) e₁) (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noKA l cl (lnc ip) e₁) (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noKA l sv (lns ip) e₁) (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noKA l cl (lfc ip) e₁) (absLFs-noKA l sv (lfs ip) e₁))))))))) ) (_ , sTail))
... | PEA.evR _ q1
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAs l sv (kas ip)) _ q1
...   | PEA.evSync () _ _
...   | PEA.evL _ sM = finishKAs-ev-abs-wt l cl sv csc css bfc bfs ip cl≢sv iomem sM
...   | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absCSc l cl csc) _ (absCSc-noKA l cl csc e₁) (SStep.⦀-noOffer (absCSs l sv css) _ (absCSs-noKA l sv css e₁) (SStep.⦀-noOffer (absBFc l cl bfc) _ (absBFc-noKA l cl bfc e₁) (SStep.⦀-noOffer (absBFs l sv bfs) _ (absBFs-noKA l sv bfs e₁) (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noKA l cl (tsc ip) e₁) (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noKA l sv (tss ip) e₁) (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noKA l cl (lnc ip) e₁) (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noKA l sv (lns ip) e₁) (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noKA l cl (lfc ip) e₁) (absLFs-noKA l sv (lfs ip) e₁)))))))) ) (_ , sTail))
...   | PEA.evR _ q2
      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSc l cl csc) _ q2
...     | PEA.evSync () _ _
...     | PEA.evL _ sM     = ⊥-elim (absCSc-noKA l cl csc e₁ (_ , sM))
...     | PEA.evBoth _ sM _ = ⊥-elim (absCSc-noKA l cl csc e₁ (_ , sM))
...     | PEA.evR _ q3
        with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSs l sv css) _ q3
...       | PEA.evSync () _ _
...       | PEA.evL _ sM     = ⊥-elim (absCSs-noKA l sv css e₁ (_ , sM))
...       | PEA.evBoth _ sM _ = ⊥-elim (absCSs-noKA l sv css e₁ (_ , sM))
...       | PEA.evR _ q4
          with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFc l cl bfc) _ q4
...         | PEA.evSync () _ _
...         | PEA.evL _ sM     = ⊥-elim (absBFc-noKA l cl bfc e₁ (_ , sM))
...         | PEA.evBoth _ sM _ = ⊥-elim (absBFc-noKA l cl bfc e₁ (_ , sM))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM     = ⊥-elim (absBFs-noKA l sv bfs e₁ (_ , sM))
...           | PEA.evBoth _ sM _ = ⊥-elim (absBFs-noKA l sv bfs e₁ (_ , sM))
...           | PEA.evR _ q6
              with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSc l cl (tsc ip)) _ q6
...             | PEA.evSync () _ _
...             | PEA.evL _ sM     = ⊥-elim (absTSc-noKA l cl (tsc ip) e₁ (_ , sM))
...             | PEA.evBoth _ sM _ = ⊥-elim (absTSc-noKA l cl (tsc ip) e₁ (_ , sM))
...             | PEA.evR _ q7
                with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSs l sv (tss ip)) _ q7
...               | PEA.evSync () _ _
...               | PEA.evL _ sM     = ⊥-elim (absTSs-noKA l sv (tss ip) e₁ (_ , sM))
...               | PEA.evBoth _ sM _ = ⊥-elim (absTSs-noKA l sv (tss ip) e₁ (_ , sM))
...               | PEA.evR _ q8
                  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNc l cl (lnc ip)) _ q8
...                 | PEA.evSync () _ _
...                 | PEA.evL _ sM     = ⊥-elim (absLNc-noKA l cl (lnc ip) e₁ (_ , sM))
...                 | PEA.evBoth _ sM _ = ⊥-elim (absLNc-noKA l cl (lnc ip) e₁ (_ , sM))
...                 | PEA.evR _ q9
                    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNs l sv (lns ip)) _ q9
...                   | PEA.evSync () _ _
...                   | PEA.evL _ sM     = ⊥-elim (absLNs-noKA l sv (lns ip) e₁ (_ , sM))
...                   | PEA.evBoth _ sM _ = ⊥-elim (absLNs-noKA l sv (lns ip) e₁ (_ , sM))
...                   | PEA.evR _ q10
                      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) q10
...                     | PEA.evSync () _ _
...                     | PEA.evL _ sM     = ⊥-elim (absLFc-noKA l cl (lfc ip) e₁ (_ , sM))
...                     | PEA.evBoth _ sM _ = ⊥-elim (absLFc-noKA l cl (lfc ip) e₁ (_ , sM))
...                     | PEA.evR _ qs     = ⊥-elim (absLFs-noKA l sv (lfs ip) e₁ (_ , qs))

------------------------------------------------------------------------

absBundleTS-ev-prod-wt : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , ιTS e₁) a
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► Bd′
  → BundleGEvR-abs-wt l cl sv csc css bfc bfs ip (ιTS e₁) a Bd′
absBundleTS-ev-prod-wt l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} iomem step
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAc l cl (kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evL _ sM = ⊥-elim (absKAc-noTS l cl (kac ip) e₁ (_ , sM))
... | PEA.evBoth _ sM _ = ⊥-elim (absKAc-noTS l cl (kac ip) e₁ (_ , sM))
... | PEA.evR _ q1
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAs l sv (kas ip)) _ q1
...   | PEA.evSync () _ _
...   | PEA.evL _ sM = ⊥-elim (absKAs-noTS l sv (kas ip) e₁ (_ , sM))
...   | PEA.evBoth _ sM _ = ⊥-elim (absKAs-noTS l sv (kas ip) e₁ (_ , sM))
...   | PEA.evR _ q2
      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSc l cl csc) _ q2
...     | PEA.evSync () _ _
...     | PEA.evL _ sM = ⊥-elim (absCSc-noTS l cl csc e₁ (_ , sM))
...     | PEA.evBoth _ sM _ = ⊥-elim (absCSc-noTS l cl csc e₁ (_ , sM))
...     | PEA.evR _ q3
        with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSs l sv css) _ q3
...       | PEA.evSync () _ _
...       | PEA.evL _ sM = ⊥-elim (absCSs-noTS l sv css e₁ (_ , sM))
...       | PEA.evBoth _ sM _ = ⊥-elim (absCSs-noTS l sv css e₁ (_ , sM))
...       | PEA.evR _ q4
          with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFc l cl bfc) _ q4
...         | PEA.evSync () _ _
...         | PEA.evL _ sM = ⊥-elim (absBFc-noTS l cl bfc e₁ (_ , sM))
...         | PEA.evBoth _ sM _ = ⊥-elim (absBFc-noTS l cl bfc e₁ (_ , sM))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM = ⊥-elim (absBFs-noTS l sv bfs e₁ (_ , sM))
...           | PEA.evBoth _ sM _ = ⊥-elim (absBFs-noTS l sv bfs e₁ (_ , sM))
...           | PEA.evR _ q6
              with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSc l cl (tsc ip)) _ q6
...             | PEA.evSync () _ _
...             | PEA.evL _ sM = finishTSc-ev-abs-wt l cl sv csc css bfc bfs ip cl≢sv iomem sM
...             | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-dir-noBoth l sv (tss ip) e₁ (λ q → cl≢sv (trans (sym (absTSc-ev-dir l cl (tsc ip) sM)) q))) (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noTS l cl (lnc ip) e₁) (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noTS l sv (lns ip) e₁) (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noTS l cl (lfc ip) e₁) (absLFs-noTS l sv (lfs ip) e₁)))) (_ , sTail))
...             | PEA.evR _ q7
                with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSs l sv (tss ip)) _ q7
...               | PEA.evSync () _ _
...               | PEA.evL _ sM = finishTSs-ev-abs-wt l cl sv csc css bfc bfs ip cl≢sv iomem sM
...               | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noTS l cl (lnc ip) e₁) (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noTS l sv (lns ip) e₁) (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noTS l cl (lfc ip) e₁) (absLFs-noTS l sv (lfs ip) e₁))) (_ , sTail))
...               | PEA.evR _ q8
                  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNc l cl (lnc ip)) _ q8
...                 | PEA.evSync () _ _
...                 | PEA.evL _ sM = ⊥-elim (absLNc-noTS l cl (lnc ip) e₁ (_ , sM))
...                 | PEA.evBoth _ sM _ = ⊥-elim (absLNc-noTS l cl (lnc ip) e₁ (_ , sM))
...                 | PEA.evR _ q9
                    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNs l sv (lns ip)) _ q9
...                   | PEA.evSync () _ _
...                   | PEA.evL _ sM = ⊥-elim (absLNs-noTS l sv (lns ip) e₁ (_ , sM))
...                   | PEA.evBoth _ sM _ = ⊥-elim (absLNs-noTS l sv (lns ip) e₁ (_ , sM))
...                   | PEA.evR _ q10
                      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) q10
...                     | PEA.evSync () _ _
...                     | PEA.evL _ sM = ⊥-elim (absLFc-noTS l cl (lfc ip) e₁ (_ , sM))
...                     | PEA.evBoth _ sM _ = ⊥-elim (absLFc-noTS l cl (lfc ip) e₁ (_ , sM))
...                     | PEA.evR _ qs = ⊥-elim (absLFs-noTS l sv (lfs ip) e₁ (_ , qs))

------------------------------------------------------------------------

absBundleLN-ev-prod-wt : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : LN.LNEv X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , ιLN e₁) a
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► Bd′
  → BundleGEvR-abs-wt l cl sv csc css bfc bfs ip (ιLN e₁) a Bd′
absBundleLN-ev-prod-wt l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} iomem step
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAc l cl (kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evL _ sM = ⊥-elim (absKAc-noLN l cl (kac ip) e₁ (_ , sM))
... | PEA.evBoth _ sM _ = ⊥-elim (absKAc-noLN l cl (kac ip) e₁ (_ , sM))
... | PEA.evR _ q1
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAs l sv (kas ip)) _ q1
...   | PEA.evSync () _ _
...   | PEA.evL _ sM = ⊥-elim (absKAs-noLN l sv (kas ip) e₁ (_ , sM))
...   | PEA.evBoth _ sM _ = ⊥-elim (absKAs-noLN l sv (kas ip) e₁ (_ , sM))
...   | PEA.evR _ q2
      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSc l cl csc) _ q2
...     | PEA.evSync () _ _
...     | PEA.evL _ sM = ⊥-elim (absCSc-noLN l cl csc e₁ (_ , sM))
...     | PEA.evBoth _ sM _ = ⊥-elim (absCSc-noLN l cl csc e₁ (_ , sM))
...     | PEA.evR _ q3
        with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSs l sv css) _ q3
...       | PEA.evSync () _ _
...       | PEA.evL _ sM = ⊥-elim (absCSs-noLN l sv css e₁ (_ , sM))
...       | PEA.evBoth _ sM _ = ⊥-elim (absCSs-noLN l sv css e₁ (_ , sM))
...       | PEA.evR _ q4
          with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFc l cl bfc) _ q4
...         | PEA.evSync () _ _
...         | PEA.evL _ sM = ⊥-elim (absBFc-noLN l cl bfc e₁ (_ , sM))
...         | PEA.evBoth _ sM _ = ⊥-elim (absBFc-noLN l cl bfc e₁ (_ , sM))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM = ⊥-elim (absBFs-noLN l sv bfs e₁ (_ , sM))
...           | PEA.evBoth _ sM _ = ⊥-elim (absBFs-noLN l sv bfs e₁ (_ , sM))
...           | PEA.evR _ q6
              with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSc l cl (tsc ip)) _ q6
...             | PEA.evSync () _ _
...             | PEA.evL _ sM = ⊥-elim (absTSc-noLN l cl (tsc ip) e₁ (_ , sM))
...             | PEA.evBoth _ sM _ = ⊥-elim (absTSc-noLN l cl (tsc ip) e₁ (_ , sM))
...             | PEA.evR _ q7
                with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSs l sv (tss ip)) _ q7
...               | PEA.evSync () _ _
...               | PEA.evL _ sM = ⊥-elim (absTSs-noLN l sv (tss ip) e₁ (_ , sM))
...               | PEA.evBoth _ sM _ = ⊥-elim (absTSs-noLN l sv (tss ip) e₁ (_ , sM))
...               | PEA.evR _ q8
                  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNc l cl (lnc ip)) _ q8
...                 | PEA.evSync () _ _
...                 | PEA.evL _ sM = finishLNc-ev-abs-wt l cl sv csc css bfc bfs ip cl≢sv iomem sM
...                 | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-dir-noBoth l sv (lns ip) e₁ (λ q → cl≢sv (trans (sym (absLNc-ev-dir l cl (lnc ip) sM)) q))) (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noLN l cl (lfc ip) e₁) (absLFs-noLN l sv (lfs ip) e₁)) (_ , sTail))
...                 | PEA.evR _ q9
                    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNs l sv (lns ip)) _ q9
...                   | PEA.evSync () _ _
...                   | PEA.evL _ sM = finishLNs-ev-abs-wt l cl sv csc css bfc bfs ip cl≢sv iomem sM
...                   | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noLN l cl (lfc ip) e₁) (absLFs-noLN l sv (lfs ip) e₁) (_ , sTail))
...                   | PEA.evR _ q10
                      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) q10
...                     | PEA.evSync () _ _
...                     | PEA.evL _ sM = ⊥-elim (absLFc-noLN l cl (lfc ip) e₁ (_ , sM))
...                     | PEA.evBoth _ sM _ = ⊥-elim (absLFc-noLN l cl (lfc ip) e₁ (_ , sM))
...                     | PEA.evR _ qs = ⊥-elim (absLFs-noLN l sv (lfs ip) e₁ (_ , qs))

------------------------------------------------------------------------

absBundleLF-ev-prod-wt : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : LF.LFEv X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , ιLF e₁) a
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► Bd′
  → BundleGEvR-abs-wt l cl sv csc css bfc bfs ip (ιLF e₁) a Bd′
absBundleLF-ev-prod-wt l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} iomem step
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAc l cl (kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evL _ sM = ⊥-elim (absKAc-noLF l cl (kac ip) e₁ (_ , sM))
... | PEA.evBoth _ sM _ = ⊥-elim (absKAc-noLF l cl (kac ip) e₁ (_ , sM))
... | PEA.evR _ q1
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAs l sv (kas ip)) _ q1
...   | PEA.evSync () _ _
...   | PEA.evL _ sM = ⊥-elim (absKAs-noLF l sv (kas ip) e₁ (_ , sM))
...   | PEA.evBoth _ sM _ = ⊥-elim (absKAs-noLF l sv (kas ip) e₁ (_ , sM))
...   | PEA.evR _ q2
      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSc l cl csc) _ q2
...     | PEA.evSync () _ _
...     | PEA.evL _ sM = ⊥-elim (absCSc-noLF l cl csc e₁ (_ , sM))
...     | PEA.evBoth _ sM _ = ⊥-elim (absCSc-noLF l cl csc e₁ (_ , sM))
...     | PEA.evR _ q3
        with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSs l sv css) _ q3
...       | PEA.evSync () _ _
...       | PEA.evL _ sM = ⊥-elim (absCSs-noLF l sv css e₁ (_ , sM))
...       | PEA.evBoth _ sM _ = ⊥-elim (absCSs-noLF l sv css e₁ (_ , sM))
...       | PEA.evR _ q4
          with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFc l cl bfc) _ q4
...         | PEA.evSync () _ _
...         | PEA.evL _ sM = ⊥-elim (absBFc-noLF l cl bfc e₁ (_ , sM))
...         | PEA.evBoth _ sM _ = ⊥-elim (absBFc-noLF l cl bfc e₁ (_ , sM))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM = ⊥-elim (absBFs-noLF l sv bfs e₁ (_ , sM))
...           | PEA.evBoth _ sM _ = ⊥-elim (absBFs-noLF l sv bfs e₁ (_ , sM))
...           | PEA.evR _ q6
              with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSc l cl (tsc ip)) _ q6
...             | PEA.evSync () _ _
...             | PEA.evL _ sM = ⊥-elim (absTSc-noLF l cl (tsc ip) e₁ (_ , sM))
...             | PEA.evBoth _ sM _ = ⊥-elim (absTSc-noLF l cl (tsc ip) e₁ (_ , sM))
...             | PEA.evR _ q7
                with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSs l sv (tss ip)) _ q7
...               | PEA.evSync () _ _
...               | PEA.evL _ sM = ⊥-elim (absTSs-noLF l sv (tss ip) e₁ (_ , sM))
...               | PEA.evBoth _ sM _ = ⊥-elim (absTSs-noLF l sv (tss ip) e₁ (_ , sM))
...               | PEA.evR _ q8
                  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNc l cl (lnc ip)) _ q8
...                 | PEA.evSync () _ _
...                 | PEA.evL _ sM = ⊥-elim (absLNc-noLF l cl (lnc ip) e₁ (_ , sM))
...                 | PEA.evBoth _ sM _ = ⊥-elim (absLNc-noLF l cl (lnc ip) e₁ (_ , sM))
...                 | PEA.evR _ q9
                    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNs l sv (lns ip)) _ q9
...                   | PEA.evSync () _ _
...                   | PEA.evL _ sM = ⊥-elim (absLNs-noLF l sv (lns ip) e₁ (_ , sM))
...                   | PEA.evBoth _ sM _ = ⊥-elim (absLNs-noLF l sv (lns ip) e₁ (_ , sM))
...                   | PEA.evR _ q10
                      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) q10
...                     | PEA.evSync () _ _
...                     | PEA.evL _ sM = finishLFc-ev-abs-wt l cl sv csc css bfc bfs ip cl≢sv iomem sM
...                     | PEA.evBoth _ sM sTail = ⊥-elim (absLFs-dir-noBoth l sv (lfs ip) e₁ (λ q → cl≢sv (trans (sym (absLFc-ev-dir l cl (lfc ip) sM)) q)) (_ , sTail))
...                     | PEA.evR _ qs = finishLFs-ev-abs-wt l cl sv csc css bfc bfs ip cl≢sv iomem qs

------------------------------------------------------------------------

------------------------------------------------------------------------
-- the unified io dispatcher WITH drop: mirror `absBundleG-io-prod`, calling
-- the per-channel `absBundleX-ev-prod-wt` (which return `BundleGEvR-abs-wt`).
------------------------------------------------------------------------
absBundleG-io-prod-wt : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → BundleGEvR-abs-wt l cl sv csc css bfc bfs ip e a Bd′

absBundleG-io-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_ChainSync}    iomem step = absBundleCS-ev-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e₁ = CS.sendCS    l′ d′} iomem step
absBundleG-io-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_ChainSync}    iomem step = absBundleCS-ev-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e₁ = CS.receiveCS l′ d′} iomem step
absBundleG-io-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_BlockFetch}   iomem step = absBundleBF-ev-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e₁ = BF.sendBF    l′ d′} iomem step
absBundleG-io-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_BlockFetch}   iomem step = absBundleBF-ev-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e₁ = BF.receiveBF l′ d′} iomem step
absBundleG-io-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_KeepAlive}    iomem step = absBundleKA-ev-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e₁ = KA.sendKA    l′ d′} iomem step
absBundleG-io-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_KeepAlive}    iomem step = absBundleKA-ev-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e₁ = KA.receiveKA l′ d′} iomem step
absBundleG-io-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_TxSubmission} iomem step = absBundleTS-ev-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e₁ = TS.sendTS    l′ d′} iomem step
absBundleG-io-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_TxSubmission} iomem step = absBundleTS-ev-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e₁ = TS.receiveTS l′ d′} iomem step
absBundleG-io-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_LeiosNotify}  iomem step = absBundleLN-ev-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e₁ = LN.sendLN    l′ d′} iomem step
absBundleG-io-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_LeiosNotify}  iomem step = absBundleLN-ev-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e₁ = LN.receiveLN l′ d′} iomem step
absBundleG-io-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_LeiosFetch}   iomem step = absBundleLF-ev-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e₁ = LF.sendLF    l′ d′} iomem step
absBundleG-io-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_LeiosFetch}   iomem step = absBundleLF-ev-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e₁ = LF.receiveLF l′ d′} iomem step
absBundleG-io-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e = done   _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e = apiCS  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e = apiBF  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e = apiKA  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e = apiTS  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e = apiLN  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e = apiLF  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e = sndmsg _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e = rcvmsg _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e = tx     _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e = sndack _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e = rcvack _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e = ack    _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-prod-wt l cl sv cl≢sv csc css bfc bfs ip {e = break  _}     iomem step = ⊥-elim iomem


------------------------------------------------------------------------
-- NODE LEVEL — the four node io peels WITH the `nodeWtX` drop, then
-- `top-nodes-io-abs-wt` combining them into the whole `nodesWt` drop.
------------------------------------------------------------------------

data NodeAEvR-abs-wt (na : SN.NodeStateA) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                  (M : NetProc) : Set₁ where
  naEBawt : (na′ : SN.NodeStateA) → M ≡ absNodeA na′
        → SN.decNodeA na ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeA na′
        → nodeWtA na′ < nodeWtA na
        → NodeAEvR-abs-wt na e a M

data NodeBEvR-abs-wt (nb : SN.NodeStateB) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                  (M : NetProc) : Set₁ where
  nbEBawt : (nb′ : SN.NodeStateB) → M ≡ absNodeB nb′
        → SN.decNodeB nb ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeB nb′
        → nodeWtB nb′ < nodeWtB nb
        → NodeBEvR-abs-wt nb e a M

data NodeCEvR-abs-wt (nc : SN.NodeStateC) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                  (M : NetProc) : Set₁ where
  ncEBawt : (nc′ : SN.NodeStateC) → M ≡ absNodeC nc′
        → SN.decNodeC nc ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeC nc′
        → nodeWtC nc′ < nodeWtC nc
        → NodeCEvR-abs-wt nc e a M

data NodeDEvR-abs-wt (nd : SN.NodeStateD) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                  (M : NetProc) : Set₁ where
  ndEBawt : (nd′ : SN.NodeStateD) → M ≡ absNodeD nd′
        → SN.decNodeD nd ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeD nd′
        → nodeWtD nd′ < nodeWtD nd
        → NodeDEvR-abs-wt nd e a M

nodeA-io-AB-abs-wt : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeAEvR-abs-wt na e a ((Bd′ ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)))
nodeA-io-AB-abs-wt na {X} {e} {a} iomem sBAB
  with absBundleG-io-prod-wt linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) iomem sBAB
... | bgEBwt csc′ css′ bfc′ bfs′ ip′ eq run drop =
      naEBawt (SN.mkNodeA csc′ css′ bfc′ bfs′ (SN.NodeStateA.prod-AB na) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) ip′ (SN.NodeStateA.inert-AC na))
        (cong (λ z → (z ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na))) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeA-drv-io-no na iomem))
           (⦀-wev-L _ _
              (noOffer→viewV _ (bundleG-io-no linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)
                 (absBundleG-io-ahl linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) iomem sBAB) linkAB≢linkAC iomem))
              run))
        (subst₂ _<_ (sym (nodeWtA-split ((SN.mkNodeA csc′ css′ bfc′ bfs′ (SN.NodeStateA.prod-AB na) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) ip′ (SN.NodeStateA.inert-AC na))))) (sym (nodeWtA-split na)) (+-monoˡ-< (bundleWt (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) drop))

nodeA-io-AC-abs-wt : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeAEvR-abs-wt na e a ((absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ⦀ Bd′) ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)))
nodeA-io-AC-abs-wt na {X} {e} {a} iomem sBAC
  with absBundleG-io-prod-wt linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) iomem sBAC
... | bgEBwt csc′ css′ bfc′ bfs′ ip′ eq run drop =
      naEBawt (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na) csc′ css′ bfc′ bfs′ (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) ip′)
        (cong (λ z → (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ⦀ z) ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na))) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeA-drv-io-no na iomem))
           (⦀-wev-R _ _
              (noOffer→viewV _ (bundleG-io-no linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
                 (absBundleG-io-ahl linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) iomem sBAC) (λ q → linkAB≢linkAC (sym q)) iomem))
              run))
        (subst₂ _<_ (sym (nodeWtA-split ((SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na) csc′ css′ bfc′ bfs′ (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) ip′)))) (sym (nodeWtA-split na)) (+-monoʳ-< (bundleWt (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)) drop))

nodeB-io-AB-abs-wt : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeBEvR-abs-wt nb e a ((Bd′ ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
nodeB-io-AB-abs-wt nb {X} {e} {a} iomem sBAB
  with absBundleG-io-prod-wt linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) iomem sBAB
... | bgEBwt csc′ css′ bfc′ bfs′ ip′ eq run drop =
      nbEBawt (SN.mkNodeB csc′ css′ bfc′ bfs′ (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) ip′ (SN.NodeStateB.inert-BD nb))
        (cong (λ z → (z ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb)) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeB-drv-io-no nb iomem))
           (⦀-wev-L _ _
              (noOffer→viewV _ (bundleG-io-no linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)
                 (absBundleG-io-ahl linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) iomem sBAB) linkAB≢linkBD iomem))
              run))
        (subst₂ _<_ (sym (nodeWtB-split ((SN.mkNodeB csc′ css′ bfc′ bfs′ (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) ip′ (SN.NodeStateB.inert-BD nb))))) (sym (nodeWtB-split nb)) (+-monoˡ-< (bundleWt (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)) drop))

nodeB-io-BD-abs-wt : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeBEvR-abs-wt nb e a ((absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ⦀ Bd′) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
nodeB-io-BD-abs-wt nb {X} {e} {a} iomem sBBD
  with absBundleG-io-prod-wt linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) iomem sBBD
... | bgEBwt csc′ css′ bfc′ bfs′ ip′ eq run drop =
      nbEBawt (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) csc′ css′ bfc′ bfs′ (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) ip′)
        (cong (λ z → (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ⦀ z) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb)) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeB-drv-io-no nb iomem))
           (⦀-wev-R _ _
              (noOffer→viewV _ (bundleG-io-no linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
                 (absBundleG-io-ahl linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) iomem sBBD) (λ q → linkAB≢linkBD (sym q)) iomem))
              run))
        (subst₂ _<_ (sym (nodeWtB-split ((SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) csc′ css′ bfc′ bfs′ (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) ip′)))) (sym (nodeWtB-split nb)) (+-monoʳ-< (bundleWt (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)) drop))

nodeC-io-AC-abs-wt : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeCEvR-abs-wt nc e a ((Bd′ ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
nodeC-io-AC-abs-wt nc {X} {e} {a} iomem sBAC
  with absBundleG-io-prod-wt linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) iomem sBAC
... | bgEBwt csc′ css′ bfc′ bfs′ ip′ eq run drop =
      ncEBawt (SN.mkNodeC csc′ css′ bfc′ bfs′ (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) ip′ (SN.NodeStateC.inert-CD nc))
        (cong (λ z → (z ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc)) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeC-drv-io-no nc iomem))
           (⦀-wev-L _ _
              (noOffer→viewV _ (bundleG-io-no linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)
                 (absBundleG-io-ahl linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) iomem sBAC) linkAC≢linkCD iomem))
              run))
        (subst₂ _<_ (sym (nodeWtC-split ((SN.mkNodeC csc′ css′ bfc′ bfs′ (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) ip′ (SN.NodeStateC.inert-CD nc))))) (sym (nodeWtC-split nc)) (+-monoˡ-< (bundleWt (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)) drop))

nodeC-io-CD-abs-wt : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeCEvR-abs-wt nc e a ((absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ⦀ Bd′) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
nodeC-io-CD-abs-wt nc {X} {e} {a} iomem sBCD
  with absBundleG-io-prod-wt linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) iomem sBCD
... | bgEBwt csc′ css′ bfc′ bfs′ ip′ eq run drop =
      ncEBawt (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) csc′ css′ bfc′ bfs′ (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) ip′)
        (cong (λ z → (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ⦀ z) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc)) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeC-drv-io-no nc iomem))
           (⦀-wev-R _ _
              (noOffer→viewV _ (bundleG-io-no linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
                 (absBundleG-io-ahl linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) iomem sBCD) (λ q → linkAC≢linkCD (sym q)) iomem))
              run))
        (subst₂ _<_ (sym (nodeWtC-split ((SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) csc′ css′ bfc′ bfs′ (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) ip′)))) (sym (nodeWtC-split nc)) (+-monoʳ-< (bundleWt (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)) drop))

nodeD-io-BD-abs-wt : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeDEvR-abs-wt nd e a ((Bd′ ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)))
nodeD-io-BD-abs-wt nd {X} {e} {a} iomem sBBD
  with absBundleG-io-prod-wt linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) iomem sBBD
... | bgEBwt csc′ css′ bfc′ bfs′ ip′ eq run drop =
      ndEBawt (SN.mkNodeD csc′ css′ bfc′ bfs′ (SN.NodeStateD.cons-BD nd) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) ip′ (SN.NodeStateD.inert-CD nd))
        (cong (λ z → (z ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeD-drv-io-no nd iomem))
           (⦀-wev-L _ _
              (noOffer→viewV _ (bundleG-io-no linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)
                 (absBundleG-io-ahl linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) iomem sBBD) linkBD≢linkCD iomem))
              run))
        (subst₂ _<_ (sym (nodeWtD-split ((SN.mkNodeD csc′ css′ bfc′ bfs′ (SN.NodeStateD.cons-BD nd) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) ip′ (SN.NodeStateD.inert-CD nd))))) (sym (nodeWtD-split nd)) (+-monoˡ-< (bundleWt (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) drop))

nodeD-io-CD-abs-wt : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeDEvR-abs-wt nd e a ((absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ⦀ Bd′) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)))
nodeD-io-CD-abs-wt nd {X} {e} {a} iomem sBCD
  with absBundleG-io-prod-wt linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) iomem sBCD
... | bgEBwt csc′ css′ bfc′ bfs′ ip′ eq run drop =
      ndEBawt (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd) csc′ css′ bfc′ bfs′ (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) ip′)
        (cong (λ z → (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ⦀ z) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeD-drv-io-no nd iomem))
           (⦀-wev-R _ _
              (noOffer→viewV _ (bundleG-io-no linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
                 (absBundleG-io-ahl linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) iomem sBCD) (λ q → linkBD≢linkCD (sym q)) iomem))
              run))
        (subst₂ _<_ (sym (nodeWtD-split ((SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd) csc′ css′ bfc′ bfs′ (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) ip′)))) (sym (nodeWtD-split nd)) (+-monoʳ-< (bundleWt (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)) drop))

nodeA-ev-io-abs-wt : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodeA na ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeAEvR-abs-wt na e a M
nodeA-ev-io-abs-wt na {X} {e} {a} iomem step
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
...   | PEA.evL _ sBAB = nodeA-io-AB-abs-wt na iomem sBAB
...   | PEA.evR _ sBAC = nodeA-io-AC-abs-wt na iomem sBAC

nodeB-ev-io-abs-wt : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodeB nb ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeBEvR-abs-wt nb e a M
nodeB-ev-io-abs-wt nb {X} {e} {a} iomem step
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
...   | PEA.evL _ sBAB = nodeB-io-AB-abs-wt nb iomem sBAB
...   | PEA.evR _ sBBD = nodeB-io-BD-abs-wt nb iomem sBBD

nodeC-ev-io-abs-wt : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodeC nc ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeCEvR-abs-wt nc e a M
nodeC-ev-io-abs-wt nc {X} {e} {a} iomem step
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
...   | PEA.evL _ sBAC = nodeC-io-AC-abs-wt nc iomem sBAC
...   | PEA.evR _ sBCD = nodeC-io-CD-abs-wt nc iomem sBCD

nodeD-ev-io-abs-wt : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodeD nd ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeDEvR-abs-wt nd e a M
nodeD-ev-io-abs-wt nd {X} {e} {a} iomem step
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
...   | PEA.evL _ sBBD = nodeD-io-BD-abs-wt nd iomem sBBD
...   | PEA.evR _ sBCD = nodeD-io-CD-abs-wt nd iomem sBCD

top-nodes-io-abs-wt : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → SStep.absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ s′ ∈ SysState ] (med s ≡ med s′) × (M ≡ SStep.absNodesOf s′) × (SStep.nodesOf s ═[ ev (evl (evLabel X e a)) ]═► SStep.nodesOf s′) × (nodesWt s′ < nodesWt s)
top-nodes-io-abs-wt s iomem nodesStep
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (absNodeA (nA s)) (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s))) nodesStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sA sRest = ⊥-elim (absGroupA-io-no (nA s) (nB s) (nC s) (nD s) iomem sA (_ , sRest))
... | PEA.evL _ sA with nodeA-ev-io-abs-wt (nA s) iomem sA
...   | naEBawt na′ Meq weakRunA ndrop =
        mkSys (med s) na′ (nB s) (nC s) (nD s) , refl ,
        cong (λ z → z ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) Meq ,
        ⦀-wev-L (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (SStep.⦀-noOffer (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (nodeB-io-no-when-A (nB s) iomem fpA)
             (SStep.⦀-noOffer (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (nodeC-io-no-when-A (nC s) iomem fpA) (nodeD-io-no-when-A (nD s) iomem fpA))))
          weakRunA
        ,
        (+-monoˡ-< (nodeWtD (nD s)) (+-monoˡ-< (nodeWtC (nC s)) (+-monoˡ-< (nodeWtB (nB s)) ndrop)))
  where fpA = absNodeA-io-fp (nA s) iomem sA
top-nodes-io-abs-wt s iomem nodesStep | PEA.evR _ sRest
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s)) sRest
... | PEA.evSync () _ _
... | PEA.evBoth _ sB sCD = ⊥-elim (absGroupB-io-no (nB s) (nC s) (nD s) iomem sB (_ , sCD))
... | PEA.evL _ sB with nodeB-ev-io-abs-wt (nB s) iomem sB
...   | nbEBawt nb′ Meq weakRunB ndrop =
        mkSys (med s) (nA s) nb′ (nC s) (nD s) , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (z ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) Meq ,
        ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (nodeA-io-no-when-B (nA s) iomem fpB))
          (⦀-wev-L (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (noOffer→viewV _ (SStep.⦀-noOffer (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (nodeC-io-no-when-B (nC s) iomem fpB) (nodeD-io-no-when-B (nD s) iomem fpB)))
             weakRunB)
        ,
        (+-monoˡ-< (nodeWtD (nD s)) (+-monoˡ-< (nodeWtC (nC s)) (+-monoʳ-< (nodeWtA (nA s)) ndrop)))
  where fpB = absNodeB-io-fp (nB s) iomem sB
top-nodes-io-abs-wt s iomem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absNodeC (nC s)) (absNodeD (nD s)) sCD
... | PEA.evSync () _ _
... | PEA.evBoth _ sC sD = ⊥-elim (absNodeD-io-no-when-C (nD s) iomem (absNodeC-io-fp (nC s) iomem sC) (_ , sD))
... | PEA.evL _ sC with nodeC-ev-io-abs-wt (nC s) iomem sC
...   | ncEBawt nc′ Meq weakRunC ndrop =
        mkSys (med s) (nA s) (nB s) nc′ (nD s) , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (z ⦀ absNodeD (nD s)))) Meq ,
        ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (nodeA-io-no-when-C (nA s) iomem fpC))
          (⦀-wev-R (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (noOffer→viewV _ (nodeB-io-no-when-C (nB s) iomem fpC))
             (⦀-wev-L (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (noOffer→viewV _ (nodeD-io-no-when-C (nD s) iomem fpC))
                weakRunC))
        ,
        (+-monoˡ-< (nodeWtD (nD s)) (+-monoʳ-< (nodeWtA (nA s) + nodeWtB (nB s)) ndrop))
  where fpC = absNodeC-io-fp (nC s) iomem sC
top-nodes-io-abs-wt s iomem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD | PEA.evR _ sD
    with nodeD-ev-io-abs-wt (nD s) iomem sD
... | ndEBawt nd′ Meq weakRunD ndrop =
        mkSys (med s) (nA s) (nB s) (nC s) nd′ , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ z))) Meq ,
        ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (nodeA-io-no-when-D (nA s) iomem fpD))
          (⦀-wev-R (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (noOffer→viewV _ (nodeB-io-no-when-D (nB s) iomem fpD))
             (⦀-wev-R (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (noOffer→viewV _ (nodeC-io-no-when-D (nC s) iomem fpD))
                weakRunD))
        ,
        (+-monoʳ-< ((nodeWtA (nA s) + nodeWtB (nB s)) + nodeWtC (nC s)) ndrop)
  where fpD = absNodeD-io-fp (nD s) iomem sD

------------------------------------------------------------------------
