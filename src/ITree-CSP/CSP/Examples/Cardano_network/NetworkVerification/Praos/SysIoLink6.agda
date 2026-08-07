{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R2 — io-peel layer, PART 6 (WEAK-`⦀` congruence lift).
--
-- The backward abstract-primary node peels `nodeX-ev-{api,io}-abs` invoke a
-- peer's committed `decX-ev-prod-abs` leaf to obtain a CONCRETE peer WEAK run
-- `P ═[ev l]═► P′`, then must lift it up the node's `⦀` / `∥⇘apiES⇙ driver`
-- structure to a concrete NODE weak run.  `Semantics.WeakBisim` has the strong
-- single-step congruences (`⦀-ev-L`/`∥⇘⇙-ev-soloL`/`∥⇘⇙-ev-sync` in SysStep) but
-- NO weak-run versions.  This module supplies them, built directly on top of
-- those strong intro congruences:
--
--   · `⦀-τ*-L/R`, `∥⇘⇙-τ*-L/R`  — fold the strong τ-intro over a `─[τ*]─►` chain
--   · `⦀-wev-L/R`               — solo (∅ES interleave) weak lift through `⦀`
--   · `∥⇘⇙-wev-soloL/R`         — solo (event ∉ A) weak lift through `∥⇘ A ⇙`
--   · `∥⇘⇙-wev-sync`            — synchronised weak lift through `∥⇘ A ⇙` (BOTH
--                                 operands run weakly; interleaves each idle τ*)
--
-- A weak run `wev pre fire post` is a `τ*-refl`-padded fire; the `⦀`/`∥⇘⇙` lift
-- moves the firing operand while the OTHER stays idle (the sibling's non-offer
-- `viewV (force _) ≡ nothing` is the hypothesis for the solo lifts, exactly as
-- the strong congruences take it).
--
-- Re-exports PART 5 (`open import SysIoLink5 public`) so downstream consumers
-- import only SysIoLink6 (keeps SysIoLink5 frozen/capped; cheap `.agdai` load).
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.SysIoLink6 (blkA : Block₃) where

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
-- τ* folds: lift a whole silent run of one operand through `⦀` / `∥⇘ A ⇙`,
-- the other operand held fixed.
------------------------------------------------------------------------

-- left operand's τ* run through `⦀` (right idle)
⦀-τ*-L : (P Q : NetProc) {P′ : NetProc} → P ─[τ*]─► P′ → (P ⦀ Q) ─[τ*]─► (P′ ⦀ Q)
⦀-τ*-L P Q τ*-refl = τ*-refl
⦀-τ*-L P Q (τ*-step {t′ = P₁} s rest) = τ*-step (⦀-τ-L P Q s) (⦀-τ*-L P₁ Q rest)

-- right operand's τ* run through `⦀` (left idle)
⦀-τ*-R : (P Q : NetProc) {Q′ : NetProc} → Q ─[τ*]─► Q′ → (P ⦀ Q) ─[τ*]─► (P ⦀ Q′)
⦀-τ*-R P Q τ*-refl = τ*-refl
⦀-τ*-R P Q (τ*-step {t′ = Q₁} s rest) = τ*-step (⦀-τ-R P Q s) (⦀-τ*-R P Q₁ rest)

-- left operand's τ* run through `∥⇘ A ⇙` (right idle)
∥⇘⇙-τ*-L : (A : EventSet) (P Q : NetProc) {P′ : NetProc}
         → P ─[τ*]─► P′ → (P ∥⇘ A ⇙ Q) ─[τ*]─► (P′ ∥⇘ A ⇙ Q)
∥⇘⇙-τ*-L A P Q τ*-refl = τ*-refl
∥⇘⇙-τ*-L A P Q (τ*-step {t′ = P₁} s rest) = τ*-step (∥⇘⇙-τ-L A P Q s) (∥⇘⇙-τ*-L A P₁ Q rest)

-- right operand's τ* run through `∥⇘ A ⇙` (left idle)
∥⇘⇙-τ*-R : (A : EventSet) (P Q : NetProc) {Q′ : NetProc}
         → Q ─[τ*]─► Q′ → (P ∥⇘ A ⇙ Q) ─[τ*]─► (P ∥⇘ A ⇙ Q′)
∥⇘⇙-τ*-R A P Q τ*-refl = τ*-refl
∥⇘⇙-τ*-R A P Q (τ*-step {t′ = Q₁} s rest) = τ*-step (∥⇘⇙-τ-R A P Q s) (∥⇘⇙-τ*-R A P Q₁ rest)

------------------------------------------------------------------------
-- SOLO weak lifts: the firing operand runs weakly; the idle sibling
-- (held fixed) offers nothing at the fired event.
------------------------------------------------------------------------

-- LEFT operand weak-fires solo through `⦀`; right idle (non-offer hypothesis)
⦀-wev-L : (P Q : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {P′ : NetProc}
        → viewV (PTree.force Q) (X , e) a ≡ nothing
        → P ═[ ev (evl (evLabel X e a)) ]═► P′
        → (P ⦀ Q) ═[ ev (evl (evLabel X e a)) ]═► (P′ ⦀ Q)
⦀-wev-L P Q nq (wev {p′ = P₁} {q′ = P₂} pre fire post) =
  wev (⦀-τ*-L P Q pre) (⦀-ev-L P₁ Q fire nq) (⦀-τ*-L P₂ Q post)

-- RIGHT operand weak-fires solo through `⦀`; left idle (non-offer hypothesis)
⦀-wev-R : (P Q : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Q′ : NetProc}
        → viewV (PTree.force P) (X , e) a ≡ nothing
        → Q ═[ ev (evl (evLabel X e a)) ]═► Q′
        → (P ⦀ Q) ═[ ev (evl (evLabel X e a)) ]═► (P ⦀ Q′)
⦀-wev-R P Q np (wev {p′ = Q₁} {q′ = Q₂} pre fire post) =
  wev (⦀-τ*-R P Q pre) (⦀-ev-R P Q₁ fire np) (⦀-τ*-R P Q₂ post)

-- LEFT operand weak-fires solo through `∥⇘ A ⇙` (event ∉ A); right idle
∥⇘⇙-wev-soloL : (A : EventSet) (P Q : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X}
                {a : X} {P′ : NetProc}
              → ¬ A .mem (X , e) a
              → viewV (PTree.force Q) (X , e) a ≡ nothing
              → P ═[ ev (evl (evLabel X e a)) ]═► P′
              → (P ∥⇘ A ⇙ Q) ═[ ev (evl (evLabel X e a)) ]═► (P′ ∥⇘ A ⇙ Q)
∥⇘⇙-wev-soloL A P Q ¬mem nq (wev {p′ = P₁} {q′ = P₂} pre fire post) =
  wev (∥⇘⇙-τ*-L A P Q pre) (∥⇘⇙-ev-soloL A P₁ Q ¬mem fire nq) (∥⇘⇙-τ*-L A P₂ Q post)

-- RIGHT operand weak-fires solo through `∥⇘ A ⇙` (event ∉ A); left idle
∥⇘⇙-wev-soloR : (A : EventSet) (P Q : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X}
                {a : X} {Q′ : NetProc}
              → ¬ A .mem (X , e) a
              → viewV (PTree.force P) (X , e) a ≡ nothing
              → Q ═[ ev (evl (evLabel X e a)) ]═► Q′
              → (P ∥⇘ A ⇙ Q) ═[ ev (evl (evLabel X e a)) ]═► (P ∥⇘ A ⇙ Q′)
∥⇘⇙-wev-soloR A P Q ¬mem np (wev {p′ = Q₁} {q′ = Q₂} pre fire post) =
  wev (∥⇘⇙-τ*-R A P Q pre) (∥⇘⇙-ev-soloR A P Q₁ ¬mem fire np) (∥⇘⇙-τ*-R A P Q₂ post)

------------------------------------------------------------------------
-- SYNC weak lift: BOTH operands weak-fire the shared event (∈ A).  Each
-- operand's τ* prefix/suffix is interleaved against the other held idle
-- (the τ*-fold above), the fires synchronised by the strong `∥⇘⇙-ev-sync`.
------------------------------------------------------------------------

-- synchronised weak fire through `∥⇘ A ⇙` (api driver↔peer sync)
∥⇘⇙-wev-sync : (A : EventSet) (P D : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X}
               {a : X} {P′ D′ : NetProc}
             → A .mem (X , e) a
             → P ═[ ev (evl (evLabel X e a)) ]═► P′
             → D ═[ ev (evl (evLabel X e a)) ]═► D′
             → (P ∥⇘ A ⇙ D) ═[ ev (evl (evLabel X e a)) ]═► (P′ ∥⇘ A ⇙ D′)
∥⇘⇙-wev-sync A P D m (wev {p′ = P₁} {q′ = P₂} pP fP qP)
                     (wev {p′ = D₁} {q′ = D₂} pD fD qD) =
  wev (τ*-trans (∥⇘⇙-τ*-L A P D pP) (∥⇘⇙-τ*-R A P₁ D pD))
      (∥⇘⇙-ev-sync A P₁ D₁ m fP fD)
      (τ*-trans (∥⇘⇙-τ*-L A P₂ D₂ qP) (∥⇘⇙-τ*-R A _ D₂ qD))

------------------------------------------------------------------------
-- PART 2a — abstract CS bundle inversion (produces a concrete WEAK run).
--
-- Mirror of the committed forward `bundle-CS-ev-inv` skeleton, but with the
-- direction reversed: given an ABSTRACT bundle visible step at a CS-image
-- event, invert to the firing abstract CS peer, invoke the committed leaf
-- `decCSc/CSs-ev-prod-abs` to obtain the concrete peer WEAK run, and lift
-- that run up the 12-`⦀` nesting via the PART-1 `⦀-wev-L/R`.  The ten
-- sibling non-firings are refuted exactly as in `absBundleCS-io-role`.
------------------------------------------------------------------------

-- abstract CS-client firing pins the event's direction to `cl`
absCSc-ev-dir : (l : Link) (cl : Dir) (csc : CScPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {M : NetProc}
  → absCSc l cl csc ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► M → csEvDir e₁ ≡ cl
absCSc-ev-dir l cl csc {e₁ = e₁} step with tableSpec-ev-inv (Tcsc l cl) (coarsenCSc csc) step
... | q′ , ceq , _ with csEvDir e₁ ≟ cl
...   | yes eq  = eq
...   | no  ¬eq = ⊥-elim (nothing-absurd (trans (sym (csCnxt-dir-no l cl (coarsenCSc csc) e₁ ¬eq)) ceq))

-- abstract CS-server firing pins the event's direction to `sv`
absCSs-ev-dir : (l : Link) (sv : Dir) (css : CSsPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {M : NetProc}
  → absCSs l sv css ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► M → csEvDir e₁ ≡ sv
absCSs-ev-dir l sv css {e₁ = e₁} step with tableSpec-ev-inv (Tcss l sv) (coarsenCSs css) step
... | q′ , ceq , _ with csEvDir e₁ ≟ sv
...   | yes eq  = eq
...   | no  ¬eq = ⊥-elim (nothing-absurd (trans (sym (csSnxt-dir-no l sv (coarsenCSs css) e₁ ¬eq)) ceq))

-- which driven CS peer fired + the updated position + the concrete WEAK run
data BundleCSEvR-abs (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} (e₁ : CS.CSEv X) (a : X) (Bd′ : NetProc) : Set₁ where
  bcscEB : (csc′ : CScPos)
        → Bd′ ≡ absBundleG l cl sv csc′ css bfc bfs ip
        → bundleG l cl sv csc css bfc bfs ip
            ═[ ev (evl (evLabel X (ιCS e₁) a)) ]═► bundleG l cl sv csc′ css bfc bfs ip
        → BundleCSEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′
  bcssEB : (css′ : CSsPos)
        → Bd′ ≡ absBundleG l cl sv csc css′ bfc bfs ip
        → bundleG l cl sv csc css bfc bfs ip
            ═[ ev (evl (evLabel X (ιCS e₁) a)) ]═► bundleG l cl sv csc css′ bfc bfs ip
        → BundleCSEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′

-- fold a CS-client abstract fire into the bundle result: leaf → concrete run,
-- lifted past `decKAc`/`decKAs` (⦀-wev-R) and the 9-peer tail (⦀-wev-L)
finishCSc-ev-abs : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → absCSc l cl csc ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► P′
  → BundleCSEvR-abs l cl sv csc css bfc bfs ip e₁ a
      (absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (P′
        ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
        ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
        ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip))))))))))))
finishCSc-ev-abs l cl sv csc css bfc bfs ip {e₁ = e₁} cl≢sv sM with decCSc-ev-prod-abs l cl csc sM
... | csc′ , run , Meq =
      bcscEB csc′
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

-- fold a CS-server abstract fire into the bundle result: leaf → concrete run,
-- lifted past `decKAc`/`decKAs`/`decCSc` (⦀-wev-R) and the 8-peer tail (⦀-wev-L)
finishCSs-ev-abs : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → absCSs l sv css ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► P′
  → BundleCSEvR-abs l cl sv csc css bfc bfs ip e₁ a
      (absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (P′
        ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
        ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
        ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip))))))))))))
finishCSs-ev-abs l cl sv csc css bfc bfs ip {e₁ = e₁} cl≢sv sM with decCSs-ev-prod-abs l sv css sM
... | css′ , run , Meq =
      bcssEB css′
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

-- 12-peer abstract bundle ev-inversion (CS): peel each `⦀`, refute the ten
-- siblings (verbatim `absBundleCS-io-role` skeleton), fold the driven CS peer
absBundleCS-ev-prod : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {Bd′ : NetProc}
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► Bd′
  → BundleCSEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′
absBundleCS-ev-prod l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
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
...     | PEA.evL _ sM = finishCSc-ev-abs l cl sv csc css bfc bfs ip cl≢sv sM
...     | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absCSs l sv css) _ (absCSs-dir-noBoth l sv css e₁ (λ q → cl≢sv (trans (sym (absCSc-ev-dir l cl csc sM)) q))) (SStep.⦀-noOffer (absBFc l cl bfc) _ (absBFc-noCS l cl bfc e₁) (SStep.⦀-noOffer (absBFs l sv bfs) _ (absBFs-noCS l sv bfs e₁) (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noCS l cl (tsc ip) e₁) (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noCS l sv (tss ip) e₁) (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noCS l cl (lnc ip) e₁) (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noCS l sv (lns ip) e₁) (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noCS l cl (lfc ip) e₁) (absLFs-noCS l sv (lfs ip) e₁)))))))) (_ , sTail))
...     | PEA.evR _ q3
        with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSs l sv css) _ q3
...       | PEA.evSync () _ _
...       | PEA.evL _ sM = finishCSs-ev-abs l cl sv csc css bfc bfs ip cl≢sv sM
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

------------------------------------------------------------------------
-- PART 2b — abstract BF bundle inversion (mirror of PART 2a, BF channel).
------------------------------------------------------------------------

-- abstract BF-client firing pins the event's direction to `cl`
absBFc-ev-dir : (l : Link) (cl : Dir) (bfc : BFcPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {M : NetProc}
  → absBFc l cl bfc ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► M → bfEvDir e₁ ≡ cl
absBFc-ev-dir l cl bfc {e₁ = e₁} step with tableSpec-ev-inv (Tbfc l cl) (coarsenBFc bfc) step
... | q′ , ceq , _ with bfEvDir e₁ ≟ cl
...   | yes eq  = eq
...   | no  ¬eq = ⊥-elim (nothing-absurd (trans (sym (bfCnxt-dir-no l cl (coarsenBFc bfc) e₁ ¬eq)) ceq))

-- abstract BF-server firing pins the event's direction to `sv`
absBFs-ev-dir : (l : Link) (sv : Dir) (bfs : BFsPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {M : NetProc}
  → absBFs l sv bfs ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► M → bfEvDir e₁ ≡ sv
absBFs-ev-dir l sv bfs {e₁ = e₁} step with tableSpec-ev-inv (Tbfs l sv) (coarsenBFs bfs) step
... | q′ , ceq , _ with bfEvDir e₁ ≟ sv
...   | yes eq  = eq
...   | no  ¬eq = ⊥-elim (nothing-absurd (trans (sym (bfSnxt-dir-no l sv (coarsenBFs bfs) e₁ ¬eq)) ceq))

-- which driven BF peer fired + the updated position + the concrete WEAK run
data BundleBFEvR-abs (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} (e₁ : BF.BFEv X) (a : X) (Bd′ : NetProc) : Set₁ where
  bcbcEB : (bfc′ : BFcPos)
        → Bd′ ≡ absBundleG l cl sv csc css bfc′ bfs ip
        → bundleG l cl sv csc css bfc bfs ip
            ═[ ev (evl (evLabel X (ιBF e₁) a)) ]═► bundleG l cl sv csc css bfc′ bfs ip
        → BundleBFEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′
  bcbsEB : (bfs′ : BFsPos)
        → Bd′ ≡ absBundleG l cl sv csc css bfc bfs′ ip
        → bundleG l cl sv csc css bfc bfs ip
            ═[ ev (evl (evLabel X (ιBF e₁) a)) ]═► bundleG l cl sv csc css bfc bfs′ ip
        → BundleBFEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′

-- fold a BF-client abstract fire into the bundle result
finishBFc-ev-abs : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → absBFc l cl bfc ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► P′
  → BundleBFEvR-abs l cl sv csc css bfc bfs ip e₁ a
      (absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (P′
        ⦀ (absBFs l sv bfs ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
        ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip))))))))))))
finishBFc-ev-abs l cl sv csc css bfc bfs ip {e₁ = e₁} cl≢sv sM with decBFc-ev-prod-abs l cl bfc sM
... | bfc′ , run , Meq =
      bcbcEB bfc′
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

-- fold a BF-server abstract fire into the bundle result
finishBFs-ev-abs : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → absBFs l sv bfs ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► P′
  → BundleBFEvR-abs l cl sv csc css bfc bfs ip e₁ a
      (absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (P′
        ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
        ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip))))))))))))
finishBFs-ev-abs l cl sv csc css bfc bfs ip {e₁ = e₁} cl≢sv sM with decBFs-ev-prod-abs l sv bfs sM
... | bfs′ , run , Meq =
      bcbsEB bfs′
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

-- 12-peer abstract bundle ev-inversion (BF)
absBundleBF-ev-prod : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {Bd′ : NetProc}
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► Bd′
  → BundleBFEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′
absBundleBF-ev-prod l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
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
...         | PEA.evL _ sM = finishBFc-ev-abs l cl sv csc css bfc bfs ip cl≢sv sM
...         | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absBFs l sv bfs) _ (absBFs-dir-noBoth l sv bfs e₁ (λ q → cl≢sv (trans (sym (absBFc-ev-dir l cl bfc sM)) q))) (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noBF l cl (tsc ip) e₁) (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noBF l sv (tss ip) e₁) (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noBF l cl (lnc ip) e₁) (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noBF l sv (lns ip) e₁) (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noBF l cl (lfc ip) e₁) (absLFs-noBF l sv (lfs ip) e₁)))))) (_ , sTail))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM = finishBFs-ev-abs l cl sv csc css bfc bfs ip cl≢sv sM
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
-- PART 2c — abstract KA bundle inversion (KA client/server are peers #0/#1).
------------------------------------------------------------------------

-- abstract KA-client firing pins the event's direction to `cl`
absKAc-ev-dir : (l : Link) (cl : Dir) (kacp : KAcPos)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {M : NetProc}
  → absKAc l cl kacp ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► M → kaEvDir e₁ ≡ cl
absKAc-ev-dir l cl kacp {e₁ = e₁} step with tableSpec-ev-inv (Tkac l cl) (coarsenKAc kacp) step
... | q′ , ceq , _ with kaEvDir e₁ ≟ cl
...   | yes eq  = eq
...   | no  ¬eq = ⊥-elim (nothing-absurd (trans (sym (kaCnxt-dir-no l cl (coarsenKAc kacp) e₁ ¬eq)) ceq))

-- abstract KA-server firing pins the event's direction to `sv`
absKAs-ev-dir : (l : Link) (sv : Dir) (kasp : KAsPos)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {M : NetProc}
  → absKAs l sv kasp ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► M → kaEvDir e₁ ≡ sv
absKAs-ev-dir l sv kasp {e₁ = e₁} step with tableSpec-ev-inv (Tkas l sv) (coarsenKAs kasp) step
... | q′ , ceq , _ with kaEvDir e₁ ≟ sv
...   | yes eq  = eq
...   | no  ¬eq = ⊥-elim (nothing-absurd (trans (sym (kaSnxt-dir-no l sv (coarsenKAs kasp) e₁ ¬eq)) ceq))

-- which driven KA peer fired + the updated InertPos field + the concrete WEAK run
data BundleKAEvR-abs (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} (e₁ : KA.KAEv X) (a : X) (Bd′ : NetProc) : Set₁ where
  bkacEB : (kac′ : KAcPos)
        → Bd′ ≡ absBundleG l cl sv csc css bfc bfs (record ip { kac = kac′ })
        → bundleG l cl sv csc css bfc bfs ip
            ═[ ev (evl (evLabel X (ιKA e₁) a)) ]═► bundleG l cl sv csc css bfc bfs (record ip { kac = kac′ })
        → BundleKAEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′
  bkasEB : (kas′ : KAsPos)
        → Bd′ ≡ absBundleG l cl sv csc css bfc bfs (record ip { kas = kas′ })
        → bundleG l cl sv csc css bfc bfs ip
            ═[ ev (evl (evLabel X (ιKA e₁) a)) ]═► bundleG l cl sv csc css bfc bfs (record ip { kas = kas′ })
        → BundleKAEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′

-- fold a KA-client abstract fire into the bundle result (peer #0, head)
finishKAc-ev-abs : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → absKAc l cl (kac ip) ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► P′
  → BundleKAEvR-abs l cl sv csc css bfc bfs ip e₁ a
      (P′ ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
        ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
        ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip))))))))))))
finishKAc-ev-abs l cl sv csc css bfc bfs ip {e₁ = e₁} cl≢sv sM with decKAc-ev-prod-abs l cl (kac ip) sM
... | kac′ , run , Meq =
      bkacEB kac′
        (cong (λ z → z ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
               ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
               ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip)))))))))))) Meq)
        (⦀-wev-L (decKAc l cl (kac ip)) _
          (noOffer→viewV _
            (kaTail-kas-noOffer l cl sv csc css bfc bfs ip e₁
              (λ q → cl≢sv (trans (sym (absKAc-ev-dir l cl (kac ip) sM)) q))))
          run)

-- fold a KA-server abstract fire into the bundle result (peer #1)
finishKAs-ev-abs : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → absKAs l sv (kas ip) ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► P′
  → BundleKAEvR-abs l cl sv csc css bfc bfs ip e₁ a
      (absKAc l cl (kac ip) ⦀ (P′ ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
        ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
        ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip))))))))))))
finishKAs-ev-abs l cl sv csc css bfc bfs ip {e₁ = e₁} cl≢sv sM with decKAs-ev-prod-abs l sv (kas ip) sM
... | kas′ , run , Meq =
      bkasEB kas′
        (cong (λ z → absKAc l cl (kac ip) ⦀ (z ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
               ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
               ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip)))))))))))) Meq)
        (⦀-wev-R (decKAc l cl (kac ip)) _
          (noOffer→viewV (decKAc l cl (kac ip))
            (decKAc-dir-noOffer l cl (kac ip) e₁ (λ q → cl≢sv (trans (sym q) (absKAs-ev-dir l sv (kas ip) sM)))))
          (⦀-wev-L (decKAs l sv (kas ip)) _
            (noOffer→viewV _ (kaTail-csc-noOffer l cl sv csc css bfc bfs ip e₁))
            run))

-- 12-peer abstract bundle ev-inversion (KA)
absBundleKA-ev-prod : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {Bd′ : NetProc}
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► Bd′
  → BundleKAEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′
absBundleKA-ev-prod l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAc l cl (kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evL _ sM = finishKAc-ev-abs l cl sv csc css bfc bfs ip cl≢sv sM
... | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absKAs l sv (kas ip)) _ (absKAs-dir-noBoth l sv (kas ip) e₁ (λ q → cl≢sv (trans (sym (absKAc-ev-dir l cl (kac ip) sM)) q))) (SStep.⦀-noOffer (absCSc l cl csc) _ (absCSc-noKA l cl csc e₁) (SStep.⦀-noOffer (absCSs l sv css) _ (absCSs-noKA l sv css e₁) (SStep.⦀-noOffer (absBFc l cl bfc) _ (absBFc-noKA l cl bfc e₁) (SStep.⦀-noOffer (absBFs l sv bfs) _ (absBFs-noKA l sv bfs e₁) (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noKA l cl (tsc ip) e₁) (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noKA l sv (tss ip) e₁) (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noKA l cl (lnc ip) e₁) (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noKA l sv (lns ip) e₁) (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noKA l cl (lfc ip) e₁) (absLFs-noKA l sv (lfs ip) e₁))))))))) ) (_ , sTail))
... | PEA.evR _ q1
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAs l sv (kas ip)) _ q1
...   | PEA.evSync () _ _
...   | PEA.evL _ sM = finishKAs-ev-abs l cl sv csc css bfc bfs ip cl≢sv sM
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
-- PART 2d — abstract TS bundle inversion (TS client/server are peers #6/#7).
------------------------------------------------------------------------

-- abstract TS-client firing pins the event's direction to `cl`
absTSc-ev-dir : (l : Link) (cl : Dir) (tscp : TScPos)
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {M : NetProc}
  → absTSc l cl tscp ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► M → tsEvDir e₁ ≡ cl
absTSc-ev-dir l cl tscp {e₁ = e₁} step with tableSpec-ev-inv (Ttsc l cl) (coarsenTSc tscp) step
... | q′ , ceq , _ with tsEvDir e₁ ≟ cl
...   | yes eq  = eq
...   | no  ¬eq = ⊥-elim (nothing-absurd (trans (sym (tsCnxt-dir-no l cl (coarsenTSc tscp) e₁ ¬eq)) ceq))

-- abstract TS-server firing pins the event's direction to `sv`
absTSs-ev-dir : (l : Link) (sv : Dir) (tssp : TSsPos)
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {M : NetProc}
  → absTSs l sv tssp ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► M → tsEvDir e₁ ≡ sv
absTSs-ev-dir l sv tssp {e₁ = e₁} step with tableSpec-ev-inv (Ttss l sv) (coarsenTSs tssp) step
... | q′ , ceq , _ with tsEvDir e₁ ≟ sv
...   | yes eq  = eq
...   | no  ¬eq = ⊥-elim (nothing-absurd (trans (sym (tsSnxt-dir-no l sv (coarsenTSs tssp) e₁ ¬eq)) ceq))

-- which driven TS peer fired + the updated InertPos field + the concrete WEAK run
data BundleTSEvR-abs (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} (e₁ : TS.TSEv X) (a : X) (Bd′ : NetProc) : Set₁ where
  btscEB : (tsc′ : TScPos)
        → Bd′ ≡ absBundleG l cl sv csc css bfc bfs (record ip { tsc = tsc′ })
        → bundleG l cl sv csc css bfc bfs ip
            ═[ ev (evl (evLabel X (ιTS e₁) a)) ]═► bundleG l cl sv csc css bfc bfs (record ip { tsc = tsc′ })
        → BundleTSEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′
  btssEB : (tss′ : TSsPos)
        → Bd′ ≡ absBundleG l cl sv csc css bfc bfs (record ip { tss = tss′ })
        → bundleG l cl sv csc css bfc bfs ip
            ═[ ev (evl (evLabel X (ιTS e₁) a)) ]═► bundleG l cl sv csc css bfc bfs (record ip { tss = tss′ })
        → BundleTSEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′

-- fold a TS-client abstract fire into the bundle result (peer #6)
finishTSc-ev-abs : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → absTSc l cl (tsc ip) ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► P′
  → BundleTSEvR-abs l cl sv csc css bfc bfs ip e₁ a
      (absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
        ⦀ (P′ ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
        ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip))))))))))))
finishTSc-ev-abs l cl sv csc css bfc bfs ip {e₁ = e₁} cl≢sv sM with decTSc-ev-prod-abs l cl (tsc ip) sM
... | tsc′ , run , Meq =
      btscEB tsc′
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
finishTSs-ev-abs : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → absTSs l sv (tss ip) ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► P′
  → BundleTSEvR-abs l cl sv csc css bfc bfs ip e₁ a
      (absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
        ⦀ (absTSc l cl (tsc ip) ⦀ (P′ ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
        ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip))))))))))))
finishTSs-ev-abs l cl sv csc css bfc bfs ip {e₁ = e₁} cl≢sv sM with decTSs-ev-prod-abs l sv (tss ip) sM
... | tss′ , run , Meq =
      btssEB tss′
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
absBundleTS-ev-prod : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {Bd′ : NetProc}
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► Bd′
  → BundleTSEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′
absBundleTS-ev-prod l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
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
...             | PEA.evL _ sM = finishTSc-ev-abs l cl sv csc css bfc bfs ip cl≢sv sM
...             | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-dir-noBoth l sv (tss ip) e₁ (λ q → cl≢sv (trans (sym (absTSc-ev-dir l cl (tsc ip) sM)) q))) (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noTS l cl (lnc ip) e₁) (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noTS l sv (lns ip) e₁) (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noTS l cl (lfc ip) e₁) (absLFs-noTS l sv (lfs ip) e₁)))) (_ , sTail))
...             | PEA.evR _ q7
                with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSs l sv (tss ip)) _ q7
...               | PEA.evSync () _ _
...               | PEA.evL _ sM = finishTSs-ev-abs l cl sv csc css bfc bfs ip cl≢sv sM
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
-- PART 2e — abstract LN bundle inversion (LN client/server are peers #8/#9).
------------------------------------------------------------------------

-- abstract LN-client firing pins the event's direction to `cl`
absLNc-ev-dir : (l : Link) (cl : Dir) (lncp : LNcPos)
    {X : Set 0ℓ} {e₁ : LN.LNEv X} {a : X} {M : NetProc}
  → absLNc l cl lncp ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► M → lnEvDir e₁ ≡ cl
absLNc-ev-dir l cl lncp {e₁ = e₁} step with tableSpec-ev-inv (Tlnc l cl) (coarsenLNc lncp) step
... | q′ , ceq , _ with lnEvDir e₁ ≟ cl
...   | yes eq  = eq
...   | no  ¬eq = ⊥-elim (nothing-absurd (trans (sym (lnCnxt-dir-no l cl (coarsenLNc lncp) e₁ ¬eq)) ceq))

-- abstract LN-server firing pins the event's direction to `sv`
absLNs-ev-dir : (l : Link) (sv : Dir) (lnsp : LNsPos)
    {X : Set 0ℓ} {e₁ : LN.LNEv X} {a : X} {M : NetProc}
  → absLNs l sv lnsp ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► M → lnEvDir e₁ ≡ sv
absLNs-ev-dir l sv lnsp {e₁ = e₁} step with tableSpec-ev-inv (Tlns l sv) (coarsenLNs lnsp) step
... | q′ , ceq , _ with lnEvDir e₁ ≟ sv
...   | yes eq  = eq
...   | no  ¬eq = ⊥-elim (nothing-absurd (trans (sym (lnSnxt-dir-no l sv (coarsenLNs lnsp) e₁ ¬eq)) ceq))

-- which driven LN peer fired + the updated InertPos field + the concrete WEAK run
data BundleLNEvR-abs (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} (e₁ : LN.LNEv X) (a : X) (Bd′ : NetProc) : Set₁ where
  blncEB : (lnc′ : LNcPos)
        → Bd′ ≡ absBundleG l cl sv csc css bfc bfs (record ip { lnc = lnc′ })
        → bundleG l cl sv csc css bfc bfs ip
            ═[ ev (evl (evLabel X (ιLN e₁) a)) ]═► bundleG l cl sv csc css bfc bfs (record ip { lnc = lnc′ })
        → BundleLNEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′
  blnsEB : (lns′ : LNsPos)
        → Bd′ ≡ absBundleG l cl sv csc css bfc bfs (record ip { lns = lns′ })
        → bundleG l cl sv csc css bfc bfs ip
            ═[ ev (evl (evLabel X (ιLN e₁) a)) ]═► bundleG l cl sv csc css bfc bfs (record ip { lns = lns′ })
        → BundleLNEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′

-- fold a LN-client abstract fire into the bundle result (peer #8)
finishLNc-ev-abs : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : LN.LNEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → absLNc l cl (lnc ip) ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► P′
  → BundleLNEvR-abs l cl sv csc css bfc bfs ip e₁ a
      (absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
        ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (P′ ⦀ (absLNs l sv (lns ip)
        ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip))))))))))))
finishLNc-ev-abs l cl sv csc css bfc bfs ip {e₁ = e₁} cl≢sv sM with decLNc-ev-prod-abs l cl (lnc ip) sM
... | lnc′ , run , Meq =
      blncEB lnc′
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
finishLNs-ev-abs : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : LN.LNEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → absLNs l sv (lns ip) ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► P′
  → BundleLNEvR-abs l cl sv csc css bfc bfs ip e₁ a
      (absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
        ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (P′
        ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip))))))))))))
finishLNs-ev-abs l cl sv csc css bfc bfs ip {e₁ = e₁} cl≢sv sM with decLNs-ev-prod-abs l sv (lns ip) sM
... | lns′ , run , Meq =
      blnsEB lns′
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
absBundleLN-ev-prod : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : LN.LNEv X} {a : X} {Bd′ : NetProc}
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► Bd′
  → BundleLNEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′
absBundleLN-ev-prod l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
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
...                 | PEA.evL _ sM = finishLNc-ev-abs l cl sv csc css bfc bfs ip cl≢sv sM
...                 | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-dir-noBoth l sv (lns ip) e₁ (λ q → cl≢sv (trans (sym (absLNc-ev-dir l cl (lnc ip) sM)) q))) (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noLN l cl (lfc ip) e₁) (absLFs-noLN l sv (lfs ip) e₁)) (_ , sTail))
...                 | PEA.evR _ q9
                    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNs l sv (lns ip)) _ q9
...                   | PEA.evSync () _ _
...                   | PEA.evL _ sM = finishLNs-ev-abs l cl sv csc css bfc bfs ip cl≢sv sM
...                   | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noLN l cl (lfc ip) e₁) (absLFs-noLN l sv (lfs ip) e₁) (_ , sTail))
...                   | PEA.evR _ q10
                      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) q10
...                     | PEA.evSync () _ _
...                     | PEA.evL _ sM = ⊥-elim (absLFc-noLN l cl (lfc ip) e₁ (_ , sM))
...                     | PEA.evBoth _ sM _ = ⊥-elim (absLFc-noLN l cl (lfc ip) e₁ (_ , sM))
...                     | PEA.evR _ qs = ⊥-elim (absLFs-noLN l sv (lfs ip) e₁ (_ , qs))

------------------------------------------------------------------------
-- PART 2f — abstract LF bundle inversion (LF client/server are peers #10/#11).
------------------------------------------------------------------------

-- abstract LF-client firing pins the event's direction to `cl`
absLFc-ev-dir : (l : Link) (cl : Dir) (lfcp : LFcPos)
    {X : Set 0ℓ} {e₁ : LF.LFEv X} {a : X} {M : NetProc}
  → absLFc l cl lfcp ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► M → lfEvDir e₁ ≡ cl
absLFc-ev-dir l cl lfcp {e₁ = e₁} step with tableSpec-ev-inv (Tlfc l cl) (coarsenLFc lfcp) step
... | q′ , ceq , _ with lfEvDir e₁ ≟ cl
...   | yes eq  = eq
...   | no  ¬eq = ⊥-elim (nothing-absurd (trans (sym (lfCnxt-dir-no l cl (coarsenLFc lfcp) e₁ ¬eq)) ceq))

-- abstract LF-server firing pins the event's direction to `sv`
absLFs-ev-dir : (l : Link) (sv : Dir) (lfsp : LFsPos)
    {X : Set 0ℓ} {e₁ : LF.LFEv X} {a : X} {M : NetProc}
  → absLFs l sv lfsp ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► M → lfEvDir e₁ ≡ sv
absLFs-ev-dir l sv lfsp {e₁ = e₁} step with tableSpec-ev-inv (Tlfs l sv) (coarsenLFs lfsp) step
... | q′ , ceq , _ with lfEvDir e₁ ≟ sv
...   | yes eq  = eq
...   | no  ¬eq = ⊥-elim (nothing-absurd (trans (sym (lfSnxt-dir-no l sv (coarsenLFs lfsp) e₁ ¬eq)) ceq))

-- which driven LF peer fired + the updated InertPos field + the concrete WEAK run
data BundleLFEvR-abs (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} (e₁ : LF.LFEv X) (a : X) (Bd′ : NetProc) : Set₁ where
  blfcEB : (lfc′ : LFcPos)
        → Bd′ ≡ absBundleG l cl sv csc css bfc bfs (record ip { lfc = lfc′ })
        → bundleG l cl sv csc css bfc bfs ip
            ═[ ev (evl (evLabel X (ιLF e₁) a)) ]═► bundleG l cl sv csc css bfc bfs (record ip { lfc = lfc′ })
        → BundleLFEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′
  blfsEB : (lfs′ : LFsPos)
        → Bd′ ≡ absBundleG l cl sv csc css bfc bfs (record ip { lfs = lfs′ })
        → bundleG l cl sv csc css bfc bfs ip
            ═[ ev (evl (evLabel X (ιLF e₁) a)) ]═► bundleG l cl sv csc css bfc bfs (record ip { lfs = lfs′ })
        → BundleLFEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′

-- fold a LF-client abstract fire into the bundle result (peer #10)
finishLFc-ev-abs : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : LF.LFEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → absLFc l cl (lfc ip) ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► P′
  → BundleLFEvR-abs l cl sv csc css bfc bfs ip e₁ a
      (absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
        ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
        ⦀ (P′ ⦀ absLFs l sv (lfs ip))))))))))))
finishLFc-ev-abs l cl sv csc css bfc bfs ip {e₁ = e₁} cl≢sv sM with decLFc-ev-prod-abs l cl (lfc ip) sM
... | lfc′ , run , Meq =
      blfcEB lfc′
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
finishLFs-ev-abs : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : LF.LFEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → absLFs l sv (lfs ip) ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► P′
  → BundleLFEvR-abs l cl sv csc css bfc bfs ip e₁ a
      (absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
        ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
        ⦀ (absLFc l cl (lfc ip) ⦀ P′)))))))))))
finishLFs-ev-abs l cl sv csc css bfc bfs ip {e₁ = e₁} cl≢sv sM with decLFs-ev-prod-abs l sv (lfs ip) sM
... | lfs′ , run , Meq =
      blfsEB lfs′
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
absBundleLF-ev-prod : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : LF.LFEv X} {a : X} {Bd′ : NetProc}
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► Bd′
  → BundleLFEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′
absBundleLF-ev-prod l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
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
...                     | PEA.evL _ sM = finishLFc-ev-abs l cl sv csc css bfc bfs ip cl≢sv sM
...                     | PEA.evBoth _ sM sTail = ⊥-elim (absLFs-dir-noBoth l sv (lfs ip) e₁ (λ q → cl≢sv (trans (sym (absLFc-ev-dir l cl (lfc ip) sM)) q)) (_ , sTail))
...                     | PEA.evR _ qs = finishLFs-ev-abs l cl sv csc css bfc bfs ip cl≢sv qs

------------------------------------------------------------------------
-- PART 2g — UNIFIED abstract bundle io inversion dispatcher.
-- Given the whole 12-peer abstract bundle firing a raw io event `e`, decide
-- the channel (mirror `absBundleG-io-role`'s dispatch on `e`) and invoke the
-- committed per-channel `absBundleX-ev-prod`, repackaging its two-constructor
-- result into a SINGLE `BundleGEvR-abs` carrying the full updated bundle args
-- + the concrete WEAK run.  The node peels then lift THIS run up the node `⦀`.
------------------------------------------------------------------------

-- unified abstract bundle ev-inversion result: full bundle-arg update + weak run
data BundleGEvR-abs (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) (Bd′ : NetProc) : Set₁ where
  bgEB : (csc′ : CScPos) (css′ : CSsPos) (bfc′ : BFcPos) (bfs′ : BFsPos) (ip′ : InertPos)
       → Bd′ ≡ absBundleG l cl sv csc′ css′ bfc′ bfs′ ip′
       → bundleG l cl sv csc css bfc bfs ip
           ═[ ev (evl (evLabel X e a)) ]═► bundleG l cl sv csc′ css′ bfc′ bfs′ ip′
       → BundleGEvR-abs l cl sv csc css bfc bfs ip e a Bd′

-- six per-channel lifters into the unified result (eq pins all five updated args)
csEvR→g : {l : Link} {cl sv : Dir} {csc : CScPos} {css : CSsPos} {bfc : BFcPos} {bfs : BFsPos} {ip : InertPos}
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {Bd′ : NetProc}
  → BundleCSEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′
  → BundleGEvR-abs l cl sv csc css bfc bfs ip (ιCS e₁) a Bd′
csEvR→g {csc = csc} {css} {bfc} {bfs} {ip} (bcscEB csc′ eq run) = bgEB csc′ css  bfc bfs ip eq run
csEvR→g {csc = csc} {css} {bfc} {bfs} {ip} (bcssEB css′ eq run) = bgEB csc  css′ bfc bfs ip eq run

bfEvR→g : {l : Link} {cl sv : Dir} {csc : CScPos} {css : CSsPos} {bfc : BFcPos} {bfs : BFsPos} {ip : InertPos}
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {Bd′ : NetProc}
  → BundleBFEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′
  → BundleGEvR-abs l cl sv csc css bfc bfs ip (ιBF e₁) a Bd′
bfEvR→g {csc = csc} {css} {bfc} {bfs} {ip} (bcbcEB bfc′ eq run) = bgEB csc css bfc′ bfs  ip eq run
bfEvR→g {csc = csc} {css} {bfc} {bfs} {ip} (bcbsEB bfs′ eq run) = bgEB csc css bfc  bfs′ ip eq run

kaEvR→g : {l : Link} {cl sv : Dir} {csc : CScPos} {css : CSsPos} {bfc : BFcPos} {bfs : BFsPos} {ip : InertPos}
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {Bd′ : NetProc}
  → BundleKAEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′
  → BundleGEvR-abs l cl sv csc css bfc bfs ip (ιKA e₁) a Bd′
kaEvR→g {csc = csc} {css} {bfc} {bfs} {ip} (bkacEB kac′ eq run) = bgEB csc css bfc bfs (record ip { kac = kac′ }) eq run
kaEvR→g {csc = csc} {css} {bfc} {bfs} {ip} (bkasEB kas′ eq run) = bgEB csc css bfc bfs (record ip { kas = kas′ }) eq run

tsEvR→g : {l : Link} {cl sv : Dir} {csc : CScPos} {css : CSsPos} {bfc : BFcPos} {bfs : BFsPos} {ip : InertPos}
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {Bd′ : NetProc}
  → BundleTSEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′
  → BundleGEvR-abs l cl sv csc css bfc bfs ip (ιTS e₁) a Bd′
tsEvR→g {csc = csc} {css} {bfc} {bfs} {ip} (btscEB tsc′ eq run) = bgEB csc css bfc bfs (record ip { tsc = tsc′ }) eq run
tsEvR→g {csc = csc} {css} {bfc} {bfs} {ip} (btssEB tss′ eq run) = bgEB csc css bfc bfs (record ip { tss = tss′ }) eq run

lnEvR→g : {l : Link} {cl sv : Dir} {csc : CScPos} {css : CSsPos} {bfc : BFcPos} {bfs : BFsPos} {ip : InertPos}
    {X : Set 0ℓ} {e₁ : LN.LNEv X} {a : X} {Bd′ : NetProc}
  → BundleLNEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′
  → BundleGEvR-abs l cl sv csc css bfc bfs ip (ιLN e₁) a Bd′
lnEvR→g {csc = csc} {css} {bfc} {bfs} {ip} (blncEB lnc′ eq run) = bgEB csc css bfc bfs (record ip { lnc = lnc′ }) eq run
lnEvR→g {csc = csc} {css} {bfc} {bfs} {ip} (blnsEB lns′ eq run) = bgEB csc css bfc bfs (record ip { lns = lns′ }) eq run

lfEvR→g : {l : Link} {cl sv : Dir} {csc : CScPos} {css : CSsPos} {bfc : BFcPos} {bfs : BFsPos} {ip : InertPos}
    {X : Set 0ℓ} {e₁ : LF.LFEv X} {a : X} {Bd′ : NetProc}
  → BundleLFEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′
  → BundleGEvR-abs l cl sv csc css bfc bfs ip (ιLF e₁) a Bd′
lfEvR→g {csc = csc} {css} {bfc} {bfs} {ip} (blfcEB lfc′ eq run) = bgEB csc css bfc bfs (record ip { lfc = lfc′ }) eq run
lfEvR→g {csc = csc} {css} {bfc} {bfs} {ip} (blfsEB lfs′ eq run) = bgEB csc css bfc bfs (record ip { lfs = lfs′ }) eq run

-- the unified io dispatcher: case on the raw io event `e`, invoke the channel's
-- committed `absBundleX-ev-prod`, lift into the unified result
absBundleG-io-prod : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → BundleGEvR-abs l cl sv csc css bfc bfs ip e a Bd′
absBundleG-io-prod l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_ChainSync}    iomem step = csEvR→g (absBundleCS-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = CS.sendCS    l′ d′} step)
absBundleG-io-prod l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_ChainSync}    iomem step = csEvR→g (absBundleCS-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = CS.receiveCS l′ d′} step)
absBundleG-io-prod l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_BlockFetch}   iomem step = bfEvR→g (absBundleBF-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = BF.sendBF    l′ d′} step)
absBundleG-io-prod l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_BlockFetch}   iomem step = bfEvR→g (absBundleBF-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = BF.receiveBF l′ d′} step)
absBundleG-io-prod l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_KeepAlive}    iomem step = kaEvR→g (absBundleKA-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = KA.sendKA    l′ d′} step)
absBundleG-io-prod l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_KeepAlive}    iomem step = kaEvR→g (absBundleKA-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = KA.receiveKA l′ d′} step)
absBundleG-io-prod l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_TxSubmission} iomem step = tsEvR→g (absBundleTS-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = TS.sendTS    l′ d′} step)
absBundleG-io-prod l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_TxSubmission} iomem step = tsEvR→g (absBundleTS-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = TS.receiveTS l′ d′} step)
absBundleG-io-prod l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_LeiosNotify}  iomem step = lnEvR→g (absBundleLN-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = LN.sendLN    l′ d′} step)
absBundleG-io-prod l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_LeiosNotify}  iomem step = lnEvR→g (absBundleLN-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = LN.receiveLN l′ d′} step)
absBundleG-io-prod l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_LeiosFetch}   iomem step = lfEvR→g (absBundleLF-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = LF.sendLF    l′ d′} step)
absBundleG-io-prod l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_LeiosFetch}   iomem step = lfEvR→g (absBundleLF-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = LF.receiveLF l′ d′} step)
absBundleG-io-prod l cl sv cl≢sv csc css bfc bfs ip {e = done   _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-prod l cl sv cl≢sv csc css bfc bfs ip {e = apiCS  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-prod l cl sv cl≢sv csc css bfc bfs ip {e = apiBF  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-prod l cl sv cl≢sv csc css bfc bfs ip {e = apiKA  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-prod l cl sv cl≢sv csc css bfc bfs ip {e = apiTS  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-prod l cl sv cl≢sv csc css bfc bfs ip {e = apiLN  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-prod l cl sv cl≢sv csc css bfc bfs ip {e = apiLF  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-prod l cl sv cl≢sv csc css bfc bfs ip {e = sndmsg _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-prod l cl sv cl≢sv csc css bfc bfs ip {e = rcvmsg _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-prod l cl sv cl≢sv csc css bfc bfs ip {e = tx     _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-prod l cl sv cl≢sv csc css bfc bfs ip {e = sndack _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-prod l cl sv cl≢sv csc css bfc bfs ip {e = rcvack _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-prod l cl sv cl≢sv csc css bfc bfs ip {e = ack    _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-prod l cl sv cl≢sv csc css bfc bfs ip {e = break  _}     iomem step = ⊥-elim iomem

------------------------------------------------------------------------
-- PART 2h — CONCRETE `bundleG-io-no` (the ⦀-wev-L / ⦀-wev-R sibling non-offer).
--
-- The concrete node peels lift a firing peer's weak run up the node's two-link
-- `⦀`; the strong `⦀-ev-L/R` congruence (via `⦀-wev-*`) demands the idle
-- sibling bundle offers NOTHING on the fired io event.  For a wrong-link io
-- (link ≢ the sibling bundle's own link `l`) this is the CONCRETE analog of the
-- abstract `absBundleG-io-no` (SysIoLink.2052): dispatch on the raw io event `e`
-- and use the committed per-channel link pin `bundleX-io-link-{in,out}` (each
-- says a bundle io step at a X-channel event pins the io's link to `l`), so an
-- io whose own link `l₀ ≢ l` cannot be offered.  Api / non-io events are refuted
-- by `iomem : ioES .mem …`.
------------------------------------------------------------------------

-- the whole concrete idle bundle at `l` offers nothing on a wrong-link io event
bundleG-io-no : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {l₀ : Link}
  → ApiHasLink l₀ e → l₀ ≢ l → ioES .mem (X , e) a
  → ¬ IoOffers (bundleG l cl sv csc css bfc bfs ip) e a
bundleG-io-no l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_ChainSync}    ahlIn  l₀≢l iomem (_ , step) = l₀≢l (sym (bundleCS-io-link-in  l cl sv cl≢sv csc css bfc bfs ip step))
bundleG-io-no l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_ChainSync}    ahlOut l₀≢l iomem (_ , step) = l₀≢l (sym (bundleCS-io-link-out l cl sv cl≢sv csc css bfc bfs ip step))
bundleG-io-no l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_BlockFetch}   ahlIn  l₀≢l iomem (_ , step) = l₀≢l (sym (bundleBF-io-link-in  l cl sv cl≢sv csc css bfc bfs ip step))
bundleG-io-no l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_BlockFetch}   ahlOut l₀≢l iomem (_ , step) = l₀≢l (sym (bundleBF-io-link-out l cl sv cl≢sv csc css bfc bfs ip step))
bundleG-io-no l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_KeepAlive}    ahlIn  l₀≢l iomem (_ , step) = l₀≢l (sym (bundleKA-io-link-in  l cl sv cl≢sv csc css bfc bfs ip step))
bundleG-io-no l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_KeepAlive}    ahlOut l₀≢l iomem (_ , step) = l₀≢l (sym (bundleKA-io-link-out l cl sv cl≢sv csc css bfc bfs ip step))
bundleG-io-no l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_TxSubmission} ahlIn  l₀≢l iomem (_ , step) = l₀≢l (sym (bundleTS-io-link-in  l cl sv cl≢sv csc css bfc bfs ip step))
bundleG-io-no l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_TxSubmission} ahlOut l₀≢l iomem (_ , step) = l₀≢l (sym (bundleTS-io-link-out l cl sv cl≢sv csc css bfc bfs ip step))
bundleG-io-no l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_LeiosNotify}  ahlIn  l₀≢l iomem (_ , step) = l₀≢l (sym (bundleLN-io-link-in  l cl sv cl≢sv csc css bfc bfs ip step))
bundleG-io-no l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_LeiosNotify}  ahlOut l₀≢l iomem (_ , step) = l₀≢l (sym (bundleLN-io-link-out l cl sv cl≢sv csc css bfc bfs ip step))
bundleG-io-no l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_LeiosFetch}   ahlIn  l₀≢l iomem (_ , step) = l₀≢l (sym (bundleLF-io-link-in  l cl sv cl≢sv csc css bfc bfs ip step))
bundleG-io-no l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_LeiosFetch}   ahlOut l₀≢l iomem (_ , step) = l₀≢l (sym (bundleLF-io-link-out l cl sv cl≢sv csc css bfc bfs ip step))
bundleG-io-no l cl sv cl≢sv csc css bfc bfs ip {e = done   _ _ _} _ _ ()
bundleG-io-no l cl sv cl≢sv csc css bfc bfs ip {e = apiCS  _ _ _} _ _ ()
bundleG-io-no l cl sv cl≢sv csc css bfc bfs ip {e = apiBF  _ _ _} _ _ ()
bundleG-io-no l cl sv cl≢sv csc css bfc bfs ip {e = apiKA  _ _ _} _ _ ()
bundleG-io-no l cl sv cl≢sv csc css bfc bfs ip {e = apiTS  _ _ _} _ _ ()
bundleG-io-no l cl sv cl≢sv csc css bfc bfs ip {e = apiLN  _ _ _} _ _ ()
bundleG-io-no l cl sv cl≢sv csc css bfc bfs ip {e = apiLF  _ _ _} _ _ ()
bundleG-io-no l cl sv cl≢sv csc css bfc bfs ip {e = sndmsg _ _ _} _ _ ()
bundleG-io-no l cl sv cl≢sv csc css bfc bfs ip {e = rcvmsg _ _ _} _ _ ()
bundleG-io-no l cl sv cl≢sv csc css bfc bfs ip {e = tx     _ _ _} _ _ ()
bundleG-io-no l cl sv cl≢sv csc css bfc bfs ip {e = sndack _ _ _} _ _ ()
bundleG-io-no l cl sv cl≢sv csc css bfc bfs ip {e = rcvack _ _ _} _ _ ()
bundleG-io-no l cl sv cl≢sv csc css bfc bfs ip {e = ack    _ _ _} _ _ ()
bundleG-io-no l cl sv cl≢sv csc css bfc bfs ip {e = break  _}     _ _ ()

------------------------------------------------------------------------
-- PART 2i — UNIFIED abstract bundle API inversion dispatcher.
--
-- The api node peels sync the SHARED driver (`decProd`/`decCons…`) with the
-- firing bundle peer over `apiES` via `∥⇘⇙-wev-sync`; the bundle's side of that
-- sync is THIS dispatcher.  `apiES` covers the six `apiX` api events AND the six
-- `done` teardown events (`apiSet done = ⊤`, FourNodeDiamond); each is
-- `ιX (apiXev …)` / `ιX (doneX …)`, so the dispatch invokes the channel's
-- committed `absBundleX-ev-prod` exactly as the io dispatcher does, repackaging
-- via the same `xEvR→g` lifters.  Non-api / non-done events are refuted by the
-- membership witness `apimem : apiES .mem …`.
------------------------------------------------------------------------

-- wrap a strong driver fire as a (padding-free) weak run for `∥⇘⇙-wev-sync`
ev→wev : {P P′ : NetProc} {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
       → P ─[ ev (evl (evLabel X e a)) ]─► P′
       → P ═[ ev (evl (evLabel X e a)) ]═► P′
ev→wev fire = wev τ*-refl fire τ*-refl

-- the unified api dispatcher: case on the raw api/done event `e`, invoke the
-- channel's committed `absBundleX-ev-prod`, lift into the unified result
absBundleG-api-prod : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → apiES .mem (X , e) a
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → BundleGEvR-abs l cl sv csc css bfc bfs ip e a Bd′
absBundleG-api-prod l cl sv cl≢sv csc css bfc bfs ip {e = apiCS l′ d′ m} apimem step = csEvR→g (absBundleCS-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = CS.apiCSev l′ d′ m} step)
absBundleG-api-prod l cl sv cl≢sv csc css bfc bfs ip {e = apiBF l′ d′ m} apimem step = bfEvR→g (absBundleBF-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = BF.apiBFev l′ d′ m} step)
absBundleG-api-prod l cl sv cl≢sv csc css bfc bfs ip {e = apiKA l′ d′ m} apimem step = kaEvR→g (absBundleKA-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = KA.apiKAev l′ d′ m} step)
absBundleG-api-prod l cl sv cl≢sv csc css bfc bfs ip {e = apiTS l′ d′ m} apimem step = tsEvR→g (absBundleTS-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = TS.apiTSev l′ d′ m} step)
absBundleG-api-prod l cl sv cl≢sv csc css bfc bfs ip {e = apiLN l′ d′ m} apimem step = lnEvR→g (absBundleLN-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = LN.apiLNev l′ d′ m} step)
absBundleG-api-prod l cl sv cl≢sv csc css bfc bfs ip {e = apiLF l′ d′ m} apimem step = lfEvR→g (absBundleLF-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = LF.apiLFev l′ d′ m} step)
absBundleG-api-prod l cl sv cl≢sv csc css bfc bfs ip {e = done l′ d′ N2N_ChainSync}    apimem step = csEvR→g (absBundleCS-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = CS.doneCS l′ d′} step)
absBundleG-api-prod l cl sv cl≢sv csc css bfc bfs ip {e = done l′ d′ N2N_BlockFetch}   apimem step = bfEvR→g (absBundleBF-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = BF.doneBF l′ d′} step)
absBundleG-api-prod l cl sv cl≢sv csc css bfc bfs ip {e = done l′ d′ N2N_KeepAlive}    apimem step = kaEvR→g (absBundleKA-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = KA.doneKA l′ d′} step)
absBundleG-api-prod l cl sv cl≢sv csc css bfc bfs ip {e = done l′ d′ N2N_TxSubmission} apimem step = tsEvR→g (absBundleTS-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = TS.doneTS l′ d′} step)
absBundleG-api-prod l cl sv cl≢sv csc css bfc bfs ip {e = done l′ d′ N2N_LeiosNotify}  apimem step = lnEvR→g (absBundleLN-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = LN.doneLN l′ d′} step)
absBundleG-api-prod l cl sv cl≢sv csc css bfc bfs ip {e = done l′ d′ N2N_LeiosFetch}   apimem step = lfEvR→g (absBundleLF-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = LF.doneLF l′ d′} step)
absBundleG-api-prod l cl sv cl≢sv csc css bfc bfs ip {e = input  _ _ _} apimem step = ⊥-elim apimem
absBundleG-api-prod l cl sv cl≢sv csc css bfc bfs ip {e = output _ _ _} apimem step = ⊥-elim apimem
absBundleG-api-prod l cl sv cl≢sv csc css bfc bfs ip {e = sndmsg _ _ _} apimem step = ⊥-elim apimem
absBundleG-api-prod l cl sv cl≢sv csc css bfc bfs ip {e = rcvmsg _ _ _} apimem step = ⊥-elim apimem
absBundleG-api-prod l cl sv cl≢sv csc css bfc bfs ip {e = tx     _ _ _} apimem step = ⊥-elim apimem
absBundleG-api-prod l cl sv cl≢sv csc css bfc bfs ip {e = sndack _ _ _} apimem step = ⊥-elim apimem
absBundleG-api-prod l cl sv cl≢sv csc css bfc bfs ip {e = rcvack _ _ _} apimem step = ⊥-elim apimem
absBundleG-api-prod l cl sv cl≢sv csc css bfc bfs ip {e = ack    _ _ _} apimem step = ⊥-elim apimem
absBundleG-api-prod l cl sv cl≢sv csc css bfc bfs ip {e = break  _}     apimem step = ⊥-elim apimem

------------------------------------------------------------------------
-- PART 2j — abstract-primary node io peels `nodeX-ev-io-abs`.
--
-- The DUAL of the concrete `nodeX-ev-io`: given `absNodeX na ─[io]─► M`, peel
-- the solo bundle fire (io ∉ apiES ⇒ no driver sync; driver is api-only ⇒ the
-- `∥⇘apiES⇙` peel lands on the bundle `⦀`; the two-link `evBoth` is refuted by
-- distinct links via `absBundleG-io-ahl`), invoke `absBundleG-io-prod` for the
-- firing bundle's CONCRETE weak run, then lift that run up the node `⦀` /
-- `∥⇘apiES⇙ driver` with the PART-1 weak congruences (`⦀-wev-L/R`,
-- `∥⇘⇙-wev-soloL`; idle sibling via the concrete `bundleG-io-no`, idle driver
-- via the SHARED `nodeX-drv-io-no`).  Output a concrete NODE weak run
-- `decNodeX na ═[io]═► decNodeX na′` plus `M ≡ absNodeX na′`.
------------------------------------------------------------------------

-- node-A abstract-primary io result: concrete successor + weak run + abstract eq
data NodeAEvR-abs (na : SN.NodeStateA) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                  (M : NetProc) : Set₁ where
  naEBa : (na′ : SN.NodeStateA) → M ≡ absNodeA na′
        → SN.decNodeA na ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeA na′
        → NodeAEvR-abs na e a M

-- firing link = linkAB: invert the AB bundle io, rebuild `na′`, lift concrete run
nodeA-io-AB-abs : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeAEvR-abs na e a ((Bd′ ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)))
nodeA-io-AB-abs na {X} {e} {a} iomem sBAB
  with absBundleG-io-prod linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) iomem sBAB
... | bgEB csc′ css′ bfc′ bfs′ ip′ eq run =
      naEBa (SN.mkNodeA csc′ css′ bfc′ bfs′ (SN.NodeStateA.prod-AB na) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) ip′ (SN.NodeStateA.inert-AC na))
        (cong (λ z → (z ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na))) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeA-drv-io-no na iomem))
           (⦀-wev-L _ _
              (noOffer→viewV _ (bundleG-io-no linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)
                 (absBundleG-io-ahl linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) iomem sBAB) linkAB≢linkAC iomem))
              run))

-- firing link = linkAC (mirror via ⦀-wev-R)
nodeA-io-AC-abs : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeAEvR-abs na e a ((absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ⦀ Bd′) ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)))
nodeA-io-AC-abs na {X} {e} {a} iomem sBAC
  with absBundleG-io-prod linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) iomem sBAC
... | bgEB csc′ css′ bfc′ bfs′ ip′ eq run =
      naEBa (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na) csc′ css′ bfc′ bfs′ (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) ip′)
        (cong (λ z → (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ⦀ z) ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na))) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeA-drv-io-no na iomem))
           (⦀-wev-R _ _
              (noOffer→viewV _ (bundleG-io-no linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
                 (absBundleG-io-ahl linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) iomem sBAC) (λ q → linkAB≢linkAC (sym q)) iomem))
              run))

-- node-A io inversion: reflect the io as a bundle solo (driver idle), peel to the
-- firing link (`evBoth` refuted by distinct links), dispatch to `nodeA-io-{AB,AC}-abs`
nodeA-ev-io-abs : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodeA na ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeAEvR-abs na e a M
nodeA-ev-io-abs na {X} {e} {a} iomem step
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
...   | PEA.evL _ sBAB = nodeA-io-AB-abs na iomem sBAB
...   | PEA.evR _ sBAC = nodeA-io-AC-abs na iomem sBAC

------------------------------------------------------------------------
-- node-B abstract-primary io peel (relay: single `decCP` driver)
------------------------------------------------------------------------
data NodeBEvR-abs (nb : SN.NodeStateB) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                  (M : NetProc) : Set₁ where
  nbEBa : (nb′ : SN.NodeStateB) → M ≡ absNodeB nb′
        → SN.decNodeB nb ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeB nb′
        → NodeBEvR-abs nb e a M

nodeB-io-AB-abs : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeBEvR-abs nb e a ((Bd′ ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
nodeB-io-AB-abs nb {X} {e} {a} iomem sBAB
  with absBundleG-io-prod linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) iomem sBAB
... | bgEB csc′ css′ bfc′ bfs′ ip′ eq run =
      nbEBa (SN.mkNodeB csc′ css′ bfc′ bfs′ (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) ip′ (SN.NodeStateB.inert-BD nb))
        (cong (λ z → (z ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb)) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeB-drv-io-no nb iomem))
           (⦀-wev-L _ _
              (noOffer→viewV _ (bundleG-io-no linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)
                 (absBundleG-io-ahl linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) iomem sBAB) linkAB≢linkBD iomem))
              run))

nodeB-io-BD-abs : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeBEvR-abs nb e a ((absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ⦀ Bd′) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
nodeB-io-BD-abs nb {X} {e} {a} iomem sBBD
  with absBundleG-io-prod linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) iomem sBBD
... | bgEB csc′ css′ bfc′ bfs′ ip′ eq run =
      nbEBa (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) csc′ css′ bfc′ bfs′ (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) ip′)
        (cong (λ z → (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ⦀ z) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb)) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeB-drv-io-no nb iomem))
           (⦀-wev-R _ _
              (noOffer→viewV _ (bundleG-io-no linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
                 (absBundleG-io-ahl linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) iomem sBBD) (λ q → linkAB≢linkBD (sym q)) iomem))
              run))

nodeB-ev-io-abs : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodeB nb ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeBEvR-abs nb e a M
nodeB-ev-io-abs nb {X} {e} {a} iomem step
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
...   | PEA.evL _ sBAB = nodeB-io-AB-abs nb iomem sBAB
...   | PEA.evR _ sBBD = nodeB-io-BD-abs nb iomem sBBD

------------------------------------------------------------------------
-- node-C abstract-primary io peel (relay: single `decCP` driver)
------------------------------------------------------------------------
data NodeCEvR-abs (nc : SN.NodeStateC) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                  (M : NetProc) : Set₁ where
  ncEBa : (nc′ : SN.NodeStateC) → M ≡ absNodeC nc′
        → SN.decNodeC nc ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeC nc′
        → NodeCEvR-abs nc e a M

nodeC-io-AC-abs : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeCEvR-abs nc e a ((Bd′ ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
nodeC-io-AC-abs nc {X} {e} {a} iomem sBAC
  with absBundleG-io-prod linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) iomem sBAC
... | bgEB csc′ css′ bfc′ bfs′ ip′ eq run =
      ncEBa (SN.mkNodeC csc′ css′ bfc′ bfs′ (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) ip′ (SN.NodeStateC.inert-CD nc))
        (cong (λ z → (z ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc)) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeC-drv-io-no nc iomem))
           (⦀-wev-L _ _
              (noOffer→viewV _ (bundleG-io-no linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)
                 (absBundleG-io-ahl linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) iomem sBAC) linkAC≢linkCD iomem))
              run))

nodeC-io-CD-abs : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeCEvR-abs nc e a ((absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ⦀ Bd′) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
nodeC-io-CD-abs nc {X} {e} {a} iomem sBCD
  with absBundleG-io-prod linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) iomem sBCD
... | bgEB csc′ css′ bfc′ bfs′ ip′ eq run =
      ncEBa (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) csc′ css′ bfc′ bfs′ (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) ip′)
        (cong (λ z → (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ⦀ z) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc)) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeC-drv-io-no nc iomem))
           (⦀-wev-R _ _
              (noOffer→viewV _ (bundleG-io-no linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
                 (absBundleG-io-ahl linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) iomem sBCD) (λ q → linkAC≢linkCD (sym q)) iomem))
              run))

nodeC-ev-io-abs : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodeC nc ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeCEvR-abs nc e a M
nodeC-ev-io-abs nc {X} {e} {a} iomem step
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
...   | PEA.evL _ sBAC = nodeC-io-AC-abs nc iomem sBAC
...   | PEA.evR _ sBCD = nodeC-io-CD-abs nc iomem sBCD

------------------------------------------------------------------------
-- node-D abstract-primary io peel (sink: two `decConsD` drivers)
------------------------------------------------------------------------
data NodeDEvR-abs (nd : SN.NodeStateD) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                  (M : NetProc) : Set₁ where
  ndEBa : (nd′ : SN.NodeStateD) → M ≡ absNodeD nd′
        → SN.decNodeD nd ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeD nd′
        → NodeDEvR-abs nd e a M

nodeD-io-BD-abs : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeDEvR-abs nd e a ((Bd′ ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)))
nodeD-io-BD-abs nd {X} {e} {a} iomem sBBD
  with absBundleG-io-prod linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) iomem sBBD
... | bgEB csc′ css′ bfc′ bfs′ ip′ eq run =
      ndEBa (SN.mkNodeD csc′ css′ bfc′ bfs′ (SN.NodeStateD.cons-BD nd) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) ip′ (SN.NodeStateD.inert-CD nd))
        (cong (λ z → (z ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeD-drv-io-no nd iomem))
           (⦀-wev-L _ _
              (noOffer→viewV _ (bundleG-io-no linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)
                 (absBundleG-io-ahl linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) iomem sBBD) linkBD≢linkCD iomem))
              run))

nodeD-io-CD-abs : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeDEvR-abs nd e a ((absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ⦀ Bd′) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)))
nodeD-io-CD-abs nd {X} {e} {a} iomem sBCD
  with absBundleG-io-prod linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) iomem sBCD
... | bgEB csc′ css′ bfc′ bfs′ ip′ eq run =
      ndEBa (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd) csc′ css′ bfc′ bfs′ (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) ip′)
        (cong (λ z → (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ⦀ z) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeD-drv-io-no nd iomem))
           (⦀-wev-R _ _
              (noOffer→viewV _ (bundleG-io-no linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
                 (absBundleG-io-ahl linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) iomem sBCD) (λ q → linkBD≢linkCD (sym q)) iomem))
              run))

nodeD-ev-io-abs : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodeD nd ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeDEvR-abs nd e a M
nodeD-ev-io-abs nd {X} {e} {a} iomem step
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
...   | PEA.evL _ sBBD = nodeD-io-BD-abs nd iomem sBBD
...   | PEA.evR _ sBCD = nodeD-io-CD-abs nd iomem sBCD

------------------------------------------------------------------------
-- PART 2k — CONCRETE `bundleG-api-no` (api/done analog of `bundleG-io-no`).
--
-- The sibling non-offer used to lift a firing peer's api weak run up the node's
-- two-link bundle `⦀` via `⦀-wev-L/R`: a bundle at link `l` offers NOTHING on an
-- api/done event whose OWN link `l₀ ≢ l`.  Dispatch on the raw api/done event and
-- use the committed per-channel link pin `bundleX-ev-link` (a bundleG step at an
-- X-image event pins the event's link to the bundle's own `l`), so an event with
-- `l₀ ≢ l` cannot be offered.  Non-api events are refuted by `apimem`.
------------------------------------------------------------------------

-- the whole concrete idle bundle at `l` offers nothing on a wrong-link api/done event
bundleG-api-no : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {l₀ : Link}
  → ApiHasLink l₀ e → l₀ ≢ l → apiES .mem (X , e) a
  → ¬ IoOffers (bundleG l cl sv csc css bfc bfs ip) e a
bundleG-api-no l cl sv cl≢sv csc css bfc bfs ip {e = apiCS l′ d′ m} ahlCS   l₀≢l apimem (_ , step) = l₀≢l (apiLink-inj ahlCS   (bundleCS-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = CS.apiCSev l′ d′ m} step))
bundleG-api-no l cl sv cl≢sv csc css bfc bfs ip {e = apiBF l′ d′ m} ahlBF   l₀≢l apimem (_ , step) = l₀≢l (apiLink-inj ahlBF   (bundleBF-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = BF.apiBFev l′ d′ m} step))
bundleG-api-no l cl sv cl≢sv csc css bfc bfs ip {e = apiKA l′ d′ m} ahlKA   l₀≢l apimem (_ , step) = l₀≢l (apiLink-inj ahlKA   (bundleKA-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = KA.apiKAev l′ d′ m} step))
bundleG-api-no l cl sv cl≢sv csc css bfc bfs ip {e = apiTS l′ d′ m} ahlTS   l₀≢l apimem (_ , step) = l₀≢l (apiLink-inj ahlTS   (bundleTS-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = TS.apiTSev l′ d′ m} step))
bundleG-api-no l cl sv cl≢sv csc css bfc bfs ip {e = apiLN l′ d′ m} ahlLN   l₀≢l apimem (_ , step) = l₀≢l (apiLink-inj ahlLN   (bundleLN-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = LN.apiLNev l′ d′ m} step))
bundleG-api-no l cl sv cl≢sv csc css bfc bfs ip {e = apiLF l′ d′ m} ahlLF   l₀≢l apimem (_ , step) = l₀≢l (apiLink-inj ahlLF   (bundleLF-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = LF.apiLFev l′ d′ m} step))
bundleG-api-no l cl sv cl≢sv csc css bfc bfs ip {e = done l′ d′ N2N_ChainSync}    ahlDone l₀≢l apimem (_ , step) = l₀≢l (apiLink-inj ahlDone (bundleCS-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = CS.doneCS l′ d′} step))
bundleG-api-no l cl sv cl≢sv csc css bfc bfs ip {e = done l′ d′ N2N_BlockFetch}   ahlDone l₀≢l apimem (_ , step) = l₀≢l (apiLink-inj ahlDone (bundleBF-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = BF.doneBF l′ d′} step))
bundleG-api-no l cl sv cl≢sv csc css bfc bfs ip {e = done l′ d′ N2N_KeepAlive}    ahlDone l₀≢l apimem (_ , step) = l₀≢l (apiLink-inj ahlDone (bundleKA-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = KA.doneKA l′ d′} step))
bundleG-api-no l cl sv cl≢sv csc css bfc bfs ip {e = done l′ d′ N2N_TxSubmission} ahlDone l₀≢l apimem (_ , step) = l₀≢l (apiLink-inj ahlDone (bundleTS-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = TS.doneTS l′ d′} step))
bundleG-api-no l cl sv cl≢sv csc css bfc bfs ip {e = done l′ d′ N2N_LeiosNotify}  ahlDone l₀≢l apimem (_ , step) = l₀≢l (apiLink-inj ahlDone (bundleLN-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = LN.doneLN l′ d′} step))
bundleG-api-no l cl sv cl≢sv csc css bfc bfs ip {e = done l′ d′ N2N_LeiosFetch}   ahlDone l₀≢l apimem (_ , step) = l₀≢l (apiLink-inj ahlDone (bundleLF-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = LF.doneLF l′ d′} step))
bundleG-api-no l cl sv cl≢sv csc css bfc bfs ip {e = input  _ _ _} _ _ apimem = ⊥-elim apimem
bundleG-api-no l cl sv cl≢sv csc css bfc bfs ip {e = output _ _ _} _ _ apimem = ⊥-elim apimem
bundleG-api-no l cl sv cl≢sv csc css bfc bfs ip {e = sndmsg _ _ _} _ _ apimem = ⊥-elim apimem
bundleG-api-no l cl sv cl≢sv csc css bfc bfs ip {e = rcvmsg _ _ _} _ _ apimem = ⊥-elim apimem
bundleG-api-no l cl sv cl≢sv csc css bfc bfs ip {e = tx     _ _ _} _ _ apimem = ⊥-elim apimem
bundleG-api-no l cl sv cl≢sv csc css bfc bfs ip {e = sndack _ _ _} _ _ apimem = ⊥-elim apimem
bundleG-api-no l cl sv cl≢sv csc css bfc bfs ip {e = rcvack _ _ _} _ _ apimem = ⊥-elim apimem
bundleG-api-no l cl sv cl≢sv csc css bfc bfs ip {e = ack    _ _ _} _ _ apimem = ⊥-elim apimem
bundleG-api-no l cl sv cl≢sv csc css bfc bfs ip {e = break  _}     _ _ apimem = ⊥-elim apimem

------------------------------------------------------------------------
-- PART 2l — ABSTRACT `absBundleG-api-no` (api/done analog of `absBundleG-io-no`).
-- The abstract sibling non-offer: dispatch on the raw api/done event and route to
-- the committed per-channel `absBundleG-X-link-noIoOffer` at the X-image event.
------------------------------------------------------------------------

absBundleG-api-no : (l : Link) (cl sv : Dir)
     (qcc : CScPos) (qcs : CSsPos) (qbc : BFcPos) (qbs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {l₀ : Link}
  → ApiHasLink l₀ e → l₀ ≢ l → apiES .mem (X , e) a
  → ¬ IoOffers (absBundleG l cl sv qcc qcs qbc qbs ip) e a
absBundleG-api-no l cl sv qcc qcs qbc qbs ip {e = apiCS l′ d′ m} ahlCS   l₀≢l apimem = absBundleG-CS-link-noIoOffer l cl sv qcc qcs qbc qbs ip (CS.apiCSev l′ d′ m) l₀≢l
absBundleG-api-no l cl sv qcc qcs qbc qbs ip {e = apiBF l′ d′ m} ahlBF   l₀≢l apimem = absBundleG-BF-link-noIoOffer l cl sv qcc qcs qbc qbs ip (BF.apiBFev l′ d′ m) l₀≢l
absBundleG-api-no l cl sv qcc qcs qbc qbs ip {e = apiKA l′ d′ m} ahlKA   l₀≢l apimem = absBundleG-KA-link-noIoOffer l cl sv qcc qcs qbc qbs ip (KA.apiKAev l′ d′ m) l₀≢l
absBundleG-api-no l cl sv qcc qcs qbc qbs ip {e = apiTS l′ d′ m} ahlTS   l₀≢l apimem = absBundleG-TS-link-noIoOffer l cl sv qcc qcs qbc qbs ip (TS.apiTSev l′ d′ m) l₀≢l
absBundleG-api-no l cl sv qcc qcs qbc qbs ip {e = apiLN l′ d′ m} ahlLN   l₀≢l apimem = absBundleG-LN-link-noIoOffer l cl sv qcc qcs qbc qbs ip (LN.apiLNev l′ d′ m) l₀≢l
absBundleG-api-no l cl sv qcc qcs qbc qbs ip {e = apiLF l′ d′ m} ahlLF   l₀≢l apimem = absBundleG-LF-link-noIoOffer l cl sv qcc qcs qbc qbs ip (LF.apiLFev l′ d′ m) l₀≢l
absBundleG-api-no l cl sv qcc qcs qbc qbs ip {e = done l′ d′ N2N_ChainSync}    ahlDone l₀≢l apimem = absBundleG-CS-link-noIoOffer l cl sv qcc qcs qbc qbs ip (CS.doneCS l′ d′) l₀≢l
absBundleG-api-no l cl sv qcc qcs qbc qbs ip {e = done l′ d′ N2N_BlockFetch}   ahlDone l₀≢l apimem = absBundleG-BF-link-noIoOffer l cl sv qcc qcs qbc qbs ip (BF.doneBF l′ d′) l₀≢l
absBundleG-api-no l cl sv qcc qcs qbc qbs ip {e = done l′ d′ N2N_KeepAlive}    ahlDone l₀≢l apimem = absBundleG-KA-link-noIoOffer l cl sv qcc qcs qbc qbs ip (KA.doneKA l′ d′) l₀≢l
absBundleG-api-no l cl sv qcc qcs qbc qbs ip {e = done l′ d′ N2N_TxSubmission} ahlDone l₀≢l apimem = absBundleG-TS-link-noIoOffer l cl sv qcc qcs qbc qbs ip (TS.doneTS l′ d′) l₀≢l
absBundleG-api-no l cl sv qcc qcs qbc qbs ip {e = done l′ d′ N2N_LeiosNotify}  ahlDone l₀≢l apimem = absBundleG-LN-link-noIoOffer l cl sv qcc qcs qbc qbs ip (LN.doneLN l′ d′) l₀≢l
absBundleG-api-no l cl sv qcc qcs qbc qbs ip {e = done l′ d′ N2N_LeiosFetch}   ahlDone l₀≢l apimem = absBundleG-LF-link-noIoOffer l cl sv qcc qcs qbc qbs ip (LF.doneLF l′ d′) l₀≢l
absBundleG-api-no l cl sv qcc qcs qbc qbs ip {e = input  _ _ _} _ _ apimem = ⊥-elim apimem
absBundleG-api-no l cl sv qcc qcs qbc qbs ip {e = output _ _ _} _ _ apimem = ⊥-elim apimem
absBundleG-api-no l cl sv qcc qcs qbc qbs ip {e = sndmsg _ _ _} _ _ apimem = ⊥-elim apimem
absBundleG-api-no l cl sv qcc qcs qbc qbs ip {e = rcvmsg _ _ _} _ _ apimem = ⊥-elim apimem
absBundleG-api-no l cl sv qcc qcs qbc qbs ip {e = tx     _ _ _} _ _ apimem = ⊥-elim apimem
absBundleG-api-no l cl sv qcc qcs qbc qbs ip {e = sndack _ _ _} _ _ apimem = ⊥-elim apimem
absBundleG-api-no l cl sv qcc qcs qbc qbs ip {e = rcvack _ _ _} _ _ apimem = ⊥-elim apimem
absBundleG-api-no l cl sv qcc qcs qbc qbs ip {e = ack    _ _ _} _ _ apimem = ⊥-elim apimem
absBundleG-api-no l cl sv qcc qcs qbc qbs ip {e = break  _}     _ _ apimem = ⊥-elim apimem

------------------------------------------------------------------------
-- PART 2m — abstract-primary node API peel `nodeA-ev-api-abs`.
--
-- The api DUAL of `nodeA-ev-io-abs`: an api event ∈ apiES is a driver↔bundle
-- SYNC (`reflect-node-api`).  Peel the driver `⦀` for the firing link, read the
-- driver's successor phase (`decProd-ev-inv`), invert the firing abstract bundle
-- (`absBundleG-api-prod` → concrete weak run), then re-synchronise the concrete
-- node with `∥⇘⇙-wev-sync` (driver fire wrapped by `ev→wev`, lifted up the driver
-- `⦀` by the strong `⦀-ev-L/R`; bundle weak run lifted by `⦀-wev-L/R`).
------------------------------------------------------------------------

-- node-A: the idle produce driver at linkAC offers nothing on a linkAB-pinned api event
drvA-AC-no : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ApiHasLink linkAB e → ¬ IoOffers (SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)) e a
drvA-AC-no na ahl (_ , s) = linkAB≢linkAC (sym (apiLink-inj (decProd-ev-link linkAC hi blkA (SN.NodeStateA.prod-AC na) s) ahl))

-- node-A: the idle produce driver at linkAB offers nothing on a linkAC-pinned api event
drvA-AB-no : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ApiHasLink linkAC e → ¬ IoOffers (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na)) e a
drvA-AB-no na ahl (_ , s) = linkAB≢linkAC (apiLink-inj (decProd-ev-link linkAB hi blkA (SN.NodeStateA.prod-AB na) s) ahl)

-- firing link = linkAB: read the driver phase, peel the abstract bundle `⦀`
-- (siblings refuted by `absBundleG-api-no`), invert the linkAB bundle, re-sync
nodeA-api-AB-abs : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁AB : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
     ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ─[ ev (evl (evLabel X e a)) ]─► D₁AB
  → ApiHasLink linkAB e
  → NodeAEvR-abs na e a (B₁ ∥⇘ apiES ⇙ (D₁AB ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)))
nodeA-api-AB-abs na {X} {e} {a} apimem bStep sDAB ahl
  with decProd-ev-inv linkAB hi blkA (SN.NodeStateA.prod-AB na) sDAB
... | peR pp′ refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
           (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) bStep
...   | PEA.evSync () _ _
...   | PEA.evR _ sBAC = ⊥-elim (absBundleG-api-no linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) ahl linkAB≢linkAC apimem (_ , sBAC))
...   | PEA.evBoth _ _ sBAC = ⊥-elim (absBundleG-api-no linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) ahl linkAB≢linkAC apimem (_ , sBAC))
...   | PEA.evL _ sBAB
      with absBundleG-api-prod linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) apimem sBAB
...     | bgEB csc′ css′ bfc′ bfs′ ip′ eq run =
          naEBa (SN.mkNodeA csc′ css′ bfc′ bfs′ pp′ (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) ip′ (SN.NodeStateA.inert-AC na))
            (cong (λ z → (z ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA pp′ ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na))) eq)
            (∥⇘⇙-wev-sync apiES _ _ apimem
               (⦀-wev-L _ _ (noOffer→viewV _ (bundleG-api-no linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) ahl linkAB≢linkAC apimem)) run)
               (ev→wev (⦀-ev-L (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na)) _ sDAB (noOffer→viewV _ (drvA-AC-no na ahl)))))

-- firing link = linkAC (mirror via ⦀-wev-R / ⦀-ev-R)
nodeA-api-AC-abs : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁AC : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
     ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na) ─[ ev (evl (evLabel X e a)) ]─► D₁AC
  → ApiHasLink linkAC e
  → NodeAEvR-abs na e a (B₁ ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ D₁AC))
nodeA-api-AC-abs na {X} {e} {a} apimem bStep sDAC ahl
  with decProd-ev-inv linkAC hi blkA (SN.NodeStateA.prod-AC na) sDAC
... | peR pp′ refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
           (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) bStep
...   | PEA.evSync () _ _
...   | PEA.evL _ sBAB = ⊥-elim (absBundleG-api-no linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ahl (λ q → linkAB≢linkAC (sym q)) apimem (_ , sBAB))
...   | PEA.evBoth _ sBAB _ = ⊥-elim (absBundleG-api-no linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ahl (λ q → linkAB≢linkAC (sym q)) apimem (_ , sBAB))
...   | PEA.evR _ sBAC
      with absBundleG-api-prod linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) apimem sBAC
...     | bgEB csc′ css′ bfc′ bfs′ ip′ eq run =
          naEBa (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na) csc′ css′ bfc′ bfs′ pp′ (SN.NodeStateA.inert-AB na) ip′)
            (cong (λ z → (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ⦀ z) ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA pp′)) eq)
            (∥⇘⇙-wev-sync apiES _ _ apimem
               (⦀-wev-R _ _ (noOffer→viewV _ (bundleG-api-no linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ahl (λ q → linkAB≢linkAC (sym q)) apimem)) run)
               (ev→wev (⦀-ev-R _ (SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)) sDAC (noOffer→viewV _ (drvA-AB-no na ahl)))))

-- node-A api inversion: reflect the driver↔bundle sync, peel the driver `⦀`, dispatch
nodeA-ev-api-abs : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeA na ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeAEvR-abs na e a M
nodeA-ev-api-abs na {X} {e} {a} apimem step
  with SStep.reflect-node-api
         (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
          ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
         (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na)) (SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)) dStep
... | PEA.evSync () _ _
... | PEA.evL _ sDAB = nodeA-api-AB-abs na apimem bStep sDAB (decProd-ev-link linkAB hi blkA (SN.NodeStateA.prod-AB na) sDAB)
... | PEA.evR _ sDAC = nodeA-api-AC-abs na apimem bStep sDAC (decProd-ev-link linkAC hi blkA (SN.NodeStateA.prod-AC na) sDAC)
... | PEA.evBoth _ sDAB sDAC = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (decProd-ev-link linkAB hi blkA (SN.NodeStateA.prod-AB na) sDAB)
                     (decProd-ev-link linkAC hi blkA (SN.NodeStateA.prod-AC na) sDAC)))

------------------------------------------------------------------------
-- node-D abstract-primary API peel (sink: two `decConsD` drivers, dirs `hi lo`)
------------------------------------------------------------------------

-- node-D: the idle consume driver at linkCD offers nothing on a linkBD-pinned api event
drvD-CD-no : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ApiHasLink linkBD e → ¬ IoOffers (SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)) e a
drvD-CD-no nd ahl (_ , s) = linkBD≢linkCD (sym (apiLink-inj (decConsD-ev-link linkCD (SN.NodeStateD.cons-CD nd) s) ahl))

-- node-D: the idle consume driver at linkBD offers nothing on a linkCD-pinned api event
drvD-BD-no : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ApiHasLink linkCD e → ¬ IoOffers (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd)) e a
drvD-BD-no nd ahl (_ , s) = linkBD≢linkCD (apiLink-inj (decConsD-ev-link linkBD (SN.NodeStateD.cons-BD nd) s) ahl)

-- firing link = linkBD
nodeD-api-BD-abs : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁BD : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
     ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ─[ ev (evl (evLabel X e a)) ]─► D₁BD
  → ApiHasLink linkBD e
  → NodeDEvR-abs nd e a (B₁ ∥⇘ apiES ⇙ (D₁BD ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)))
nodeD-api-BD-abs nd {X} {e} {a} apimem bStep sDBD ahl
  with decConsD-ev-inv linkBD (SN.NodeStateD.cons-BD nd) sDBD
... | cdR b′ cp′ refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
           (absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) bStep
...   | PEA.evSync () _ _
...   | PEA.evR _ sBCD = ⊥-elim (absBundleG-api-no linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) ahl linkBD≢linkCD apimem (_ , sBCD))
...   | PEA.evBoth _ _ sBCD = ⊥-elim (absBundleG-api-no linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) ahl linkBD≢linkCD apimem (_ , sBCD))
...   | PEA.evL _ sBBD
      with absBundleG-api-prod linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) apimem sBBD
...     | bgEB csc′ css′ bfc′ bfs′ ip′ eq run =
          ndEBa (SN.mkNodeD csc′ css′ bfc′ bfs′ (consD b′ cp′) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) ip′ (SN.NodeStateD.inert-CD nd))
            (cong (λ z → (z ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) ∥⇘ apiES ⇙ (SN.decConsD linkBD (consD b′ cp′) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))) eq)
            (∥⇘⇙-wev-sync apiES _ _ apimem
               (⦀-wev-L _ _ (noOffer→viewV _ (bundleG-api-no linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) ahl linkBD≢linkCD apimem)) run)
               (ev→wev (⦀-ev-L (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd)) _ sDBD (noOffer→viewV _ (drvD-CD-no nd ahl)))))

-- firing link = linkCD (mirror via ⦀-wev-R / ⦀-ev-R)
nodeD-api-CD-abs : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁CD : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
     ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decConsD linkCD (SN.NodeStateD.cons-CD nd) ─[ ev (evl (evLabel X e a)) ]─► D₁CD
  → ApiHasLink linkCD e
  → NodeDEvR-abs nd e a (B₁ ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ D₁CD))
nodeD-api-CD-abs nd {X} {e} {a} apimem bStep sDCD ahl
  with decConsD-ev-inv linkCD (SN.NodeStateD.cons-CD nd) sDCD
... | cdR b′ cp′ refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
           (absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) bStep
...   | PEA.evSync () _ _
...   | PEA.evL _ sBBD = ⊥-elim (absBundleG-api-no linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ahl (λ q → linkBD≢linkCD (sym q)) apimem (_ , sBBD))
...   | PEA.evBoth _ sBBD _ = ⊥-elim (absBundleG-api-no linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ahl (λ q → linkBD≢linkCD (sym q)) apimem (_ , sBBD))
...   | PEA.evR _ sBCD
      with absBundleG-api-prod linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) apimem sBCD
...     | bgEB csc′ css′ bfc′ bfs′ ip′ eq run =
          ndEBa (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd) csc′ css′ bfc′ bfs′ (consD b′ cp′) (SN.NodeStateD.inert-BD nd) ip′)
            (cong (λ z → (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ⦀ z) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (consD b′ cp′))) eq)
            (∥⇘⇙-wev-sync apiES _ _ apimem
               (⦀-wev-R _ _ (noOffer→viewV _ (bundleG-api-no linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ahl (λ q → linkBD≢linkCD (sym q)) apimem)) run)
               (ev→wev (⦀-ev-R _ (SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)) sDCD (noOffer→viewV _ (drvD-BD-no nd ahl)))))

-- node-D api inversion: reflect the driver↔bundle sync, peel the driver `⦀`, dispatch
nodeD-ev-api-abs : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeD nd ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeDEvR-abs nd e a M
nodeD-ev-api-abs nd {X} {e} {a} apimem step
  with SStep.reflect-node-api
         (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
          ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
         (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd)) (SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)) dStep
... | PEA.evSync () _ _
... | PEA.evL _ sDBD = nodeD-api-BD-abs nd apimem bStep sDBD (decConsD-ev-link linkBD (SN.NodeStateD.cons-BD nd) sDBD)
... | PEA.evR _ sDCD = nodeD-api-CD-abs nd apimem bStep sDCD (decConsD-ev-link linkCD (SN.NodeStateD.cons-CD nd) sDCD)
... | PEA.evBoth _ sDBD sDCD = ⊥-elim (linkBD≢linkCD
        (apiLink-inj (decConsD-ev-link linkBD (SN.NodeStateD.cons-BD nd) sDBD)
                     (decConsD-ev-link linkCD (SN.NodeStateD.cons-CD nd) sDCD)))

------------------------------------------------------------------------
-- node-B abstract-primary API peel (relay: SINGLE `decCP` driver).  No driver
-- `⦀` peel: `decCP-ev-link`'s `⊎` picks the firing link, `decCP-ev-inv`'s
-- `CPEvR` gives the successor phase (consuming/producing).  The driver weak run
-- is just `ev→wev dStep` (decCP is a single process, no sibling lift).
------------------------------------------------------------------------

-- firing link = linkAB (consume leg, LEFT bundle)
nodeB-api-AB-abs : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁ : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
     ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb) ─[ ev (evl (evLabel X e a)) ]─► D₁
  → ApiHasLink linkAB e
  → CPEvR linkAB linkBD (SN.NodeStateB.cp-B nb) D₁
  → NodeBEvR-abs nb e a (B₁ ∥⇘ apiES ⇙ D₁)
nodeB-api-AB-abs nb {X} {e} {a} apimem bStep dStep ahl cpr
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb))
         (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)) bStep
... | PEA.evSync () _ _
... | PEA.evR _ sBBD = ⊥-elim (absBundleG-api-no linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) ahl linkAB≢linkBD apimem (_ , sBBD))
... | PEA.evBoth _ _ sBBD = ⊥-elim (absBundleG-api-no linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) ahl linkAB≢linkBD apimem (_ , sBBD))
... | PEA.evL _ sBAB
    with absBundleG-api-prod linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) apimem sBAB | cpr
...   | bgEB csc′ css′ bfc′ bfs′ ip′ eq run | cpR-cons b′ cp′ refl =
        nbEBa (SN.mkNodeB csc′ css′ bfc′ bfs′ (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (consuming b′ cp′) ip′ (SN.NodeStateB.inert-BD nb))
          (cong (λ z → (z ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD (consuming b′ cp′)) eq)
          (∥⇘⇙-wev-sync apiES _ _ apimem
             (⦀-wev-L _ _ (noOffer→viewV _ (bundleG-api-no linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) ahl linkAB≢linkBD apimem)) run)
             (ev→wev dStep))
...   | bgEB csc′ css′ bfc′ bfs′ ip′ eq run | cpR-prod b′ pp′ refl =
        nbEBa (SN.mkNodeB csc′ css′ bfc′ bfs′ (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (producing b′ pp′) ip′ (SN.NodeStateB.inert-BD nb))
          (cong (λ z → (z ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD (producing b′ pp′)) eq)
          (∥⇘⇙-wev-sync apiES _ _ apimem
             (⦀-wev-L _ _ (noOffer→viewV _ (bundleG-api-no linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) ahl linkAB≢linkBD apimem)) run)
             (ev→wev dStep))

-- firing link = linkBD (produce leg, RIGHT bundle)
nodeB-api-BD-abs : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁ : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
     ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb) ─[ ev (evl (evLabel X e a)) ]─► D₁
  → ApiHasLink linkBD e
  → CPEvR linkAB linkBD (SN.NodeStateB.cp-B nb) D₁
  → NodeBEvR-abs nb e a (B₁ ∥⇘ apiES ⇙ D₁)
nodeB-api-BD-abs nb {X} {e} {a} apimem bStep dStep ahl cpr
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb))
         (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)) bStep
... | PEA.evSync () _ _
... | PEA.evL _ sBAB = ⊥-elim (absBundleG-api-no linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ahl (λ q → linkAB≢linkBD (sym q)) apimem (_ , sBAB))
... | PEA.evBoth _ sBAB _ = ⊥-elim (absBundleG-api-no linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ahl (λ q → linkAB≢linkBD (sym q)) apimem (_ , sBAB))
... | PEA.evR _ sBBD
    with absBundleG-api-prod linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) apimem sBBD | cpr
...   | bgEB csc′ css′ bfc′ bfs′ ip′ eq run | cpR-cons b′ cp′ refl =
        nbEBa (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) csc′ css′ bfc′ bfs′ (consuming b′ cp′) (SN.NodeStateB.inert-AB nb) ip′)
          (cong (λ z → (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ⦀ z) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD (consuming b′ cp′)) eq)
          (∥⇘⇙-wev-sync apiES _ _ apimem
             (⦀-wev-R _ _ (noOffer→viewV _ (bundleG-api-no linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ahl (λ q → linkAB≢linkBD (sym q)) apimem)) run)
             (ev→wev dStep))
...   | bgEB csc′ css′ bfc′ bfs′ ip′ eq run | cpR-prod b′ pp′ refl =
        nbEBa (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) csc′ css′ bfc′ bfs′ (producing b′ pp′) (SN.NodeStateB.inert-AB nb) ip′)
          (cong (λ z → (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ⦀ z) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD (producing b′ pp′)) eq)
          (∥⇘⇙-wev-sync apiES _ _ apimem
             (⦀-wev-R _ _ (noOffer→viewV _ (bundleG-api-no linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ahl (λ q → linkAB≢linkBD (sym q)) apimem)) run)
             (ev→wev dStep))

-- node-B api inversion: reflect the sync, pick the firing link via `decCP-ev-link`'s ⊎
nodeB-ev-api-abs : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeB nb ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeBEvR-abs nb e a M
nodeB-ev-api-abs nb {X} {e} {a} apimem step
  with SStep.reflect-node-api
         (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
          ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
         (SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with decCP-ev-link linkAB linkBD (SN.NodeStateB.cp-B nb) dStep
... | inj₁ ahl = nodeB-api-AB-abs nb apimem bStep dStep ahl (decCP-ev-inv linkAB linkBD (SN.NodeStateB.cp-B nb) dStep)
... | inj₂ ahl = nodeB-api-BD-abs nb apimem bStep dStep ahl (decCP-ev-inv linkAB linkBD (SN.NodeStateB.cp-B nb) dStep)

------------------------------------------------------------------------
-- node-C abstract-primary API peel (relay: SINGLE `decCP` driver; mirror of B)
------------------------------------------------------------------------

-- firing link = linkAC (consume leg, LEFT bundle)
nodeC-api-AC-abs : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁ : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
     ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc) ─[ ev (evl (evLabel X e a)) ]─► D₁
  → ApiHasLink linkAC e
  → CPEvR linkAC linkCD (SN.NodeStateC.cp-C nc) D₁
  → NodeCEvR-abs nc e a (B₁ ∥⇘ apiES ⇙ D₁)
nodeC-api-AC-abs nc {X} {e} {a} apimem bStep dStep ahl cpr
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc))
         (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)) bStep
... | PEA.evSync () _ _
... | PEA.evR _ sBCD = ⊥-elim (absBundleG-api-no linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) ahl linkAC≢linkCD apimem (_ , sBCD))
... | PEA.evBoth _ _ sBCD = ⊥-elim (absBundleG-api-no linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) ahl linkAC≢linkCD apimem (_ , sBCD))
... | PEA.evL _ sBAC
    with absBundleG-api-prod linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) apimem sBAC | cpr
...   | bgEB csc′ css′ bfc′ bfs′ ip′ eq run | cpR-cons b′ cp′ refl =
        ncEBa (SN.mkNodeC csc′ css′ bfc′ bfs′ (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (consuming b′ cp′) ip′ (SN.NodeStateC.inert-CD nc))
          (cong (λ z → (z ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD (consuming b′ cp′)) eq)
          (∥⇘⇙-wev-sync apiES _ _ apimem
             (⦀-wev-L _ _ (noOffer→viewV _ (bundleG-api-no linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) ahl linkAC≢linkCD apimem)) run)
             (ev→wev dStep))
...   | bgEB csc′ css′ bfc′ bfs′ ip′ eq run | cpR-prod b′ pp′ refl =
        ncEBa (SN.mkNodeC csc′ css′ bfc′ bfs′ (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (producing b′ pp′) ip′ (SN.NodeStateC.inert-CD nc))
          (cong (λ z → (z ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD (producing b′ pp′)) eq)
          (∥⇘⇙-wev-sync apiES _ _ apimem
             (⦀-wev-L _ _ (noOffer→viewV _ (bundleG-api-no linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) ahl linkAC≢linkCD apimem)) run)
             (ev→wev dStep))

-- firing link = linkCD (produce leg, RIGHT bundle)
nodeC-api-CD-abs : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁ : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
     ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc) ─[ ev (evl (evLabel X e a)) ]─► D₁
  → ApiHasLink linkCD e
  → CPEvR linkAC linkCD (SN.NodeStateC.cp-C nc) D₁
  → NodeCEvR-abs nc e a (B₁ ∥⇘ apiES ⇙ D₁)
nodeC-api-CD-abs nc {X} {e} {a} apimem bStep dStep ahl cpr
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc))
         (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)) bStep
... | PEA.evSync () _ _
... | PEA.evL _ sBAC = ⊥-elim (absBundleG-api-no linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ahl (λ q → linkAC≢linkCD (sym q)) apimem (_ , sBAC))
... | PEA.evBoth _ sBAC _ = ⊥-elim (absBundleG-api-no linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ahl (λ q → linkAC≢linkCD (sym q)) apimem (_ , sBAC))
... | PEA.evR _ sBCD
    with absBundleG-api-prod linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) apimem sBCD | cpr
...   | bgEB csc′ css′ bfc′ bfs′ ip′ eq run | cpR-cons b′ cp′ refl =
        ncEBa (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) csc′ css′ bfc′ bfs′ (consuming b′ cp′) (SN.NodeStateC.inert-AC nc) ip′)
          (cong (λ z → (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ⦀ z) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD (consuming b′ cp′)) eq)
          (∥⇘⇙-wev-sync apiES _ _ apimem
             (⦀-wev-R _ _ (noOffer→viewV _ (bundleG-api-no linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ahl (λ q → linkAC≢linkCD (sym q)) apimem)) run)
             (ev→wev dStep))
...   | bgEB csc′ css′ bfc′ bfs′ ip′ eq run | cpR-prod b′ pp′ refl =
        ncEBa (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) csc′ css′ bfc′ bfs′ (producing b′ pp′) (SN.NodeStateC.inert-AC nc) ip′)
          (cong (λ z → (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ⦀ z) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD (producing b′ pp′)) eq)
          (∥⇘⇙-wev-sync apiES _ _ apimem
             (⦀-wev-R _ _ (noOffer→viewV _ (bundleG-api-no linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ahl (λ q → linkAC≢linkCD (sym q)) apimem)) run)
             (ev→wev dStep))

-- node-C api inversion: reflect the sync, pick the firing link via `decCP-ev-link`'s ⊎
nodeC-ev-api-abs : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeC nc ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeCEvR-abs nc e a M
nodeC-ev-api-abs nc {X} {e} {a} apimem step
  with SStep.reflect-node-api
         (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
          ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
         (SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with decCP-ev-link linkAC linkCD (SN.NodeStateC.cp-C nc) dStep
... | inj₁ ahl = nodeC-api-AC-abs nc apimem bStep dStep ahl (decCP-ev-inv linkAC linkCD (SN.NodeStateC.cp-C nc) dStep)
... | inj₂ ahl = nodeC-api-CD-abs nc apimem bStep dStep ahl (decCP-ev-inv linkAC linkCD (SN.NodeStateC.cp-C nc) dStep)

------------------------------------------------------------------------
-- PART 2n — REVERSE concrete pairwise node non-offers (api + io).
--
-- The concrete weak-`⦀` lift in `top-nodes-abs`/`top-nodes-io-abs` (when a LATER
-- node fires) must show the EARLIER idle nodes offer nothing on the fired event.
-- The committed non-offers cover only the FORWARD direction (later-when-earlier);
-- these are the six REVERSE (earlier-when-later) mirrors, per channel, reading
-- the firing node's fingerprint off the CONCRETE `nodeX-fp` / `nodeX-io-fp` and
-- clashing on prod≢cons / link / dir⊕role exactly as the forward ones do.
------------------------------------------------------------------------

-- api reverse: node A idle when B/C/D fires; node B idle when C/D; node C idle when D
nodeA-no-when-B : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → (ApiIsCons e × ApiHasLink linkAB e) ⊎ (ApiIsProd e × ApiHasLink linkBD e)
  → ¬ IoOffers (SN.decNodeA na) e a
nodeA-no-when-B na mem fpB (M , step) with nodeA-fp na mem step | fpB
... | (prodA , _)      | inj₁ (consB , _)  = prod≢cons prodA consB
... | (_ , inj₁ ahlAB) | inj₂ (_ , ahlBD)  = linkAB≢linkBD (apiLink-inj ahlAB ahlBD)
... | (_ , inj₂ ahlAC) | inj₂ (_ , ahlBD)  = linkAC≢linkBD (apiLink-inj ahlAC ahlBD)

nodeA-no-when-C : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → (ApiIsCons e × ApiHasLink linkAC e) ⊎ (ApiIsProd e × ApiHasLink linkCD e)
  → ¬ IoOffers (SN.decNodeA na) e a
nodeA-no-when-C na mem fpC (M , step) with nodeA-fp na mem step | fpC
... | (prodA , _)      | inj₁ (consC , _)  = prod≢cons prodA consC
... | (_ , inj₁ ahlAB) | inj₂ (_ , ahlCD)  = linkAB≢linkCD (apiLink-inj ahlAB ahlCD)
... | (_ , inj₂ ahlAC) | inj₂ (_ , ahlCD)  = linkAC≢linkCD (apiLink-inj ahlAC ahlCD)

nodeB-no-when-C : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → (ApiIsCons e × ApiHasLink linkAC e) ⊎ (ApiIsProd e × ApiHasLink linkCD e)
  → ¬ IoOffers (SN.decNodeB nb) e a
nodeB-no-when-C nb mem fpC (M , step) with nodeB-fp nb mem step | fpC
... | inj₁ (_ , ahlAB) | inj₁ (_ , ahlAC) = linkAB≢linkAC (apiLink-inj ahlAB ahlAC)
... | inj₁ (consB , _) | inj₂ (prodC , _) = prod≢cons prodC consB
... | inj₂ (prodB , _) | inj₁ (consC , _) = prod≢cons prodB consC
... | inj₂ (_ , ahlBD) | inj₂ (_ , ahlCD) = linkBD≢linkCD (apiLink-inj ahlBD ahlCD)

nodeA-no-when-D : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → ApiIsCons e × (ApiHasLink linkBD e ⊎ ApiHasLink linkCD e)
  → ¬ IoOffers (SN.decNodeA na) e a
nodeA-no-when-D na mem (consDd , _) (M , step) with nodeA-fp na mem step
... | (prodA , _) = prod≢cons prodA consDd

nodeB-no-when-D : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → ApiIsCons e × (ApiHasLink linkBD e ⊎ ApiHasLink linkCD e)
  → ¬ IoOffers (SN.decNodeB nb) e a
nodeB-no-when-D nb mem fpD (M , step) with nodeB-fp nb mem step | fpD
... | inj₁ (_ , ahlAB) | (_ , inj₁ ahlBD) = linkAB≢linkBD (apiLink-inj ahlAB ahlBD)
... | inj₁ (_ , ahlAB) | (_ , inj₂ ahlCD) = linkAB≢linkCD (apiLink-inj ahlAB ahlCD)
... | inj₂ (prodB , _) | (consDd , _)     = prod≢cons prodB consDd

nodeC-no-when-D : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → apiES .mem (X , e) a → ApiIsCons e × (ApiHasLink linkBD e ⊎ ApiHasLink linkCD e)
  → ¬ IoOffers (SN.decNodeC nc) e a
nodeC-no-when-D nc mem fpD (M , step) with nodeC-fp nc mem step | fpD
... | inj₁ (_ , ahlAC) | (_ , inj₁ ahlBD) = linkAC≢linkBD (apiLink-inj ahlAC ahlBD)
... | inj₁ (_ , ahlAC) | (_ , inj₂ ahlCD) = linkAC≢linkCD (apiLink-inj ahlAC ahlCD)
... | inj₂ (prodC , _) | (consDd , _)     = prod≢cons prodC consDd

-- io reverse: node A idle when B/C/D fires; node B idle when C/D; node C idle when D
nodeA-io-no-when-B : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a → (ApiHasLink linkAB e × RoleFP hi lo e a) ⊎ (ApiHasLink linkBD e × RoleFP lo hi e a)
  → ¬ IoOffers (SN.decNodeA na) e a
nodeA-io-no-when-B na iomem fpB (M , step) with nodeA-io-fp na iomem step | fpB
... | inj₁ (_ , roleA)    | inj₁ (_ , roleB)    = role-clash lo hi lo≢hi iomem roleA roleB
... | inj₁ (ahlAB , _)    | inj₂ (ahlBD , _)    = linkAB≢linkBD (apiLink-inj ahlAB ahlBD)
... | inj₂ (ahlAC , _)    | inj₁ (ahlAB , _)    = linkAB≢linkAC (apiLink-inj ahlAB ahlAC)
... | inj₂ (ahlAC , _)    | inj₂ (ahlBD , _)    = linkAC≢linkBD (apiLink-inj ahlAC ahlBD)

nodeA-io-no-when-C : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a → (ApiHasLink linkAC e × RoleFP hi lo e a) ⊎ (ApiHasLink linkCD e × RoleFP lo hi e a)
  → ¬ IoOffers (SN.decNodeA na) e a
nodeA-io-no-when-C na iomem fpC (M , step) with nodeA-io-fp na iomem step | fpC
... | inj₂ (_ , roleA)    | inj₁ (_ , roleC)    = role-clash lo hi lo≢hi iomem roleA roleC
... | inj₁ (ahlAB , _)    | inj₁ (ahlAC , _)    = linkAB≢linkAC (apiLink-inj ahlAB ahlAC)
... | inj₁ (ahlAB , _)    | inj₂ (ahlCD , _)    = linkAB≢linkCD (apiLink-inj ahlAB ahlCD)
... | inj₂ (ahlAC , _)    | inj₂ (ahlCD , _)    = linkAC≢linkCD (apiLink-inj ahlAC ahlCD)

nodeB-io-no-when-C : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a → (ApiHasLink linkAC e × RoleFP hi lo e a) ⊎ (ApiHasLink linkCD e × RoleFP lo hi e a)
  → ¬ IoOffers (SN.decNodeB nb) e a
nodeB-io-no-when-C nb iomem fpC (M , step) with nodeB-io-fp nb iomem step | fpC
... | inj₁ (ahlAB , _)    | inj₁ (ahlAC , _)    = linkAB≢linkAC (apiLink-inj ahlAB ahlAC)
... | inj₁ (ahlAB , _)    | inj₂ (ahlCD , _)    = linkAB≢linkCD (apiLink-inj ahlAB ahlCD)
... | inj₂ (ahlBD , _)    | inj₁ (ahlAC , _)    = linkAC≢linkBD (apiLink-inj ahlAC ahlBD)
... | inj₂ (ahlBD , _)    | inj₂ (ahlCD , _)    = linkBD≢linkCD (apiLink-inj ahlBD ahlCD)

nodeA-io-no-when-D : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a → (ApiHasLink linkBD e × RoleFP hi lo e a) ⊎ (ApiHasLink linkCD e × RoleFP hi lo e a)
  → ¬ IoOffers (SN.decNodeA na) e a
nodeA-io-no-when-D na iomem fpD (M , step) with nodeA-io-fp na iomem step | fpD
... | inj₁ (ahlAB , _)    | inj₁ (ahlBD , _)    = linkAB≢linkBD (apiLink-inj ahlAB ahlBD)
... | inj₁ (ahlAB , _)    | inj₂ (ahlCD , _)    = linkAB≢linkCD (apiLink-inj ahlAB ahlCD)
... | inj₂ (ahlAC , _)    | inj₁ (ahlBD , _)    = linkAC≢linkBD (apiLink-inj ahlAC ahlBD)
... | inj₂ (ahlAC , _)    | inj₂ (ahlCD , _)    = linkAC≢linkCD (apiLink-inj ahlAC ahlCD)

nodeB-io-no-when-D : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a → (ApiHasLink linkBD e × RoleFP hi lo e a) ⊎ (ApiHasLink linkCD e × RoleFP hi lo e a)
  → ¬ IoOffers (SN.decNodeB nb) e a
nodeB-io-no-when-D nb iomem fpD (M , step) with nodeB-io-fp nb iomem step | fpD
... | inj₂ (_ , roleB)    | inj₁ (_ , roleD)    = role-clash lo hi lo≢hi iomem roleB roleD
... | inj₁ (ahlAB , _)    | inj₁ (ahlBD , _)    = linkAB≢linkBD (apiLink-inj ahlAB ahlBD)
... | inj₁ (ahlAB , _)    | inj₂ (ahlCD , _)    = linkAB≢linkCD (apiLink-inj ahlAB ahlCD)
... | inj₂ (ahlBD , _)    | inj₂ (ahlCD , _)    = linkBD≢linkCD (apiLink-inj ahlBD ahlCD)

nodeC-io-no-when-D : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a → (ApiHasLink linkBD e × RoleFP hi lo e a) ⊎ (ApiHasLink linkCD e × RoleFP hi lo e a)
  → ¬ IoOffers (SN.decNodeC nc) e a
nodeC-io-no-when-D nc iomem fpD (M , step) with nodeC-io-fp nc iomem step | fpD
... | inj₂ (_ , roleC)    | inj₂ (_ , roleD)    = role-clash lo hi lo≢hi iomem roleC roleD
... | inj₁ (ahlAC , _)    | inj₁ (ahlBD , _)    = linkAC≢linkBD (apiLink-inj ahlAC ahlBD)
... | inj₁ (ahlAC , _)    | inj₂ (ahlCD , _)    = linkAC≢linkCD (apiLink-inj ahlAC ahlCD)
... | inj₂ (ahlCD , _)    | inj₁ (ahlBD , _)    = linkBD≢linkCD (apiLink-inj ahlBD ahlCD)

------------------------------------------------------------------------
-- PART 2o — `top-nodes-io-abs`: the abstract-primary DUAL of `top-nodes-io`.
--
-- An abstract hidden-io visible event of the 4-node `⦀` bundle (`absNodesOf s`)
-- is peeled to a UNIQUE firing abstract node (interleave `evBoth` overlap refuted
-- by the abstract io group non-offers — NO surviving evBoth, route (a)).  The
-- firing abstract node is inverted by the DONE `nodeX-ev-io-abs` (returning
-- `NodeXEvR-abs`: successor `nx′`, `M ≡ absNodeX nx′`, and the CONCRETE node WEAK
-- run `decNodeX (nX s) ═► decNodeX nx′`); `s′` is that single field update, so
-- `med s ≡ med s′` is `refl`.  The concrete node weak run is lifted up `nodesOf`
-- by the weak `⦀-wev-L/R` with idle CONCRETE siblings via the pairwise io
-- non-offers.  Feeds `oevB`'s nodes-side concrete weak run + `M ≡ absNodesOf s′`.
------------------------------------------------------------------------
top-nodes-io-abs : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → SStep.absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ s′ ∈ SysState ] (med s ≡ med s′) × (M ≡ SStep.absNodesOf s′) × (SStep.nodesOf s ═[ ev (evl (evLabel X e a)) ]═► SStep.nodesOf s′)
top-nodes-io-abs s iomem nodesStep
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (absNodeA (nA s)) (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s))) nodesStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sA sRest = ⊥-elim (absGroupA-io-no (nA s) (nB s) (nC s) (nD s) iomem sA (_ , sRest))
... | PEA.evL _ sA with nodeA-ev-io-abs (nA s) iomem sA
...   | naEBa na′ Meq weakRunA =
        mkSys (med s) na′ (nB s) (nC s) (nD s) , refl ,
        cong (λ z → z ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) Meq ,
        ⦀-wev-L (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (SStep.⦀-noOffer (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (nodeB-io-no-when-A (nB s) iomem fpA)
             (SStep.⦀-noOffer (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (nodeC-io-no-when-A (nC s) iomem fpA) (nodeD-io-no-when-A (nD s) iomem fpA))))
          weakRunA
  where fpA = absNodeA-io-fp (nA s) iomem sA
top-nodes-io-abs s iomem nodesStep | PEA.evR _ sRest
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s)) sRest
... | PEA.evSync () _ _
... | PEA.evBoth _ sB sCD = ⊥-elim (absGroupB-io-no (nB s) (nC s) (nD s) iomem sB (_ , sCD))
... | PEA.evL _ sB with nodeB-ev-io-abs (nB s) iomem sB
...   | nbEBa nb′ Meq weakRunB =
        mkSys (med s) (nA s) nb′ (nC s) (nD s) , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (z ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) Meq ,
        ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (nodeA-io-no-when-B (nA s) iomem fpB))
          (⦀-wev-L (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (noOffer→viewV _ (SStep.⦀-noOffer (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (nodeC-io-no-when-B (nC s) iomem fpB) (nodeD-io-no-when-B (nD s) iomem fpB)))
             weakRunB)
  where fpB = absNodeB-io-fp (nB s) iomem sB
top-nodes-io-abs s iomem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absNodeC (nC s)) (absNodeD (nD s)) sCD
... | PEA.evSync () _ _
... | PEA.evBoth _ sC sD = ⊥-elim (absNodeD-io-no-when-C (nD s) iomem (absNodeC-io-fp (nC s) iomem sC) (_ , sD))
... | PEA.evL _ sC with nodeC-ev-io-abs (nC s) iomem sC
...   | ncEBa nc′ Meq weakRunC =
        mkSys (med s) (nA s) (nB s) nc′ (nD s) , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (z ⦀ absNodeD (nD s)))) Meq ,
        ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (nodeA-io-no-when-C (nA s) iomem fpC))
          (⦀-wev-R (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (noOffer→viewV _ (nodeB-io-no-when-C (nB s) iomem fpC))
             (⦀-wev-L (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (noOffer→viewV _ (nodeD-io-no-when-C (nD s) iomem fpC))
                weakRunC))
  where fpC = absNodeC-io-fp (nC s) iomem sC
top-nodes-io-abs s iomem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD | PEA.evR _ sD
    with nodeD-ev-io-abs (nD s) iomem sD
... | ndEBa nd′ Meq weakRunD =
        mkSys (med s) (nA s) (nB s) (nC s) nd′ , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ z))) Meq ,
        ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (nodeA-io-no-when-D (nA s) iomem fpD))
          (⦀-wev-R (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (noOffer→viewV _ (nodeB-io-no-when-D (nB s) iomem fpD))
             (⦀-wev-R (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (noOffer→viewV _ (nodeC-io-no-when-D (nC s) iomem fpD))
                weakRunD))
  where fpD = absNodeD-io-fp (nD s) iomem sD

------------------------------------------------------------------------
-- PART 2p — `top-nodes-abs`: the abstract-primary DUAL of `top-nodes` (api).
-- Same shape as `top-nodes-io-abs`; the api fingerprints (`absNodeX-fp`) and
-- pairwise non-offers (`nodeX-no-when-Y`) replace the io ones, and the firing
-- node is inverted by `nodeX-ev-api-abs`.  The abstract `evBoth` group non-offer
-- is built inline from the committed FORWARD abstract non-offers.
------------------------------------------------------------------------
top-nodes-abs : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → SStep.absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ s′ ∈ SysState ] (med s ≡ med s′) × (M ≡ SStep.absNodesOf s′) × (SStep.nodesOf s ═[ ev (evl (evLabel X e a)) ]═► SStep.nodesOf s′)
top-nodes-abs s apimem nodesStep
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (absNodeA (nA s)) (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s))) nodesStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sA sRest = ⊥-elim (SStep.⦀-noOffer (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s))
        (absNodeB-no-when-A (nB s) apimem (absNodeA-fp (nA s) apimem sA))
        (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
          (absNodeC-no-when-A (nC s) apimem (absNodeA-fp (nA s) apimem sA))
          (absNodeD-no-when-A (nD s) apimem (absNodeA-fp (nA s) apimem sA))) (_ , sRest))
... | PEA.evL _ sA with nodeA-ev-api-abs (nA s) apimem sA
...   | naEBa na′ Meq weakRunA =
        mkSys (med s) na′ (nB s) (nC s) (nD s) , refl ,
        cong (λ z → z ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) Meq ,
        ⦀-wev-L (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (SStep.⦀-noOffer (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (nodeB-no-when-A (nB s) apimem fpA)
             (SStep.⦀-noOffer (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (nodeC-no-when-A (nC s) apimem fpA) (nodeD-no-when-A (nD s) apimem fpA))))
          weakRunA
  where fpA = absNodeA-fp (nA s) apimem sA
top-nodes-abs s apimem nodesStep | PEA.evR _ sRest
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s)) sRest
... | PEA.evSync () _ _
... | PEA.evBoth _ sB sCD = ⊥-elim (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
        (absNodeC-no-when-B (nC s) apimem (absNodeB-fp (nB s) apimem sB))
        (absNodeD-no-when-B (nD s) apimem (absNodeB-fp (nB s) apimem sB)) (_ , sCD))
... | PEA.evL _ sB with nodeB-ev-api-abs (nB s) apimem sB
...   | nbEBa nb′ Meq weakRunB =
        mkSys (med s) (nA s) nb′ (nC s) (nD s) , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (z ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) Meq ,
        ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (nodeA-no-when-B (nA s) apimem fpB))
          (⦀-wev-L (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (noOffer→viewV _ (SStep.⦀-noOffer (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (nodeC-no-when-B (nC s) apimem fpB) (nodeD-no-when-B (nD s) apimem fpB)))
             weakRunB)
  where fpB = absNodeB-fp (nB s) apimem sB
top-nodes-abs s apimem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absNodeC (nC s)) (absNodeD (nD s)) sCD
... | PEA.evSync () _ _
... | PEA.evBoth _ sC sD = ⊥-elim (absNodeD-no-when-C (nD s) apimem (absNodeC-fp (nC s) apimem sC) (_ , sD))
... | PEA.evL _ sC with nodeC-ev-api-abs (nC s) apimem sC
...   | ncEBa nc′ Meq weakRunC =
        mkSys (med s) (nA s) (nB s) nc′ (nD s) , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (z ⦀ absNodeD (nD s)))) Meq ,
        ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (nodeA-no-when-C (nA s) apimem fpC))
          (⦀-wev-R (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (noOffer→viewV _ (nodeB-no-when-C (nB s) apimem fpC))
             (⦀-wev-L (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (noOffer→viewV _ (nodeD-no-when-C (nD s) apimem fpC))
                weakRunC))
  where fpC = absNodeC-fp (nC s) apimem sC
top-nodes-abs s apimem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD | PEA.evR _ sD
    with nodeD-ev-api-abs (nD s) apimem sD
... | ndEBa nd′ Meq weakRunD =
        mkSys (med s) (nA s) (nB s) (nC s) nd′ , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ z))) Meq ,
        ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (nodeA-no-when-D (nA s) apimem fpD))
          (⦀-wev-R (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (noOffer→viewV _ (nodeB-no-when-D (nB s) apimem fpD))
             (⦀-wev-R (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (noOffer→viewV _ (nodeC-no-when-D (nC s) apimem fpD))
                weakRunD))
  where fpD = absNodeD-fp (nD s) apimem sD
