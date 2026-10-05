{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the ev-hop `μTot` DROP CONE (`Praos.WalkApiDrop`).
--
-- The API-advance analogue of the committed io-drop `WalkConvNodeDrop`
-- (`nodeX-ev-io-abs-wt` / `top-nodes-io-abs-wt`).  RE-MIRRORS the frozen
-- SysIoLink6 abstract-primary API node peels (`nodeX-ev-api-abs` ×4 +
-- `top-nodes-abs`), swapping the phase-only driver inverter
-- (`decProd-ev-inv`/`decConsD-ev-inv`/`decCP-ev-inv`) for the `WalkClassify`
-- driver-advance EXTRACTOR (`prodAdv-of`/`consDAdv-of`/`cpAdv-of`) so the
-- firing node returns its successor `nx′` + `M ≡ absNodeX nx′` + the driver
-- ADJACENCY (`ProdAdv`/`ConsAdv`) / direct `cpW`-drop ALONGSIDE the concrete
-- weak run.  Unlike the io-drop cone, the BUNDLE is measure-NEUTRAL
-- (`WalkMeasure.μGk-cong`), so `absBundleG-api-prod` is reused VERBATIM — no
-- bundle-weight re-mirror is needed.
--
-- `top-nodes-abs-wt` then assembles the whole-system `μTot` strict decrease
-- via `Walk.μTot-adv-G1`/`-G2` (the firing group's `μGk` strictly ↓ by the
-- adjacency, the OTHER group fixed by `μGk-cong`, the break budget fixed by
-- `med s ≡ med s′` since an api event leaves the medium untouched).
--
-- Node→group map: A.prod-AB / B.cp-B / D.cons-BD → G1;
--                 A.prod-AC / C.cp-C / D.cons-CD → G2.
--
-- The re-mirror keeps SysIoLink5/6 READ-ONLY (imported, never edited).  The
-- 10-sibling `⊥-elim` refutations + the `∥⇘⇙-wev-sync` weak-run assembly are
-- copied VERBATIM (a `⊥-elim` fits any target; the run does not read the
-- measure).  No postulate/hole/meta.
------------------------------------------------------------------------

open import Data.Nat using ( ℕ; _<_; _+_ )
open import Data.Nat.Properties using ( +-monoˡ-<; +-monoʳ-< )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkApiDrop (blkA : Block₃) where

open import Level using (0ℓ)
open import Data.Product using ( _,_ )
open import Data.Maybe using ( nothing )
open import Relation.Binary.PropositionalEquality using ( _≡_ )
open import Relation.Nullary using ( ¬_ )
open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using
  ( p; apiES; linkAB; linkAC; linkBD; linkCD; Block₃ )
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
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep
open SStep using
  ( NetProc; IoOffers
  ; ⦀-τ-L; ⦀-τ-R; ∥⇘⇙-τ-L; ∥⇘⇙-τ-R
  ; ⦀-ev-L; ⦀-ev-R; ∥⇘⇙-ev-sync; ∥⇘⇙-ev-soloL; ∥⇘⇙-ev-soloR )

open import Data.Empty using ( ⊥-elim )
open import Data.Unit.Polymorphic using ( tt )
open import Relation.Nullary using ( yes; no )
open import Relation.Binary.PropositionalEquality using ( refl; cong; trans; sym; _≢_; subst )
open import Class.DecEq using ( _≟_ )
open import Data.Product using ( Σ; _×_; Σ-syntax )
open import Data.Sum using ( inj₁; inj₂; _⊎_ )

open import CSP.Examples.Cardano_network.Base using
  ( Dir; lo; hi )
open import CSP.Examples.Cardano_network.Net p using
  ( Link; apiBF; recvBFBlock )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )
open SStep using
  ( absBundleG; absNodeA; absNodeB; absNodeC; absNodeD )
-- node states, decodes and constructors (qualified: SN.decNodeA / SN.mkNodeA / SN.NodeStateA…)
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using
  ( ProdPh; ConsPh; CPPh; consuming; producing; consD; cph; cblk; cp3
  ; prod-AB; prod-AC; cp-B; cp-C; cons-BD; cons-CD )
import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload}) as PEA
open Op using () renaming ( ∅ES to ∅ESa )

-- the api-link fingerprint + the driver phase link inversions
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA using
  ( ApiHasLink; apiLink-inj; io⇒¬api
  ; decProd-ev-link; decConsD-ev-link; decCP-ev-link )

-- top-nodes machinery: SysState + api fingerprints + FORWARD pairwise/group
-- non-offers (abstract + concrete api).
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA using
  ( SysState; mkSys; med; nA; nB; nC; nD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysRoute blkA using
  ( nodeA-fp; nodeB-fp; nodeC-fp; nodeD-fp
  ; absNodeA-fp; absNodeB-fp; absNodeC-fp; absNodeD-fp
  ; nodeB-no-when-A; nodeC-no-when-A; nodeD-no-when-A; nodeC-no-when-B; nodeD-no-when-B; nodeD-no-when-C
  ; absNodeB-no-when-A; absNodeC-no-when-A; absNodeD-no-when-A; absNodeC-no-when-B; absNodeD-no-when-B; absNodeD-no-when-C )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink3 blkA using
  ( linkAB≢linkCD; linkAC≢linkBD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink blkA using
  ( linkAB≢linkAC; linkAB≢linkBD; linkAC≢linkCD; linkBD≢linkCD )

-- the frozen SysIoLink6 API node-peel machinery (weak-run congruences, abstract
-- bundle api production/non-offer, driver idle non-offers, `ev→wev`, the bundle
-- result ctor `bgEB`).  IMPORTED, never edited.
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_RouteLnLf blkA
  using ( noOffer→viewV )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink6 blkA
  using ( ⦀-wev-L; ⦀-wev-R; ∥⇘⇙-wev-sync
        ; ev→wev
        ; BundleGEvR-abs; bgEB
        ; absBundleG-api-prod; absBundleG-api-no; bundleG-api-no
        ; drvA-AC-no; drvA-AB-no; drvD-CD-no; drvD-BD-no
        ; nodeA-no-when-B; nodeA-no-when-C; nodeA-no-when-D
        ; nodeB-no-when-C; nodeB-no-when-D; nodeC-no-when-D )

-- the driver-advance classifiers (return the ADJACENCY / direct cpW-drop)
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkClassify blkA using
  ( prodAdv-of; consDAdv-of; cpAdv-of; consD-c34-lbl )
-- SESSION-36: the VALUE-ANCHORED node-D classifier (`consDAdv-of` with the
-- delivering label pinned at the SAME successor block), so the two `ndEBawt`
-- reports can carry `cblk (cons-BD nd′) ≡ b″` by `refl`
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkDAnchor blkA using
  ( consDAdv-of⁺ )
-- the per-group measure `μG1`/`μG2`, its congruences, the driver adjacencies,
-- the driver weights, and the per-driver group advances
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkMeasure blkA using
  ( ProdAdv; ConsAdv; cpW; prodW; consW; consDW
  ; μG1; μG2; μG1-cong; μG2-cong
  ; μG1-adv-prod; μG1-adv-cons; μG2-adv-prod; μG2-adv-cons )
-- the whole-trace measure `μTot` and its per-group strict-descent lemmas
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.Walk blkA using
  ( μTot; μTot-adv-G1; μTot-adv-G2; breakBudget )

------------------------------------------------------------------------
-- The `-wt` node result types: the successor `nx′`, `M ≡ absNodeX nx′`, the
-- concrete node weak run, and the GROUP-TAGGED driver advance (nodes A/D can
-- fire either group; B is G1-only, C is G2-only).
------------------------------------------------------------------------

-- node A: fires produce on link AB (G1) or AC (G2)
data NodeAEvR-abs-wt (na : SN.NodeStateA) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                     (M : NetProc) : Set₁ where
  naEBawt1 : (na′ : SN.NodeStateA) → M ≡ absNodeA na′
           → SN.decNodeA na ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeA na′
           → ProdAdv (SN.NodeStateA.prod-AB na) (SN.NodeStateA.prod-AB na′)
           → SN.NodeStateA.prod-AC na′ ≡ SN.NodeStateA.prod-AC na
           → NodeAEvR-abs-wt na e a M
  naEBawt2 : (na′ : SN.NodeStateA) → M ≡ absNodeA na′
           → SN.decNodeA na ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeA na′
           → ProdAdv (SN.NodeStateA.prod-AC na) (SN.NodeStateA.prod-AC na′)
           → SN.NodeStateA.prod-AB na′ ≡ SN.NodeStateA.prod-AB na
           → NodeAEvR-abs-wt na e a M

-- node B: fires the relay `cp-B` (G1), direct `cpW` decrease
data NodeBEvR-abs-wt (nb : SN.NodeStateB) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                     (M : NetProc) : Set₁ where
  nbEBawt : (nb′ : SN.NodeStateB) → M ≡ absNodeB nb′
          → SN.decNodeB nb ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeB nb′
          → cpW (SN.NodeStateB.cp-B nb′) < cpW (SN.NodeStateB.cp-B nb)
          → NodeBEvR-abs-wt nb e a M

-- node C: fires the relay `cp-C` (G2), direct `cpW` decrease
data NodeCEvR-abs-wt (nc : SN.NodeStateC) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                     (M : NetProc) : Set₁ where
  ncEBawt : (nc′ : SN.NodeStateC) → M ≡ absNodeC nc′
          → SN.decNodeC nc ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeC nc′
          → cpW (SN.NodeStateC.cp-C nc′) < cpW (SN.NodeStateC.cp-C nc)
          → NodeCEvR-abs-wt nc e a M

-- node D: fires consume on link BD (G1) or CD (G2)
data NodeDEvR-abs-wt (nd : SN.NodeStateD) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                     (M : NetProc) : Set₁ where
  ndEBawt1 : (nd′ : SN.NodeStateD) → M ≡ absNodeD nd′
           → SN.decNodeD nd ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeD nd′
           → ConsAdv (cph (SN.NodeStateD.cons-BD nd)) (cph (SN.NodeStateD.cons-BD nd′))
           → SN.NodeStateD.cons-CD nd′ ≡ SN.NodeStateD.cons-CD nd
           -- delivering-hop label: if D's BD-consume is at cp3, the fired event is
           -- exactly `apiBF linkBD hi recvBFBlock` carrying the received block `b″`
           -- — SESSION-36 ANCHOR: and `b″` is the block the SUCCESSOR slot records,
           -- so a state-side value invariant at `nd′` reaches the label's block
           → (cph (SN.NodeStateD.cons-BD nd) ≡ cp3
              → Σ[ b″ ∈ Block₃ ]
                  (evLabel X e a ≡ evLabel Block₃ (apiBF linkBD hi recvBFBlock) b″)
                × (cblk (SN.NodeStateD.cons-BD nd′) ≡ b″))
           → NodeDEvR-abs-wt nd e a M
  ndEBawt2 : (nd′ : SN.NodeStateD) → M ≡ absNodeD nd′
           → SN.decNodeD nd ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeD nd′
           → ConsAdv (cph (SN.NodeStateD.cons-CD nd)) (cph (SN.NodeStateD.cons-CD nd′))
           → SN.NodeStateD.cons-BD nd′ ≡ SN.NodeStateD.cons-BD nd
           -- delivering-hop label: if D's CD-consume is at cp3, the fired event is
           -- exactly `apiBF linkCD hi recvBFBlock` carrying the received block `b″`
           -- — SESSION-36 ANCHOR (mirror of `ndEBawt1`'s)
           → (cph (SN.NodeStateD.cons-CD nd) ≡ cp3
              → Σ[ b″ ∈ Block₃ ]
                  (evLabel X e a ≡ evLabel Block₃ (apiBF linkCD hi recvBFBlock) b″)
                × (cblk (SN.NodeStateD.cons-CD nd′) ≡ b″))
           → NodeDEvR-abs-wt nd e a M

------------------------------------------------------------------------
-- node-A API peel (two produce drivers, dirs AB / AC)
------------------------------------------------------------------------

-- firing link = linkAB (G1)
nodeA-api-AB-abs-wt : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁AB : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
     ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ─[ ev (evl (evLabel X e a)) ]─► D₁AB
  → ApiHasLink linkAB e
  → NodeAEvR-abs-wt na e a (B₁ ∥⇘ apiES ⇙ (D₁AB ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)))
nodeA-api-AB-abs-wt na {X} {e} {a} apimem bStep sDAB ahl
  with prodAdv-of linkAB hi blkA (SN.NodeStateA.prod-AB na) sDAB
... | pp′ , refl , padv
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
           (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) bStep
...   | PEA.evSync () _ _
...   | PEA.evR _ sBAC = ⊥-elim (absBundleG-api-no linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) ahl linkAB≢linkAC apimem (_ , sBAC))
...   | PEA.evBoth _ _ sBAC = ⊥-elim (absBundleG-api-no linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) ahl linkAB≢linkAC apimem (_ , sBAC))
...   | PEA.evL _ sBAB
      with absBundleG-api-prod linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) apimem sBAB
...     | bgEB csc′ css′ bfc′ bfs′ ip′ eq run =
          naEBawt1 (SN.mkNodeA csc′ css′ bfc′ bfs′ pp′ (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) ip′ (SN.NodeStateA.inert-AC na))
            (cong (λ z → (z ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA pp′ ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na))) eq)
            (∥⇘⇙-wev-sync apiES _ _ apimem
               (⦀-wev-L _ _ (noOffer→viewV _ (bundleG-api-no linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) ahl linkAB≢linkAC apimem)) run)
               (ev→wev (⦀-ev-L (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na)) _ sDAB (noOffer→viewV _ (drvA-AC-no na ahl)))))
            padv refl

-- firing link = linkAC (G2)
nodeA-api-AC-abs-wt : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁AC : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
     ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na) ─[ ev (evl (evLabel X e a)) ]─► D₁AC
  → ApiHasLink linkAC e
  → NodeAEvR-abs-wt na e a (B₁ ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ D₁AC))
nodeA-api-AC-abs-wt na {X} {e} {a} apimem bStep sDAC ahl
  with prodAdv-of linkAC hi blkA (SN.NodeStateA.prod-AC na) sDAC
... | pp′ , refl , padv
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
           (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) bStep
...   | PEA.evSync () _ _
...   | PEA.evL _ sBAB = ⊥-elim (absBundleG-api-no linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ahl (λ q → linkAB≢linkAC (sym q)) apimem (_ , sBAB))
...   | PEA.evBoth _ sBAB _ = ⊥-elim (absBundleG-api-no linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ahl (λ q → linkAB≢linkAC (sym q)) apimem (_ , sBAB))
...   | PEA.evR _ sBAC
      with absBundleG-api-prod linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) apimem sBAC
...     | bgEB csc′ css′ bfc′ bfs′ ip′ eq run =
          naEBawt2 (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na) csc′ css′ bfc′ bfs′ pp′ (SN.NodeStateA.inert-AB na) ip′)
            (cong (λ z → (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ⦀ z) ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA pp′)) eq)
            (∥⇘⇙-wev-sync apiES _ _ apimem
               (⦀-wev-R _ _ (noOffer→viewV _ (bundleG-api-no linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ahl (λ q → linkAB≢linkAC (sym q)) apimem)) run)
               (ev→wev (⦀-ev-R _ (SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)) sDAC (noOffer→viewV _ (drvA-AB-no na ahl)))))
            padv refl

-- node-A api inversion: reflect the driver↔bundle sync, peel the driver `⦀`, dispatch
nodeA-ev-api-abs-wt : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeA na ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeAEvR-abs-wt na e a M
nodeA-ev-api-abs-wt na {X} {e} {a} apimem step
  with SStep.reflect-node-api
         (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
          ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
         (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na)) (SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)) dStep
... | PEA.evSync () _ _
... | PEA.evL _ sDAB = nodeA-api-AB-abs-wt na apimem bStep sDAB (decProd-ev-link linkAB hi blkA (SN.NodeStateA.prod-AB na) sDAB)
... | PEA.evR _ sDAC = nodeA-api-AC-abs-wt na apimem bStep sDAC (decProd-ev-link linkAC hi blkA (SN.NodeStateA.prod-AC na) sDAC)
... | PEA.evBoth _ sDAB sDAC = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (decProd-ev-link linkAB hi blkA (SN.NodeStateA.prod-AB na) sDAB)
                     (decProd-ev-link linkAC hi blkA (SN.NodeStateA.prod-AC na) sDAC)))

------------------------------------------------------------------------
-- node-D API peel (two consume drivers, dirs BD / CD)
------------------------------------------------------------------------

-- firing link = linkBD (G1)
nodeD-api-BD-abs-wt : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁BD : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
     ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ─[ ev (evl (evLabel X e a)) ]─► D₁BD
  → ApiHasLink linkBD e
  → NodeDEvR-abs-wt nd e a (B₁ ∥⇘ apiES ⇙ (D₁BD ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)))
nodeD-api-BD-abs-wt nd {X} {e} {a} apimem bStep sDBD ahl
  with consDAdv-of⁺ linkBD (SN.NodeStateD.cons-BD nd) sDBD
... | b′ , cp′ , refl , cadv , lblv , _
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
           (absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) bStep
...   | PEA.evSync () _ _
...   | PEA.evR _ sBCD = ⊥-elim (absBundleG-api-no linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) ahl linkBD≢linkCD apimem (_ , sBCD))
...   | PEA.evBoth _ _ sBCD = ⊥-elim (absBundleG-api-no linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) ahl linkBD≢linkCD apimem (_ , sBCD))
...   | PEA.evL _ sBBD
      with absBundleG-api-prod linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) apimem sBBD
...     | bgEB csc′ css′ bfc′ bfs′ ip′ eq run =
          ndEBawt1 (SN.mkNodeD csc′ css′ bfc′ bfs′ (consD b′ cp′) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) ip′ (SN.NodeStateD.inert-CD nd))
            (cong (λ z → (z ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) ∥⇘ apiES ⇙ (SN.decConsD linkBD (consD b′ cp′) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))) eq)
            (∥⇘⇙-wev-sync apiES _ _ apimem
               (⦀-wev-L _ _ (noOffer→viewV _ (bundleG-api-no linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) ahl linkBD≢linkCD apimem)) run)
               (ev→wev (⦀-ev-L (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd)) _ sDBD (noOffer→viewV _ (drvD-CD-no nd ahl)))))
            -- SESSION-36: the anchored classifier already pins the delivering
            -- label at `b′`, and `nd′`'s BD slot IS `consD b′ cp′`, so the
            -- successor-value conjunct is `refl` (inlined, not a `where` block:
            -- the field's type mentions `nd′`, which is written inline above)
            cadv refl (λ hcp → b′ , lblv hcp , refl)

-- firing link = linkCD (G2)
nodeD-api-CD-abs-wt : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁CD : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
     ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decConsD linkCD (SN.NodeStateD.cons-CD nd) ─[ ev (evl (evLabel X e a)) ]─► D₁CD
  → ApiHasLink linkCD e
  → NodeDEvR-abs-wt nd e a (B₁ ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ D₁CD))
nodeD-api-CD-abs-wt nd {X} {e} {a} apimem bStep sDCD ahl
  with consDAdv-of⁺ linkCD (SN.NodeStateD.cons-CD nd) sDCD
... | b′ , cp′ , refl , cadv , lblv , _
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
           (absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) bStep
...   | PEA.evSync () _ _
...   | PEA.evL _ sBBD = ⊥-elim (absBundleG-api-no linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ahl (λ q → linkBD≢linkCD (sym q)) apimem (_ , sBBD))
...   | PEA.evBoth _ sBBD _ = ⊥-elim (absBundleG-api-no linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ahl (λ q → linkBD≢linkCD (sym q)) apimem (_ , sBBD))
...   | PEA.evR _ sBCD
      with absBundleG-api-prod linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) apimem sBCD
...     | bgEB csc′ css′ bfc′ bfs′ ip′ eq run =
          ndEBawt2 (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd) csc′ css′ bfc′ bfs′ (consD b′ cp′) (SN.NodeStateD.inert-BD nd) ip′)
            (cong (λ z → (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ⦀ z) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (consD b′ cp′))) eq)
            (∥⇘⇙-wev-sync apiES _ _ apimem
               (⦀-wev-R _ _ (noOffer→viewV _ (bundleG-api-no linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ahl (λ q → linkBD≢linkCD (sym q)) apimem)) run)
               (ev→wev (⦀-ev-R _ (SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)) sDCD (noOffer→viewV _ (drvD-BD-no nd ahl)))))
            -- SESSION-36 anchor (mirror of the BD site)
            cadv refl (λ hcp → b′ , lblv hcp , refl)

-- node-D api inversion
nodeD-ev-api-abs-wt : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeD nd ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeDEvR-abs-wt nd e a M
nodeD-ev-api-abs-wt nd {X} {e} {a} apimem step
  with SStep.reflect-node-api
         (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
          ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
         (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd)) (SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)) dStep
... | PEA.evSync () _ _
... | PEA.evL _ sDBD = nodeD-api-BD-abs-wt nd apimem bStep sDBD (decConsD-ev-link linkBD (SN.NodeStateD.cons-BD nd) sDBD)
... | PEA.evR _ sDCD = nodeD-api-CD-abs-wt nd apimem bStep sDCD (decConsD-ev-link linkCD (SN.NodeStateD.cons-CD nd) sDCD)
... | PEA.evBoth _ sDBD sDCD = ⊥-elim (linkBD≢linkCD
        (apiLink-inj (decConsD-ev-link linkBD (SN.NodeStateD.cons-BD nd) sDBD)
                     (decConsD-ev-link linkCD (SN.NodeStateD.cons-CD nd) sDCD)))

------------------------------------------------------------------------
-- node-B API peel (single relay `decCP` driver; G1; direct cpW drop)
------------------------------------------------------------------------

-- firing link = linkAB (consume leg, LEFT bundle)
nodeB-api-AB-abs-wt : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁ : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
     ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb) ─[ ev (evl (evLabel X e a)) ]─► D₁
  → ApiHasLink linkAB e
  → NodeBEvR-abs-wt nb e a (B₁ ∥⇘ apiES ⇙ D₁)
nodeB-api-AB-abs-wt nb {X} {e} {a} apimem bStep dStep ahl
  with cpAdv-of linkAB linkBD (SN.NodeStateB.cp-B nb) dStep
... | x′ , refl , cpdrop
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb))
           (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)) bStep
...   | PEA.evSync () _ _
...   | PEA.evR _ sBBD = ⊥-elim (absBundleG-api-no linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) ahl linkAB≢linkBD apimem (_ , sBBD))
...   | PEA.evBoth _ _ sBBD = ⊥-elim (absBundleG-api-no linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) ahl linkAB≢linkBD apimem (_ , sBBD))
...   | PEA.evL _ sBAB
      with absBundleG-api-prod linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) apimem sBAB
...     | bgEB csc′ css′ bfc′ bfs′ ip′ eq run =
          nbEBawt (SN.mkNodeB csc′ css′ bfc′ bfs′ (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) x′ ip′ (SN.NodeStateB.inert-BD nb))
            (cong (λ z → (z ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD x′) eq)
            (∥⇘⇙-wev-sync apiES _ _ apimem
               (⦀-wev-L _ _ (noOffer→viewV _ (bundleG-api-no linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) ahl linkAB≢linkBD apimem)) run)
               (ev→wev dStep))
            cpdrop

-- firing link = linkBD (produce leg, RIGHT bundle)
nodeB-api-BD-abs-wt : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁ : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
     ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb) ─[ ev (evl (evLabel X e a)) ]─► D₁
  → ApiHasLink linkBD e
  → NodeBEvR-abs-wt nb e a (B₁ ∥⇘ apiES ⇙ D₁)
nodeB-api-BD-abs-wt nb {X} {e} {a} apimem bStep dStep ahl
  with cpAdv-of linkAB linkBD (SN.NodeStateB.cp-B nb) dStep
... | x′ , refl , cpdrop
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb))
           (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)) bStep
...   | PEA.evSync () _ _
...   | PEA.evL _ sBAB = ⊥-elim (absBundleG-api-no linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ahl (λ q → linkAB≢linkBD (sym q)) apimem (_ , sBAB))
...   | PEA.evBoth _ sBAB _ = ⊥-elim (absBundleG-api-no linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ahl (λ q → linkAB≢linkBD (sym q)) apimem (_ , sBAB))
...   | PEA.evR _ sBBD
      with absBundleG-api-prod linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) apimem sBBD
...     | bgEB csc′ css′ bfc′ bfs′ ip′ eq run =
          nbEBawt (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) csc′ css′ bfc′ bfs′ x′ (SN.NodeStateB.inert-AB nb) ip′)
            (cong (λ z → (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ⦀ z) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD x′) eq)
            (∥⇘⇙-wev-sync apiES _ _ apimem
               (⦀-wev-R _ _ (noOffer→viewV _ (bundleG-api-no linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ahl (λ q → linkAB≢linkBD (sym q)) apimem)) run)
               (ev→wev dStep))
            cpdrop

-- node-B api inversion
nodeB-ev-api-abs-wt : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeB nb ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeBEvR-abs-wt nb e a M
nodeB-ev-api-abs-wt nb {X} {e} {a} apimem step
  with SStep.reflect-node-api
         (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
          ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
         (SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with decCP-ev-link linkAB linkBD (SN.NodeStateB.cp-B nb) dStep
... | inj₁ ahl = nodeB-api-AB-abs-wt nb apimem bStep dStep ahl
... | inj₂ ahl = nodeB-api-BD-abs-wt nb apimem bStep dStep ahl

------------------------------------------------------------------------
-- node-C API peel (single relay `decCP` driver; G2; direct cpW drop)
------------------------------------------------------------------------

-- firing link = linkAC (consume leg, LEFT bundle)
nodeC-api-AC-abs-wt : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁ : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
     ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc) ─[ ev (evl (evLabel X e a)) ]─► D₁
  → ApiHasLink linkAC e
  → NodeCEvR-abs-wt nc e a (B₁ ∥⇘ apiES ⇙ D₁)
nodeC-api-AC-abs-wt nc {X} {e} {a} apimem bStep dStep ahl
  with cpAdv-of linkAC linkCD (SN.NodeStateC.cp-C nc) dStep
... | x′ , refl , cpdrop
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc))
           (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)) bStep
...   | PEA.evSync () _ _
...   | PEA.evR _ sBCD = ⊥-elim (absBundleG-api-no linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) ahl linkAC≢linkCD apimem (_ , sBCD))
...   | PEA.evBoth _ _ sBCD = ⊥-elim (absBundleG-api-no linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) ahl linkAC≢linkCD apimem (_ , sBCD))
...   | PEA.evL _ sBAC
      with absBundleG-api-prod linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) apimem sBAC
...     | bgEB csc′ css′ bfc′ bfs′ ip′ eq run =
          ncEBawt (SN.mkNodeC csc′ css′ bfc′ bfs′ (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) x′ ip′ (SN.NodeStateC.inert-CD nc))
            (cong (λ z → (z ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD x′) eq)
            (∥⇘⇙-wev-sync apiES _ _ apimem
               (⦀-wev-L _ _ (noOffer→viewV _ (bundleG-api-no linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) ahl linkAC≢linkCD apimem)) run)
               (ev→wev dStep))
            cpdrop

-- firing link = linkCD (produce leg, RIGHT bundle)
nodeC-api-CD-abs-wt : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁ : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
     ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc) ─[ ev (evl (evLabel X e a)) ]─► D₁
  → ApiHasLink linkCD e
  → NodeCEvR-abs-wt nc e a (B₁ ∥⇘ apiES ⇙ D₁)
nodeC-api-CD-abs-wt nc {X} {e} {a} apimem bStep dStep ahl
  with cpAdv-of linkAC linkCD (SN.NodeStateC.cp-C nc) dStep
... | x′ , refl , cpdrop
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc))
           (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)) bStep
...   | PEA.evSync () _ _
...   | PEA.evL _ sBAC = ⊥-elim (absBundleG-api-no linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ahl (λ q → linkAC≢linkCD (sym q)) apimem (_ , sBAC))
...   | PEA.evBoth _ sBAC _ = ⊥-elim (absBundleG-api-no linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ahl (λ q → linkAC≢linkCD (sym q)) apimem (_ , sBAC))
...   | PEA.evR _ sBCD
      with absBundleG-api-prod linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) apimem sBCD
...     | bgEB csc′ css′ bfc′ bfs′ ip′ eq run =
          ncEBawt (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) csc′ css′ bfc′ bfs′ x′ (SN.NodeStateC.inert-AC nc) ip′)
            (cong (λ z → (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ⦀ z) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD x′) eq)
            (∥⇘⇙-wev-sync apiES _ _ apimem
               (⦀-wev-R _ _ (noOffer→viewV _ (bundleG-api-no linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ahl (λ q → linkAC≢linkCD (sym q)) apimem)) run)
               (ev→wev dStep))
            cpdrop

-- node-C api inversion
nodeC-ev-api-abs-wt : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeC nc ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeCEvR-abs-wt nc e a M
nodeC-ev-api-abs-wt nc {X} {e} {a} apimem step
  with SStep.reflect-node-api
         (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
          ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
         (SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with decCP-ev-link linkAC linkCD (SN.NodeStateC.cp-C nc) dStep
... | inj₁ ahl = nodeC-api-AC-abs-wt nc apimem bStep dStep ahl
... | inj₂ ahl = nodeC-api-CD-abs-wt nc apimem bStep dStep ahl

------------------------------------------------------------------------
-- `top-nodes-abs-wt`: lift the firing node's driver advance to the whole
-- `μTot` strict decrease (the OTHER group + break budget fixed).
------------------------------------------------------------------------

top-nodes-abs-wt : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → SStep.absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ s′ ∈ SysState ] (med s ≡ med s′) × (M ≡ SStep.absNodesOf s′) × (SStep.nodesOf s ═[ ev (evl (evLabel X e a)) ]═► SStep.nodesOf s′) × (μTot s′ < μTot s)
top-nodes-abs-wt s apimem nodesStep
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
  where
    fpA = absNodeA-fp (nA s) apimem sA
    wrunA = ⦀-wev-L (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
              (noOffer→viewV _ (SStep.⦀-noOffer (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
                 (nodeB-no-when-A (nB s) apimem fpA)
                 (SStep.⦀-noOffer (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                    (nodeC-no-when-A (nC s) apimem fpA) (nodeD-no-when-A (nD s) apimem fpA))))
              weakRunA
top-nodes-abs-wt s apimem nodesStep | PEA.evR _ sRest
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
  where fpB = absNodeB-fp (nB s) apimem sB
top-nodes-abs-wt s apimem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD
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
  where fpC = absNodeC-fp (nC s) apimem sC
top-nodes-abs-wt s apimem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD | PEA.evR _ sD
    with nodeD-ev-api-abs-wt (nD s) apimem sD
... | ndEBawt1 nd′ Meq weakRunD cadv cCDeq _ =
        mkSys (med s) (nA s) (nB s) (nC s) nd′ , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ z))) Meq ,
        wrunD ,
        μTot-adv-G1 s (mkSys (med s) (nA s) (nB s) (nC s) nd′)
          (μG1-adv-cons s (mkSys (med s) (nA s) (nB s) (nC s) nd′) refl refl cadv)
          (sym (μG2-cong s (mkSys (med s) (nA s) (nB s) (nC s) nd′) refl refl (sym cCDeq)))
          refl
  where
    fpD = absNodeD-fp (nD s) apimem sD
    wrunD = ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
              (noOffer→viewV _ (nodeA-no-when-D (nA s) apimem fpD))
              (⦀-wev-R (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
                 (noOffer→viewV _ (nodeB-no-when-D (nB s) apimem fpD))
                 (⦀-wev-R (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                    (noOffer→viewV _ (nodeC-no-when-D (nC s) apimem fpD))
                    weakRunD))
... | ndEBawt2 nd′ Meq weakRunD cadv cBDeq _ =
        mkSys (med s) (nA s) (nB s) (nC s) nd′ , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ z))) Meq ,
        wrunD ,
        μTot-adv-G2 s (mkSys (med s) (nA s) (nB s) (nC s) nd′)
          (sym (μG1-cong s (mkSys (med s) (nA s) (nB s) (nC s) nd′) refl refl (sym cBDeq)))
          (μG2-adv-cons s (mkSys (med s) (nA s) (nB s) (nC s) nd′) refl refl cadv)
          refl
  where
    fpD = absNodeD-fp (nD s) apimem sD
    wrunD = ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
              (noOffer→viewV _ (nodeA-no-when-D (nA s) apimem fpD))
              (⦀-wev-R (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
                 (noOffer→viewV _ (nodeB-no-when-D (nB s) apimem fpD))
                 (⦀-wev-R (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                    (noOffer→viewV _ (nodeC-no-when-D (nC s) apimem fpD))
                    weakRunD))
