{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the per-peer BF-CLIENT FIXITY api node cone
-- (`Praos.PipeNodeFixApi`).
--
-- The io analogue `PipeNodeFix.top-nodes-io-abs-client-cls` classifies the four
-- `PipeInv`-tracked BF-client peers across a hidden io-sync.  This module builds
-- the VISIBLE api-CSBF MIDDLE analogue `top-nodes-abs-expose-cls`: it re-mirrors
-- `WalkDExpose.top-nodes-abs-expose` (the api node exposure cone that carries the
-- nodeD `DReport` + the whole-`μTot` strict drop) and ADDITIONALLY returns the
-- whole-nodes client classifier `AllClientClass`.
--
-- SCOPE (session 13): the api peels differ from the io peels — an api-CSBF event
-- is a bundle↔DRIVER SYNC (`SStep.reflect-node-api` / `∥⇘⇙-wev-sync`), whereas an
-- io-sync is a solo bundle pass-through (`∥⇘⇙-wev-soloL`).  BUT the concrete
-- successor node still exposes `bfc′` the SAME way: `absBundleG-api-prod` returns
-- `bgEB csc′ css′ bfc′ bfs′ ip′ eq run` with `bfc′` concrete, built into the
-- literal `mkNodeX`.  So the `PipeNodeFix` technique transfers verbatim: re-derive
-- each api peel keeping `mkNodeX` concrete, replace nothing (KEEP the driver
-- delta + `DReport` witnesses for the drop) and ADD the per-client `ClientClass1`
-- — the fired bundle's tracked BF-client `clAdv (adv-of … bfc′)`, the co-located
-- non-fired peer `clFix refl` (a LITERAL in the `mkNodeX`).  Node A hosts NO
-- tracked client, so it reuses the FROZEN `WalkApiDrop.nodeA-ev-api-abs-wt` and
-- all four clients are `clFix refl`.
--
-- Re-mirrors `WalkApiDrop`'s api peels + `WalkDExpose.top-nodes-abs-expose`
-- VERBATIM for the reachability/drop/`DReport`.  No postulate/hole/meta.  All
-- base modules READ-ONLY.
------------------------------------------------------------------------

open import Data.Nat using ( ℕ; _<_; _+_ )
open import Data.Nat.Properties using ( +-monoˡ-<; +-monoʳ-< )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Archive.PipeNodeFixApi (blkA : Block₃) where

open import Level using (0ℓ)
open import Data.Product using ( _,_; Σ; _×_; Σ-syntax )
open import Data.Maybe using ( nothing )
open import Data.Empty using ( ⊥-elim )
open import Data.Unit.Polymorphic using ( tt )
open import Relation.Nullary using ( yes; no; ¬_ )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; cong; trans; sym; _≢_; subst )
open import Data.Sum using ( inj₁; inj₂; _⊎_ )
open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using
  ( p; apiES; linkAB; linkAC; linkBD; linkCD; Block₃ )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟ )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel; τ )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[τ*]─►_; τ*-refl; τ*-step; τ*-trans; _═[_]═►_; wev )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; EventSet; viewV )
open EventSet using ( mem )
open Op using () renaming ( ∅ES to ∅ESa )

import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep
open SStep using
  ( NetProc; IoOffers
  ; ⦀-ev-L; ⦀-ev-R )

open import CSP.Examples.Cardano_network.Base using ( Dir; lo; hi )
open import CSP.Examples.Cardano_network.Net p using ( Link; apiBF; recvBFBlock )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )
open SStep using
  ( absBundleG; absNodeA; absNodeB; absNodeC; absNodeD )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using
  ( ProdPh; ConsPh; CPPh; consuming; producing; consD; cph; cblk; cp3
  ; prod-AB; prod-AC; cp-B; cp-C; cons-BD; cons-CD )
import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload}) as PEA

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA using
  ( ApiHasLink; apiLink-inj; io⇒¬api
  ; decProd-ev-link; decConsD-ev-link; decCP-ev-link )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA using
  ( SysState; mkSys; med; nA; nB; nC; nD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysRoute blkA using
  ( absNodeA-fp; absNodeB-fp; absNodeC-fp; absNodeD-fp
  ; nodeB-no-when-A; nodeC-no-when-A; nodeD-no-when-A; nodeC-no-when-B; nodeD-no-when-B; nodeD-no-when-C
  ; absNodeB-no-when-A; absNodeC-no-when-A; absNodeD-no-when-A; absNodeC-no-when-B; absNodeD-no-when-B; absNodeD-no-when-C )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink blkA using
  ( linkAB≢linkAC; linkAB≢linkBD; linkAC≢linkCD; linkBD≢linkCD )

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

open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkClassify blkA using
  ( prodAdv-of; consDAdv-of; cpAdv-of; consD-c34-lbl )
-- SESSION-36: the VALUE-ANCHORED node-D classifier (mirror of `WalkApiDrop`'s)
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkDAnchor blkA using
  ( consDAdv-of⁺ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkMeasure blkA using
  ( ProdAdv; ConsAdv; cpW; prodW; consW; consDW
  ; μG1; μG2; μG1-cong; μG2-cong
  ; μG1-adv-prod; μG1-adv-cons; μG2-adv-prod; μG2-adv-cons )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.Walk blkA using
  ( μTot; μTot-adv-G1; μTot-adv-G2; breakBudget )

-- the nodeD D-phase report + the frozen node-A api peel (node A has no client)
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkDExpose blkA using
  ( DReport; dFix; dBD; dCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkApiDrop blkA using
  ( NodeAEvR-abs-wt; naEBawt1; naEBawt2; nodeA-ev-api-abs-wt )

-- the genuine per-client classifier algebra (reuse from the io node cone)
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Archive.PipeNodeFix blkA using
  ( ClientClass1; clFix; clAdv; AllClientClass )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Archive.PipeExposeNode blkA using
  ( ClientAdv; adv-of )
-- the io-sync driver-fixity cone (τ-run substrate for the prod/relay classes)
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvNodeFix blkA using
  ( top-nodes-io-abs-fix )
-- the leg-indexed producer / relay accessors + the permissive advance algebras
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA using
  ( prodOf; relayOf )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA using
  ( TwoLegs; legBD; legCD )
import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Archive.PipeExposeNodeProd blkA as PPr
import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Archive.PipeExposeNodeRelay blkA as PRl

------------------------------------------------------------------------
-- The genuine PRODUCER + RELAY per-driver CLASSIFIERS (the `ClientClass1`
-- shape, reusing the permissive advance algebras of `PipeExposeNodeProd`/
-- `PipeExposeNodeRelay` for the `Adv` case): either FIXED (a `≡`, the datum a
-- `PipeStep⁺` core needs) or ADVANCED (a concrete `ProdAdv`/`RelayAdv`).
------------------------------------------------------------------------

-- one producer's classification across a step/run
data ProdClass1 (a b : SN.ProdPh) : Set where
  pcFix : a ≡ b           → ProdClass1 a b
  pcAdv : PPr.ProdAdv a b → ProdClass1 a b

-- one relay's classification across a step/run
data RelayClass1 (a b : SN.CPPh) : Set where
  rcFix : a ≡ b           → RelayClass1 a b
  rcAdv : PRl.RelayAdv a b → RelayClass1 a b

-- compose two producer classifications (a τ-run fold)
pcFold : ∀ {a b c} → ProdClass1 a b → ProdClass1 b c → ProdClass1 a c
pcFold             (pcFix p) (pcFix q) = pcFix (trans p q)
pcFold {a} {b} {c} (pcFix p) (pcAdv g) = pcAdv (subst (λ z → PPr.ProdAdv z c) (sym p) g)
pcFold {a} {b} {c} (pcAdv f) (pcFix q) = pcAdv (subst (PPr.ProdAdv a) q f)
pcFold             (pcAdv f) (pcAdv g) = pcAdv (PPr.pl-trans f g)

-- compose two relay classifications (a τ-run fold)
rcFold : ∀ {a b c} → RelayClass1 a b → RelayClass1 b c → RelayClass1 a c
rcFold             (rcFix p) (rcFix q) = rcFix (trans p q)
rcFold {a} {b} {c} (rcFix p) (rcAdv g) = rcAdv (subst (λ z → PRl.RelayAdv z c) (sym p) g)
rcFold {a} {b} {c} (rcAdv f) (rcFix q) = rcAdv (subst (PRl.RelayAdv a) q f)
rcFold             (rcAdv f) (rcAdv g) = rcAdv (PRl.rl-trans f g)

-- whole-nodes producer classifier: a `ProdClass1` for each tracked producer
AllProdClass : SysState → SysState → Set
AllProdClass s s′ =
    ProdClass1 (prodOf legBD s) (prodOf legBD s′)
  × ProdClass1 (prodOf legCD s) (prodOf legCD s′)

allProdClass-refl : (s : SysState) → AllProdClass s s
allProdClass-refl s = pcFix refl , pcFix refl

allProdClass-trans : (s s₁ s₂ : SysState)
                   → AllProdClass s s₁ → AllProdClass s₁ s₂ → AllProdClass s s₂
allProdClass-trans s s₁ s₂ (u₁ , v₁) (u₂ , v₂) = pcFold u₁ u₂ , pcFold v₁ v₂

-- whole-nodes relay classifier: a `RelayClass1` for each tracked relay
AllRelayClass : SysState → SysState → Set
AllRelayClass s s′ =
    RelayClass1 (relayOf legBD s) (relayOf legBD s′)
  × RelayClass1 (relayOf legCD s) (relayOf legCD s′)

allRelayClass-refl : (s : SysState) → AllRelayClass s s
allRelayClass-refl s = rcFix refl , rcFix refl

allRelayClass-trans : (s s₁ s₂ : SysState)
                    → AllRelayClass s s₁ → AllRelayClass s₁ s₂ → AllRelayClass s s₂
allRelayClass-trans s s₁ s₂ (u₁ , v₁) (u₂ , v₂) = rcFold u₁ u₂ , rcFold v₁ v₂

------------------------------------------------------------------------
-- Per-node api peel records: WalkApiDrop's `-wt` fields (successor node, node
-- weak run, driver advance, `DReport` witnesses for the drop) PLUS the
-- per-tracked-client `ClientClass1` for the node's tracked BF-client peer(s).
------------------------------------------------------------------------

-- node B hosts ONE tracked client (bfC-AB)
data NodeBEvR-acls (nb : SN.NodeStateB) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                   (M : NetProc) : Set₁ where
  nbEBacls : (nb′ : SN.NodeStateB) → M ≡ absNodeB nb′
           → SN.decNodeB nb ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeB nb′
           → cpW (SN.NodeStateB.cp-B nb′) < cpW (SN.NodeStateB.cp-B nb)
           → ClientClass1 (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfC-AB nb′)
           → NodeBEvR-acls nb e a M

-- node C hosts ONE tracked client (bfC-AC)
data NodeCEvR-acls (nc : SN.NodeStateC) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                   (M : NetProc) : Set₁ where
  ncEBacls : (nc′ : SN.NodeStateC) → M ≡ absNodeC nc′
           → SN.decNodeC nc ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeC nc′
           → cpW (SN.NodeStateC.cp-C nc′) < cpW (SN.NodeStateC.cp-C nc)
           → ClientClass1 (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfC-AC nc′)
           → NodeCEvR-acls nc e a M

-- node D hosts TWO tracked clients (bfC-BD, bfC-CD); carries the `DReport` shape
data NodeDEvR-acls (nd : SN.NodeStateD) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                   (M : NetProc) : Set₁ where
  ndEBacls1 : (nd′ : SN.NodeStateD) → M ≡ absNodeD nd′
            → SN.decNodeD nd ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeD nd′
            → ConsAdv (cph (SN.NodeStateD.cons-BD nd)) (cph (SN.NodeStateD.cons-BD nd′))
            → SN.NodeStateD.cons-CD nd′ ≡ SN.NodeStateD.cons-CD nd
            -- SESSION-36 ANCHOR: `b″` is the block the SUCCESSOR slot records
            → (cph (SN.NodeStateD.cons-BD nd) ≡ cp3
               → Σ[ b″ ∈ Block₃ ]
                   (evLabel X e a ≡ evLabel Block₃ (apiBF linkBD hi recvBFBlock) b″)
                 × (cblk (SN.NodeStateD.cons-BD nd′) ≡ b″))
            → ClientClass1 (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfC-BD nd′)
            → ClientClass1 (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfC-CD nd′)
            → NodeDEvR-acls nd e a M
  ndEBacls2 : (nd′ : SN.NodeStateD) → M ≡ absNodeD nd′
            → SN.decNodeD nd ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeD nd′
            → ConsAdv (cph (SN.NodeStateD.cons-CD nd)) (cph (SN.NodeStateD.cons-CD nd′))
            → SN.NodeStateD.cons-BD nd′ ≡ SN.NodeStateD.cons-BD nd
            -- SESSION-36 ANCHOR (mirror)
            → (cph (SN.NodeStateD.cons-CD nd) ≡ cp3
               → Σ[ b″ ∈ Block₃ ]
                   (evLabel X e a ≡ evLabel Block₃ (apiBF linkCD hi recvBFBlock) b″)
                 × (cblk (SN.NodeStateD.cons-CD nd′) ≡ b″))
            → ClientClass1 (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfC-BD nd′)
            → ClientClass1 (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfC-CD nd′)
            → NodeDEvR-acls nd e a M

------------------------------------------------------------------------
-- node-D api peels (re-mirror `WalkApiDrop.nodeD-api-{BD,CD}-abs-wt` VERBATIM,
-- keeping `mkNodeD` concrete): the fired bundle's BF-client `clAdv (adv-of …
-- bfc′)`, the co-located non-fired peer `clFix refl`.
------------------------------------------------------------------------

-- firing link = linkBD (G1): bfC-BD advances (fired), bfC-CD fixed (literal)
nodeD-api-BD-abs-cls : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁BD : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
     ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ─[ ev (evl (evLabel X e a)) ]─► D₁BD
  → ApiHasLink linkBD e
  → NodeDEvR-acls nd e a (B₁ ∥⇘ apiES ⇙ (D₁BD ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)))
nodeD-api-BD-abs-cls nd {X} {e} {a} apimem bStep sDBD ahl
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
          ndEBacls1 (SN.mkNodeD csc′ css′ bfc′ bfs′ (consD b′ cp′) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) ip′ (SN.NodeStateD.inert-CD nd))
            (cong (λ z → (z ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) ∥⇘ apiES ⇙ (SN.decConsD linkBD (consD b′ cp′) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))) eq)
            (∥⇘⇙-wev-sync apiES _ _ apimem
               (⦀-wev-L _ _ (noOffer→viewV _ (bundleG-api-no linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) ahl linkBD≢linkCD apimem)) run)
               (ev→wev (⦀-ev-L (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd)) _ sDBD (noOffer→viewV _ (drvD-CD-no nd ahl)))))
            -- SESSION-36: anchored classifier pins the label at `b′`; `nd′`'s BD
            -- slot IS `consD b′ cp′`, so the successor conjunct is `refl`
            cadv refl (λ hcp → b′ , lblv hcp , refl)
            (clAdv (adv-of (SN.NodeStateD.bfC-BD nd) bfc′))
            (clFix refl)

-- firing link = linkCD (G2): bfC-CD advances (fired), bfC-BD fixed (literal)
nodeD-api-CD-abs-cls : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁CD : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
     ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decConsD linkCD (SN.NodeStateD.cons-CD nd) ─[ ev (evl (evLabel X e a)) ]─► D₁CD
  → ApiHasLink linkCD e
  → NodeDEvR-acls nd e a (B₁ ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ D₁CD))
nodeD-api-CD-abs-cls nd {X} {e} {a} apimem bStep sDCD ahl
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
          ndEBacls2 (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd) csc′ css′ bfc′ bfs′ (consD b′ cp′) (SN.NodeStateD.inert-BD nd) ip′)
            (cong (λ z → (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ⦀ z) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (consD b′ cp′))) eq)
            (∥⇘⇙-wev-sync apiES _ _ apimem
               (⦀-wev-R _ _ (noOffer→viewV _ (bundleG-api-no linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ahl (λ q → linkBD≢linkCD (sym q)) apimem)) run)
               (ev→wev (⦀-ev-R _ (SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)) sDCD (noOffer→viewV _ (drvD-BD-no nd ahl)))))
            -- SESSION-36 anchor (mirror of the BD site)
            cadv refl (λ hcp → b′ , lblv hcp , refl)
            (clFix refl)
            (clAdv (adv-of (SN.NodeStateD.bfC-CD nd) bfc′))

-- node-D api inversion (mirror `WalkApiDrop.nodeD-ev-api-abs-wt`)
nodeD-ev-api-abs-cls : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeD nd ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeDEvR-acls nd e a M
nodeD-ev-api-abs-cls nd {X} {e} {a} apimem step
  with SStep.reflect-node-api
         (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
          ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
         (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd)) (SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)) dStep
... | PEA.evSync () _ _
... | PEA.evL _ sDBD = nodeD-api-BD-abs-cls nd apimem bStep sDBD (decConsD-ev-link linkBD (SN.NodeStateD.cons-BD nd) sDBD)
... | PEA.evR _ sDCD = nodeD-api-CD-abs-cls nd apimem bStep sDCD (decConsD-ev-link linkCD (SN.NodeStateD.cons-CD nd) sDCD)
... | PEA.evBoth _ sDBD sDCD = ⊥-elim (linkBD≢linkCD
        (apiLink-inj (decConsD-ev-link linkBD (SN.NodeStateD.cons-BD nd) sDBD)
                     (decConsD-ev-link linkCD (SN.NodeStateD.cons-CD nd) sDCD)))

------------------------------------------------------------------------
-- node-B api peels (relay `decCP` driver; tracked client bfC-AB)
------------------------------------------------------------------------

-- firing link = linkAB (consume leg, LEFT bundle): bfC-AB advances (fired)
nodeB-api-AB-abs-cls : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁ : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
     ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb) ─[ ev (evl (evLabel X e a)) ]─► D₁
  → ApiHasLink linkAB e
  → NodeBEvR-acls nb e a (B₁ ∥⇘ apiES ⇙ D₁)
nodeB-api-AB-abs-cls nb {X} {e} {a} apimem bStep dStep ahl
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
          nbEBacls (SN.mkNodeB csc′ css′ bfc′ bfs′ (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) x′ ip′ (SN.NodeStateB.inert-BD nb))
            (cong (λ z → (z ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD x′) eq)
            (∥⇘⇙-wev-sync apiES _ _ apimem
               (⦀-wev-L _ _ (noOffer→viewV _ (bundleG-api-no linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) ahl linkAB≢linkBD apimem)) run)
               (ev→wev dStep))
            cpdrop
            (clAdv (adv-of (SN.NodeStateB.bfC-AB nb) bfc′))

-- firing link = linkBD (produce leg, RIGHT bundle): bfC-AB fixed (literal)
nodeB-api-BD-abs-cls : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁ : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
     ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb) ─[ ev (evl (evLabel X e a)) ]─► D₁
  → ApiHasLink linkBD e
  → NodeBEvR-acls nb e a (B₁ ∥⇘ apiES ⇙ D₁)
nodeB-api-BD-abs-cls nb {X} {e} {a} apimem bStep dStep ahl
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
          nbEBacls (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) csc′ css′ bfc′ bfs′ x′ (SN.NodeStateB.inert-AB nb) ip′)
            (cong (λ z → (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ⦀ z) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD x′) eq)
            (∥⇘⇙-wev-sync apiES _ _ apimem
               (⦀-wev-R _ _ (noOffer→viewV _ (bundleG-api-no linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ahl (λ q → linkAB≢linkBD (sym q)) apimem)) run)
               (ev→wev dStep))
            cpdrop
            (clFix refl)

-- node-B api inversion
nodeB-ev-api-abs-cls : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeB nb ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeBEvR-acls nb e a M
nodeB-ev-api-abs-cls nb {X} {e} {a} apimem step
  with SStep.reflect-node-api
         (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
          ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
         (SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with decCP-ev-link linkAB linkBD (SN.NodeStateB.cp-B nb) dStep
... | inj₁ ahl = nodeB-api-AB-abs-cls nb apimem bStep dStep ahl
... | inj₂ ahl = nodeB-api-BD-abs-cls nb apimem bStep dStep ahl

------------------------------------------------------------------------
-- node-C api peels (relay `decCP` driver; tracked client bfC-AC)
------------------------------------------------------------------------

-- firing link = linkAC (consume leg, LEFT bundle): bfC-AC advances (fired)
nodeC-api-AC-abs-cls : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁ : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
     ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc) ─[ ev (evl (evLabel X e a)) ]─► D₁
  → ApiHasLink linkAC e
  → NodeCEvR-acls nc e a (B₁ ∥⇘ apiES ⇙ D₁)
nodeC-api-AC-abs-cls nc {X} {e} {a} apimem bStep dStep ahl
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
          ncEBacls (SN.mkNodeC csc′ css′ bfc′ bfs′ (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) x′ ip′ (SN.NodeStateC.inert-CD nc))
            (cong (λ z → (z ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD x′) eq)
            (∥⇘⇙-wev-sync apiES _ _ apimem
               (⦀-wev-L _ _ (noOffer→viewV _ (bundleG-api-no linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) ahl linkAC≢linkCD apimem)) run)
               (ev→wev dStep))
            cpdrop
            (clAdv (adv-of (SN.NodeStateC.bfC-AC nc) bfc′))

-- firing link = linkCD (produce leg, RIGHT bundle): bfC-AC fixed (literal)
nodeC-api-CD-abs-cls : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁ : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
     ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc) ─[ ev (evl (evLabel X e a)) ]─► D₁
  → ApiHasLink linkCD e
  → NodeCEvR-acls nc e a (B₁ ∥⇘ apiES ⇙ D₁)
nodeC-api-CD-abs-cls nc {X} {e} {a} apimem bStep dStep ahl
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
          ncEBacls (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) csc′ css′ bfc′ bfs′ x′ (SN.NodeStateC.inert-AC nc) ip′)
            (cong (λ z → (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ⦀ z) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD x′) eq)
            (∥⇘⇙-wev-sync apiES _ _ apimem
               (⦀-wev-R _ _ (noOffer→viewV _ (bundleG-api-no linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ahl (λ q → linkAC≢linkCD (sym q)) apimem)) run)
               (ev→wev dStep))
            cpdrop
            (clFix refl)

-- node-C api inversion
nodeC-ev-api-abs-cls : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeC nc ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeCEvR-acls nc e a M
nodeC-ev-api-abs-cls nc {X} {e} {a} apimem step
  with SStep.reflect-node-api
         (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
          ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
         (SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with decCP-ev-link linkAC linkCD (SN.NodeStateC.cp-C nc) dStep
... | inj₁ ahl = nodeC-api-AC-abs-cls nc apimem bStep dStep ahl
... | inj₂ ahl = nodeC-api-CD-abs-cls nc apimem bStep dStep ahl

------------------------------------------------------------------------
-- TOP: the whole-nodes api-CSBF BF-CLIENT CLASSIFIER `top-nodes-abs-expose-cls`.
-- Re-mirror of `WalkDExpose.top-nodes-abs-expose` (same 4-node dispatch, same
-- `DReport` + `μTot` drop) routing B/C/D through the per-peer classifier
-- dispatchers above (node A via the FROZEN `nodeA-ev-api-abs-wt`), ADDITIONALLY
-- returning the whole-nodes `AllClientClass`.  A non-firing node keeps its
-- clients `clFix refl` (its node is LITERAL in the successor `mkSys`).
------------------------------------------------------------------------

top-nodes-abs-expose-cls : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → SStep.absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ s′ ∈ SysState ] (med s ≡ med s′) × (M ≡ SStep.absNodesOf s′)
      × (SStep.nodesOf s ═[ ev (evl (evLabel X e a)) ]═► SStep.nodesOf s′)
      × (μTot s′ < μTot s) × DReport s s′ e a × AllClientClass s s′
      × AllProdClass s s′ × AllRelayClass s s′
top-nodes-abs-expose-cls s apimem nodesStep
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
        , (clFix refl , clFix refl , clFix refl , clFix refl)
        , (pcAdv (PPr.adv-of (SN.NodeStateA.prod-AB (nA s)) (SN.NodeStateA.prod-AB na′)) , pcFix (sym pACeq))
        , (rcFix refl , rcFix refl)
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
        , (clFix refl , clFix refl , clFix refl , clFix refl)
        , (pcFix (sym pABeq) , pcAdv (PPr.adv-of (SN.NodeStateA.prod-AC (nA s)) (SN.NodeStateA.prod-AC na′)))
        , (rcFix refl , rcFix refl)
  where
    fpA = absNodeA-fp (nA s) apimem sA
    wrunA = ⦀-wev-L (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
              (noOffer→viewV _ (SStep.⦀-noOffer (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
                 (nodeB-no-when-A (nB s) apimem fpA)
                 (SStep.⦀-noOffer (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                    (nodeC-no-when-A (nC s) apimem fpA) (nodeD-no-when-A (nD s) apimem fpA))))
              weakRunA
top-nodes-abs-expose-cls s apimem nodesStep | PEA.evR _ sRest
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s)) sRest
... | PEA.evSync () _ _
... | PEA.evBoth _ sB sCD = ⊥-elim (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
        (absNodeC-no-when-B (nC s) apimem (absNodeB-fp (nB s) apimem sB))
        (absNodeD-no-when-B (nD s) apimem (absNodeB-fp (nB s) apimem sB)) (_ , sCD))
... | PEA.evL _ sB with nodeB-ev-api-abs-cls (nB s) apimem sB
...   | nbEBacls nb′ Meq weakRunB cpdrop clsAB =
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
        , (clsAB , clFix refl , clFix refl , clFix refl)
        , (pcFix refl , pcFix refl)
        , (rcAdv (PRl.adv-of (SN.NodeStateB.cp-B (nB s)) (SN.NodeStateB.cp-B nb′)) , rcFix refl)
  where fpB = absNodeB-fp (nB s) apimem sB
top-nodes-abs-expose-cls s apimem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absNodeC (nC s)) (absNodeD (nD s)) sCD
... | PEA.evSync () _ _
... | PEA.evBoth _ sC sD = ⊥-elim (absNodeD-no-when-C (nD s) apimem (absNodeC-fp (nC s) apimem sC) (_ , sD))
... | PEA.evL _ sC with nodeC-ev-api-abs-cls (nC s) apimem sC
...   | ncEBacls nc′ Meq weakRunC cpdrop clsAC =
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
        , (clFix refl , clsAC , clFix refl , clFix refl)
        , (pcFix refl , pcFix refl)
        , (rcFix refl , rcAdv (PRl.adv-of (SN.NodeStateC.cp-C (nC s)) (SN.NodeStateC.cp-C nc′)))
  where fpC = absNodeC-fp (nC s) apimem sC
top-nodes-abs-expose-cls s apimem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD | PEA.evR _ sD
    with nodeD-ev-api-abs-cls (nD s) apimem sD
... | ndEBacls1 nd′ Meq weakRunD cadv cCDeq lblD clsBD clsCD =
        mkSys (med s) (nA s) (nB s) (nC s) nd′ , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ z))) Meq ,
        wrunD ,
        μTot-adv-G1 s (mkSys (med s) (nA s) (nB s) (nC s) nd′)
          (μG1-adv-cons s (mkSys (med s) (nA s) (nB s) (nC s) nd′) refl refl cadv)
          (sym (μG2-cong s (mkSys (med s) (nA s) (nB s) (nC s) nd′) refl refl (sym cCDeq)))
          refl
        , dBD cadv cCDeq lblD
        , (clFix refl , clFix refl , clsBD , clsCD)
        , (pcFix refl , pcFix refl)
        , (rcFix refl , rcFix refl)
  where
    fpD = absNodeD-fp (nD s) apimem sD
    wrunD = ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
              (noOffer→viewV _ (nodeA-no-when-D (nA s) apimem fpD))
              (⦀-wev-R (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
                 (noOffer→viewV _ (nodeB-no-when-D (nB s) apimem fpD))
                 (⦀-wev-R (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                    (noOffer→viewV _ (nodeC-no-when-D (nC s) apimem fpD))
                    weakRunD))
... | ndEBacls2 nd′ Meq weakRunD cadv cBDeq lblD clsBD clsCD =
        mkSys (med s) (nA s) (nB s) (nC s) nd′ , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ z))) Meq ,
        wrunD ,
        μTot-adv-G2 s (mkSys (med s) (nA s) (nB s) (nC s) nd′)
          (sym (μG1-cong s (mkSys (med s) (nA s) (nB s) (nC s) nd′) refl refl (sym cBDeq)))
          (μG2-adv-cons s (mkSys (med s) (nA s) (nB s) (nC s) nd′) refl refl cadv)
          refl
        , dCD cadv cBDeq lblD
        , (clFix refl , clFix refl , clsBD , clsCD)
        , (pcFix refl , pcFix refl)
        , (rcFix refl , rcFix refl)
  where
    fpD = absNodeD-fp (nD s) apimem sD
    wrunD = ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
              (noOffer→viewV _ (nodeA-no-when-D (nA s) apimem fpD))
              (⦀-wev-R (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
                 (noOffer→viewV _ (nodeB-no-when-D (nB s) apimem fpD))
                 (⦀-wev-R (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                    (noOffer→viewV _ (nodeC-no-when-D (nC s) apimem fpD))
                    weakRunD))

------------------------------------------------------------------------
-- The io-sync PRODUCER / RELAY classifiers (τ-run substrate): a hidden io-sync
-- leaves every DRIVER phase FIXED (`top-nodes-io-abs-fix` surfaces the six
-- driver fixities as `≡`), so every tracked producer/relay is `pcFix`/`rcFix`.
------------------------------------------------------------------------

top-nodes-io-abs-prod-cls : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → SStep.absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ s′ ∈ SysState ] (med s ≡ med s′) × (M ≡ SStep.absNodesOf s′)
      × (SStep.nodesOf s ═[ ev (evl (evLabel X e a)) ]═► SStep.nodesOf s′)
      × AllProdClass s s′
top-nodes-io-abs-prod-cls s iomem step with top-nodes-io-abs-fix s iomem step
... | s′ , meq , Meq , wrun , epAB , epAC , _ , _ , _ , _ =
      s′ , meq , Meq , wrun , (pcFix epAB , pcFix epAC)

top-nodes-io-abs-relay-cls : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → SStep.absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ s′ ∈ SysState ] (med s ≡ med s′) × (M ≡ SStep.absNodesOf s′)
      × (SStep.nodesOf s ═[ ev (evl (evLabel X e a)) ]═► SStep.nodesOf s′)
      × AllRelayClass s s′
top-nodes-io-abs-relay-cls s iomem step with top-nodes-io-abs-fix s iomem step
... | s′ , meq , Meq , wrun , _ , _ , ecpB , ecpC , _ , _ =
      s′ , meq , Meq , wrun , (rcFix ecpB , rcFix ecpC)
