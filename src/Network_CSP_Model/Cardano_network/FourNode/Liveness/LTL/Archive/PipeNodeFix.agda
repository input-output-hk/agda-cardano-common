{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the per-peer BF-CLIENT FIXITY node cone
-- (`Praos.PipeNodeFix`).
--
-- SCOPE VERDICT (session 12): the CHEAP per-peer-refl technique that made the
-- CELL classifier (`PipeClassCell`) trivial does NOT transfer to the nodes.  For
-- the cell, the R2 medium inversion (`medium-ev-inv-wt`) hands back the CONCRETE
-- touched key + a `setCell` updater, and the reflector builds `s′` as a LITERAL
-- `mkMed (phase-upd … i (setCell …))`, so `phase (med s′) kl kd kid` REDUCES via
-- `with kl ≟ i` — a non-touched cell literally becomes its source (`clcFix
-- refl`).  For the nodes, `WalkConvNodeFix.top-nodes-io-abs-fix` returns its
-- successor `s′` with the FIRED node bound as an OPAQUE pattern variable
-- (`nd′` from `ndEBafix nd′`), surfacing only the SIX driver fixities (prod-AB/
-- prod-AC/cp-B/cp-C/cons-BD/cons-CD) — NOT the `bfC-*` client fixities.  The
-- concrete successor node `mkNodeD … (bfC-CD nd) …` (with the co-located
-- non-fired peer a LITERAL) is visible only INSIDE the frozen peel
-- (`nodeD-io-BD-abs-fix`), never to a caller.  So `bfC-CD (toSys r′) ≡ bfC-CD
-- (toSys r)` is NOT `refl` through the frozen interface — it is stuck on the
-- opaque `nd′`.
--
-- HENCE this module RE-MIRRORS the io-sync node dispatch (the
-- `WalkConvNodeFix.top-nodes-io-abs-fix` structure, api template
-- `WalkDExpose.top-nodes-abs-expose`) with per-node peels that KEEP the
-- successor node concrete, so each tracked BF-client peer is CLASSIFIED: the
-- fired peer gets `clAdv (adv-of …)` (its new phase `bfc′` off `bgEBwt`), the
-- co-located non-fired peer gets `clFix refl` (a LITERAL in the `mkNode`).  The
-- whole-nodes classifier `top-nodes-io-abs-client-cls` assembles the four
-- tracked clients (bfC-AB on B, bfC-AC on C, bfC-BD/bfC-CD on D); a node that
-- does not fire keeps its clients `clFix refl`.
--
-- Built per-node (D first — the two-co-located-client blocker the plan flagged).
-- No postulate/hole/meta.  All base modules READ-ONLY (re-mirror, not edit).
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Unit.Polymorphic using ( tt )
open import Relation.Nullary using ( yes; no; ¬_ )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; cong₂; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Archive.PipeNodeFix (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; apiES; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟; Link )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using ( Dir; lo; hi )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; EventSet; viewV )
  renaming ( ∅ES to ∅ESa )
open EventSet using ( mem )

import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload}) as PEA

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; τ; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_ )

import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep
open SStep using ( NetProc; absNodeA; absNodeB; absNodeC; absNodeD; absBundleG; ⦀-noOffer
                 ; absNodesOf; nodesOf )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN

open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvNodeDrop blkA
  using ( absBundleG-io-prod-wt; bgEBwt )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvNodeFix blkA
  using ( nodeA-ev-io-abs-fix; naEBafix )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA
  using ( io⇒¬api; apiLink-inj )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_RouteLnLf blkA
  using ( noOffer→viewV )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink blkA
  using ( nodeA-drv-io-no; nodeB-drv-io-no; nodeC-drv-io-no; nodeD-drv-io-no
        ; linkAB≢linkBD; linkAC≢linkCD; linkBD≢linkCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink2 blkA
  using ( nodeC-io-no-when-B; nodeD-io-no-when-B; nodeD-io-no-when-C
        ; nodeB-io-no-when-A; nodeC-io-no-when-A; nodeD-io-no-when-A )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink3 blkA
  using ( absNodeA-io-fp; absNodeB-io-fp; absNodeC-io-fp; absNodeD-io-fp
        ; absNodeD-io-no-when-C; absGroupA-io-no; absGroupB-io-no; absBundleG-io-ahl )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink6 blkA
  using ( bundleG-io-no; ∥⇘⇙-wev-soloL; ⦀-wev-L; ⦀-wev-R
        ; nodeA-io-no-when-B; nodeA-io-no-when-C; nodeA-io-no-when-D
        ; nodeB-io-no-when-C; nodeB-io-no-when-D; nodeC-io-no-when-D )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; mkSys; med; nA; nB; nC; nD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( upClient; dnClient )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Archive.PipeExposeNode blkA
  using ( ClientAdv; cl-refl; cl-step; cl-trans; adv-of )

------------------------------------------------------------------------
-- The genuine per-client CLASSIFIER `ClientClass1` (the `DReport`/`CellClass1`
-- shape for a single BF-client peer): either the client is FIXED (a
-- propositional `≡`, the datum a `PipeStep⁺` client core needs) or it ADVANCED
-- (a concrete `ClientAdv`).
------------------------------------------------------------------------

-- one client's classification across a step/run: fixed-with-proof, or advanced
data ClientClass1 (a b : SN.BFcPos) : Set where
  clFix : a ≡ b        → ClientClass1 a b
  clAdv : ClientAdv a b → ClientClass1 a b

-- compose two classifications (a τ-run fold): fixed∘fixed stays fixed (`trans`),
-- anything touching an advance becomes an advance
ccFold : ∀ {a b c} → ClientClass1 a b → ClientClass1 b c → ClientClass1 a c
ccFold             (clFix p) (clFix q) = clFix (trans p q)
ccFold {a} {b} {c} (clFix p) (clAdv g) = clAdv (subst (λ z → ClientAdv z c) (sym p) g)
ccFold {a} {b} {c} (clAdv f) (clFix q) = clAdv (subst (ClientAdv a) q f)
ccFold             (clAdv f) (clAdv g) = clAdv (cl-trans f g)

------------------------------------------------------------------------
-- Per-node io peel records carrying the concrete successor node AND the
-- per-tracked-client `ClientClass1` (the client analogue of
-- `WalkConvNodeFix.NodeDEvR-abs-fix`, which carried only driver fixities).
------------------------------------------------------------------------

-- node D hosts TWO tracked clients (bfC-BD, bfC-CD): expose both
data NodeDEvR-cls (nd : SN.NodeStateD) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                  (M : NetProc) : Set₁ where
  ndEBcls : (nd′ : SN.NodeStateD) → M ≡ absNodeD nd′
        → SN.decNodeD nd ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeD nd′
        → ClientClass1 (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfC-BD nd′)
        → ClientClass1 (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfC-CD nd′)
        → SN.NodeStateD.cons-BD nd ≡ SN.NodeStateD.cons-BD nd′
        → SN.NodeStateD.cons-CD nd ≡ SN.NodeStateD.cons-CD nd′
        → NodeDEvR-cls nd e a M

------------------------------------------------------------------------
-- Node D io peels (mirror `WalkConvNodeFix.nodeD-io-{BD,CD}-abs-fix` VERBATIM
-- for the reachability, replacing the discarded driver fixities with the
-- per-client classes: the fired peer `clAdv (adv-of … bfc′)`, the co-located
-- non-fired peer `clFix refl` — a LITERAL in the constructed `mkNodeD`).
------------------------------------------------------------------------

-- D fires on link BD: bfC-BD advances (fired), bfC-CD fixed (literal)
nodeD-io-BD-abs-cls : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeDEvR-cls nd e a ((Bd′ ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)))
nodeD-io-BD-abs-cls nd {X} {e} {a} iomem sBBD
  with absBundleG-io-prod-wt linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) iomem sBBD
... | bgEBwt csc′ css′ bfc′ bfs′ ip′ eq run drop =
      ndEBcls (SN.mkNodeD csc′ css′ bfc′ bfs′ (SN.NodeStateD.cons-BD nd) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) ip′ (SN.NodeStateD.inert-CD nd))
        (cong (λ z → (z ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeD-drv-io-no nd iomem))
           (⦀-wev-L _ _
              (noOffer→viewV _ (bundleG-io-no linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)
                 (absBundleG-io-ahl linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) iomem sBBD) linkBD≢linkCD iomem))
              run))
        (clAdv (adv-of (SN.NodeStateD.bfC-BD nd) bfc′))
        (clFix refl)
        refl refl

-- D fires on link CD: bfC-CD advances (fired), bfC-BD fixed (literal)
nodeD-io-CD-abs-cls : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeDEvR-cls nd e a ((absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ⦀ Bd′) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)))
nodeD-io-CD-abs-cls nd {X} {e} {a} iomem sBCD
  with absBundleG-io-prod-wt linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) iomem sBCD
... | bgEBwt csc′ css′ bfc′ bfs′ ip′ eq run drop =
      ndEBcls (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd) csc′ css′ bfc′ bfs′ (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) ip′)
        (cong (λ z → (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ⦀ z) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeD-drv-io-no nd iomem))
           (⦀-wev-R _ _
              (noOffer→viewV _ (bundleG-io-no linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
                 (absBundleG-io-ahl linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) iomem sBCD) (λ q → linkBD≢linkCD (sym q)) iomem))
              run))
        (clFix refl)
        (clAdv (adv-of (SN.NodeStateD.bfC-CD nd) bfc′))
        refl refl

------------------------------------------------------------------------
-- Node D dispatcher (mirror `WalkConvNodeFix.nodeD-ev-io-abs-fix`): peel the
-- two D bundles + the D-consumer driver, route the fired link to its peel.
------------------------------------------------------------------------

nodeD-ev-io-abs-cls : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodeD nd ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeDEvR-cls nd e a M
nodeD-ev-io-abs-cls nd {X} {e} {a} iomem step
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
...   | PEA.evL _ sBBD = nodeD-io-BD-abs-cls nd iomem sBBD
...   | PEA.evR _ sBCD = nodeD-io-CD-abs-cls nd iomem sBCD

------------------------------------------------------------------------
-- Node B hosts ONE tracked client (bfC-AB): expose it.  Node C mirrors it.
------------------------------------------------------------------------

data NodeBEvR-cls (nb : SN.NodeStateB) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                  (M : NetProc) : Set₁ where
  nbEBcls : (nb′ : SN.NodeStateB) → M ≡ absNodeB nb′
        → SN.decNodeB nb ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeB nb′
        → ClientClass1 (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfC-AB nb′)
        → SN.NodeStateB.cp-B nb ≡ SN.NodeStateB.cp-B nb′
        → NodeBEvR-cls nb e a M

data NodeCEvR-cls (nc : SN.NodeStateC) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                  (M : NetProc) : Set₁ where
  ncEBcls : (nc′ : SN.NodeStateC) → M ≡ absNodeC nc′
        → SN.decNodeC nc ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeC nc′
        → ClientClass1 (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfC-AC nc′)
        → SN.NodeStateC.cp-C nc ≡ SN.NodeStateC.cp-C nc′
        → NodeCEvR-cls nc e a M

-- B fires on link AB: bfC-AB advances (fired)
nodeB-io-AB-abs-cls : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeBEvR-cls nb e a ((Bd′ ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
nodeB-io-AB-abs-cls nb {X} {e} {a} iomem sBAB
  with absBundleG-io-prod-wt linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) iomem sBAB
... | bgEBwt csc′ css′ bfc′ bfs′ ip′ eq run drop =
      nbEBcls (SN.mkNodeB csc′ css′ bfc′ bfs′ (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) ip′ (SN.NodeStateB.inert-BD nb))
        (cong (λ z → (z ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb)) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeB-drv-io-no nb iomem))
           (⦀-wev-L _ _
              (noOffer→viewV _ (bundleG-io-no linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)
                 (absBundleG-io-ahl linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) iomem sBAB) linkAB≢linkBD iomem))
              run))
        (clAdv (adv-of (SN.NodeStateB.bfC-AB nb) bfc′))
        refl

-- B fires on link BD: bfC-AB fixed (literal)
nodeB-io-BD-abs-cls : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeBEvR-cls nb e a ((absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ⦀ Bd′) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
nodeB-io-BD-abs-cls nb {X} {e} {a} iomem sBBD
  with absBundleG-io-prod-wt linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) iomem sBBD
... | bgEBwt csc′ css′ bfc′ bfs′ ip′ eq run drop =
      nbEBcls (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) csc′ css′ bfc′ bfs′ (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) ip′)
        (cong (λ z → (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ⦀ z) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb)) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeB-drv-io-no nb iomem))
           (⦀-wev-R _ _
              (noOffer→viewV _ (bundleG-io-no linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
                 (absBundleG-io-ahl linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) iomem sBBD) (λ q → linkAB≢linkBD (sym q)) iomem))
              run))
        (clFix refl)
        refl

nodeB-ev-io-abs-cls : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodeB nb ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeBEvR-cls nb e a M
nodeB-ev-io-abs-cls nb {X} {e} {a} iomem step
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
...   | PEA.evL _ sBAB = nodeB-io-AB-abs-cls nb iomem sBAB
...   | PEA.evR _ sBBD = nodeB-io-BD-abs-cls nb iomem sBBD

-- C fires on link AC: bfC-AC advances (fired)
nodeC-io-AC-abs-cls : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeCEvR-cls nc e a ((Bd′ ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
nodeC-io-AC-abs-cls nc {X} {e} {a} iomem sBAC
  with absBundleG-io-prod-wt linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) iomem sBAC
... | bgEBwt csc′ css′ bfc′ bfs′ ip′ eq run drop =
      ncEBcls (SN.mkNodeC csc′ css′ bfc′ bfs′ (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) ip′ (SN.NodeStateC.inert-CD nc))
        (cong (λ z → (z ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc)) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeC-drv-io-no nc iomem))
           (⦀-wev-L _ _
              (noOffer→viewV _ (bundleG-io-no linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)
                 (absBundleG-io-ahl linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) iomem sBAC) linkAC≢linkCD iomem))
              run))
        (clAdv (adv-of (SN.NodeStateC.bfC-AC nc) bfc′))
        refl

-- C fires on link CD: bfC-AC fixed (literal)
nodeC-io-CD-abs-cls : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeCEvR-cls nc e a ((absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ⦀ Bd′) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
nodeC-io-CD-abs-cls nc {X} {e} {a} iomem sBCD
  with absBundleG-io-prod-wt linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) iomem sBCD
... | bgEBwt csc′ css′ bfc′ bfs′ ip′ eq run drop =
      ncEBcls (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) csc′ css′ bfc′ bfs′ (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) ip′)
        (cong (λ z → (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ⦀ z) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc)) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeC-drv-io-no nc iomem))
           (⦀-wev-R _ _
              (noOffer→viewV _ (bundleG-io-no linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
                 (absBundleG-io-ahl linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) iomem sBCD) (λ q → linkAC≢linkCD (sym q)) iomem))
              run))
        (clFix refl)
        refl

nodeC-ev-io-abs-cls : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodeC nc ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeCEvR-cls nc e a M
nodeC-ev-io-abs-cls nc {X} {e} {a} iomem step
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
...   | PEA.evL _ sBAC = nodeC-io-AC-abs-cls nc iomem sBAC
...   | PEA.evR _ sBCD = nodeC-io-CD-abs-cls nc iomem sBCD

------------------------------------------------------------------------
-- The whole-nodes client classifier `AllClientClass`: a `ClientClass1` for EACH
-- of the four `PipeInv`-tracked BF-client peers (bfC-AB on B, bfC-AC on C,
-- bfC-BD/bfC-CD on D).  The genuine (Fix/Adv) analogue of
-- `PipeExposeNodeClient.AllClientAdv`; composes pointwise via `ccFold`.
------------------------------------------------------------------------

AllClientClass : SysState → SysState → Set
AllClientClass s s′ =
    ClientClass1 (upClient legBD s) (upClient legBD s′)
  × ClientClass1 (upClient legCD s) (upClient legCD s′)
  × ClientClass1 (dnClient legBD s) (dnClient legBD s′)
  × ClientClass1 (dnClient legCD s) (dnClient legCD s′)

-- reflexivity: a nodes-fixed step classifies every tracked client FIXED
allClientClass-refl : (s : SysState) → AllClientClass s s
allClientClass-refl s = clFix refl , clFix refl , clFix refl , clFix refl

-- transitivity (pointwise fold): compose two classifiers across a τ-run
allClientClass-trans : (s s₁ s₂ : SysState)
                     → AllClientClass s s₁ → AllClientClass s₁ s₂ → AllClientClass s s₂
allClientClass-trans s s₁ s₂ (a₁ , b₁ , c₁ , d₁) (a₂ , b₂ , c₂ , d₂) =
    ccFold a₁ a₂ , ccFold b₁ b₂ , ccFold c₁ c₂ , ccFold d₁ d₂

------------------------------------------------------------------------
-- TOP: the whole-nodes io-sync BF-CLIENT CLASSIFIER (`top-nodes-io-abs-client
-- -cls`).  Re-mirror of `WalkConvNodeFix.top-nodes-io-abs-fix`'s 4-node dispatch
-- (api template `WalkDExpose.top-nodes-abs-expose`), routing B/C/D through the
-- per-peer classifier dispatchers above and A through the FROZEN driver-fixity
-- peel (node A hosts NO tracked client, so all four are `clFix refl` there).
-- Each non-firing node keeps its clients `clFix refl` (its node is LITERAL in
-- the successor `mkSys`); the firing node's clients come off its dispatcher.
------------------------------------------------------------------------

top-nodes-io-abs-client-cls : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ s′ ∈ SysState ] (med s ≡ med s′) × (M ≡ absNodesOf s′)
      × (nodesOf s ═[ ev (evl (evLabel X e a)) ]═► nodesOf s′)
      × AllClientClass s s′
      × (SN.NodeStateA.prod-AB (nA s) ≡ SN.NodeStateA.prod-AB (nA s′))
      × (SN.NodeStateA.prod-AC (nA s) ≡ SN.NodeStateA.prod-AC (nA s′))
      × (SN.NodeStateB.cp-B (nB s) ≡ SN.NodeStateB.cp-B (nB s′))
      × (SN.NodeStateC.cp-C (nC s) ≡ SN.NodeStateC.cp-C (nC s′))
      × (SN.NodeStateD.cons-BD (nD s) ≡ SN.NodeStateD.cons-BD (nD s′))
      × (SN.NodeStateD.cons-CD (nD s) ≡ SN.NodeStateD.cons-CD (nD s′))
top-nodes-io-abs-client-cls s iomem nodesStep
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (absNodeA (nA s)) (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s))) nodesStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sA sRest = ⊥-elim (absGroupA-io-no (nA s) (nB s) (nC s) (nD s) iomem sA (_ , sRest))
... | PEA.evL _ sA with nodeA-ev-io-abs-fix (nA s) iomem sA
...   | naEBafix na′ Meq weakRunA epAB epAC =
        mkSys (med s) na′ (nB s) (nC s) (nD s) , refl ,
        cong (λ z → z ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) Meq ,
        ⦀-wev-L (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (⦀-noOffer (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (nodeB-io-no-when-A (nB s) iomem fpA)
             (⦀-noOffer (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (nodeC-io-no-when-A (nC s) iomem fpA) (nodeD-io-no-when-A (nD s) iomem fpA))))
          weakRunA
        , (clFix refl , clFix refl , clFix refl , clFix refl)
        , epAB , epAC , refl , refl , refl , refl
  where fpA = absNodeA-io-fp (nA s) iomem sA
top-nodes-io-abs-client-cls s iomem nodesStep | PEA.evR _ sRest
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s)) sRest
... | PEA.evSync () _ _
... | PEA.evBoth _ sB sCD = ⊥-elim (absGroupB-io-no (nB s) (nC s) (nD s) iomem sB (_ , sCD))
... | PEA.evL _ sB with nodeB-ev-io-abs-cls (nB s) iomem sB
...   | nbEBcls nb′ Meq weakRunB clsAB ecpB =
        mkSys (med s) (nA s) nb′ (nC s) (nD s) , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (z ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) Meq ,
        ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (nodeA-io-no-when-B (nA s) iomem fpB))
          (⦀-wev-L (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (noOffer→viewV _ (⦀-noOffer (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (nodeC-io-no-when-B (nC s) iomem fpB) (nodeD-io-no-when-B (nD s) iomem fpB)))
             weakRunB)
        , (clsAB , clFix refl , clFix refl , clFix refl)
        , refl , refl , ecpB , refl , refl , refl
  where fpB = absNodeB-io-fp (nB s) iomem sB
top-nodes-io-abs-client-cls s iomem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absNodeC (nC s)) (absNodeD (nD s)) sCD
... | PEA.evSync () _ _
... | PEA.evBoth _ sC sD = ⊥-elim (absNodeD-io-no-when-C (nD s) iomem (absNodeC-io-fp (nC s) iomem sC) (_ , sD))
... | PEA.evL _ sC with nodeC-ev-io-abs-cls (nC s) iomem sC
...   | ncEBcls nc′ Meq weakRunC clsAC ecpC =
        mkSys (med s) (nA s) (nB s) nc′ (nD s) , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (z ⦀ absNodeD (nD s)))) Meq ,
        ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (nodeA-io-no-when-C (nA s) iomem fpC))
          (⦀-wev-R (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (noOffer→viewV _ (nodeB-io-no-when-C (nB s) iomem fpC))
             (⦀-wev-L (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (noOffer→viewV _ (nodeD-io-no-when-C (nD s) iomem fpC))
                weakRunC))
        , (clFix refl , clsAC , clFix refl , clFix refl)
        , refl , refl , refl , ecpC , refl , refl
  where fpC = absNodeC-io-fp (nC s) iomem sC
top-nodes-io-abs-client-cls s iomem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD | PEA.evR _ sD
    with nodeD-ev-io-abs-cls (nD s) iomem sD
... | ndEBcls nd′ Meq weakRunD clsBD clsCD econsBD econsCD =
        mkSys (med s) (nA s) (nB s) (nC s) nd′ , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ z))) Meq ,
        ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (nodeA-io-no-when-D (nA s) iomem fpD))
          (⦀-wev-R (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (noOffer→viewV _ (nodeB-io-no-when-D (nB s) iomem fpD))
             (⦀-wev-R (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (noOffer→viewV _ (nodeC-io-no-when-D (nC s) iomem fpD))
                weakRunD))
        , (clFix refl , clFix refl , clsBD , clsCD)
        , refl , refl , refl , refl , econsBD , econsCD
  where fpD = absNodeD-io-fp (nD s) iomem sD
