{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the node-A api peel WITH the BF-SERVER evolution
-- (`Praos.PipeNodeAEvo`), step (i) of item G2 (`SrvEvStep`/`EvStepS`).
--
-- `WalkApiDrop.nodeA-ev-api-abs-wt` peels node A's visible api step through
-- the FROZEN `SysIoLink6.absBundleG-api-prod` (`bgEB`), whose result DROPS the
-- BF-server slot.  `PipeSrvInv.SrvCoupled`'s upstream clause reads exactly that
-- slot (`upSrv legBD = bfS-AB (nA s)`, `upSrv legCD = bfS-AC (nA s)`), so the
-- product invariant cannot cross a visible step through it.
--
-- This module re-mirrors the SAME three functions on
-- `PipeBundleEvo.absBundleG-api-evo` (`bgEB⁺`, which carries the server slot's
-- evolution `(bfs ≡ bfs′) ⊎ BfsSucc l sv bfs′ e a`) and RESOLVES the pin on
-- the spot: `BfsSucc`'s block arm hands over the label pin
-- `evLabel X e a ≡ evLabel Block₃ (apiBF linkAB hi sendBFBlock) b″`, and the
-- co-firing produce driver is right there, so
-- `PipeProdFire.decProd-sbb-pp5` forces `prod-AB na ≡ pp5`, whence the genuine
-- `ProdAdv pp5 pp′` is `a56` and `ProdSent (prod-AB na′)` holds OUTRIGHT.
--
-- ECONOMY: resolving the pin INSIDE the peel (rather than exporting the raw
-- `BfsSucc` and re-inverting later) is what keeps the consumer trivial — the
-- caller never has to relate a second peel of the same step to the first
-- (`absNodesOf` is not known injective; the session-30 negative result).
--
-- The delivered field is exactly `PipeSrvInv.SrvEvoUp`'s shape at node A:
--     (bfS ≡ bfS′) ⊎ ((BFsHasBlk bfS′ → ⊥) ⊎ ProdSent (prod′))
--
-- No postulate/hole/meta.  All base modules stay READ-ONLY (this is a new leaf;
-- `WalkApiDrop` is untouched).
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Relation.Nullary using ( ¬_ )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; subst; _≢_ )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeNodeAEvo (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using
  ( p; apiES; linkAB; linkAC )
open import CSP.Examples.Cardano_network.Net p using
  ( Net_Api; Net_Api-≟; Link; apiBF; sendBFBlock )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using ( Dir; lo; hi )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; EventSet; viewV )
open EventSet using ( mem )
open Op using () renaming ( ∅ES to ∅ESa )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_ )

import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload}) as PEA

import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep
open SStep using ( NetProc; absBundleG; absNodeA; ⦀-ev-L; ⦀-ev-R )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using ( ProdPh; pp0; pp1; pp2; pp3; pp4; pp5; pp6; pp7; pp8; pp9; BFsPos )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA using
  ( ApiHasLink; apiLink-inj; decProd-ev-link )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink blkA using
  ( linkAB≢linkAC )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_RouteLnLf blkA
  using ( noOffer→viewV )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink6 blkA
  using ( ⦀-wev-L; ⦀-wev-R; ∥⇘⇙-wev-sync; ev→wev
        ; absBundleG-api-no; bundleG-api-no; drvA-AC-no; drvA-AB-no )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkClassify blkA
  using ( prodAdv-of )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkMeasure blkA
  using ( ProdAdv; a01; a12; a23; a34; a45; a56; a67; a78; a89 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( ProdSent )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleEvo blkA
  using ( BFsHasBlk; BfsSucc; BundleGEvR⁺; bgEB⁺; absBundleG-api-evo )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeProdFire blkA
  using ( IsSBB; decProd-sbb-pp5 )

------------------------------------------------------------------------
-- (1) The two tiny phase lemmas that resolve the label pin into `ProdSent`.
------------------------------------------------------------------------

-- out of the OFFERING phase `pp5` the only genuine adjacency is `a56`, which
-- lands on `pp6` — a SENT phase
padv-pp5-sent : {q : ProdPh} → ProdAdv pp5 q → ProdSent q
padv-pp5-sent a56 = tt

-- the block arm of `BfsSucc` at node A's server key resolves to `ProdSent`
-- (the pinned label IS the co-firing produce driver's `pp5 → pp6` fire)
srvBlk⇒sent : (l : Link) (pp pp′ : ProdPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → SN.decProd l hi blkA pp ─[ ev (evl (evLabel X e a)) ]─► M
  → ProdAdv pp pp′
  → {b″ : Block₃} → evLabel X e a ≡ evLabel Block₃ (apiBF l hi sendBFBlock) b″
  → ProdSent pp′
srvBlk⇒sent l pp pp′ st padv lbl =
  padv-pp5-sent (subst (λ q → ProdAdv q pp′)
                       (decProd-sbb-pp5 l hi blkA pp st (subst IsSBB (sym lbl) tt))
                       padv)

-- fold a raw `bgEB⁺` server slot into the `PipeSrvInv.SrvEvoUp` shape
srvEvo⇒up : (l : Link) (bfs bfs′ : BFsPos) (pp pp′ : ProdPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → SN.decProd l hi blkA pp ─[ ev (evl (evLabel X e a)) ]─► M
  → ProdAdv pp pp′
  → ((bfs ≡ bfs′) ⊎ BfsSucc l hi bfs′ e a)
  → (bfs ≡ bfs′) ⊎ ((BFsHasBlk bfs′ → ⊥) ⊎ ProdSent pp′)
srvEvo⇒up l bfs bfs′ pp pp′ st padv (inj₁ eq)                   = inj₁ eq
srvEvo⇒up l bfs bfs′ pp pp′ st padv (inj₂ (inj₁ nb))            = inj₂ (inj₁ nb)
srvEvo⇒up l bfs bfs′ pp pp′ st padv (inj₂ (inj₂ (b″ , lbl , _))) =
  inj₂ (inj₂ (srvBlk⇒sent l pp pp′ st padv lbl))

------------------------------------------------------------------------
-- (2) The node-A peel record, carrying the genuine `ProdAdv`, the other-leg
-- producer fixity, the FIRING leg's resolved server evolution and the other
-- leg's server fixity.
------------------------------------------------------------------------

-- node A fires `produce` on link AB (leg BD) or AC (leg CD), with the AB/AC
-- BF-SERVER slots reported
data NodeAEvR-abs-evo (na : SN.NodeStateA) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                      (M : NetProc) : Set₁ where
  naEBaev1 : (na′ : SN.NodeStateA) → M ≡ absNodeA na′
           → SN.decNodeA na ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeA na′
           → ProdAdv (SN.NodeStateA.prod-AB na) (SN.NodeStateA.prod-AB na′)
           → SN.NodeStateA.prod-AC na′ ≡ SN.NodeStateA.prod-AC na
           -- SESSION-51: the resolved `SrvEvoUp` arm PAIRED with the RAW
           -- `BfsSucc` witness (which names the fired block and the successor
           -- position `bsBlk1 b″`) — the value invariant's clause (1) needs the
           -- raw one, and carrying it ALONGSIDE keeps the session-30 property
           -- that no caller ever re-peels the same step
           → (((SN.NodeStateA.bfS-AB na ≡ SN.NodeStateA.bfS-AB na′)
               ⊎ ((BFsHasBlk (SN.NodeStateA.bfS-AB na′) → ⊥)
                  ⊎ ProdSent (SN.NodeStateA.prod-AB na′)))
              × ((SN.NodeStateA.bfS-AB na ≡ SN.NodeStateA.bfS-AB na′)
                 ⊎ BfsSucc linkAB hi (SN.NodeStateA.bfS-AB na′) e a))
           → SN.NodeStateA.bfS-AC na ≡ SN.NodeStateA.bfS-AC na′
           → NodeAEvR-abs-evo na e a M
  naEBaev2 : (na′ : SN.NodeStateA) → M ≡ absNodeA na′
           → SN.decNodeA na ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeA na′
           → ProdAdv (SN.NodeStateA.prod-AC na) (SN.NodeStateA.prod-AC na′)
           → SN.NodeStateA.prod-AB na′ ≡ SN.NodeStateA.prod-AB na
           -- SESSION-51 (mirror)
           → (((SN.NodeStateA.bfS-AC na ≡ SN.NodeStateA.bfS-AC na′)
               ⊎ ((BFsHasBlk (SN.NodeStateA.bfS-AC na′) → ⊥)
                  ⊎ ProdSent (SN.NodeStateA.prod-AC na′)))
              × ((SN.NodeStateA.bfS-AC na ≡ SN.NodeStateA.bfS-AC na′)
                 ⊎ BfsSucc linkAC hi (SN.NodeStateA.bfS-AC na′) e a))
           → SN.NodeStateA.bfS-AB na ≡ SN.NodeStateA.bfS-AB na′
           → NodeAEvR-abs-evo na e a M

------------------------------------------------------------------------
-- (3) The two link-tagged peels (re-mirror of `WalkApiDrop.nodeA-api-*-abs-wt`
-- with `absBundleG-api-prod`/`bgEB` swapped for `absBundleG-api-evo`/`bgEB⁺`).
------------------------------------------------------------------------

-- firing link = linkAB (leg BD)
nodeA-api-AB-abs-evo : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁AB : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
     ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ─[ ev (evl (evLabel X e a)) ]─► D₁AB
  → ApiHasLink linkAB e
  → NodeAEvR-abs-evo na e a (B₁ ∥⇘ apiES ⇙ (D₁AB ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)))
nodeA-api-AB-abs-evo na {X} {e} {a} apimem bStep sDAB ahl
  with prodAdv-of linkAB hi blkA (SN.NodeStateA.prod-AB na) sDAB
... | pp′ , refl , padv
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
           (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) bStep
...   | PEA.evSync () _ _
...   | PEA.evR _ sBAC = ⊥-elim (absBundleG-api-no linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) ahl linkAB≢linkAC apimem (_ , sBAC))
...   | PEA.evBoth _ _ sBAC = ⊥-elim (absBundleG-api-no linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) ahl linkAB≢linkAC apimem (_ , sBAC))
...   | PEA.evL _ sBAB
      with absBundleG-api-evo linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) apimem sBAB
...     | bgEB⁺ csc′ css′ bfc′ bfs′ ip′ eq run _ srvEvo =
          naEBaev1 (SN.mkNodeA csc′ css′ bfc′ bfs′ pp′ (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) ip′ (SN.NodeStateA.inert-AC na))
            (cong (λ z → (z ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA pp′ ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na))) eq)
            (∥⇘⇙-wev-sync apiES _ _ apimem
               (⦀-wev-L _ _ (noOffer→viewV _ (bundleG-api-no linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) ahl linkAB≢linkAC apimem)) run)
               (ev→wev (⦀-ev-L (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na)) _ sDAB (noOffer→viewV _ (drvA-AC-no na ahl)))))
            padv refl
            (srvEvo⇒up linkAB (SN.NodeStateA.bfS-AB na) bfs′ (SN.NodeStateA.prod-AB na) pp′ sDAB padv srvEvo , srvEvo)
            refl

-- firing link = linkAC (leg CD)
nodeA-api-AC-abs-evo : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁AC : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
     ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na) ─[ ev (evl (evLabel X e a)) ]─► D₁AC
  → ApiHasLink linkAC e
  → NodeAEvR-abs-evo na e a (B₁ ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ D₁AC))
nodeA-api-AC-abs-evo na {X} {e} {a} apimem bStep sDAC ahl
  with prodAdv-of linkAC hi blkA (SN.NodeStateA.prod-AC na) sDAC
... | pp′ , refl , padv
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
           (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) bStep
...   | PEA.evSync () _ _
...   | PEA.evL _ sBAB = ⊥-elim (absBundleG-api-no linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ahl (λ q → linkAB≢linkAC (sym q)) apimem (_ , sBAB))
...   | PEA.evBoth _ sBAB _ = ⊥-elim (absBundleG-api-no linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ahl (λ q → linkAB≢linkAC (sym q)) apimem (_ , sBAB))
...   | PEA.evR _ sBAC
      with absBundleG-api-evo linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) apimem sBAC
...     | bgEB⁺ csc′ css′ bfc′ bfs′ ip′ eq run _ srvEvo =
          naEBaev2 (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na) csc′ css′ bfc′ bfs′ pp′ (SN.NodeStateA.inert-AB na) ip′)
            (cong (λ z → (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ⦀ z) ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA pp′)) eq)
            (∥⇘⇙-wev-sync apiES _ _ apimem
               (⦀-wev-R _ _ (noOffer→viewV _ (bundleG-api-no linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ahl (λ q → linkAB≢linkAC (sym q)) apimem)) run)
               (ev→wev (⦀-ev-R _ (SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)) sDAC (noOffer→viewV _ (drvA-AB-no na ahl)))))
            padv refl
            (srvEvo⇒up linkAC (SN.NodeStateA.bfS-AC na) bfs′ (SN.NodeStateA.prod-AC na) pp′ sDAC padv srvEvo , srvEvo)
            refl

------------------------------------------------------------------------
-- (4) The node-A api inversion (dispatch on which produce driver fired).
------------------------------------------------------------------------

-- node-A api inversion carrying the server evolution (mirror
-- `WalkApiDrop.nodeA-ev-api-abs-wt`)
nodeA-ev-api-abs-evo : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeA na ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeAEvR-abs-evo na e a M
nodeA-ev-api-abs-evo na {X} {e} {a} apimem step
  with SStep.reflect-node-api
         (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
          ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
         (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na))
           (SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)) dStep
... | PEA.evSync () _ _
... | PEA.evL _ sDAB = nodeA-api-AB-abs-evo na apimem bStep sDAB (decProd-ev-link linkAB hi blkA (SN.NodeStateA.prod-AB na) sDAB)
... | PEA.evR _ sDAC = nodeA-api-AC-abs-evo na apimem bStep sDAC (decProd-ev-link linkAC hi blkA (SN.NodeStateA.prod-AC na) sDAC)
... | PEA.evBoth _ sDAB sDAC = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (decProd-ev-link linkAB hi blkA (SN.NodeStateA.prod-AB na) sDAB)
                     (decProd-ev-link linkAC hi blkA (SN.NodeStateA.prod-AC na) sDAC)))
