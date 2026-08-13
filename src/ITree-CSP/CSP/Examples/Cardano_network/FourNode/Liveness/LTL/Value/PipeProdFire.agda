{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the PRODUCER-OFFER INVERSION (`Praos.PipeProdFire`),
-- item (E2) of the session-32 frontier.
--
-- THE FACT.  A STRONG visible `apiBF linkAB hi sendBFBlock` out of a reachable
-- abstract config forces node A's AB producer driver to phase `pp5` (and dually
-- for `linkAC` / the AC producer):
--
--   radec r ─[ ev (evl (evLabel Block₃ (apiBF linkAB hi sendBFBlock) b)) ]─► M
--     ⇒  prodOf legBD (toSys r) ≡ pp5
--
-- This is what `PipeInv.pipeInv⇒Pr` (hence `PipeInvProd.pipeInvS⇒Pr`) demands
-- and what session 32 found MISSING from the recorded `pcone` recipe.
--
-- TABLE CHECK RUN FIRST (the method mandate).  `sendBFBlock` occurs at EXACTLY
-- one place in the whole driver algebra: `FourNodeDiamond.produce`'s sixth hop,
-- i.e. the head of `SysNode.decProd _ _ _ pp5`.  It occurs NOWHERE in
-- `consume`/`consume-k` (hence nowhere in `decCons`, hence nowhere in
-- `decConsD` or in `decCP`'s consuming arm).  So the claim is SOUND, and the
-- inversion below machine-checks it.
--
-- THE ECONOMY (this is what keeps the module at ~250 lines instead of a
-- 12-peer non-offer cascade).  A node api step is a `∥⇘ apiES ⇙` SYNC
-- (`SysStep.reflect-node-api`), so the node's DRIVER must co-fire the very same
-- event.  Every refutation can therefore be taken on the DRIVER side alone —
-- the twelve protocol peers are never examined:
--   · node A  — driver `decProd linkAB ⦀ decProd linkAC`: the good case, closed
--     by the `decProd` table inversion `decProd-sbb-pp5`;
--   · node B  — driver `decCP linkAB linkBD`: the consuming arm is `decCons`
--     (no `sendBFBlock` — `decCons-sbb-⊥`), the producing arm and the `cp6`
--     hand-off live on `linkBD` (link injectivity);
--   · node C  — driver `decCP linkAC linkCD`: both links differ from `linkAB`;
--   · node D  — driver `decConsD linkBD ⦀ decConsD linkCD`: both links differ.
--
-- The tag is transported across the fired-label equalities by the CLASSIFIER
-- `IsSBB` (a `Set`-valued predicate on `Event`), NOT by matching `refl` on the
-- label: the two `evLabel`s carry DIFFERENT carrier types and `Set` is not
-- injective, so the unifier gets stuck on a direct `refl`/`()` match.
--
-- No postulate/hole/meta.  All base modules stay READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Relation.Nullary using ( ¬_ )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeProdFire (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using
  ( p; apiES; linkAB; linkAC; linkBD; linkCD; produce )
open import CSP.Examples.Cardano_network.Net p using
  ( Net_Api; Net_Api-≟; Link; apiBF; sendBFBlock )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using ( Dir; lo; hi )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; EventSet )
open EventSet using ( mem )
open Op using () renaming ( ∅ES to ∅ESa )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel; Event; Event√ )

import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload}) as PEA
open import CSP.Laws.Traces.PrefixInversion (Net_Api-≟ {Payload})
  using ( ⟶₀-ev-inv )

import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using ( ProdPh; pp0; pp1; pp2; pp3; pp4; pp5; pp6; pp7; pp8; pp9
              ; ConsPh; cp0; cp1; cp2; cp3; cp4; cp5; cp6
              ; CPPh; consuming; producing )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep
open SStep using ( NetProc; absBundleG; absNodeA; absNodeB; absNodeC; absNodeD
                 ; absNodesOf; medEv; nodesEv; reflect-top-ev )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; med; nA; nB; nC; nD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( decMed )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( RState; radec; toSys )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA using
  ( ApiHasLink; apiLink-inj; ahlBF; IsApiCSBF; aicBF
  ; output-ev-lab; prefix-ev-lab
  ; decProd-ev-link; decCons-ev-link; decConsD-ev-link; decCP-ev-link )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( ret-no-ev; bind-ev-inv; step-fcong )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysRoute blkA using
  ( medium-api-non-offer
  ; absNodeA-fp; absNodeB-fp; absNodeC-fp
  ; absNodeB-no-when-A; absNodeC-no-when-A; absNodeD-no-when-A
  ; absNodeC-no-when-B; absNodeD-no-when-B; absNodeD-no-when-C )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink blkA using
  ( linkAB≢linkAC; linkAB≢linkBD; linkAC≢linkCD; linkBD≢linkCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( prodOf )

------------------------------------------------------------------------
-- (0) The two link disequalities the four-node diamond needs here and that
-- `SysIoLink` does not already export.
------------------------------------------------------------------------

-- AB and CD are distinct links
linkAB≢linkCD : ¬ (linkAB ≡ linkCD)
linkAB≢linkCD ()

-- AC and BD are distinct links
linkAC≢linkBD : ¬ (linkAC ≡ linkBD)
linkAC≢linkBD ()

------------------------------------------------------------------------
-- (1) THE TAG CLASSIFIER.  `Set` is not injective, so a label equality between
-- two `evLabel`s with different carriers cannot be matched on `refl`/`()`;
-- instead we transport a `Set`-valued predicate along it.
------------------------------------------------------------------------

-- the fired event is a BlockFetch `sendBFBlock` api event
IsSBB : Event → Set
IsSBB (evLabel _ (apiBF _ _ sendBFBlock) _) = ⊤
IsSBB _                                     = ⊥

-- `evl` is injective (a data constructor of `Event√`)
evl-inj : {R : Set} {x y : Event} → (evl {R = R} x) ≡ evl y → x ≡ y
evl-inj refl = refl

-- transport the `sendBFBlock` tag along a fired-label equality
sbb-along : {R : Set} {x y : Event} → (evl {R = R} x) ≡ evl y → IsSBB x → IsSBB y
sbb-along eq h = subst IsSBB (evl-inj eq) h

-- the concrete `sendBFBlock` label IS classified (used at the top level)
sbb-here : (l : Link) (d : Dir) (b : Block₃) → IsSBB (evLabel Block₃ (apiBF l d sendBFBlock) b)
sbb-here l d b = tt

------------------------------------------------------------------------
-- (2) THE `decProd` TABLE INVERSION — the heart of (E2).  Only `pp5` heads the
-- producer chain with `apiBF … sendBFBlock`; each other phase heads it with a
-- DIFFERENT channel, off which `IsSBB` reduces to `⊥`.
------------------------------------------------------------------------

-- a producer driver fires `sendBFBlock` ONLY from the offering phase `pp5`
decProd-sbb-pp5 : (l : Link) (d : Dir) (blk : Block₃) (pp : ProdPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → SN.decProd l d blk pp ─[ ev (evl (evLabel X e a)) ]─► M
  → IsSBB (evLabel X e a) → pp ≡ pp5
decProd-sbb-pp5 l d blk pp0 step sbb = ⊥-elim (sbb-along (proj₁ (proj₂ (⟶₀-ev-inv step))) sbb)
decProd-sbb-pp5 l d blk pp1 step sbb = ⊥-elim (sbb-along (proj₁ (proj₂ (⟶₀-ev-inv step))) sbb)
decProd-sbb-pp5 l d blk pp2 step sbb = ⊥-elim (sbb-along (output-ev-lab step) sbb)
decProd-sbb-pp5 l d blk pp3 step sbb = ⊥-elim (sbb-along (proj₁ (proj₂ (⟶₀-ev-inv step))) sbb)
decProd-sbb-pp5 l d blk pp4 step sbb = ⊥-elim (sbb-along (output-ev-lab step) sbb)
decProd-sbb-pp5 l d blk pp5 step sbb = refl
decProd-sbb-pp5 l d blk pp6 step sbb = ⊥-elim (sbb-along (output-ev-lab step) sbb)
decProd-sbb-pp5 l d blk pp7 step sbb = ⊥-elim (sbb-along (proj₁ (proj₂ (⟶₀-ev-inv step))) sbb)
decProd-sbb-pp5 l d blk pp8 step sbb = ⊥-elim (sbb-along (proj₁ (proj₂ (⟶₀-ev-inv step))) sbb)
decProd-sbb-pp5 l d blk pp9 step sbb = ⊥-elim (ret-no-ev {P = SN.decProd l d blk pp9} refl step)

------------------------------------------------------------------------
-- (3) THE `decCons` TABLE REFUTATION — a CONSUMER driver never fires
-- `sendBFBlock` (its BF api hops are `sendBFRequestRange` / `recvBFBlock` /
-- `sendBFClientDone`).
------------------------------------------------------------------------

-- a consume driver never fires `sendBFBlock`
decCons-sbb-⊥ : (l : Link) (d : Dir) (b : Block₃) (cp : ConsPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃}
  → SN.decCons l d b cp ─[ ev (evl (evLabel X e a)) ]─► M
  → IsSBB (evLabel X e a) → ⊥
decCons-sbb-⊥ l d b cp0 step sbb = sbb-along (proj₁ (proj₂ (⟶₀-ev-inv step))) sbb
decCons-sbb-⊥ l d b cp1 step sbb = sbb-along (proj₂ (prefix-ev-lab step)) sbb
decCons-sbb-⊥ l d b cp2 step sbb = sbb-along (output-ev-lab step) sbb
decCons-sbb-⊥ l d b cp3 step sbb = sbb-along (proj₂ (prefix-ev-lab step)) sbb
decCons-sbb-⊥ l d b cp4 step sbb = sbb-along (output-ev-lab step) sbb
decCons-sbb-⊥ l d b cp5 step sbb = sbb-along (proj₁ (proj₂ (⟶₀-ev-inv step))) sbb
decCons-sbb-⊥ l d b cp6 step sbb = ret-no-ev {P = SN.decCons l d b cp6} refl step

------------------------------------------------------------------------
-- (4) THE `decCP` REFUTATION on the CONSUME link.  A relay driver
-- `consume l₁ hi >>= produce l₂ hi` can fire `sendBFBlock` — but only on its
-- PRODUCE link `l₂`.  So an event pinned to `l₁ ≢ l₂` is refuted.
------------------------------------------------------------------------

-- a relay driver never fires `sendBFBlock` on its CONSUME link
decCP-sbb-⊥ : (l₁ l₂ : Link) (x : CPPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → SN.decCP l₁ l₂ x ─[ ev (evl (evLabel X e a)) ]─► M
  → IsSBB (evLabel X e a) → ApiHasLink l₁ e → ¬ (l₁ ≡ l₂) → ⊥
decCP-sbb-⊥ l₁ l₂ (consuming b cp0) step sbb ahl ne
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (SN.decCons l₁ hi b cp0) refl step
... | _ , sc , refl = decCons-sbb-⊥ l₁ hi b cp0 sc sbb
decCP-sbb-⊥ l₁ l₂ (consuming b cp1) step sbb ahl ne
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (SN.decCons l₁ hi b cp1) refl step
... | _ , sc , refl = decCons-sbb-⊥ l₁ hi b cp1 sc sbb
decCP-sbb-⊥ l₁ l₂ (consuming b cp2) step sbb ahl ne
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (SN.decCons l₁ hi b cp2) refl step
... | _ , sc , refl = decCons-sbb-⊥ l₁ hi b cp2 sc sbb
decCP-sbb-⊥ l₁ l₂ (consuming b cp3) step sbb ahl ne
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (SN.decCons l₁ hi b cp3) refl step
... | _ , sc , refl = decCons-sbb-⊥ l₁ hi b cp3 sc sbb
decCP-sbb-⊥ l₁ l₂ (consuming b cp4) step sbb ahl ne
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (SN.decCons l₁ hi b cp4) refl step
... | _ , sc , refl = decCons-sbb-⊥ l₁ hi b cp4 sc sbb
decCP-sbb-⊥ l₁ l₂ (consuming b cp5) step sbb ahl ne
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (SN.decCons l₁ hi b cp5) refl step
... | _ , sc , refl = decCons-sbb-⊥ l₁ hi b cp5 sc sbb
-- the `cp6` hand-off: `Ret b >>= produce l₂` fires produce's FIRST hop, on `l₂`
decCP-sbb-⊥ l₁ l₂ (consuming b cp6) step sbb ahl ne =
  ne (sym (apiLink-inj (decProd-ev-link l₂ hi b pp0 (step-fcong refl step)) ahl))
decCP-sbb-⊥ l₁ l₂ (producing b pp) step sbb ahl ne =
  ne (sym (apiLink-inj (decProd-ev-link l₂ hi b pp step) ahl))

------------------------------------------------------------------------
-- (5) THE PER-NODE PEELS.  Each is `reflect-node-api` (the api event is a
-- driver↔peer SYNC) followed by driver-side reasoning only.
------------------------------------------------------------------------

-- node A firing an api event pinned to `linkAB` and tagged `sendBFBlock` forces
-- its AB producer to `pp5`
nodeA-sbb-AB : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeA na ─[ ev (evl (evLabel X e a)) ]─► M
  → IsSBB (evLabel X e a) → ApiHasLink linkAB e
  → SN.NodeStateA.prod-AB na ≡ pp5
nodeA-sbb-AB na {X} {e} {a} apimem step sbb ahl
  with SStep.reflect-node-api
         (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
          ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
         (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na)
          ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na))
           (SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)) dStep
... | PEA.evSync () _ _
... | PEA.evL _ sAB = decProd-sbb-pp5 linkAB hi blkA (SN.NodeStateA.prod-AB na) sAB sbb
... | PEA.evR _ sAC = ⊥-elim (linkAB≢linkAC
        (sym (apiLink-inj (decProd-ev-link linkAC hi blkA (SN.NodeStateA.prod-AC na) sAC) ahl)))
... | PEA.evBoth _ _ sAC = ⊥-elim (linkAB≢linkAC
        (sym (apiLink-inj (decProd-ev-link linkAC hi blkA (SN.NodeStateA.prod-AC na) sAC) ahl)))

-- node A firing an api event pinned to `linkAC` and tagged `sendBFBlock` forces
-- its AC producer to `pp5`
nodeA-sbb-AC : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeA na ─[ ev (evl (evLabel X e a)) ]─► M
  → IsSBB (evLabel X e a) → ApiHasLink linkAC e
  → SN.NodeStateA.prod-AC na ≡ pp5
nodeA-sbb-AC na {X} {e} {a} apimem step sbb ahl
  with SStep.reflect-node-api
         (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
          ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
         (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na)
          ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na))
           (SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)) dStep
... | PEA.evSync () _ _
... | PEA.evR _ sAC = decProd-sbb-pp5 linkAC hi blkA (SN.NodeStateA.prod-AC na) sAC sbb
... | PEA.evL _ sAB = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (decProd-ev-link linkAB hi blkA (SN.NodeStateA.prod-AB na) sAB) ahl))
... | PEA.evBoth _ sAB _ = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (decProd-ev-link linkAB hi blkA (SN.NodeStateA.prod-AB na) sAB) ahl))

-- node B's api events live on `linkAB` or `linkBD` (its driver's two links)
nodeB-link : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeB nb ─[ ev (evl (evLabel X e a)) ]─► M
  → ApiHasLink linkAB e ⊎ ApiHasLink linkBD e
nodeB-link nb {X} {e} {a} apimem step
  with SStep.reflect-node-api
         (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
          ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
         (SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl =
      decCP-ev-link linkAB linkBD (SN.NodeStateB.cp-B nb) dStep

-- node B never fires `sendBFBlock` on `linkAB` (there it hosts the CONSUME leg)
nodeB-sbb-AB-⊥ : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeB nb ─[ ev (evl (evLabel X e a)) ]─► M
  → IsSBB (evLabel X e a) → ApiHasLink linkAB e → ⊥
nodeB-sbb-AB-⊥ nb {X} {e} {a} apimem step sbb ahl
  with SStep.reflect-node-api
         (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
          ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
         (SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl =
      decCP-sbb-⊥ linkAB linkBD (SN.NodeStateB.cp-B nb) dStep sbb ahl linkAB≢linkBD

-- node C's api events live on `linkAC` or `linkCD`
nodeC-link : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeC nc ─[ ev (evl (evLabel X e a)) ]─► M
  → ApiHasLink linkAC e ⊎ ApiHasLink linkCD e
nodeC-link nc {X} {e} {a} apimem step
  with SStep.reflect-node-api
         (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
          ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
         (SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl =
      decCP-ev-link linkAC linkCD (SN.NodeStateC.cp-C nc) dStep

-- node C never fires `sendBFBlock` on `linkAC` (there it hosts the CONSUME leg)
nodeC-sbb-AC-⊥ : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeC nc ─[ ev (evl (evLabel X e a)) ]─► M
  → IsSBB (evLabel X e a) → ApiHasLink linkAC e → ⊥
nodeC-sbb-AC-⊥ nc {X} {e} {a} apimem step sbb ahl
  with SStep.reflect-node-api
         (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
          ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
         (SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl =
      decCP-sbb-⊥ linkAC linkCD (SN.NodeStateC.cp-C nc) dStep sbb ahl linkAC≢linkCD

-- node D's api events live on `linkBD` or `linkCD`
nodeD-link : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeD nd ─[ ev (evl (evLabel X e a)) ]─► M
  → ApiHasLink linkBD e ⊎ ApiHasLink linkCD e
nodeD-link nd {X} {e} {a} apimem step
  with SStep.reflect-node-api
         (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
          ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
         (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd))
           (SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)) dStep
... | PEA.evSync () _ _
... | PEA.evL _ sBD     = inj₁ (decConsD-ev-link linkBD (SN.NodeStateD.cons-BD nd) sBD)
... | PEA.evR _ sCD     = inj₂ (decConsD-ev-link linkCD (SN.NodeStateD.cons-CD nd) sCD)
... | PEA.evBoth _ sBD _ = inj₁ (decConsD-ev-link linkBD (SN.NodeStateD.cons-BD nd) sBD)

------------------------------------------------------------------------
-- (6) THE WHOLE-NODES DISPATCH (skeleton of `PipeEvDriverCone.driverExpose`).
-- Stated on the RAW node fields (NOT on `prodOf`) so the `with`-abstraction
-- cannot renormalise an imported `PipeInv` type; the `prodOf` face is a
-- `with`-free wrapper below.
------------------------------------------------------------------------

-- a whole-nodes `sendBFBlock` on `linkAB` forces node A's AB producer to `pp5`
nodes-sbb-AB : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → IsSBB (evLabel X e a) → ApiHasLink linkAB e
  → SN.NodeStateA.prod-AB (nA s) ≡ pp5
nodes-sbb-AB s {X} {e} {a} apimem nodesStep sbb ahl
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (absNodeA (nA s)) (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s))) nodesStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sA sRest = ⊥-elim (SStep.⦀-noOffer (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s))
        (absNodeB-no-when-A (nB s) apimem (absNodeA-fp (nA s) apimem sA))
        (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
          (absNodeC-no-when-A (nC s) apimem (absNodeA-fp (nA s) apimem sA))
          (absNodeD-no-when-A (nD s) apimem (absNodeA-fp (nA s) apimem sA))) (_ , sRest))
... | PEA.evL _ sA = nodeA-sbb-AB (nA s) apimem sA sbb ahl
nodes-sbb-AB s {X} {e} {a} apimem nodesStep sbb ahl | PEA.evR _ sRest
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s)) sRest
... | PEA.evSync () _ _
... | PEA.evBoth _ sB sCD = ⊥-elim (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
        (absNodeC-no-when-B (nC s) apimem (absNodeB-fp (nB s) apimem sB))
        (absNodeD-no-when-B (nD s) apimem (absNodeB-fp (nB s) apimem sB)) (_ , sCD))
... | PEA.evL _ sB = ⊥-elim (nodeB-sbb-AB-⊥ (nB s) apimem sB sbb ahl)
nodes-sbb-AB s {X} {e} {a} apimem nodesStep sbb ahl | PEA.evR _ sRest | PEA.evR _ sCD
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absNodeC (nC s)) (absNodeD (nD s)) sCD
... | PEA.evSync () _ _
... | PEA.evBoth _ sC sD = ⊥-elim (absNodeD-no-when-C (nD s) apimem (absNodeC-fp (nC s) apimem sC) (_ , sD))
... | PEA.evL _ sC with nodeC-link (nC s) apimem sC
...   | inj₁ ahlAC = ⊥-elim (linkAB≢linkAC (sym (apiLink-inj ahlAC ahl)))
...   | inj₂ ahlCD = ⊥-elim (linkAB≢linkCD (sym (apiLink-inj ahlCD ahl)))
nodes-sbb-AB s {X} {e} {a} apimem nodesStep sbb ahl | PEA.evR _ sRest | PEA.evR _ sCD | PEA.evR _ sD
    with nodeD-link (nD s) apimem sD
... | inj₁ ahlBD = ⊥-elim (linkAB≢linkBD (sym (apiLink-inj ahlBD ahl)))
... | inj₂ ahlCD = ⊥-elim (linkAB≢linkCD (sym (apiLink-inj ahlCD ahl)))

-- a whole-nodes `sendBFBlock` on `linkAC` forces node A's AC producer to `pp5`
nodes-sbb-AC : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → IsSBB (evLabel X e a) → ApiHasLink linkAC e
  → SN.NodeStateA.prod-AC (nA s) ≡ pp5
nodes-sbb-AC s {X} {e} {a} apimem nodesStep sbb ahl
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (absNodeA (nA s)) (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s))) nodesStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sA sRest = ⊥-elim (SStep.⦀-noOffer (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s))
        (absNodeB-no-when-A (nB s) apimem (absNodeA-fp (nA s) apimem sA))
        (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
          (absNodeC-no-when-A (nC s) apimem (absNodeA-fp (nA s) apimem sA))
          (absNodeD-no-when-A (nD s) apimem (absNodeA-fp (nA s) apimem sA))) (_ , sRest))
... | PEA.evL _ sA = nodeA-sbb-AC (nA s) apimem sA sbb ahl
nodes-sbb-AC s {X} {e} {a} apimem nodesStep sbb ahl | PEA.evR _ sRest
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s)) sRest
... | PEA.evSync () _ _
... | PEA.evBoth _ sB sCD = ⊥-elim (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
        (absNodeC-no-when-B (nC s) apimem (absNodeB-fp (nB s) apimem sB))
        (absNodeD-no-when-B (nD s) apimem (absNodeB-fp (nB s) apimem sB)) (_ , sCD))
... | PEA.evL _ sB with nodeB-link (nB s) apimem sB
...   | inj₁ ahlAB = ⊥-elim (linkAB≢linkAC (apiLink-inj ahlAB ahl))
...   | inj₂ ahlBD = ⊥-elim (linkAC≢linkBD (sym (apiLink-inj ahlBD ahl)))
nodes-sbb-AC s {X} {e} {a} apimem nodesStep sbb ahl | PEA.evR _ sRest | PEA.evR _ sCD
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absNodeC (nC s)) (absNodeD (nD s)) sCD
... | PEA.evSync () _ _
... | PEA.evBoth _ sC sD = ⊥-elim (absNodeD-no-when-C (nD s) apimem (absNodeC-fp (nC s) apimem sC) (_ , sD))
... | PEA.evL _ sC = ⊥-elim (nodeC-sbb-AC-⊥ (nC s) apimem sC sbb ahl)
nodes-sbb-AC s {X} {e} {a} apimem nodesStep sbb ahl | PEA.evR _ sRest | PEA.evR _ sCD | PEA.evR _ sD
    with nodeD-link (nD s) apimem sD
... | inj₁ ahlBD = ⊥-elim (linkAC≢linkBD (sym (apiLink-inj ahlBD ahl)))
... | inj₂ ahlCD = ⊥-elim (linkAC≢linkCD (sym (apiLink-inj ahlCD ahl)))

------------------------------------------------------------------------
-- (7) THE TOP LEVEL — peel the hide/medium stack (the medium offers NO api,
-- `medium-api-non-offer`), land on the whole-nodes step, apply (6).
------------------------------------------------------------------------

-- raw-field form on the AB leg (carries the `with`; mentions no `PipeInv` type)
reach-sbb-AB : (r : RState) {b : Block₃} {M : NetProc}
  → radec r ─[ ev (evl (evLabel Block₃ (apiBF linkAB hi sendBFBlock) b)) ]─► M
  → SN.NodeStateA.prod-AB (nA (toSys r)) ≡ pp5
reach-sbb-AB r {b} step
  with reflect-top-ev (decMed (med (toSys r))) (absNodesOf (toSys r))
         (inj₁ (medium-api-non-offer (med (toSys r)) aicBF)) step
... | medEv M₁ ms _      = ⊥-elim (medium-api-non-offer (med (toSys r)) aicBF (M₁ , ms))
... | nodesEv N₁ ns refl = nodes-sbb-AB (toSys r) tt ns (sbb-here linkAB hi b) ahlBF

-- raw-field form on the AC leg
reach-sbb-AC : (r : RState) {b : Block₃} {M : NetProc}
  → radec r ─[ ev (evl (evLabel Block₃ (apiBF linkAC hi sendBFBlock) b)) ]─► M
  → SN.NodeStateA.prod-AC (nA (toSys r)) ≡ pp5
reach-sbb-AC r {b} step
  with reflect-top-ev (decMed (med (toSys r))) (absNodesOf (toSys r))
         (inj₁ (medium-api-non-offer (med (toSys r)) aicBF)) step
... | medEv M₁ ms _      = ⊥-elim (medium-api-non-offer (med (toSys r)) aicBF (M₁ , ms))
... | nodesEv N₁ ns refl = nodes-sbb-AC (toSys r) tt ns (sbb-here linkAC hi b) ahlBF

------------------------------------------------------------------------
-- (E2), the consumer-facing face: `with`-FREE wrappers in `prodOf` shape (the
-- exact antecedent `PipeInvProd.pipeInvS⇒Pr` demands).
------------------------------------------------------------------------

-- (E2) AB leg: firing `apiBF linkAB hi sendBFBlock` pins leg BD's producer to `pp5`
prodFire-AB : (r : RState) {b : Block₃} {M : NetProc}
  → radec r ─[ ev (evl (evLabel Block₃ (apiBF linkAB hi sendBFBlock) b)) ]─► M
  → prodOf legBD (toSys r) ≡ pp5
prodFire-AB r step = reach-sbb-AB r step

-- (E2) AC leg: firing `apiBF linkAC hi sendBFBlock` pins leg CD's producer to `pp5`
prodFire-AC : (r : RState) {b : Block₃} {M : NetProc}
  → radec r ─[ ev (evl (evLabel Block₃ (apiBF linkAC hi sendBFBlock) b)) ]─► M
  → prodOf legCD (toSys r) ≡ pp5
prodFire-AC r step = reach-sbb-AC r step
