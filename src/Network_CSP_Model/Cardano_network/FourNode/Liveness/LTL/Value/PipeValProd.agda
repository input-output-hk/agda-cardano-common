{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the PRODUCER-VALUE cone (`Praos.PipeValProd`),
-- SESSION-48 step (v).
--
-- `PipeProdFire.prodFire-{AB,AC}` inverts a strong visible
-- `apiBF link{AB,AC} hi sendBFBlock ! b` and concludes the PHASE
-- (`prodOf l (toSys r) ≡ pp5`), dropping the value the `!` pins.  This module
-- concludes the VALUE (`b ≡ blkA`) over the same dispatch.
--
-- A PARALLEL LEAF, NOT A WIDENING — and that is the economy.  The phase fact and
-- the value fact are INDEPENDENT: both are read off the same step, but neither
-- needs the other.  So instead of giving `nodes-sbb-{AB,AC}` a product
-- conclusion — a type change with no `Σ` to widen, costing ~4 consumer sites
-- (`reach-sbb`, `prodFire`, `PipeLocate.weak-pp5`) — the value cone is built
-- beside it.  **`PipeProdFire` is not edited and no consumer moves.**
--
-- THE ICE-DODGING INTERFACE (approved).  `nodeA-sbb-AB`'s label is GENERIC
-- (`X`/`e`/`a`) and the driver step is only reachable inside a `with` branch, so
-- projecting a value out of it would apply a function to a `with`-abstracted
-- variable in the result type — the documented `__IMPOSSIBLE__` trigger
-- (`Substitute.hs:139`).  Instead the CALLER supplies the label equation
-- (`SbbVal` below); it is `refl` at `prodFire-blkA-{AB,AC}`, whose carrier is
-- already `Block₃`, and inside the cone it transports the driver step to the
-- pinned label before `PipeValFill.decProd-sbb-blkA` reads the value off it.
--
-- Every refutation branch is `PipeProdFire`'s verbatim: only the ONE productive
-- branch per lemma differs.
--
-- No postulate/hole/meta.  `PipeProdFire` stays READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Relation.Nullary using ( ¬_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; trans; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValProd (blkA : Block₃) where

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
open Op using ( Skip )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel; Event )

import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload}) as PEA

import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using ( ProdPh; pp0; pp5
              ; ConsPh; cp0; cp1; cp2; cp3; cp4; cp5; cp6
              ; ConsDPh; consD
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
  ( ApiHasLink; apiLink-inj; ahlBF; aicBF; decProd-ev-link )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysRoute blkA using
  ( medium-api-non-offer
  ; absNodeA-fp; absNodeB-fp; absNodeC-fp
  ; absNodeB-no-when-A; absNodeC-no-when-A; absNodeD-no-when-A
  ; absNodeC-no-when-B; absNodeD-no-when-B; absNodeD-no-when-C )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink blkA using
  ( linkAB≢linkAC; linkAB≢linkBD; linkAC≢linkCD; linkBD≢linkCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( ret-no-ev; bind-ev-inv; step-fcong )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeEvRelay blkA
  using ( pp0≢pp5 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValInv blkA
  using ( RelayValOK )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeProdFire blkA using
  ( IsSBB; sbb-here; decProd-sbb-pp5; decCons-sbb-⊥
  ; linkAB≢linkCD; linkAC≢linkBD
  ; nodeB-sbb-AB-⊥; nodeC-sbb-AC-⊥; nodeB-link; nodeC-link; nodeD-link )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValFill blkA using
  ( decProd-sbb-blkA; decProd-sbb-val )

------------------------------------------------------------------------
-- The caller-supplied-label interface.  `SbbVal l e a` says: whenever the fired
-- observation IS `apiBF l hi sendBFBlock` carrying `b`, that `b` is `blkA`.
-- Keeping the label equation as a HYPOTHESIS is what stops the generic cone from
-- projecting a value out of a `with`-abstracted variable.
------------------------------------------------------------------------

-- the fired `sendBFBlock` on link `l`, whatever its value, is `blkA`
SbbVal : (l : Link) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) → Set₁
SbbVal l {X} e a =
  (b : Block₃) → evLabel X e a ≡ evLabel Block₃ (apiBF l hi sendBFBlock) b → b ≡ blkA

------------------------------------------------------------------------
-- (1) NODE A.  The productive branch transports the driver step to the pinned
-- phase (`decProd-sbb-pp5`) and then to the pinned label (the caller's
-- equation), and reads the value off the `!` (`decProd-sbb-blkA`).
------------------------------------------------------------------------

-- node A firing `sendBFBlock` on `linkAB` fires it at `blkA`
nodeA-sbb-blkA-AB : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeA na ─[ ev (evl (evLabel X e a)) ]─► M
  → IsSBB (evLabel X e a) → ApiHasLink linkAB e
  → SbbVal linkAB e a
nodeA-sbb-blkA-AB na {X} {e} {a} apimem step sbb ahl
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
... | PEA.evL _ sAB = λ b lbl →
      decProd-sbb-blkA linkAB hi
        (subst (λ z → SN.decProd linkAB hi blkA pp5 ─[ ev (evl z) ]─► _) lbl
          (subst (λ ph → SN.decProd linkAB hi blkA ph ─[ ev (evl (evLabel X e a)) ]─► _)
                 (decProd-sbb-pp5 linkAB hi blkA (SN.NodeStateA.prod-AB na) sAB sbb) sAB))
... | PEA.evR _ sAC = ⊥-elim (linkAB≢linkAC
        (sym (apiLink-inj (decProd-ev-link linkAC hi blkA (SN.NodeStateA.prod-AC na) sAC) ahl)))
... | PEA.evBoth _ _ sAC = ⊥-elim (linkAB≢linkAC
        (sym (apiLink-inj (decProd-ev-link linkAC hi blkA (SN.NodeStateA.prod-AC na) sAC) ahl)))

-- node A firing `sendBFBlock` on `linkAC` fires it at `blkA` (mirror)
nodeA-sbb-blkA-AC : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeA na ─[ ev (evl (evLabel X e a)) ]─► M
  → IsSBB (evLabel X e a) → ApiHasLink linkAC e
  → SbbVal linkAC e a
nodeA-sbb-blkA-AC na {X} {e} {a} apimem step sbb ahl
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
... | PEA.evR _ sAC = λ b lbl →
      decProd-sbb-blkA linkAC hi
        (subst (λ z → SN.decProd linkAC hi blkA pp5 ─[ ev (evl z) ]─► _) lbl
          (subst (λ ph → SN.decProd linkAC hi blkA ph ─[ ev (evl (evLabel X e a)) ]─► _)
                 (decProd-sbb-pp5 linkAC hi blkA (SN.NodeStateA.prod-AC na) sAC sbb) sAC))
... | PEA.evL _ sAB = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (decProd-ev-link linkAB hi blkA (SN.NodeStateA.prod-AB na) sAB) ahl))
... | PEA.evBoth _ sAB _ = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (decProd-ev-link linkAB hi blkA (SN.NodeStateA.prod-AB na) sAB) ahl))

------------------------------------------------------------------------
-- (2) THE WHOLE-NODES DISPATCH.  Every refutation branch is
-- `PipeProdFire.nodes-sbb-{AB,AC}`'s verbatim; only the node-A branch differs.
------------------------------------------------------------------------

-- a whole-nodes `sendBFBlock` on `linkAB` fires at `blkA`
nodes-sbb-blkA-AB : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → IsSBB (evLabel X e a) → ApiHasLink linkAB e
  → SbbVal linkAB e a
nodes-sbb-blkA-AB s {X} {e} {a} apimem nodesStep sbb ahl
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (absNodeA (nA s)) (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s))) nodesStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sA sRest = ⊥-elim (SStep.⦀-noOffer (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s))
        (absNodeB-no-when-A (nB s) apimem (absNodeA-fp (nA s) apimem sA))
        (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
          (absNodeC-no-when-A (nC s) apimem (absNodeA-fp (nA s) apimem sA))
          (absNodeD-no-when-A (nD s) apimem (absNodeA-fp (nA s) apimem sA))) (_ , sRest))
... | PEA.evL _ sA = nodeA-sbb-blkA-AB (nA s) apimem sA sbb ahl
nodes-sbb-blkA-AB s {X} {e} {a} apimem nodesStep sbb ahl | PEA.evR _ sRest
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s)) sRest
... | PEA.evSync () _ _
... | PEA.evBoth _ sB sCD = ⊥-elim (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
        (absNodeC-no-when-B (nC s) apimem (absNodeB-fp (nB s) apimem sB))
        (absNodeD-no-when-B (nD s) apimem (absNodeB-fp (nB s) apimem sB)) (_ , sCD))
... | PEA.evL _ sB = ⊥-elim (nodeB-sbb-AB-⊥ (nB s) apimem sB sbb ahl)
nodes-sbb-blkA-AB s {X} {e} {a} apimem nodesStep sbb ahl | PEA.evR _ sRest | PEA.evR _ sCD
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absNodeC (nC s)) (absNodeD (nD s)) sCD
... | PEA.evSync () _ _
... | PEA.evBoth _ sC sD = ⊥-elim (absNodeD-no-when-C (nD s) apimem (absNodeC-fp (nC s) apimem sC) (_ , sD))
... | PEA.evL _ sC with nodeC-link (nC s) apimem sC
...   | inj₁ ahlAC = ⊥-elim (linkAB≢linkAC (sym (apiLink-inj ahlAC ahl)))
...   | inj₂ ahlCD = ⊥-elim (linkAB≢linkCD (sym (apiLink-inj ahlCD ahl)))
nodes-sbb-blkA-AB s {X} {e} {a} apimem nodesStep sbb ahl | PEA.evR _ sRest | PEA.evR _ sCD | PEA.evR _ sD
    with nodeD-link (nD s) apimem sD
... | inj₁ ahlBD = ⊥-elim (linkAB≢linkBD (sym (apiLink-inj ahlBD ahl)))
... | inj₂ ahlCD = ⊥-elim (linkAB≢linkCD (sym (apiLink-inj ahlCD ahl)))

-- a whole-nodes `sendBFBlock` on `linkAC` fires at `blkA` (mirror)
nodes-sbb-blkA-AC : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → IsSBB (evLabel X e a) → ApiHasLink linkAC e
  → SbbVal linkAC e a
nodes-sbb-blkA-AC s {X} {e} {a} apimem nodesStep sbb ahl
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (absNodeA (nA s)) (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s))) nodesStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sA sRest = ⊥-elim (SStep.⦀-noOffer (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s))
        (absNodeB-no-when-A (nB s) apimem (absNodeA-fp (nA s) apimem sA))
        (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
          (absNodeC-no-when-A (nC s) apimem (absNodeA-fp (nA s) apimem sA))
          (absNodeD-no-when-A (nD s) apimem (absNodeA-fp (nA s) apimem sA))) (_ , sRest))
... | PEA.evL _ sA = nodeA-sbb-blkA-AC (nA s) apimem sA sbb ahl
nodes-sbb-blkA-AC s {X} {e} {a} apimem nodesStep sbb ahl | PEA.evR _ sRest
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s)) sRest
... | PEA.evSync () _ _
... | PEA.evBoth _ sB sCD = ⊥-elim (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
        (absNodeC-no-when-B (nC s) apimem (absNodeB-fp (nB s) apimem sB))
        (absNodeD-no-when-B (nD s) apimem (absNodeB-fp (nB s) apimem sB)) (_ , sCD))
... | PEA.evL _ sB with nodeB-link (nB s) apimem sB
...   | inj₁ ahlAB = ⊥-elim (linkAB≢linkAC (apiLink-inj ahlAB ahl))
...   | inj₂ ahlBD = ⊥-elim (linkAC≢linkBD (sym (apiLink-inj ahlBD ahl)))
nodes-sbb-blkA-AC s {X} {e} {a} apimem nodesStep sbb ahl | PEA.evR _ sRest | PEA.evR _ sCD
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absNodeC (nC s)) (absNodeD (nD s)) sCD
... | PEA.evSync () _ _
... | PEA.evBoth _ sC sD = ⊥-elim (absNodeD-no-when-C (nD s) apimem (absNodeC-fp (nC s) apimem sC) (_ , sD))
... | PEA.evL _ sC = ⊥-elim (nodeC-sbb-AC-⊥ (nC s) apimem sC sbb ahl)
nodes-sbb-blkA-AC s {X} {e} {a} apimem nodesStep sbb ahl | PEA.evR _ sRest | PEA.evR _ sCD | PEA.evR _ sD
    with nodeD-link (nD s) apimem sD
... | inj₁ ahlBD = ⊥-elim (linkAC≢linkBD (sym (apiLink-inj ahlBD ahl)))
... | inj₂ ahlCD = ⊥-elim (linkAC≢linkCD (sym (apiLink-inj ahlCD ahl)))

------------------------------------------------------------------------
-- (3) THE TOP LEVEL.  Peel the hide/medium stack (the medium offers no api),
-- land on the whole-nodes step, and instantiate the label equation at `refl` —
-- at this level the carrier IS `Block₃`, so no transport is needed.
------------------------------------------------------------------------

-- a strong `apiBF linkAB hi sendBFBlock ! b` out of a reachable config has `b ≡ blkA`
prodFire-blkA-AB : (r : RState) {b : Block₃} {M : NetProc}
  → radec r ─[ ev (evl (evLabel Block₃ (apiBF linkAB hi sendBFBlock) b)) ]─► M
  → b ≡ blkA
prodFire-blkA-AB r {b} step
  with reflect-top-ev (decMed (med (toSys r))) (absNodesOf (toSys r))
         (inj₁ (medium-api-non-offer (med (toSys r)) aicBF)) step
... | medEv M₁ ms _      = ⊥-elim (medium-api-non-offer (med (toSys r)) aicBF (M₁ , ms))
... | nodesEv N₁ ns refl =
      nodes-sbb-blkA-AB (toSys r) tt ns (sbb-here linkAB hi b) ahlBF b refl

-- the AC mirror
prodFire-blkA-AC : (r : RState) {b : Block₃} {M : NetProc}
  → radec r ─[ ev (evl (evLabel Block₃ (apiBF linkAC hi sendBFBlock) b)) ]─► M
  → b ≡ blkA
prodFire-blkA-AC r {b} step
  with reflect-top-ev (decMed (med (toSys r))) (absNodesOf (toSys r))
         (inj₁ (medium-api-non-offer (med (toSys r)) aicBF)) step
... | medEv M₁ ms _      = ⊥-elim (medium-api-non-offer (med (toSys r)) aicBF (M₁ , ms))
... | nodesEv N₁ ns refl =
      nodes-sbb-blkA-AC (toSys r) tt ns (sbb-here linkAC hi b) ahlBF b refl

------------------------------------------------------------------------
-- (4) THE MISSING PREREQUISITE: `nodeA-link`.
--
-- `PipeProdFire` exports `nodeB-link`/`nodeC-link`/`nodeD-link` but NOT the
-- node-A analogue — it never needed one, because its two productive lemmas are
-- exactly node A's own links, so node A is never the node being refuted there.
-- A BD/CD dispatch DOES have to refute node A, hence this.
--
-- Mirror of `nodeB-link`, with one structural difference: node B's driver is a
-- single `decCP`, so its link comes straight from `decCP-ev-link`, whereas node
-- A's driver is a `⦀` PAIR of `decProd`s, so the pair has to be peeled first and
-- the link read off whichever arm fired.
------------------------------------------------------------------------

-- node A's api events live on `linkAB` or `linkAC` (its two produce drivers)
nodeA-link : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeA na ─[ ev (evl (evLabel X e a)) ]─► M
  → ApiHasLink linkAB e ⊎ ApiHasLink linkAC e
nodeA-link na {X} {e} {a} apimem step
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
... | PEA.evL _ sAB     = inj₁ (decProd-ev-link linkAB hi blkA (SN.NodeStateA.prod-AB na) sAB)
... | PEA.evR _ sAC     = inj₂ (decProd-ev-link linkAC hi blkA (SN.NodeStateA.prod-AC na) sAC)
... | PEA.evBoth _ sAB _ = inj₁ (decProd-ev-link linkAB hi blkA (SN.NodeStateA.prod-AB na) sAB)

------------------------------------------------------------------------
-- (5) THE SECOND MISSING PREREQUISITE: node D never fires `sendBFBlock`.
--
-- `PipeProdFire`'s dispatch only ever targets node A's links (AB/AC), so it
-- refutes every OTHER node by LINK DISEQUALITY alone and never needs a
-- per-node `sendBFBlock` refutation (its header says of node D: "both links
-- differ").  A BD/CD dispatch cannot use that argument for node D, which OWNS
-- both those links — so the refutation has to be built.
--
-- My threading-3 pre-flight checked which `node*-link` lemmas existed but NOT
-- which per-node `sendBFBlock` refutations existed; this is the gap that check
-- missed.  The asymmetry is structural: a dispatch on link `l` needs an
-- sbb-refutation exactly for the nodes that OWN `l` but do not produce on it.
------------------------------------------------------------------------

-- node D's consume driver never fires `sendBFBlock` (the api is not in
-- `consume`; the `>> Skip` bind is peeled and the inner chain refutes)
decConsD-sbb-⊥ : (l : Link) (cd : ConsDPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → SN.decConsD l cd ─[ ev (evl (evLabel X e a)) ]─► M → IsSBB (evLabel X e a) → ⊥
decConsD-sbb-⊥ l (consD b cp0) step sbb
  with bind-ev-inv (λ _ → Skip) (SN.decCons l hi b cp0) refl step
... | _ , sc , refl = decCons-sbb-⊥ l hi b cp0 sc sbb
decConsD-sbb-⊥ l (consD b cp1) step sbb
  with bind-ev-inv (λ _ → Skip) (SN.decCons l hi b cp1) refl step
... | _ , sc , refl = decCons-sbb-⊥ l hi b cp1 sc sbb
decConsD-sbb-⊥ l (consD b cp2) step sbb
  with bind-ev-inv (λ _ → Skip) (SN.decCons l hi b cp2) refl step
... | _ , sc , refl = decCons-sbb-⊥ l hi b cp2 sc sbb
decConsD-sbb-⊥ l (consD b cp3) step sbb
  with bind-ev-inv (λ _ → Skip) (SN.decCons l hi b cp3) refl step
... | _ , sc , refl = decCons-sbb-⊥ l hi b cp3 sc sbb
decConsD-sbb-⊥ l (consD b cp4) step sbb
  with bind-ev-inv (λ _ → Skip) (SN.decCons l hi b cp4) refl step
... | _ , sc , refl = decCons-sbb-⊥ l hi b cp4 sc sbb
decConsD-sbb-⊥ l (consD b cp5) step sbb
  with bind-ev-inv (λ _ → Skip) (SN.decCons l hi b cp5) refl step
... | _ , sc , refl = decCons-sbb-⊥ l hi b cp5 sc sbb
decConsD-sbb-⊥ l (consD b cp6) step sbb = ret-no-ev refl step

-- node D never fires `sendBFBlock` on EITHER of its links
nodeD-sbb-⊥ : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeD nd ─[ ev (evl (evLabel X e a)) ]─► M → IsSBB (evLabel X e a) → ⊥
nodeD-sbb-⊥ nd {X} {e} {a} apimem step sbb
  with SStep.reflect-node-api
         (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
          ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
         (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd)
          ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd))
           (SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)) dStep
... | PEA.evSync () _ _
... | PEA.evL _ sBD      = decConsD-sbb-⊥ linkBD (SN.NodeStateD.cons-BD nd) sBD sbb
... | PEA.evR _ sCD      = decConsD-sbb-⊥ linkCD (SN.NodeStateD.cons-CD nd) sCD sbb
... | PEA.evBoth _ sBD _ = decConsD-sbb-⊥ linkBD (SN.NodeStateD.cons-BD nd) sBD sbb

------------------------------------------------------------------------
-- (6) THE RELAY'S PRODUCE-LEG VALUE PIN.  A `sendBFBlock` out of `decCP l₁ l₂`
-- can only be the PRODUCE arm's `pp5` hop, where the `!` pins the value to the
-- relay's RECORDED block — which `PipeVal` clause (4) (`RelayValOK`) says is
-- `blkA`.  The consume arm has no `sendBFBlock` at all.
--
-- Unlike `PipeProdFire.decCP-sbb-⊥`, which refutes by LINK disequality, here the
-- fired link IS `l₂`, so the `cp6` hand-off is refuted by PHASE instead
-- (`pp0 ≢ pp5`) — the produce leg's first hop is `apiCS`, not `sendBFBlock`.
------------------------------------------------------------------------

-- a `sendBFBlock` out of a relay driver carries `blkA`, given clause (4)
decCP-sbb-val : (l₁ l₂ : Link) (x : CPPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → SN.decCP l₁ l₂ x ─[ ev (evl (evLabel X e a)) ]─► M
  → IsSBB (evLabel X e a) → RelayValOK x → SbbVal l₂ e a
decCP-sbb-val l₁ l₂ (consuming b cp0) step sbb h
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (SN.decCons l₁ hi b cp0) refl step
... | _ , sc , refl = ⊥-elim (decCons-sbb-⊥ l₁ hi b cp0 sc sbb)
decCP-sbb-val l₁ l₂ (consuming b cp1) step sbb h
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (SN.decCons l₁ hi b cp1) refl step
... | _ , sc , refl = ⊥-elim (decCons-sbb-⊥ l₁ hi b cp1 sc sbb)
decCP-sbb-val l₁ l₂ (consuming b cp2) step sbb h
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (SN.decCons l₁ hi b cp2) refl step
... | _ , sc , refl = ⊥-elim (decCons-sbb-⊥ l₁ hi b cp2 sc sbb)
decCP-sbb-val l₁ l₂ (consuming b cp3) step sbb h
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (SN.decCons l₁ hi b cp3) refl step
... | _ , sc , refl = ⊥-elim (decCons-sbb-⊥ l₁ hi b cp3 sc sbb)
decCP-sbb-val l₁ l₂ (consuming b cp4) step sbb h
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (SN.decCons l₁ hi b cp4) refl step
... | _ , sc , refl = ⊥-elim (decCons-sbb-⊥ l₁ hi b cp4 sc sbb)
decCP-sbb-val l₁ l₂ (consuming b cp5) step sbb h
  with bind-ev-inv (λ b′ → produce l₂ hi b′) (SN.decCons l₁ hi b cp5) refl step
... | _ , sc , refl = ⊥-elim (decCons-sbb-⊥ l₁ hi b cp5 sc sbb)
-- the `cp6` hand-off fires `produce`'s FIRST hop (`apiCS`), i.e. phase `pp0`
decCP-sbb-val l₁ l₂ (consuming b cp6) step sbb h =
  ⊥-elim (pp0≢pp5 (decProd-sbb-pp5 l₂ hi b pp0 (step-fcong refl step) sbb))
-- the produce arm: pin the phase, then the label, then read the `!`
decCP-sbb-val l₁ l₂ (producing b pp) {X} {e} {a} step sbb h = λ b′ lbl →
  trans (decProd-sbb-val l₂ hi b
          (subst (λ z → SN.decProd l₂ hi b pp5 ─[ ev (evl z) ]─► _) lbl
            (subst (λ ph → SN.decProd l₂ hi b ph ─[ ev (evl (evLabel X e a)) ]─► _)
                   (decProd-sbb-pp5 l₂ hi b pp step sbb) step)))
        h

------------------------------------------------------------------------
-- (7) THE TWO RELAY NODES.  Node B/C's driver is a SINGLE `decCP`, so the peel
-- is just `reflect-node-api` — no driver-pair split (contrast node A).
------------------------------------------------------------------------

-- node B firing `sendBFBlock` on `linkBD` fires it at `blkA`, given clause (4)
nodeB-sbb-blkA-BD : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeB nb ─[ ev (evl (evLabel X e a)) ]─► M
  → IsSBB (evLabel X e a) → RelayValOK (SN.NodeStateB.cp-B nb)
  → SbbVal linkBD e a
nodeB-sbb-blkA-BD nb {X} {e} {a} apimem step sbb h
  with SStep.reflect-node-api
         (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
          ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
         (SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl =
      decCP-sbb-val linkAB linkBD (SN.NodeStateB.cp-B nb) dStep sbb h

-- node C firing `sendBFBlock` on `linkCD` fires it at `blkA` (mirror)
nodeC-sbb-blkA-CD : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeC nc ─[ ev (evl (evLabel X e a)) ]─► M
  → IsSBB (evLabel X e a) → RelayValOK (SN.NodeStateC.cp-C nc)
  → SbbVal linkCD e a
nodeC-sbb-blkA-CD nc {X} {e} {a} apimem step sbb h
  with SStep.reflect-node-api
         (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
          ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
         (SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl =
      decCP-sbb-val linkAC linkCD (SN.NodeStateC.cp-C nc) dStep sbb h

------------------------------------------------------------------------
-- (8) THE WHOLE-NODES DISPATCH ON THE DOWNSTREAM LINKS.
--
-- OWNER ENUMERATION (the pre-flight rule): `linkBD` is owned by node B (which
-- PRODUCES on it) and node D (which consumes); `linkCD` by node C (produces) and
-- node D.  So node D is the only owner that needs an sbb-REFUTATION
-- (`nodeD-sbb-⊥`), and nodes A/B/C are refuted on the other link by disequality.
------------------------------------------------------------------------

-- a whole-nodes `sendBFBlock` on `linkBD` fires at `blkA`, given clause (4)
nodes-sbb-relayVal-BD : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → IsSBB (evLabel X e a) → ApiHasLink linkBD e
  → RelayValOK (SN.NodeStateB.cp-B (nB s))
  → SbbVal linkBD e a
nodes-sbb-relayVal-BD s {X} {e} {a} apimem nodesStep sbb ahl h
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (absNodeA (nA s)) (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s))) nodesStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sA sRest = ⊥-elim (SStep.⦀-noOffer (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s))
        (absNodeB-no-when-A (nB s) apimem (absNodeA-fp (nA s) apimem sA))
        (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
          (absNodeC-no-when-A (nC s) apimem (absNodeA-fp (nA s) apimem sA))
          (absNodeD-no-when-A (nD s) apimem (absNodeA-fp (nA s) apimem sA))) (_ , sRest))
... | PEA.evL _ sA with nodeA-link (nA s) apimem sA
...   | inj₁ ahlAB = ⊥-elim (linkAB≢linkBD (apiLink-inj ahlAB ahl))
...   | inj₂ ahlAC = ⊥-elim (linkAC≢linkBD (apiLink-inj ahlAC ahl))
nodes-sbb-relayVal-BD s {X} {e} {a} apimem nodesStep sbb ahl h | PEA.evR _ sRest
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s)) sRest
... | PEA.evSync () _ _
... | PEA.evBoth _ sB sCD = ⊥-elim (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
        (absNodeC-no-when-B (nC s) apimem (absNodeB-fp (nB s) apimem sB))
        (absNodeD-no-when-B (nD s) apimem (absNodeB-fp (nB s) apimem sB)) (_ , sCD))
... | PEA.evL _ sB = nodeB-sbb-blkA-BD (nB s) apimem sB sbb h
nodes-sbb-relayVal-BD s {X} {e} {a} apimem nodesStep sbb ahl h | PEA.evR _ sRest | PEA.evR _ sCD
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absNodeC (nC s)) (absNodeD (nD s)) sCD
... | PEA.evSync () _ _
... | PEA.evBoth _ sC sD = ⊥-elim (absNodeD-no-when-C (nD s) apimem (absNodeC-fp (nC s) apimem sC) (_ , sD))
... | PEA.evL _ sC with nodeC-link (nC s) apimem sC
...   | inj₁ ahlAC = ⊥-elim (linkAC≢linkBD (apiLink-inj ahlAC ahl))
...   | inj₂ ahlCD = ⊥-elim (linkBD≢linkCD (sym (apiLink-inj ahlCD ahl)))
nodes-sbb-relayVal-BD s {X} {e} {a} apimem nodesStep sbb ahl h | PEA.evR _ sRest | PEA.evR _ sCD | PEA.evR _ sD =
  ⊥-elim (nodeD-sbb-⊥ (nD s) apimem sD sbb)

-- a whole-nodes `sendBFBlock` on `linkCD` fires at `blkA` (mirror)
nodes-sbb-relayVal-CD : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → IsSBB (evLabel X e a) → ApiHasLink linkCD e
  → RelayValOK (SN.NodeStateC.cp-C (nC s))
  → SbbVal linkCD e a
nodes-sbb-relayVal-CD s {X} {e} {a} apimem nodesStep sbb ahl h
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (absNodeA (nA s)) (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s))) nodesStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sA sRest = ⊥-elim (SStep.⦀-noOffer (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s))
        (absNodeB-no-when-A (nB s) apimem (absNodeA-fp (nA s) apimem sA))
        (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
          (absNodeC-no-when-A (nC s) apimem (absNodeA-fp (nA s) apimem sA))
          (absNodeD-no-when-A (nD s) apimem (absNodeA-fp (nA s) apimem sA))) (_ , sRest))
... | PEA.evL _ sA with nodeA-link (nA s) apimem sA
...   | inj₁ ahlAB = ⊥-elim (linkAB≢linkCD (apiLink-inj ahlAB ahl))
...   | inj₂ ahlAC = ⊥-elim (linkAC≢linkCD (apiLink-inj ahlAC ahl))
nodes-sbb-relayVal-CD s {X} {e} {a} apimem nodesStep sbb ahl h | PEA.evR _ sRest
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s)) sRest
... | PEA.evSync () _ _
... | PEA.evBoth _ sB sCD = ⊥-elim (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
        (absNodeC-no-when-B (nC s) apimem (absNodeB-fp (nB s) apimem sB))
        (absNodeD-no-when-B (nD s) apimem (absNodeB-fp (nB s) apimem sB)) (_ , sCD))
... | PEA.evL _ sB with nodeB-link (nB s) apimem sB
...   | inj₁ ahlAB = ⊥-elim (linkAB≢linkCD (apiLink-inj ahlAB ahl))
...   | inj₂ ahlBD = ⊥-elim (linkBD≢linkCD (apiLink-inj ahlBD ahl))
nodes-sbb-relayVal-CD s {X} {e} {a} apimem nodesStep sbb ahl h | PEA.evR _ sRest | PEA.evR _ sCD
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absNodeC (nC s)) (absNodeD (nD s)) sCD
... | PEA.evSync () _ _
... | PEA.evBoth _ sC sD = ⊥-elim (absNodeD-no-when-C (nD s) apimem (absNodeC-fp (nC s) apimem sC) (_ , sD))
... | PEA.evL _ sC = nodeC-sbb-blkA-CD (nC s) apimem sC sbb h
nodes-sbb-relayVal-CD s {X} {e} {a} apimem nodesStep sbb ahl h | PEA.evR _ sRest | PEA.evR _ sCD | PEA.evR _ sD =
  ⊥-elim (nodeD-sbb-⊥ (nD s) apimem sD sbb)

------------------------------------------------------------------------
-- (9) THE TOP LEVEL on the downstream links.  Conditional on `PipeVal`
-- clause (4), which is available at every `evStepV` call site.
------------------------------------------------------------------------

-- a strong `apiBF linkBD hi sendBFBlock ! b` has `b ≡ blkA`, given clause (4)
prodFire-relayVal-BD : (r : RState) {b : Block₃} {M : NetProc}
  → radec r ─[ ev (evl (evLabel Block₃ (apiBF linkBD hi sendBFBlock) b)) ]─► M
  → RelayValOK (SN.NodeStateB.cp-B (nB (toSys r)))
  → b ≡ blkA
prodFire-relayVal-BD r {b} step h
  with reflect-top-ev (decMed (med (toSys r))) (absNodesOf (toSys r))
         (inj₁ (medium-api-non-offer (med (toSys r)) aicBF)) step
... | medEv M₁ ms _      = ⊥-elim (medium-api-non-offer (med (toSys r)) aicBF (M₁ , ms))
... | nodesEv N₁ ns refl =
      nodes-sbb-relayVal-BD (toSys r) tt ns (sbb-here linkBD hi b) ahlBF h b refl

-- the CD mirror
prodFire-relayVal-CD : (r : RState) {b : Block₃} {M : NetProc}
  → radec r ─[ ev (evl (evLabel Block₃ (apiBF linkCD hi sendBFBlock) b)) ]─► M
  → RelayValOK (SN.NodeStateC.cp-C (nC (toSys r)))
  → b ≡ blkA
prodFire-relayVal-CD r {b} step h
  with reflect-top-ev (decMed (med (toSys r))) (absNodesOf (toSys r))
         (inj₁ (medium-api-non-offer (med (toSys r)) aicBF)) step
... | medEv M₁ ms _      = ⊥-elim (medium-api-non-offer (med (toSys r)) aicBF (M₁ , ms))
... | nodesEv N₁ ns refl =
      nodes-sbb-relayVal-CD (toSys r) tt ns (sbb-here linkCD hi b) ahlBF h b refl
