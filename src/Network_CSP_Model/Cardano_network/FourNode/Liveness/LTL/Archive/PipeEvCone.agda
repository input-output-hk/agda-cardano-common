{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the NODE-LEVEL receive-coupling dischargers
-- (`Praos.PipeEvCone`).
--
-- `PipeEvDriver.pres-relay`/`pres-cons` demand the client-holds-block fact
-- `BFcHasBlk (upClient/dnClient l s)` (`wUp`/`wDn`) on the `recvBFBlock`
-- receive boundary.  `PipeBundleRecv.bundle-recvBFBlock-forces-src` proved it
-- at the BUNDLE level (`absBundleG l cl sv … bfc …`).  THIS module pushes it up
-- ONE more level, to the NODE: a `recvBFBlock` fire out of `absNodeB`/`absNodeC`
-- (relay, upstream client) or `absNodeD` (consumer, downstream clients) forces
-- the corresponding BF-client peer to hold the block.
--
-- Each discharger reflects the node api sync (`SysStep.reflect-node-api`) into
-- the firing bundle transition, `Par-ev-elim`-dispatches to the leg-`l` bundle
-- (the OTHER bundle refuted by `absBundleG-api-no` on link mismatch), and hands
-- the isolated bundle transition to `bundle-recvBFBlock-forces-src`.  These are
-- exactly the `wUp` (relay@B = `bfC-AB`, relay@C = `bfC-AC`) and `wDn`
-- (cons@D-BD = `bfC-BD`, cons@D-CD = `bfC-CD`) witnesses the api cone must feed
-- `PipeEvDriver` on the receive boundary (pinned there by `lblD`'s label).
--
-- MEDIUM weight (a node api-sync reflection + one bundle `Par-ev-elim` +
-- the bundle bridge, per node).  No postulate/hole/meta.  Base modules
-- READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Empty using ( ⊥-elim )
open import Data.Unit.Polymorphic using ( tt )
open import Data.Product using ( _,_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Archive.PipeEvCone (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using
  ( p; apiES; Block₃; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟; Link; apiBF; recvBFBlock )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using ( Dir; lo; hi )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; EventSet ) renaming ( ∅ES to ∅ESa )
open EventSet using ( mem )

import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload}) as PEA
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN

open SStep using
  ( NetProc; absBundleG; absNodeB; absNodeC; absNodeD; reflect-node-api; apiSync )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA using
  ( ApiHasLink; ahlBF )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink6 blkA using
  ( absBundleG-api-no )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink blkA using
  ( linkAB≢linkBD; linkAC≢linkCD; linkBD≢linkCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleRecv blkA using
  ( bundle-recvBFBlock-forces-src )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA using
  ( BFcHasBlk )

------------------------------------------------------------------------
-- CONSUMER (node D).  A `recvBFBlock linkBD` / `linkCD` fire out of node D
-- forces the corresponding downstream BF client (`bfC-BD` / `bfC-CD`) to hold
-- the block — the `wDn` witness for leg BD / CD.
------------------------------------------------------------------------

-- node D, leg BD: `recvBFBlock linkBD` ⇒ `BFcHasBlk (bfC-BD nd)`
nodeD-BD-recv-forces :
    (nd : SN.NodeStateD) {a : Block₃} {M : NetProc}
  → apiES .mem (Block₃ , apiBF linkBD hi recvBFBlock) a
  → absNodeD nd ─[ ev (evl (evLabel Block₃ (apiBF linkBD hi recvBFBlock) a)) ]─► M
  → BFcHasBlk (SN.NodeStateD.bfC-BD nd)
nodeD-BD-recv-forces nd apimem step
  with reflect-node-api
         (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
          ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
         (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))
         apimem step
... | apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
           (absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) bStep
...   | PEA.evSync () _ _
...   | PEA.evL _ sBBD =
        bundle-recvBFBlock-forces-src linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) sBBD
...   | PEA.evR _ sBCD = ⊥-elim (absBundleG-api-no linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) ahlBF linkBD≢linkCD apimem (_ , sBCD))
...   | PEA.evBoth _ _ sBCD = ⊥-elim (absBundleG-api-no linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) ahlBF linkBD≢linkCD apimem (_ , sBCD))

-- node D, leg CD: `recvBFBlock linkCD` ⇒ `BFcHasBlk (bfC-CD nd)`
nodeD-CD-recv-forces :
    (nd : SN.NodeStateD) {a : Block₃} {M : NetProc}
  → apiES .mem (Block₃ , apiBF linkCD hi recvBFBlock) a
  → absNodeD nd ─[ ev (evl (evLabel Block₃ (apiBF linkCD hi recvBFBlock) a)) ]─► M
  → BFcHasBlk (SN.NodeStateD.bfC-CD nd)
nodeD-CD-recv-forces nd apimem step
  with reflect-node-api
         (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
          ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
         (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))
         apimem step
... | apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
           (absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) bStep
...   | PEA.evSync () _ _
...   | PEA.evR _ sBCD =
        bundle-recvBFBlock-forces-src linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) sBCD
...   | PEA.evL _ sBBD = ⊥-elim (absBundleG-api-no linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ahlBF (λ q → linkBD≢linkCD (sym q)) apimem (_ , sBBD))
...   | PEA.evBoth _ sBBD _ = ⊥-elim (absBundleG-api-no linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ahlBF (λ q → linkBD≢linkCD (sym q)) apimem (_ , sBBD))

------------------------------------------------------------------------
-- RELAY (node B / node C).  A `recvBFBlock linkAB` / `linkAC` fire out of the
-- relay node forces the UPSTREAM BF client (`bfC-AB` / `bfC-AC`) to hold the
-- block — the `wUp` witness for leg BD / CD.
------------------------------------------------------------------------

-- node B, upstream leg AB: `recvBFBlock linkAB` ⇒ `BFcHasBlk (bfC-AB nb)`
nodeB-AB-recv-forces :
    (nb : SN.NodeStateB) {a : Block₃} {M : NetProc}
  → apiES .mem (Block₃ , apiBF linkAB hi recvBFBlock) a
  → absNodeB nb ─[ ev (evl (evLabel Block₃ (apiBF linkAB hi recvBFBlock) a)) ]─► M
  → BFcHasBlk (SN.NodeStateB.bfC-AB nb)
nodeB-AB-recv-forces nb apimem step
  with reflect-node-api
         (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
          ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
         (SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
         apimem step
... | apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb))
           (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)) bStep
...   | PEA.evSync () _ _
...   | PEA.evL _ sBAB =
        bundle-recvBFBlock-forces-src linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) sBAB
...   | PEA.evR _ sBBD = ⊥-elim (absBundleG-api-no linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) ahlBF linkAB≢linkBD apimem (_ , sBBD))
...   | PEA.evBoth _ _ sBBD = ⊥-elim (absBundleG-api-no linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) ahlBF linkAB≢linkBD apimem (_ , sBBD))

-- node C, upstream leg AC: `recvBFBlock linkAC` ⇒ `BFcHasBlk (bfC-AC nc)`
nodeC-AC-recv-forces :
    (nc : SN.NodeStateC) {a : Block₃} {M : NetProc}
  → apiES .mem (Block₃ , apiBF linkAC hi recvBFBlock) a
  → absNodeC nc ─[ ev (evl (evLabel Block₃ (apiBF linkAC hi recvBFBlock) a)) ]─► M
  → BFcHasBlk (SN.NodeStateC.bfC-AC nc)
nodeC-AC-recv-forces nc apimem step
  with reflect-node-api
         (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
          ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
         (SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
         apimem step
... | apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc))
           (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)) bStep
...   | PEA.evSync () _ _
...   | PEA.evL _ sBAC =
        bundle-recvBFBlock-forces-src linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) sBAC
...   | PEA.evR _ sBCD = ⊥-elim (absBundleG-api-no linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) ahlBF linkAC≢linkCD apimem (_ , sBCD))
...   | PEA.evBoth _ _ sBCD = ⊥-elim (absBundleG-api-no linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) ahlBF linkAC≢linkCD apimem (_ , sBCD))
