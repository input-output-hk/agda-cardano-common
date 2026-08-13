{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the whole-nodes io EVOLUTION cone
-- (`Praos.PipeNodeIoEvo`), sub-obligation (d) of the `PipeInvProd.TauIoS` arm.
--
-- `PipeNodeFix.top-nodes-io-abs-client-cls` already delivers, for an io fire of
-- `absNodesOf s`: the successor state `s′` with `med s ≡ med s′`, the concrete
-- weak run, and the SIX driver fixities (prod-AB/prod-AC/cp-B/cp-C/cons-BD/
-- cons-CD).  What it does NOT deliver is any CONTENT for the four tracked BF
-- clients — its `ClientClass1.clAdv` carries a `ClientAdv`, which `adv-of`
-- makes total on any pair, so it says nothing — and it exposes NO server slot
-- at all (node A goes through the frozen driver-only peel
-- `WalkConvNodeFix.nodeA-ev-io-abs-fix`).
--
-- THIS leaf re-mirrors the same four-node dispatch on top of
-- `PipeBundleIoEvo.absBundleG-io-evo`, so the successor carries, per node:
--   · a `CliIoCls` for every tracked BF CLIENT  (bfC-AB on B, bfC-AC on C,
--     bfC-BD and bfC-CD on D)     — fixed / ¬-holding / the payload WAS a block
--   · a `SrvIoCls` for every tracked BF SERVER  (bfS-AB and bfS-AC on A,
--     bfS-BD on B, bfS-CD on C)   — fixed / ¬-holding
-- plus the six driver fixities, kept verbatim.  Node A is re-mirrored too (the
-- frozen peel drops both upstream servers).
--
-- The four tracked clients are exactly `PipeInv.upClient`/`dnClient` and the
-- four tracked servers exactly `PipeSrvInv.upSrv`/`dnSrv`, so the output is
-- precisely the antecedent material of `PipeInv.Coupled`'s two CLIENT clauses
-- and of `PipeSrvInv.SrvCoupled`'s two clauses.
--
-- Every non-firing node keeps ALL its slots `inj₁ refl` (its node record is a
-- LITERAL in the successor `mkSys`); a firing node's co-located non-fired peer
-- likewise (a LITERAL in the `mkNodeX`).
--
-- Imported by nothing yet.  No postulate/hole/meta.  Base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Unit.Polymorphic using ( tt )
open import Relation.Nullary using ( yes; no; ¬_ )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeNodeIoEvo (blkA : Block₃) where

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

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA
  using ( io⇒¬api; apiLink-inj )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_RouteLnLf blkA
  using ( noOffer→viewV )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink blkA
  using ( nodeA-drv-io-no; nodeB-drv-io-no; nodeC-drv-io-no; nodeD-drv-io-no
        ; linkAB≢linkAC; linkAB≢linkBD; linkAC≢linkCD; linkBD≢linkCD )
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
  using ( upClient; dnClient; BFcHasBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA
  using ( upSrv; dnSrv )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleEvo blkA
  using ( BFsHasBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleIoEvo blkA
  using ( BlkReadAt; BundleGEvRio⁺; bgEBio⁺; absBundleG-io-evo )

------------------------------------------------------------------------
-- (1) THE TWO PER-PEER io CLASSIFIERS — the bundle result's two arms, named so
-- the per-node records can carry them.
------------------------------------------------------------------------

-- one BF CLIENT peer's io evolution, INDEXED BY THE PEER'S OWN KEY `(l,d)`:
-- fixed, or the successor is not holding a block, or the io was a BF wire READ
-- AT THAT KEY carrying a block.  The key index is load-bearing: the consumer
-- discharges `Coupled`'s client clause from the CELL clause, which reads the
-- medium at the LEG's own `(link,dir,BF)`, so the fired key has to be pinned.
CliIoCls : (l : Link) (d : Dir) → SN.BFcPos → SN.BFcPos
         → {X : Set 0ℓ} → Net_Api Payload X → X → Set
CliIoCls l d bfc bfc′ e a = (bfc ≡ bfc′) ⊎ ((BFcHasBlk bfc′ → ⊥) ⊎ BlkReadAt l d bfc′ e a)

-- one BF SERVER peer's io evolution: fixed, or the successor is not holding
SrvIoCls : SN.BFsPos → SN.BFsPos → Set
SrvIoCls bfs bfs′ = (bfs ≡ bfs′) ⊎ (BFsHasBlk bfs′ → ⊥)

------------------------------------------------------------------------
-- (2) PER-NODE io PEEL RECORDS.  Each carries the CONCRETE successor node, the
-- concrete weak run, the tracked clients' `CliIoCls`, the tracked servers'
-- `SrvIoCls` and the node's driver fixities.
------------------------------------------------------------------------

-- node A hosts the TWO upstream BF servers (bfS-AB, bfS-AC) and both producers
data NodeAEvR-io (na : SN.NodeStateA) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                 (M : NetProc) : Set₁ where
  naEBio : (na′ : SN.NodeStateA) → M ≡ absNodeA na′
        → SN.decNodeA na ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeA na′
        → SrvIoCls (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.bfS-AB na′)
        → SrvIoCls (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.bfS-AC na′)
        → SN.NodeStateA.prod-AB na ≡ SN.NodeStateA.prod-AB na′
        → SN.NodeStateA.prod-AC na ≡ SN.NodeStateA.prod-AC na′
        → NodeAEvR-io na e a M

-- node B hosts the upstream client of leg BD (bfC-AB) and its downstream
-- server (bfS-BD), plus the relay driver
data NodeBEvR-io (nb : SN.NodeStateB) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                 (M : NetProc) : Set₁ where
  nbEBio : (nb′ : SN.NodeStateB) → M ≡ absNodeB nb′
        → SN.decNodeB nb ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeB nb′
        → CliIoCls linkAB hi (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfC-AB nb′) e a
        → SrvIoCls (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.bfS-BD nb′)
        → SN.NodeStateB.cp-B nb ≡ SN.NodeStateB.cp-B nb′
        → NodeBEvR-io nb e a M

-- node C mirrors node B on leg CD
data NodeCEvR-io (nc : SN.NodeStateC) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                 (M : NetProc) : Set₁ where
  ncEBio : (nc′ : SN.NodeStateC) → M ≡ absNodeC nc′
        → SN.decNodeC nc ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeC nc′
        → CliIoCls linkAC hi (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfC-AC nc′) e a
        → SrvIoCls (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.bfS-CD nc′)
        → SN.NodeStateC.cp-C nc ≡ SN.NodeStateC.cp-C nc′
        → NodeCEvR-io nc e a M

-- node D hosts the TWO downstream clients (bfC-BD, bfC-CD) and both consumers
data NodeDEvR-io (nd : SN.NodeStateD) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
                 (M : NetProc) : Set₁ where
  ndEBio : (nd′ : SN.NodeStateD) → M ≡ absNodeD nd′
        → SN.decNodeD nd ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeD nd′
        → CliIoCls linkBD hi (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfC-BD nd′) e a
        → CliIoCls linkCD hi (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfC-CD nd′) e a
        → SN.NodeStateD.cons-BD nd ≡ SN.NodeStateD.cons-BD nd′
        → SN.NodeStateD.cons-CD nd ≡ SN.NodeStateD.cons-CD nd′
        → NodeDEvR-io nd e a M

------------------------------------------------------------------------
-- (3) NODE A (re-mirror of `WalkConvNodeFix.nodeA-io-{AB,AC}-abs-fix`, whose
-- result drops both server slots).  A's two bundles put A at the SERVER end
-- (`absBundleG link lo hi`), so the fired bundle's server arm IS the tracked
-- one and the other bundle's server is a LITERAL.
------------------------------------------------------------------------

-- A fires on link AB: bfS-AB evolves (fired), bfS-AC fixed (literal)
nodeA-io-AB-evo : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeAEvR-io na e a ((Bd′ ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)))
nodeA-io-AB-evo na {X} {e} {a} iomem sBAB
  with absBundleG-io-evo linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) iomem sBAB
... | bgEBio⁺ csc′ css′ bfc′ bfs′ ip′ eq run cli srv =
      naEBio (SN.mkNodeA csc′ css′ bfc′ bfs′ (SN.NodeStateA.prod-AB na) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) ip′ (SN.NodeStateA.inert-AC na))
        (cong (λ z → (z ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na))) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeA-drv-io-no na iomem))
           (⦀-wev-L _ _
              (noOffer→viewV _ (bundleG-io-no linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)
                 (absBundleG-io-ahl linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) iomem sBAB) linkAB≢linkAC iomem))
              run))
        srv (inj₁ refl) refl refl

-- A fires on link AC: bfS-AC evolves (fired), bfS-AB fixed (literal)
nodeA-io-AC-evo : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeAEvR-io na e a ((absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ⦀ Bd′) ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)))
nodeA-io-AC-evo na {X} {e} {a} iomem sBAC
  with absBundleG-io-evo linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) iomem sBAC
... | bgEBio⁺ csc′ css′ bfc′ bfs′ ip′ eq run cli srv =
      naEBio (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na) csc′ css′ bfc′ bfs′ (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) ip′)
        (cong (λ z → (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ⦀ z) ∥⇘ apiES ⇙ (SN.decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ SN.decProd linkAC hi blkA (SN.NodeStateA.prod-AC na))) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeA-drv-io-no na iomem))
           (⦀-wev-R _ _
              (noOffer→viewV _ (bundleG-io-no linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
                 (absBundleG-io-ahl linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) iomem sBAC) (λ q → linkAB≢linkAC (sym q)) iomem))
              run))
        (inj₁ refl) srv refl refl

-- node A dispatcher: peel the two A bundles + the produce drivers
nodeA-ev-io-evo : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodeA na ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeAEvR-io na e a M
nodeA-ev-io-evo na {X} {e} {a} iomem step
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
...   | PEA.evL _ sBAB = nodeA-io-AB-evo na iomem sBAB
...   | PEA.evR _ sBAC = nodeA-io-AC-evo na iomem sBAC

------------------------------------------------------------------------
-- (4) NODE B (mirror `PipeNodeFix.nodeB-io-{AB,BD}-abs-cls`, adding the
-- server slot).  On link AB node B is the CLIENT (`hi lo`), on link BD it is
-- the SERVER (`lo hi`).
------------------------------------------------------------------------

-- B fires on link AB: bfC-AB evolves (client end), bfS-BD fixed (literal)
nodeB-io-AB-evo : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeBEvR-io nb e a ((Bd′ ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
nodeB-io-AB-evo nb {X} {e} {a} iomem sBAB
  with absBundleG-io-evo linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) iomem sBAB
... | bgEBio⁺ csc′ css′ bfc′ bfs′ ip′ eq run cli srv =
      nbEBio (SN.mkNodeB csc′ css′ bfc′ bfs′ (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) ip′ (SN.NodeStateB.inert-BD nb))
        (cong (λ z → (z ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb)) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeB-drv-io-no nb iomem))
           (⦀-wev-L _ _
              (noOffer→viewV _ (bundleG-io-no linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)
                 (absBundleG-io-ahl linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) iomem sBAB) linkAB≢linkBD iomem))
              run))
        cli (inj₁ refl) refl

-- B fires on link BD: bfS-BD evolves (server end), bfC-AB fixed (literal)
nodeB-io-BD-evo : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeBEvR-io nb e a ((absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ⦀ Bd′) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
nodeB-io-BD-evo nb {X} {e} {a} iomem sBBD
  with absBundleG-io-evo linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) iomem sBBD
... | bgEBio⁺ csc′ css′ bfc′ bfs′ ip′ eq run cli srv =
      nbEBio (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) csc′ css′ bfc′ bfs′ (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) ip′)
        (cong (λ z → (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ⦀ z) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb)) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeB-drv-io-no nb iomem))
           (⦀-wev-R _ _
              (noOffer→viewV _ (bundleG-io-no linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
                 (absBundleG-io-ahl linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) iomem sBBD) (λ q → linkAB≢linkBD (sym q)) iomem))
              run))
        (inj₁ refl) srv refl

-- node B dispatcher
nodeB-ev-io-evo : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodeB nb ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeBEvR-io nb e a M
nodeB-ev-io-evo nb {X} {e} {a} iomem step
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
...   | PEA.evL _ sBAB = nodeB-io-AB-evo nb iomem sBAB
...   | PEA.evR _ sBBD = nodeB-io-BD-evo nb iomem sBBD

------------------------------------------------------------------------
-- (5) NODE C — the leg-CD mirror of node B.
------------------------------------------------------------------------

-- C fires on link AC: bfC-AC evolves (client end), bfS-CD fixed (literal)
nodeC-io-AC-evo : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeCEvR-io nc e a ((Bd′ ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
nodeC-io-AC-evo nc {X} {e} {a} iomem sBAC
  with absBundleG-io-evo linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) iomem sBAC
... | bgEBio⁺ csc′ css′ bfc′ bfs′ ip′ eq run cli srv =
      ncEBio (SN.mkNodeC csc′ css′ bfc′ bfs′ (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) ip′ (SN.NodeStateC.inert-CD nc))
        (cong (λ z → (z ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc)) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeC-drv-io-no nc iomem))
           (⦀-wev-L _ _
              (noOffer→viewV _ (bundleG-io-no linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)
                 (absBundleG-io-ahl linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) iomem sBAC) linkAC≢linkCD iomem))
              run))
        cli (inj₁ refl) refl

-- C fires on link CD: bfS-CD evolves (server end), bfC-AC fixed (literal)
nodeC-io-CD-evo : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeCEvR-io nc e a ((absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ⦀ Bd′) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
nodeC-io-CD-evo nc {X} {e} {a} iomem sBCD
  with absBundleG-io-evo linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) iomem sBCD
... | bgEBio⁺ csc′ css′ bfc′ bfs′ ip′ eq run cli srv =
      ncEBio (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) csc′ css′ bfc′ bfs′ (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) ip′)
        (cong (λ z → (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ⦀ z) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc)) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeC-drv-io-no nc iomem))
           (⦀-wev-R _ _
              (noOffer→viewV _ (bundleG-io-no linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
                 (absBundleG-io-ahl linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) iomem sBCD) (λ q → linkAC≢linkCD (sym q)) iomem))
              run))
        (inj₁ refl) srv refl

-- node C dispatcher
nodeC-ev-io-evo : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodeC nc ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeCEvR-io nc e a M
nodeC-ev-io-evo nc {X} {e} {a} iomem step
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
...   | PEA.evL _ sBAC = nodeC-io-AC-evo nc iomem sBAC
...   | PEA.evR _ sBCD = nodeC-io-CD-evo nc iomem sBCD

------------------------------------------------------------------------
-- (6) NODE D — two tracked CLIENTS, no tracked server (mirror
-- `PipeNodeFix.nodeD-io-{BD,CD}-abs-cls`, client class strengthened).
------------------------------------------------------------------------

-- D fires on link BD: bfC-BD evolves (fired), bfC-CD fixed (literal)
nodeD-io-BD-evo : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeDEvR-io nd e a ((Bd′ ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)))
nodeD-io-BD-evo nd {X} {e} {a} iomem sBBD
  with absBundleG-io-evo linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) iomem sBBD
... | bgEBio⁺ csc′ css′ bfc′ bfs′ ip′ eq run cli srv =
      ndEBio (SN.mkNodeD csc′ css′ bfc′ bfs′ (SN.NodeStateD.cons-BD nd) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) ip′ (SN.NodeStateD.inert-CD nd))
        (cong (λ z → (z ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeD-drv-io-no nd iomem))
           (⦀-wev-L _ _
              (noOffer→viewV _ (bundleG-io-no linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)
                 (absBundleG-io-ahl linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) iomem sBBD) linkBD≢linkCD iomem))
              run))
        cli (inj₁ refl) refl refl

-- D fires on link CD: bfC-CD evolves (fired), bfC-BD fixed (literal)
nodeD-io-CD-evo : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeDEvR-io nd e a ((absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ⦀ Bd′) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)))
nodeD-io-CD-evo nd {X} {e} {a} iomem sBCD
  with absBundleG-io-evo linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) iomem sBCD
... | bgEBio⁺ csc′ css′ bfc′ bfs′ ip′ eq run cli srv =
      ndEBio (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd) csc′ css′ bfc′ bfs′ (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) ip′)
        (cong (λ z → (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ⦀ z) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))) eq)
        (∥⇘⇙-wev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (noOffer→viewV _ (nodeD-drv-io-no nd iomem))
           (⦀-wev-R _ _
              (noOffer→viewV _ (bundleG-io-no linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
                 (absBundleG-io-ahl linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) iomem sBCD) (λ q → linkBD≢linkCD (sym q)) iomem))
              run))
        (inj₁ refl) cli refl refl

-- node D dispatcher
nodeD-ev-io-evo : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodeD nd ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeDEvR-io nd e a M
nodeD-ev-io-evo nd {X} {e} {a} iomem step
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
...   | PEA.evL _ sBBD = nodeD-io-BD-evo nd iomem sBBD
...   | PEA.evR _ sBCD = nodeD-io-CD-evo nd iomem sBCD

------------------------------------------------------------------------
-- (7) THE WHOLE-NODES CLASSIFIERS and the top dispatcher (mirror
-- `PipeNodeFix.top-nodes-io-abs-client-cls`, both slot families carried).
------------------------------------------------------------------------

-- the four `PipeInv`-tracked BF clients' io evolutions
AllCliIoCls : (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) → Set
AllCliIoCls s s′ e a =
    CliIoCls linkAB hi (upClient legBD s) (upClient legBD s′) e a
  × CliIoCls linkAC hi (upClient legCD s) (upClient legCD s′) e a
  × CliIoCls linkBD hi (dnClient legBD s) (dnClient legBD s′) e a
  × CliIoCls linkCD hi (dnClient legCD s) (dnClient legCD s′) e a

-- the four `PipeSrvInv`-tracked BF servers' io evolutions
AllSrvIoCls : SysState → SysState → Set
AllSrvIoCls s s′ =
    SrvIoCls (upSrv legBD s) (upSrv legBD s′)
  × SrvIoCls (upSrv legCD s) (upSrv legCD s′)
  × SrvIoCls (dnSrv legBD s) (dnSrv legBD s′)
  × SrvIoCls (dnSrv legCD s) (dnSrv legCD s′)

-- TOP: an io fire of the whole abstract node group, with the medium untouched,
-- the concrete weak run, BOTH tracked slot families classified, and the six
-- driver phases fixed
top-nodes-io-evo : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ s′ ∈ SysState ] (med s ≡ med s′) × (M ≡ absNodesOf s′)
      × (nodesOf s ═[ ev (evl (evLabel X e a)) ]═► nodesOf s′)
      × AllCliIoCls s s′ e a
      × AllSrvIoCls s s′
      × (SN.NodeStateA.prod-AB (nA s) ≡ SN.NodeStateA.prod-AB (nA s′))
      × (SN.NodeStateA.prod-AC (nA s) ≡ SN.NodeStateA.prod-AC (nA s′))
      × (SN.NodeStateB.cp-B (nB s) ≡ SN.NodeStateB.cp-B (nB s′))
      × (SN.NodeStateC.cp-C (nC s) ≡ SN.NodeStateC.cp-C (nC s′))
      × (SN.NodeStateD.cons-BD (nD s) ≡ SN.NodeStateD.cons-BD (nD s′))
      × (SN.NodeStateD.cons-CD (nD s) ≡ SN.NodeStateD.cons-CD (nD s′))
top-nodes-io-evo s iomem nodesStep
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (absNodeA (nA s)) (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s))) nodesStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sA sRest = ⊥-elim (absGroupA-io-no (nA s) (nB s) (nC s) (nD s) iomem sA (_ , sRest))
... | PEA.evL _ sA with nodeA-ev-io-evo (nA s) iomem sA
...   | naEBio na′ Meq weakRunA srvAB srvAC epAB epAC =
        mkSys (med s) na′ (nB s) (nC s) (nD s) , refl ,
        cong (λ z → z ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) Meq ,
        ⦀-wev-L (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (⦀-noOffer (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (nodeB-io-no-when-A (nB s) iomem fpA)
             (⦀-noOffer (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (nodeC-io-no-when-A (nC s) iomem fpA) (nodeD-io-no-when-A (nD s) iomem fpA))))
          weakRunA
        , (inj₁ refl , inj₁ refl , inj₁ refl , inj₁ refl)
        , (srvAB , srvAC , inj₁ refl , inj₁ refl)
        , epAB , epAC , refl , refl , refl , refl
  where fpA = absNodeA-io-fp (nA s) iomem sA
top-nodes-io-evo s iomem nodesStep | PEA.evR _ sRest
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s)) sRest
... | PEA.evSync () _ _
... | PEA.evBoth _ sB sCD = ⊥-elim (absGroupB-io-no (nB s) (nC s) (nD s) iomem sB (_ , sCD))
... | PEA.evL _ sB with nodeB-ev-io-evo (nB s) iomem sB
...   | nbEBio nb′ Meq weakRunB cliAB srvBD ecpB =
        mkSys (med s) (nA s) nb′ (nC s) (nD s) , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (z ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) Meq ,
        ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (nodeA-io-no-when-B (nA s) iomem fpB))
          (⦀-wev-L (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (noOffer→viewV _ (⦀-noOffer (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (nodeC-io-no-when-B (nC s) iomem fpB) (nodeD-io-no-when-B (nD s) iomem fpB)))
             weakRunB)
        , (cliAB , inj₁ refl , inj₁ refl , inj₁ refl)
        , (inj₁ refl , inj₁ refl , srvBD , inj₁ refl)
        , refl , refl , ecpB , refl , refl , refl
  where fpB = absNodeB-io-fp (nB s) iomem sB
top-nodes-io-evo s iomem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absNodeC (nC s)) (absNodeD (nD s)) sCD
... | PEA.evSync () _ _
... | PEA.evBoth _ sC sD = ⊥-elim (absNodeD-io-no-when-C (nD s) iomem (absNodeC-io-fp (nC s) iomem sC) (_ , sD))
... | PEA.evL _ sC with nodeC-ev-io-evo (nC s) iomem sC
...   | ncEBio nc′ Meq weakRunC cliAC srvCD ecpC =
        mkSys (med s) (nA s) (nB s) nc′ (nD s) , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (z ⦀ absNodeD (nD s)))) Meq ,
        ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (nodeA-io-no-when-C (nA s) iomem fpC))
          (⦀-wev-R (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (noOffer→viewV _ (nodeB-io-no-when-C (nB s) iomem fpC))
             (⦀-wev-L (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (noOffer→viewV _ (nodeD-io-no-when-C (nD s) iomem fpC))
                weakRunC))
        , (inj₁ refl , cliAC , inj₁ refl , inj₁ refl)
        , (inj₁ refl , inj₁ refl , inj₁ refl , srvCD)
        , refl , refl , refl , ecpC , refl , refl
  where fpC = absNodeC-io-fp (nC s) iomem sC
top-nodes-io-evo s iomem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD | PEA.evR _ sD
    with nodeD-ev-io-evo (nD s) iomem sD
... | ndEBio nd′ Meq weakRunD cliBD cliCD econsBD econsCD =
        mkSys (med s) (nA s) (nB s) (nC s) nd′ , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ z))) Meq ,
        ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (nodeA-io-no-when-D (nA s) iomem fpD))
          (⦀-wev-R (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (noOffer→viewV _ (nodeB-io-no-when-D (nB s) iomem fpD))
             (⦀-wev-R (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (noOffer→viewV _ (nodeC-io-no-when-D (nC s) iomem fpD))
                weakRunD))
        , (inj₁ refl , inj₁ refl , cliBD , cliCD)
        , (inj₁ refl , inj₁ refl , inj₁ refl , inj₁ refl)
        , refl , refl , refl , refl , econsBD , econsCD
  where fpD = absNodeD-io-fp (nD s) iomem sD
