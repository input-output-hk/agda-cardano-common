{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the WHOLE-NODES fill VALUE cone (`Praos.PipeValFire`),
-- SESSION-39 step (ii)1: the node ROUTING mirror.
--
-- `PipeValFill.bundle-blkfill-val` says a block-carrying cell fill out of a
-- BUNDLE whose server sits at `bsBlk1 b` carries exactly `MsgBlock b`.  This
-- module routes a WHOLE-NODES fill down to the right bundle and re-emits that
-- fact, exactly as `PipeSrvFire.nodes-blockfill-hi` routes down and re-emits
-- `BFsHasBlk`.
--
-- STRUCTURALLY IDENTICAL to `PipeSrvFire`'s cone — same `Par-ev-elim` splits,
-- same refutations, same frozen helpers — with two substitutions:
--   · each `proj₂ (bundle-blkfill-srv … blk)` becomes `bundle-blkfill-val … blk`;
--   · each disjunct carries `(srv ≡ bsBlk1 b → pl ≡ blkPayload b)` instead of
--     `BFsHasBlk srv`, so the server position is a HYPOTHESIS (supplied by the
--     consumer from `PipeValFill.hasBlk⇒isBlk1` applied to
--     `PipeSrvFire.srvHit-{up,dn}`), and one `subst` rewrites the server slot
--     inside `absBundleG` before `bundle-blkfill-val` is applied.
-- The `lo`-side refutations still go through `bundle-blkfill-srv` (they only
-- need the DIRECTION component, which is unchanged), so nothing is duplicated
-- that did not have to be.
--
-- `PipeSrvFire` stays READ-ONLY: every helper this mirror needs is already
-- exported from it or from the frozen `SysIoLink*`/`SysOracle*` layer.
--
-- No postulate/hole/meta.  Base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Relation.Nullary using ( ¬_ )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValFire (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; apiES; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( Block )
open import CSP.Examples.Cardano_network.Base
  using ( Dir; lo; hi; N2N_BlockFetch )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; Net_Api-≟; Link; input )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; EventSet )
  renaming ( ∅ES to ∅ESa )
open EventSet using ( mem )

import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload}) as PEA

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )

import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep
open SStep using ( NetProc; absBundleG; absNodeA; absNodeB; absNodeC; absNodeD; absNodesOf )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using ( BFcPos; BFsPos; bsBlk1; CScPos; CSsPos; InertPos
              ; decProd; decConsD; decCP )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA
  using ( io⇒¬api; apiLink-inj; ahlIn )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink blkA
  using ( nodeA-drv-io-no; nodeB-drv-io-no; nodeC-drv-io-no; nodeD-drv-io-no
        ; linkAB≢linkAC; linkAB≢linkBD; linkAC≢linkCD; linkBD≢linkCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink2 blkA
  using ( lo≢hi )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink3 blkA
  using ( absBundleG-io-ahl; absGroupA-io-no; absGroupB-io-no
        ; absNodeC-io-fp; absNodeD-io-no-when-C )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; nA; nB; nC; nD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeFillSource blkA
  using ( PlIsBlk; upLink; dnLink )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA
  using ( upSrv; dnSrv )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvFire blkA
  using ( bundle-blkfill-srv )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValFill blkA
  using ( blkPayload; bundle-blkfill-val )

------------------------------------------------------------------------
-- The per-bundle value fact, with the server position as a HYPOTHESIS (the
-- `subst` that rewrites the slot inside `absBundleG` lives here, once).
------------------------------------------------------------------------

-- a bundle fill, given that the bundle's server slot IS `bsBlk1 b`
bundleVal : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     (b : Block) {l′ : Link} {d′ : Dir} {pl : Payload} {Bd′ : NetProc}
  → absBundleG l cl sv csc css bfc bfs ip
      ─[ ev (evl (evLabel Payload (input l′ d′ N2N_BlockFetch) pl)) ]─► Bd′
  → PlIsBlk pl → bfs ≡ bsBlk1 b → pl ≡ blkPayload b
bundleVal l cl sv csc css bfc bfs ip b {l′} {d′} {pl} {Bd′} step blk eq =
  bundle-blkfill-val l cl sv csc css bfc b ip
    (subst (λ z → absBundleG l cl sv csc css bfc z ip
                    ─[ ev (evl (evLabel Payload (input l′ d′ N2N_BlockFetch) pl)) ]─► Bd′)
           eq step)
    blk

------------------------------------------------------------------------
-- `SrvHitVal` — the value twin of `PipeSrvFire.SrvHit`, same four-way nesting
-- so the selectors below mirror `srvHit-{up,dn}` clause for clause.
------------------------------------------------------------------------

-- which server fired, plus its payload-value pin (position as hypothesis)
SrvHitVal : SysState → Block → Payload → Link → Set
SrvHitVal s b pl l′ =
    ((l′ ≡ linkAB) × (SN.NodeStateA.bfS-AB (nA s) ≡ bsBlk1 b → pl ≡ blkPayload b))
  ⊎ ((l′ ≡ linkAC) × (SN.NodeStateA.bfS-AC (nA s) ≡ bsBlk1 b → pl ≡ blkPayload b))
  ⊎ ((l′ ≡ linkBD) × (SN.NodeStateB.bfS-BD (nB s) ≡ bsBlk1 b → pl ≡ blkPayload b))
  ⊎ ((l′ ≡ linkCD) × (SN.NodeStateC.bfS-CD (nC s) ≡ bsBlk1 b → pl ≡ blkPayload b))

------------------------------------------------------------------------
-- The four per-node cones (mirror of `PipeSrvFire.node{A,B,C,D}-blockfill-hi`).
------------------------------------------------------------------------

-- node A hosts BOTH `sv ≡ hi` upstream servers
nodeA-blockfill-val : (na : SN.NodeStateA) (b : Block)
    {l′ : Link} {pl : Payload} {M : NetProc}
  → absNodeA na ─[ ev (evl (evLabel Payload (input l′ hi N2N_BlockFetch) pl)) ]─► M
  → PlIsBlk pl
  → ((l′ ≡ linkAB) × (SN.NodeStateA.bfS-AB na ≡ bsBlk1 b → pl ≡ blkPayload b))
  ⊎ ((l′ ≡ linkAC) × (SN.NodeStateA.bfS-AC na ≡ bsBlk1 b → pl ≡ blkPayload b))
nodeA-blockfill-val na b {l′} {pl} step blk
  with PEA.Par-ev-elim apiES (λ _ _ → tt)
         (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
          ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
         (decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ decProd linkAC hi blkA (SN.NodeStateA.prod-AC na))
         step
... | PEA.evSync amem _ _ = ⊥-elim (io⇒¬api {Payload} {input l′ hi N2N_BlockFetch} {pl} tt amem)
... | PEA.evR _ sD      = ⊥-elim (nodeA-drv-io-no na tt (_ , sD))
... | PEA.evBoth _ _ sD = ⊥-elim (nodeA-drv-io-no na tt (_ , sD))
... | PEA.evL _ sB
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
           (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
           sB
...   | PEA.evSync () _ _
...   | PEA.evBoth _ sBAB sBAC = ⊥-elim (linkAB≢linkAC
          (apiLink-inj (absBundleG-io-ahl linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) tt sBAB)
                       (absBundleG-io-ahl linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) tt sBAC)))
...   | PEA.evL _ sBAB = inj₁
          ( apiLink-inj ahlIn (absBundleG-io-ahl linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) tt sBAB)
          , bundleVal linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) b sBAB blk )
...   | PEA.evR _ sBAC = inj₂
          ( apiLink-inj ahlIn (absBundleG-io-ahl linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) tt sBAC)
          , bundleVal linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) b sBAC blk )

-- node B hosts ONE `sv ≡ hi` server (`bfS-BD`); its AB bundle serves at `lo`
nodeB-blockfill-val : (nb : SN.NodeStateB) (b : Block)
    {l′ : Link} {pl : Payload} {M : NetProc}
  → absNodeB nb ─[ ev (evl (evLabel Payload (input l′ hi N2N_BlockFetch) pl)) ]─► M
  → PlIsBlk pl
  → (l′ ≡ linkBD) × (SN.NodeStateB.bfS-BD nb ≡ bsBlk1 b → pl ≡ blkPayload b)
nodeB-blockfill-val nb b {l′} {pl} step blk
  with PEA.Par-ev-elim apiES (λ _ _ → tt)
         (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
          ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
         (decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
         step
... | PEA.evSync amem _ _ = ⊥-elim (io⇒¬api {Payload} {input l′ hi N2N_BlockFetch} {pl} tt amem)
... | PEA.evR _ sD      = ⊥-elim (nodeB-drv-io-no nb tt (_ , sD))
... | PEA.evBoth _ _ sD = ⊥-elim (nodeB-drv-io-no nb tt (_ , sD))
... | PEA.evL _ sB
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb))
           (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
           sB
...   | PEA.evSync () _ _
...   | PEA.evBoth _ sBAB sBBD = ⊥-elim (linkAB≢linkBD
          (apiLink-inj (absBundleG-io-ahl linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) tt sBAB)
                       (absBundleG-io-ahl linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) tt sBBD)))
...   | PEA.evL _ sBAB = ⊥-elim (lo≢hi (sym (proj₁
          (bundle-blkfill-srv linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) sBAB blk))))
...   | PEA.evR _ sBBD =
          ( apiLink-inj ahlIn (absBundleG-io-ahl linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) tt sBBD)
          , bundleVal linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) b sBBD blk )

-- node C mirrors node B (`bfS-CD` at `hi`, `bfS-AC` at `lo`)
nodeC-blockfill-val : (nc : SN.NodeStateC) (b : Block)
    {l′ : Link} {pl : Payload} {M : NetProc}
  → absNodeC nc ─[ ev (evl (evLabel Payload (input l′ hi N2N_BlockFetch) pl)) ]─► M
  → PlIsBlk pl
  → (l′ ≡ linkCD) × (SN.NodeStateC.bfS-CD nc ≡ bsBlk1 b → pl ≡ blkPayload b)
nodeC-blockfill-val nc b {l′} {pl} step blk
  with PEA.Par-ev-elim apiES (λ _ _ → tt)
         (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
          ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
         (decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
         step
... | PEA.evSync amem _ _ = ⊥-elim (io⇒¬api {Payload} {input l′ hi N2N_BlockFetch} {pl} tt amem)
... | PEA.evR _ sD      = ⊥-elim (nodeC-drv-io-no nc tt (_ , sD))
... | PEA.evBoth _ _ sD = ⊥-elim (nodeC-drv-io-no nc tt (_ , sD))
... | PEA.evL _ sB
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc))
           (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
           sB
...   | PEA.evSync () _ _
...   | PEA.evBoth _ sBAC sBCD = ⊥-elim (linkAC≢linkCD
          (apiLink-inj (absBundleG-io-ahl linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) tt sBAC)
                       (absBundleG-io-ahl linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) tt sBCD)))
...   | PEA.evL _ sBAC = ⊥-elim (lo≢hi (sym (proj₁
          (bundle-blkfill-srv linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) sBAC blk))))
...   | PEA.evR _ sBCD =
          ( apiLink-inj ahlIn (absBundleG-io-ahl linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) tt sBCD)
          , bundleVal linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) b sBCD blk )

-- node D hosts NO `sv ≡ hi` BF server: it can never block-fill on `hi`
-- (verbatim `PipeSrvFire.nodeD-blockfill-hi`, re-derived here only because that
-- one is `PlIsBlk`-only and this cone needs it in the same clause shape)
nodeD-blockfill-val : (nd : SN.NodeStateD)
    {l′ : Link} {pl : Payload} {M : NetProc}
  → absNodeD nd ─[ ev (evl (evLabel Payload (input l′ hi N2N_BlockFetch) pl)) ]─► M
  → PlIsBlk pl → ⊥
nodeD-blockfill-val nd {l′} {pl} step blk
  with PEA.Par-ev-elim apiES (λ _ _ → tt)
         (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
          ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
         (decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ decConsD linkCD (SN.NodeStateD.cons-CD nd))
         step
... | PEA.evSync amem _ _ = io⇒¬api {Payload} {input l′ hi N2N_BlockFetch} {pl} tt amem
... | PEA.evR _ sD      = nodeD-drv-io-no nd tt (_ , sD)
... | PEA.evBoth _ _ sD = nodeD-drv-io-no nd tt (_ , sD)
... | PEA.evL _ sB
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
           (absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
           sB
...   | PEA.evSync () _ _
...   | PEA.evBoth _ sBBD sBCD = linkBD≢linkCD
          (apiLink-inj (absBundleG-io-ahl linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) tt sBBD)
                       (absBundleG-io-ahl linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) tt sBCD))
...   | PEA.evL _ sBBD = lo≢hi (sym (proj₁
          (bundle-blkfill-srv linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) sBBD blk)))
...   | PEA.evR _ sBCD = lo≢hi (sym (proj₁
          (bundle-blkfill-srv linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) sBCD blk)))

------------------------------------------------------------------------
-- THE WHOLE-NODES VALUE CONE (mirror of `PipeSrvFire.nodes-blockfill-hi`).
------------------------------------------------------------------------

-- a `hi`-directed BLOCK fill out of the whole nodes names the firing server's
-- link AND pins the payload to that server's own block
nodes-blockfill-val : (s : SysState) (b : Block)
    {l′ : Link} {pl : Payload} {M : NetProc}
  → absNodesOf s ─[ ev (evl (evLabel Payload (input l′ hi N2N_BlockFetch) pl)) ]─► M
  → PlIsBlk pl → SrvHitVal s b pl l′
nodes-blockfill-val s b {l′} {pl} step blk
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (absNodeA (nA s)) (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s))) step
... | PEA.evSync () _ _
... | PEA.evBoth _ sA sRest = ⊥-elim (absGroupA-io-no (nA s) (nB s) (nC s) (nD s) tt sA (_ , sRest))
... | PEA.evL _ sA with nodeA-blockfill-val (nA s) b sA blk
...   | inj₁ q = inj₁ q
...   | inj₂ q = inj₂ (inj₁ q)
nodes-blockfill-val s b {l′} {pl} step blk | PEA.evR _ sRest
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s)) sRest
... | PEA.evSync () _ _
... | PEA.evBoth _ sB sCD = ⊥-elim (absGroupB-io-no (nB s) (nC s) (nD s) tt sB (_ , sCD))
... | PEA.evL _ sB  = inj₂ (inj₂ (inj₁ (nodeB-blockfill-val (nB s) b sB blk)))
nodes-blockfill-val s b {l′} {pl} step blk | PEA.evR _ sRest | PEA.evR _ sCD
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absNodeC (nC s)) (absNodeD (nD s)) sCD
... | PEA.evSync () _ _
... | PEA.evBoth _ sC sD = ⊥-elim (absNodeD-io-no-when-C (nD s) {Payload} {input l′ hi N2N_BlockFetch} {pl} tt
                                    (absNodeC-io-fp (nC s) {Payload} {input l′ hi N2N_BlockFetch} {pl} tt sC) (_ , sD))
... | PEA.evL _ sC = inj₂ (inj₂ (inj₂ (nodeC-blockfill-val (nC s) b sC blk)))
... | PEA.evR _ sD = ⊥-elim (nodeD-blockfill-val (nD s) sD blk)

------------------------------------------------------------------------
-- THE TWO LEG SELECTORS (mirror of `PipeSrvFire.srvHit-{up,dn}`).
------------------------------------------------------------------------

-- the leg's UPSTREAM server's payload pin
srvHitVal-up : (l : TwoLegs) (s : SysState) (b : Block) (pl : Payload)
             → SrvHitVal s b pl (upLink l)
             → upSrv l s ≡ bsBlk1 b → pl ≡ blkPayload b
srvHitVal-up legBD s b pl (inj₁ (_ , q))               = q
srvHitVal-up legBD s b pl (inj₂ (inj₁ ()))
srvHitVal-up legBD s b pl (inj₂ (inj₂ (inj₁ ())))
srvHitVal-up legBD s b pl (inj₂ (inj₂ (inj₂ ())))
srvHitVal-up legCD s b pl (inj₁ ())
srvHitVal-up legCD s b pl (inj₂ (inj₁ (_ , q)))        = q
srvHitVal-up legCD s b pl (inj₂ (inj₂ (inj₁ ())))
srvHitVal-up legCD s b pl (inj₂ (inj₂ (inj₂ ())))

-- the leg's DOWNSTREAM server's payload pin
srvHitVal-dn : (l : TwoLegs) (s : SysState) (b : Block) (pl : Payload)
             → SrvHitVal s b pl (dnLink l)
             → dnSrv l s ≡ bsBlk1 b → pl ≡ blkPayload b
srvHitVal-dn legBD s b pl (inj₁ ())
srvHitVal-dn legBD s b pl (inj₂ (inj₁ ()))
srvHitVal-dn legBD s b pl (inj₂ (inj₂ (inj₁ (_ , q)))) = q
srvHitVal-dn legBD s b pl (inj₂ (inj₂ (inj₂ ())))
srvHitVal-dn legCD s b pl (inj₁ ())
srvHitVal-dn legCD s b pl (inj₂ (inj₁ ()))
srvHitVal-dn legCD s b pl (inj₂ (inj₂ (inj₁ ())))
srvHitVal-dn legCD s b pl (inj₂ (inj₂ (inj₂ (_ , q)))) = q
