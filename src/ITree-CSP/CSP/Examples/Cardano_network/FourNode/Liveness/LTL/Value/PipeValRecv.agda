{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the RECEIVE-value cone (`Praos.PipeValRecv`),
-- SESSION-51, the delivering mirror of `PipeValProd.prodFire-blkA-{AB,AC}`:
--
--     recvFire-blkA-BD : (r : RState) {a : Block₃} {M : NetProc}
--       → radec r ─[ ev (evl (evLabel Block₃ (apiBF linkBD hi recvBFBlock) a)) ]─► M
--       → CliValOK (dnClient legBD (toSys r)) → a ≡ blkA
--
-- This is what upgrades the payload-AGNOSTIC delivery to the payload-carrying one:
-- the value on the delivering api IS the block node D's BF client is holding, and
-- `PipeVal` clause (7) says that block is `blkA`.
--
-- OWNER ENUMERATION (the session-49 rule, one link over).  A dispatch on link BD
-- must refute every node that OWNS BD but does not receive on it.  Owners are B
-- and D, so nodes A and C fall to link disequality (`nodeA-link` / `nodeC-link`),
-- but **node B needs its own refutation** — and, unlike the `sendBFBlock`
-- dispatch, it cannot be a LINK argument.  It is a **DIR** argument:
-- node B's BD bundle is `absBundleG linkBD lo hi …`, so its BF CLIENT sits on
-- `lo` while the delivering event is at `hi`, and `absBundleG-api-no` refutes on
-- link mismatch ONLY.  Hence the new `recvBFBlock-cli-dir` /
-- `bundle-recv-dir` pair below; the node-B/C refutations then need only the
-- BUNDLE half of `reflect-node-api` (the relay DRIVER is never inspected).
--
-- Everything else was already built: `PipeValFill.bundle-recv-cliPos` (bundle
-- level, on the already-parametric `PipeBundleRecv.bundleBF-ev-forces`) and
-- `PipeEvCone.nodeD-{BD,CD}-recv-forces`, whose two productive branches are
-- re-mirrored here with `bundle-recv-cliPos` in place of
-- `bundle-recvBFBlock-forces-src`.  `PipeEvCone` stays READ-ONLY.
--
-- No postulate/hole/meta; no `dne`.  Base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Relation.Nullary using ( ¬_; Dec; yes; no )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; _≢_; refl; sym; trans; cong; subst )

open import Class.DecEq using ( DecEq; _≟_ )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValRecv (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using
  ( p; apiES; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( Block )
open import CSP.Examples.Cardano_network.Net p using
  ( Net_Api; Net_Api-≟; Link; apiBF; recvBFBlock )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using ( Dir; lo; hi )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; EventSet )
open EventSet using ( mem )
open Op using () renaming ( ∅ES to ∅ESa )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )

import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload}) as PEA
import CSP.Examples.Cardano_network.BlockFetch p as BF
open import CSP.Examples.Cardano_network.NetworkPar p using ( ιBF )

import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using ( BFcPos; bcHead; bcReq1; bcDone1; bcBlk1; bcSil
              ; BFsPos; CScPos; CSsPos; InertPos )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep
open SStep using ( NetProc; absBFc; coarsenBFc; absBundleG
                 ; absNodeA; absNodeB; absNodeC; absNodeD; absNodesOf
                 ; medEv; nodesEv; reflect-top-ev )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; med; nA; nB; nC; nD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( decMed )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( RState; radec; toSys )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA using
  ( ApiHasLink; apiLink-inj; ahlBF; aicBF )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( tableSpec-ev-inv; nothing-absurd )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysRoute blkA using
  ( medium-api-non-offer
  ; absNodeA-fp; absNodeB-fp; absNodeC-fp
  ; absNodeB-no-when-A; absNodeC-no-when-A; absNodeD-no-when-A
  ; absNodeC-no-when-B; absNodeD-no-when-B; absNodeD-no-when-C )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink blkA using
  ( linkAB≢linkBD; linkAC≢linkCD; linkBD≢linkCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink2 blkA using
  ( lo≢hi )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink5 blkA using
  ( Tbfc )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink6 blkA using
  ( absBundleG-api-no )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleRecv blkA using
  ( bundleBF-ev-forces; recvBFBlock-server-absurd )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeRecvSource blkA using
  ( recvBFBlock-forces-src )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA using
  ( dnClient )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA using
  ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValInv blkA using
  ( CliValOK )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValFill blkA using
  ( bundle-recv-cliPos )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeProdFire blkA using
  ( nodeB-link; nodeC-link; linkAC≢linkBD; linkAB≢linkCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValProd blkA using
  ( nodeA-link )

------------------------------------------------------------------------
-- (1) THE CLIENT'S DIR PIN.  `recvBFBlock-forces-src` returns the POSITION and
-- `recvBFBlock-src-val` the VALUE; neither returns the DIRECTION, which is what a
-- BD/CD dispatch needs in order to refute the relay (whose BD/CD client sits on
-- `lo`).  One clause, exactly `recvBFBlock-src-val`'s shape: the ten non-`bcBlk1`
-- positions are already refuted by the frozen `recvBFBlock-forces-src`.
------------------------------------------------------------------------

-- a BF CLIENT decoded at dir `d` can only fire `recvBFBlock` AT dir `d`
recvBFBlock-cli-dir :
    (l : Link) (d : Dir) (bfc : BFcPos)
    {l′ : Link} {d′ : Dir} {a : Block} {M : NetProc}
  → absBFc l d bfc
      ─[ ev (evl (evLabel Block (ιBF (BF.apiBFev l′ d′ recvBFBlock)) a)) ]─► M
  → d′ ≡ d
recvBFBlock-cli-dir l d (bcBlk1 b) {l′} {d′} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , _ with l′ ≟ l | d′ ≟ d
...   | no  _    | _       = ⊥-elim (nothing-absurd ceq)
...   | yes refl | no  _   = ⊥-elim (nothing-absurd ceq)
...   | yes refl | yes deq = deq
recvBFBlock-cli-dir l d (bcHead st) step = ⊥-elim (recvBFBlock-forces-src l d (bcHead st) step)
recvBFBlock-cli-dir l d (bcReq1 r)  step = ⊥-elim (recvBFBlock-forces-src l d (bcReq1 r) step)
recvBFBlock-cli-dir l d bcDone1     step = ⊥-elim (recvBFBlock-forces-src l d bcDone1 step)
recvBFBlock-cli-dir l d (bcSil st)  step = ⊥-elim (recvBFBlock-forces-src l d (bcSil st) step)

-- the same at the BUNDLE level: only the client can fire `recvBFBlock`
-- (`recvBFBlock-server-absurd`), so the fired dir IS the bundle's client dir
bundle-recv-dir :
    (l : Link) (cl sv : Dir) → cl ≢ sv
  → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {l′ : Link} {d′ : Dir} {a : Block} {Bd′ : NetProc}
  → absBundleG l cl sv csc css bfc bfs ip
      ─[ ev (evl (evLabel Block (ιBF (BF.apiBFev l′ d′ recvBFBlock)) a)) ]─► Bd′
  → d′ ≡ cl
bundle-recv-dir l cl sv cl≢sv csc css bfc bfs ip step =
  bundleBF-ev-forces l cl sv cl≢sv csc css bfc bfs ip
    (λ sC → recvBFBlock-cli-dir l cl bfc sC)
    (λ sM → ⊥-elim (recvBFBlock-server-absurd l sv bfs sM))
    step

------------------------------------------------------------------------
-- (2) NODE D's two productive peels — verbatim `PipeEvCone.nodeD-{BD,CD}-recv-forces`
-- with `bundle-recv-cliPos` in place of `bundle-recvBFBlock-forces-src`, so the
-- conclusion names the block AT THE FIRED VALUE instead of merely `BFcHasBlk`.
------------------------------------------------------------------------

-- node D, leg BD: the delivering `recvBFBlock linkBD` value IS `bfC-BD`'s block
nodeD-BD-recv-cliPos :
    (nd : SN.NodeStateD) {a : Block₃} {M : NetProc}
  → apiES .mem (Block₃ , apiBF linkBD hi recvBFBlock) a
  → absNodeD nd ─[ ev (evl (evLabel Block₃ (apiBF linkBD hi recvBFBlock) a)) ]─► M
  → SN.NodeStateD.bfC-BD nd ≡ bcBlk1 a
nodeD-BD-recv-cliPos nd apimem step
  with SStep.reflect-node-api
         (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
          ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
         (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
           (absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) bStep
...   | PEA.evSync () _ _
...   | PEA.evL _ sBBD =
        bundle-recv-cliPos linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) sBBD
...   | PEA.evR _ sBCD = ⊥-elim (absBundleG-api-no linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) ahlBF linkBD≢linkCD apimem (_ , sBCD))
...   | PEA.evBoth _ _ sBCD = ⊥-elim (absBundleG-api-no linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) ahlBF linkBD≢linkCD apimem (_ , sBCD))

-- node D, leg CD (mirror)
nodeD-CD-recv-cliPos :
    (nd : SN.NodeStateD) {a : Block₃} {M : NetProc}
  → apiES .mem (Block₃ , apiBF linkCD hi recvBFBlock) a
  → absNodeD nd ─[ ev (evl (evLabel Block₃ (apiBF linkCD hi recvBFBlock) a)) ]─► M
  → SN.NodeStateD.bfC-CD nd ≡ bcBlk1 a
nodeD-CD-recv-cliPos nd apimem step
  with SStep.reflect-node-api
         (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
          ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
         (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
           (absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) bStep
...   | PEA.evSync () _ _
...   | PEA.evR _ sBCD =
        bundle-recv-cliPos linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) sBCD
...   | PEA.evL _ sBBD = ⊥-elim (absBundleG-api-no linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ahlBF (λ q → linkBD≢linkCD (sym q)) apimem (_ , sBBD))
...   | PEA.evBoth _ sBBD _ = ⊥-elim (absBundleG-api-no linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ahlBF (λ q → linkBD≢linkCD (sym q)) apimem (_ , sBBD))

------------------------------------------------------------------------
-- (3) THE RELAY REFUTATIONS — the owner-enumeration twist.  Node B owns BD but
-- its BD BF client sits on `lo`; the delivering event is at `hi`.  Only the
-- BUNDLE half of the api sync is inspected, so the relay DRIVER never appears.
------------------------------------------------------------------------

-- node B cannot fire `recvBFBlock` on link BD at dir `hi`
nodeB-BD-recv-⊥ :
    (nb : SN.NodeStateB) {a : Block₃} {M : NetProc}
  → apiES .mem (Block₃ , apiBF linkBD hi recvBFBlock) a
  → absNodeB nb ─[ ev (evl (evLabel Block₃ (apiBF linkBD hi recvBFBlock) a)) ]─► M
  → ⊥
nodeB-BD-recv-⊥ nb apimem step
  with SStep.reflect-node-api
         (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
          ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
         (SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb))
           (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)) bStep
...   | PEA.evSync () _ _
...   | PEA.evL _ sBAB = absBundleG-api-no linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ahlBF (λ q → linkAB≢linkBD (sym q)) apimem (_ , sBAB)
...   | PEA.evBoth _ sBAB _ = absBundleG-api-no linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ahlBF (λ q → linkAB≢linkBD (sym q)) apimem (_ , sBAB)
...   | PEA.evR _ sBBD =
        lo≢hi (sym (bundle-recv-dir linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) sBBD))

-- node C cannot fire `recvBFBlock` on link CD at dir `hi` (mirror)
nodeC-CD-recv-⊥ :
    (nc : SN.NodeStateC) {a : Block₃} {M : NetProc}
  → apiES .mem (Block₃ , apiBF linkCD hi recvBFBlock) a
  → absNodeC nc ─[ ev (evl (evLabel Block₃ (apiBF linkCD hi recvBFBlock) a)) ]─► M
  → ⊥
nodeC-CD-recv-⊥ nc apimem step
  with SStep.reflect-node-api
         (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
          ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
         (SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc))
           (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)) bStep
...   | PEA.evSync () _ _
...   | PEA.evL _ sBAC = absBundleG-api-no linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ahlBF (λ q → linkAC≢linkCD (sym q)) apimem (_ , sBAC)
...   | PEA.evBoth _ sBAC _ = absBundleG-api-no linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ahlBF (λ q → linkAC≢linkCD (sym q)) apimem (_ , sBAC)
...   | PEA.evR _ sBCD =
        lo≢hi (sym (bundle-recv-dir linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) sBCD))

------------------------------------------------------------------------
-- (4) THE WHOLE-NODES DISPATCH (skeleton = `PipeValProd.nodes-sbb-relayVal-BD`).
------------------------------------------------------------------------

-- a `recvBFBlock linkBD@hi` out of the abstract nodes IS node D's BD client
-- firing, at the value it holds
nodes-recv-cliPos-BD :
    (s : SysState) {a : Block₃} {M : NetProc}
  → apiES .mem (Block₃ , apiBF linkBD hi recvBFBlock) a
  → absNodesOf s ─[ ev (evl (evLabel Block₃ (apiBF linkBD hi recvBFBlock) a)) ]─► M
  → SN.NodeStateD.bfC-BD (nD s) ≡ bcBlk1 a
nodes-recv-cliPos-BD s apimem nodesStep
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (absNodeA (nA s)) (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s))) nodesStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sA sRest = ⊥-elim (SStep.⦀-noOffer (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s))
        (absNodeB-no-when-A (nB s) apimem (absNodeA-fp (nA s) apimem sA))
        (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
          (absNodeC-no-when-A (nC s) apimem (absNodeA-fp (nA s) apimem sA))
          (absNodeD-no-when-A (nD s) apimem (absNodeA-fp (nA s) apimem sA))) (_ , sRest))
... | PEA.evL _ sA with nodeA-link (nA s) apimem sA
...   | inj₁ ahlAB = ⊥-elim (linkAB≢linkBD (apiLink-inj ahlAB ahlBF))
...   | inj₂ ahlAC = ⊥-elim (linkAC≢linkBD (apiLink-inj ahlAC ahlBF))
nodes-recv-cliPos-BD s apimem nodesStep | PEA.evR _ sRest
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s)) sRest
... | PEA.evSync () _ _
... | PEA.evBoth _ sB sCD = ⊥-elim (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
        (absNodeC-no-when-B (nC s) apimem (absNodeB-fp (nB s) apimem sB))
        (absNodeD-no-when-B (nD s) apimem (absNodeB-fp (nB s) apimem sB)) (_ , sCD))
... | PEA.evL _ sB = ⊥-elim (nodeB-BD-recv-⊥ (nB s) apimem sB)
nodes-recv-cliPos-BD s apimem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absNodeC (nC s)) (absNodeD (nD s)) sCD
... | PEA.evSync () _ _
... | PEA.evBoth _ sC sD = ⊥-elim (absNodeD-no-when-C (nD s) apimem (absNodeC-fp (nC s) apimem sC) (_ , sD))
... | PEA.evL _ sC with nodeC-link (nC s) apimem sC
...   | inj₁ ahlAC = ⊥-elim (linkAC≢linkBD (apiLink-inj ahlAC ahlBF))
...   | inj₂ ahlCD = ⊥-elim (linkBD≢linkCD (sym (apiLink-inj ahlCD ahlBF)))
nodes-recv-cliPos-BD s apimem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD | PEA.evR _ sD =
  nodeD-BD-recv-cliPos (nD s) apimem sD

-- the CD mirror
nodes-recv-cliPos-CD :
    (s : SysState) {a : Block₃} {M : NetProc}
  → apiES .mem (Block₃ , apiBF linkCD hi recvBFBlock) a
  → absNodesOf s ─[ ev (evl (evLabel Block₃ (apiBF linkCD hi recvBFBlock) a)) ]─► M
  → SN.NodeStateD.bfC-CD (nD s) ≡ bcBlk1 a
nodes-recv-cliPos-CD s apimem nodesStep
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (absNodeA (nA s)) (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s))) nodesStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sA sRest = ⊥-elim (SStep.⦀-noOffer (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s))
        (absNodeB-no-when-A (nB s) apimem (absNodeA-fp (nA s) apimem sA))
        (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
          (absNodeC-no-when-A (nC s) apimem (absNodeA-fp (nA s) apimem sA))
          (absNodeD-no-when-A (nD s) apimem (absNodeA-fp (nA s) apimem sA))) (_ , sRest))
... | PEA.evL _ sA with nodeA-link (nA s) apimem sA
...   | inj₁ ahlAB = ⊥-elim (linkAB≢linkCD (apiLink-inj ahlAB ahlBF))
...   | inj₂ ahlAC = ⊥-elim (linkAC≢linkCD (apiLink-inj ahlAC ahlBF))
nodes-recv-cliPos-CD s apimem nodesStep | PEA.evR _ sRest
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s)) sRest
... | PEA.evSync () _ _
... | PEA.evBoth _ sB sCD = ⊥-elim (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
        (absNodeC-no-when-B (nC s) apimem (absNodeB-fp (nB s) apimem sB))
        (absNodeD-no-when-B (nD s) apimem (absNodeB-fp (nB s) apimem sB)) (_ , sCD))
... | PEA.evL _ sB with nodeB-link (nB s) apimem sB
...   | inj₁ ahlAB = ⊥-elim (linkAB≢linkCD (apiLink-inj ahlAB ahlBF))
...   | inj₂ ahlBD = ⊥-elim (linkBD≢linkCD (apiLink-inj ahlBD ahlBF))
nodes-recv-cliPos-CD s apimem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absNodeC (nC s)) (absNodeD (nD s)) sCD
... | PEA.evSync () _ _
... | PEA.evBoth _ sC sD = ⊥-elim (absNodeD-no-when-C (nD s) apimem (absNodeC-fp (nC s) apimem sC) (_ , sD))
... | PEA.evL _ sC = ⊥-elim (nodeC-CD-recv-⊥ (nC s) apimem sC)
nodes-recv-cliPos-CD s apimem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD | PEA.evR _ sD =
  nodeD-CD-recv-cliPos (nD s) apimem sD

------------------------------------------------------------------------
-- (5) THE HEADLINE, at the whole system (mirror `PipeValProd.prodFire-*`): the
-- medium never offers an api, so a visible api is a NODES solo.
------------------------------------------------------------------------

-- the delivering value on link BD is `blkA`, given the leg's client clause
recvFire-blkA-BD : (r : RState) {a : Block₃} {M : NetProc}
  → radec r ─[ ev (evl (evLabel Block₃ (apiBF linkBD hi recvBFBlock) a)) ]─► M
  → CliValOK (dnClient legBD (toSys r)) → a ≡ blkA
recvFire-blkA-BD r step h
  with reflect-top-ev (decMed (med (toSys r))) (absNodesOf (toSys r))
         (inj₁ (medium-api-non-offer (med (toSys r)) aicBF)) step
... | medEv M₁ ms _      = ⊥-elim (medium-api-non-offer (med (toSys r)) aicBF (M₁ , ms))
... | nodesEv N₁ ns refl = subst CliValOK (nodes-recv-cliPos-BD (toSys r) tt ns) h

-- the CD mirror
recvFire-blkA-CD : (r : RState) {a : Block₃} {M : NetProc}
  → radec r ─[ ev (evl (evLabel Block₃ (apiBF linkCD hi recvBFBlock) a)) ]─► M
  → CliValOK (dnClient legCD (toSys r)) → a ≡ blkA
recvFire-blkA-CD r step h
  with reflect-top-ev (decMed (med (toSys r))) (absNodesOf (toSys r))
         (inj₁ (medium-api-non-offer (med (toSys r)) aicBF)) step
... | medEv M₁ ms _      = ⊥-elim (medium-api-non-offer (med (toSys r)) aicBF (M₁ , ms))
... | nodesEv N₁ ns refl = subst CliValOK (nodes-recv-cliPos-CD (toSys r) tt ns) h
