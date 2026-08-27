{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — (P5) `noRetA`'s REFUTATION HALF, at the INERT-FREEZE
-- HYPOTHESIS (`Praos.LiveRetFree`).
--
-- WHAT THIS MODULE IS.  `LiveFSim`'s `√` arm needs "no reachable abstract config
-- whose joint invariant holds forces to `ret`" (premise (P5) `noRetA`).  The
-- adversarial verification of that premise (`p5-verify-report.md`) established
-- TWO things:
--   (i)  it is NOT derivable from the carried `LegJointB` — an explicit escape
--        config satisfies every conjunct of the invariant while the abstract
--        decode rets (`lpDone ∧ cp6`: `ProdSent` admits `pp9`, `RelayFwd` admits
--        `producing _ pp9`, `ConsRecv` admits `cp6`, and all three decode to
--        `Skip`/`Ret`).  So a NEW invariant component is needed;
--   (ii) with ANY ONE non-`Fin` peer carried, the refutation is EIGHT banked
--        `ret`-inversion rungs plus `SysSqrt.tableSpec-ret-fin` plus one absurd
--        pattern — the ten-arm `LegPos` dispatch the gate priced is dead work.
--
-- THIS MODULE IS (ii), MACHINE-CHECKED, at the verifier's siting: the peer is
-- NODE B's LINK-AB bundle KA CLIENT, at the FINE position `kcHead KA.stClient`
-- (its coarsening is `NS.kcClient`, whose `kaCfin` is `false`; the gate's
-- node-D/abstract-position version does not even typecheck).  Nodes A/B/C are
-- the sitings whose api successors are built inside the NON-FROZEN
-- `LiveLegApiCone`, so this is the siting a future discharge wants.
--
-- AND THE CONJUNCT IS CARRIED.  `LiveLegAssembly.LegJoint⁺` gained
-- `LiveKAFrozen.KAcFrz` as its trailing component, so `LiveFSim`'s `Rel` hands the
-- freeze to the `√` arm for free and (P5) IS A THEOREM — it left `Sim`'s telescope
-- and `LivenessProof.Premises` (which has had ZERO fields since the cellCp3 window
-- discharged `cellCp3`; it read ONE field from T12's close of the cross-node api
-- campaign, and "now three fields", true only until T8c-iii).  What made that possible was
-- owner grant #6: the io cone that binds a bundle's `InertPos` successor
-- (`PipeNodeIoEvo.top-nodes-io-evoP`, via the per-node `NodeXEvR-io` records) had
-- only the `Cf`/`Sf` fact channels, neither of which sees `InertPos`, so it gained
-- a third abstract family; `LiveLegIoCone` and `LiveLegApiCone` instantiate it at
-- `KAcAtHead ip → KAcAtHead ip′`.
--
-- NOTE the fact recorded here beyond the ladder: the ladder consumes NO
-- `LegJointB` at all.  So the theorem this module exports is STRICTLY STRONGER
-- than the premise (P5) used to be, and `noRetA-lit` below is that premise's
-- literal shape, derived from it in one line.
--
-- Consumed by `LiveFSim`'s §4 `sqrt-⊥` (the ONLY consumer of the `√` arm).  No
-- postulate, hole, meta, `NON_TERMINATING` or `mutual`.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveRetFree
  (blkA : Block₃) where

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Bool using ( true; false )
open import Data.Empty using ( ⊥ )
open import Data.Product using ( proj₁; proj₂ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; subst )

open import Process_Trees using ( PTree; ExtI; ret )
open PTree using ( force )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; linkAB )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟; Link )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using ( Dir; hi; lo )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )
import CSP.Examples.Cardano_network.KeepAlive p as KA

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_ )

import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
-- the frozen position, the conjunct and the inversion that preserves it all live
-- together, so they cannot drift apart
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveKAFrozen blkA as KAF
open KAF using ( KAcAtHead )
-- the assembly, for the LITERAL premise type of (P5) (`noRetA-lit` below).  No
-- cycle: the assembly takes the conjunct from `LiveKAFrozen`, not from here.
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegAssembly blkA as LA
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.NodeSpecs blkA as NS
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; med; nA; nB; nC; nD; initial )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( decMed )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
  using ( NetProc; absDec; absNodeA; absNodeB; absNodeC; absNodeD
        ; absBundleG; absKAc; coarsenKAc )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysSqrt blkA
  using ( fHide-ret-inv; ⦀-ret-inv; ∥⇙-ret-inv; tableSpec-ret-fin )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( RState; radec; toSys )

------------------------------------------------------------------------
-- THE INERT-FREEZE CONJUNCT.
------------------------------------------------------------------------

-- the ONE-PEER inert-freeze conjunct and its seed are `LiveKAFrozen`'s (they live
-- beside the position they are about and beside the inversion that preserves it);
-- re-exported here because this module's own statements are phrased in them:
-- node B's link-AB bundle KA CLIENT sits at its loop head, at the FINE position
-- (`SysStep.coarsenKAc (kcHead stClient)` is `NS.kcClient`, whose only rows are the
-- two `apiKA` requests — and `apiKA` is never offered by the abstract nodes, so
-- this peer is the system's permanently non-terminal one)
open KAF public using ( KAcFrz; KAcFrz-init )

------------------------------------------------------------------------
-- THE `ret` REFUTATION — eight banked rungs, `tableSpec-ret-fin`, one absurdity.
--
-- `∖`, `∥⇘ ⇙` and `⦀` all preserve `ret` BACKWARD (`SysSqrt`'s `fHide-ret-inv`,
-- `∥⇙-ret-inv`, `⦀-ret-inv`), so a `ret` of the whole abstract decode peels to a
-- `ret` of every component, in particular of ONE chosen peer.  Each rung is
-- stated at an EXPLICIT type: the inversions leave their operands as metas that
-- only a typed consumer pins (the shape `SysSqrt.decNodeB-wret` uses).
------------------------------------------------------------------------

-- rungs 7-8: an abstract bundle rets only if its LEADING KA-client peer does,
-- i.e. only if that peer's coarse position is `Fin`
bundle-ret-kaCfin : (l : Link) (cl sv : Dir)
      (csc : SN.CScPos) (css : SN.CSsPos) (bfc : SN.BFcPos) (bfs : SN.BFsPos)
      (ip : SN.InertPos) {x : ⊤ {0ℓ}}
    → force (absBundleG l cl sv csc css bfc bfs ip) ≡ ret x
    → NS.kaCfin (coarsenKAc (SN.kac ip)) ≡ true
bundle-ret-kaCfin l cl sv csc css bfc bfs ip eq =
  tableSpec-ret-fin _ (coarsenKAc (SN.kac ip)) kacRet
  where
    kacRet : force (absKAc l cl (SN.kac ip)) ≡ ret tt
    kacRet = proj₁ (⦀-ret-inv eq)

-- rungs 5-6: node B rets only if its LINK-AB bundle does (the driver side of the
-- `∥⇘ apiES ⇙` and the link-BD bundle are discarded)
nodeB-ret-kaCfin : (nb : SN.NodeStateB) {x : ⊤ {0ℓ}}
    → force (absNodeB nb) ≡ ret x
    → NS.kaCfin (coarsenKAc (SN.kac (SN.NodeStateB.inert-AB nb))) ≡ true
nodeB-ret-kaCfin (SN.mkNodeB cscab cssab bfcab bfsab cscbd cssbd bfcbd bfsbd cpb ipab ipbd) eq =
  bundle-ret-kaCfin linkAB hi lo cscab cssab bfcab bfsab ipab bundABret
  where
    bundABret : force (absBundleG linkAB hi lo cscab cssab bfcab bfsab ipab) ≡ ret tt
    bundABret = proj₁ (⦀-ret-inv (proj₁ (∥⇙-ret-inv eq)))

-- rungs 1-4: the whole abstract decode rets only if node B does (the outer hide,
-- the medium/nodes `∥⇘ ioES ⇙`, and two rungs of the four-node `⦀` nest)
absDec-ret-kaCfin : (s : SysState) {x : ⊤ {0ℓ}}
    → force (absDec s) ≡ ret x
    → NS.kaCfin (coarsenKAc (SN.kac (SN.NodeStateB.inert-AB (nB s)))) ≡ true
absDec-ret-kaCfin s {x} eq = nodeB-ret-kaCfin (nB s) nodeBret
  where
    -- the four abstract nodes, named so the hide rung can pass its operand
    -- EXPLICITLY: `fHide-ret-inv`'s `P` is otherwise a meta whose constraint is
    -- blocked under `force` (the `∖` reduct is a `with`-function application, and
    -- `force` is not invertible), which no later consumer pins
    nodesP : NetProc
    nodesP = absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))
    inner : force (decMed (med s) ∥⇘ ioES ⇙ nodesP) ≡ ret x
    inner = fHide-ret-inv {P = decMed (med s) ∥⇘ ioES ⇙ nodesP} {A = ioES} eq
    nodeBret : force (absNodeB (nB s)) ≡ ret tt
    nodeBret = proj₁ (⦀-ret-inv (proj₂ (⦀-ret-inv (proj₂ (∥⇙-ret-inv inner)))))

-- the ladder's last rung: `kaCfin NS.kcClient` is `false` (`NodeSpecs:185-188`)
false≢true : false ≡ true → ⊥
false≢true ()

-- *** THE REFUTATION. ***  A config whose node-B/link-AB KA client is frozen at
-- `kcHead KA.stClient` cannot force to `ret`: the ladder makes that peer's coarse
-- position `Fin`, and `kaCfin (coarsenKAc (kcHead stClient)) = kaCfin kcClient`
-- is `false`.
absDec-noRet : (s : SysState) → KAcFrz s
             → {x : ⊤ {0ℓ}} → force (absDec s) ≡ ret x → ⊥
absDec-noRet s frz eq =
  false≢true (subst (λ q → NS.kaCfin (coarsenKAc q) ≡ true) frz (absDec-ret-kaCfin s eq))

-- (P5) `noRetA` AT THE INERT-FREEZE HYPOTHESIS, in the premise's own `RState`
-- shape (`radec r = absDec (toSys r)` definitionally).  *** The premise's
-- `LegJointB legBD (toSys r)` argument is NOT consumed anywhere above ***, which
-- is the machine-checked form of the verifier's finding (i): the carried
-- invariant contributes nothing to the refutation.
radec-noRet : (r : RState) → KAcFrz (toSys r)
            → {x : ⊤ {0ℓ}} → force (radec r) ≡ ret x → ⊥
radec-noRet r frz eq = absDec-noRet (toSys r) frz eq

-- (P5) `noRetA` AT ITS LITERAL PREMISE TYPE — the shape `LiveFSim.Sim` asked for
-- until this module discharged it, and the shape `LiveFSim.sqrt-⊥` consumes.  The
-- `LegJointB` argument is where the conjunct now comes FROM (its trailing
-- component, at either leg), which is exactly why the premise could be dropped.
noRetA-lit : (r : RState) → LA.LegJointB legBD (toSys r)
           → {x : ⊤ {0ℓ}} → force (radec r) ≡ ret x → ⊥
noRetA-lit r j eq = radec-noRet r (proj₂ (proj₂ (j legBD))) eq
