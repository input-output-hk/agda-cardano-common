{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the PAYLOAD UPGRADE (`Praos.PipeValArrive`), SESSION-51
-- step (iv′)/(vi): turn the delivery walk's payload-AGNOSTIC observation
-- `arrivedD⁻` into the payload-CARRYING `arrivedD b`, closing the campaign's one
-- remaining model relaxation.
--
--     arrUpgradeAt : (b : Block₃) (tr : WTrace ⊤ abstractSystem) (n : ℕ)
--                  → ⟦ atom (producedA b) ⟧ᵂ (drop n tr)
--                  → (k : ℕ) → ⟦ atom arrivedD⁻ ⟧ᵂ (drop k (drop n tr))
--                  → ⟦ atom (arrivedD b) ⟧ᵂ (drop k (drop n tr))
--
-- WHY THIS AND NOT THE RECORDED FUSION.  Session 36 planned to fuse
-- `WalkReachExpose.liftReach-ev-expose` so that ONE successor carries both the
-- `DReport` and the `PipeVal` preservation, letting `PipeVal` ride the delivery
-- descent.  Measured against the code that is the expensive route: the medium-τ
-- arm fuses for free (`WalkTauExpose.τreflect-med-expose`'s successor IS
-- `PipeTauMed.drainSucc`'s) but the io arm does NOT — `τreflect-io-expose` builds
-- its successor from `WalkConvNodeFix.top-nodes-io-abs-fix` while `PipeValTauIo`
-- builds its own from `PipeNodeIoEvo.top-nodes-io-evo`, two different cones whose
-- `SysState`s are not convertible, so the whole `WalkTauExpose`/`WalkReachExpose`
-- family would have to be re-mirrored.
--
-- Instead `PipeVal` NEVER enters the descent.  The `F` witness the descent returns
-- hands over the delivering frame's INDEX `k` while the whole trace is still in
-- scope, so `PipeValWalk.pipeVal-fold` is run TWICE, composing at its own
-- successors and needing no index arithmetic at all:
--
--   · `rinit` ──(n steps, stop at `producedA b`)──► rₚ   with `PipeVal l (toSys rₚ)`
--   · rₚ      ──(k steps, stop at `arrivedD⁻`)───► r_d   with `PipeVal l (toSys r_d)`
--
-- The second call's start equality is LITERALLY the first call's output
-- (`dropIdx n tr ≡ radec rₚ`) and its trace is `drop n tr`, so `drop k (drop n tr)`
-- never has to be related to `drop (n + k) tr` — which would be a HETEROGENEOUS
-- equation (`drop`'s type is indexed by `dropIdx`).
--
-- ORDERING.  The `⊎` of `arrivedD⁻` (`l ≡ linkBD ⊎ l ≡ linkCD`) is cased FIRST,
-- before either fold is run, because `pipeVal-fold` is leg-INDEXED and the two
-- legs' folds build different successors — the same non-convertibility that kills
-- the fusion route, one level up.  Both legs' folds are supplied to `arrUpgrade`
-- so the split can happen inside it.
--
-- No postulate/hole/meta; no `dne`.  Base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
import Data.Unit as U
open import Data.Nat using ( ℕ; zero; suc )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValArrive (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using
  ( p; Block₃; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Net p using
  ( Net_Api; apiBF; recvBFBlock )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using ( hi )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_; wev )
open import Semantics.LTL.Traces_Based
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( LTLᵗ; atom )
open import Semantics.LTL.WTrace
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( WTrace; step; done; stuck; div; ⟦_⟧ᵂ; frameOf; IsTermᵂ
        ; drop; dropIdx )

open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Spec
  using ( producedA; arrivedD; arrivedD⁻ )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( NetProc; RState; radec; toSys )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.AbstractSystem blkA
  using ( abstractSystem )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( dnClient )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValInv blkA
  using ( PipeVal; CliValOK )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValStep blkA
  using ( TauIoV; tauStepV-from; liftτ*-preserveV′ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValTauIo blkA
  using ( tauIoV )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValEvStep blkA
  using ( stepEmitVᶠ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValRecv blkA
  using ( recvFire-blkA-BD; recvFire-blkA-CD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValWalk blkA
  using ( pipeVal-fold; pipeVal-along-walk; prodBlkA )

------------------------------------------------------------------------
-- (1) THE TERMINAL REFUTATION for the new stopping predicate — the 7-clause
-- mirror of `WalkCausal.term-no-prod`: `drop` stutters on a terminal frame, so
-- `frameOf (drop m w)` is again `done`/`stuck`/`div`, on which `arrivedD⁻` is `⊥`.
------------------------------------------------------------------------

-- a TERMINAL `WTrace` never presents a delivering frame at ANY position
term-no-arr : {t : NetProc} (w : WTrace (⊤ {0ℓ}) t) → IsTermᵂ w → (m : ℕ)
            → arrivedD⁻ (frameOf (drop m w)) → ⊥
term-no-arr (step _ _)     () _       _
term-no-arr (done p eq)   _ zero    ar = ar
term-no-arr (done p eq)   _ (suc m) ar = term-no-arr (done p eq)  U.tt m ar
term-no-arr (stuck p st)  _ zero    ar = ar
term-no-arr (stuck p st)  _ (suc m) ar = term-no-arr (stuck p st) U.tt m ar
term-no-arr (div dv)      _ zero    ar = ar
term-no-arr (div dv)      _ (suc m) ar = term-no-arr (div dv)     U.tt m ar

------------------------------------------------------------------------
-- (2) THE DELIVERED VALUE at a frame whose state carries the leg's `PipeVal`.
-- The delivering frame is a WEAK move; its τ-prefix is lifted with the value
-- preservation (`PipeValStep.liftτ*-preserveV′`, at its OWN successor — nothing
-- has to be related to anything else), and the strong middle then feeds
-- `PipeValRecv.recvFire-blkA-*` with the leg's client clause (7).
------------------------------------------------------------------------

-- clause (7) of the invariant, by projection
pv⇒cli : (l : TwoLegs) (s : SysState) → PipeVal l s → CliValOK (dnClient l s)
pv⇒cli l s (_ , _ , _ , _ , _ , _ , h7 , _) = h7

-- leg BD: a weak delivering move out of a `PipeVal`-carrying state fires `blkA`
arrValBD : (r : RState) {a : Block₃} {t′ : NetProc}
         → radec r ═[ ev (evl (evLabel Block₃ (apiBF linkBD hi recvBFBlock) a)) ]═► t′
         → PipeVal legBD (toSys r) → a ≡ blkA
arrValBD r {a} (wev pre mid post) pv =
  let (r₁ , eq₁ , pmap) = liftτ*-preserveV′ legBD (tauStepV-from legBD (tauIoV legBD)) r refl pre
  in  recvFire-blkA-BD r₁
        (subst (λ z → z ─[ ev (evl (evLabel Block₃ (apiBF linkBD hi recvBFBlock) a)) ]─► _)
               eq₁ mid)
        (pv⇒cli legBD (toSys r₁) (pmap pv))

-- leg CD (mirror)
arrValCD : (r : RState) {a : Block₃} {t′ : NetProc}
         → radec r ═[ ev (evl (evLabel Block₃ (apiBF linkCD hi recvBFBlock) a)) ]═► t′
         → PipeVal legCD (toSys r) → a ≡ blkA
arrValCD r {a} (wev pre mid post) pv =
  let (r₁ , eq₁ , pmap) = liftτ*-preserveV′ legCD (tauStepV-from legCD (tauIoV legCD)) r refl pre
  in  recvFire-blkA-CD r₁
        (subst (λ z → z ─[ ev (evl (evLabel Block₃ (apiBF linkCD hi recvBFBlock) a)) ]─► _)
               eq₁ mid)
        (pv⇒cli legCD (toSys r₁) (pmap pv))

------------------------------------------------------------------------
-- (3) THE FRAME UPGRADE.  One clause per link disjunct; every other frame shape
-- makes `arrivedD⁻` `⊥`, so Agda's coverage discharges it (the
-- `PipeLocate.prodFrame-inv` idiom).
------------------------------------------------------------------------

-- `arrivedD⁻` + `b ≡ blkA` + the leg's `PipeVal` at the frame ⇒ `arrivedD b`
arrUpgrade : (b : Block₃) → b ≡ blkA
           → (rBD rCD : RState) {t : NetProc} (w : WTrace (⊤ {0ℓ}) t)
           → t ≡ radec rBD → t ≡ radec rCD
           → PipeVal legBD (toSys rBD) → PipeVal legCD (toSys rCD)
           → arrivedD⁻ (frameOf w) → arrivedD b (frameOf w)
arrUpgrade b beq rBD rCD (step {e = evl (evLabel _ (apiBF l d recvBFBlock) a)} ws _)
           eqBD eqCD pvBD pvCD (inj₁ refl , refl) =
  inj₁ refl , refl
  , trans (arrValBD rBD
             (subst (λ z → z ═[ ev (evl (evLabel Block₃ (apiBF linkBD hi recvBFBlock) a)) ]═► _)
                    eqBD ws) pvBD)
          (sym beq)
arrUpgrade b beq rBD rCD (step {e = evl (evLabel _ (apiBF l d recvBFBlock) a)} ws _)
           eqBD eqCD pvBD pvCD (inj₂ refl , refl) =
  inj₂ refl , refl
  , trans (arrValCD rCD
             (subst (λ z → z ═[ ev (evl (evLabel Block₃ (apiBF linkCD hi recvBFBlock) a)) ]═► _)
                    eqCD ws) pvCD)
          (sym beq)

------------------------------------------------------------------------
-- (4) THE ASSEMBLY.  Run the two folds per leg (produce frame, then delivering
-- frame) and apply the upgrade.  `b ≡ blkA` is `PipeValWalk.prodBlkA`.
------------------------------------------------------------------------

-- the delivering frame's payload-carrying observation, from the agnostic one
arrUpgradeAt : (b : Block₃) (tr : WTrace (⊤ {0ℓ}) abstractSystem) (n : ℕ)
             → (pn : ⟦ atom (producedA b) ⟧ᵂ (drop n tr))
             → (k : ℕ) → (ar : ⟦ atom arrivedD⁻ ⟧ᵂ (drop k (drop n tr)))
             → ⟦ atom (arrivedD b) ⟧ᵂ (drop k (drop n tr))
arrUpgradeAt b tr n pn k ar =
  let (rpBD , eqpBD , pvpBD) = pipeVal-along-walk b legBD tr n pn
      (rpCD , eqpCD , pvpCD) = pipeVal-along-walk b legCD tr n pn
      (rdBD , eqdBD , pvdBD) = pipeVal-fold legBD arrivedD⁻ term-no-arr
                                 (stepEmitVᶠ legBD) rpBD eqpBD pvpBD (drop n tr) k ar
      (rdCD , eqdCD , pvdCD) = pipeVal-fold legCD arrivedD⁻ term-no-arr
                                 (stepEmitVᶠ legCD) rpCD eqpCD pvpCD (drop n tr) k ar
  in  arrUpgrade b (prodBlkA b tr n pn) rdBD rdCD (drop k (drop n tr))
        eqdBD eqdCD pvdBD pvdCD ar
