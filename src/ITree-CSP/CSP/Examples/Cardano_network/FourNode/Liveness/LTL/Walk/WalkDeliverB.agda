{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 (SESSION-34, `wprog` discharge) — the PREMISE-FREE
-- per-observable-step reflector (`Praos.WalkDeliverB`).
--
-- Mirrors `WalkDeliver.deliver` clause-for-clause, with the `wprog`
-- premise DELETED.  The walk invariant is enriched to
-- `PrU r = Pr b r × Unb gs (toSys r)` (the pending leg AND the confined
-- group's two links still unbroken), and:
--
--   · the TERMINAL frames (`done`/`stuck`/`√`) — previously the ONLY
--     consumers of `wprog` — are refuted by `Unb` alone: the τ*-run fixes
--     every break flag (`liftτ*-brk`), and an unbroken link's `break`
--     offer (`WalkBrkFire.unb-{ret,stuck}-⊥`) contradicts a `ret`/stuck
--     descendant.  `Pr` is NOT needed there.
--   · each POSITIVE step (api/done/break) runs the existing `Pr`/μ lift
--     AND the parallel `WalkBrkLift` flag lift on the SAME weak step; the
--     two independently-built successors are glued by the decode
--     transport `unbT` (`radec rᵤ ≡ tailIdx w ≡ radec r′`).
--   · the `break l₀` step preserves `Unb` because the trace confinement
--     pins `l₀` off the protected links (`head-not-prot` at the head).
--
-- No postulate/hole/meta; no `dne`; NO `wprog`.  Base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
import Data.Unit as U
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Product using ( Σ; Σ-syntax; _,_; _×_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Nat using ( _<_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; trans; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkDeliverB (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Base using ( hi )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; Link
        ; apiCS; apiBF; apiTS; apiKA; apiLN; apiLF; break
        ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; store; env
        ; recvBFBlock; sendBFBlock; sendBFBatchDone; reqBFRange
        ; sendBFRequestRange; sendBFClientDone; sendBFStartBatch; sendBFNoBlocks )
  renaming ( done to netDone )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( Event; Event√; evl; √; evLabel; ev; _─[_]─►_; sRet )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_; wev; _─[τ*]─►_ )
open import Semantics.Deadlock {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( IsStuck )

open import Semantics.LTL.Traces_Based
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( atom )
open import Semantics.LTL.WTrace
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( WTrace; step; done; stuck; div; ⟦_⟧ᵂ; tailIdx )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; med )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( NetProc; RState; radec; toSys )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.Walk blkA
  using ( μTot )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( Pr; Pr-step; legBD; legCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkReachExpose blkA
  using ( liftReach-ev-expose; liftReach-break-expose )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvNoDiv blkA
  using ( absNoDiv )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkDeliver blkA
  using ( refute-weak; isRecvBF )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysBisim blkA as SB
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA as SO
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysRoute blkA as SR
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Spec
  using ( arrivedD⁻ )

open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkBrkFire blkA
  using ( GSide; protA; protB; Unb; unbFix; unbT; unb-retU; unb-stuckU )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkBrkLift blkA
  using ( liftτ*-brk; liftReach-ev-brk; liftReach-break-brk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkUnbLocate blkA
  using ( Cfᵂ; head-not-prot )

------------------------------------------------------------------------
-- `deliverB` — TOTAL over the WTrace head, at a fixed block `b` and a fixed
-- confined side `gs`.  NO premise module.
------------------------------------------------------------------------

module _ (b : Block₃) (gs : GSide) where

  -- the enriched walk invariant: pending AND the protected links unbroken
  PrU : RState → Set
  PrU r = Pr b r × Unb gs (toSys r)

  deliverB : (r : RState) → PrU r
           → (w : WTrace (⊤ {0ℓ}) (radec r)) → Cfᵂ gs w
           → ⟦ atom arrivedD⁻ ⟧ᵂ w
           ⊎ Σ[ r′ ∈ RState ] (tailIdx w ≡ radec r′)
               × (μTot (toSys r′) < μTot (toSys r)) × PrU r′

  -- terminal frames: refuted by the UNBROKEN-LINK offer alone (`Pr` unread)
  deliverB r pr (done run eqr) _ =
    let (r₁ , u≡ , bfix) = liftτ*-brk r run
    in  ⊥-elim (unb-retU (toSys r₁) gs
                  (unbFix (toSys r) (toSys r₁) gs bfix (proj₂ pr))
                  (subst (λ z → PTree.force z ≡ _) u≡ eqr))
  deliverB r pr (stuck run st) _ =
    let (r₁ , u≡ , bfix) = liftτ*-brk r run
    in  ⊥-elim (unb-stuckU (toSys r₁) gs
                  (unbFix (toSys r) (toSys r₁) gs bfix (proj₂ pr))
                  (subst IsStuck u≡ st))
  deliverB r pr (div dv) _ = ⊥-elim (absNoDiv r dv)

  -- √-step: its middle is an `sRet`, so the τ*-prefix reaches a `ret`
  -- descendant — refuted like `done`
  deliverB r pr (step {e = √ x} (wev pfx (sRet feq) _) _) _ =
    let (r₁ , p′≡ , bfix) = liftτ*-brk r pfx
    in  ⊥-elim (unb-retU (toSys r₁) gs
                  (unbFix (toSys r) (toSys r₁) gs bfix (proj₂ pr))
                  (subst (λ z → PTree.force z ≡ _) p′≡ feq))

  -- apiCS (driver-advance, never delivering): successor, c34 impossible
  deliverB r pr (step {e = evl (evLabel _ (apiCS l₀ d₀ m) a)} wstep _) _
    with liftReach-ev-expose r SO.aicCS tt wstep
       | liftReach-ev-brk r SO.aicCS tt wstep
  ... | r′ , eq , lt , drep | rᵤ , equ , bfix
      with Pr-step b {r} {r′} (proj₁ pr) drep
  ...   | inj₁ pr′ =
          inj₂ (r′ , eq , lt , pr′ ,
                unbT (toSys rᵤ) (toSys r′) gs (trans (sym equ) eq)
                     (unbFix (toSys r) (toSys rᵤ) gs bfix (proj₂ pr)))
  ...   | inj₂ (_ , _ , _ , _ , lbl , _) = ⊥-elim (subst isRecvBF (sym lbl) U.tt)

  -- apiBF recvBFBlock: the DELIVERING hop — c34 on BD/CD builds `arrivedD`
  deliverB r pr (step {e = evl (evLabel _ (apiBF l₀ d₀ recvBFBlock) a)} wstep _) _
    with liftReach-ev-expose r SO.aicBF tt wstep
       | liftReach-ev-brk r SO.aicBF tt wstep
  ... | r′ , eq , lt , drep | rᵤ , equ , bfix
      with Pr-step b {r} {r′} (proj₁ pr) drep
  ...   | inj₁ pr′ =
          inj₂ (r′ , eq , lt , pr′ ,
                unbT (toSys rᵤ) (toSys r′) gs (trans (sym equ) eq)
                     (unbFix (toSys r) (toSys rᵤ) gs bfix (proj₂ pr)))
  ...   | inj₂ (legBD , _ , _ , _ , refl , _) = inj₁ (inj₁ refl , refl)
  ...   | inj₂ (legCD , _ , _ , _ , refl , _) = inj₁ (inj₂ refl , refl)

  -- apiBF non-delivering tags: successor, c34 impossible
  deliverB r pr (step {e = evl (evLabel _ (apiBF l₀ d₀ sendBFBlock) a)} wstep _) _
    with liftReach-ev-expose r SO.aicBF tt wstep
       | liftReach-ev-brk r SO.aicBF tt wstep
  ... | r′ , eq , lt , drep | rᵤ , equ , bfix
      with Pr-step b {r} {r′} (proj₁ pr) drep
  ...   | inj₁ pr′ =
          inj₂ (r′ , eq , lt , pr′ ,
                unbT (toSys rᵤ) (toSys r′) gs (trans (sym equ) eq)
                     (unbFix (toSys r) (toSys rᵤ) gs bfix (proj₂ pr)))
  ...   | inj₂ (_ , _ , _ , _ , lbl , _) = ⊥-elim (subst isRecvBF (sym lbl) U.tt)
  deliverB r pr (step {e = evl (evLabel _ (apiBF l₀ d₀ sendBFBatchDone) a)} wstep _) _
    with liftReach-ev-expose r SO.aicBF tt wstep
       | liftReach-ev-brk r SO.aicBF tt wstep
  ... | r′ , eq , lt , drep | rᵤ , equ , bfix
      with Pr-step b {r} {r′} (proj₁ pr) drep
  ...   | inj₁ pr′ =
          inj₂ (r′ , eq , lt , pr′ ,
                unbT (toSys rᵤ) (toSys r′) gs (trans (sym equ) eq)
                     (unbFix (toSys r) (toSys rᵤ) gs bfix (proj₂ pr)))
  ...   | inj₂ (_ , _ , _ , _ , lbl , _) = ⊥-elim (subst isRecvBF (sym lbl) U.tt)
  deliverB r pr (step {e = evl (evLabel _ (apiBF l₀ d₀ reqBFRange) a)} wstep _) _
    with liftReach-ev-expose r SO.aicBF tt wstep
       | liftReach-ev-brk r SO.aicBF tt wstep
  ... | r′ , eq , lt , drep | rᵤ , equ , bfix
      with Pr-step b {r} {r′} (proj₁ pr) drep
  ...   | inj₁ pr′ =
          inj₂ (r′ , eq , lt , pr′ ,
                unbT (toSys rᵤ) (toSys r′) gs (trans (sym equ) eq)
                     (unbFix (toSys r) (toSys rᵤ) gs bfix (proj₂ pr)))
  ...   | inj₂ (_ , _ , _ , _ , lbl , _) = ⊥-elim (subst isRecvBF (sym lbl) U.tt)
  deliverB r pr (step {e = evl (evLabel _ (apiBF l₀ d₀ sendBFRequestRange) a)} wstep _) _
    with liftReach-ev-expose r SO.aicBF tt wstep
       | liftReach-ev-brk r SO.aicBF tt wstep
  ... | r′ , eq , lt , drep | rᵤ , equ , bfix
      with Pr-step b {r} {r′} (proj₁ pr) drep
  ...   | inj₁ pr′ =
          inj₂ (r′ , eq , lt , pr′ ,
                unbT (toSys rᵤ) (toSys r′) gs (trans (sym equ) eq)
                     (unbFix (toSys r) (toSys rᵤ) gs bfix (proj₂ pr)))
  ...   | inj₂ (_ , _ , _ , _ , lbl , _) = ⊥-elim (subst isRecvBF (sym lbl) U.tt)
  deliverB r pr (step {e = evl (evLabel _ (apiBF l₀ d₀ sendBFClientDone) a)} wstep _) _
    with liftReach-ev-expose r SO.aicBF tt wstep
       | liftReach-ev-brk r SO.aicBF tt wstep
  ... | r′ , eq , lt , drep | rᵤ , equ , bfix
      with Pr-step b {r} {r′} (proj₁ pr) drep
  ...   | inj₁ pr′ =
          inj₂ (r′ , eq , lt , pr′ ,
                unbT (toSys rᵤ) (toSys r′) gs (trans (sym equ) eq)
                     (unbFix (toSys r) (toSys rᵤ) gs bfix (proj₂ pr)))
  ...   | inj₂ (_ , _ , _ , _ , lbl , _) = ⊥-elim (subst isRecvBF (sym lbl) U.tt)
  deliverB r pr (step {e = evl (evLabel _ (apiBF l₀ d₀ sendBFStartBatch) a)} wstep _) _
    with liftReach-ev-expose r SO.aicBF tt wstep
       | liftReach-ev-brk r SO.aicBF tt wstep
  ... | r′ , eq , lt , drep | rᵤ , equ , bfix
      with Pr-step b {r} {r′} (proj₁ pr) drep
  ...   | inj₁ pr′ =
          inj₂ (r′ , eq , lt , pr′ ,
                unbT (toSys rᵤ) (toSys r′) gs (trans (sym equ) eq)
                     (unbFix (toSys r) (toSys rᵤ) gs bfix (proj₂ pr)))
  ...   | inj₂ (_ , _ , _ , _ , lbl , _) = ⊥-elim (subst isRecvBF (sym lbl) U.tt)
  deliverB r pr (step {e = evl (evLabel _ (apiBF l₀ d₀ sendBFNoBlocks) a)} wstep _) _
    with liftReach-ev-expose r SO.aicBF tt wstep
       | liftReach-ev-brk r SO.aicBF tt wstep
  ... | r′ , eq , lt , drep | rᵤ , equ , bfix
      with Pr-step b {r} {r′} (proj₁ pr) drep
  ...   | inj₁ pr′ =
          inj₂ (r′ , eq , lt , pr′ ,
                unbT (toSys rᵤ) (toSys r′) gs (trans (sym equ) eq)
                     (unbFix (toSys r) (toSys rᵤ) gs bfix (proj₂ pr)))
  ...   | inj₂ (_ , _ , _ , _ , lbl , _) = ⊥-elim (subst isRecvBF (sym lbl) U.tt)

  -- done (api, driver receives CS-server callback): successor, c34 impossible
  deliverB r pr (step {e = evl (evLabel _ (netDone l₀ d₀ id) a)} wstep _) _
    with liftReach-ev-expose r SO.aicDone tt wstep
       | liftReach-ev-brk r SO.aicDone tt wstep
  ... | r′ , eq , lt , drep | rᵤ , equ , bfix
      with Pr-step b {r} {r′} (proj₁ pr) drep
  ...   | inj₁ pr′ =
          inj₂ (r′ , eq , lt , pr′ ,
                unbT (toSys rᵤ) (toSys r′) gs (trans (sym equ) eq)
                     (unbFix (toSys r) (toSys rᵤ) gs bfix (proj₂ pr)))
  ...   | inj₂ (_ , _ , _ , _ , lbl , _) = ⊥-elim (subst isRecvBF (sym lbl) U.tt)

  -- break: medium solo (`dFix` ⇒ `Pr` preserved); the CONFINEMENT pins the
  -- fired link off the protected pair, so `Unb` rides across `bupd-miss`
  deliverB r pr (step {e = evl (evLabel _ (break l₀) a)} wstep tr∞) cf
    with liftReach-break-expose r l₀ wstep
       | liftReach-break-brk r l₀ wstep
       | head-not-prot gs wstep tr∞ cf
  ... | r′ , eq , lt , drep | rᵤ , equ , bupd | notA , notB
      with Pr-step b {r} {r′} (proj₁ pr) drep
  ...   | inj₁ pr′ =
          inj₂ (r′ , eq , lt , pr′ ,
                unbT (toSys rᵤ) (toSys r′) gs (trans (sym equ) eq)
                     ( trans (bupd (protA gs) (λ q → notA (sym q))) (proj₁ (proj₂ pr))
                     , trans (bupd (protB gs) (λ q → notB (sym q))) (proj₂ (proj₂ pr)) ))
  ...   | inj₂ (_ , _ , _ , _ , lbl , _) = ⊥-elim (subst isRecvBF (sym lbl) U.tt)

  -- inert api events (not `IsApiCSBF`): no reachable state offers them
  deliverB r pr (step {e = evl (evLabel _ (apiKA l₀ d₀ m) a)} wstep _) _ =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-apiKA (med (toSys r₁)))
                    (SR.absnodes-no-nonCSBF (toSys r₁) tt (λ ())) st) wstep)
  deliverB r pr (step {e = evl (evLabel _ (apiTS l₀ d₀ m) a)} wstep _) _ =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-apiTS (med (toSys r₁)))
                    (SR.absnodes-no-nonCSBF (toSys r₁) tt (λ ())) st) wstep)
  deliverB r pr (step {e = evl (evLabel _ (apiLN l₀ d₀ m) a)} wstep _) _ =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-apiLN (med (toSys r₁)))
                    (SR.absnodes-no-nonCSBF (toSys r₁) tt (λ ())) st) wstep)
  deliverB r pr (step {e = evl (evLabel _ (apiLF l₀ d₀ m) a)} wstep _) _ =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-apiLF (med (toSys r₁)))
                    (SR.absnodes-no-nonCSBF (toSys r₁) tt (λ ())) st) wstep)

  -- hidden io events: `∖ ioES` makes them invisible (`oevB-no-io`)
  deliverB r pr (step {e = evl (evLabel _ (input l₀ d₀ id) a)} wstep _) _ =
    ⊥-elim (refute-weak r (λ r₁ st → SB.oevB-no-io r₁ tt st) wstep)
  deliverB r pr (step {e = evl (evLabel _ (output l₀ d₀ id) a)} wstep _) _ =
    ⊥-elim (refute-weak r (λ r₁ st → SB.oevB-no-io r₁ tt st) wstep)

  -- wire events: offered by neither the medium nor the abstract nodes
  deliverB r pr (step {e = evl (evLabel _ (sndmsg l₀ d₀ id) a)} wstep _) _ =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-sndmsg (med (toSys r₁)))
                    (SR.absnodes-no-sndmsg (toSys r₁)) st) wstep)
  deliverB r pr (step {e = evl (evLabel _ (rcvmsg l₀ d₀ id) a)} wstep _) _ =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-rcvmsg (med (toSys r₁)))
                    (SR.absnodes-no-rcvmsg (toSys r₁)) st) wstep)
  deliverB r pr (step {e = evl (evLabel _ (tx l₀ d₀ id) a)} wstep _) _ =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-tx (med (toSys r₁)))
                    (SR.absnodes-no-tx (toSys r₁)) st) wstep)
  deliverB r pr (step {e = evl (evLabel _ (sndack l₀ d₀ id) a)} wstep _) _ =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-sndack (med (toSys r₁)))
                    (SR.absnodes-no-sndack (toSys r₁)) st) wstep)
  deliverB r pr (step {e = evl (evLabel _ (rcvack l₀ d₀ id) a)} wstep _) _ =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-rcvack (med (toSys r₁)))
                    (SR.absnodes-no-rcvack (toSys r₁)) st) wstep)
  deliverB r pr (step {e = evl (evLabel _ (ack l₀ d₀ id) a)} wstep _) _ =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-ack (med (toSys r₁)))
                    (SR.absnodes-no-ack (toSys r₁)) st) wstep)

  -- node-local store / env channels: offered by neither medium nor abstract nodes
  deliverB r pr (step {e = evl (evLabel _ (store l₀ d₀ m) a)} wstep _) _ =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-store (med (toSys r₁)))
                    (SR.absnodes-no-store (toSys r₁)) st) wstep)
  deliverB r pr (step {e = evl (evLabel _ (env l₀ d₀ m) a)} wstep _) _ =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-env (med (toSys r₁)))
                    (SR.absnodes-no-env (toSys r₁)) st) wstep)
