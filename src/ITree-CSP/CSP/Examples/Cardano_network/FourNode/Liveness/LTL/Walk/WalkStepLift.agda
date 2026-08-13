{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the STEP-LIFT REACHABILITY SPINE (`Praos.WalkStepLift`).
--
-- The `WalkEngine` descent reduces `walkPos` to `Pr`/`deliver`/`locate`.  Both
-- `deliver`'s successor branch and `locate` need the SAME reachability fact:
-- an ABSTRACT observable move from a reachable config lands on ANOTHER
-- reachable config's decode.  This module BUILDS that fact — the plan's
-- "reachability is FREE" claim, realised concretely from the R2 oracle
-- (`SysBisim.theOracle`, TOTAL, 0-postulate):
--
--   · `liftτ*`      : a hidden τ-run `radec r ─[τ*]─► u` lands on `u ≡ radec r′`
--                     (structural induction on the `─[τ*]─►` Star, `otauB` per hop);
--   · `liftReach-ev`: a WEAK VISIBLE move `radec r ═[ ev (evl e) ]═► t′`
--                     (`τ* · ev · τ*`) lands on `t′ ≡ radec r′` (`liftτ*` on the
--                     two τ-paddings + `oevB` on the strong middle hop).
--
-- This is EXACTLY the reachability half of the `WalkEngine.deliver`/`locate`
-- hypotheses; the NEW content those still need is the `μ`-DECREASE + event
-- CLASSIFICATION (`μGk-adv-*` per driver advance) + the pending invariant `Pr`
-- — none of which `liftReach-ev` provides (it is measure-blind), and which is
-- the remaining heavy multi-session crux.
--
-- HEAVY (pulls the `SysBisim`/`SysOracle` cone via `theOracle`), 0-postulate.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤ )
open import Data.Product using ( Σ; Σ-syntax; _,_; proj₁; proj₂ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; subst )

open import Process_Trees using ( ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkStepLift (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

-- reachable-config machinery + the whole-system process type
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( NetProc; RState; radec )
-- the R2 oracle: TOTAL abstract-step reflectors `otauB`/`oevB` (reachability)
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysBisim blkA
  using ( theOracle; otauB; oevB )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; τ; evl; Event )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wev )

------------------------------------------------------------------------
-- A hidden τ-run from a reachable config lands on a reachable config.
------------------------------------------------------------------------

-- generalised over the start tree with a `start ≡ radec r` witness, so the
-- Star sub-term `rest` is passed to the recursive call STRUCTURALLY unchanged
-- (the `subst` lands on the τ-step `s`, not on the recursion argument) — this
-- is what makes the descent pass the termination checker
liftτ*′ : (r : RState) {start u : NetProc} → start ≡ radec r
        → start ─[τ*]─► u → Σ[ r′ ∈ RState ] (u ≡ radec r′)
liftτ*′ r eq τ*-refl = r , eq
liftτ*′ r eq (τ*-step s rest) with theOracle .otauB r (subst (λ z → z ─[ τ ]─► _) eq s)
... | r₁ , eq₁ , _ = liftτ*′ r₁ eq₁ rest

-- iterate `otauB` over the `─[τ*]─►` Star (each hop is reachability-free)
liftτ* : (r : RState) {u : NetProc}
       → radec r ─[τ*]─► u → Σ[ r′ ∈ RState ] (u ≡ radec r′)
liftτ* r = liftτ*′ r refl

------------------------------------------------------------------------
-- A WEAK VISIBLE move from a reachable config lands on a reachable config.
------------------------------------------------------------------------

-- decompose `τ* · ev · τ*`: lift the leading τ-padding (`liftτ*`), the strong
-- middle ev hop (`oevB`), then the trailing τ-padding (`liftτ*`)
liftReach-ev : (r : RState) {e : Event} {t′ : NetProc}
             → radec r ═[ ev (evl e) ]═► t′
             → Σ[ r′ ∈ RState ] (t′ ≡ radec r′)
liftReach-ev r (wev pre mid post) with liftτ* r pre
... | r₁ , eq₁ with theOracle .oevB r₁ (subst (λ z → z ─[ ev (evl _) ]─► _) eq₁ mid)
...   | r₂ , eq₂ , _ = liftτ* r₂ (subst (λ z → z ─[τ*]─► _) eq₂ post)
