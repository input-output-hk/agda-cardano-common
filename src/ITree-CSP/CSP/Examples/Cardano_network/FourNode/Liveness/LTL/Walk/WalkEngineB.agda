{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 (SESSION-34, `wprog` discharge) — the SIDE-FIXED walk
-- descent engine and the premise-free `walkPos` (`Praos.WalkEngineB`).
--
-- Mirror of `WalkEngine`'s well-founded descent, but over the SIDE-FIXED
-- confinement `Cfᵂ gs` (one `G⁺`, not the `⊎`): the enriched invariant
-- `PrU = Pr × Unb gs` is only preservable when the walk KNOWS which group
-- the trace protects, so the root `⊎` is cased ONCE (`walkPosB`) and each
-- branch runs its own side's descent with `WalkDeliverB.deliverB` and
-- `WalkUnbLocate.locateU`.  `walkPosB` inhabits `Walk.walkPos`'s module
-- parameter type EXACTLY — the `wprog` slot is GONE.
--
-- The generic `G⁺`/`F` plumbing (`G⁺-dropn`, `F-suc`, `F-transport`) is
-- imported from the frozen `WalkEngine` unchanged.
--
-- No postulate/hole/meta; no `dne`; NO premise module.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤ )
open import Data.Nat using ( ℕ; zero; suc; _<_ )
open import Data.Nat.Induction using ( <-wellFounded )
open import Induction.WellFounded using ( Acc; acc )
open import Data.Product using ( Σ; Σ-syntax; _,_; _×_ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkEngineB (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( NetProc; RState; radec; toSys )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.AbstractSystem blkA
  using ( abstractSystem )

open import Semantics.LTL.Traces_Based
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( atom; ¬_; F_ )
open import Semantics.LTL.WTrace
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( WTrace; ⟦_⟧ᵂ; drop; dropIdx; tail; tailIdx )

open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Spec
  using ( producedA; arrivedD; arrivedD⁻; brkG1; brkG2 )

open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.Walk blkA
  using ( μTot; G⁺ᵂ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkEngine blkA
  using ( G⁺-dropn; F-suc; F-transport )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkBrkFire blkA
  using ( GSide; g1; g2 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkUnbLocate blkA
  using ( Cfᵂ; Cf-tail; brkOf; locateU )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkDeliverB blkA
  using ( PrU; deliverB )
-- SESSION-51: the PAYLOAD upgrade.  The descent establishes the payload-AGNOSTIC
-- `arrivedD⁻`; the `F` witness then hands over the delivering frame's index while
-- `tr` is still in scope, so the value layer runs from `rinit` to that frame
-- instead of riding the descent.
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValArrive blkA
  using ( arrUpgradeAt )

------------------------------------------------------------------------
-- Side-fixed confinement plumbing (mirror `Conf-subst` / `Conf-dropn`).
------------------------------------------------------------------------

-- transport a side-fixed confinement along an index equality
Cf-subst : (gs : GSide) {t₁ t₂ : NetProc} (eq : t₁ ≡ t₂) {w : WTrace (⊤ {0ℓ}) t₁}
         → Cfᵂ gs w → Cfᵂ gs (subst (WTrace (⊤ {0ℓ})) eq w)
Cf-subst gs refl x = x

-- side-fixed confinement restricts to an n-fold suffix
Cf-dropn : (gs : GSide) (n : ℕ) {t : NetProc} (w : WTrace (⊤ {0ℓ}) t)
         → Cfᵂ gs w → Cfᵂ gs (drop n w)
Cf-dropn gs n w = G⁺-dropn (¬ atom (brkOf gs)) n w

------------------------------------------------------------------------
-- THE SIDE-FIXED WELL-FOUNDED DELIVERY DESCENT (mirror `WalkEngine.descend`).
------------------------------------------------------------------------

module _ (gs : GSide) (b : Block₃) where

  -- accessible form: with `μTot (toSys r)` accessible, delivery from `r`
  descend-acc : (r : RState) → PrU b gs r
              → (w : WTrace (⊤ {0ℓ}) (radec r)) → Cfᵂ gs w
              → Acc _<_ (μTot (toSys r)) → ⟦ F_ (atom arrivedD⁻) ⟧ᵂ w
  descend-acc r pr w cf (acc rec) with deliverB b gs r pr w cf
  ... | inj₁ arr = zero , arr , (λ _ ())
  ... | inj₂ (r′ , eq , lt , pr′) =
        F-suc (atom arrivedD⁻) w
          (F-transport (atom arrivedD⁻) eq (tail w)
            (descend-acc r′ pr′
              (subst (WTrace (⊤ {0ℓ})) eq (tail w))
              (Cf-subst gs eq (Cf-tail gs w cf))
              (rec lt)))

  -- delivery from any reachable, side-confined, pending-and-unbroken `r`
  descend : (r : RState) → PrU b gs r
          → (w : WTrace (⊤ {0ℓ}) (radec r)) → Cfᵂ gs w
          → ⟦ F_ (atom arrivedD⁻) ⟧ᵂ w
  descend r pr w cf = descend-acc r pr w cf (<-wellFounded (μTot (toSys r)))

------------------------------------------------------------------------
-- `walkPosB` — the PREMISE-FREE positive walk: case the root `⊎` once,
-- run each side's descent from its `locateU` start.  This is EXACTLY the
-- type of `Walk.walkPos` (`AbstractLive`'s remaining slot).  The per-side
-- body is a `let` over the Σ (NOT a `with` — the with-translation of the
-- `locateU` application exhausts the heap; the applicative `let` is cheap).
------------------------------------------------------------------------

-- one side's walk: locate (`Pr` + `Unb`), then descend
walkSide : (gs : GSide) (b : Block₃) (tr : WTrace (⊤ {0ℓ}) abstractSystem)
         → Cfᵂ gs tr
         → (n : ℕ) → ⟦ atom (producedA b) ⟧ᵂ (drop n tr)
         → ⟦ F_ (atom (arrivedD b)) ⟧ᵂ (drop n tr)
walkSide gs b tr g n prod =
  let (r0 , eq0 , pr0 , unb0) = locateU gs b tr g n prod
      (k , ar , rest) =
        F-transport (atom arrivedD⁻) eq0 (drop n tr)
          (descend gs b r0 (pr0 , unb0)
            (subst (WTrace (⊤ {0ℓ})) eq0 (drop n tr))
            (Cf-subst gs eq0 (Cf-dropn gs n tr g)))
  in  k , arrUpgradeAt b tr n prod k ar , rest

-- the ⊎-rooted walk (the literal `Walk.walkPos` slot type)
walkPosB : (b : Block₃) (tr : WTrace (⊤ {0ℓ}) abstractSystem)
         → (G⁺ᵂ (¬ atom brkG1) tr ⊎ G⁺ᵂ (¬ atom brkG2) tr)
         → (n : ℕ) → ⟦ atom (producedA b) ⟧ᵂ (drop n tr)
         → ⟦ F_ (atom (arrivedD b)) ⟧ᵂ (drop n tr)
walkPosB b tr (inj₁ g) = walkSide g1 b tr g
walkPosB b tr (inj₂ g) = walkSide g2 b tr g
