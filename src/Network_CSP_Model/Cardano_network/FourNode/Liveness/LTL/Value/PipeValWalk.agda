{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the WALK-LEVEL value layer (`Praos.PipeValWalk`),
-- SESSION-51.  Two independent results, both premise-free:
--
-- (A) `pipeVal-along-walk` — the block-VALUE invariant folded from `rinit` to the
--     located `producedA` frame, driven by `PipeValEvStep.stepEmitVᶠ` (which is
--     itself unconditional).  A verbatim mirror of
--     `PipeInvProd.pipeInvS-along-walk′` at `PipeVal`; the √/terminal backbone is
--     `WalkCausal`'s.
--
-- (B) `prodBlkA` — **the produced block IS `blkA`**:
--
--         prodBlkA : (b : Block₃) (tr : WTrace ⊤ abstractSystem) (n : ℕ)
--                  → ⟦ atom (producedA b) ⟧ᵂ (drop n tr) → b ≡ blkA
--
--     `producedA b` pins the frame to a weak `apiBF (linkAB|linkAC) hi
--     sendBFBlock ! b` move (`PipeLocate.prodFrame-inv`); at the reachable state
--     of that frame (`PipeLocate.locate`) the τ-prefix is lifted and node A's
--     produce driver `!`-pin (`PipeValProd.prodFire-blkA-{AB,AC}`) reads the fired
--     value off the step.  This is HALF of the payload-agnostic-`arrivedD` repair:
--     with `b ≡ blkA` in hand, restoring `arrivedD`'s `a ≡ b` conjunct reduces to
--     `a ≡ blkA` at the delivering frame, which is what (A) is for.
--
-- No postulate/hole/meta; no `dne`.  Base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤ )
import Data.Unit as U
open import Data.Nat using ( ℕ; zero; suc )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; subst )

open import Process_Trees using ( PTree; ExtI; deadlock )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValWalk (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using
  ( p; Block₃; linkAB; linkAC )
open import CSP.Examples.Cardano_network.Net p using
  ( Net_Api; apiBF; sendBFBlock )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using ( hi )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel; Event; Event√; √ )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_; wev )
open import Semantics.LTL.Traces_Based
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( LTLᵗ; atom; FramePred )
open import Semantics.LTL.WTrace
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( WTrace; step; done; stuck; div; ⟦_⟧ᵂ; frameOf; IsTermᵂ
        ; drop; dropIdx; tail; tailIdx; dropIdx-stutter )

open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Spec
  using ( producedA )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; initial )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( NetProc; RState; radec; toSys; rinit; rinit-toSys; radec-init )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.AbstractSystem blkA
  using ( abstractSystem )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkCausal blkA
  using ( term-no-prod; noWeakVis-deadlock; sqrt-target-deadlock )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkTauExpose blkA
  using ( liftτ*-expose )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValInv blkA
  using ( PipeVal; pipeVal-init )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValStep blkA
  using ( StepEmitV )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValEvStep blkA
  using ( stepEmitVᶠ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValProd blkA
  using ( prodFire-blkA-AB; prodFire-blkA-AC )
import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeLocate blkA as PL

------------------------------------------------------------------------
-- (A) THE WALK FOLD at `PipeVal` (mirror `PipeInvProd.pipeInvS-along-walk′`).
------------------------------------------------------------------------

-- SESSION-51: GENERIC in the stopping predicate.  `producedA` was consumed in ONE
-- place only — the `√` clause, where the tail is terminal and the predicate has to
-- be refutable there — so the same fold serves the DELIVERING frame
-- (`arrivedD⁻` + `PipeValArrive.term-no-arr`), which is what lets the value layer
-- run from `rinit` to the delivery instead of riding the descent.
module _ (l : TwoLegs) (φ : FramePred 0ℓ (⊤ {0ℓ}))
         (termNo : {t : NetProc} (w : WTrace (⊤ {0ℓ}) t) → IsTermᵂ w → (m : ℕ)
                 → φ (frameOf (drop m w)) → ⊥) where

  -- fold the value preservation along the walk to the frame at position `n`
  pipeVal-fold : StepEmitV l → (r : RState) {t : NetProc} → t ≡ radec r
               → PipeVal l (toSys r)
               → (w : WTrace (⊤ {0ℓ}) t) (n : ℕ) → φ (frameOf (drop n w))
               → Σ[ r′ ∈ RState ] (dropIdx n w ≡ radec r′) × PipeVal l (toSys r′)
  pipeVal-fold emit r eq pv w zero pn = r , eq , pv
  -- a visible `evl`-step: transport the value invariant, recurse on the tail
  pipeVal-fold emit r eq pv (step {e = evl e0} wstep tr) (suc m) pn
    with emit r (subst (λ z → z ═[ ev (evl e0) ]═► _) eq wstep)
  ... | r₁ , eq₁ , ps =
        pipeVal-fold emit r₁ eq₁ (ps pv)
          (tail (step {e = evl e0} wstep tr)) m pn
  -- a `√`-step: the tail lives over `deadlock`, hence terminal ⇒ no `producedA`
  pipeVal-fold emit r eq pv (step {e = √ x} wstep tr) (suc m) pn =
    ⊥-elim (termNo (tail (step {e = √ x} wstep tr)) termTail m pn)
    where
      tdead : tailIdx (step {e = √ x} wstep tr) ≡ deadlock
      tdead = sqrt-target-deadlock wstep
      termTail : IsTermᵂ (tail (step {e = √ x} wstep tr))
      termTail with tail (step {e = √ x} wstep tr)
      ... | step wstep₂ _ =
              ⊥-elim (noWeakVis-deadlock (subst (λ z → z ═[ ev _ ]═► _) tdead wstep₂))
      ... | done _ _  = U.tt
      ... | stuck _ _ = U.tt
      ... | div _     = U.tt
  -- terminal frames: `dropIdx` stutters back to the start index; value kept
  pipeVal-fold emit r eq pv (done q eqr) (suc m) pn =
    r , trans (dropIdx-stutter (suc m) (done q eqr) U.tt) eq , pv
  pipeVal-fold emit r eq pv (stuck q st) (suc m) pn =
    r , trans (dropIdx-stutter (suc m) (stuck q st) U.tt) eq , pv
  pipeVal-fold emit r eq pv (div dv) (suc m) pn =
    r , trans (dropIdx-stutter (suc m) (div dv) U.tt) eq , pv

-- headline: seeded at `rinit`, driven by the UNCONDITIONAL `stepEmitVᶠ`, stopped
-- at the located `producedA` frame
pipeVal-along-walk : (b : Block₃) (l : TwoLegs)
                     (tr : WTrace (⊤ {0ℓ}) abstractSystem) (n : ℕ)
                   → producedA b (frameOf (drop n tr))
                   → Σ[ r′ ∈ RState ] (dropIdx n tr ≡ radec r′) × PipeVal l (toSys r′)
pipeVal-along-walk b l tr n pn =
  pipeVal-fold l (producedA b) (term-no-prod b) (stepEmitVᶠ l) rinit (sym radec-init)
    (subst (PipeVal l) (sym rinit-toSys) (pipeVal-init l)) tr n pn

------------------------------------------------------------------------
-- (B) THE PRODUCED BLOCK IS `blkA`.  The weak produce move's τ-prefix is lifted
-- (any reachability-preserving τ-run lift will do — `liftτ*-expose` is reused),
-- then node A's driver `!`-pin reads the fired value off the STRONG middle.
------------------------------------------------------------------------

-- a WEAK `apiBF linkAB hi sendBFBlock ! b` out of `radec r` forces `b ≡ blkA`
weak-blkA-AB : (r : RState) (b : Block₃) {t′ : NetProc}
             → radec r ═[ ev (evl (evLabel Block₃ (apiBF linkAB hi sendBFBlock) b)) ]═► t′
             → b ≡ blkA
weak-blkA-AB r b (wev pre mid post) =
  let (r₁ , eq₁ , _ , _) = liftτ*-expose r pre
  in  prodFire-blkA-AB r₁
        (subst (λ z → z ─[ ev (evl (evLabel Block₃ (apiBF linkAB hi sendBFBlock) b)) ]─► _)
               eq₁ mid)

-- the AC mirror
weak-blkA-AC : (r : RState) (b : Block₃) {t′ : NetProc}
             → radec r ═[ ev (evl (evLabel Block₃ (apiBF linkAC hi sendBFBlock) b)) ]═► t′
             → b ≡ blkA
weak-blkA-AC r b (wev pre mid post) =
  let (r₁ , eq₁ , _ , _) = liftτ*-expose r pre
  in  prodFire-blkA-AC r₁
        (subst (λ z → z ─[ ev (evl (evLabel Block₃ (apiBF linkAC hi sendBFBlock) b)) ]─► _)
               eq₁ mid)

-- THE RESULT: whatever block node A is observed to hand out, it is `blkA`
prodBlkA : (b : Block₃) (tr : WTrace (⊤ {0ℓ}) abstractSystem) (n : ℕ)
         → ⟦ atom (producedA b) ⟧ᵂ (drop n tr)
         → b ≡ blkA
prodBlkA b tr n pn with PL.locate b tr n pn | PL.prodFrame-inv b (drop n tr) pn
... | r0 , eq0 , _ | t′ , inj₁ ws =
      weak-blkA-AB r0 b
        (subst (λ z → z ═[ ev (evl (evLabel Block₃ (apiBF linkAB hi sendBFBlock) b)) ]═► t′)
               eq0 ws)
... | r0 , eq0 , _ | t′ , inj₂ ws =
      weak-blkA-AC r0 b
        (subst (λ z → z ═[ ev (evl (evLabel Block₃ (apiBF linkAC hi sendBFBlock) b)) ]═► t′)
               eq0 ws)
