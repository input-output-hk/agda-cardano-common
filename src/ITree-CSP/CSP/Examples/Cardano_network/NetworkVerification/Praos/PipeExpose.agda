{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the FORWARD `PipeInv⁺`-THREADING ENGINE
-- (`Praos.PipeExpose`).
--
-- `PipeInv.pipeInv⁺-step : PipeStep⁺ l s s′ → PipeInv⁺ l s → PipeInv⁺ l s′`
-- is the GREEN consumer-side dispatcher (a classified step preserves the
-- strengthened per-leg single-token invariant).  This module FOLDS it along
-- the FORWARD reachability walk of `WalkCausal.walkReach′`, threading
-- `PipeInv⁺ l (toSys r)` from the seed `pipeInv⁺-init` to the located
-- `producedA` frame — the shared engine that `pcone` (and later
-- producer-exposure / `wprog`) consume:
--
--   `pipeInv⁺-along-walk′` : from a reachable `r` with `PipeInv⁺ l (toSys r)`,
--   a `WTrace` of `radec r`, and a `producedA b` frame at position `n`,
--   produce the reachable suffix index `radec r′` TOGETHER with
--   `PipeInv⁺ l (toSys r′)`.
--
-- The one still-missing ingredient is the per-step CLASSIFIER `StepEmit l` —
-- a weak visible move `radec r ═[ ev (evl e) ]═► t′` decoded to the reachable
-- successor `r′` (`t′ ≡ radec r′`) AND its `PipeStep⁺ l (toSys r) (toSys r′)`
-- class.  That is the WalkDExpose-scale FORWARD EXPOSURE CONE (extend
-- `WalkReachExpose.liftReach-ev-expose`'s `DReport` to all seven leg-`l`
-- components; oracle-scale, RAM-risky, ×2 legs, multi-session).  It is taken
-- here as an EXPLICIT COMBINATOR ARGUMENT — exactly as `WalkEngine.walkPosFrom`
-- takes `deliver`/`locate` — so the ENGINE is green now and the cone slots in
-- later without re-plumbing.  This module adds NO chain premise (it is a LEAF,
-- imported by nothing; the chain premises stay `{wprog, pcone}`).
--
-- LIGHT: reuses the frozen `WalkCausal` √/terminal walk backbone
-- (`term-no-prod` / `noWeakVis-deadlock` / `sqrt-target-deadlock`) verbatim and
-- the LIGHT `PipeInv` phase logic; it does NOT itself pull the oracle cone
-- (only the emitter argument will).  No postulate/hole/meta.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤ )
import Data.Unit as U
open import Data.Nat using ( ℕ; zero; suc )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; trans; subst )

open import Process_Trees using ( PTree; ExtI; deadlock )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeExpose (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; Block₃ )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysReach blkA
  using ( NetProc; RState; radec; toSys )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysDecode blkA
  using ( initial )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkPr blkA
  using ( TwoLegs )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeInv blkA
  using ( PipeInv⁺; PipeStep⁺; pipeInv⁺-step; pipeInv⁺-init )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( Event; Event√; evl; √; ev )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_ )

open import Semantics.LTL.WTrace
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( WTrace; step; done; stuck; div; frameOf; IsTermᵂ
        ; drop; dropIdx; tail; tailIdx; dropIdx-stutter )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamondLiveness
  using ( producedA )

-- the frozen √/terminal walk backbone (WalkCausal, green)
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkCausal blkA
  using ( term-no-prod; noWeakVis-deadlock; sqrt-target-deadlock )

------------------------------------------------------------------------
-- `StepEmit l`: the per-step CLASSIFIER the forward exposure cone supplies.
-- One weak visible move is decoded to the reachable successor `r′`
-- (`t′ ≡ radec r′`) and its `PipeStep⁺ l (toSys r) (toSys r′)` transition
-- class.  (This is `WalkStepLift.liftReach-ev` STRENGTHENED with the
-- `PipeStep⁺` — the `WalkReachExpose.liftReach-ev-expose` `DReport` extended
-- to all seven leg-`l` components.)
------------------------------------------------------------------------

-- a per-leg forward step classifier
StepEmit : TwoLegs → Set₁
StepEmit l = (r : RState) {e : Event} {t′ : NetProc}
           → radec r ═[ ev (evl e) ]═► t′
           → Σ[ r′ ∈ RState ] (t′ ≡ radec r′) × PipeStep⁺ l (toSys r) (toSys r′)

module _ (b : Block₃) (l : TwoLegs) where

  ------------------------------------------------------------------------
  -- The engine, generalised over the start tree with a `t ≡ radec r`
  -- witness (mirror `WalkCausal.walkReach′`), threading `PipeInv⁺` across each
  -- classified visible step via `pipeInv⁺-step`.
  ------------------------------------------------------------------------

  -- fold `pipeInv⁺-step` along the walk to the `producedA` frame at position `n`
  pipeInv⁺-along-walk′ : StepEmit l → (r : RState) {t : NetProc} → t ≡ radec r
                       → PipeInv⁺ l (toSys r)
                       → (w : WTrace (⊤ {0ℓ}) t) (n : ℕ)
                       → producedA b (frameOf (drop n w))
                       → Σ[ r′ ∈ RState ] (dropIdx n w ≡ radec r′) × PipeInv⁺ l (toSys r′)
  pipeInv⁺-along-walk′ emit r eq pinv w zero pn = r , eq , pinv
  -- a visible `evl`-step: classify it, advance `PipeInv⁺`, recurse on the tail
  pipeInv⁺-along-walk′ emit r eq pinv (step {e = evl e0} wstep tr) (suc m) pn
    with emit r (subst (λ z → z ═[ ev (evl e0) ]═► _) eq wstep)
  ... | r₁ , eq₁ , ps =
        pipeInv⁺-along-walk′ emit r₁ eq₁
          (pipeInv⁺-step l (toSys r) (toSys r₁) ps pinv)
          (tail (step {e = evl e0} wstep tr)) m pn
  -- a `√`-step: the tail lives over `deadlock`, hence terminal ⇒ no `producedA`
  pipeInv⁺-along-walk′ emit r eq pinv (step {e = √ x} wstep tr) (suc m) pn =
    ⊥-elim (term-no-prod b (tail (step {e = √ x} wstep tr)) termTail m pn)
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
  -- terminal frames: `dropIdx` stutters back to the start index; `PipeInv⁺` kept
  pipeInv⁺-along-walk′ emit r eq pinv (done p eqr) (suc m) pn =
    r , trans (dropIdx-stutter (suc m) (done p eqr) U.tt) eq , pinv
  pipeInv⁺-along-walk′ emit r eq pinv (stuck p st) (suc m) pn =
    r , trans (dropIdx-stutter (suc m) (stuck p st) U.tt) eq , pinv
  pipeInv⁺-along-walk′ emit r eq pinv (div dv) (suc m) pn =
    r , trans (dropIdx-stutter (suc m) (div dv) U.tt) eq , pinv

  ------------------------------------------------------------------------
  -- `pipeInv⁺-along-walk` — headline: seeded at `initial` by `pipeInv⁺-init`,
  -- the walk delivers `PipeInv⁺ l (toSys r′)` at the located `producedA` frame.
  ------------------------------------------------------------------------

  -- from a reachable `r` at the initial state, thread `PipeInv⁺` to the frame
  pipeInv⁺-along-walk : StepEmit l → (r : RState) → toSys r ≡ initial
                      → (w : WTrace (⊤ {0ℓ}) (radec r)) (n : ℕ)
                      → producedA b (frameOf (drop n w))
                      → Σ[ r′ ∈ RState ] (dropIdx n w ≡ radec r′) × PipeInv⁺ l (toSys r′)
  pipeInv⁺-along-walk emit r ini w n pn =
    pipeInv⁺-along-walk′ emit r refl
      (subst (PipeInv⁺ l) (sym ini) (pipeInv⁺-init l)) w n pn
