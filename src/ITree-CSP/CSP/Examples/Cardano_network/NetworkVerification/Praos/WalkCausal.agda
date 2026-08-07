{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the FORWARD REACHABILITY WALK (`Praos.WalkCausal`).
--
-- `WalkEngine.walkPosFrom`'s `locate` parameter needs, from a `WTrace` of
-- `abstractSystem` and a `producedA b` frame at position `n`, a REACHABLE
-- config `r0` with `dropIdx n tr ≡ radec r0`.  This module builds the
-- REACHABILITY half — the "reachability is FREE" claim, realised as an
-- `n`-fold `WalkStepLift.liftReach-ev` over the `WTrace` prefix:
--
--   `walkReach` : from a reachable `r` and a `WTrace` of `radec r`, the
--   `n`-step suffix index `dropIdx n w` is again a `radec r′` (reachable).
--
-- The induction is on `n` with a generalised start-equality (`t ≡ radec r`,
-- mirror of `WalkStepLift.liftτ*′`), so NO `subst` is needed on the trace
-- plumbing — `drop (suc m) w = drop m (tail w)` and `dropIdx (suc m) w =
-- dropIdx m (tail w)` hold DEFINITIONALLY.  The three frame classes:
--
--   · a VISIBLE `evl`-step  → lift the weak move with `liftReach-ev`, recurse
--     on the tail at the reachable successor;
--   · a TERMINAL frame (`done`/`stuck`/`div`) → `dropIdx` STUTTERS
--     (`dropIdx-stutter`), so the suffix index is `radec r` unchanged;
--   · a `√`-step → its weak target is `deadlock` (`sRet`), from which the
--     tail can only be TERMINAL, so a `producedA` frame is IMPOSSIBLE at any
--     later position (`term-no-prod`) — the `√`-branch is `⊥`-eliminated
--     using the `producedA` hypothesis it is fed.
--
-- LIGHT: pulls only `WalkStepLift.liftReach-ev` (which itself is the R2
-- oracle's reachability half) + the generic `WTrace`/`deadlock` vocabulary.
-- No postulate/hole/meta.  `wprog` is NOT used (this is the enabledness-free
-- reachability backbone).
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤ )
import Data.Unit as U
open import Data.Nat using ( ℕ; zero; suc )
open import Data.Product using ( Σ; Σ-syntax; _,_ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Function using ( case_of_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; trans; subst )

open import Process_Trees using ( PTree; ExtI; deadlock; ret; sil; react )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkCausal (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; Block₃ )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysReach blkA
  using ( NetProc; RState; radec )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkStepLift blkA
  using ( liftReach-ev )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( Event; Event√; evl; √; ev; Label; _─[_]─►_; sRet; sSil; sVis; sTau )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_; wev; _─[τ*]─►_; τ*-refl; τ*-step )
open import Semantics.Deadlock {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( IsStuck )

open import Semantics.LTL.WTrace
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( WTrace; step; done; stuck; div; frameOf; IsTermᵂ
        ; drop; dropIdx; tail; tailIdx; dropIdx-stutter )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamondLiveness
  using ( producedA )

------------------------------------------------------------------------
-- `deadlock` is stuck (rebuild of the stdlib `Deadlock.Sanity` witness,
-- which is `private`): no LTS label is enabled at `deadlock`.
------------------------------------------------------------------------

dl-stuck : IsStuck (deadlock {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} {R = ⊤ {0ℓ}})
dl-stuck (sRet eq)      = case eq of λ ()
dl-stuck (sSil eq)      = case eq of λ ()
dl-stuck (sVis refl br) = case br of λ ()
dl-stuck (sTau refl br) = case br of λ ()

------------------------------------------------------------------------
-- `deadlock` has no WEAK visible move: its τ*-prefix is forced empty (stuck),
-- and the strong middle hop is refuted by `dl-stuck`.
------------------------------------------------------------------------

noWeakVis-deadlock : {e : Event√ (⊤ {0ℓ})} {t : NetProc}
                   → deadlock ═[ ev e ]═► t → ⊥
noWeakVis-deadlock (wev τ*-refl       mid _) = dl-stuck mid
noWeakVis-deadlock (wev (τ*-step s _) _   _) = dl-stuck s

------------------------------------------------------------------------
-- A weak `√` move always targets `deadlock`: the `√` hop is `sRet` (→
-- `deadlock`), and `deadlock`'s trailing τ*-padding is forced empty.
------------------------------------------------------------------------

sqrt-target-deadlock : {t t′ : NetProc} {x : ⊤ {0ℓ}}
                     → t ═[ ev (√ x) ]═► t′ → t′ ≡ deadlock
sqrt-target-deadlock (wev _ (sRet _) τ*-refl)       = refl
sqrt-target-deadlock (wev _ (sRet _) (τ*-step s _))  = ⊥-elim (dl-stuck s)

module _ (b : Block₃) where

  ------------------------------------------------------------------------
  -- A TERMINAL `WTrace` never presents a `producedA` frame at ANY position:
  -- `drop` stutters on a terminal frame, so `frameOf (drop m w)` is again a
  -- `done`/`stuck`/`div` frame, on which `producedA b` denotes `⊥`.
  ------------------------------------------------------------------------

  term-no-prod : {t : NetProc} (w : WTrace (⊤ {0ℓ}) t) → IsTermᵂ w → (m : ℕ)
               → producedA b (frameOf (drop m w)) → ⊥
  term-no-prod (step _ _)      () _       _
  term-no-prod (done p eq)   _ zero    pr = pr
  term-no-prod (done p eq)   _ (suc m) pr = term-no-prod (done p eq)  U.tt m pr
  term-no-prod (stuck p st)  _ zero    pr = pr
  term-no-prod (stuck p st)  _ (suc m) pr = term-no-prod (stuck p st) U.tt m pr
  term-no-prod (div dv)      _ zero    pr = pr
  term-no-prod (div dv)      _ (suc m) pr = term-no-prod (div dv)     U.tt m pr

  ------------------------------------------------------------------------
  -- The reachability walk, generalised over the start tree with a
  -- `t ≡ radec r` witness (so the recursion argument is the tail unchanged,
  -- passing the termination check on `n`).
  ------------------------------------------------------------------------

  walkReach′ : (r : RState) {t : NetProc} → t ≡ radec r
             → (w : WTrace (⊤ {0ℓ}) t) (n : ℕ)
             → producedA b (frameOf (drop n w))
             → Σ[ r′ ∈ RState ] (dropIdx n w ≡ radec r′)
  walkReach′ r eq w zero pn = r , eq
  -- a visible `evl`-step: lift the weak move, recurse on the tail
  walkReach′ r eq (step {e = evl e0} wstep tr) (suc m) pn
    with liftReach-ev r (subst (λ z → z ═[ ev (evl e0) ]═► _) eq wstep)
  ... | r₁ , eq₁ = walkReach′ r₁ eq₁ (tail (step {e = evl e0} wstep tr)) m pn
  -- a `√`-step: the tail lives over `deadlock`, hence terminal ⇒ no `producedA`
  walkReach′ r eq (step {e = √ x} wstep tr) (suc m) pn =
    ⊥-elim (term-no-prod (tail (step {e = √ x} wstep tr)) termTail m pn)
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
  -- terminal frames: `dropIdx` stutters back to the start index
  walkReach′ r eq (done p eqr) (suc m) pn =
    r , trans (dropIdx-stutter (suc m) (done p eqr) U.tt) eq
  walkReach′ r eq (stuck p st) (suc m) pn =
    r , trans (dropIdx-stutter (suc m) (stuck p st) U.tt) eq
  walkReach′ r eq (div dv) (suc m) pn =
    r , trans (dropIdx-stutter (suc m) (div dv) U.tt) eq

  ------------------------------------------------------------------------
  -- `walkReach` — the headline: from a reachable `r`, a `WTrace` of `radec r`,
  -- and a `producedA b` frame at position `n`, the suffix index `dropIdx n w`
  -- is a reachable `radec r′`.
  ------------------------------------------------------------------------

  walkReach : (r : RState) (w : WTrace (⊤ {0ℓ}) (radec r)) (n : ℕ)
            → producedA b (frameOf (drop n w))
            → Σ[ r′ ∈ RState ] (dropIdx n w ≡ radec r′)
  walkReach r w n pn = walkReach′ r refl w n pn
