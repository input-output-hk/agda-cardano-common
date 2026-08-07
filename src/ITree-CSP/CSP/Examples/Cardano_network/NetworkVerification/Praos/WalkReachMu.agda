{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the measure-carrying WEAK-visible move (`WalkReachMu`).
--
-- `liftReach-ev-μ` is the `μTot`-carrying analogue of `WalkStepLift.liftReach-ev`
-- for the driver-advancing api class: a WEAK visible api move `radec r ═[ ev
-- (evl (evLabel X e a)) ]═► t′` (`τ* · ev · τ*`, with `e` in `IsApiCSBF`) lands
-- on a reachable `r′` with `t′ ≡ radec r′` AND `μTot (toSys r′) < μTot (toSys r)`.
--
-- The strict `<` comes from the STRONG middle `WalkApiReach.reach-ev-μ`; the two
-- τ-paddings are `μTot`-NEUTRAL by `WalkTauMu.liftτ*-μ` (`≡`), so the net effect
-- is a strict decrease.  No postulate/hole/meta.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Nat using ( _<_ )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkReachMu (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; apiES )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟ )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[τ*]─►_; _═[_]═►_; wev )

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysReach blkA
  using ( NetProc; RState; radec; toSys )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle blkA
  using ( IsApiCSBF )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.Walk blkA
  using ( μTot )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkApiReach blkA
  using ( reach-ev-μ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkTauMu blkA
  using ( liftτ*-μ )

------------------------------------------------------------------------
-- A driver-advancing weak-visible api move lands on a reachable, strictly
-- lighter config.
------------------------------------------------------------------------

liftReach-ev-μ : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {t′ : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ═[ ev (evl (evLabel X e a)) ]═► t′
  → Σ[ r′ ∈ RState ] (t′ ≡ radec r′) × (μTot (toSys r′) < μTot (toSys r))
liftReach-ev-μ r {X} {e} {a} aic apimem (wev pre mid post) with liftτ*-μ r pre
... | r₁ , eq₁ , μ₁
    with reach-ev-μ r₁ aic apimem
           (subst (λ z → z ─[ ev (evl (evLabel X e a)) ]─► _) eq₁ mid)
...   | r₂ , eq₂ , _ , μ₂
      with liftτ*-μ r₂ (subst (λ z → z ─[τ*]─► _) eq₂ post)
...     | r′ , equ , μ₃ =
          r′ , equ ,
          subst (λ n → μTot (toSys r′) < n) μ₁
            (subst (λ n → n < μTot (toSys r₁)) (sym μ₃) μ₂)
