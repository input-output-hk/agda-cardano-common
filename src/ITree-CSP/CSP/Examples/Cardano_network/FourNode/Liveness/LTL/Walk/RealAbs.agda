{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — `realAbs : Realisableᴿ abstractSystem` (the R4 seam's
-- SOURCE-SIDE realisability, RISK-B) (`Praos.RealAbs`).
--
-- `⊨-DRWB-invariantᴿ→` transports `abstractSystem ⊨ᵂ φ` to
-- `systemBroken ⊨ᵂ φ` and needs `Realisableᴿ abstractSystem` on the SOURCE
-- side.  The record has two fields:
--
--   τprogᴿ : ∀ {s} → abstractSystem ↠ s → τ-progress s
--   convᴿ  : ∀ {s u} → abstractSystem ↠ s → DRbisim R u s → IsStuck u
--          → Converges s
--
-- BOTH quantify over states `s` REACHABLE (`↠`, τ+visible) from
-- `abstractSystem`.  This module discharges everything EXCEPT the abstract
-- τ-enabledness DECISION, isolating that single obligation as the module
-- premise `tprog`:
--
--   · REACHABILITY CLOSURE `↠-close`: every `abstractSystem ↠ s` lands on
--     either a reachable config decode `radec r′` (τ closed by `otauB`, non-√
--     visible by `oevB`) OR the terminal `deadlock` (a √ step targets
--     `deadlock`, after which the run stutters — `↠-from-stuck`).  Uses the
--     already-green oracle `SysBisim.theOracle`.
--   · `convᴿ`: `Converges (radec r′)` is built DIRECTLY from the τ-convergence
--     measure `WalkConvNoDiv.μτ` + reflector `τreflect` by well-founded
--     recursion (the POSITIVE form of `absNoDiv`); `Converges deadlock` is
--     `stuck⇒Converges`.  So `convᴿ` needs NO extra premise.
--   · `τprogᴿ`: at a `deadlock` frame it is `inj₂` (stuck ⇒ no τ); at a
--     reachable `radec r′` it is `tprog r′` — the ONE obligation neither
--     `absNoDiv` nor the τ-free `LivenessSpike` harvest supplies (the abstract
--     system is NOT τ-free — it has hidden io-sync + medium-drain τ's — so a
--     genuine FORWARD τ-enabledness decision is required; the τ-free instances
--     `τfreeᴿ→Realisableᴿ`/`τfree-Realisable` do not apply).
--
-- Given `tprog`, `realAbs` is green, 0-postulate/hole/meta.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Product using ( Σ; Σ-syntax; _,_; _×_ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Nat using ( _<_ )
open import Data.Nat.Induction using ( <-wellFounded )
open import Induction.WellFounded using ( Acc; acc )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; subst )

open import Process_Trees using ( PTree; ExtI; deadlock )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.RealAbs (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; τ; ev; evl; √; sRet; sSil; sVis; sTau )
open import Semantics.Deadlock {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( IsStuck )
open import Semantics.DRBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( DRbisim )
open import Semantics.LTL.Convergence {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( Converges; cvg; stuck⇒Converges; τ-progress; _↠_; ↠-refl; ↠-τ; ↠-ev )
open import Semantics.LTL.WBisimInvariantR {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( Realisableᴿ; τprogᴿ; convᴿ )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( NetProc; RState; radec; toSys; rinit; radec-init )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.AbstractSystem blkA
  using ( abstractSystem )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysBisim blkA
  using ( theOracle; otauB; oevB )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvMeasure blkA
  using ( μτ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvNoDiv blkA
  using ( τreflect )

------------------------------------------------------------------------
-- `deadlock` is stuck, and reachability cannot leave a stuck root.
------------------------------------------------------------------------

-- `deadlock` (the empty-offer react node) rejects EVERY LTS label
deadlock-stuck : IsStuck (deadlock {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} {R = ⊤ {0ℓ}})
deadlock-stuck (sRet ())
deadlock-stuck (sSil ())
deadlock-stuck (sVis refl ())
deadlock-stuck (sTau refl ())

-- from a stuck root, τ+visible reachability cannot leave the root
↠-from-stuck : {t s : NetProc} → IsStuck t → t ↠ s → s ≡ t
↠-from-stuck st ↠-refl     = refl
↠-from-stuck st (↠-τ  x _) = ⊥-elim (st x)
↠-from-stuck st (↠-ev x _) = ⊥-elim (st x)

------------------------------------------------------------------------
-- CONVERGENCE at every reachable config decode — the POSITIVE form of
-- `absNoDiv`, by well-founded recursion on the τ-convergence measure `μτ`.
------------------------------------------------------------------------

-- accessible form: with `μτ r` accessible, `radec r` converges.  The τ-step
-- reflector `τreflect` yields a strictly-smaller reachable successor, so the
-- recursion bottoms out on `<`-accessibility (the positive form of `absNoDiv`).
converges-acc  : (r : RState) → Acc _<_ (μτ r) → Converges (radec r)
converges-step : (r : RState) → Acc _<_ (μτ r)
               → {M : NetProc} → radec r ─[ τ ]─► M → Converges M

converges-acc r ac = cvg (converges-step r ac)
converges-step r (acc rec) tstep with τreflect r tstep
... | r′ , refl , lt = converges-acc r′ (rec lt)

-- `radec r` converges (τ-accessibility at every reachable config)
converges-radec : (r : RState) → Converges (radec r)
converges-radec r = converges-acc r (<-wellFounded (μτ r))

------------------------------------------------------------------------
-- REACHABILITY CLOSURE — every `radec r ↠ s` lands on a reachable config
-- decode OR the terminal `deadlock` (via a √ step).
------------------------------------------------------------------------

↠-close : (r : RState) {s : NetProc} → radec r ↠ s
        → (Σ[ r′ ∈ RState ] (s ≡ radec r′)) ⊎ (s ≡ deadlock)
↠-close r ↠-refl = inj₁ (r , refl)
-- a τ step: closed to a reachable config by the oracle `otauB`
↠-close r (↠-τ step rest) with theOracle .otauB r step
... | r′ , refl , _ = ↠-close r′ rest
-- a non-√ visible step: closed to a reachable config by the oracle `oevB`
↠-close r (↠-ev {l = evl e} step rest) with theOracle .oevB r step
... | r′ , refl , _ = ↠-close r′ rest
-- a √ step targets `deadlock`; the run then stutters (deadlock is stuck)
↠-close r (↠-ev {l = √ x} (sRet eqf) rest) =
  inj₂ (↠-from-stuck deadlock-stuck rest)

------------------------------------------------------------------------
-- `realAbs`, reduced to the SINGLE abstract-τ-enabledness DECISION `tprog`.
------------------------------------------------------------------------

module _ (tprog : (r : RState) → τ-progress (radec r)) where

  realAbs : Realisableᴿ abstractSystem
  τprogᴿ realAbs {s} reach with ↠-close rinit (subst (_↠ s) (sym radec-init) reach)
  ... | inj₁ (r′ , refl) = tprog r′
  ... | inj₂ refl        = inj₂ (λ st → deadlock-stuck st)
  convᴿ realAbs {s} reach _ _ with ↠-close rinit (subst (_↠ s) (sym radec-init) reach)
  ... | inj₁ (r′ , refl) = converges-radec r′
  ... | inj₂ refl        = stuck⇒Converges deadlock-stuck
