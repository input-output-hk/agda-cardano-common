{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the STRICT-`<` VISIBLE-API MIDDLE (`Praos.WalkApiReach`).
--
-- `WalkStepLift.liftReach-ev` lifts a WEAK visible move `radec r ═[ ev e ]═► t′`
-- to a reachable successor `r′` with `t′ ≡ radec r′`, but it is MEASURE-BLIND
-- (its middle uses `theOracle .oevB`, whose successor `r′` is OPAQUE — `radec =
-- absDec ∘ toSys` is non-injective, so the `μTot` drop CANNOT be recovered from
-- it).  This module BUILDS the measure-carrying analogue of the STRONG middle
-- hop for the driver-advancing api class:
--
--   `reach-ev-μ` : a STRONG abstract api event `radec r ─[ ev (evl (evLabel X e
--   a)) ]─► M` (with `e` in the driver-advancing api class `IsApiCSBF`) lands on
--   a reachable `r′` with `M ≡ radec r′`, a concrete weak co-run `rdec r ═[ ev
--   ]═► rdec r′`, AND — the new content — `μTot (toSys r′) < μTot (toSys r)`.
--
-- It MIRRORS `SysBisim.oevB-api` VERBATIM, swapping the phase-only backward node
-- peel `SIL6.top-nodes-abs` for the driver-advance-carrying `WalkApiDrop.top-
-- nodes-abs-wt`, which returns the successor SysState `s′` ALONGSIDE the strict
-- `μTot s′ < μTot s`.  The reachable successor is built via `rcloseʷ`, so `toSys
-- r′ = s′` DEFINITIONALLY and the drop transfers with NO transport.
--
-- This is the strict-`<` visible MIDDLE of the `liftReach-ev-μ` sub-cone (the
-- deliver frontier piece (2)).  The two τ-paddings around it are `μTot`-NEUTRAL
-- (`liftτ*-μ`, still open — its hidden io-sync branch needs a driver-fixity
-- re-mirror of the io node cone).  HEAVY (pulls the `SysBisim`/`WalkApiDrop`
-- cone), 0-postulate.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Nat using ( _<_ )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( inj₁ )
open import Data.Empty using ( ⊥-elim )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; trans; cong₂; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Archive.WalkApiReach (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; apiES )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟ )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _∖_; _⦀_; EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_ )

-- the whole-system state, its medium/decode
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; med; nA; nB; nC; nD; ⟦_⟧ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( decMed )
-- the abstract/concrete decodes + the FORWARD visible-event top inversion
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
  using ( NetProc; absDec; absNodesOf; nodesOf
        ; TopEvR; medEv; nodesEv; reflect-top-ev )
-- reachable-config foundation (weak-run closure)
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( RState; radec; rdec; toSys; rcloseʷ; rcloseʷ-abs )
-- the abstract api-class fingerprint + api∉ioES + the medium api non-offer
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA
  using ( IsApiCSBF )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysRoute blkA as SR
-- the whole-system NODES weak-visible lift (medium fixed) + noOffer→viewV
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysBisim blkA
  using ( lift-nodes-whole-wev )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_GapBDisj blkA
  using ( noOffer→viewV )
-- the driver-advance-carrying backward node peel + the whole-trace measure
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkApiDrop blkA
  using ( top-nodes-abs-wt )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.Walk blkA
  using ( μTot )

------------------------------------------------------------------------
-- The strict-`<` visible-api middle: a driver-advancing api event of `radec r`
-- lands on a reachable `r′` with a strictly smaller `μTot`.
------------------------------------------------------------------------

reach-ev-μ : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′)
      × (rdec r ═[ ev (evl (evLabel X e a)) ]═► rdec r′)
      × (μTot (toSys r′) < μTot (toSys r))
reach-ev-μ r {X} {e} {a} aic apimem step
    with reflect-top-ev (decMed (med (toSys r))) (absNodesOf (toSys r))
           (inj₁ (SR.medium-api-non-offer (med (toSys r)) aic)) step
... | medEv M₁ ms _   = ⊥-elim (SR.medium-api-non-offer (med (toSys r)) aic (M₁ , ms))
... | nodesEv N₁ ns refl with top-nodes-abs-wt (toSys r) apimem ns
...   | s′ , medEq , N₁≡ , cWeakRun , drop = r′ , Mr , wr , drop
  where
    -- abstract target identification (mirror `oevB-api`'s `Meq′`)
    Meq′ : ((decMed (med (toSys r)) ∥⇘ ioES ⇙ N₁) ∖ ioES) ≡ absDec s′
    Meq′ = cong₂ (λ mm nn → (decMed mm ∥⇘ ioES ⇙ nn) ∖ ioES) medEq N₁≡
    -- concrete weak co-run into `⟦ s′ ⟧` (nodes solo, medium fixed)
    wrun : rdec r ═[ ev (evl (evLabel X e a)) ]═► ⟦ s′ ⟧
    wrun = subst (λ mm → rdec r ═[ ev (evl (evLabel X e a)) ]═►
                          ((decMed mm ∥⇘ ioES ⇙ nodesOf s′) ∖ ioES))
             medEq
             (lift-nodes-whole-wev (decMed (med (toSys r))) (nodesOf (toSys r))
               (SR.api∉ioES {X} {e} {a} aic)
               (noOffer→viewV _ (SR.medium-api-non-offer (med (toSys r)) aic))
               cWeakRun)
    -- the reachable successor (`toSys r′ = s′` DEFINITIONALLY via `rcloseʷ`)
    r′ : RState
    r′ = proj₁ (rcloseʷ r {s′ = s′} wrun)
    Mr : ((decMed (med (toSys r)) ∥⇘ ioES ⇙ N₁) ∖ ioES) ≡ radec r′
    Mr = trans Meq′ (sym (rcloseʷ-abs r {s′ = s′} wrun))
    wr : rdec r ═[ ev (evl (evLabel X e a)) ]═► rdec r′
    wr = subst (λ z → rdec r ═[ ev (evl (evLabel X e a)) ]═► z)
           (sym (proj₂ (rcloseʷ r {s′ = s′} wrun))) wrun
