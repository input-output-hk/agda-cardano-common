{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — measure-carrying weak moves WITH the D-PHASE REPORT
-- (`Praos.WalkReachExpose`).
--
-- `liftReach-ev-μ` / `liftReach-break-μ` supply `deliver`'s two visible
-- successor classes with `μTot ↓`, but DISCARD how nD's D-consume phases
-- relate in the successor — the Pr-preservation content.  This module threads
-- the `WalkDExpose.DReport` alongside:
--
--   `reach-ev-expose`     — the strong api middle + `DReport (toSys r)(toSys r′)`
--                           (swap `top-nodes-abs-wt` → `top-nodes-abs-expose`);
--   `liftReach-ev-expose` — the weak api move: `DReport` of the strong middle,
--                           transported across the two `μTot`-neutral
--                           D-phase-FIXED τ-paddings (`WalkTauExpose.liftτ*-expose`);
--   `liftReach-break-expose` — the weak break move: nodes are literal ⇒ the
--                           report is always `dFix` (both consume phases fixed).
--
-- No postulate/hole/meta.  All base modules stay READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit using () renaming ( ⊤ to ⊤₀ )
open import Data.Nat using ( _<_ )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( inj₁; inj₂ )
open import Data.Empty using ( ⊥-elim )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; trans; cong; cong₂; subst; subst₂ )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkReachExpose (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; apiES )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟; Link; break )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _∖_; _⦀_; EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[τ*]─►_; _═[_]═►_; wev; τ*-refl )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; mkSys; med; nA; nB; nC; nD; ⟦_⟧ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( decMed )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
  using ( NetProc; absDec; absNodesOf; nodesOf
        ; TopEvR; medEv; nodesEv; reflect-top-ev; lift-med-whole-ev )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( RState; radec; rdec; toSys; rcloseʷ; rcloseʷ-abs )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA
  using ( IsApiCSBF )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysRoute blkA as SR
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysBisim blkA
  using ( lift-nodes-whole-wev )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_GapBDisj blkA
  using ( noOffer→viewV )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.Walk blkA
  using ( μTot; μTot-break )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkBreakDrop blkA
  using ( medium-break-drop )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkBreakReach blkA
  using ( reach-break-μ )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN
  using ( cph; cblk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkMeasure blkA
  using ( ConsAdv )

-- the exposure cone (strong ev step + DReport) and the τ-run D-phase fixity
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkDExpose blkA
  using ( DReport; dFix; dBD; dCD; top-nodes-abs-expose )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkTauExpose blkA
  using ( DFix; BD; CD; liftτ*-expose )

------------------------------------------------------------------------
-- Compose a D-phase-fixed τ-pre, a strong-middle `DReport`, and a
-- D-phase-fixed τ-post into one `DReport (toSys r)(toSys r′)`.
------------------------------------------------------------------------

-- `DFix s s₁ = (BD s₁ ≡ BD s) × (CD s₁ ≡ CD s)` (WalkTauExpose), so `pre`
-- carries `BD s₁ ≡ BD s` and `post` carries `BD s′ ≡ BD s₂`.
compose-DReport : (s s₁ s₂ s′ : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → DFix s s₁ → DReport s₁ s₂ e a → DFix s₂ s′ → DReport s s′ e a
compose-DReport s s₁ s₂ s′ (bpre , cpre) (dFix bmid cmid) (bpost , cpost) =
  dFix (trans bpost (trans bmid bpre)) (trans cpost (trans cmid cpre))
compose-DReport s s₁ s₂ s′ (bpre , cpre) (dBD adv cmid lblmid) (bpost , cpost) =
  -- the fired event is fixed across the τ-paddings, so the middle's label id
  -- carries through; the cp3-trigger is transported from `s` back to `s₁` via `bpre`
  dBD (subst₂ ConsAdv (cong cph bpre) (cong cph (sym bpost)) adv)
      (trans cpost (trans cmid cpre))
      -- SESSION-36: the anchor rides the τ-post fixity — `bpost` says `s′`'s BD
      -- slot IS `s₂`'s, so the middle's recorded block is `s′`'s recorded block
      (λ hcp → let (b″ , lbl , anc) = lblmid (trans (cong cph bpre) hcp)
               in  b″ , lbl , trans (cong cblk bpost) anc)
compose-DReport s s₁ s₂ s′ (bpre , cpre) (dCD adv bmid lblmid) (bpost , cpost) =
  dCD (subst₂ ConsAdv (cong cph cpre) (cong cph (sym cpost)) adv)
      (trans bpost (trans bmid bpre))
      -- SESSION-36 anchor transport (mirror)
      (λ hcp → let (b″ , lbl , anc) = lblmid (trans (cong cph cpre) hcp)
               in  b″ , lbl , trans (cong cblk cpost) anc)

------------------------------------------------------------------------
-- The strong-`<` visible-api middle WITH the `DReport` (mirror
-- `WalkApiReach.reach-ev-μ`, swapping `top-nodes-abs-wt` → the exposure cone).
------------------------------------------------------------------------

reach-ev-expose : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′)
      × (rdec r ═[ ev (evl (evLabel X e a)) ]═► rdec r′)
      × (μTot (toSys r′) < μTot (toSys r)) × DReport (toSys r) (toSys r′) e a
reach-ev-expose r {X} {e} {a} aic apimem step
    with reflect-top-ev (decMed (med (toSys r))) (absNodesOf (toSys r))
           (inj₁ (SR.medium-api-non-offer (med (toSys r)) aic)) step
... | medEv M₁ ms _   = ⊥-elim (SR.medium-api-non-offer (med (toSys r)) aic (M₁ , ms))
... | nodesEv N₁ ns refl with top-nodes-abs-expose (toSys r) apimem ns
...   | s′ , medEq , N₁≡ , cWeakRun , drop , drep = r′ , Mr , wr , drop , drep
  where
    Meq′ : ((decMed (med (toSys r)) ∥⇘ ioES ⇙ N₁) ∖ ioES) ≡ absDec s′
    Meq′ = cong₂ (λ mm nn → (decMed mm ∥⇘ ioES ⇙ nn) ∖ ioES) medEq N₁≡
    wrun : rdec r ═[ ev (evl (evLabel X e a)) ]═► ⟦ s′ ⟧
    wrun = subst (λ mm → rdec r ═[ ev (evl (evLabel X e a)) ]═►
                          ((decMed mm ∥⇘ ioES ⇙ nodesOf s′) ∖ ioES))
             medEq
             (lift-nodes-whole-wev (decMed (med (toSys r))) (nodesOf (toSys r))
               (SR.api∉ioES {X} {e} {a} aic)
               (noOffer→viewV _ (SR.medium-api-non-offer (med (toSys r)) aic))
               cWeakRun)
    r′ : RState
    r′ = proj₁ (rcloseʷ r {s′ = s′} wrun)
    Mr : ((decMed (med (toSys r)) ∥⇘ ioES ⇙ N₁) ∖ ioES) ≡ radec r′
    Mr = trans Meq′ (sym (rcloseʷ-abs r {s′ = s′} wrun))
    wr : rdec r ═[ ev (evl (evLabel X e a)) ]═► rdec r′
    wr = subst (λ z → rdec r ═[ ev (evl (evLabel X e a)) ]═► z)
           (sym (proj₂ (rcloseʷ r {s′ = s′} wrun))) wrun

------------------------------------------------------------------------
-- The weak api move WITH the `DReport` (mirror `WalkReachMu.liftReach-ev-μ`,
-- composing the two `liftτ*-expose` D-phase fixities around the middle).
------------------------------------------------------------------------

liftReach-ev-expose : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {t′ : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ═[ ev (evl (evLabel X e a)) ]═► t′
  → Σ[ r′ ∈ RState ] (t′ ≡ radec r′) × (μTot (toSys r′) < μTot (toSys r)) × DReport (toSys r) (toSys r′) e a
liftReach-ev-expose r {X} {e} {a} aic apimem (wev pre mid post) with liftτ*-expose r pre
... | r₁ , eq₁ , μ₁ , fix₁
    with reach-ev-expose r₁ aic apimem
           (subst (λ z → z ─[ ev (evl (evLabel X e a)) ]─► _) eq₁ mid)
...   | r₂ , eq₂ , _ , μ₂ , drep
      with liftτ*-expose r₂ (subst (λ z → z ─[τ*]─► _) eq₂ post)
...     | r′ , equ , μ₃ , fix₃ =
          r′ , equ ,
          subst (λ n → μTot (toSys r′) < n) μ₁
            (subst (λ n → n < μTot (toSys r₁)) (sym μ₃) μ₂) ,
          compose-DReport (toSys r) (toSys r₁) (toSys r₂) (toSys r′) fix₁ drep fix₃

------------------------------------------------------------------------
-- The strong break middle WITH the `DReport` (always `dFix`): break is a
-- medium solo, so the successor `s′` keeps all four node fields LITERAL — the
-- `dFix refl refl` reduces INSIDE this scope (`toSys r′ = s′` definitionally).
-- MIRRORS `WalkBreakReach.reach-break-μ` VERBATIM + the report.
------------------------------------------------------------------------

reach-break-expose : (r : RState) (l : Link) {a : ⊤₀} {M : NetProc}
  → radec r ─[ ev (evl (evLabel ⊤₀ (break l) a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′)
      × (rdec r ═[ ev (evl (evLabel ⊤₀ (break l) a)) ]═► rdec r′)
      × (μTot (toSys r′) < μTot (toSys r)) × DReport (toSys r) (toSys r′) (break l) a
reach-break-expose r l {a} {M} step
    with reflect-top-ev (decMed (med (toSys r))) (absNodesOf (toSys r))
           (inj₂ (SR.absnodes-no-break (toSys r))) step
... | nodesEv N₁ ns _ = ⊥-elim (SR.absnodes-no-break (toSys r) (N₁ , ns))
... | medEv M₁ medStep Meq0 with medium-break-drop (med (toSys r)) l medStep
...   | m′ , M₁≡ , drop = r′ , Mr , wr , drop′ , dFix refl refl
  where
    s′ : SysState
    s′ = mkSys m′ (nA (toSys r)) (nB (toSys r)) (nC (toSys r)) (nD (toSys r))
    Meq′ : M ≡ absDec s′
    Meq′ = trans Meq0 (cong₂ (λ mm nn → (mm ∥⇘ ioES ⇙ nn) ∖ ioES) M₁≡ refl)
    wrun : rdec r ═[ ev (evl (evLabel ⊤₀ (break l) a)) ]═► ⟦ s′ ⟧
    wrun = subst (λ mm → rdec r ═[ ev (evl (evLabel ⊤₀ (break l) a)) ]═►
                          ((mm ∥⇘ ioES ⇙ nodesOf s′) ∖ ioES))
             M₁≡
             (wev τ*-refl
               (lift-med-whole-ev (decMed (med (toSys r))) (nodesOf (toSys r))
                 (SR.break∉ioES {l} {a}) medStep
                 (noOffer→viewV _ (SR.nodes-no-break (toSys r))))
               τ*-refl)
    r′ : RState
    r′ = proj₁ (rcloseʷ r {s′ = s′} wrun)
    Mr : M ≡ radec r′
    Mr = trans Meq′ (sym (rcloseʷ-abs r {s′ = s′} wrun))
    wr : rdec r ═[ ev (evl (evLabel ⊤₀ (break l) a)) ]═► rdec r′
    wr = subst (λ z → rdec r ═[ ev (evl (evLabel ⊤₀ (break l) a)) ]═► z)
           (sym (proj₂ (rcloseʷ r {s′ = s′} wrun))) wrun
    drop′ : μTot (toSys r′) < μTot (toSys r)
    drop′ = μTot-break (toSys r) s′ refl refl drop

------------------------------------------------------------------------
-- The weak break move WITH the `DReport` (mirror `liftReach-break-μ`).
------------------------------------------------------------------------

liftReach-break-expose : (r : RState) (l : Link) {a : ⊤₀} {t′ : NetProc}
  → radec r ═[ ev (evl (evLabel ⊤₀ (break l) a)) ]═► t′
  → Σ[ r′ ∈ RState ] (t′ ≡ radec r′) × (μTot (toSys r′) < μTot (toSys r)) × DReport (toSys r) (toSys r′) (break l) a
liftReach-break-expose r l {a} (wev pre mid post) with liftτ*-expose r pre
... | r₁ , eq₁ , μ₁ , fix₁
    with reach-break-expose r₁ l
           (subst (λ z → z ─[ ev (evl (evLabel ⊤₀ (break l) a)) ]─► _) eq₁ mid)
...   | r₂ , eq₂ , _ , μ₂ , drep
      with liftτ*-expose r₂ (subst (λ z → z ─[τ*]─► _) eq₂ post)
...     | r′ , equ , μ₃ , fix₃ =
          r′ , equ ,
          subst (λ n → μTot (toSys r′) < n) μ₁
            (subst (λ n → n < μTot (toSys r₁)) (sym μ₃) μ₂) ,
          compose-DReport (toSys r) (toSys r₁) (toSys r₂) (toSys r′) fix₁ drep fix₃
