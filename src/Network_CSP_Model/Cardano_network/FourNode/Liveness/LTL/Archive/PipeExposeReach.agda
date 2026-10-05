{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the VISIBLE-MIDDLE cell frame
-- (`Praos.PipeExposeReach`).
--
-- `PipeExposeCell.liftτ*-cell` exposes the leg-`l` medium cells' deltas across
-- a hidden τ-run.  The strong VISIBLE api-CSBF middle of a weak move needs the
-- complementary fact: how the cells move across that visible hop.  An api-CSBF
-- event is a NODE hand-off (`apiES`, `api∉ioES`), so the medium is a SOLO
-- pass-through — `top-nodes-abs-expose` returns `med s ≡ med s′`, hence EVERY
-- cell is FIXED (`allCellAdv-medEq`, which transports `ca-refl` along the
-- medium equality).
--
-- `reach-ev-both` RE-MIRRORS `WalkReachExpose.reach-ev-expose` (same api cone,
-- reusing the four node peels through `top-nodes-abs-expose`) and returns BOTH
-- the nodeD `DReport` AND the whole-medium `AllCellAdv` on the SAME reflected
-- `r′` — so the combined `PipeReport` can ride one successor.  `reach-ev-cell`
-- projects out the cell half (the plan's headline for this piece).
--
-- No postulate/hole/meta.  All base modules stay READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Nat using ( _<_ )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( inj₁ )
open import Data.Empty using ( ⊥-elim )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; cong₂; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Archive.PipeExposeReach (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; apiES )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟; Link )
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
  using ( CopyPhase; MedState; phase; decMed )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
  using ( NetProc; absDec; absNodesOf; nodesOf
        ; medEv; nodesEv; reflect-top-ev; lift-med-whole-ev )
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
  using ( μTot )

-- the nodeD D-phase report (visible middle) + the cell algebra (whole medium)
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkDExpose blkA
  using ( DReport; top-nodes-abs-expose )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Archive.PipeExposeCell blkA
  using ( CellAdv; ca-refl; AllCellAdv; cellAt; CellReport; allCellAdv⇒CellReport )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs )

------------------------------------------------------------------------
-- Transport `AllCellAdv` along a medium equality: if `med s ≡ med s′` then
-- every cell is unchanged (`ca-refl` transported by the equality).
------------------------------------------------------------------------

-- a medium-fixed step keeps every cell (the visible-api-middle frame case)
allCellAdv-medEq : (s s′ : SysState) → med s ≡ med s′ → AllCellAdv s s′
allCellAdv-medEq s s′ meq kl kd kid =
  subst (λ m → CellAdv (phase (med s) kl kd kid) (phase m kl kd kid)) meq ca-refl

------------------------------------------------------------------------
-- The strong-visible api middle WITH BOTH reports on one `r′` (mirror
-- `WalkReachExpose.reach-ev-expose`, additionally exposing the medium fixity as
-- a whole-medium `AllCellAdv`).
------------------------------------------------------------------------

reach-ev-both : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′)
      × (rdec r ═[ ev (evl (evLabel X e a)) ]═► rdec r′)
      × (μTot (toSys r′) < μTot (toSys r))
      × DReport (toSys r) (toSys r′) e a × AllCellAdv (toSys r) (toSys r′)
reach-ev-both r {X} {e} {a} aic apimem step
    with reflect-top-ev (decMed (med (toSys r))) (absNodesOf (toSys r))
           (inj₁ (SR.medium-api-non-offer (med (toSys r)) aic)) step
... | medEv M₁ ms _   = ⊥-elim (SR.medium-api-non-offer (med (toSys r)) aic (M₁ , ms))
... | nodesEv N₁ ns refl with top-nodes-abs-expose (toSys r) apimem ns
...   | s′ , medEq , N₁≡ , cWeakRun , drop , drep =
        r′ , Mr , wr , drop , drep , allCellAdv-medEq (toSys r) s′ medEq
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
-- `reach-ev-cell`: the cell half of the visible middle (the plan's headline).
------------------------------------------------------------------------

reach-ev-cell : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′)
      × (rdec r ═[ ev (evl (evLabel X e a)) ]═► rdec r′)
      × (μTot (toSys r′) < μTot (toSys r)) × AllCellAdv (toSys r) (toSys r′)
reach-ev-cell r aic apimem step with reach-ev-both r aic apimem step
... | r′ , Mr , wr , drop , _ , acr = r′ , Mr , wr , drop , acr

-- the leg-`l` projection of the visible-middle cell frame (both cells fixed)
reach-ev-cellReport : (l : TwoLegs) (r : RState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′)
      × (rdec r ═[ ev (evl (evLabel X e a)) ]═► rdec r′)
      × (μTot (toSys r′) < μTot (toSys r)) × CellReport l (toSys r) (toSys r′)
-- NB `let`-destructuring, NOT `with`: since this module became `(blkA : Block₃)`-
-- parameterised, a `with` here abstracts the block out of the imported
-- `PipeExposeCell.cellUp`/`cellDn` copies, and the abstracted goal then no
-- longer converts ("one is a variable and one a defined identifier").
reach-ev-cellReport l r aic apimem step =
  let (r′ , Mr , wr , drop , acr) = reach-ev-cell r aic apimem step
  in  r′ , Mr , wr , drop , allCellAdv⇒CellReport l (toSys r) (toSys r′) acr
