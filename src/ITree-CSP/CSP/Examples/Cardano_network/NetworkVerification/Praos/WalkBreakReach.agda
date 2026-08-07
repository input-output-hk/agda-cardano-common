{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the measure-carrying WEAK-visible BREAK move
-- (`Praos.WalkBreakReach`).
--
-- The break analogue of `WalkApiReach.reach-ev-μ` + `WalkReachMu.liftReach-ev-μ`.
-- A `break l` event fires a still-unbroken link, which the medium decode turns
-- into `Skip`; the four diamond NODES are UNTOUCHED (a break is a medium solo).
-- Hence the successor SysState `s′` KEEPS all four node fields LITERAL — so the
-- group measures `μG1`/`μG2` are FIXED (`refl`) and ONLY `breakBudget` drops
-- (`WalkBreakDrop.medium-break-drop`).  `μTot` therefore strictly decreases via
-- `Walk.μTot-break`.
--
--   `reach-break-μ` — the STRONG middle: `radec r ─[ ev (break l) ]─► M` lands
--   on a reachable `r′` (built via `rcloseʷ`, so `toSys r′ = s′` definitionally)
--   with `M ≡ radec r′`, a concrete co-run, AND `μTot (toSys r′) < μTot (toSys r)`.
--
--   `liftReach-break-μ` — the WEAK move: threads the `μTot`-neutral `liftτ*-μ`
--   paddings around the strict `<` middle (mirror `liftReach-ev-μ`).
--
-- MIRRORS `SysBisim.oevB-break` VERBATIM for the reconstruction, swapping the
-- frozen `medium-break-ev-inv` for `medium-break-drop` (same `m′`, plus the
-- strict `breakBudget` drop).  HEAVY (pulls the `SysStep`/`SysRoute` cone),
-- 0-postulate.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit using () renaming ( ⊤ to ⊤₀ )
open import Data.Nat using ( _<_ )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( inj₂ )
open import Data.Empty using ( ⊥-elim )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; trans; cong; cong₂; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkBreakReach (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
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

-- the whole-system state, its medium/decode
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysDecode blkA
  using ( SysState; mkSys; med; nA; nB; nC; nD; ⟦_⟧ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysMedium blkA
  using ( decMed; MedState )
-- the abstract/concrete decodes + the FORWARD visible-event top inversion
-- + the medium-solo whole-system lift
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep blkA
  using ( NetProc; absDec; absNodesOf; nodesOf
        ; TopEvR; medEv; nodesEv; reflect-top-ev; lift-med-whole-ev )
-- reachable-config foundation (weak-run closure)
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysReach blkA
  using ( RState; radec; rdec; toSys; rcloseʷ; rcloseʷ-abs )
-- the nodes-refuse-break facts + break∉ioES
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysRoute blkA as SR
-- noOffer→viewV (the viewV-nothing for the medium-solo lift)
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_GapBDisj blkA
  using ( noOffer→viewV )
-- the medium break-budget DROP inversion
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkBreakDrop blkA
  using ( medium-break-drop )
-- the whole-trace measure + its break-class strict decrease
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.Walk blkA
  using ( μTot; μTot-break )
-- the τ-neutral measure-carrying padding
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkTauMu blkA
  using ( liftτ*-μ )

------------------------------------------------------------------------
-- The strict-`<` visible-break middle: a break event of `radec r` lands on a
-- reachable `r′` with a strictly smaller `μTot` (only `breakBudget` drops).
------------------------------------------------------------------------

reach-break-μ : (r : RState) (l : Link) {a : ⊤₀} {M : NetProc}
  → radec r ─[ ev (evl (evLabel ⊤₀ (break l) a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′)
      × (rdec r ═[ ev (evl (evLabel ⊤₀ (break l) a)) ]═► rdec r′)
      × (μTot (toSys r′) < μTot (toSys r))
reach-break-μ r l {a} {M} step
    with reflect-top-ev (decMed (med (toSys r))) (absNodesOf (toSys r))
           (inj₂ (SR.absnodes-no-break (toSys r))) step
... | nodesEv N₁ ns _ = ⊥-elim (SR.absnodes-no-break (toSys r) (N₁ , ns))
... | medEv M₁ medStep Meq0 with medium-break-drop (med (toSys r)) l medStep
...   | m′ , M₁≡ , drop = r′ , Mr , wr , drop′
  where
    -- successor SysState: only the medium changes; the four nodes are LITERAL
    s′ : SysState
    s′ = mkSys m′ (nA (toSys r)) (nB (toSys r)) (nC (toSys r)) (nD (toSys r))
    -- abstract target identification (mirror `oevB-break`'s `Meq′`)
    Meq′ : M ≡ absDec s′
    Meq′ = trans Meq0
             (cong₂ (λ mm nn → (mm ∥⇘ ioES ⇙ nn) ∖ ioES) M₁≡ refl)
    -- concrete medium-solo weak co-run into `⟦ s′ ⟧`
    wrun : rdec r ═[ ev (evl (evLabel ⊤₀ (break l) a)) ]═► ⟦ s′ ⟧
    wrun = subst (λ mm → rdec r ═[ ev (evl (evLabel ⊤₀ (break l) a)) ]═►
                          ((mm ∥⇘ ioES ⇙ nodesOf s′) ∖ ioES))
             M₁≡
             (wev τ*-refl
               (lift-med-whole-ev (decMed (med (toSys r))) (nodesOf (toSys r))
                 (SR.break∉ioES {l} {a}) medStep
                 (noOffer→viewV _ (SR.nodes-no-break (toSys r))))
               τ*-refl)
    -- the reachable successor (`toSys r′ = s′` DEFINITIONALLY via `rcloseʷ`)
    r′ : RState
    r′ = proj₁ (rcloseʷ r {s′ = s′} wrun)
    Mr : M ≡ radec r′
    Mr = trans Meq′ (sym (rcloseʷ-abs r {s′ = s′} wrun))
    wr : rdec r ═[ ev (evl (evLabel ⊤₀ (break l) a)) ]═► rdec r′
    wr = subst (λ z → rdec r ═[ ev (evl (evLabel ⊤₀ (break l) a)) ]═► z)
           (sym (proj₂ (rcloseʷ r {s′ = s′} wrun))) wrun
    -- the strict `μTot` drop: nodes fixed ⇒ μG1/μG2 `refl`; breakBudget drops
    drop′ : μTot (toSys r′) < μTot (toSys r)
    drop′ = μTot-break (toSys r) s′ refl refl drop

------------------------------------------------------------------------
-- A break weak-visible move lands on a reachable, strictly lighter config.
------------------------------------------------------------------------

liftReach-break-μ : (r : RState) (l : Link) {a : ⊤₀} {t′ : NetProc}
  → radec r ═[ ev (evl (evLabel ⊤₀ (break l) a)) ]═► t′
  → Σ[ r′ ∈ RState ] (t′ ≡ radec r′) × (μTot (toSys r′) < μTot (toSys r))
liftReach-break-μ r l {a} (wev pre mid post) with liftτ*-μ r pre
... | r₁ , eq₁ , μ₁
    with reach-break-μ r₁ l
           (subst (λ z → z ─[ ev (evl (evLabel ⊤₀ (break l) a)) ]─► _) eq₁ mid)
...   | r₂ , eq₂ , _ , μ₂
      with liftτ*-μ r₂ (subst (λ z → z ─[τ*]─► _) eq₂ post)
...     | r′ , equ , μ₃ =
          r′ , equ ,
          subst (λ n → μTot (toSys r′) < n) μ₁
            (subst (λ n → n < μTot (toSys r₁)) (sym μ₃) μ₂)
