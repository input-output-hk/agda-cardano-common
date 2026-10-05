{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 (SESSION-34, `wprog` discharge) — the `broken`-flag
-- carrying step LIFTS (`Praos.WalkBrkLift`).
--
-- Mirrors `WalkTauExpose` (the τ arms) and `WalkReachExpose` (the api and
-- break arms), but instead of the D-phase `DFix`/`DReport` each lift
-- carries the medium's per-link BREAK-FLAG evolution:
--
--   · `liftτ*-brk`          — a hidden τ-run FIXES every `broken` flag
--     (`BrkFix`): the drain arm keeps `broken` literal, the io-sync arm
--     rebuilds the medium via `medium-ev-inv-wt`'s literal
--     `mkMed … (broken m)` successor.
--   · `liftReach-ev-brk`    — a weak api/done move fixes every flag
--     (api events are nodes-solo: `top-nodes-abs-expose`'s `medEq`).
--   · `liftReach-break-brk` — a weak `break l` move flips ONLY link `l`
--     (`BrkUpd l`): the frozen `link-break-chan` PINS the peeled `⦀Fin`
--     position to `l` (the pin `medium-break-drop` erases), and
--     `bupd-miss` fixes every other flag.
--
-- These lifts construct their OWN reachable successors; consumers relate
-- them to the walk's successors by decode equality via
-- `WalkBrkFire.unb-transport` (the `broken` flag is decode-transportable).
--
-- No postulate/hole/meta; no `dne`.  All base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit using () renaming ( ⊤ to ⊤₀ )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( inj₁; inj₂ )
open import Data.Empty using ( ⊥-elim )
open import Relation.Binary.PropositionalEquality using ( _≡_; _≢_; refl; sym; trans; cong; cong₂; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkBrkLift (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; apiES )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟; Link; break )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( numLinks )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _∖_; ⦀Fin; Skip; EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; τ; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wev; wτ )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; mkSys; med; nA; nB; nC; nD; ⟦_⟧ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( MedState; mkMed; phase; broken; decMed; decLink )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
  using ( absDec; absNodesOf; nodesOf; lift-med-whole-τ; lift-med-whole-ev
        ; ReflOut; innerτ; hidSync; reflect-absDec-τ
        ; InnerτR; medτ; nodesτ; reflect-inner-τ
        ; TopEvR; medEv; nodesEv; reflect-top-ev )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( absNodesOf-no-τ; setCell; ⦀Fin-ev-inv )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysBisim blkA
  using ( lift-io-sync-whole-wτ; lift-nodes-whole-wev )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA
  using ( IsApiCSBF )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_GapBDisj blkA
  using ( noOffer→viewV )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( NetProc; RState; mkR; radec; toSys; rdec; reach; Reachable
        ; rcloseʷ; rcloseʷ-abs )
open Reachable using ( rStepʷ )

open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvEvInv blkA
  using ( medium-ev-inv-wt )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvTauInv blkA
  using ( medium-τ-inv-wt )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_TauCore blkA as STC
open STC using ( phase-upd; flipCell; finUpd )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvNodeFix blkA
  using ( top-nodes-io-abs-fix )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkDExpose blkA
  using ( top-nodes-abs-expose )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysRoute blkA as SR
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkBreakDrop blkA
  using ( bupd-miss )

------------------------------------------------------------------------
-- The two evolution reports.
------------------------------------------------------------------------

-- every per-link break flag is FIXED across the move
BrkFix : SysState → SysState → Set
BrkFix s s′ = ∀ (l : Link) → broken (med s′) l ≡ broken (med s) l

-- a `break l` move: every OTHER link's flag is fixed
BrkUpd : Link → SysState → SysState → Set
BrkUpd l s s′ = ∀ (j : Link) → j ≢ l → broken (med s′) j ≡ broken (med s) j

------------------------------------------------------------------------
-- MEDIUM-τ reflector: the drain successor keeps `broken` LITERAL.
------------------------------------------------------------------------

-- mirror `WalkTauExpose.τreflect-med-expose`, reporting the flag fixity
τbrk-med : (r : RState) {M M′ : NetProc}
    (ms  : decMed (med (toSys r)) ─[ τ ]─► M′)
    (Meq : M ≡ ((M′ ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × BrkFix (toSys r) (toSys r′)
τbrk-med r {M} {M′} ms Meq with medium-τ-inv-wt (med (toSys r)) ms
... | i , d₀ , id₀ , x , drainEq , M′≡ = r′ , Meq′ , (λ _ → refl)
  where
    m′ : MedState
    m′ = mkMed (phase-upd (phase (med (toSys r))) i (flipCell (phase (med (toSys r)) i) d₀ id₀))
               (broken (med (toSys r)))
    s′ : SysState
    s′ = mkSys m′ (nA (toSys r)) (nB (toSys r)) (nC (toSys r)) (nD (toSys r))
    wrun : rdec r ═[ τ ]═► ⟦ s′ ⟧
    wrun = wτ (τ*-step
             (lift-med-whole-τ (decMed (med (toSys r))) (nodesOf (toSys r))
               (subst (λ z → decMed (med (toSys r)) ─[ τ ]─► z) M′≡ ms))
             τ*-refl)
    r′ : RState
    r′ = mkR s′ (rStepʷ (reach r) wrun)
    Meq′ : M ≡ radec r′
    Meq′ = trans Meq (cong (λ z → (z ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES) M′≡)

------------------------------------------------------------------------
-- io-SYNC reflector: rebuild the medium successor OURSELVES from
-- `medium-ev-inv-wt`, so `broken` stays literal (`WalkTauMu`'s
-- `medium-ev-inv-brk` proves exactly this shape but returns `m′` opaquely).
------------------------------------------------------------------------

-- mirror `WalkTauExpose.τreflect-io-expose` at the flag fixity
τbrk-io : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M₁ N₁ M : NetProc}
    (iomem : ioES .mem (X , e) a)
    (sM : decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► M₁)
    (sN : absNodesOf (toSys r)   ─[ ev (evl (evLabel X e a)) ]─► N₁)
    (Meq : M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × BrkFix (toSys r) (toSys r′)
τbrk-io r {X} {e} {a} {M₁} {N₁} {M} iomem sM sN Meq
    with medium-ev-inv-wt (med (toSys r)) iomem sM
       | top-nodes-io-abs-fix (toSys r) iomem sN
... | i , d₀ , id₀ , np , riseEq , M₁≡ | s″ , medEq , N₁≡ , cWeakRun , _ , _ , _ , _ , _ , _ =
      r′ , Meq′ , (λ _ → refl)
  where
    m′ : MedState
    m′ = mkMed (phase-upd (phase (med (toSys r))) i (setCell (phase (med (toSys r)) i) d₀ id₀ np))
               (broken (med (toSys r)))
    s′ : SysState
    s′ = mkSys m′ (nA s″) (nB s″) (nC s″) (nD s″)
    medWeak : decMed (med (toSys r)) ═[ ev (evl (evLabel X e a)) ]═► decMed m′
    medWeak = wev τ*-refl
                (subst (λ z → decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► z) M₁≡ sM)
                τ*-refl
    wrun : rdec r ═[ τ ]═► ⟦ s′ ⟧
    wrun = lift-io-sync-whole-wτ (decMed (med (toSys r))) (nodesOf (toSys r)) iomem medWeak cWeakRun
    r′ : RState
    r′ = mkR s′ (rStepʷ (reach r) wrun)
    Meq′ : M ≡ radec r′
    Meq′ = trans Meq (cong₂ (λ mm nn → (mm ∥⇘ ioES ⇙ nn) ∖ ioES) M₁≡ N₁≡)

------------------------------------------------------------------------
-- TOTAL per-τ reflector and the τ*-fold (mirror `τreflect-expose` /
-- `liftτ*-expose`).
------------------------------------------------------------------------

-- one hidden τ fixes every break flag
τbrk : (r : RState) {M : NetProc} → radec r ─[ τ ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × BrkFix (toSys r) (toSys r′)
τbrk r step with reflect-absDec-τ (toSys r) step
... | innerτ P′ innerStep Peq
    with reflect-inner-τ (decMed (med (toSys r))) (absNodesOf (toSys r)) innerStep
...   | medτ   M′ ms eqP = τbrk-med r ms (trans Peq (cong (λ z → z ∖ ioES) eqP))
...   | nodesτ N′ ns eqP = ⊥-elim (absNodesOf-no-τ (toSys r) ns)
τbrk r step | hidSync M₁ N₁ iomem sM sN Peq = τbrk-io r iomem sM sN Peq

-- fold: a hidden τ-run fixes every break flag
liftτ*-brk′ : (r : RState) {start u : NetProc} → start ≡ radec r
  → start ─[τ*]─► u
  → Σ[ r′ ∈ RState ] (u ≡ radec r′) × BrkFix (toSys r) (toSys r′)
liftτ*-brk′ r eq τ*-refl = r , eq , (λ _ → refl)
liftτ*-brk′ r eq (τ*-step s rest) with τbrk r (subst (λ z → z ─[ τ ]─► _) eq s)
... | r₁ , eq₁ , b₁ with liftτ*-brk′ r₁ eq₁ rest
...   | r′ , equ , b′ = r′ , equ , (λ l → trans (b′ l) (b₁ l))

liftτ*-brk : (r : RState) {u : NetProc}
  → radec r ─[τ*]─► u
  → Σ[ r′ ∈ RState ] (u ≡ radec r′) × BrkFix (toSys r) (toSys r′)
liftτ*-brk r = liftτ*-brk′ r refl

------------------------------------------------------------------------
-- The api strong middle + weak move (mirror `reach-ev-expose` /
-- `liftReach-ev-expose`, medium untouched ⇒ flags fixed via `medEq`).
------------------------------------------------------------------------

-- a strong api/done step fixes every break flag (nodes-solo)
reach-ev-brk : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × BrkFix (toSys r) (toSys r′)
reach-ev-brk r {X} {e} {a} aic apimem step
    with reflect-top-ev (decMed (med (toSys r))) (absNodesOf (toSys r))
           (inj₁ (SR.medium-api-non-offer (med (toSys r)) aic)) step
... | medEv M₁ ms _   = ⊥-elim (SR.medium-api-non-offer (med (toSys r)) aic (M₁ , ms))
... | nodesEv N₁ ns refl with top-nodes-abs-expose (toSys r) apimem ns
...   | s′ , medEq , N₁≡ , cWeakRun , _ , _ =
        r′ , Mr , (λ l → cong (λ mm → broken mm l) (sym medEq))
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

-- the weak api/done move (compose the two τ-paddings)
liftReach-ev-brk : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {t′ : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ═[ ev (evl (evLabel X e a)) ]═► t′
  → Σ[ r′ ∈ RState ] (t′ ≡ radec r′) × BrkFix (toSys r) (toSys r′)
liftReach-ev-brk r {X} {e} {a} aic apimem (wev pre mid post) with liftτ*-brk r pre
... | r₁ , eq₁ , b₁
    with reach-ev-brk r₁ aic apimem
           (subst (λ z → z ─[ ev (evl (evLabel X e a)) ]─► _) eq₁ mid)
...   | r₂ , eq₂ , b₂
      with liftτ*-brk r₂ (subst (λ z → z ─[τ*]─► _) eq₂ post)
...     | r′ , equ , b₃ =
          r′ , equ , (λ l → trans (b₃ l) (trans (b₂ l) (b₁ l)))

------------------------------------------------------------------------
-- The break strong middle + weak move: the fired `⦀Fin` position is PINNED
-- to the label's link (`link-break-chan`), so every OTHER flag is fixed.
------------------------------------------------------------------------

-- a strong `break l` step flips ONLY link `l`'s flag
reach-break-brk : (r : RState) (l : Link) {a : ⊤₀} {M : NetProc}
  → radec r ─[ ev (evl (evLabel ⊤₀ (break l) a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × BrkUpd l (toSys r) (toSys r′)
reach-break-brk r l {a} {M} step
    with reflect-top-ev (decMed (med (toSys r))) (absNodesOf (toSys r))
           (inj₂ (SR.absnodes-no-break (toSys r))) step
... | nodesEv N₁ ns _ = ⊥-elim (SR.absnodes-no-break (toSys r) (N₁ , ns))
... | medEv M₁ medStep Meq0
    with ⦀Fin-ev-inv numLinks
           (λ i → decLink i (phase (med (toSys r)) i) (broken (med (toSys r)) i))
           (SR.break-noBoth (med (toSys r))) medStep
...   | i , Mi , linkStep , Meq
      with SR.link-break-chan i (phase (med (toSys r)) i) (broken (med (toSys r)) i) linkStep
...     | i≡l , MiSkip = r′ , Mr , bupd
  where
    m : MedState
    m = med (toSys r)
    m′ : MedState
    m′ = mkMed (phase m) (SR.broken-upd (broken m) i)
    M₁≡ : M₁ ≡ decMed m′
    M₁≡ = trans Meq
            (trans (cong (λ z → ⦀Fin numLinks
                       (finUpd (λ k → decLink k (phase m k) (broken m k)) i z)) MiSkip)
                   (SR.recon-decMed-brk m i))
    s′ : SysState
    s′ = mkSys m′ (nA (toSys r)) (nB (toSys r)) (nC (toSys r)) (nD (toSys r))
    Meq′ : M ≡ absDec s′
    Meq′ = trans Meq0 (cong₂ (λ mm nn → (mm ∥⇘ ioES ⇙ nn) ∖ ioES) M₁≡ refl)
    wrun : rdec r ═[ ev (evl (evLabel ⊤₀ (break l) a)) ]═► ⟦ s′ ⟧
    wrun = subst (λ mm → rdec r ═[ ev (evl (evLabel ⊤₀ (break l) a)) ]═►
                          ((mm ∥⇘ ioES ⇙ nodesOf s′) ∖ ioES))
             M₁≡
             (wev τ*-refl
               (lift-med-whole-ev (decMed m) (nodesOf (toSys r))
                 (SR.break∉ioES {l} {a}) medStep
                 (noOffer→viewV _ (SR.nodes-no-break (toSys r))))
               τ*-refl)
    r′ : RState
    r′ = proj₁ (rcloseʷ r {s′ = s′} wrun)
    Mr : M ≡ radec r′
    Mr = trans Meq′ (sym (rcloseʷ-abs r {s′ = s′} wrun))
    -- every other link's flag is fixed: `bupd-miss` at `j ≢ i` (from `j ≢ l`)
    bupd : BrkUpd l (toSys r) (toSys r′)
    bupd j j≢l = bupd-miss (broken m) i j (λ q → j≢l (trans q i≡l))

-- the weak `break l` move (compose the two flag-FIXED τ-paddings)
liftReach-break-brk : (r : RState) (l : Link) {a : ⊤₀} {t′ : NetProc}
  → radec r ═[ ev (evl (evLabel ⊤₀ (break l) a)) ]═► t′
  → Σ[ r′ ∈ RState ] (t′ ≡ radec r′) × BrkUpd l (toSys r) (toSys r′)
liftReach-break-brk r l {a} (wev pre mid post) with liftτ*-brk r pre
... | r₁ , eq₁ , b₁
    with reach-break-brk r₁ l
           (subst (λ z → z ─[ ev (evl (evLabel ⊤₀ (break l) a)) ]─► _) eq₁ mid)
...   | r₂ , eq₂ , b₂
      with liftτ*-brk r₂ (subst (λ z → z ─[τ*]─► _) eq₂ post)
...     | r′ , equ , b₃ =
          r′ , equ , (λ j j≢l → trans (b₃ j) (trans (b₂ j j≢l) (b₁ j)))
