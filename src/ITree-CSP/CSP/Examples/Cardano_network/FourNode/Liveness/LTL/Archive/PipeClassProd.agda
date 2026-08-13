{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the GENUINE Fix/Adv PRODUCER CLASSIFIER
-- (`Praos.PipeClassProd`).
--
-- `PipeExposeNodeProd` built a PERMISSIVE producer report (always an advance
-- from the TOTAL `allProdAdv-of`).  This module reshapes it into the
-- `WalkDExpose.DReport` SHAPE, using the genuine classes `PipeNodeFixApi.
-- AllProdClass` — `pcFix` (a propositional `≡`, the datum a `PipeStep⁺` prod core
-- needs on a FIXED producer) or `pcAdv` (a concrete `ProdAdv`).
--
-- CHEAPER than the client (session-12/13): a producer is a DRIVER, so its io-sync
-- FIXITY is ALREADY surfaced by `WalkConvNodeFix.top-nodes-io-abs-fix` (the six
-- driver fixities as `≡`) — the τ-run reflector reads `pcFix` directly via the
-- thin `top-nodes-io-abs-prod-cls`, NO per-peer re-mirror.  The visible api-CSBF
-- middle moves a producer only when node A fires; that decision comes off the
-- SHARED api cone `top-nodes-abs-expose-cls` (which already carries `AllProdClass`).
--
-- Reuses the reflector STRUCTURE of `PipeClassClient` VERBATIM.  No postulate/
-- hole/meta.  All base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Nat using ( _<_ )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( inj₁ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; cong₂; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Archive.PipeClassProd (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; apiES )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟ )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _∖_; EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; τ; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wev; wτ )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; mkSys; med; nA; nB; nC; nD; ⟦_⟧ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( MedState; mkMed; phase; broken; decMed )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
  using ( NetProc; absDec; absNodesOf; nodesOf; lift-med-whole-τ
        ; medEv; nodesEv; reflect-top-ev
        ; reflect-absDec-τ; innerτ; hidSync; reflect-inner-τ; medτ; nodesτ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( RState; mkR; radec; toSys; rdec; reach; Reachable; rcloseʷ; rcloseʷ-abs )
open Reachable using ( rStepʷ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA
  using ( IsApiCSBF )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysRoute blkA as SR
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvTauInv blkA
  using ( medium-τ-inv-wt )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvEvInv blkA
  using ( medium-ev-inv-wt )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysBisim blkA
  using ( lift-io-sync-whole-wτ; lift-nodes-whole-wev )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_GapBDisj blkA
  using ( noOffer→viewV )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.Walk blkA
  using ( μTot )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_TauCore blkA as STC
open STC using ( phase-upd; flipCell )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( setCell; absNodesOf-no-τ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( prodOf )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Archive.PipeNodeFixApi blkA
  using ( ProdClass1; pcFix; pcAdv
        ; AllProdClass; allProdClass-refl; allProdClass-trans
        ; top-nodes-io-abs-prod-cls; top-nodes-abs-expose-cls )

------------------------------------------------------------------------
-- MEDIUM-τ reflector: a medium drain moves NO node, so every producer is FIXED.
------------------------------------------------------------------------

τreflect-med-classprod : (r : RState) {M M′ : NetProc}
    (ms  : decMed (med (toSys r)) ─[ τ ]─► M′)
    (Meq : M ≡ ((M′ ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × AllProdClass (toSys r) (toSys r′)
τreflect-med-classprod r {M} {M′} ms Meq with medium-τ-inv-wt (med (toSys r)) ms
... | i , d₀ , id₀ , _ , _ , M′≡ = r′ , Meq′ , allProdClass-refl (toSys r)
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
-- io-SYNC reflector: a hidden io-sync leaves every driver fixed, so every
-- producer is `pcFix` (read off `top-nodes-io-abs-prod-cls`).
------------------------------------------------------------------------

τreflect-io-classprod : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M₁ N₁ M : NetProc}
    (iomem : ioES .mem (X , e) a)
    (sM : decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► M₁)
    (sN : absNodesOf (toSys r)   ─[ ev (evl (evLabel X e a)) ]─► N₁)
    (Meq : M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × AllProdClass (toSys r) (toSys r′)
τreflect-io-classprod r {X} {e} {a} {M₁} {N₁} {M} iomem sM sN Meq
    with medium-ev-inv-wt (med (toSys r)) iomem sM
       | top-nodes-io-abs-prod-cls (toSys r) iomem sN
... | i , d₀ , id₀ , np , _ , M₁≡ | s″ , _ , N₁≡ , cWeakRun , prodRep =
      r′ , Meq′ , prodRep
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
-- TOTAL per-τ reflector: dispatch a hidden τ (nodes-τ refuted).
------------------------------------------------------------------------

τreflect-classprod : (r : RState) {M : NetProc} → radec r ─[ τ ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × AllProdClass (toSys r) (toSys r′)
τreflect-classprod r step with reflect-absDec-τ (toSys r) step
... | innerτ P′ innerStep Peq
    with reflect-inner-τ (decMed (med (toSys r))) (absNodesOf (toSys r)) innerStep
...   | medτ   M′ ms eqP = τreflect-med-classprod r ms (trans Peq (cong (λ z → z ∖ ioES) eqP))
...   | nodesτ N′ ns eqP = ⊥-elim (absNodesOf-no-τ (toSys r) ns)
τreflect-classprod r step | hidSync M₁ N₁ iomem sM sN Peq = τreflect-io-classprod r iomem sM sN Peq

------------------------------------------------------------------------
-- τ-run lift: fold the per-τ classifiers by `allProdClass-trans`.
------------------------------------------------------------------------

liftτ*-classprod′ : (r : RState) {start u : NetProc} → start ≡ radec r
          → start ─[τ*]─► u
          → Σ[ r′ ∈ RState ] (u ≡ radec r′) × AllProdClass (toSys r) (toSys r′)
liftτ*-classprod′ r eq τ*-refl = r , eq , allProdClass-refl (toSys r)
liftτ*-classprod′ r eq (τ*-step s rest) with τreflect-classprod r (subst (λ z → z ─[ τ ]─► _) eq s)
... | r₁ , eq₁ , rep₁ with liftτ*-classprod′ r₁ eq₁ rest
...   | r′ , equ , rep′ =
        r′ , equ , allProdClass-trans (toSys r) (toSys r₁) (toSys r′) rep₁ rep′

liftτ*-classprod : (r : RState) {u : NetProc}
         → radec r ─[τ*]─► u
         → Σ[ r′ ∈ RState ] (u ≡ radec r′) × AllProdClass (toSys r) (toSys r′)
liftτ*-classprod r = liftτ*-classprod′ r refl

------------------------------------------------------------------------
-- VISIBLE api-CSBF MIDDLE: the producer classes come off the shared api cone
-- `top-nodes-abs-expose-cls` (node A fires ⇒ its producer advances; else fixed).
------------------------------------------------------------------------

reach-ev-classprod : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′)
      × (rdec r ═[ ev (evl (evLabel X e a)) ]═► rdec r′)
      × (μTot (toSys r′) < μTot (toSys r)) × AllProdClass (toSys r) (toSys r′)
reach-ev-classprod r {X} {e} {a} aic apimem step
    with reflect-top-ev (decMed (med (toSys r))) (absNodesOf (toSys r))
           (inj₁ (SR.medium-api-non-offer (med (toSys r)) aic)) step
... | medEv M₁ ms _   = ⊥-elim (SR.medium-api-non-offer (med (toSys r)) aic (M₁ , ms))
... | nodesEv N₁ ns refl with top-nodes-abs-expose-cls (toSys r) apimem ns
...   | s′ , medEq , N₁≡ , cWeakRun , drop , _ , _ , prodcls , _ =
        r′ , Mr , wr , drop , prodcls
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
-- The FULL weak api-CSBF move: compose τ-pre + visible middle + τ-post.
------------------------------------------------------------------------

liftReach-classprod : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {t′ : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ═[ ev (evl (evLabel X e a)) ]═► t′
  → Σ[ r′ ∈ RState ] (t′ ≡ radec r′) × AllProdClass (toSys r) (toSys r′)
liftReach-classprod r {X} {e} {a} aic apimem (wev pre mid post) with liftτ*-classprod r pre
... | r₁ , eq₁ , pc₁
    with reach-ev-classprod r₁ aic apimem
           (subst (λ z → z ─[ ev (evl (evLabel X e a)) ]─► _) eq₁ mid)
...   | r₂ , eq₂ , _ , _ , pcmid
      with liftτ*-classprod r₂ (subst (λ z → z ─[τ*]─► _) eq₂ post)
...     | r′ , equ , pc₃ =
          r′ , equ ,
          allProdClass-trans (toSys r) (toSys r₁) (toSys r′) pc₁
            (allProdClass-trans (toSys r₁) (toSys r₂) (toSys r′) pcmid pc₃)

------------------------------------------------------------------------
-- The leg-`l` `ProdReport⁺`: the leg's producer CLASSIFIED across a move.
------------------------------------------------------------------------

-- how the leg-`l` producer is classified across a step/run
ProdReport⁺ : TwoLegs → SysState → SysState → Set
ProdReport⁺ l s s′ = ProdClass1 (prodOf l s) (prodOf l s′)

-- project the whole-nodes classifier onto the leg producer
allProdClass⇒ProdReport⁺ : (l : TwoLegs) (s s′ : SysState)
                         → AllProdClass s s′ → ProdReport⁺ l s s′
allProdClass⇒ProdReport⁺ legBD s s′ (u , v) = u
allProdClass⇒ProdReport⁺ legCD s s′ (u , v) = v

-- HEADLINE (τ-run half)
liftτ*-prodReport⁺ : (l : TwoLegs) (r : RState) {u : NetProc}
                  → radec r ─[τ*]─► u
                  → Σ[ r′ ∈ RState ] (u ≡ radec r′) × ProdReport⁺ l (toSys r) (toSys r′)
liftτ*-prodReport⁺ l r run with liftτ*-classprod r run
... | r′ , eq , acc = r′ , eq , allProdClass⇒ProdReport⁺ l (toSys r) (toSys r′) acc

-- HEADLINE (full weak move)
liftReach-prodReport⁺ : (l : TwoLegs) (r : RState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {t′ : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ═[ ev (evl (evLabel X e a)) ]═► t′
  → Σ[ r′ ∈ RState ] (t′ ≡ radec r′) × ProdReport⁺ l (toSys r) (toSys r′)
liftReach-prodReport⁺ l r aic apimem w with liftReach-classprod r aic apimem w
... | r′ , eq , acc = r′ , eq , allProdClass⇒ProdReport⁺ l (toSys r) (toSys r′) acc
