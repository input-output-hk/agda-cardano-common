{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the τ-RUN PRODUCER-FIXITY fold (`Praos.PipeProdFix`),
-- item (E1) of the session-32 frontier.
--
-- `PipeExposeNodeProd` folds the PERMISSIVE `ProdAdv` advance algebra across a
-- hidden τ-run.  For the `pcone` endgame we need the much sharper fact that a
-- hidden τ moves NO producer driver at all: the `prodOf` phases of BOTH legs
-- are literally UNCHANGED across a whole `─[τ*]─►` run.
--
-- This is already available componentwise and needs no new inversion:
--   · a medium DRAIN rebuilds `mkSys m′ (nA s) (nB s) (nC s) (nD s)`, so every
--     node — hence every producer — is fixed by `refl`;
--   · an io-SYNC goes through the frozen `WalkConvNodeFix.top-nodes-io-abs-fix`,
--     which ALREADY RETURNS the six driver fixities (its `epAB`/`epAC` legs are
--     exactly the two `prodOf` equalities);
--   · `absNodesOf` has no autonomous τ (`absNodesOf-no-τ`).
-- So the module is a re-mirror of `PipeExposeNodeProd`'s τ-reflector chain with
-- the `AllProdAdv` report replaced by the FIXITY pair `AllProdFix`.
--
-- Consumed by the `pcone` assembly: the `producedA` frame carries a WEAK
-- `apiBF … sendBFBlock` (τ*·ev·τ*), and the `pp5` inversion (E2) only sees the
-- STRONG middle; `liftτ*-prodFix` transports the resulting `pp5` fact back
-- across the τ-prefix to the frame's own state.
--
-- No postulate/hole/meta.  All base modules stay READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; cong₂; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeProdFix (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
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

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysDecode blkA
  using ( SysState; mkSys; med; nA; nB; nC; nD; ⟦_⟧ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysMedium blkA
  using ( MedState; mkMed; phase; broken; decMed )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep blkA
  using ( NetProc; absNodesOf; nodesOf; lift-med-whole-τ
        ; reflect-absDec-τ; innerτ; hidSync; reflect-inner-τ; medτ; nodesτ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode blkA
  using ( ProdPh )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysReach blkA
  using ( RState; mkR; radec; toSys; rdec; reach; Reachable )
open Reachable using ( rStepʷ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvTauInv blkA
  using ( medium-τ-inv-wt )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvEvInv blkA
  using ( medium-ev-inv-wt )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvNodeFix blkA
  using ( top-nodes-io-abs-fix )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysBisim blkA
  using ( lift-io-sync-whole-wτ )
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_TauCore blkA as STC
open STC using ( phase-upd; flipCell )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_NodeTauEv blkA
  using ( setCell; absNodesOf-no-τ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkPr blkA
  using ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeInv blkA
  using ( prodOf )

------------------------------------------------------------------------
-- (1) THE FIXITY REPORT.  Both tracked producer drivers (`prod-AB` = leg BD's,
-- `prod-AC` = leg CD's) are literally unchanged.
------------------------------------------------------------------------

-- both tracked producer drivers are UNCHANGED across the step/run
AllProdFix : SysState → SysState → Set
AllProdFix s s′ =
    (prodOf legBD s ≡ prodOf legBD s′) × (prodOf legCD s ≡ prodOf legCD s′)

-- reflexivity (the frame case: a step that rebuilds every node literally)
allProdFix-refl : (s : SysState) → AllProdFix s s
allProdFix-refl s = refl , refl

-- transitivity (pointwise): compose two fixity reports across a τ-run
allProdFix-trans : (s s₁ s₂ : SysState)
                 → AllProdFix s s₁ → AllProdFix s₁ s₂ → AllProdFix s s₂
allProdFix-trans s s₁ s₂ (u₁ , v₁) (u₂ , v₂) = trans u₁ u₂ , trans v₁ v₂

-- project the whole-nodes fixity onto one leg's producer
prodFixOf : (l : TwoLegs) (s s′ : SysState) → AllProdFix s s′ → prodOf l s ≡ prodOf l s′
prodFixOf legBD s s′ (u , v) = u
prodFixOf legCD s s′ (u , v) = v

------------------------------------------------------------------------
-- (2) THE io-SYNC NODE HALF — a thin wrapper over the frozen
-- `top-nodes-io-abs-fix`, keeping only its two producer legs.
------------------------------------------------------------------------

-- the whole-nodes io-sync exposure, reporting producer FIXITY
top-nodes-io-abs-pfix : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ s′ ∈ SysState ] (med s ≡ med s′) × (M ≡ absNodesOf s′)
      × (nodesOf s ═[ ev (evl (evLabel X e a)) ]═► nodesOf s′)
      × AllProdFix s s′
top-nodes-io-abs-pfix s iomem step =
  let (s′ , meq , Meq , wrun , epAB , epAC , _ , _ , _ , _) = top-nodes-io-abs-fix s iomem step
  in  s′ , meq , Meq , wrun , epAB , epAC

------------------------------------------------------------------------
-- (3) THE MEDIUM-τ REFLECTOR — a drain rebuilds every node literally, so both
-- producers are `refl`-fixed.
------------------------------------------------------------------------

-- reflect a medium drain, reporting producer FIXITY (single `let`, no `with`)
τfix-med : (r : RState) {M M′ : NetProc}
    (ms  : decMed (med (toSys r)) ─[ τ ]─► M′)
    (Meq : M ≡ ((M′ ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × AllProdFix (toSys r) (toSys r′)
τfix-med r {M} {M′} ms Meq =
  let (i , d₀ , id₀ , _ , _ , M′≡) = medium-τ-inv-wt (med (toSys r)) ms
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
  in  r′ , Meq′ , allProdFix-refl (toSys r)

------------------------------------------------------------------------
-- (4) THE io-SYNC REFLECTOR — medium sets one cell, nodes fire the same io;
-- the producer fixity comes off the reflected `s″`.
------------------------------------------------------------------------

-- reflect an io-sync, reporting producer FIXITY (single `let`, no `with`)
τfix-io : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M₁ N₁ M : NetProc}
    (iomem : ioES .mem (X , e) a)
    (sM : decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► M₁)
    (sN : absNodesOf (toSys r)   ─[ ev (evl (evLabel X e a)) ]─► N₁)
    (Meq : M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × AllProdFix (toSys r) (toSys r′)
τfix-io r {X} {e} {a} {M₁} {N₁} {M} iomem sM sN Meq =
  let (i , d₀ , id₀ , np , _ , M₁≡) = medium-ev-inv-wt (med (toSys r)) iomem sM
      (s″ , _ , N₁≡ , cWeakRun , pfix) = top-nodes-io-abs-pfix (toSys r) iomem sN
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
  in  r′ , Meq′ , pfix

------------------------------------------------------------------------
-- (5) THE PER-τ DISPATCH + THE RUN FOLD.
------------------------------------------------------------------------

-- one hidden τ keeps both producers fixed (medium drain / io-sync; nodes-τ absurd)
τfix-prod : (r : RState) {M : NetProc} → radec r ─[ τ ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × AllProdFix (toSys r) (toSys r′)
τfix-prod r step with reflect-absDec-τ (toSys r) step
... | innerτ P′ innerStep Peq
    with reflect-inner-τ (decMed (med (toSys r))) (absNodesOf (toSys r)) innerStep
...   | medτ   M′ ms eqP = τfix-med r ms (trans Peq (cong (λ z → z ∖ ioES) eqP))
...   | nodesτ N′ ns eqP = ⊥-elim (absNodesOf-no-τ (toSys r) ns)
τfix-prod r step | hidSync M₁ N₁ iomem sM sN Peq = τfix-io r iomem sM sN Peq

-- fold the per-τ fixities across a whole hidden τ-run (start-equality form)
liftτ*-pfix′ : (r : RState) {start u : NetProc} → start ≡ radec r
             → start ─[τ*]─► u
             → Σ[ r′ ∈ RState ] (u ≡ radec r′) × AllProdFix (toSys r) (toSys r′)
liftτ*-pfix′ r eq τ*-refl = r , eq , allProdFix-refl (toSys r)
liftτ*-pfix′ r eq (τ*-step s rest) with τfix-prod r (subst (λ z → z ─[ τ ]─► _) eq s)
... | r₁ , eq₁ , rep₁ with liftτ*-pfix′ r₁ eq₁ rest
...   | r′ , equ , rep′ =
        r′ , equ , allProdFix-trans (toSys r) (toSys r₁) (toSys r′) rep₁ rep′

-- HEADLINE (E1): a hidden τ-run out of `radec r` reaches a reachable `r′` at
-- which BOTH producer drivers hold their original phase
liftτ*-prodFix : (r : RState) {u : NetProc} → radec r ─[τ*]─► u
               → Σ[ r′ ∈ RState ] (u ≡ radec r′) × AllProdFix (toSys r) (toSys r′)
liftτ*-prodFix r = liftτ*-pfix′ r refl
