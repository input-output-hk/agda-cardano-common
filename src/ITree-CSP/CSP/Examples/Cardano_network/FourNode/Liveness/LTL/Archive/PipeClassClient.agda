{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the GENUINE Fix/Adv CLIENT CLASSIFIER, τ-run half
-- (`Praos.PipeClassClient`).
--
-- `PipeExposeNodeClient` built a PERMISSIVE client report (a `ClientAdv` for
-- every tracked client, ALWAYS an advance from the TOTAL `allClientAdv-of`) — it
-- never carried the propositional `≡` a `PipeStep⁺` client core needs on a FIXED
-- client, and it could not DECIDE which clients moved (session-10 D2/D3 gap).
--
-- This module reshapes the client report into the `WalkDExpose.DReport` SHAPE,
-- using the genuine per-peer node classifier `PipeNodeFix.top-nodes-io-abs
-- -client-cls` (which — unlike `top-nodes-io-abs-fix` — keeps each successor node
-- CONCRETE, so a non-fired client is `clFix refl` and only the fired peer is
-- `clAdv`).  The τ-run half is built here (medium-τ + io-sync reflectors + the
-- fold + the leg `ClientReport⁺`); the visible api-CSBF MIDDLE half is deferred
-- to a companion api node cone.
--
-- Reuses the io reflector STRUCTURE of `PipeExposeNodeClient` and the algebra of
-- `PipeNodeFix` VERBATIM; only the report content is the genuine decision.  No
-- postulate/hole/meta.  All base modules READ-ONLY.
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
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Archive.PipeClassClient (blkA : Block₃) where

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
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_GapBDisj blkA
  using ( noOffer→viewV )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.Walk blkA
  using ( μTot )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvTauInv blkA
  using ( medium-τ-inv-wt )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvEvInv blkA
  using ( medium-ev-inv-wt )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysBisim blkA
  using ( lift-io-sync-whole-wτ; lift-nodes-whole-wev )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_TauCore blkA as STC
open STC using ( phase-upd; flipCell )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( setCell; absNodesOf-no-τ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( upClient; dnClient )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Archive.PipeNodeFix blkA
  using ( ClientClass1; clFix; clAdv; ccFold
        ; AllClientClass; allClientClass-refl; allClientClass-trans
        ; top-nodes-io-abs-client-cls )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Archive.PipeNodeFixApi blkA
  using ( top-nodes-abs-expose-cls )

------------------------------------------------------------------------
-- MEDIUM-τ reflector with the classifier (mirror `PipeExposeNodeClient.
-- τreflect-med-client`, LIGHT — medium-only τ lift): a medium drain moves NO
-- node, so every tracked client is FIXED (`allClientClass-refl`).
------------------------------------------------------------------------

τreflect-med-classcl : (r : RState) {M M′ : NetProc}
    (ms  : decMed (med (toSys r)) ─[ τ ]─► M′)
    (Meq : M ≡ ((M′ ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × AllClientClass (toSys r) (toSys r′)
τreflect-med-classcl r {M} {M′} ms Meq with medium-τ-inv-wt (med (toSys r)) ms
... | i , d₀ , id₀ , _ , _ , M′≡ = r′ , Meq′ , allClientClass-refl (toSys r)
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
-- io-SYNC reflector with the classifier (RAM-heavy — mirror `PipeExposeNode
-- Client.τreflect-io-client`, but using `top-nodes-io-abs-client-cls` so the
-- reflected successor's tracked clients are genuinely CLASSIFIED — the fired
-- one advanced, the others fixed).
------------------------------------------------------------------------

τreflect-io-classcl : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M₁ N₁ M : NetProc}
    (iomem : ioES .mem (X , e) a)
    (sM : decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► M₁)
    (sN : absNodesOf (toSys r)   ─[ ev (evl (evLabel X e a)) ]─► N₁)
    (Meq : M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × AllClientClass (toSys r) (toSys r′)
τreflect-io-classcl r {X} {e} {a} {M₁} {N₁} {M} iomem sM sN Meq
    with medium-ev-inv-wt (med (toSys r)) iomem sM
       | top-nodes-io-abs-client-cls (toSys r) iomem sN
... | i , d₀ , id₀ , np , _ , M₁≡ | s″ , _ , N₁≡ , cWeakRun , clientRep , _ , _ , _ , _ , _ , _ =
      r′ , Meq′ , clientRep
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
-- TOTAL per-τ reflector with the classifier (mirror `PipeExposeNodeClient.
-- τreflect-client`): dispatch a hidden τ to the medium-τ drain reflector or the
-- io-sync reflector (nodes-τ is refuted by `absNodesOf-no-τ`).
------------------------------------------------------------------------

τreflect-classcl : (r : RState) {M : NetProc} → radec r ─[ τ ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × AllClientClass (toSys r) (toSys r′)
τreflect-classcl r step with reflect-absDec-τ (toSys r) step
... | innerτ P′ innerStep Peq
    with reflect-inner-τ (decMed (med (toSys r))) (absNodesOf (toSys r)) innerStep
...   | medτ   M′ ms eqP = τreflect-med-classcl r ms (trans Peq (cong (λ z → z ∖ ioES) eqP))
...   | nodesτ N′ ns eqP = ⊥-elim (absNodesOf-no-τ (toSys r) ns)
τreflect-classcl r step | hidSync M₁ N₁ iomem sM sN Peq = τreflect-io-classcl r iomem sM sN Peq

------------------------------------------------------------------------
-- τ-run lift with the classifier (mirror `PipeExposeNodeClient.liftτ*-client`):
-- fold the per-τ classifiers across a whole hidden τ-run by `allClientClass
-- -trans` (pointwise `ccFold`).  This is the τ-run half of the leg `ClientReport⁺`.
------------------------------------------------------------------------

liftτ*-classcl′ : (r : RState) {start u : NetProc} → start ≡ radec r
          → start ─[τ*]─► u
          → Σ[ r′ ∈ RState ] (u ≡ radec r′) × AllClientClass (toSys r) (toSys r′)
liftτ*-classcl′ r eq τ*-refl = r , eq , allClientClass-refl (toSys r)
liftτ*-classcl′ r eq (τ*-step s rest) with τreflect-classcl r (subst (λ z → z ─[ τ ]─► _) eq s)
... | r₁ , eq₁ , rep₁ with liftτ*-classcl′ r₁ eq₁ rest
...   | r′ , equ , rep′ =
        r′ , equ , allClientClass-trans (toSys r) (toSys r₁) (toSys r′) rep₁ rep′

liftτ*-classcl : (r : RState) {u : NetProc}
         → radec r ─[τ*]─► u
         → Σ[ r′ ∈ RState ] (u ≡ radec r′) × AllClientClass (toSys r) (toSys r′)
liftτ*-classcl r = liftτ*-classcl′ r refl

------------------------------------------------------------------------
-- The leg-`l` `ClientReport⁺`: instantiate `AllClientClass` at the leg's
-- upstream and downstream BF-client peers (`upClient`/`dnClient`) — the genuine
-- (Fix/Adv) CLIENT component of the reshaped `PipeReport`, feeding a `PipeStep⁺`
-- client core's `upClient`/`dnClient` needs.
------------------------------------------------------------------------

-- how the leg-`l` upstream + downstream BF-client peers are CLASSIFIED
ClientReport⁺ : TwoLegs → SysState → SysState → Set
ClientReport⁺ l s s′ =
    ClientClass1 (upClient l s) (upClient l s′) × ClientClass1 (dnClient l s) (dnClient l s′)

-- project the whole-nodes classifier onto the two leg clients
allClientClass⇒ClientReport⁺ : (l : TwoLegs) (s s′ : SysState)
                             → AllClientClass s s′ → ClientReport⁺ l s s′
allClientClass⇒ClientReport⁺ legBD s s′ (uBD , uCD , dBD , dCD) = uBD , dBD
allClientClass⇒ClientReport⁺ legCD s s′ (uBD , uCD , dBD , dCD) = uCD , dCD

-- HEADLINE (τ-run half): a hidden τ-run CLASSIFIES the leg-`l` BF-client peers
-- (fixed with `≡`, or advanced) — the datum a `PipeStep⁺` client core consumes
liftτ*-clientReport⁺ : (l : TwoLegs) (r : RState) {u : NetProc}
                    → radec r ─[τ*]─► u
                    → Σ[ r′ ∈ RState ] (u ≡ radec r′) × ClientReport⁺ l (toSys r) (toSys r′)
liftτ*-clientReport⁺ l r run with liftτ*-classcl r run
... | r′ , eq , acc = r′ , eq , allClientClass⇒ClientReport⁺ l (toSys r) (toSys r′) acc

------------------------------------------------------------------------
-- VISIBLE api-CSBF MIDDLE with the classifier (RAM-heavy — re-mirror
-- `PipeExposeReach.reach-ev-both` / `PipeClassCell.reach-ev-classcell`, but using
-- the genuine api client cone `top-nodes-abs-expose-cls`): unlike the cell (which
-- stays FIXED across the api middle because the medium is a solo pass-through),
-- an api-CSBF hand-off MOVES the handing client — so the classifier comes
-- directly off the cone's `AllClientClass`, not from a medium equality.
------------------------------------------------------------------------

reach-ev-classcl : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′)
      × (rdec r ═[ ev (evl (evLabel X e a)) ]═► rdec r′)
      × (μTot (toSys r′) < μTot (toSys r)) × AllClientClass (toSys r) (toSys r′)
reach-ev-classcl r {X} {e} {a} aic apimem step
    with reflect-top-ev (decMed (med (toSys r))) (absNodesOf (toSys r))
           (inj₁ (SR.medium-api-non-offer (med (toSys r)) aic)) step
... | medEv M₁ ms _   = ⊥-elim (SR.medium-api-non-offer (med (toSys r)) aic (M₁ , ms))
... | nodesEv N₁ ns refl with top-nodes-abs-expose-cls (toSys r) apimem ns
...   | s′ , medEq , N₁≡ , cWeakRun , drop , _ , clientcls , _ , _ =
        r′ , Mr , wr , drop , clientcls
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

-- the leg-`l` projection of the visible-middle client frame
reach-ev-clientReport⁺ : (l : TwoLegs) (r : RState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′)
      × (rdec r ═[ ev (evl (evLabel X e a)) ]═► rdec r′)
      × (μTot (toSys r′) < μTot (toSys r)) × ClientReport⁺ l (toSys r) (toSys r′)
reach-ev-clientReport⁺ l r aic apimem step with reach-ev-classcl r aic apimem step
... | r′ , Mr , wr , drop , acc =
      r′ , Mr , wr , drop , allClientClass⇒ClientReport⁺ l (toSys r) (toSys r′) acc

------------------------------------------------------------------------
-- The FULL weak api-CSBF move with the classifier (mirror `PipeExposeReport.
-- liftReach-ev-both`): compose the τ-pre run (`liftτ*-classcl`), the visible
-- api-CSBF middle (`reach-ev-classcl`), and the τ-post run on ONE reflected `r′`
-- by `allClientClass-trans`.
------------------------------------------------------------------------

liftReach-classcl : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {t′ : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ═[ ev (evl (evLabel X e a)) ]═► t′
  → Σ[ r′ ∈ RState ] (t′ ≡ radec r′) × AllClientClass (toSys r) (toSys r′)
liftReach-classcl r {X} {e} {a} aic apimem (wev pre mid post) with liftτ*-classcl r pre
... | r₁ , eq₁ , cc₁
    with reach-ev-classcl r₁ aic apimem
           (subst (λ z → z ─[ ev (evl (evLabel X e a)) ]─► _) eq₁ mid)
...   | r₂ , eq₂ , _ , _ , ccmid
      with liftτ*-classcl r₂ (subst (λ z → z ─[τ*]─► _) eq₂ post)
...     | r′ , equ , cc₃ =
          r′ , equ ,
          allClientClass-trans (toSys r) (toSys r₁) (toSys r′) cc₁
            (allClientClass-trans (toSys r₁) (toSys r₂) (toSys r′) ccmid cc₃)

-- HEADLINE (full weak move): a weak api-CSBF move CLASSIFIES the leg-`l` BF-client
-- peers across the whole hop — the datum a `PipeStep⁺` client core consumes
liftReach-clientReport⁺ : (l : TwoLegs) (r : RState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {t′ : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ═[ ev (evl (evLabel X e a)) ]═► t′
  → Σ[ r′ ∈ RState ] (t′ ≡ radec r′) × ClientReport⁺ l (toSys r) (toSys r′)
liftReach-clientReport⁺ l r aic apimem w with liftReach-classcl r aic apimem w
... | r′ , eq , acc = r′ , eq , allClientClass⇒ClientReport⁺ l (toSys r) (toSys r′) acc
