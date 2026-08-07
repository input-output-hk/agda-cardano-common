{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the GENUINE five-component `PipeReport⁺-gen`
-- (`Praos.PipeReportGen`).
--
-- `PipeExposeReportAll.liftReach-pipe⁺` merged the FIVE reports but from the
-- PERMISSIVE total-`adv-of` classifiers (session-10 D2/D3 gap).  This module
-- re-does the merge off the GENUINE Fix/Adv classifiers (`PipeClassCell`,
-- `PipeClassClient`, `PipeClassProd`, `PipeClassRelay`, `WalkDExpose.DReport`),
-- so every FIXED component carries the propositional `≡` a `PipeStep⁺` core
-- consumes and every MOVE is a decided advance.
--
-- The crux is ONE reflected successor `r′` shared by all five: the cell +
-- client + prod + relay + D deltas must be read off the SAME `s′`.  We rebuild
-- ONE reflector `τreflect-gen` (mirror `PipeExposeReport.τreflect-both`) that
-- uses `medium-ev-inv-wt` for the cell and the NOW-EXTENDED
-- `PipeNodeFix.top-nodes-io-abs-client-cls` (which emits the client classes AND
-- the six driver/consumer fixities) for the four node components.  The visible
-- api-CSBF middle rides the SINGLE `PipeNodeFixApi.top-nodes-abs-expose-cls`
-- (which already emits `DReport` + client + prod + relay on one `s′`; the cell
-- is fixed there by `med s ≡ med s′`).  `liftReach-gen` composes τ-pre + middle
-- + τ-post on the ONE `r′`; `liftReach-pipe⁺-gen` projects to the leg reports.
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
module CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeReportGen (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; apiES )
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
  using ( NetProc; absDec; absNodesOf; nodesOf; lift-med-whole-τ
        ; medEv; nodesEv; reflect-top-ev
        ; reflect-absDec-τ; innerτ; hidSync; reflect-inner-τ; medτ; nodesτ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysReach blkA
  using ( RState; mkR; radec; toSys; rdec; reach; Reachable; rcloseʷ; rcloseʷ-abs )
open Reachable using ( rStepʷ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle blkA
  using ( IsApiCSBF )
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysRoute blkA as SR
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_GapBDisj blkA
  using ( noOffer→viewV )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.Walk blkA
  using ( μTot )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvTauInv blkA
  using ( medium-τ-inv-wt )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvEvInv blkA
  using ( medium-ev-inv-wt )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysBisim blkA
  using ( lift-io-sync-whole-wτ; lift-nodes-whole-wev )
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_TauCore blkA as STC
open STC using ( phase-upd; flipCell )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_NodeTauEv blkA
  using ( setCell; absNodesOf-no-τ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkPr blkA
  using ( TwoLegs )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeInv blkA
  using ( prodOf; relayOf )

-- the five genuine classifier algebras (Fix/Adv sums) + their trans/refl
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkTauExpose blkA
  using ( BD; CD; DFix )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkDExpose blkA
  using ( DReport )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkReachExpose blkA
  using ( compose-DReport )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeClassCell blkA
  using ( AllCellClass; allCellClass-refl; allCellClass-trans; allCellClass-medEq
        ; cell-drain-class; cell-fill-class; CellReport⁺; allCellClass⇒CellReport⁺ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeNodeFix blkA
  using ( ClientClass1; clFix; AllClientClass; allClientClass-refl; allClientClass-trans
        ; top-nodes-io-abs-client-cls )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeNodeFixApi blkA
  using ( ProdClass1; pcFix; RelayClass1; rcFix
        ; AllProdClass; allProdClass-refl; allProdClass-trans
        ; AllRelayClass; allRelayClass-refl; allRelayClass-trans
        ; top-nodes-abs-expose-cls )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeClassClient blkA
  using ( ClientReport⁺; allClientClass⇒ClientReport⁺ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeClassProd blkA
  using ( ProdReport⁺; allProdClass⇒ProdReport⁺ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeClassRelay blkA
  using ( RelayReport⁺; allRelayClass⇒RelayReport⁺ )

------------------------------------------------------------------------
-- The whole-system τ-run bundle: the four node/medium classifiers plus the
-- D-consumer `DFix` (D moves only on the visible api middle, so it is FIXED
-- across a hidden τ-run).  Composes component-wise.
------------------------------------------------------------------------

GenClassτ : SysState → SysState → Set
GenClassτ s s′ =
    AllCellClass s s′ × AllClientClass s s′ × AllProdClass s s′
  × AllRelayClass s s′ × DFix s s′

-- reflexivity: a fixed step classifies every component FIXED
genClassτ-refl : (s : SysState) → GenClassτ s s
genClassτ-refl s =
  allCellClass-refl s , allClientClass-refl s , allProdClass-refl s
  , allRelayClass-refl s , (refl , refl)

-- transitivity: compose two τ-bundles (D `DFix` folds by `trans`, reversed)
genClassτ-trans : (s s₁ s₂ : SysState)
                → GenClassτ s s₁ → GenClassτ s₁ s₂ → GenClassτ s s₂
genClassτ-trans s s₁ s₂
  (ce₁ , cl₁ , pr₁ , rl₁ , (bd₁ , cd₁)) (ce₂ , cl₂ , pr₂ , rl₂ , (bd₂ , cd₂)) =
    allCellClass-trans   s s₁ s₂ ce₁ ce₂
  , allClientClass-trans s s₁ s₂ cl₁ cl₂
  , allProdClass-trans   s s₁ s₂ pr₁ pr₂
  , allRelayClass-trans  s s₁ s₂ rl₁ rl₂
  , (trans bd₂ bd₁ , trans cd₂ cd₁)

------------------------------------------------------------------------
-- MEDIUM-τ reflector with ALL FIVE (mirror `PipeExposeReport.τreflect-med
-- -both`): a medium drain moves NO node, so client/prod/relay/D are FIXED and
-- only the drained cell advances.  Same `r′` as the cell/D reflectors.
------------------------------------------------------------------------

τreflect-med-gen : (r : RState) {M M′ : NetProc}
    (ms  : decMed (med (toSys r)) ─[ τ ]─► M′)
    (Meq : M ≡ ((M′ ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × GenClassτ (toSys r) (toSys r′)
τreflect-med-gen r {M} {M′} ms Meq with medium-τ-inv-wt (med (toSys r)) ms
... | i , d₀ , id₀ , x , drainEq , M′≡ =
      r′ , Meq′
      , ( (λ kl kd kid → cell-drain-class (med (toSys r)) i d₀ id₀ x drainEq kl kd kid)
        , allClientClass-refl (toSys r) , allProdClass-refl (toSys r)
        , allRelayClass-refl (toSys r) , (refl , refl) )
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
-- io-SYNC reflector with ALL FIVE (RAM-heavy — mirror `PipeExposeReport.
-- τreflect-io-both`): the cell fills (`cell-fill-class`), the fired client
-- advances (from the cone's `AllClientClass`), and the drivers + D-consumer
-- are FIXED (the cone's six driver/consumer fixities `pcFix`/`rcFix`/`DFix`).
------------------------------------------------------------------------

τreflect-io-gen : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M₁ N₁ M : NetProc}
    (iomem : ioES .mem (X , e) a)
    (sM : decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► M₁)
    (sN : absNodesOf (toSys r)   ─[ ev (evl (evLabel X e a)) ]─► N₁)
    (Meq : M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × GenClassτ (toSys r) (toSys r′)
τreflect-io-gen r {X} {e} {a} {M₁} {N₁} {M} iomem sM sN Meq
    with medium-ev-inv-wt (med (toSys r)) iomem sM
       | top-nodes-io-abs-client-cls (toSys r) iomem sN
... | i , d₀ , id₀ , np , wtEq , M₁≡
    | s″ , _ , N₁≡ , cWeakRun , clientRep , epAB , epAC , ecpB , ecpC , econsBD , econsCD =
      r′ , Meq′
      , ( (λ kl kd kid → cell-fill-class (med (toSys r)) i d₀ id₀ np wtEq kl kd kid)
        , clientRep
        , (pcFix epAB , pcFix epAC)
        , (rcFix ecpB , rcFix ecpC)
        , (sym econsBD , sym econsCD) )
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
-- TOTAL per-τ reflector with ALL FIVE (mirror `PipeExposeReport.τreflect-both`).
------------------------------------------------------------------------

τreflect-gen : (r : RState) {M : NetProc} → radec r ─[ τ ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × GenClassτ (toSys r) (toSys r′)
τreflect-gen r step with reflect-absDec-τ (toSys r) step
... | innerτ P′ innerStep Peq
    with reflect-inner-τ (decMed (med (toSys r))) (absNodesOf (toSys r)) innerStep
...   | medτ   M′ ms eqP = τreflect-med-gen r ms (trans Peq (cong (λ z → z ∖ ioES) eqP))
...   | nodesτ N′ ns eqP = ⊥-elim (absNodesOf-no-τ (toSys r) ns)
τreflect-gen r step | hidSync M₁ N₁ iomem sM sN Peq = τreflect-io-gen r iomem sM sN Peq

------------------------------------------------------------------------
-- τ-run lift with ALL FIVE (mirror `PipeExposeReport.liftτ*-both`): fold the
-- per-τ five-component bundle across a whole hidden τ-run.
------------------------------------------------------------------------

liftτ*-gen′ : (r : RState) {start u : NetProc} → start ≡ radec r
          → start ─[τ*]─► u
          → Σ[ r′ ∈ RState ] (u ≡ radec r′) × GenClassτ (toSys r) (toSys r′)
liftτ*-gen′ r eq τ*-refl = r , eq , genClassτ-refl (toSys r)
liftτ*-gen′ r eq (τ*-step s rest) with τreflect-gen r (subst (λ z → z ─[ τ ]─► _) eq s)
... | r₁ , eq₁ , g₁ with liftτ*-gen′ r₁ eq₁ rest
...   | r′ , equ , g′ =
        r′ , equ , genClassτ-trans (toSys r) (toSys r₁) (toSys r′) g₁ g′

liftτ*-gen : (r : RState) {u : NetProc}
         → radec r ─[τ*]─► u
         → Σ[ r′ ∈ RState ] (u ≡ radec r′) × GenClassτ (toSys r) (toSys r′)
liftτ*-gen r = liftτ*-gen′ r refl

------------------------------------------------------------------------
-- VISIBLE api-CSBF MIDDLE with ALL FIVE (mirror `PipeClassClient.reach-ev
-- -classcl`, but reading EVERY output of the shared cone
-- `top-nodes-abs-expose-cls`): the cell is FIXED (`med s ≡ med s′` ⇒
-- `allCellClass-medEq`); the D-consumer `DReport`, the clients, the producers,
-- and the relays all come off the cone.
------------------------------------------------------------------------

reach-ev-gen : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′)
      × (rdec r ═[ ev (evl (evLabel X e a)) ]═► rdec r′)
      × (μTot (toSys r′) < μTot (toSys r))
      × AllCellClass (toSys r) (toSys r′)
      × AllClientClass (toSys r) (toSys r′)
      × AllProdClass (toSys r) (toSys r′)
      × AllRelayClass (toSys r) (toSys r′)
      × DReport (toSys r) (toSys r′) e a
reach-ev-gen r {X} {e} {a} aic apimem step
    with reflect-top-ev (decMed (med (toSys r))) (absNodesOf (toSys r))
           (inj₁ (SR.medium-api-non-offer (med (toSys r)) aic)) step
... | medEv M₁ ms _   = ⊥-elim (SR.medium-api-non-offer (med (toSys r)) aic (M₁ , ms))
... | nodesEv N₁ ns refl with top-nodes-abs-expose-cls (toSys r) apimem ns
...   | s′ , medEq , N₁≡ , cWeakRun , drop , drep , clientcls , prodcls , relaycls =
        r′ , Mr , wr , drop
        , allCellClass-medEq (toSys r) s′ medEq , clientcls , prodcls , relaycls , drep
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
-- The FULL weak api-CSBF move with ALL FIVE (mirror `PipeExposeReport.
-- liftReach-ev-both`): compose the τ-pre bundle, the visible middle, and the
-- τ-post bundle on ONE reflected `r′` (D via `compose-DReport`).
------------------------------------------------------------------------

liftReach-gen : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {t′ : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ═[ ev (evl (evLabel X e a)) ]═► t′
  → Σ[ r′ ∈ RState ] (t′ ≡ radec r′)
      × AllCellClass (toSys r) (toSys r′)
      × AllClientClass (toSys r) (toSys r′)
      × AllProdClass (toSys r) (toSys r′)
      × AllRelayClass (toSys r) (toSys r′)
      × DReport (toSys r) (toSys r′) e a
liftReach-gen r {X} {e} {a} aic apimem (wev pre mid post) with liftτ*-gen r pre
... | r₁ , eq₁ , (ce₁ , cl₁ , pr₁ , rl₁ , dfix₁)
    with reach-ev-gen r₁ aic apimem
           (subst (λ z → z ─[ ev (evl (evLabel X e a)) ]─► _) eq₁ mid)
...   | r₂ , eq₂ , _ , _ , cemid , clmid , prmid , rlmid , drep
      with liftτ*-gen r₂ (subst (λ z → z ─[τ*]─► _) eq₂ post)
...     | r′ , equ , (ce₃ , cl₃ , pr₃ , rl₃ , dfix₃) =
          r′ , equ
          , allCellClass-trans (toSys r) (toSys r₁) (toSys r′) ce₁
              (allCellClass-trans (toSys r₁) (toSys r₂) (toSys r′) cemid ce₃)
          , allClientClass-trans (toSys r) (toSys r₁) (toSys r′) cl₁
              (allClientClass-trans (toSys r₁) (toSys r₂) (toSys r′) clmid cl₃)
          , allProdClass-trans (toSys r) (toSys r₁) (toSys r′) pr₁
              (allProdClass-trans (toSys r₁) (toSys r₂) (toSys r′) prmid pr₃)
          , allRelayClass-trans (toSys r) (toSys r₁) (toSys r′) rl₁
              (allRelayClass-trans (toSys r₁) (toSys r₂) (toSys r′) rlmid rl₃)
          , compose-DReport (toSys r) (toSys r₁) (toSys r₂) (toSys r′) dfix₁ drep dfix₃

------------------------------------------------------------------------
-- The GENUINE five-component leg-`l` report `PipeReport⁺-gen` and its weak-move
-- producer `liftReach-pipe⁺-gen` (mirror `PipeExposeReportAll.liftReach-pipe⁺`
-- but off the genuine classifiers — every FIXED component carries `≡`).
------------------------------------------------------------------------

PipeReport⁺-gen : TwoLegs → (s s′ : SysState) {X : Set 0ℓ} → Net_Api Payload X → X → Set₁
PipeReport⁺-gen l s s′ e a =
    DReport      s s′ e a
  × CellReport⁺   l s s′
  × ClientReport⁺ l s s′
  × ProdReport⁺   l s s′
  × RelayReport⁺  l s s′

-- HEADLINE: a weak api-CSBF move exposes the leg-`l` GENUINE five-component
-- report on ONE reflected successor `r′`
liftReach-pipe⁺-gen : (l : TwoLegs) (r : RState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {t′ : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ═[ ev (evl (evLabel X e a)) ]═► t′
  → Σ[ r′ ∈ RState ] (t′ ≡ radec r′) × PipeReport⁺-gen l (toSys r) (toSys r′) e a
liftReach-pipe⁺-gen l r aic apimem w with liftReach-gen r aic apimem w
... | r′ , eq , ce , cl , pr , rl , drep =
      r′ , eq ,
      ( drep
      , allCellClass⇒CellReport⁺     l (toSys r) (toSys r′) ce
      , allClientClass⇒ClientReport⁺ l (toSys r) (toSys r′) cl
      , allProdClass⇒ProdReport⁺     l (toSys r) (toSys r′) pr
      , allRelayClass⇒RelayReport⁺   l (toSys r) (toSys r′) rl
      )
