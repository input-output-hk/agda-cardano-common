{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the NODE PRODUCER exposure cone + τ-run
-- (`Praos.PipeExposeNodeProd`).
--
-- The BF-client counterpart `PipeExposeNodeClient` exposes, across a hidden
-- τ-run, how the leg's BF-client peers advance (`AllClientAdv`, read off the
-- reflected `s′` via the TOTAL `PipeExposeNode.adv-of`).  This module is the
-- PRODUCER counterpart: how the leg's node-A producer driver phase (`prodOf`, a
-- `ProdPh`) advances across the same τ-paddings — in particular the SEND
-- transition (`sendBFBlock`, `pp5 → pp6`) that fires the block onto the network
-- (`ProdSent`, the delivery gate the `PipeInv⁺` coupling reads upstream).
--
-- RECIPE ADAPTATION (as in session-8).  The frozen `WalkMeasure.ProdAdv` is the
-- STRICT single-step phase adjacency (`a01 … a89`), NOT total, so it cannot be
-- read off an arbitrary reflected successor.  We instead mirror
-- `PipeExposeNode.ClientAdv`: a permissive reflexive-transitive advance whose
-- one-step classifier `adv-of : (q q′) → ProdAdv q q′` is TOTAL (it flags
-- `pSent` exactly when the target phase satisfies the genuine `ProdSent`
-- property — sound and when-agnostic, the same soundness nuance as the client's
-- `cGetBlk`).  Because `WalkConvNodeFix.top-nodes-io-abs-fix` already reflects
-- the io-sync to a successor carrying the producer's concrete new phase, the
-- `ProdAdv` reads DIRECTLY off `s′` — `top-nodes-io-abs-prod` is a thin wrapper,
-- no per-peer bundle threading.
--
-- No postulate/hole/meta.  All base modules stay READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Nat using ( _<_ )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; cong₂; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeExposeNodeProd (blkA : Block₃) where

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
  using ( NetProc; absNodesOf; nodesOf; lift-med-whole-τ
        ; reflect-absDec-τ; innerτ; hidSync; reflect-inner-τ; medτ; nodesτ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode blkA
  using ( ProdPh; pp0; pp1; pp2; pp3; pp4; pp5; pp6; pp7; pp8; pp9 )
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
  using ( prodOf; ProdSent )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle blkA
  using ( IsApiCSBF )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.Walk blkA
  using ( μTot )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeExposeReach blkA
  using ( reach-ev-both )

------------------------------------------------------------------------
-- The producer phase-advance algebra.  `Prod1` is one legal single move of a
-- producer driver: either it reached a SENT phase (`pSent`, carrying the genuine
-- `ProdSent` property — the `sendBFBlock` gate), or it made some other move
-- (`pAdv`).  `ProdAdv` is its reflexive-transitive closure, so a whole hidden
-- run composes (mirror `PipeExposeNode.ClientAdv`).
------------------------------------------------------------------------

-- one legal producer move (target-classified: sent-gate vs other move)
data Prod1 : ProdPh → ProdPh → Set where
  pSent : ∀ {q q′} → ProdSent q′ → Prod1 q q′   -- reached a sent phase (block fired)
  pAdv  : ∀ {q q′} → Prod1 q q′                  -- some other move

-- the reflexive-transitive closure: a producer's phase across a whole run
data ProdAdv : ProdPh → ProdPh → Set where
  pl-refl : ∀ {q}     → ProdAdv q q
  pl-step : ∀ {q r s} → Prod1 q r → ProdAdv r s → ProdAdv q s

-- `ProdAdv` composes (transitive), so it threads across a τ-run
pl-trans : ∀ {q r s} → ProdAdv q r → ProdAdv r s → ProdAdv q s
pl-trans pl-refl          g = g
pl-trans (pl-step x rest) g = pl-step x (pl-trans rest g)

------------------------------------------------------------------------
-- The pure classify: any concrete successor phase yields a one-step `ProdAdv`
-- (a sent phase `pp6 … pp9` is flagged `pSent`; every other phase is `pAdv`).
-- Total on the successor — no weight bookkeeping needed.
------------------------------------------------------------------------

-- one producer move as a `ProdAdv`, classified by the concrete successor phase
adv-of : (q q′ : ProdPh) → ProdAdv q q′
adv-of q pp0 = pl-step pAdv pl-refl
adv-of q pp1 = pl-step pAdv pl-refl
adv-of q pp2 = pl-step pAdv pl-refl
adv-of q pp3 = pl-step pAdv pl-refl
adv-of q pp4 = pl-step pAdv pl-refl
adv-of q pp5 = pl-step pAdv pl-refl
adv-of q pp6 = pl-step (pSent tt) pl-refl
adv-of q pp7 = pl-step (pSent tt) pl-refl
adv-of q pp8 = pl-step (pSent tt) pl-refl
adv-of q pp9 = pl-step (pSent tt) pl-refl

------------------------------------------------------------------------
-- The whole-nodes producer report `AllProdAdv`: a `ProdAdv` for EACH of the two
-- `PipeInv`-tracked producer drivers (the two legs' producers — `prod-AB`/
-- `prod-AC` on node A).  Composes pointwise, refl-everywhere for a nodes-fixed
-- step; total-classifiable off any successor (`allProdAdv-of`).
------------------------------------------------------------------------

-- the two tracked producer drivers advance together
AllProdAdv : SysState → SysState → Set
AllProdAdv s s′ =
    ProdAdv (prodOf legBD s) (prodOf legBD s′)
  × ProdAdv (prodOf legCD s) (prodOf legCD s′)

-- reflexivity: a nodes-fixed step keeps every tracked producer (the frame case)
allProdAdv-refl : (s : SysState) → AllProdAdv s s
allProdAdv-refl s = pl-refl , pl-refl

-- transitivity (pointwise): compose two producer reports across a τ-run
allProdAdv-trans : (s s₁ s₂ : SysState)
                 → AllProdAdv s s₁ → AllProdAdv s₁ s₂ → AllProdAdv s s₂
allProdAdv-trans s s₁ s₂ (u₁ , v₁) (u₂ , v₂) =
    pl-trans u₁ u₂ , pl-trans v₁ v₂

-- TOTAL classify: any successor state yields an `AllProdAdv`, reading each
-- tracked producer's `ProdAdv` off the concrete successor phase (`adv-of`).
allProdAdv-of : (s s′ : SysState) → AllProdAdv s s′
allProdAdv-of s s′ =
    adv-of (prodOf legBD s) (prodOf legBD s′)
  , adv-of (prodOf legCD s) (prodOf legCD s′)

------------------------------------------------------------------------
-- TOP: the whole-nodes io-sync PRODUCER exposure (`top-nodes-io-abs-prod`).  A
-- thin wrapper over the frozen `top-nodes-io-abs-fix`: it reuses the reflected
-- successor state `s′`, the `med`-fixity, the `M ≡ absNodesOf s′` equation and
-- the `nodesOf` weak run VERBATIM, and attaches the `AllProdAdv` read off `s′`
-- via the total `allProdAdv-of` (the six driver fixities are discarded — the
-- producer's own fixity is subsumed by the more permissive `ProdAdv`).
------------------------------------------------------------------------

top-nodes-io-abs-prod : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ s′ ∈ SysState ] (med s ≡ med s′) × (M ≡ absNodesOf s′)
      × (nodesOf s ═[ ev (evl (evLabel X e a)) ]═► nodesOf s′)
      × AllProdAdv s s′
top-nodes-io-abs-prod s iomem step with top-nodes-io-abs-fix s iomem step
... | s′ , meq , Meq , wrun , _ , _ , _ , _ , _ , _ =
      s′ , meq , Meq , wrun , allProdAdv-of s s′

------------------------------------------------------------------------
-- MEDIUM-τ reflector with the producer report (mirror
-- `PipeExposeNodeClient.τreflect-med-client`, LIGHT — medium-only τ lift): a
-- medium drain moves NO node, so every tracked producer is fixed
-- (`allProdAdv-refl`).
------------------------------------------------------------------------

τreflect-med-prod : (r : RState) {M M′ : NetProc}
    (ms  : decMed (med (toSys r)) ─[ τ ]─► M′)
    (Meq : M ≡ ((M′ ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × AllProdAdv (toSys r) (toSys r′)
τreflect-med-prod r {M} {M′} ms Meq with medium-τ-inv-wt (med (toSys r)) ms
... | i , d₀ , id₀ , _ , _ , M′≡ = r′ , Meq′ , allProdAdv-refl (toSys r)
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
-- io-SYNC reflector with the producer report (RAM-heavy — mirror
-- `PipeExposeNodeClient.τreflect-io-client`, but using `top-nodes-io-abs-prod`
-- for the node side).  The medium side (setting one cell) is rebuilt through
-- `lift-io-sync-whole-wτ` exactly as the frozen module does; the producer report
-- comes off the reflected `s″`.
------------------------------------------------------------------------

τreflect-io-prod : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M₁ N₁ M : NetProc}
    (iomem : ioES .mem (X , e) a)
    (sM : decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► M₁)
    (sN : absNodesOf (toSys r)   ─[ ev (evl (evLabel X e a)) ]─► N₁)
    (Meq : M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × AllProdAdv (toSys r) (toSys r′)
τreflect-io-prod r {X} {e} {a} {M₁} {N₁} {M} iomem sM sN Meq
    with medium-ev-inv-wt (med (toSys r)) iomem sM
       | top-nodes-io-abs-prod (toSys r) iomem sN
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
-- TOTAL per-τ reflector with the producer report (mirror
-- `PipeExposeNodeClient.τreflect-client`): dispatch a hidden τ to the medium-τ
-- drain reflector or the io-sync reflector (nodes-τ refuted by `absNodesOf-no-τ`).
------------------------------------------------------------------------

τreflect-prod : (r : RState) {M : NetProc} → radec r ─[ τ ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × AllProdAdv (toSys r) (toSys r′)
τreflect-prod r step with reflect-absDec-τ (toSys r) step
... | innerτ P′ innerStep Peq
    with reflect-inner-τ (decMed (med (toSys r))) (absNodesOf (toSys r)) innerStep
...   | medτ   M′ ms eqP = τreflect-med-prod r ms (trans Peq (cong (λ z → z ∖ ioES) eqP))
...   | nodesτ N′ ns eqP = ⊥-elim (absNodesOf-no-τ (toSys r) ns)
τreflect-prod r step | hidSync M₁ N₁ iomem sM sN Peq = τreflect-io-prod r iomem sM sN Peq

------------------------------------------------------------------------
-- τ-run lift with the producer report (mirror
-- `PipeExposeNodeClient.liftτ*-client`): fold the per-τ producer reports across
-- a whole hidden τ-run by pointwise `ProdAdv` composition.
------------------------------------------------------------------------

liftτ*-prod′ : (r : RState) {start u : NetProc} → start ≡ radec r
          → start ─[τ*]─► u
          → Σ[ r′ ∈ RState ] (u ≡ radec r′) × AllProdAdv (toSys r) (toSys r′)
liftτ*-prod′ r eq τ*-refl = r , eq , allProdAdv-refl (toSys r)
liftτ*-prod′ r eq (τ*-step s rest) with τreflect-prod r (subst (λ z → z ─[ τ ]─► _) eq s)
... | r₁ , eq₁ , rep₁ with liftτ*-prod′ r₁ eq₁ rest
...   | r′ , equ , rep′ =
        r′ , equ , allProdAdv-trans (toSys r) (toSys r₁) (toSys r′) rep₁ rep′

liftτ*-prod : (r : RState) {u : NetProc}
         → radec r ─[τ*]─► u
         → Σ[ r′ ∈ RState ] (u ≡ radec r′) × AllProdAdv (toSys r) (toSys r′)
liftτ*-prod r = liftτ*-prod′ r refl

------------------------------------------------------------------------
-- The leg-`l` `ProdReport`: instantiate `AllProdAdv` at the leg's producer
-- driver (`prodOf`) — the PRODUCER component of the seven-component
-- `PipeReport`, the node counterpart of `CellReport`/`ClientReport`.
------------------------------------------------------------------------

-- how the leg-`l` producer driver moves across a τ-run
ProdReport : TwoLegs → SysState → SysState → Set
ProdReport l s s′ = ProdAdv (prodOf l s) (prodOf l s′)

-- project the whole-nodes report onto the leg producer
allProdAdv⇒ProdReport : (l : TwoLegs) (s s′ : SysState)
                      → AllProdAdv s s′ → ProdReport l s s′
allProdAdv⇒ProdReport legBD s s′ (uBD , uCD) = uBD
allProdAdv⇒ProdReport legCD s s′ (uBD , uCD) = uCD

-- HEADLINE (τ-run half of the leg `ProdReport`): a hidden τ-run exposes the
-- leg-`l` producer driver's phase delta (a `ProdAdv`, sent-gate flagged)
liftτ*-prodReport : (l : TwoLegs) (r : RState) {u : NetProc}
                  → radec r ─[τ*]─► u
                  → Σ[ r′ ∈ RState ] (u ≡ radec r′) × ProdReport l (toSys r) (toSys r′)
liftτ*-prodReport l r run with liftτ*-prod r run
... | r′ , eq , apr = r′ , eq , allProdAdv⇒ProdReport l (toSys r) (toSys r′) apr

------------------------------------------------------------------------
-- The strong-visible api middle WITH the producer report on the SAME `r′`
-- (mirror `PipeExposeReachClient.reach-ev-client`, but for the producer driver).
-- Reuses `reach-ev-both`'s reflected successor `r′` and reads `AllProdAdv` off
-- it via the total `allProdAdv-of` — no per-peer node cone.
------------------------------------------------------------------------

reach-ev-prod : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′)
      × (rdec r ═[ ev (evl (evLabel X e a)) ]═► rdec r′)
      × (μTot (toSys r′) < μTot (toSys r)) × AllProdAdv (toSys r) (toSys r′)
reach-ev-prod r aic apimem step with reach-ev-both r aic apimem step
... | r′ , Mr , wr , drop , _ , _ = r′ , Mr , wr , drop , allProdAdv-of (toSys r) (toSys r′)

-- the leg-`l` projection of the visible-middle producer frame
reach-ev-prodReport : (l : TwoLegs) (r : RState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′)
      × (rdec r ═[ ev (evl (evLabel X e a)) ]═► rdec r′)
      × (μTot (toSys r′) < μTot (toSys r)) × ProdReport l (toSys r) (toSys r′)
-- NB `let`-destructuring, NOT `with`: in this `(blkA : Block₃)`-parameterised
-- module a `with` abstracts the block out of the imported `PipeInv.prodOf`
-- copy and the abstracted goal stops converting.
reach-ev-prodReport l r aic apimem step =
  let (r′ , Mr , wr , drop , apr) = reach-ev-prod r aic apimem step
  in  r′ , Mr , wr , drop , allProdAdv⇒ProdReport l (toSys r) (toSys r′) apr
