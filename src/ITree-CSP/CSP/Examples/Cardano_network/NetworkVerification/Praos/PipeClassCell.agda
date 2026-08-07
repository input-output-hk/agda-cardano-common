{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the GENUINE Fix/Adv CELL CLASSIFIER
-- (`Praos.PipeClassCell`).
--
-- `PipeExposeCell` built a PERMISSIVE cell report: a `CellAdv` (reflexive-
-- transitive closure of `Cell1`) for every cell, ALWAYS an advance — it never
-- carries the propositional `≡` that a `PipeStep⁺` constructor needs on a FIXED
-- cell, and it cannot DECIDE which cells actually moved (session-10 D2/D3 gap).
--
-- This module reshapes the cell report into the `WalkDExpose.DReport` SHAPE: a
-- per-cell sum `CellClass1` with a `clcFix` case carrying `a ≡ b` and a `clcAdv`
-- case carrying the concrete `CellAdv`, DECIDED by inverting the fired event
-- against the cell key.  The decision is CLEAN for the cell because the R2
-- medium inversions (`medium-τ-inv-wt`/`medium-ev-inv-wt`) expose the CONCRETE
-- touched cell key `(i,d₀,id₀)`; `with kl ≟ i` reduces the buried `phase-upd`, so
-- a non-touched cell literally reduces to its source phase (`clcFix refl`) and a
-- touched cell advances (`clcAdv`).  On the visible api-CSBF middle the medium is
-- a solo pass-through (`med s ≡ med s′`), so every cell is fixed.
--
-- Reuses the `Cell1`/`CellAdv` algebra + the io/medium reflector structure from
-- `PipeExposeCell` and the api middle cone of `PipeExposeReach` VERBATIM; only
-- the report content is replaced by the decision.  No postulate/hole/meta.  All
-- base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Nat using ( ℕ; zero; suc; _<_ )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( inj₁ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Relation.Nullary using ( yes; no )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; cong₂; subst )

open import Process_Trees using ( PTree; ExtI )

open import Class.DecEq using ( DecEq; _≟_ )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeClassCell (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; apiES; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟; Link )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using ( Dir; IDs; hi; N2N_BlockFetch )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _∖_; _⦀_; EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; τ; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wev; wτ )

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysDecode blkA
  using ( SysState; mkSys; med; nA; nB; nC; nD; ⟦_⟧ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysMedium blkA
  using ( CopyPhase; empty; full; draining; MedState; mkMed; phase; broken; decMed )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep blkA
  using ( NetProc; absDec; absNodesOf; nodesOf; lift-med-whole-τ
        ; medEv; nodesEv; reflect-top-ev; lift-med-whole-ev
        ; reflect-absDec-τ; innerτ; hidSync; reflect-inner-τ; medτ; nodesτ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysReach blkA
  using ( RState; mkR; radec; toSys; rdec; reach; Reachable; rcloseʷ; rcloseʷ-abs )
open Reachable using ( rStepʷ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle blkA
  using ( IsApiCSBF )
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysRoute blkA as SR
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvTauInv blkA
  using ( medium-τ-inv-wt )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvEvInv blkA
  using ( medium-ev-inv-wt )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvNodeFix blkA
  using ( top-nodes-io-abs-fix )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysBisim blkA
  using ( lift-io-sync-whole-wτ; lift-nodes-whole-wev )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_GapBDisj blkA
  using ( noOffer→viewV )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvMeasure blkA
  using ( cellWt )
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_TauCore blkA as STC
open STC using ( phase-upd; flipCell )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_NodeTauEv blkA
  using ( setCell; absNodesOf-no-τ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.Walk blkA
  using ( μTot )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkPr blkA
  using ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeInv blkA
  using ( cellUp; cellDn )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkDExpose blkA
  using ( top-nodes-abs-expose )

-- REUSE the cell-delta algebra + the set-advance lemma from the permissive module
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeExposeCell blkA
  using ( Cell1; cFix; cFill; cOut; cDrn
        ; CellAdv; ca-refl; ca-step; ca-trans; cellAt; cell-set-adv )

------------------------------------------------------------------------
-- The genuine per-cell CLASSIFIER `CellClass1` (the `DReport` shape for a
-- single cell): either the cell is FIXED (a propositional `≡`, the datum a
-- `PipeStep⁺` core needs) or it ADVANCED (a concrete `CellAdv`).
------------------------------------------------------------------------

-- one cell's classification across a step/run: fixed-with-proof, or advanced
data CellClass1 (a b : CopyPhase) : Set where
  clcFix : a ≡ b     → CellClass1 a b
  clcAdv : CellAdv a b → CellClass1 a b

-- compose two classifications (a τ-run fold): fixed∘fixed stays fixed (with the
-- transitive `≡`), anything touching an advance becomes an advance
ccFold : ∀ {a b c} → CellClass1 a b → CellClass1 b c → CellClass1 a c
ccFold             (clcFix p) (clcFix q) = clcFix (trans p q)
ccFold {a} {b} {c} (clcFix p) (clcAdv g) = clcAdv (subst (λ z → CellAdv z c) (sym p) g)
ccFold {a} {b} {c} (clcAdv f) (clcFix q) = clcAdv (subst (CellAdv a) q f)
ccFold             (clcAdv f) (clcAdv g) = clcAdv (ca-trans f g)

------------------------------------------------------------------------
-- The whole-medium classifier `AllCellClass`: a `CellClass1` for EVERY cell
-- key (the generalisation of `DReport`'s per-component decision to all cells).
------------------------------------------------------------------------

-- every medium cell is classified fixed-or-advanced
AllCellClass : SysState → SysState → Set
AllCellClass s s′ = (kl : Link) (kd : Dir) (kid : IDs)
                  → CellClass1 (cellAt kl kd kid s) (cellAt kl kd kid s′)

-- reflexivity: a step that fixes the whole medium classifies every cell fixed
allCellClass-refl : (s : SysState) → AllCellClass s s
allCellClass-refl s kl kd kid = clcFix refl

-- transitivity (pointwise fold): compose two classifiers across a τ-run
allCellClass-trans : (s s₁ s₂ : SysState)
                   → AllCellClass s s₁ → AllCellClass s₁ s₂ → AllCellClass s s₂
allCellClass-trans s s₁ s₂ f g kl kd kid = ccFold (f kl kd kid) (g kl kd kid)

-- a medium-fixed step (`med s ≡ med s′`) classifies every cell FIXED, the
-- proof read off the medium equality (the visible-api-middle frame case)
allCellClass-medEq : (s s′ : SysState) → med s ≡ med s′ → AllCellClass s s′
allCellClass-medEq s s′ meq kl kd kid = clcFix (cong (λ m → phase m kl kd kid) meq)

------------------------------------------------------------------------
-- The two pure per-cell read-classifiers: invert the fired cell key against an
-- arbitrary key.  `with kl ≟ i` reduces the buried `phase-upd`, so a non-touched
-- cell literally reduces to its source phase (`clcFix refl`) and the touched
-- cell advances (`clcAdv`).  Exact analogue of `PipeExposeCell.cell-{drain,fill}
-- -read` but returning the DECISION instead of an always-advance.
------------------------------------------------------------------------

-- MEDIUM-τ read: a drain flips key `(i,d₀,id₀)` `draining x → empty`; every
-- other cell is FIXED (`clcFix refl`, the guard having reduced `phase-upd`).
cell-drain-class : (m : MedState) (i : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
                → phase m i d₀ id₀ ≡ draining x
                → (kl : Link) (kd : Dir) (kid : IDs)
                → CellClass1 (phase m kl kd kid)
                             (phase-upd (phase m) i (flipCell (phase m i) d₀ id₀) kl kd kid)
cell-drain-class m i d₀ id₀ x drainEq kl kd kid with kl ≟ i
... | no ¬p = clcFix refl
cell-drain-class m i d₀ id₀ x drainEq kl kd kid | yes refl with kd ≟ d₀ | kid ≟ id₀
... | yes refl | yes refl rewrite drainEq = clcAdv (ca-step cDrn ca-refl)
... | no ¬p | _ = clcFix refl
... | yes refl | no ¬p = clcFix refl

-- io-SYNC read: a fill/output sets key `(i,d₀,id₀)` to `np` with `cellWt np ≡
-- suc (cellWt old)`; every other cell is FIXED (`clcFix refl`).
cell-fill-class : (m : MedState) (i : Link) (d₀ : Dir) (id₀ : IDs) (np : CopyPhase)
               → cellWt np ≡ suc (cellWt (phase m i d₀ id₀))
               → (kl : Link) (kd : Dir) (kid : IDs)
               → CellClass1 (phase m kl kd kid)
                            (phase-upd (phase m) i (setCell (phase m i) d₀ id₀ np) kl kd kid)
cell-fill-class m i d₀ id₀ np wtEq kl kd kid with kl ≟ i
... | no ¬p = clcFix refl
cell-fill-class m i d₀ id₀ np wtEq kl kd kid | yes refl with kd ≟ d₀ | kid ≟ id₀
... | yes refl | yes refl = clcAdv (ca-step (cell-set-adv (phase m i d₀ id₀) np wtEq) ca-refl)
... | no ¬p | _ = clcFix refl
... | yes refl | no ¬p = clcFix refl

------------------------------------------------------------------------
-- MEDIUM-τ reflector with the classifier (mirror `PipeExposeCell.τreflect-med
-- -cell`, LIGHT): the drained cell advances, every other cell fixed.
------------------------------------------------------------------------

τreflect-med-classcell : (r : RState) {M M′ : NetProc}
    (ms  : decMed (med (toSys r)) ─[ τ ]─► M′)
    (Meq : M ≡ ((M′ ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × AllCellClass (toSys r) (toSys r′)
τreflect-med-classcell r {M} {M′} ms Meq with medium-τ-inv-wt (med (toSys r)) ms
... | i , d₀ , id₀ , x , drainEq , M′≡ = r′ , Meq′ , report
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
    report : AllCellClass (toSys r) (toSys r′)
    report kl kd kid = cell-drain-class (med (toSys r)) i d₀ id₀ x drainEq kl kd kid

------------------------------------------------------------------------
-- io-SYNC reflector with the classifier (RAM-heavy — mirror `PipeExposeCell.
-- τreflect-io-cell`): the filled/output cell advances, every other cell fixed.
------------------------------------------------------------------------

τreflect-io-classcell : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M₁ N₁ M : NetProc}
    (iomem : ioES .mem (X , e) a)
    (sM : decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► M₁)
    (sN : absNodesOf (toSys r)   ─[ ev (evl (evLabel X e a)) ]─► N₁)
    (Meq : M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × AllCellClass (toSys r) (toSys r′)
τreflect-io-classcell r {X} {e} {a} {M₁} {N₁} {M} iomem sM sN Meq
    with medium-ev-inv-wt (med (toSys r)) iomem sM
       | top-nodes-io-abs-fix (toSys r) iomem sN
... | i , d₀ , id₀ , np , wtEq , M₁≡ | s″ , _ , N₁≡ , cWeakRun , _ , _ , _ , _ , _ , _ =
      r′ , Meq′ , report
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
    report : AllCellClass (toSys r) (toSys r′)
    report kl kd kid = cell-fill-class (med (toSys r)) i d₀ id₀ np wtEq kl kd kid

------------------------------------------------------------------------
-- TOTAL per-τ reflector with the classifier (mirror `PipeExposeCell.τreflect
-- -cell`): dispatch to the medium-τ drain reflector or the io-sync reflector.
------------------------------------------------------------------------

τreflect-classcell : (r : RState) {M : NetProc} → radec r ─[ τ ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × AllCellClass (toSys r) (toSys r′)
τreflect-classcell r step with reflect-absDec-τ (toSys r) step
... | innerτ P′ innerStep Peq
    with reflect-inner-τ (decMed (med (toSys r))) (absNodesOf (toSys r)) innerStep
...   | medτ   M′ ms eqP = τreflect-med-classcell r ms (trans Peq (cong (λ z → z ∖ ioES) eqP))
...   | nodesτ N′ ns eqP = ⊥-elim (absNodesOf-no-τ (toSys r) ns)
τreflect-classcell r step | hidSync M₁ N₁ iomem sM sN Peq = τreflect-io-classcell r iomem sM sN Peq

------------------------------------------------------------------------
-- τ-run lift with the classifier (mirror `PipeExposeCell.liftτ*-cell`): fold
-- the per-τ classifiers across a whole hidden τ-run.
------------------------------------------------------------------------

liftτ*-classcell′ : (r : RState) {start u : NetProc} → start ≡ radec r
          → start ─[τ*]─► u
          → Σ[ r′ ∈ RState ] (u ≡ radec r′) × AllCellClass (toSys r) (toSys r′)
liftτ*-classcell′ r eq τ*-refl = r , eq , allCellClass-refl (toSys r)
liftτ*-classcell′ r eq (τ*-step s rest) with τreflect-classcell r (subst (λ z → z ─[ τ ]─► _) eq s)
... | r₁ , eq₁ , rep₁ with liftτ*-classcell′ r₁ eq₁ rest
...   | r′ , equ , rep′ =
        r′ , equ , allCellClass-trans (toSys r) (toSys r₁) (toSys r′) rep₁ rep′

liftτ*-classcell : (r : RState) {u : NetProc}
         → radec r ─[τ*]─► u
         → Σ[ r′ ∈ RState ] (u ≡ radec r′) × AllCellClass (toSys r) (toSys r′)
liftτ*-classcell r = liftτ*-classcell′ r refl

------------------------------------------------------------------------
-- VISIBLE api-CSBF MIDDLE with the classifier (RAM-heavy — re-mirror
-- `PipeExposeReach.reach-ev-both`): an api middle is a NODE hand-off, so the
-- medium is a solo pass-through (`med s ≡ med s′`) and EVERY cell is FIXED.
------------------------------------------------------------------------

reach-ev-classcell : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′)
      × (rdec r ═[ ev (evl (evLabel X e a)) ]═► rdec r′)
      × (μTot (toSys r′) < μTot (toSys r)) × AllCellClass (toSys r) (toSys r′)
reach-ev-classcell r {X} {e} {a} aic apimem step
    with reflect-top-ev (decMed (med (toSys r))) (absNodesOf (toSys r))
           (inj₁ (SR.medium-api-non-offer (med (toSys r)) aic)) step
... | medEv M₁ ms _   = ⊥-elim (SR.medium-api-non-offer (med (toSys r)) aic (M₁ , ms))
... | nodesEv N₁ ns refl with top-nodes-abs-expose (toSys r) apimem ns
...   | s′ , medEq , N₁≡ , cWeakRun , drop , _ =
        r′ , Mr , wr , drop , allCellClass-medEq (toSys r) s′ medEq
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
-- The leg-`l` `CellReport⁺`: instantiate `AllCellClass` at the two leg cells
-- (`cellUp`/`cellDn`).  This is the genuine (Fix/Adv) CELL component of the
-- reshaped `PipeReport`, feeding a `PipeStep⁺` core's `cellUp`/`cellDn` needs.
------------------------------------------------------------------------

-- how the leg-`l` upstream + downstream cells are CLASSIFIED across a step/run
CellReport⁺ : TwoLegs → SysState → SysState → Set
CellReport⁺ l s s′ =
    CellClass1 (cellUp l s) (cellUp l s′) × CellClass1 (cellDn l s) (cellDn l s′)

-- project the whole-medium classifier onto the two leg cells (keys are defeq)
allCellClass⇒CellReport⁺ : (l : TwoLegs) (s s′ : SysState)
                         → AllCellClass s s′ → CellReport⁺ l s s′
allCellClass⇒CellReport⁺ legBD s s′ f =
  f linkAB hi N2N_BlockFetch , f linkBD hi N2N_BlockFetch
allCellClass⇒CellReport⁺ legCD s s′ f =
  f linkAC hi N2N_BlockFetch , f linkCD hi N2N_BlockFetch

-- HEADLINE (τ-run half): a hidden τ-run CLASSIFIES the leg-`l` cells (fixed
-- with `≡`, or advanced) — the datum a `PipeStep⁺` cell core consumes
liftτ*-cellReport⁺ : (l : TwoLegs) (r : RState) {u : NetProc}
                  → radec r ─[τ*]─► u
                  → Σ[ r′ ∈ RState ] (u ≡ radec r′) × CellReport⁺ l (toSys r) (toSys r′)
liftτ*-cellReport⁺ l r run with liftτ*-classcell r run
... | r′ , eq , acc = r′ , eq , allCellClass⇒CellReport⁺ l (toSys r) (toSys r′) acc

-- HEADLINE (visible-middle half): the api-CSBF middle CLASSIFIES both leg cells
-- FIXED (medium solo pass-through)
reach-ev-cellReport⁺ : (l : TwoLegs) (r : RState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′)
      × (rdec r ═[ ev (evl (evLabel X e a)) ]═► rdec r′)
      × (μTot (toSys r′) < μTot (toSys r)) × CellReport⁺ l (toSys r) (toSys r′)
reach-ev-cellReport⁺ l r aic apimem step with reach-ev-classcell r aic apimem step
... | r′ , Mr , wr , drop , acc =
      r′ , Mr , wr , drop , allCellClass⇒CellReport⁺ l (toSys r) (toSys r′) acc
