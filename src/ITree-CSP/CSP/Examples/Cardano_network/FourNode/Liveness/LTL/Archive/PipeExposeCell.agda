{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the CELL-DELTA exposure companion to `WalkTauExpose`
-- (`Praos.PipeExposeCell`).
--
-- `WalkTauExpose.liftτ*-expose` exposes, across a hidden τ-run, that nD's two
-- D-consume phases are FIXED (`DFix`).  The `PipeStep⁺` classifier additionally
-- needs to know how the leg-`l` MEDIUM CELLS move across the same τ-paddings —
-- the block travels through those cells (`empty → full → draining → empty`), so
-- they are the FIRST of the seven `PipeReport` components that are NOT fixed.
--
-- This module builds the analog of `DFix` for `SysMedium.phase`, GENERALISED to
-- EVERY medium cell (`AllCellAdv`), from which the two leg-`l` cells derive by
-- instantiation.  A single medium/io τ moves at most one cell by one cyclic
-- advance (`Cell1`); a τ-run composes them (`CellAdv`, the reflexive-transitive
-- closure).  The medium-τ reflector `τreflect-med-cell` (the DRAIN
-- `draining x → empty`) is here (LIGHT — reuses only the frozen medium-τ
-- inversion + the medium-only lift).  The io-sync reflector (the FILL/OUTPUT
-- `empty → full → draining`, RAM-heavy — it rebuilds the io-sync reachability)
-- and the τ-run fold live in later pieces.
--
-- The two pure per-cell read lemmas `cell-drain-read` (medium-τ) and
-- `cell-fill-read` (io-sync) are BOTH light and both here: they translate the
-- R2 medium inversions' `flipCell`/`setCell` phase updates into a `CellAdv` for
-- an arbitrary cell key.  No postulate/hole/meta.  All base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Nat using ( ℕ; zero; suc )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Relation.Nullary using ( yes; no )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; cong₂; subst; subst₂ )

open import Process_Trees using ( PTree; ExtI )

open import Class.DecEq using ( DecEq; _≟_ )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Archive.PipeExposeCell (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟; Link )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using ( Dir; IDs; hi; N2N_BlockFetch )
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
  using ( CopyPhase; empty; full; draining; MedState; mkMed; phase; broken; decMed )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
  using ( absNodesOf; nodesOf; lift-med-whole-τ
        ; reflect-absDec-τ; innerτ; hidSync; reflect-inner-τ; medτ; nodesτ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( NetProc; RState; mkR; radec; toSys; rdec; reach; Reachable )
open Reachable using ( rStepʷ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvTauInv blkA
  using ( medium-τ-inv-wt )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvEvInv blkA
  using ( medium-ev-inv-wt )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvNodeFix blkA
  using ( top-nodes-io-abs-fix )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysBisim blkA
  using ( lift-io-sync-whole-wτ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvMeasure blkA
  using ( cellWt )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_TauCore blkA as STC
open STC using ( phase-upd; flipCell )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( setCell; absNodesOf-no-τ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( cellUp; cellDn )

------------------------------------------------------------------------
-- The cell-delta algebra.  `Cell1` is one legal single-τ-step effect on a cell
-- (the phase-class cycle `empty → full → draining → empty`, tracking WEIGHT not
-- payload — the R2 inversions only expose the weight).  `CellAdv` is its
-- reflexive-transitive closure (a τ-run walks the cycle some number of steps).
------------------------------------------------------------------------

-- a single legal cell transition: unchanged, a fill (input), an output, or a
-- drain (medium τ).  fill/output/drain are payload-agnostic (weight cycle 0→1→2→0)
data Cell1 : CopyPhase → CopyPhase → Set where
  cFix  : ∀ {c}   → Cell1 c c
  cFill : ∀ {y}   → Cell1 empty (full y)
  cOut  : ∀ {y z} → Cell1 (full y) (draining z)
  cDrn  : ∀ {z}   → Cell1 (draining z) empty

-- the reflexive-transitive closure: a cell's phase across a whole τ-run
data CellAdv : CopyPhase → CopyPhase → Set where
  ca-refl : ∀ {c}     → CellAdv c c
  ca-step : ∀ {a b c} → Cell1 a b → CellAdv b c → CellAdv a c

-- `CellAdv` composes (transitive), so it threads across a τ-run
ca-trans : ∀ {a b c} → CellAdv a b → CellAdv b c → CellAdv a c
ca-trans ca-refl          g = g
ca-trans (ca-step s rest) g = ca-step s (ca-trans rest g)

-- read one medium cell's phase at a fixed key of a state
cellAt : Link → Dir → IDs → SysState → CopyPhase
cellAt kl kd kid s = phase (med s) kl kd kid

-- the whole-medium cell report: EVERY cell either fixed or one cyclic advance
-- (the generalisation of `DFix` to all medium cells; composes pointwise)
AllCellAdv : SysState → SysState → Set
AllCellAdv s s′ = (kl : Link) (kd : Dir) (kid : IDs)
                → CellAdv (cellAt kl kd kid s) (cellAt kl kd kid s′)

-- reflexivity: a medium-fixed step keeps every cell (the frame case)
allCellAdv-refl : (s : SysState) → AllCellAdv s s
allCellAdv-refl s kl kd kid = ca-refl

-- transitivity (pointwise): compose two cell reports across a τ-run
allCellAdv-trans : (s s₁ s₂ : SysState)
                 → AllCellAdv s s₁ → AllCellAdv s₁ s₂ → AllCellAdv s s₂
allCellAdv-trans s s₁ s₂ f g kl kd kid = ca-trans (f kl kd kid) (g kl kd kid)

------------------------------------------------------------------------
-- Hit/miss reductions for the two R2 medium phase updates `phase-upd` (link
-- level) and `flipCell`/`setCell` (cell level).  Each re-does the definition's
-- `_≟_`-`with` so Agda reduces the stuck guard.
------------------------------------------------------------------------

-- `phase-upd` at its own link returns the new cell row
phase-upd-hit : (ph : Link → Dir → IDs → CopyPhase) (i : Link)
                (g : Dir → IDs → CopyPhase) (d : Dir) (id : IDs)
              → phase-upd ph i g i d id ≡ g d id
phase-upd-hit ph i g d id with i ≟ i
... | yes _  = refl
... | no ¬p  = ⊥-elim (¬p refl)

-- `phase-upd` is the identity away from its link
phase-upd-miss : (ph : Link → Dir → IDs → CopyPhase) (i : Link)
                 (g : Dir → IDs → CopyPhase) (l : Link) → (l ≡ i → ⊥)
               → (d : Dir) (id : IDs)
               → phase-upd ph i g l d id ≡ ph l d id
phase-upd-miss ph i g l l≢i d id with l ≟ i
... | yes p  = ⊥-elim (l≢i p)
... | no _   = refl

-- `flipCell` at its own cell key gives `empty`
flipCell-hit : (g : Dir → IDs → CopyPhase) (d₀ : Dir) (id₀ : IDs)
             → flipCell g d₀ id₀ d₀ id₀ ≡ empty
flipCell-hit g d₀ id₀ with d₀ ≟ d₀ | id₀ ≟ id₀
... | yes _  | yes _  = refl
... | yes _  | no ¬p  = ⊥-elim (¬p refl)
... | no ¬p  | _      = ⊥-elim (¬p refl)

-- `flipCell` is the identity away from its cell key (direction mismatch)
flipCell-miss-d : (g : Dir → IDs → CopyPhase) (d₀ : Dir) (id₀ : IDs) (d : Dir) (id : IDs)
                → (d ≡ d₀ → ⊥) → flipCell g d₀ id₀ d id ≡ g d id
flipCell-miss-d g d₀ id₀ d id d≢ with d ≟ d₀ | id ≟ id₀
... | no _    | _     = refl
... | yes p   | _     = ⊥-elim (d≢ p)

-- `flipCell` is the identity away from its cell key (id mismatch)
flipCell-miss-id : (g : Dir → IDs → CopyPhase) (d₀ : Dir) (id₀ : IDs) (d : Dir) (id : IDs)
                 → (id ≡ id₀ → ⊥) → flipCell g d₀ id₀ d id ≡ g d id
flipCell-miss-id g d₀ id₀ d id id≢ with d ≟ d₀ | id ≟ id₀
... | no _    | _      = refl
... | yes _   | no _   = refl
... | yes _   | yes p  = ⊥-elim (id≢ p)

-- `setCell` at its own cell key returns the new phase
setCell-hit : (g : Dir → IDs → CopyPhase) (d₀ : Dir) (id₀ : IDs) (np : CopyPhase)
            → setCell g d₀ id₀ np d₀ id₀ ≡ np
setCell-hit g d₀ id₀ np with d₀ ≟ d₀ | id₀ ≟ id₀
... | yes _  | yes _  = refl
... | yes _  | no ¬p  = ⊥-elim (¬p refl)
... | no ¬p  | _      = ⊥-elim (¬p refl)

-- `setCell` is the identity away from its cell key (direction mismatch)
setCell-miss-d : (g : Dir → IDs → CopyPhase) (d₀ : Dir) (id₀ : IDs) (np : CopyPhase)
                 (d : Dir) (id : IDs)
               → (d ≡ d₀ → ⊥) → setCell g d₀ id₀ np d id ≡ g d id
setCell-miss-d g d₀ id₀ np d id d≢ with d ≟ d₀ | id ≟ id₀
... | no _    | _     = refl
... | yes p   | _     = ⊥-elim (d≢ p)

-- `setCell` is the identity away from its cell key (id mismatch)
setCell-miss-id : (g : Dir → IDs → CopyPhase) (d₀ : Dir) (id₀ : IDs) (np : CopyPhase)
                  (d : Dir) (id : IDs)
                → (id ≡ id₀ → ⊥) → setCell g d₀ id₀ np d id ≡ g d id
setCell-miss-id g d₀ id₀ np d id id≢ with d ≟ d₀ | id ≟ id₀
... | no _    | _      = refl
... | yes _   | no _   = refl
... | yes _   | yes p  = ⊥-elim (id≢ p)

------------------------------------------------------------------------
-- The two pure per-cell read lemmas: translate one medium inversion's phase
-- update into a `CellAdv` for an arbitrary key.  Both are LIGHT.
------------------------------------------------------------------------

-- a set cell advances by exactly one weight ⇒ exactly one `Cell1` move.  The
-- `draining`-source case is impossible (weight would exceed 2); the mismatched
-- weight combinations are refuted by the ℕ equality.
cell-set-adv : (src np : CopyPhase) → cellWt np ≡ suc (cellWt src) → Cell1 src np
cell-set-adv empty        (full y)     eq = cFill
cell-set-adv empty        empty        ()
cell-set-adv empty        (draining z) ()
cell-set-adv (full y)     (draining z) eq = cOut
cell-set-adv (full y)     empty        ()
cell-set-adv (full y)     (full z)     ()
cell-set-adv (draining z) empty        ()
cell-set-adv (draining z) (full y)     ()
cell-set-adv (draining z) (draining y) ()

-- MEDIUM-τ per-cell read: a drain flips one key `(i,d₀,id₀)` from `draining x`
-- to `empty`; every other cell is fixed.  For an ARBITRARY key `(kl,kd,kid)`
-- this yields the `CellAdv` from the source phase to the `flipCell`-updated one.
cell-drain-read : (m : MedState) (i : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
                → phase m i d₀ id₀ ≡ draining x
                → (kl : Link) (kd : Dir) (kid : IDs)
                → CellAdv (phase m kl kd kid)
                          (phase-upd (phase m) i (flipCell (phase m i) d₀ id₀) kl kd kid)
cell-drain-read m i d₀ id₀ x drainEq kl kd kid with kl ≟ i
... | no ¬p = ca-refl
cell-drain-read m i d₀ id₀ x drainEq kl kd kid | yes refl with kd ≟ d₀ | kid ≟ id₀
... | yes refl | yes refl rewrite drainEq = ca-step cDrn ca-refl
... | no ¬p | _ = ca-refl
... | yes refl | no ¬p = ca-refl

-- io-SYNC per-cell read: a fill/output sets one key `(i,d₀,id₀)` to `np` with
-- `cellWt np ≡ suc (cellWt old)`; every other cell is fixed.  For an ARBITRARY
-- key this yields the `CellAdv` from the source phase to the `setCell`-updated one.
cell-fill-read : (m : MedState) (i : Link) (d₀ : Dir) (id₀ : IDs) (np : CopyPhase)
               → cellWt np ≡ suc (cellWt (phase m i d₀ id₀))
               → (kl : Link) (kd : Dir) (kid : IDs)
               → CellAdv (phase m kl kd kid)
                         (phase-upd (phase m) i (setCell (phase m i) d₀ id₀ np) kl kd kid)
cell-fill-read m i d₀ id₀ np wtEq kl kd kid with kl ≟ i
... | no ¬p = ca-refl
cell-fill-read m i d₀ id₀ np wtEq kl kd kid | yes refl with kd ≟ d₀ | kid ≟ id₀
... | yes refl | yes refl = ca-step (cell-set-adv (phase m i d₀ id₀) np wtEq) ca-refl
... | no ¬p | _ = ca-refl
... | yes refl | no ¬p = ca-refl

------------------------------------------------------------------------
-- MEDIUM-τ reflector WITH the cell report (mirror
-- `WalkTauExpose.τreflect-med-expose`, LIGHT — medium-only τ lift): the drained
-- cell advances (`cDrn`), every other cell fixed.
------------------------------------------------------------------------

τreflect-med-cell : (r : RState) {M M′ : NetProc}
    (ms  : decMed (med (toSys r)) ─[ τ ]─► M′)
    (Meq : M ≡ ((M′ ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × AllCellAdv (toSys r) (toSys r′)
τreflect-med-cell r {M} {M′} ms Meq with medium-τ-inv-wt (med (toSys r)) ms
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
    report : AllCellAdv (toSys r) (toSys r′)
    report kl kd kid = cell-drain-read (med (toSys r)) i d₀ id₀ x drainEq kl kd kid

------------------------------------------------------------------------
-- io-SYNC reflector WITH the cell report (RAM-heavy — mirror
-- `WalkTauExpose.τreflect-io-expose`, but using `medium-ev-inv-wt` (the
-- cell-weight-carrying inversion) in place of `medium-ev-inv-brk`, so the
-- filled/output cell's advance is exposed).  The io-sync sets one cell
-- `(i,d₀,id₀)` to `np` with weight `+1` (a `cFill` or `cOut`); every other cell
-- is fixed.  Reachability is rebuilt through `lift-io-sync-whole-wτ` exactly as
-- the frozen expose module does (the medium target is now the `setCell` form,
-- whose `broken` is unchanged, so no budget bookkeeping is needed).
------------------------------------------------------------------------

τreflect-io-cell : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M₁ N₁ M : NetProc}
    (iomem : ioES .mem (X , e) a)
    (sM : decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► M₁)
    (sN : absNodesOf (toSys r)   ─[ ev (evl (evLabel X e a)) ]─► N₁)
    (Meq : M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × AllCellAdv (toSys r) (toSys r′)
τreflect-io-cell r {X} {e} {a} {M₁} {N₁} {M} iomem sM sN Meq
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
    report : AllCellAdv (toSys r) (toSys r′)
    report kl kd kid = cell-fill-read (med (toSys r)) i d₀ id₀ np wtEq kl kd kid

------------------------------------------------------------------------
-- TOTAL per-τ reflector with the cell report (mirror
-- `WalkTauExpose.τreflect-expose`): dispatch a hidden τ to the medium-τ drain
-- reflector or the io-sync fill reflector (nodes-τ is refuted).
------------------------------------------------------------------------

τreflect-cell : (r : RState) {M : NetProc} → radec r ─[ τ ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × AllCellAdv (toSys r) (toSys r′)
τreflect-cell r step with reflect-absDec-τ (toSys r) step
... | innerτ P′ innerStep Peq
    with reflect-inner-τ (decMed (med (toSys r))) (absNodesOf (toSys r)) innerStep
...   | medτ   M′ ms eqP = τreflect-med-cell r ms (trans Peq (cong (λ z → z ∖ ioES) eqP))
...   | nodesτ N′ ns eqP = ⊥-elim (absNodesOf-no-τ (toSys r) ns)
τreflect-cell r step | hidSync M₁ N₁ iomem sM sN Peq = τreflect-io-cell r iomem sM sN Peq

------------------------------------------------------------------------
-- τ-run lift with the cell report (mirror `WalkTauExpose.liftτ*-expose`): fold
-- the per-τ cell reports across a whole hidden τ-run by pointwise `CellAdv`
-- composition.  This is the τ-run half of the leg-`l` `CellReport`.
------------------------------------------------------------------------

liftτ*-cell′ : (r : RState) {start u : NetProc} → start ≡ radec r
          → start ─[τ*]─► u
          → Σ[ r′ ∈ RState ] (u ≡ radec r′) × AllCellAdv (toSys r) (toSys r′)
liftτ*-cell′ r eq τ*-refl = r , eq , allCellAdv-refl (toSys r)
liftτ*-cell′ r eq (τ*-step s rest) with τreflect-cell r (subst (λ z → z ─[ τ ]─► _) eq s)
... | r₁ , eq₁ , rep₁ with liftτ*-cell′ r₁ eq₁ rest
...   | r′ , equ , rep′ =
        r′ , equ , allCellAdv-trans (toSys r) (toSys r₁) (toSys r′) rep₁ rep′

liftτ*-cell : (r : RState) {u : NetProc}
         → radec r ─[τ*]─► u
         → Σ[ r′ ∈ RState ] (u ≡ radec r′) × AllCellAdv (toSys r) (toSys r′)
liftτ*-cell r = liftτ*-cell′ r refl

------------------------------------------------------------------------
-- The leg-`l` `CellReport`: instantiate `AllCellAdv` at the two leg cells
-- (`cellUp`/`cellDn` — the BF `(hi, N2N_BlockFetch)` copy cells the block
-- travels through), the CELL component of the seven-component `PipeReport`.
------------------------------------------------------------------------

-- how the leg-`l` upstream + downstream cells move across a τ-run
CellReport : TwoLegs → SysState → SysState → Set
CellReport l s s′ = CellAdv (cellUp l s) (cellUp l s′) × CellAdv (cellDn l s) (cellDn l s′)

-- project the whole-medium report onto the two leg cells (the keys are defeq)
allCellAdv⇒CellReport : (l : TwoLegs) (s s′ : SysState)
                      → AllCellAdv s s′ → CellReport l s s′
allCellAdv⇒CellReport legBD s s′ f =
  f linkAB hi N2N_BlockFetch , f linkBD hi N2N_BlockFetch
allCellAdv⇒CellReport legCD s s′ f =
  f linkAC hi N2N_BlockFetch , f linkCD hi N2N_BlockFetch

-- HEADLINE (τ-run half of the leg `CellReport`): a hidden τ-run exposes the
-- leg-`l` cells' phase deltas (fixed, or advanced empty→full→draining→empty)
liftτ*-cellReport : (l : TwoLegs) (r : RState) {u : NetProc}
                  → radec r ─[τ*]─► u
                  → Σ[ r′ ∈ RState ] (u ≡ radec r′) × CellReport l (toSys r) (toSys r′)
liftτ*-cellReport l r run with liftτ*-cell r run
... | r′ , eq , acr = r′ , eq , allCellAdv⇒CellReport l (toSys r) (toSys r′) acr
