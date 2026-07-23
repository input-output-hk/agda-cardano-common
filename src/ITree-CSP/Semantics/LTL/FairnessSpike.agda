{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- ██  SPIKE MODULE — DISPOSABLE, IMPORTED BY NOTHING  ██
--
-- LTL-fairness feasibility spike for the FourNode-liveness campaign.
-- Design: docs/superpowers/specs/2026-07-19-ltl-fairness-spike-design.md
-- Report: docs/superpowers/specs/2026-07-19-ltl-fairness-spike-report.md
--
-- Postulates/holes are permitted HERE ONLY.  This module explores the
-- weakest fairness notion (Q1), the transfer viability across the campaign
-- seams (Q2), and it feeds the re-staging (Q3).  It must be deleted after
-- the report is harvested.  Toy systems only — never step the composite.
--
-- KEY FINDING (Q1, τ-level): the coinductive `Trace` records only WEAK
-- visible steps (`step : t ═[ ev e ]═► t′`, and `═[ ev e ]═►` = τ* · e · τ*
-- from WeakBisim).  So the τ delivery chain that gates D's `recvBFBlock` is
-- ALREADY absorbed into the WEAK-enabledness of the visible target event.
-- Hence weak fairness stated on WEAK-visible-enabledness of the target
-- event class SUFFICES to exclude KA starvation, and the τ-level starvation
-- the design worried about does NOT bite at the Trace layer (it would bite
-- only if fairness were stated on STRONG single-step enabledness, or if the
-- target were a hidden τ event).  Demonstrated below on a toy that puts the
-- gating τ (the "hidden wire") in front of the visible target.
------------------------------------------------------------------------

open import Level using (Level; _⊔_; Lift; lift) renaming (zero to lzero; suc to lsuc)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Process_Trees hiding (div)

module Semantics.LTL.FairnessSpike where

open PTree

------------------------------------------------------------------------
-- §0  Toy alphabet.  Two visible events, both ⊤-carried:
--       a = the "KeepAlive loop" event (fires forever, autonomously);
--       b = the "delivery / arrivedD" target event.
------------------------------------------------------------------------

data Ev : Set → Set where
  a : Ev ⊤   -- KA-loop event (models apiKA sendKAMsg: autonomous, ∉ sync alphabet)
  b : Ev ⊤   -- target event  (models apiBF recvBFBlock at D = arrivedD)

-- τ-branch index type: reuse Ev (the specific index is irrelevant).
I₀ : Set → Set
I₀ = Ev

R₀ : Set
R₀ = ⊤

------------------------------------------------------------------------
-- Semantics layers instantiated at the toy alphabet.
------------------------------------------------------------------------

open import Semantics.LTS       {lzero} {lzero} {lzero} {Ev} {I₀}
open import Semantics.WeakBisim {lzero} {lzero} {lzero} {Ev} {I₀}
  using (_─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wτ; wev)
open import Semantics.DRBisim   {lzero} {lzero} {lzero} {Ev} {I₀}
  using (DRbisim; _≈DR_; dr-wev-sim)
open import Semantics.LTL.Traces_Based {lzero} {lzero} {lzero} {Ev} {I₀}

------------------------------------------------------------------------
-- §1  The toy system: a hand-built interleaving of an autonomous KA loop
--     with a "hidden-wire-then-deliver" pipeline.  Never a CSP composite.
--
--   sys0  = SLIDING node: offers visible `a` (→ sys0, KA self-loop) AND has
--           an enabled τ (→ sys1, the hidden wire step to the deliver state).
--   sys1  = offers visible `a` (→ sys1) and visible `b` (→ deadlock, deliver).
--   After `b` the pipeline is done (deadlock); KA could continue but the
--   point is made once `b` is reachable.
--
-- This is the FourNode shape in miniature: the target `b` (= arrivedD) is
-- reachable only AFTER a τ (= the hidden io wire), and the KA `a`-loop can
-- be scheduled forever without ever taking that τ.
------------------------------------------------------------------------

sys0 sys1 : PTree Ev I₀ R₀

-- sys0's visible offers: `a` self-loops, nothing else.
v0 : (at : AnyTypes Ev) → ContinueType at (Maybe (PTree Ev I₀ R₀))
v0 (_ , a) _ = just sys0
v0 (_ , b) _ = nothing
-- sys0's τ-branches: the single "hidden wire" τ to sys1.
t0 : (i : AnyTypes I₀) → ContinueType i (Maybe (PTree Ev I₀ R₀))
t0 (_ , a) _ = just sys1
t0 (_ , b) _ = nothing

-- sys1's visible offers: `a` self-loops, `b` delivers (→ deadlock).
v1 : (at : AnyTypes Ev) → ContinueType at (Maybe (PTree Ev I₀ R₀))
v1 (_ , a) _ = just sys1
v1 (_ , b) _ = just deadlock
-- sys1 is stable (no τ).
t1 : (i : AnyTypes I₀) → ContinueType i (Maybe (PTree Ev I₀ R₀))
t1 _ _ = nothing

PTree.force sys0 = react v0 t0
PTree.force sys1 = react v1 t1

------------------------------------------------------------------------
-- §2  The event classes (predicates on visible events).
------------------------------------------------------------------------

-- The target class C = "the `b` event".  (In the campaign: the intact-path
-- fetch-delivery event class.)
Cb : Event√ R₀ → Set
Cb (evl (evLabel _ b _)) = ⊤
Cb (evl (evLabel _ a _)) = ⊥
Cb (√ _)                 = ⊥

------------------------------------------------------------------------
-- §3  Generic fairness vocabulary (Q1).  Stated on `Trace` via
--     `frameState`-enabledness, exactly as the design asks.
--
--   * WEnabled C t : the state `t` can WEAKLY perform a C-event
--                    (`═[ ev l ]═►`, so it absorbs any τ prefix — this is
--                    the τ-absorption that dissolves the τ-level worry).
--   * Fires   C fr : the current frame IS a C-event step.
--   * Fair    C tr : weak fairness — from every suffix, if C stays
--                    continuously (weakly) enabled, then C eventually fires.
--
-- `Fair` is a positive Σ/Π statement: fully constructive, NO new axiom.
------------------------------------------------------------------------

-- Weak enabledness of an event class at a state (stated at the toy alphabet;
-- the definition and its proofs read identically at ANY alphabet — the
-- campaign's generic version lives in Semantics/LTL/Fairness.agda, F1).
WEnabled : (Event√ R₀ → Set) → PTree Ev I₀ R₀ → Set (lsuc lzero)
WEnabled C t = Σ[ l ∈ Event√ R₀ ] Σ[ t′ ∈ PTree Ev I₀ R₀ ] (t ═[ ev l ]═► t′) × C l

-- The current frame fires a C-event.
Fires : (Event√ R₀ → Set) → FramePred lzero R₀
Fires C (step _ e) = C e
Fires C (done _ _) = ⊥
Fires C (stuck _)  = ⊥
Fires C (div _)    = ⊥

-- C is (weakly) enabled at the k-th suffix of `tr`.
enabledAt : ∀ {t : PTree Ev I₀ R₀}
          → (Event√ R₀ → Set) → (Trace R₀) t → ℕ → Set _
enabledAt C tr k = WEnabled C (frameState (frameOf (drop k tr)))

-- Weak fairness (the design's "no bad suffix" contrapositive, positive form):
-- from suffix n, continuous weak-enabledness of C forces C to eventually fire.
Fair : ∀ {t : PTree Ev I₀ R₀}
     → (Event√ R₀ → Set) → (Trace R₀) t → Set _
Fair C tr = ∀ n → (∀ k → enabledAt C tr (n + k))
          → ◇ᵗ (atom (Fires C)) (drop n tr)

------------------------------------------------------------------------
-- §4  The starving (unfair) trace: `a`-forever (the KA-loop counterexample).
------------------------------------------------------------------------

-- sys0 weakly self-loops on `a` (τ*-refl · sVis · τ*-refl).
aStep : sys0 ═[ ev (evl (evLabel ⊤ a tt)) ]═► sys0
aStep = wev τ*-refl (sVis refl refl) τ*-refl

-- The a^ω trace (guarded self-reference via a copattern tail, so
-- `tail aωTrace = aωTrace` reduces definitionally).
aωTrace : (Trace R₀) sys0
aω∞     : ∞Trace R₀ sys0
aωTrace = step aStep aω∞
∞Trace.force aω∞ = aωTrace

-- Every suffix of a^ω observes sys0 as its source state (homogeneous PTree
-- equality; the tail self-loop reduces definitionally at each suc step).
fsaω : ∀ n → frameState (frameOf (drop n aωTrace)) ≡ sys0
fsaω zero    = refl
fsaω (suc n) = fsaω n

------------------------------------------------------------------------
-- §5  b is WEAKLY enabled at sys0 (absorbing the hidden-wire τ) and at sys1.
--     This is the τ-absorption in action: the visible target `b` is weakly
--     enabled even though a τ (the wire) gates it.
------------------------------------------------------------------------

-- sys0 ═[ b ]═►: τ (wire) to sys1, then visible b to deadlock.
bWeak0 : sys0 ═[ ev (evl (evLabel ⊤ b tt)) ]═► deadlock
bWeak0 = wev (τ*-step (sTau refl refl) τ*-refl) (sVis refl refl) τ*-refl

-- b is weakly enabled at sys0.
bEnabled0 : WEnabled Cb sys0
bEnabled0 = evl (evLabel ⊤ b tt) , deadlock , bWeak0 , tt

------------------------------------------------------------------------
-- §6  DEMONSTRATION (a): the unfair a^ω trace VIOLATES F(target).
--     `b` never appears as a frame, so ◇ᵗ (and hence F) fails.
------------------------------------------------------------------------

-- No suffix of a^ω has a b-firing head frame.
¬◇ᵗb-aω : ◇ᵗ (atom (Fires Cb)) aωTrace → ⊥
¬◇ᵗb-aω (◇ᵗ-now h)   = h                 -- head frame fires `a`, so Fires Cb = ⊥
¬◇ᵗb-aω (◇ᵗ-later d) = ¬◇ᵗb-aω d          -- tail aωTrace = aωTrace (definitional)

-- (a): a^ω does not satisfy F (atom fires-b).
demoA : ⟦ F_ (atom (Fires Cb)) ⟧ aωTrace → ⊥
demoA f = ¬◇ᵗb-aω (F⇒◇ᵗ {φ = atom (Fires Cb)} f)

------------------------------------------------------------------------
-- §7  DEMONSTRATION (b): `Fair C` EXCLUDES the unfair trace.
--     b stays continuously weakly-enabled along a^ω but never fires, so
--     `Fair Cb aωTrace` is contradictory.
------------------------------------------------------------------------

-- b is (weakly) enabled at every suffix of a^ω (each suffix's state is sys0).
contEnabled-aω : ∀ k → enabledAt Cb aωTrace k
contEnabled-aω k rewrite fsaω k = bEnabled0

-- (b): no fair trace is a^ω.
demoB : Fair Cb aωTrace → ⊥
demoB fair = ¬◇ᵗb-aω (fair zero (λ k → contEnabled-aω k))

------------------------------------------------------------------------
-- §8  DEMONSTRATION (c): under `Fair C`, F(target) becomes PROVABLE
--     whenever the target is continuously enabled (the system invariant
--     the abstract liveness walk supplies).  This is the exact shape the
--     campaign's walk consumes: persistent weak-enabledness + Fair ⇒ ◇ᵗ.
------------------------------------------------------------------------

fairForcesF : ∀ {t : PTree Ev I₀ R₀} (tr : (Trace R₀) t)
            → Fair Cb tr
            → (∀ k → enabledAt Cb tr k)     -- target continuously enabled
            → ⟦ F_ (atom (Fires Cb)) ⟧ tr
fairForcesF tr fair cont = ◇ᵗ⇒F (fair zero cont)

------------------------------------------------------------------------
-- §9  Q2 PROTOTYPE — the riskiest transfer lemma: WEAK-enabledness of a
--     visible event class is ≈DR-INVARIANT.  This is the crux of
--     `Fair`-transport across the campaign's ≈DR / `WTraceSim` seam, and it
--     is ~3 lines via `dr-wev-sim`.  Stated generically (any alphabet).
--
--   POSITIVE for Q2(a): because `Trace`/`WTrace` steps are WEAK visible
--   steps, weak-enabledness transports along ≈DR directly.  Combined with
--   FrameSim's `e₁ ≡ e₂` at step frames (which preserves "Fires"), `Fair`
--   transports along `WTraceSim`.  NO new axiom.
--
--   PRECISE NEGATIVE (Q2(a), τ-class): this uses `═[ ev l ]═►` (WEAK
--   visible).  The analogous statement for a τ-class using `─[ τ ]─►`
--   (STRONG single-step τ) is NOT ≈DR-invariant — weak bisim hides τ, so a
--   τ-step on one side may correspond to none on the other.  Hence fairness
--   MUST be stated on visible (weak) classes to be transferable; τ-class
--   fairness does not transfer.  This aligns with Q1: visible-weak fairness
--   both suffices AND transfers.
------------------------------------------------------------------------

-- Weak-enabledness of a visible event class is ≈DR-invariant.  Stated at the
-- toy alphabet; the proof body (one `dr-wev-sim`) is alphabet-generic — it
-- copies verbatim into the campaign's generic Fairness module (F2).
wenabled-invariant :
    ∀ {t₁ t₂ : PTree Ev I₀ R₀} {C : Event√ R₀ → Set}
  → t₁ ≈DR t₂ → WEnabled C t₁ → WEnabled C t₂
wenabled-invariant dr (l , t′ , w , cl) with dr-wev-sim w dr
... | t₂′ , w₂ , _ = l , t₂′ , w₂ , cl
