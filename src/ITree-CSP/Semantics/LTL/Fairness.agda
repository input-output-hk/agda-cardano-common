{-# OPTIONS --guardedness #-}

------------------------------------------------------------
-- Visible-class weak fairness on `Trace` (campaign milestone F1).
--
-- Harvested from the fairness feasibility spike
-- (`Semantics.LTL.FairnessSpike`, now disposable) per its findings report
-- (docs/superpowers/specs/2026-07-19-ltl-fairness-spike-report.md, §Q1/§Q3).
--
-- The notion: weak fairness w.r.t. a VISIBLE EVENT CLASS `C`, stated on the
-- coinductive `Trace` layer via WEAK-visible enabledness (`═[ ev l ]═►`).
-- Because `Trace.step` already carries a WEAK visible transition
-- (`═[ ev e ]═►` = τ* · e · τ* from WeakBisim), any gating τ-chain is
-- ABSORBED into the weak-enabledness of the visible target event — so
-- visible-weak fairness suffices and no τ-class fairness is needed (spike
-- §Q1 τ-level verdict).  `Fair` is a plain Σ/Π statement: fully constructive,
-- NO postulate, NO new classical axiom.
--
-- Generic (model-agnostic): parametric in E, I, R, and the event class `C`
-- (at an arbitrary level ℓc) — no FourNode content, mirroring
-- `Semantics.LTL.TraceBridge`.  The soundness toys demonstrating that the
-- notion is non-vacuous both ways live in `Semantics.LTL.FairnessToy`.
--
-- F2 (next milestone) adds the ≈DR / WTraceSim transfer (`wenabled-invariant`
-- etc.); those transfer lemmas are deliberately NOT here (spike §Q3 re-staging).
--
-- STATEMENT FIX (review-confirmed): the event class `C` is typed over the
-- √-FREE `Event` record (`Semantics.LTS.Event`), NOT `Event√ R`.  Typing `C`
-- over `Event√ R` let it accept `√ r` labels; at a `done` frame the `sRet`
-- step makes `WEnabled C` trivially inhabited (via a bare `√`-label weak
-- step) forever (a `done` leaf's tail is itself), while `Fires C` is
-- unconditionally `⊥` on terminator frames — so `Fair C` became
-- unsatisfiable for a successfully-terminated trace, purely as an artefact
-- of representing termination as a `done` LEAF rather than a step-√-then-
-- stuck frame.  Restricting `C : Event → Set ℓc` excludes `√` BY
-- CONSTRUCTION, making `Fair` independent of that Trace-representation
-- choice.
------------------------------------------------------------

open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)

open import Process_Trees using (PTree)

module Semantics.LTL.Fairness
  {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where

open import Semantics.LTS       {ℓ} {ℓe} {ℓi} {E} {I} using (Event; Event√; Label; ev; evl; √)
open import Semantics.WeakBisim {ℓ} {ℓe} {ℓi} {E} {I} using (_═[_]═►_)
open import Semantics.LTL.Traces_Based {ℓ} {ℓe} {ℓi} {E} {I}
  using ( Trace; Frame; step; done; stuck; div
        ; FramePred; frameState; frameOf; drop
        ; atom; ⟦_⟧; ◇ᵗ; ◇ᵗ-now; ◇ᵗ-later; F_; F⇒◇ᵗ; ◇ᵗ⇒F )

------------------------------------------------------------
-- §1  The fairness vocabulary (spike-report §Q1 exact shapes).
------------------------------------------------------------

-- Weak enabledness of a visible event class `C` at a state `t`: `t` can
-- perform a WEAK visible step (`═[ ev (evl e) ]═►`, absorbing any
-- surrounding τ) on some √-FREE event `e` in the class `C`.  `C`'s domain is
-- the √-free `Event` record (not `Event√ R`) BY CONSTRUCTION: a `done`
-- frame's outgoing `sRet` step is a bare `√ r` label with no `Event` behind
-- it, so quantifying `C` over `Event√ R` let a class accept termination
-- labels and made `Fair` unsatisfiable at a `done` leaf purely because of
-- the (arbitrary) choice to represent successful termination as a leaf
-- frame rather than a step-then-stuck frame — see the finding this fixes.
WEnabled : ∀ {ℓr ℓc} {R : Set ℓr}
         → (Event → Set ℓc) → PTree E I R
         → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓc)
WEnabled {R = R} C t =
  Σ[ e ∈ Event ] Σ[ t′ ∈ PTree E I R ] (t ═[ ev (evl e) ]═► t′) × C e

-- The current frame IS a visible step whose event lies in class `C`
-- (terminator frames, AND `step`-frames labelled by `√`, never fire `C` —
-- `C` has no opinion on `√` by construction, so it cannot fire on it).
Fires : ∀ {ℓr ℓc} {R : Set ℓr}
      → (Event → Set ℓc) → FramePred ℓc R
Fires        C (step _ (evl e)) = C e
Fires {ℓc = ℓc} C (step _ (√ _)) = Lift ℓc ⊥
Fires {ℓc = ℓc} C (done _ _) = Lift ℓc ⊥
Fires {ℓc = ℓc} C (stuck _)  = Lift ℓc ⊥
Fires {ℓc = ℓc} C (div _)    = Lift ℓc ⊥

-- `C` is (weakly) enabled at the k-th suffix of the trace `tr`.
enabledAt : ∀ {ℓr ℓc} {R : Set ℓr} {t : PTree E I R}
          → (Event → Set ℓc) → Trace R t → ℕ
          → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓc)
enabledAt C tr k = WEnabled C (frameState (frameOf (drop k tr)))

-- Weak fairness w.r.t. class `C` (the "no bad suffix" contrapositive in
-- positive form): from every suffix `n`, if `C` stays continuously weakly
-- enabled thereafter, then `C` eventually fires.
Fair : ∀ {ℓr ℓc} {R : Set ℓr} {t : PTree E I R}
     → (Event → Set ℓc) → Trace R t
     → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓc)
Fair C tr = ∀ n → (∀ k → enabledAt C tr (n + k))
          → ◇ᵗ (atom (Fires C)) (drop n tr)

------------------------------------------------------------
-- §2  Persistence ⇒ eventuality (the shape the liveness walk consumes).
--
-- These are the F1 general lemmas F2/F3/M5 build on: given the system
-- invariant "the target class is continuously weakly enabled", `Fair`
-- converts persistence into "the target eventually fires".
------------------------------------------------------------

-- Persistent weak-enabledness + `Fair` ⇒ raw `◇ᵗ (Fires C)` at the head.
fairForces◇ : ∀ {ℓr ℓc} {R : Set ℓr} {t : PTree E I R}
              {C : Event → Set ℓc} (tr : Trace R t)
            → Fair C tr → (∀ k → enabledAt C tr k)
            → ◇ᵗ (atom (Fires C)) tr
fairForces◇ tr fair cont = fair zero cont

-- Same, delivered in the surface `⟦ F _ ⟧` form the spec target consumes.
fairForcesF : ∀ {ℓr ℓc} {R : Set ℓr} {t : PTree E I R}
              {C : Event → Set ℓc} (tr : Trace R t)
            → Fair C tr → (∀ k → enabledAt C tr k)
            → ⟦ F_ (atom (Fires C)) ⟧ tr
fairForcesF tr fair cont = ◇ᵗ⇒F (fairForces◇ tr fair cont)

------------------------------------------------------------
-- §3  Monotonicity in the class `C` (the pieces that fall out).
--
-- WEnabled/Fires are covariant in `C`, so enlarging the class preserves
-- them.  `Fair` is NOT monotone in `C`: `C` occurs both positively (the
-- `Fires` consequent) and negatively (the `enabledAt` antecedent), so its
-- variance is mixed and no monotonicity lemma falls out.
------------------------------------------------------------

-- Enlarging the class preserves weak-enabledness.
WEnabled-mono : ∀ {ℓr ℓc ℓd} {R : Set ℓr}
                {C : Event → Set ℓc} {D : Event → Set ℓd}
              → (∀ {e} → C e → D e)
              → ∀ {t : PTree E I R} → WEnabled C t → WEnabled D t
WEnabled-mono sub (e , t′ , w , ce) = e , t′ , w , sub ce

-- Enlarging the class preserves "the current frame fires the class".
Fires-mono : ∀ {ℓr ℓc ℓd} {R : Set ℓr}
             {C : Event → Set ℓc} {D : Event → Set ℓd}
           → (∀ {e} → C e → D e)
           → ∀ (fr : Frame R) → Fires C fr → Fires D fr
Fires-mono sub (step _ (evl e)) c = sub c
Fires-mono sub (step _ (√ _))   (lift ())
Fires-mono sub (done _ _) (lift ())
Fires-mono sub (stuck _)  (lift ())
Fires-mono sub (div _)    (lift ())
