{-# OPTIONS --guardedness #-}

------------------------------------------------------------
-- Soundness toys for `Semantics.LTL.Fairness` (campaign milestone F1).
--
-- Demonstrates, constructively and postulate-free, that the visible-class
-- weak-fairness notion (`WEnabled`/`Fires`/`Fair`, from the generic
-- `Semantics.LTL.Fairness`) is non-vacuous BOTH ways.  Harvested from the
-- disposable spike (`Semantics.LTL.FairnessSpike`, §§0–8) per its report
-- (docs/superpowers/specs/2026-07-19-ltl-fairness-spike-report.md, §Q1).
--
-- The generic module is parametric in the alphabet, so the toys (which need
-- a concrete alphabet) must live in a separate, non-parametric module.
--
-- Toy = a hand-built interleaving of an autonomous KA `a`-loop with a
-- τ-gated deliver of the visible target `b`.  It puts the gating τ (the
-- "hidden wire") IN FRONT of the visible target `b`, so `b` is reachable
-- only after a τ, yet is WEAKLY enabled across it — the τ-absorption that
-- dissolves the τ-level worry.  `a^ω` is the KA-loop counterexample.
--
--   (a) the unfair `a^ω` trace VIOLATES `F (target fires)`;
--   (b) `Fair` EXCLUDES `a^ω`;
--   (c) under `Fair` + persistence, `F (target fires)` is PROVABLE.
------------------------------------------------------------

open import Level using () renaming (zero to lzero)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees hiding (div)

module Semantics.LTL.FairnessToy where

open PTree

------------------------------------------------------------
-- §0  Toy alphabet.  Two visible ⊤-carried events:
--       a = the "KeepAlive loop" event (fires forever, autonomously);
--       b = the "delivery / arrivedD" target event.
------------------------------------------------------------

-- The toy alphabet: `a` (KA-loop) and `b` (delivery target).
data Ev : Set → Set where
  a : Ev ⊤   -- KA-loop event (models apiKA sendKAMsg: autonomous, ∉ sync alphabet)
  b : Ev ⊤   -- target event  (models apiBF recvBFBlock at D = arrivedD)

-- τ-branch index type (the specific index is irrelevant here).
I₀ : Set → Set
I₀ = Ev

-- Toy result type.
R₀ : Set
R₀ = ⊤

------------------------------------------------------------
-- Semantics layers instantiated at the toy alphabet.
------------------------------------------------------------

open import Semantics.LTS       {lzero} {lzero} {lzero} {Ev} {I₀}
open import Semantics.WeakBisim {lzero} {lzero} {lzero} {Ev} {I₀}
  using (_─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wev)
open import Semantics.LTL.Traces_Based {lzero} {lzero} {lzero} {Ev} {I₀}
  using ( Trace; ∞Trace; step; tail; frameState; frameOf; drop
        ; atom; ⟦_⟧; ◇ᵗ; ◇ᵗ-now; ◇ᵗ-later; F_; F⇒◇ᵗ )
open import Semantics.LTL.Fairness {lzero} {lzero} {lzero} {Ev} {I₀}
  using (WEnabled; Fires; enabledAt; Fair; fairForcesF)

------------------------------------------------------------
-- §1  The toy system: an autonomous KA loop interleaved with a
--     "hidden-wire-then-deliver" pipeline.  Never a CSP composite.
--
--   sys0 = SLIDING node: offers visible `a` (→ sys0, KA self-loop) AND has
--          an enabled τ (→ sys1, the hidden wire to the deliver state).
--   sys1 = offers visible `a` (→ sys1) and visible `b` (→ deadlock, deliver).
------------------------------------------------------------

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

------------------------------------------------------------
-- §2  The target event class (a predicate on visible events).
------------------------------------------------------------

-- The target class C = "the `b` event" (the intact-path fetch-delivery
-- class).  Domain is the √-free `Event` record (F1 statement fix): `C` no
-- longer has a `√` case to (vacuously) rule out — it is excluded BY
-- CONSTRUCTION, not by an explicit ⊥ clause.
Cb : Event → Set
Cb (evLabel _ b _) = ⊤
Cb (evLabel _ a _) = ⊥

------------------------------------------------------------
-- §3  The starving (unfair) trace: `a`-forever (the KA-loop counterexample).
------------------------------------------------------------

-- sys0 weakly self-loops on `a` (τ*-refl · sVis · τ*-refl).
aStep : sys0 ═[ ev (evl (evLabel ⊤ a tt)) ]═► sys0
aStep = wev τ*-refl (sVis refl refl) τ*-refl

-- The a^ω trace (guarded self-reference via a copattern tail).
aωTrace : Trace R₀ sys0
aω∞     : ∞Trace R₀ sys0
aωTrace = step aStep aω∞
∞Trace.force aω∞ = aωTrace

-- Every suffix of a^ω observes sys0 as its source state.
fsaω : ∀ n → frameState (frameOf (drop n aωTrace)) ≡ sys0
fsaω zero    = refl
fsaω (suc n) = fsaω n

------------------------------------------------------------
-- §4  b is WEAKLY enabled at sys0, absorbing the hidden-wire τ.
------------------------------------------------------------

-- sys0 ═[ b ]═►: τ (wire) to sys1, then visible b to deadlock.
bWeak0 : sys0 ═[ ev (evl (evLabel ⊤ b tt)) ]═► deadlock
bWeak0 = wev (τ*-step (sTau refl refl) τ*-refl) (sVis refl refl) τ*-refl

-- b is weakly enabled at sys0 (the τ-absorption in action).
bEnabled0 : WEnabled Cb sys0
bEnabled0 = evLabel ⊤ b tt , deadlock , bWeak0 , tt

------------------------------------------------------------
-- §5  DEMONSTRATION (a): the unfair a^ω trace VIOLATES F(target).
------------------------------------------------------------

-- No suffix of a^ω has a b-firing head frame.
¬◇ᵗb-aω : ◇ᵗ (atom (Fires Cb)) aωTrace → ⊥
¬◇ᵗb-aω (◇ᵗ-now h)   = h                 -- head frame fires `a`, so Fires Cb = ⊥
¬◇ᵗb-aω (◇ᵗ-later d) = ¬◇ᵗb-aω d          -- tail aωTrace = aωTrace (definitional)

-- (a): a^ω does not satisfy F (atom fires-b).
demoA : ⟦ F_ (atom (Fires Cb)) ⟧ aωTrace → ⊥
demoA f = ¬◇ᵗb-aω (F⇒◇ᵗ {φ = atom (Fires Cb)} f)

------------------------------------------------------------
-- §6  DEMONSTRATION (b): `Fair C` EXCLUDES the unfair trace.
------------------------------------------------------------

-- b is (weakly) enabled at every suffix of a^ω (each suffix's state is sys0).
contEnabled-aω : ∀ k → enabledAt Cb aωTrace k
contEnabled-aω k rewrite fsaω k = bEnabled0

-- (b): no fair trace is a^ω.
demoB : Fair Cb aωTrace → ⊥
demoB fair = ¬◇ᵗb-aω (fair zero (λ k → contEnabled-aω k))

------------------------------------------------------------
-- §7  DEMONSTRATION (c): under `Fair C` + persistent enabledness,
--     F(target) becomes PROVABLE (the exact shape the liveness walk
--     consumes: persistent weak-enabledness + Fair ⇒ ◇ᵗ, via `fairForcesF`).
------------------------------------------------------------

-- (c): the generic persistence lemma, exercised at the toy alphabet.
demoC : (tr : Trace R₀ sys0)
      → Fair Cb tr → (∀ k → enabledAt Cb tr k)
      → ⟦ F_ (atom (Fires Cb)) ⟧ tr
demoC tr fair cont = fairForcesF tr fair cont
