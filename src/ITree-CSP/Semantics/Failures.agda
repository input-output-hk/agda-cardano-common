{-# OPTIONS --guardedness #-}

-- SPIKE: the (stable) failures model on the pure-react LTS.
-- A failure is a (trace, refusal) pair: a τ-abstracting visible trace `s` reaching a
-- state that refuses the event set `X`.  Plus trace/failure refinement preorders.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax)
open import Data.Empty using (⊥-elim)
open import Relation.Binary using (Preorder; IsPreorder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; isEquivalence)

open import Process_Trees

module Semantics.Failures {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where
open PTree
open import Semantics.LTS       {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.Refusals  {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.WeakBisim {ℓ} {ℓe} {ℓi} {E} {I}

-- τ-abstracting big-step: p performs the visible trace s (τ's are silent) reaching q
data _⟹⟨_⟩_ {ℓr} {R : Set ℓr}
    : PTree E I R → List (Event√ R) → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  ⟹-refl : ∀ {p} → p ⟹⟨ [] ⟩ p
  ⟹-τ    : ∀ {p q r s}             → p ─[ τ ]─► q    → q ⟹⟨ s ⟩ r → p ⟹⟨ s ⟩ r
  ⟹-ev   : ∀ {p q r s} {e : Event√ R} → p ─[ ev e ]─► q → q ⟹⟨ s ⟩ r → p ⟹⟨ e ∷ s ⟩ r

-- traces and (stable) failures
traces : ∀ {ℓr} {R : Set ℓr} → PTree E I R → List (Event√ R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
traces P s = Σ[ P′ ∈ PTree E I _ ] (P ⟹⟨ s ⟩ P′)

failures : ∀ {ℓr ℓx} {R : Set ℓr}
         → PTree E I R → List (Event√ R) → (Event√ R → Set ℓx)
         → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓx)
failures P s X = Σ[ P′ ∈ PTree E I _ ] (P ⟹⟨ s ⟩ P′ × Refuses P′ X)

-- refinement: P ⊑ Q  iff  Q's behaviours are among P's
_⊑T_ : ∀ {ℓr} {R : Set ℓr} → PTree E I R → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
P ⊑T Q = ∀ s → traces Q s → traces P s

_⊑F_ : ∀ {ℓr} {R : Set ℓr} → PTree E I R → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ lsuc ℓr)
_⊑F_ {ℓr = ℓr} {R = R} P Q = ∀ s (X : Event√ R → Set ℓr) → failures Q s X → failures P s X

-- both refinements are preorders
⊑T-refl  : ∀ {ℓr} {R : Set ℓr} (P : PTree E I R) → P ⊑T P
⊑T-refl P s t = t
⊑T-trans : ∀ {ℓr} {R : Set ℓr} {P Q S : PTree E I R} → P ⊑T Q → Q ⊑T S → P ⊑T S
⊑T-trans pq qs s t = pq s (qs s t)

⊑F-refl  : ∀ {ℓr} {R : Set ℓr} (P : PTree E I R) → P ⊑F P
⊑F-refl P s X f = f
⊑F-trans : ∀ {ℓr} {R : Set ℓr} {P Q S : PTree E I R} → P ⊑F Q → Q ⊑F S → P ⊑F S
⊑F-trans pq qs s X f = pq s X (qs s X f)

-- deadlock's only failure is the empty trace refusing anything (it is maximally refusing)
deadlock-failure : ∀ {ℓr ℓx} {R : Set ℓr} {X : Event√ R → Set ℓx} → failures deadlock [] X
deadlock-failure = deadlock , ⟹-refl , deadlock-refuses

-------------------------------------------------------------------------------------
-- TRACES are respected by weak bisimulation (traces-respects-≈).
-- (FAILURES are NOT — see div≈deadlock below; that needs divergence-respecting bisim.)
-------------------------------------------------------------------------------------

-- a leading τ* run is silent, so it doesn't change the trace
τ*-then : ∀ {ℓr} {R : Set ℓr} {p q r : PTree E I R} {s}
        → p ─[τ*]─► q → q ⟹⟨ s ⟩ r → p ⟹⟨ s ⟩ r
τ*-then τ*-refl           tr = tr
τ*-then (τ*-step pτ rest) tr = ⟹-τ pτ (τ*-then rest tr)

weaken-τ : ∀ {ℓr} {R : Set ℓr} {p q r : PTree E I R} {s}
         → p ═[ τ ]═► q → q ⟹⟨ s ⟩ r → p ⟹⟨ s ⟩ r
weaken-τ (wτ pre) tr = τ*-then pre tr

weaken-ev : ∀ {ℓr} {R : Set ℓr} {p q r : PTree E I R} {s} {e : Event√ R}
          → p ═[ ev e ]═► q → q ⟹⟨ s ⟩ r → p ⟹⟨ e ∷ s ⟩ r
weaken-ev (wev pre evs post) tr = τ*-then pre (⟹-ev evs (τ*-then post tr))

-- bisimilar processes simulate each other's traces
trace-sim : ∀ {ℓr} {R : Set ℓr} {P Q P′ : PTree E I R} {s}
          → Wbisim R P Q → P ⟹⟨ s ⟩ P′
          → Σ[ Q′ ∈ PTree E I R ] (Q ⟹⟨ s ⟩ Q′ × Wbisim R P′ Q′)
trace-sim p≈q ⟹-refl = _ , ⟹-refl , p≈q
trace-sim p≈q (⟹-τ pτ rest)  with p≈q .Wbisim.fwd .WSimF.on-tau pτ
... | _ , qτ , p₁≈q₁ with trace-sim p₁≈q₁ rest
...   | Q′ , q⟹ , p′≈q′ = Q′ , weaken-τ qτ q⟹ , p′≈q′
trace-sim p≈q (⟹-ev pev rest) with p≈q .Wbisim.fwd .WSimF.on-ev pev
... | _ , qev , p₁≈q₁ with trace-sim p₁≈q₁ rest
...   | Q′ , q⟹ , p′≈q′ = Q′ , weaken-ev qev q⟹ , p′≈q′

-- weak bisimulation ⇒ trace equivalence (both directions)
traces-≈→ : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} {s}
          → Wbisim R P Q → traces P s → traces Q s
traces-≈→ p≈q (_ , tr) with trace-sim p≈q tr
... | Q′ , q⟹ , _ = Q′ , q⟹

traces-respects-≈ : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} {s}
                  → Wbisim R P Q → (traces P s → traces Q s) × (traces Q s → traces P s)
traces-respects-≈ p≈q = traces-≈→ p≈q , traces-≈→ (wbisim-sym p≈q)

-------------------------------------------------------------------------------------
-- Why FAILURES are not respected: the divergent process div (= sil div, an infinite
-- τ-loop) is weakly bisimilar to deadlock — yet failures div = ∅ (div is never stable)
-- while failures deadlock ∋ ([] , X).  So failures-respects-≈ is FALSE for plain weak
-- bisimulation; it requires divergence-respecting (or stable/branching) bisimulation.
-------------------------------------------------------------------------------------

div≈deadlock : ∀ {ℓr} {R : Set ℓr} → Wbisim R (div {E = E} {I = I}) deadlock
div≈deadlock .Wbisim.fwd .WSimF.on-ev  (sRet ())
div≈deadlock .Wbisim.fwd .WSimF.on-ev  (sVis eq _) = ⊥-elim (sil≢react eq)
div≈deadlock .Wbisim.fwd .WSimF.on-tau (sSil refl) = deadlock , wτ τ*-refl , div≈deadlock
div≈deadlock .Wbisim.fwd .WSimF.on-tau (sTau eq _) = ⊥-elim (sil≢react eq)
div≈deadlock .Wbisim.bwd .WSimF.on-ev  (sRet ())
div≈deadlock .Wbisim.bwd .WSimF.on-ev  (sVis refl ())
div≈deadlock .Wbisim.bwd .WSimF.on-tau (sSil ())
div≈deadlock .Wbisim.bwd .WSimF.on-tau (sTau refl ())

⊑T-preorder : ∀ {ℓr} (R : Set ℓr) → Preorder _ _ _
⊑T-preorder R = record
  { Carrier    = PTree E I R
  ; _≈_        = _≡_
  ; _≲_        = _⊑T_
  ; isPreorder = record
      { isEquivalence = isEquivalence
      ; reflexive     = λ { refl → ⊑T-refl _ }
      ; trans         = ⊑T-trans
      }
  }

⊑F-preorder : ∀ {ℓr} (R : Set ℓr) → Preorder _ _ _
⊑F-preorder R = record
  { Carrier    = PTree E I R
  ; _≈_        = _≡_
  ; _≲_        = _⊑F_
  ; isPreorder = record
      { isEquivalence = isEquivalence
      ; reflexive     = λ { refl → ⊑F-refl _ }
      ; trans         = ⊑F-trans
      }
  }
