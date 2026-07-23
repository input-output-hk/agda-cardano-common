{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Layer 1 — the RELATIONAL spec of Roscoe's priority operator `Pri`
-- (see `docs/specs/priority-implementation-plan.md`).
--
-- `_─[_]─►ᵖ_` is the ground-truth prioritised transition relation: a subrelation
-- of the plain LTS `_─[_]─►_` that BLOCKS a visible event `e` when the state is
-- stable and some strictly-dominating `b > e` is offered.  No decidability is
-- needed here — the negative premise stays PROPOSITIONAL, exactly the style of
-- `Semantics.Refusals.Refuses` (`isStable t × ∀ e → …`).  It is discharged by
-- structure, never by a classical axiom, so this module is `--safe` and imports
-- nothing from `Classical`.
--
-- Parametrised by a `PriOrderProp` (the propositional order).  τ and ✓ are
-- ≤-maximal by convention: `pτ`/`p√` are unconditional.
------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; Σ-syntax)
open import Relation.Nullary using (¬_)

open import Process_Trees using (PTree; isStable; AnyTypes)
open import Semantics.PriOrder using (Ev; _∙_; PriOrderProp; Maximal)

module Semantics.PriLTS
  {ℓ ℓe ℓi ℓo} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi}
  (O : PriOrderProp {ℓ} {ℓe} {E} ℓo) where

open PTree
open PriOrderProp O using (_<ᵖ_)
open import Semantics.LTS      {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.Refusals {ℓ} {ℓe} {ℓi} {E} {I} using (Offers)

------------------------------------------------------------------------
-- `Event` (from the LTS) and `Ev` (from the order) are the same data,
-- differently packaged.  Convert between them.
------------------------------------------------------------------------

evToEv : Event → Ev
evToEv (evLabel A e a) = (A , e) ∙ a

evOfEv : Ev → Event
evOfEv ((A , e) ∙ a) = evLabel A e a

------------------------------------------------------------------------
-- The prioritised transition relation.
--
-- Two simplifications this ITree encoding buys over Roscoe's SOS rule:
--   * `ret` fires `√` immediately and `√` is ≤-maximal ⇒ `p√` is UNCONDITIONAL
--     (no stability / dominator side condition).
--   * a node is `ret` OR `react`, never both, so the paper's "✓ dominates
--     non-maximal events" clause is VACUOUS at `react` nodes; ✓-priority
--     collapses into τ-priority via the existing slide encoding — one fewer
--     side condition than Roscoe's rule.
------------------------------------------------------------------------

infix 4 _─[_]─►ᵖ_

data _─[_]─►ᵖ_ {ℓr} {R : Set ℓr}
    : PTree E I R → Label R → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓo ⊔ ℓr) where

  -- τ is ≤-maximal: silent moves pass through unchanged
  pτ   : ∀ {t t′}            → t ─[ τ ]─► t′            → t ─[ τ ]─►ᵖ t′

  -- ✓ is ≤-maximal and unconditional (see the note above)
  p√   : ∀ {t t′ x}          → t ─[ ev (√ x) ]─► t′      → t ─[ ev (√ x) ]─►ᵖ t′

  -- a ≤-maximal visible event fires regardless of stability or other offers
  pMax : ∀ {t t′ e}
       → Maximal O (evToEv e)
       → t ─[ ev (evl e) ]─► t′
       → t ─[ ev (evl e) ]─►ᵖ t′

  -- a non-maximal visible event fires only from a STABLE state that offers
  -- none of its strict dominators
  pLo  : ∀ {t t′ e}
       → t ─[ ev (evl e) ]─► t′
       → isStable t
       → (∀ b → (evToEv e) <ᵖ b → ¬ Offers t (evl (evOfEv b)))
       → t ─[ ev (evl e) ]─►ᵖ t′

------------------------------------------------------------------------
-- τ-coincidence: `─►ᵖ` and `─►` have exactly the same τ-steps (`pτ` is a
-- relabelling).  Hence divergence is unchanged by prioritisation —
-- `divergencesᵖ ≡ divergences` — and `Pri` can create deadlock but never
-- divergence.
------------------------------------------------------------------------

τ-pri→ : ∀ {ℓr} {R : Set ℓr} {t t′ : PTree E I R} → t ─[ τ ]─►ᵖ t′ → t ─[ τ ]─► t′
τ-pri→ (pτ st) = st

τ-pri← : ∀ {ℓr} {R : Set ℓr} {t t′ : PTree E I R} → t ─[ τ ]─► t′ → t ─[ τ ]─►ᵖ t′
τ-pri← = pτ

------------------------------------------------------------------------
-- Derived big-step trace / failure machinery over `─►ᵖ` (mirrors
-- `Semantics.Failures`, which is hardwired to the plain `─►`).
------------------------------------------------------------------------

-- τ-abstracting big step: `p` performs the visible trace `s` (τ's silent) via `─►ᵖ`
data _⟹⟨_⟩ᵖ_ {ℓr} {R : Set ℓr}
    : PTree E I R → List (Event√ R) → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓo ⊔ ℓr) where
  ⟹ᵖ-refl : ∀ {p} → p ⟹⟨ [] ⟩ᵖ p
  ⟹ᵖ-τ    : ∀ {p q r s}               → p ─[ τ ]─►ᵖ q    → q ⟹⟨ s ⟩ᵖ r → p ⟹⟨ s ⟩ᵖ r
  ⟹ᵖ-ev   : ∀ {p q r s} {e : Event√ R} → p ─[ ev e ]─►ᵖ q → q ⟹⟨ s ⟩ᵖ r → p ⟹⟨ e ∷ s ⟩ᵖ r

-- prioritised traces
tracesᵖ : ∀ {ℓr} {R : Set ℓr} → PTree E I R → List (Event√ R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓo ⊔ ℓr)
tracesᵖ P s = Σ[ P′ ∈ PTree E I _ ] (P ⟹⟨ s ⟩ᵖ P′)

-- what `P` offers under prioritisation
Offersᵖ : ∀ {ℓr} {R : Set ℓr} → PTree E I R → Event√ R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓo ⊔ ℓr)
Offersᵖ {R = R} t e = Σ[ t′ ∈ PTree E I R ] (t ─[ ev e ]─►ᵖ t′)

-- a stable `t` refuses `X` under prioritisation: stable, and offers nothing in `X`
Refusesᵖ : ∀ {ℓr ℓx} {R : Set ℓr}
         → PTree E I R → (Event√ R → Set ℓx) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓo ⊔ ℓr ⊔ ℓx)
Refusesᵖ t X = isStable t × (∀ e → X e → ¬ Offersᵖ t e)

-- prioritised (stable) failures
failuresᵖ : ∀ {ℓr ℓx} {R : Set ℓr}
          → PTree E I R → List (Event√ R) → (Event√ R → Set ℓx)
          → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓo ⊔ ℓr ⊔ ℓx)
failuresᵖ P s X = Σ[ P′ ∈ PTree E I _ ] (P ⟹⟨ s ⟩ᵖ P′ × Refusesᵖ P′ X)
