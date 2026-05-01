{-
  Failures-divergences equivalence (`_≃FD_`) on ITrees.

  Defined as the symmetric closure of the failures-divergences refinement
  `_⊑FD_` from `ITree_Relations.FailuresDivergences`:

      P ≃FD Q  iff  (P ⊑FD Q) × (Q ⊑FD P)

  Two top-level results:

    • `≃FD-isEquivalence` — `_≃FD_` is reflexive, symmetric, transitive.
    • `≈⇒≃FD` — every DRWbisim is also a failures-divergences equivalence,
      via the preservation theorems in `ITree_Relations.DRWeakBisim`.

  This is the equivalence under which we expect the full CSP algebra to
  hold (in particular `⊓-assoc`, which fails for `≈ = DRWbisim _≡_`).
-}

{-# OPTIONS --guardedness #-}

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; Σ-syntax)
open import Data.List using (List)
open import Relation.Binary using (Rel; IsEquivalence)

open import Interaction_Trees
open import ITree_Relations.LTS using (Event√)
open import ITree_Relations.FailuresDivergences
open import ITree_Relations.DRWeakBisim

module ITree_Relations.FailuresDivergencesEquiv
  {ℓ ℓe ℓi ℓr : Level}
  {E : Set ℓ → Set ℓe}
  {I : Set ℓ → Set ℓi}
  {R : Set ℓr}
  where

open Failures using (failures)

-----------------------------------------------------------------------------------------
-- Failures-divergences equivalence: refinement in both directions.
_≃FD_ : Rel (ITree E I R) (lsuc (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr))
P ≃FD Q = (P ⊑FD Q) × (Q ⊑FD P)

-----------------------------------------------------------------------------------------
-- `_≃FD_` is an equivalence.
--
-- All three closure laws are immediate from the definition: the
-- ⊑F⊥ and ⊑D refinements are pointwise implications between the
-- failures⊥/divergences sets, which are reflexive (identity), symmetric
-- (in the bidirectional pairing), and transitive (function composition).

≃FD-refl : ∀ {P : ITree E I R} → P ≃FD P
≃FD-refl = ((λ x → x) , (λ x → x)) , ((λ x → x) , (λ x → x))

≃FD-sym : ∀ {P Q : ITree E I R} → P ≃FD Q → Q ≃FD P
≃FD-sym (P⊑Q , Q⊑P) = Q⊑P , P⊑Q

≃FD-trans : ∀ {P Q S : ITree E I R} → P ≃FD Q → Q ≃FD S → P ≃FD S
≃FD-trans ((P⊑F⊥Q , P⊑DQ) , (Q⊑F⊥P , Q⊑DP))
          ((Q⊑F⊥S , Q⊑DS) , (S⊑F⊥Q , S⊑DQ)) =
    ((λ s-fail → P⊑F⊥Q (Q⊑F⊥S s-fail)) , (λ s-div → P⊑DQ (Q⊑DS s-div))) ,
    ((λ p-fail → S⊑F⊥Q (Q⊑F⊥P p-fail)) , (λ p-div → S⊑DQ (Q⊑DP p-div)))

≃FD-isEquivalence : IsEquivalence _≃FD_
≃FD-isEquivalence = record
  { refl  = ≃FD-refl
  ; sym   = ≃FD-sym
  ; trans = ≃FD-trans
  }

-----------------------------------------------------------------------------------------
-- DRWbisim implies FD-equivalence.
--
-- Direct corollary of `failures-preserved` and `divergences-preserved`
-- in `ITree_Relations.DRWeakBisim.Preservation`: lift each component
-- of `failures⊥` (`failures` or `divergences`) along the bisim, and
-- pair the two directions for `_≃FD_`.
module _ where
  open Preservation

  ≈⇒⊑F⊥ : ∀ {P Q : ITree E I R} → P ≈ Q → Q ⊑F⊥ P
  ≈⇒⊑F⊥ bisim (inj₁ failure-P) = inj₁ (failures-preserved bisim failure-P)
  ≈⇒⊑F⊥ bisim (inj₂ div-P)     = inj₂ (divergences-preserved bisim div-P)

  ≈⇒⊑D : ∀ {P Q : ITree E I R} → P ≈ Q → Q ⊑D P
  ≈⇒⊑D bisim div-P = divergences-preserved bisim div-P

  ≈⇒⊑FD : ∀ {P Q : ITree E I R} → P ≈ Q → Q ⊑FD P
  ≈⇒⊑FD bisim = ≈⇒⊑F⊥ bisim , ≈⇒⊑D bisim

  -- Top-level coercion: every DRWbisim is a failures-divergences
  -- equivalence.  Use the symmetry of `≈` to get both refinements.
  ≈⇒≃FD : ∀ {P Q : ITree E I R} → P ≈ Q → P ≃FD Q
  ≈⇒≃FD {P = P} {Q = Q} bisim =
      ≈⇒⊑FD (DRWbisimEquiv.drwbisim-sym ≡-equiv bisim)
    , ≈⇒⊑FD bisim
    where
      open import Prelude using (≡-equiv)
