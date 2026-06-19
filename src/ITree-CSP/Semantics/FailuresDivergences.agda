{-# OPTIONS --guardedness #-}

-- SPIKE: the failures-divergences (FD) model on the pure-react LTS, mirroring
-- PTree_Relations.FailuresDivergences.  Extracts traces / failures / divergences and
-- defines the divergence-strict refinement ⊑FD and FD-equivalence ≈FD.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Relation.Binary using (IsEquivalence; Setoid; Preorder; IsPreorder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Process_Trees

module Semantics.FailuresDivergences {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where
open PTree
open import Semantics.LTS      {ℓ} {ℓe} {ℓi} {E} {I}    using (Event√)
open import Semantics.Failures {ℓ} {ℓe} {ℓi} {E} {I}    using (_⟹⟨_⟩_; ⟹-refl; traces; failures)
open import Semantics.DRBisim  {ℓ} {ℓe} {ℓi} {E} {I}    using (Diverges; div-diverges)

-------------------------------------------------------------------------------------
-- Divergences (divergence-strict): s ∈ div(P) iff some prefix of s weakly reaches a
-- divergent state.
-------------------------------------------------------------------------------------

record IsDivergence {ℓr} {R : Set ℓr}
                    (P : PTree E I R) (s : List (Event√ R))
                  : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  field
    prefix  : List (Event√ R)
    suffix  : List (Event√ R)
    split   : s ≡ prefix ++ suffix
    witness : PTree E I R
    reach   : P ⟹⟨ prefix ⟩ witness
    divwit  : Diverges witness

divergences : ∀ {ℓr} {R : Set ℓr} → PTree E I R → List (Event√ R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
divergences P s = IsDivergence P s

-- divergences are extension-closed: s ∈ div(P) ⇒ s ++ t ∈ div(P)
div-extension-closed : ∀ {ℓr} {R : Set ℓr} {P : PTree E I R} {s t : List (Event√ R)}
                     → IsDivergence P s → IsDivergence P (s ++ t)
div-extension-closed {t = t} d = record
  { prefix  = d .IsDivergence.prefix
  ; suffix  = d .IsDivergence.suffix ++ t
  ; split   = trans (cong (_++ t) (d .IsDivergence.split))
                    (++-assoc (d .IsDivergence.prefix) (d .IsDivergence.suffix) t)
  ; witness = d .IsDivergence.witness
  ; reach   = d .IsDivergence.reach
  ; divwit  = d .IsDivergence.divwit
  }

-- every divergence prefix is a trace
div-prefix-is-trace : ∀ {ℓr} {R : Set ℓr} {P : PTree E I R} {s : List (Event√ R)}
                    → (d : IsDivergence P s) → traces P (d .IsDivergence.prefix)
div-prefix-is-trace d = d .IsDivergence.witness , d .IsDivergence.reach

-- a diverging process has the empty trace as a divergence
empty-div : ∀ {ℓr} {R : Set ℓr} {P : PTree E I R} → Diverges P → IsDivergence P []
empty-div {P = P} dP = record
  { prefix = [] ; suffix = [] ; split = refl ; witness = P ; reach = ⟹-refl ; divwit = dP }

-------------------------------------------------------------------------------------
-- The FD model: divergence-strict failures and refinement orders.
-------------------------------------------------------------------------------------

-- after a divergence every refusal is a failure ("chaos after divergence")
failures⊥ : ∀ {ℓr} {R : Set ℓr}
          → PTree E I R → List (Event√ R) → (Event√ R → Set ℓr)
          → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
failures⊥ P s B = failures P s B ⊎ divergences P s

_⊑F⊥_ : ∀ {ℓr} {R : Set ℓr} → PTree E I R → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ lsuc ℓr)
_⊑F⊥_ {ℓr = ℓr} {R = R} P Q =
  ∀ {s} {B : Event√ R → Set ℓr} → failures⊥ Q s B → failures⊥ P s B

_⊑D_ : ∀ {ℓr} {R : Set ℓr} → PTree E I R → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
_⊑D_ P Q = ∀ {s} → divergences Q s → divergences P s

_⊑FD_ : ∀ {ℓr} {R : Set ℓr} → PTree E I R → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ lsuc ℓr)
P ⊑FD Q = (P ⊑F⊥ Q) × (P ⊑D Q)

-- FD-equivalence: mutual refinement
_≈FD_ : ∀ {ℓr} {R : Set ℓr} → PTree E I R → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ lsuc ℓr)
P ≈FD Q = (P ⊑FD Q) × (Q ⊑FD P)

-------------------------------------------------------------------------------------
-- ⊑FD is a preorder, ≈FD an equivalence (all by subset reasoning)
-------------------------------------------------------------------------------------

⊑FD-refl : ∀ {ℓr} {R : Set ℓr} (P : PTree E I R) → P ⊑FD P
⊑FD-refl P = (λ f → f) , (λ d → d)

⊑FD-trans : ∀ {ℓr} {R : Set ℓr} {P Q S : PTree E I R} → P ⊑FD Q → Q ⊑FD S → P ⊑FD S
⊑FD-trans (pqF , pqD) (qsF , qsD) = (λ f → pqF (qsF f)) , (λ d → pqD (qsD d))

≈FD-refl : ∀ {ℓr} {R : Set ℓr} (P : PTree E I R) → P ≈FD P
≈FD-refl P = ⊑FD-refl P , ⊑FD-refl P

≈FD-sym : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} → P ≈FD Q → Q ≈FD P
≈FD-sym (pq , qp) = qp , pq

≈FD-trans : ∀ {ℓr} {R : Set ℓr} {P Q S : PTree E I R} → P ≈FD Q → Q ≈FD S → P ≈FD S
≈FD-trans (pq , qp) (qs , sq) = ⊑FD-trans pq qs , ⊑FD-trans sq qp

-------------------------------------------------------------------------------------
-- Demonstrator: div is "chaos after []" — divergent at the empty trace, hence refuses
-- everything there in the FD model (this is what distinguishes div from deadlock).
-------------------------------------------------------------------------------------

div-divergence : ∀ {ℓr} {R : Set ℓr} → divergences (div {E = E} {I = I} {R = R}) []
div-divergence = empty-div div-diverges

div-chaos : ∀ {ℓr} {R : Set ℓr} {B : Event√ R → Set ℓr}
          → failures⊥ (div {E = E} {I = I} {R = R}) [] B
div-chaos = inj₂ div-divergence

-- failures-divergences equivalence is an equivalence relation:
≈FD-isEquivalence : ∀ {ℓr} {R : Set ℓr} → IsEquivalence (_≈FD_ {R = R})
≈FD-isEquivalence = record
  { refl  = λ {x} → ≈FD-refl x
  ; sym   = ≈FD-sym
  ; trans = ≈FD-trans
  }

≈FD-setoid : ∀ {ℓr} (R : Set ℓr) → Setoid _ _
≈FD-setoid R = record
  { Carrier       = PTree E I R
  ; _≈_           = _≈FD_
  ; isEquivalence = ≈FD-isEquivalence
  }

⊑FD-preorder : ∀ {ℓr} (R : Set ℓr) → Preorder _ _ _
⊑FD-preorder R = record
  { Carrier    = PTree E I R
  ; _≈_        = _≈FD_
  ; _≲_        = _⊑FD_
  ; isPreorder = record
      { isEquivalence = ≈FD-isEquivalence
      ; reflexive     = proj₁
      ; trans         = ⊑FD-trans
      }
  }
