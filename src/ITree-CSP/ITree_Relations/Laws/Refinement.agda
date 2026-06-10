{-# OPTIONS --guardedness #-}

module ITree_Relations.Laws.Refinement where

------------------------------------------------------------------------
-- Order-theoretic properties of the refinement relations defined in
-- ITree_Relations.LTS and ITree_Relations.FailuresDivergences.
--
-- For each `_⊑X_`, this module establishes:
--   * Reflexivity:  P ⊑X P
--   * Transitivity: P ⊑X Q → Q ⊑X R → P ⊑X R
-- and, where a companion equivalence exists, antisymmetry into that
-- equivalence.
------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Product using (_,_; _×_; proj₁; proj₂)

open import Interaction_Trees using (ITree)
open import ITree_Relations.LTS
open Traces using (traces; _⊑ᵀ_)
open import ITree_Relations.FailuresDivergences
open Failures using (_ref_; failures; _⊑F_)
open import ITree_Relations.FailuresDivergencesEquiv using (_≃FD_)

variable
  ℓ ℓe ℓi ℓr : Level
  E : Set ℓ → Set ℓe
  I : Set ℓ → Set ℓi
  R : Set ℓr

------------------------------------------------------------------------
-- §1. Reflexivity
------------------------------------------------------------------------

⊑ᵀ-refl : ∀ {ℓ ℓe ℓi ℓr}
            {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
            {P : ITree E I R}
          → P ⊑ᵀ P
⊑ᵀ-refl tr = tr

⊑F-refl : ∀ {ℓ ℓe ℓi ℓr ℓB}
            {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
            {P : ITree E I R}
          → _⊑F_ {ℓB = ℓB} P P
⊑F-refl f = f

⊑F⊥-refl : ∀ {ℓ ℓe ℓi ℓr ℓB}
             {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
             {P : ITree E I R}
           → _⊑F⊥_ {ℓB = ℓB} P P
⊑F⊥-refl f = f

⊑D-refl : ∀ {ℓ ℓe ℓi ℓr}
            {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
            {P : ITree E I R}
          → P ⊑D P
⊑D-refl d = d

⊑FD-refl : ∀ {ℓ ℓe ℓi ℓr ℓB}
             {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
             {P : ITree E I R}
           → _⊑FD_ {ℓB = ℓB} P P
⊑FD-refl = ⊑F⊥-refl , ⊑D-refl

------------------------------------------------------------------------
-- §2. Transitivity
------------------------------------------------------------------------

⊑ᵀ-trans : ∀ {ℓ ℓe ℓi ℓr}
             {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
             {P Q R' : ITree E I R}
           → P ⊑ᵀ Q → Q ⊑ᵀ R' → P ⊑ᵀ R'
⊑ᵀ-trans pq qr tr = pq (qr tr)

⊑F-trans : ∀ {ℓ ℓe ℓi ℓr ℓB}
             {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
             {P Q R' : ITree E I R}
           → _⊑F_ {ℓB = ℓB} P Q → _⊑F_ {ℓB = ℓB} Q R' → _⊑F_ {ℓB = ℓB} P R'
⊑F-trans pq qr f = pq (qr f)

⊑F⊥-trans : ∀ {ℓ ℓe ℓi ℓr ℓB}
              {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
              {P Q R' : ITree E I R}
            → _⊑F⊥_ {ℓB = ℓB} P Q → _⊑F⊥_ {ℓB = ℓB} Q R' → _⊑F⊥_ {ℓB = ℓB} P R'
⊑F⊥-trans pq qr f⊥ = pq (qr f⊥)

⊑D-trans : ∀ {ℓ ℓe ℓi ℓr}
             {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
             {P Q R' : ITree E I R}
           → P ⊑D Q → Q ⊑D R' → P ⊑D R'
⊑D-trans pq qr d = pq (qr d)

⊑FD-trans : ∀ {ℓ ℓe ℓi ℓr ℓB}
              {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
              {P Q R' : ITree E I R}
            → _⊑FD_ {ℓB = ℓB} P Q → _⊑FD_ {ℓB = ℓB} Q R' → _⊑FD_ {ℓB = ℓB} P R'
⊑FD-trans pq qr = ⊑F⊥-trans (proj₁ pq) (proj₁ qr)
                , ⊑D-trans  (proj₂ pq) (proj₂ qr)

------------------------------------------------------------------------
-- §3. Trace equivalence and antisymmetry
--
-- `_≃ᵀ_` is the trace-equivalence relation: P and Q have the same
-- traces.  It pairs `_⊑ᵀ_` in both directions, mirroring how `_≃FD_`
-- pairs `_⊑FD_` in `ITree_Relations.FailuresDivergencesEquiv`.
------------------------------------------------------------------------

_≃ᵀ_ : ∀ {ℓ ℓe ℓi ℓr}
         {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
       → ITree E I R → ITree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
P ≃ᵀ Q = (P ⊑ᵀ Q) × (Q ⊑ᵀ P)

⊑ᵀ-antisym : ∀ {ℓ ℓe ℓi ℓr}
               {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
               {P Q : ITree E I R}
             → P ⊑ᵀ Q → Q ⊑ᵀ P → P ≃ᵀ Q
⊑ᵀ-antisym pq qp = pq , qp

⊑FD-antisym : ∀ {ℓ ℓe ℓi ℓr ℓB}
                {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                {P Q : ITree E I R}
              → _⊑FD_ {ℓB = ℓB} P Q → _⊑FD_ {ℓB = ℓB} Q P → _≃FD_ {ℓB = ℓB} P Q
⊑FD-antisym pq qp = pq , qp

------------------------------------------------------------------------
-- §4. Sanity: documented composition examples (no-op at runtime).
------------------------------------------------------------------------

private
  _ : ∀ {ℓ ℓe ℓi ℓr ℓB}
        {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
        {P Q R' : ITree E I R}
      → _⊑FD_ {ℓB = ℓB} P Q → _⊑FD_ {ℓB = ℓB} Q R' → _⊑FD_ {ℓB = ℓB} P R'
  _ = ⊑FD-trans

  _ : ∀ {ℓ ℓe ℓi ℓr ℓB}
        {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
        {P : ITree E I R}
      → _⊑FD_ {ℓB = ℓB} P P
  _ = ⊑FD-refl
