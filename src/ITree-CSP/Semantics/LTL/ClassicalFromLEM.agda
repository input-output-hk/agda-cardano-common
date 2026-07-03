{-# OPTIONS --guardedness #-}

-- CERTIFICATION ONLY — DO NOT IMPORT THIS MODULE IN PROOFS.
--
-- Certifies that the classical postulates of Semantics.LTL.Traces_Based are
-- derivable from a single double-negation-elimination axiom `dne` (≡ LEM) —
-- i.e. they are "just classical logic", not ad-hoc. Mirrors the
-- CSP.Laws.ClassicalFromLEM soundness-witness convention.
--
--   ⟦G⟧⇒⟦G⟧⁺   (G ⇒ its positive Π-form ∀n.⟦φ⟧(drop n))   — pointwise dne
--   ¬G⇒F¬       (De Morgan: ⟦¬(G φ)⟧ ⇒ ⟦F(¬φ)⟧)             — single dne
--   ¬F⇒G¬       (De Morgan: ⟦¬(F φ)⟧ ⇒ ⟦G(¬φ)⟧)             — CONSTRUCTIVE, no dne
--                (already a theorem in Traces_Based; re-derived here as a witness)
--
-- IMPORTANT: nothing in the development imports this module, and nothing should —
-- importing it would leak the strong `dne` axiom into the LTL layer. Standalone
-- soundness witness, kept green but never depended on.

open import Level using (Lift; lift; lower)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Classical using (dne)

module Semantics.LTL.ClassicalFromLEM
  {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where

open import Semantics.LTL.Traces_Based {ℓ} {ℓe} {ℓi} {E} {I}

-- The single classical axiom `dne` is shared from the common `Classical`
-- module (imported above); see its header for the soundness rationale.

-- ⟦ G_ φ ⟧ tr ≡ ∀n.¬¬⟦φ⟧(drop n tr); one dne per index n.
⟦G⟧⇒⟦G⟧⁺-fromLEM : ∀ {ℓr ℓa} {R : Set ℓr}
     {t} {φ : LTLᵗ ℓa R} {tr : Trace R t}
   → ⟦ G_ φ ⟧ tr → ⟦G⟧⁺ φ tr
⟦G⟧⇒⟦G⟧⁺-fromLEM {tr = tr} H n =
  dne (λ np → lower (H (n , (λ p → lift (np p)) , (λ _ _ → lift tt))))

-- ⟦ ¬ (G_ φ) ⟧ tr reduces to ¬¬⟦ F_ (¬ φ) ⟧ tr; a single dne.
¬G⇒F¬-fromLEM : ∀ {ℓr ℓa} {R : Set ℓr}
     {t} {φ : LTLᵗ ℓa R} {tr : Trace R t}
   → ⟦ ¬ (G_ φ) ⟧ tr → ⟦ F_ (¬ φ) ⟧ tr
¬G⇒F¬-fromLEM H = dne (λ na → lower (H (λ a → lift (na a))))

-- Witness that ¬F⇒G¬ needs NO LEM (constructive); identical to the
-- theorem now living in Traces_Based.
¬F⇒G¬-constructive : ∀ {ℓr ℓa} {R : Set ℓr}
     {t} {φ : LTLᵗ ℓa R} {tr : Trace R t}
   → ⟦ ¬ (F_ φ) ⟧ tr → ⟦ G_ (¬ φ) ⟧ tr
¬F⇒G¬-constructive notF (n , nnφ , bef) = nnφ (λ p → notF (n , p , bef))
