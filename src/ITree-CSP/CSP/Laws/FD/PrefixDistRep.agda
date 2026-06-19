{-# OPTIONS --guardedness #-}

-- Prefix distributes over REPLICATED internal choice (TPC 1.10 / UCS 2.10):
--   a → ⨅ S = ⨅ { a → Q ∣ Q ∈ S }.
-- With the finite replicated choice ⨅⁺ this is
--   Prefix₀ e (⨅⁺ Q qs) ≈FD ⨅⁺ (Prefix₀ e Q) (map (Prefix₀ e) qs),
-- a one-line induction: the binary prefix-dist ⟶₀-⊓-dist-FD at each step + ⊓-cong-FD≈ + IH.
-- (Exact analogue of ⨅⁺-flatten / □-Dist.)

open import Level using (Level)
open import Data.List using (List; []; _∷_; map)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Process_Trees

module CSP.Laws.FD.PrefixDistRep {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟ using (Prefix₀; _⊓_; ⨅⁺)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (_≈FD_; ≈FD-refl; ≈FD-trans)
open import CSP.Laws.FD.FDLawsPrefixDist E-≟ using (⟶₀-⊓-dist-FD)
open import CSP.Laws.FD.FDLawsIChoiceRep E-≟ using (⊓-cong-FD≈)

private
  variable
    ℓr : Level
    R  : Set ℓr
    A  : Set ℓ

prefix-Dist : (e : E A) (P : PTree E (ExtI E) R) (qs : List (PTree E (ExtI E) R))
            → (Prefix₀ e (⨅⁺ P qs)) ≈FD ⨅⁺ (Prefix₀ e P) (map (Prefix₀ e) qs)
prefix-Dist e P []       = ≈FD-refl (Prefix₀ e P)
prefix-Dist e P (X ∷ xs) =
  ≈FD-trans (⟶₀-⊓-dist-FD e P (⨅⁺ X xs))
            (⊓-cong-FD≈ (≈FD-refl (Prefix₀ e P)) (prefix-Dist e X xs))
