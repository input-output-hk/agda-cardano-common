{-# OPTIONS --guardedness #-}

-- External choice distributes over REPLICATED internal choice (TPC 1.8 / UCS 2.8):
--   P □ ⨅ S = ⨅ { P □ Q ∣ Q ∈ S }.
-- With the finite replicated choice ⨅⁺ (head + tail list, CSP.Operators) this is
--   P □ ⨅⁺ Q qs ≈FD ⨅⁺ (P □ Q) (map (P □_) qs),
-- a one-line induction on the list: the binary □-⊓-dist-FD at each step + ⊓-cong-FD≈ + IH.

open import Level using (Level)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Class.DecEq using (DecEq)

open import Process_Trees

module CSP.Laws.FD.ExtChoiceDistRep {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟ using (_□_; _⊓_; ⨅⁺)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (_≈FD_; ≈FD-refl; ≈FD-trans)
open import CSP.Laws.FD.ExtChoiceFD     E-≟ using (□-⊓-dist-FD)
open import CSP.Laws.FD.FDLawsIChoiceRep E-≟ using (⊓-cong-FD≈)

private
  variable
    ℓr : Level
    R  : Set ℓr

-- □-Dist (T1.8 / U2.8): external choice over a replicated internal choice.
□-Dist : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) (qs : List (PTree E (ExtI E) R))
       → (P □ ⨅⁺ Q qs) ≈FD ⨅⁺ (P □ Q) (map (P □_) qs)
□-Dist P Q []       = ≈FD-refl (P □ Q)
□-Dist P Q (X ∷ xs) =
  ≈FD-trans (□-⊓-dist-FD P Q (⨅⁺ X xs))
            (⊓-cong-FD≈ (≈FD-refl (P □ Q)) (□-Dist P X xs))
