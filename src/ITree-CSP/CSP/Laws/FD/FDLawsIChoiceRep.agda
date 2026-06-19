{-# OPTIONS --guardedness #-}

-- Replicated (indexed) internal choice ⨅ and its FLATTEN / associativity law (UCS 13.20):
--   ⨅(S ∪ {⨅T}) = ⨅(S ∪ T),  i.e.  (⨅ S) ⊓ (⨅ T) = ⨅ (S ∪ T).
--
-- For a finite non-empty set, Roscoe's ⨅ S is exactly iterated binary ⊓; the operator
-- `⨅⁺ P ps` (head + tail list, right-folded by ⊓) is defined in CSP.Operators.  The flatten
-- law is then a one-line induction: ⊓-assoc + ⊓-cong + IH.
-- (Set semantics — order/duplicate irrelevance — is the FD-meaning's invariance under
-- ⊓-comm/⊓-idem, already proved; not needed for flatten itself.)
--
-- We also prove the ≈FD-premised ⊓ CONGRUENCE `⊓-cong-FD≈` (the existing ⊓-cong-FD
-- needs DRbisim premises, too strong here) directly from the ⊓ FD decomposition.

open import Level using (Level)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Process_Trees

module CSP.Laws.FD.FDLawsIChoiceRep {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟ using (_⊓_; ⨅⁺)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (_≈FD_; ≈FD-refl; ≈FD-trans)
open import CSP.Laws.FD.FDLawsIChoiceAssoc E-≟
  using (⊓-assoc-FD; ⊓-failures⊥→; ⊓-failures⊥←l; ⊓-failures⊥←r; ⊓-div→; ⊓-div←l; ⊓-div←r)

private
  variable
    ℓr : Level
    R  : Set ℓr

-- ≈FD-premised ⊓ congruence (route a behaviour of one composite through the FD
-- decomposition, transport along the operand equivalence, recompose).
⊓-cong-FD≈ : {P P′ Q Q′ : PTree E (ExtI E) R}
           → P ≈FD P′ → Q ≈FD Q′ → (P ⊓ Q) ≈FD (P′ ⊓ Q′)
⊓-cong-FD≈ {P = P} {P′ = P′} {Q = Q} {Q′ = Q′}
           ((pF , pD) , (pF′ , pD′)) ((qF , qD) , (qF′ , qD′)) =
    ( (λ f → [ (λ fP′ → ⊓-failures⊥←l P Q (pF fP′)) , (λ fQ′ → ⊓-failures⊥←r P Q (qF fQ′)) ]′
               (⊓-failures⊥→ P′ Q′ f))
    , (λ d → [ (λ dP′ → ⊓-div←l P Q (pD dP′)) , (λ dQ′ → ⊓-div←r P Q (qD dQ′)) ]′
               (⊓-div→ P′ Q′ d)) )
  , ( (λ f → [ (λ fP → ⊓-failures⊥←l P′ Q′ (pF′ fP)) , (λ fQ → ⊓-failures⊥←r P′ Q′ (qF′ fQ)) ]′
               (⊓-failures⊥→ P Q f))
    , (λ d → [ (λ dP → ⊓-div←l P′ Q′ (pD′ dP)) , (λ dQ → ⊓-div←r P′ Q′ (qD′ dQ)) ]′
               (⊓-div→ P Q d)) )

-- FLATTEN (U13.20): (⨅ S) ⊓ (⨅ T) ≈FD ⨅ (S ++ T).  Nesting ⨅T as one element of the
-- outer choice and then flattening is the same as choosing over the union.
⨅⁺-flatten : (P : PTree E (ExtI E) R) (ps : List (PTree E (ExtI E) R))
             (Q : PTree E (ExtI E) R) (qs : List (PTree E (ExtI E) R))
           → (⨅⁺ P ps ⊓ ⨅⁺ Q qs) ≈FD ⨅⁺ P (ps ++ Q ∷ qs)
⨅⁺-flatten P []       Q qs = ≈FD-refl (P ⊓ ⨅⁺ Q qs)
⨅⁺-flatten P (X ∷ xs) Q qs =
  ≈FD-trans (⊓-assoc-FD P (⨅⁺ X xs) (⨅⁺ Q qs))
            (⊓-cong-FD≈ (≈FD-refl P) (⨅⁺-flatten X xs Q qs))
