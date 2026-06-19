{-# OPTIONS --guardedness #-}

open import Level using (Level; Lift; lift; lower)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; _×_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees

module CSP.Laws.FD.ChoiceRefine {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open import CSP.Operators E-≟
open import Semantics.LTS                 {E = E} {I = ExtI E}
open import Semantics.Failures            {E = E} {I = ExtI E} using (_⊑T_)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (_⊑FD_; _⊑F⊥_; _⊑D_; failures⊥; divergences)
open import CSP.Laws.FD.ExtChoiceFD         E-≟ using (□-failures⊥-elim; □-div-elim)
open import CSP.Laws.FD.FDLawsIChoiceAssoc  E-≟
  using (⊓-failures⊥←l; ⊓-failures⊥←r; ⊓-div←l; ⊓-div←r)
open import CSP.Laws.FD.FDLawsPrefixDist    E-≟
  using (prefix₀-failures⊥→; prefix₀-failures⊥-nil; prefix₀-failures⊥-cons;
         prefix₀-refuses; prefix₀-div→; prefix₀-div-cons)

-- divergences of (P □ Q) are divergences of (P ⊓ Q)
⊓⊑D□ : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄
       (P Q : PTree E (ExtI E) R) → (P ⊓ Q) ⊑D (P □ Q)
⊓⊑D□ P Q d with □-div-elim {P = P} {Q = Q} d
... | inj₁ dP = ⊓-div←l P Q dP
... | inj₂ dQ = ⊓-div←r P Q dQ

-- failures⊥ of (P □ Q) are failures⊥ of (P ⊓ Q)
⊓⊑F⊥□ : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄
        (P Q : PTree E (ExtI E) R) → (P ⊓ Q) ⊑F⊥ (P □ Q)
⊓⊑F⊥□ P Q f⊥ with □-failures⊥-elim {P = P} {Q = Q} f⊥
... | inj₁ fP = ⊓-failures⊥←l P Q fP
... | inj₂ fQ = ⊓-failures⊥←r P Q fQ

-- external choice refines internal choice in the FD model
⊓⊑FD□ : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄
        (P Q : PTree E (ExtI E) R) → (P ⊓ Q) ⊑FD (P □ Q)
⊓⊑FD□ P Q = ⊓⊑F⊥□ P Q , ⊓⊑D□ P Q

-- prefix is FD-monotone in its continuation
⟶₀-mono-⊑FD : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr} ⦃ _ : DecEq R ⦄
              (e : E A) {P Q : PTree E (ExtI E) R}
            → P ⊑FD Q → (Prefix₀ e P) ⊑FD (Prefix₀ e Q)
⟶₀-mono-⊑FD e {P} {Q} (Q⊑F⊥ , Q⊑D) = F⊥-part , D-part
  where
    F⊥-part : (Prefix₀ e P) ⊑F⊥ (Prefix₀ e Q)
    F⊥-part fQ with prefix₀-failures⊥→ e Q fQ
    ... | inj₁ (refl , ref)         =
            prefix₀-failures⊥-nil e P (prefix₀-refuses e Q P ref)
    ... | inj₂ (x , t , refl , fbQ) =
            prefix₀-failures⊥-cons e P x (Q⊑F⊥ fbQ)

    D-part : (Prefix₀ e P) ⊑D (Prefix₀ e Q)
    D-part dQ with prefix₀-div→ e Q dQ
    ... | (x , t , refl , dQt) = prefix₀-div-cons e P x (Q⊑D dQt)
