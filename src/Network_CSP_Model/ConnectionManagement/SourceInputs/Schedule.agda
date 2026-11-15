{-# OPTIONS --guardedness #-}

-- Replace a derived input at a certified position without normalizing a run.
module ConnectionManagement.SourceInputs.Schedule where
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

at : ∀ {A : Set} → ℕ → List A → Maybe A
at _ [] = nothing
at zero (x ∷ xs) = just x
at (suc n) (x ∷ xs) = at n xs
replace : ∀ {A : Set} → ℕ → A → List A → List A
replace _ y [] = []
replace zero y (x ∷ xs) = y ∷ xs
replace (suc n) y (x ∷ xs) = x ∷ replace n y xs
replace-same : ∀ {A : Set} (n : ℕ) (y : A) (xs : List A) →
  at n xs ≡ just y → replace n y xs ≡ xs
replace-same _ _ [] ()
replace-same zero y (x ∷ xs) refl = refl
replace-same (suc n) y (x ∷ xs) eq = cong (x ∷_) (replace-same n y xs eq)
