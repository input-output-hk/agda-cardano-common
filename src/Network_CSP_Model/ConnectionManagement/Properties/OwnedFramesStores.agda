{-# OPTIONS --guardedness #-}

-- Store facts used by frame-ownership proofs. Deletion of the caller's last
-- binding requires unique keys; deletion at another caller does not.
module ConnectionManagement.Properties.OwnedFramesStores where

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Class.DecEq using (DecEq; _≟_)
open import ConnectionManagement.Store using (Store; lookup; delete)
open import ConnectionManagement.Properties.Stores using (UniqueKeys; apart-lookup)

-- Removing a unique key leaves no binding for it.
delete-self : ∀ {K V} ⦃ _ : DecEq K ⦄ (k : K) (xs : Store K V) →
  UniqueKeys xs → lookup k (delete k xs) ≡ nothing
delete-self k [] unique = refl
delete-self k ((q , v) ∷ xs) (apart ∷ unique) with k ≟ q
... | yes refl = apart-lookup k xs apart
... | no neq with k ≟ q
...   | yes eq = ⊥-elim (neq eq)
...   | no _ = delete-self k xs unique

-- Removing another key leaves the complete lookup unchanged.
delete-other : ∀ {K V} ⦃ _ : DecEq K ⦄ (k q : K) (xs : Store K V) →
  q ≢ k → lookup q (delete k xs) ≡ lookup q xs
delete-other k q [] neq = refl
delete-other k q ((r , v) ∷ xs) neq with k ≟ r
... | yes refl with q ≟ k
...   | yes eq = ⊥-elim (neq eq)
...   | no _ = refl
delete-other k q ((r , v) ∷ xs) neq | no _ with q ≟ r
... | yes _ = refl
... | no _ = delete-other k q xs neq
