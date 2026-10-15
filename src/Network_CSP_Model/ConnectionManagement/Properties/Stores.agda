{-# OPTIONS --guardedness #-}

-- Representation lemmas for the local association stores, using the standard
-- library's All/AllPairs predicates. No whole-machine invariant is assumed.
module ConnectionManagement.Properties.Stores where

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (proj₁; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)
open import Class.DecEq using (DecEq; _≟_)
open import ConnectionManagement.Store using (Store; lookup; put; delete)

-- Values are deliberately ignored: uniqueness concerns store keys.
UniqueKeys : ∀ {K V} → Store K V → Set
UniqueKeys = AllPairs (λ x y → proj₁ x ≢ proj₁ y)

KeysSatisfy : ∀ {K V} → (K → Set) → Store K V → Set
KeysSatisfy P = All (λ binding → P (proj₁ binding))

-- Updates and deletions preserve arbitrary predicates on retained keys.
put-keys : ∀ {K V} ⦃ _ : DecEq K ⦄ (P : K → Set) k (v : V) xs →
  P k → KeysSatisfy P xs → KeysSatisfy P (put k v xs)
put-keys P k v [] pk [] = pk ∷ []
put-keys P k v ((q , old) ∷ xs) pk (pq ∷ ps) with k ≟ q
... | yes _ = pk ∷ ps
... | no _ = pq ∷ put-keys P k v xs pk ps

delete-keys : ∀ {K V} ⦃ _ : DecEq K ⦄ (P : K → Set) k (xs : Store K V) →
  KeysSatisfy P xs → KeysSatisfy P (delete k xs)
delete-keys P k [] [] = []
delete-keys P k ((q , old) ∷ xs) (pq ∷ ps) with k ≟ q
... | yes _ = ps
... | no _ = pq ∷ delete-keys P k xs ps

put-unique : ∀ {K V} ⦃ _ : DecEq K ⦄ (k : K) (v : V) (xs : Store K V) →
  UniqueKeys xs → UniqueKeys (put k v xs)
put-unique k v [] [] = [] ∷ []
put-unique k v ((q , old) ∷ xs) (apart ∷ unique) with k ≟ q
... | yes refl = apart ∷ unique
... | no neq = put-keys (λ r → q ≢ r) k v xs (λ eq → neq (sym eq)) apart ∷
  put-unique k v xs unique

delete-unique : ∀ {K V} ⦃ _ : DecEq K ⦄ k (xs : Store K V) →
  UniqueKeys xs → UniqueKeys (delete k xs)
delete-unique k [] [] = []
delete-unique k ((q , old) ∷ xs) (apart ∷ unique) with k ≟ q
... | yes _ = unique
... | no _ = delete-keys (λ r → q ≢ r) k xs apart ∷ delete-unique k xs unique

-- A structurally absent key cannot be found by lookup, even in a nonunique store.
apart-lookup : ∀ {K V} ⦃ _ : DecEq K ⦄ k (xs : Store K V) →
  KeysSatisfy (λ q → k ≢ q) xs → lookup k xs ≡ nothing
apart-lookup k [] [] = refl
apart-lookup k ((q , old) ∷ xs) (neq ∷ rest) with k ≟ q
... | yes eq = ⊥-elim (neq eq)
... | no _ = apart-lookup k xs rest

-- Uniqueness makes lookup coverage sufficient for traversal-wide properties.
lookup-head : ∀ {K V} ⦃ _ : DecEq K ⦄ (k : K) (v : V) xs →
  lookup k ((k , v) ∷ xs) ≡ just v
lookup-head k v xs with k ≟ k
... | yes _ = refl
... | no neq = ⊥-elim (neq refl)

lookup-properties : ∀ {K V} ⦃ _ : DecEq K ⦄ (P : V → Set) (xs : Store K V) →
  UniqueKeys xs → (∀ k v → lookup k xs ≡ just v → P v) →
  All (λ binding → P (Data.Product.proj₂ binding)) xs
lookup-properties P [] [] valid = []
lookup-properties P ((q , old) ∷ xs) (apart ∷ unique) valid =
  valid q old (lookup-head q old xs) ∷ lookup-properties P xs unique tail-valid
  where
  tail-valid : ∀ k v → lookup k xs ≡ just v → P v
  tail-valid k v eq with k ≟ q
  ... | yes refl with trans (sym (apart-lookup k xs apart)) eq
  ...   | ()
  tail-valid k v eq | no neq = valid k v lifted
    where
    lifted : lookup k ((q , old) ∷ xs) ≡ just v
    lifted with k ≟ q
    ... | yes equal = ⊥-elim (neq equal)
    ... | no _ = eq

-- Value predicates are also preserved when a replacement satisfies them.
put-values : ∀ {K V} ⦃ _ : DecEq K ⦄ (P : V → Set) (k : K) v xs →
  P v → All (λ binding → P (Data.Product.proj₂ binding)) xs →
  All (λ binding → P (Data.Product.proj₂ binding)) (put k v xs)
put-values P k v [] pv [] = pv ∷ []
put-values P k v ((q , old) ∷ xs) pv (p ∷ ps) with k ≟ q
... | yes _ = pv ∷ ps
... | no _ = p ∷ put-values P k v xs pv ps

delete-values : ∀ {K V} ⦃ _ : DecEq K ⦄ (P : V → Set) (k : K) xs →
  All (λ binding → P (Data.Product.proj₂ binding)) xs →
  All (λ binding → P (Data.Product.proj₂ binding)) (delete k xs)
delete-values P k [] [] = []
delete-values P k ((q , old) ∷ xs) (p ∷ ps) with k ≟ q
... | yes _ = ps
... | no _ = p ∷ delete-values P k xs ps
