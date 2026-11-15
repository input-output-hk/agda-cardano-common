{-# OPTIONS --guardedness #-}

-- Finite-list plumbing keeps exploration independent of decidable state/action
-- equality. Duplicates are harmless: enumeration is a list, not a set quotient.
module ConnectionManagement.Exploration.Finite where

open import Level using (Level; _⊔_)
open import Data.List using (List; []; _∷_; map; concatMap)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

infix 4 _∈_
data _∈_ {ℓ} {A : Set ℓ} (x : A) : List A → Set ℓ where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

map-in : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} (f : A → B) {x xs} → x ∈ xs → f x ∈ map f xs
map-in f here = here
map-in f (there p) = there (map-in f p)
map-out : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} (f : A → B) {y xs} → y ∈ map f xs →
  Σ A (λ x → x ∈ xs × y ≡ f x)
map-out f {xs = _ ∷ _} here = _ , here , refl
map-out f {xs = _ ∷ _} (there p) with map-out f p
... | x , member , eq = x , there member , eq

open import Data.List using (_++_)
left : ∀ {ℓ} {A : Set ℓ} {x : A} {xs} ys → x ∈ xs → x ∈ (xs ++ ys)
left ys here = here
left ys (there p) = there (left ys p)
right : ∀ {ℓ} {A : Set ℓ} {x : A} xs {ys} → x ∈ ys → x ∈ (xs ++ ys)
right [] p = p
right (_ ∷ xs) p = there (right xs p)

data Either {ℓ ℓ′} (A : Set ℓ) (B : Set ℓ′) : Set (ℓ ⊔ ℓ′) where
  inl : A → Either A B
  inr : B → Either A B
split : ∀ {ℓ} {A : Set ℓ} {x : A} xs {ys} → x ∈ (xs ++ ys) → Either (x ∈ xs) (x ∈ ys)
split [] p = inr p
split (_ ∷ xs) here = inl here
split (_ ∷ xs) (there p) with split xs p
... | inl q = inl (there q)
... | inr q = inr q

bind-in : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} (f : A → List B) {x xs y} →
  x ∈ xs → y ∈ f x → y ∈ concatMap f xs
bind-in f here q = left _ q
bind-in f (there p) q = right _ (bind-in f p q)
bind-out : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} (f : A → List B) {xs y} → y ∈ concatMap f xs →
  Σ A (λ x → x ∈ xs × y ∈ f x)
bind-out f {xs = x ∷ xs} p with split (f x) p
... | inl q = x , here , q
... | inr q with bind-out f q
...   | z , member , found = z , there member , found

-- Every element of a finite alphabet is available at every search position.
open import Data.Unit.Polymorphic using (⊤; tt)
Covered : ∀ {ℓ} {A : Set ℓ} → List A → List A → Set ℓ
Covered [] alphabet = ⊤
Covered (a ∷ as) alphabet = a ∈ alphabet × Covered as alphabet
self-covered : ∀ {ℓ} {A : Set ℓ} (xs : List A) → Covered xs xs
self-covered [] = tt
self-covered (x ∷ xs) = here , weaken xs (self-covered xs)
  where
  weaken : ∀ {ℓ} {A : Set ℓ} {x : A} (ys : List A) {zs} → Covered ys zs → Covered ys (x ∷ zs)
  weaken [] p = tt
  weaken (_ ∷ ys) (p , ps) = there p , weaken ys ps

covered-weaken : ∀ {ℓ} {A : Set ℓ} {as xs ys : List A} →
  (∀ {a} → a ∈ xs → a ∈ ys) → Covered as xs → Covered as ys
covered-weaken {as = []} f p = tt
covered-weaken {as = a ∷ as} f (p , ps) = f p , covered-weaken {as = as} f ps
covered-left : ∀ {ℓ} {A : Set ℓ} (xs : List A) ys → Covered xs (xs ++ ys)
covered-left xs ys = covered-weaken {as = xs} (left ys) (self-covered xs)
