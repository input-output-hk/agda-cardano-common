{-# OPTIONS --guardedness #-}

-- Explicit finite carriers for typed identifiers: serials strictly below n.
module ConnectionManagement.Exploration.Identities where

open import Data.Nat using (ℕ; zero; suc; _⊔_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; m≤m⊔n; m≤n⊔m)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_)
open import ConnectionManagement.Domain using (IdKind; Id; ident; serial)
open import ConnectionManagement.Exploration.Finite

ids : ∀ {k} → ℕ → List (Id k)
ids zero = []
ids {k} (suc n) = ident zero ∷ map (λ x → ident (suc (serial x))) (ids {k} n)
ids-complete : ∀ {k n} (x : Id k) → serial x < n → x ∈ ids n
ids-complete {n = suc n} (ident zero) p = here
ids-complete {n = suc n} (ident (suc m)) (s≤s p) =
  there (map-in (λ x → ident (suc (serial x))) (ids-complete (ident m) p))

-- Store keys and promises are bounded by the same explicit allocation cutoff.
maxIds : ∀ {k} → List (Id k) → ℕ
maxIds [] = 0
maxIds (x ∷ xs) = suc (serial x) ⊔ maxIds xs
maxIds-member : ∀ {k} {x : Id k} {xs n} → x ∈ xs → maxIds xs ≤ n → x ∈ ids n
maxIds-member {xs = x ∷ xs} here bound =
  ids-complete x (≤-trans (m≤m⊔n (suc (serial x)) (maxIds xs)) bound)
maxIds-member {xs = x ∷ xs} (there member) bound =
  maxIds-member member (≤-trans (m≤n⊔m (suc (serial x)) (maxIds xs)) bound)
