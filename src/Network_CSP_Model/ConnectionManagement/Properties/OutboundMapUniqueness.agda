{-# OPTIONS --guardedness #-}

-- The two outbound map writers preserve nested key uniqueness. This is a
-- helper layer reused by the current/captured-map dispatcher invariants.
module ConnectionManagement.Properties.OutboundMapUniqueness where

open import Data.Bool using (Bool; true; false; T?)
open import Data.List using ([]; _∷_; filterᵇ)
open import Data.List.Relation.Unary.AllPairs.Properties using (filter⁺)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (Store; lookup; put; delete)
open import ConnectionManagement.State
open import ConnectionManagement.Properties.Stores
open import ConnectionManagement.Properties.MapUniqueness
open import ConnectionManagement.Properties.Counters using (lookup-all)
import ConnectionManagement.Rules.OutboundAcquire as A

-- Reuse the standard library's AllPairs filter law for association keys.
filter-unique : ∀ {K V : Set} (p : K Data.Product.× V → Bool) xs →
  UniqueKeys xs → UniqueKeys (filterᵇ p xs)
filter-unique p xs = filter⁺ (λ x → T? (p x))

-- Replacing a reservation with a concrete local key, including collisions,
-- preserves both outer and inner uniqueness; the success flag is irrelevant.
update-local-unique : ∀ k m → MapUnique m → MapUnique (proj₂ (A.updateLocal k m))
update-local-unique k m (outer , inners) with lookup (remote k) m in found
... | nothing = outer , inners
... | just inner with lookup unknownLocal inner
...   | nothing = outer , inners
...   | just e with lookup (knownLocal (local k)) inner
...     | just _ = put-unique (remote k) (delete unknownLocal inner) m outer ,
  put-values UniqueKeys (remote k) (delete unknownLocal inner) m
    (delete-unique unknownLocal inner (lookup-all UniqueKeys (remote k) m inners found)) inners
...     | nothing = put-unique (remote k) (put (knownLocal (local k)) e (delete unknownLocal inner)) m outer ,
  put-values UniqueKeys (remote k) (put (knownLocal (local k)) e (delete unknownLocal inner)) m
    (put-unique (knownLocal (local k)) e (delete unknownLocal inner)
      (delete-unique unknownLocal inner (lookup-all UniqueKeys (remote k) m inners found))) inners

-- Failure cleanup filters aliases and removes an empty remote bucket.
remove-aliases-unique : ∀ p e m → MapUnique m → MapUnique (A.removeAliases p e m)
remove-aliases-unique p e m (outer , inners) with lookup p m in found
... | nothing = outer , inners
... | just inner with filterᵇ (λ pair → A.differentEntry (proj₂ pair) e) inner in filtered
...   | [] = delete-unique p m outer , delete-values UniqueKeys p m inners
...   | x ∷ xs = put-unique p (x ∷ xs) m outer ,
  put-values UniqueKeys p (x ∷ xs) m
    (subst UniqueKeys filtered (filter-unique _ inner (lookup-all UniqueKeys p m inners found))) inners
