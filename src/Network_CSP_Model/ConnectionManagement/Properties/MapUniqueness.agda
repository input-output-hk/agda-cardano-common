{-# OPTIONS --guardedness #-}

-- The two nested map levels both require unique keys to justify using lookup
-- coverage as traversal coverage. Entry aliases across distinct keys are allowed.
module ConnectionManagement.Properties.MapUniqueness where

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (refl; subst)
open import ConnectionManagement.Store using (lookup; put; delete)
open import Data.Product using (_×_; _,_; proj₂)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Properties.Stores
open import ConnectionManagement.Properties.Entries using (MapReferences; Present)
open import ConnectionManagement.Properties.Counters using
  (CounterReferences; InnerReferences; lookup-all; count-total)

MapUnique : ConnMap → Set
MapUnique m = UniqueKeys m × All (λ binding → UniqueKeys (proj₂ binding)) m

-- This supplies the missing uniqueness premise for the older lookup predicate.
lookup-to-counter-references : ∀ heap m → MapUnique m → MapReferences heap m →
  CounterReferences heap m
lookup-to-counter-references heap m (outerUnique , innerUnique) valid =
  lookup-properties (InnerReferences heap) m outerUnique
    (λ remote inner outer → lookup-properties (λ e → Present e heap) inner
      (lookup-all UniqueKeys remote m innerUnique outer)
      (λ local e innerEq → valid remote inner local e outer innerEq))

-- Actual nested-map operations preserve both levels of uniqueness.
insert-unique : ∀ remote local e m → MapUnique m → MapUnique (insertLocal remote local e m)
insert-unique remote local e m (outer , inners) with lookup remote m in found
... | nothing = put-unique remote ((local , e) ∷ []) m outer ,
  put-values UniqueKeys remote ((local , e) ∷ []) m ([] ∷ []) inners
... | just inner = put-unique remote (put local e inner) m outer ,
  put-values UniqueKeys remote (put local e inner) m
    (put-unique local e inner (lookup-all UniqueKeys remote m inners found)) inners

delete-connection-unique : ∀ key m → MapUnique m → MapUnique (deleteConnection key m)
delete-connection-unique key m (outer , inners) with lookup (remote key) m in found
... | nothing = outer , inners
... | just inner with delete (knownLocal (local key)) inner in deleted
...   | [] = delete-unique (remote key) m outer , delete-values UniqueKeys (remote key) m inners
...   | x ∷ xs = put-unique (remote key) (x ∷ xs) m outer ,
  put-values UniqueKeys (remote key) (x ∷ xs) m
    (subst UniqueKeys deleted
      (delete-unique (knownLocal (local key)) inner (lookup-all UniqueKeys (remote key) m inners found))) inners
