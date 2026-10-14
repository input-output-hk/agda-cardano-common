{-# OPTIONS --guardedness #-}

-- Reference validity, not a full machine invariant: unique keys, fresh supplies,
-- lease/worker consistency and socket ownership remain separate obligations.
module ConnectionManagement.Properties.Entries where

open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Class.DecEq using (DecEq; _≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (Store; lookup; put)
open import ConnectionManagement.State

-- Overwriting an entry never invalidates a reference to an existing entry.
lookup-put : ∀ {K V} ⦃ _ : DecEq K ⦄ (k : K) (v : V) xs →
  lookup k (put k v xs) ≡ just v
lookup-put k v [] with k ≟ k
... | yes _ = refl
... | no neq = ⊥-elim (neq refl)
lookup-put k v ((q , old) ∷ xs) with k ≟ q in test
... | yes _ with k ≟ k
...   | yes _ = refl
...   | no neq = ⊥-elim (neq refl)
lookup-put k v ((q , old) ∷ xs) | no _ rewrite test = lookup-put k v xs

Present : ∀ {K V} ⦃ _ : DecEq K ⦄ → K → Store K V → Set
Present {V = V} k xs = Σ V (λ v → lookup k xs ≡ just v)

put-preserves-present : ∀ {K V} ⦃ _ : DecEq K ⦄ (k q : K) (v : V) xs →
  Present q xs → Present q (put k v xs)
put-preserves-present k q v [] (_ , ())
put-preserves-present k q v ((r , old) ∷ xs) present with k ≟ r
... | yes eq with q ≟ k | q ≟ r
...   | yes _ | _ = v , refl
...   | no neq | yes eq′ = ⊥-elim (neq (trans eq′ (sym eq)))
...   | no _ | no _ = present
put-preserves-present k q v ((r , old) ∷ xs) present | no _ with q ≟ r
... | yes _ = old , refl
... | no _ = put-preserves-present k q v xs present

-- Quantify over both levels, including unknown-local reservations. Retained old
-- heap entries are allowed: map reachability is not heap ownership or GC.
MapReferences : EntryHeap → ConnMap → Set
MapReferences heap m = ∀ remote inner local e →
  lookup remote m ≡ just inner → lookup local inner ≡ just e → Present e heap

heap-update-preserves-map-references : ∀ e st heap m →
  MapReferences heap m → MapReferences (put e st heap) m
heap-update-preserves-map-references e st heap m valid remote inner local ref outer innerEq =
  put-preserves-present e ref st heap (valid remote inner local ref outer innerEq)

-- Applies to saved maps while the global TMVar is taken as well as full maps.
-- The lemma does not assume that the updated entry remains mapped.
empty-map-references : ∀ heap → MapReferences heap []
empty-map-references heap remote inner local e ()
