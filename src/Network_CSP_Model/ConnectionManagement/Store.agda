{-# OPTIONS --guardedness #-}

-- Small association stores for the first finite-state slice. No iteration-order
-- claims: source ordered/random remote selection is not implemented here.
module ConnectionManagement.Store where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (DecEq; _≟_)

Store : Set → Set → Set
Store K V = List (K × V)

-- Reads and replacement preserve the uniqueness of stores built with put.
lookup : ∀ {K V} ⦃ _ : DecEq K ⦄ → K → Store K V → Maybe V
lookup k [] = nothing
lookup k ((k′ , v) ∷ xs) with k ≟ k′
... | yes _ = just v
... | no _ = lookup k xs

put : ∀ {K V} ⦃ _ : DecEq K ⦄ → K → V → Store K V → Store K V
put k v [] = (k , v) ∷ []
put k v ((k′ , old) ∷ xs) with k ≟ k′
... | yes _ = (k , v) ∷ xs
... | no _ = (k′ , old) ∷ put k v xs

-- Delete an exact key; unique-key stores are the representation invariant.
delete : ∀ {K V} ⦃ _ : DecEq K ⦄ → K → Store K V → Store K V
delete k [] = []
delete k ((k′ , v) ∷ xs) with k ≟ k′
... | yes _ = xs
... | no _ = (k′ , v) ∷ delete k xs
