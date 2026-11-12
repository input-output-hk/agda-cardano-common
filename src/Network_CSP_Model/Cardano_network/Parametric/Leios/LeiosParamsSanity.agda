{-# OPTIONS --guardedness #-}

-- Computation gates and losslessness for transaction-offset chunking.
open import Cardano_network.Params using (Params)

module Cardano_network.Parametric.Leios.LeiosParamsSanity (p : Params) where

open import Level using (Level)
open import Data.Nat using (ℕ; _≤_)
open import Data.List using (List; []; _∷_; concat)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.Parametric.Leios.LeiosParams p

-- An exact multiple of the chunk size produces no trailing empty chunk.
chunks-exact : chunksOf 2 (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ≡
  (0 ∷ 1 ∷ []) ∷ (2 ∷ 3 ∷ []) ∷ []
chunks-exact = refl

-- A final incomplete chunk retains the remaining offsets.
chunks-remainder : chunksOf 2 (0 ∷ 1 ∷ 2 ∷ []) ≡
  (0 ∷ 1 ∷ []) ∷ (2 ∷ []) ∷ []
chunks-remainder = refl

-- An empty EB needs no transaction request.
chunks-empty : chunksOf 2 ([] {A = ℕ}) ≡ []
chunks-empty = refl

-- The model instances' chunk size gives singleton requests in order.
chunks-singletons : chunksOf 1 (5 ∷ 6 ∷ []) ≡
  (5 ∷ []) ∷ (6 ∷ []) ∷ []
chunks-singletons = refl

-- Every positive chunk size preserves all entries and their order.
chunks-roundtrip : ∀ {ℓ : Level} {A : Set ℓ} {c : ℕ} {xs : List A} →
  1 ≤ c → concat (chunksOf c xs) ≡ xs
chunks-roundtrip = chunksOf-concat
