{-# OPTIONS --safe #-}

module Cardano_network.Replay.LeiosFetchWireTests where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.Replay.LeiosFetchWire

-- The most significant bit denotes offset zero.
_ : offsets ((0 , 9223372036854775808) ∷ []) ≡ 0 ∷ []
_ = refl

-- The least significant bit denotes offset 63.
_ : offsets ((0 , 1) ∷ []) ≡ 63 ∷ []
_ = refl

-- Word indices shift offsets by 64.
_ : offsets ((1 , 9223372036854775808) ∷ []) ≡ 64 ∷ []
_ = refl

-- Words and their set bits retain ascending wire order.
_ : offsets ((0 , 3) ∷ (2 , 9223372036854775808) ∷ []) ≡ 62 ∷ 63 ∷ 128 ∷ []
_ = refl

-- The recorded devnet word 5:0x3fffffffffffffff has 62 set bits.
_ : popcount ((5 , 4611686018427387903) ∷ []) ≡ 62
_ = refl

-- An empty bitmap is legal.
_ : validᵇ [] ≡ true
_ = refl

-- An empty bitmap requests no transactions.
_ : popcount [] ≡ 0
_ = refl

-- The last permitted word index is 267.
_ : validᵇ ((267 , 1) ∷ []) ≡ true
_ = refl

-- The first out-of-range word index is rejected.
_ : validᵇ ((268 , 1) ∷ []) ≡ false
_ = refl

-- All 64 bits may be set.
_ : validᵇ ((0 , 18446744073709551615) ∷ []) ≡ true
_ = refl

-- Words cannot exceed Word64.
_ : validᵇ ((0 , 18446744073709551616) ∷ []) ≡ false
_ = refl

-- A zero word is forbidden on the wire.
_ : validᵇ ((0 , 0) ∷ []) ≡ false
_ = refl

-- Duplicate indices are forbidden.
_ : validᵇ ((2 , 1) ∷ (2 , 1) ∷ []) ≡ false
_ = refl

-- Descending indices are forbidden.
_ : validᵇ ((3 , 1) ∷ (2 , 1) ∷ []) ≡ false
_ = refl
