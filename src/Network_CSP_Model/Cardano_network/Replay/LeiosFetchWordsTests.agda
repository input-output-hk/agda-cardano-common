{-# OPTIONS --safe #-}

module Cardano_network.Replay.LeiosFetchWordsTests where

open import Cardano_network.Replay.LeiosFetchWire using (popcount; validᵇ; offsets)
open import Cardano_network.Replay.LeiosFetchWords
open import Data.Bool using (true; false)
open import Data.Unit using (tt)
open import Data.List using ([]; _∷_; upTo)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Offset zero occupies the most significant bit of word zero.
offset-zero : toWords (0 ∷ []) ≡ (0 , 9223372036854775808) ∷ []
offset-zero = refl

-- Offset 63 occupies the least significant bit of word zero.
offset-63 : toWords (63 ∷ []) ≡ (0 , 1) ∷ []
offset-63 = refl

-- Offset 64 starts the next wire word.
offset-64 : toWords (64 ∷ []) ≡ (1 , 9223372036854775808) ∷ []
offset-64 = refl

-- Offset 127 occupies the least significant bit of word one.
offset-127 : toWords (127 ∷ []) ≡ (1 , 1) ∷ []
offset-127 = refl

-- Offset 128 starts word two at its most significant bit.
offset-128 : toWords (128 ∷ []) ≡ (2 , 9223372036854775808) ∷ []
offset-128 = refl

-- The final honest transaction offset occupies bit ten of word 267.
offset-17141 : toWords (17141 ∷ []) ≡ (267 , 1024) ∷ []
offset-17141 = refl

-- The decoder accepts the final bit of word one.
valid-127 : validᵇ (toWords (127 ∷ [])) ≡ true
valid-127 = refl

-- The decoder accepts the first bit of word two.
valid-128 : validᵇ (toWords (128 ∷ [])) ≡ true
valid-128 = refl

-- The decoder accepts the final honest transaction offset.
valid-17141 : validᵇ (toWords (17141 ∷ [])) ≡ true
valid-17141 = refl

-- Adjacent offsets across a word boundary require two entries.
boundary-63-64 : toWords (63 ∷ 64 ∷ []) ≡
  (0 , 1) ∷ (1 , 9223372036854775808) ∷ []
boundary-63-64 = refl

-- Empty model requests encode as empty wire requests.
empty-words : toWords [] ≡ []
empty-words = refl

-- The last transaction offset is permitted.
last-canonical : canonical (17141 ∷ []) ≡ true
last-canonical = refl

-- The exclusive transaction cap is rejected.
cap-not-canonical : canonical (17142 ∷ []) ≡ false
cap-not-canonical = refl

-- Duplicate offsets are rejected.
duplicate-not-canonical : canonical (3 ∷ 3 ∷ []) ≡ false
duplicate-not-canonical = refl

-- Descending offsets are rejected.
descending-not-canonical : canonical (5 ∷ 3 ∷ []) ≡ false
descending-not-canonical = refl

-- A request spanning three words preserves its transaction count.
count-130 : popcount (toWords (upTo 130)) ≡ 130
count-130 = refl

-- A request spanning three words satisfies the wire decoder.
valid-130 : validᵇ (toWords (upTo 130)) ≡ true
valid-130 = refl

-- The final bit in the decoder's final Word64 is accepted.
last-decodable : decodable (17151 ∷ []) ≡ true
last-decodable = refl

-- The first offset beyond all decoder words is rejected.
cap-not-decodable : decodable (17152 ∷ []) ≡ false
cap-not-decodable = refl


-- Empty wire words decode to no offsets.
decodes-empty : offsets [] ≡ []
decodes-empty = refl

-- The low bit in word zero is the last position in that word.
decodes-63 : offsets ((0 , 1) ∷ []) ≡ (63 ∷ [])
decodes-63 = refl

-- The final decoder position is the low bit of the final word.
decodes-17151 : offsets ((267 , 1) ∷ []) ≡ (17151 ∷ [])
decodes-17151 = refl

-- The most significant bit of word zero decodes to offset zero.
decodes-zero : Decodes ((0 , 9223372036854775808) ∷ []) (0 ∷ [])
decodes-zero = tt , refl

-- The most significant bit of word one decodes to offset 64.
decodes-64 : Decodes ((1 , 9223372036854775808) ∷ []) (64 ∷ [])
decodes-64 = tt , refl

-- The low bit of word zero is valid and decodes to offset 63.
decodes-63-valid : Decodes ((0 , 1) ∷ []) (63 ∷ [])
decodes-63-valid = tt , refl

-- The final decoder padding bit is valid and decodes exactly.
decodes-17151-valid : Decodes ((267 , 1) ∷ []) (17151 ∷ [])
decodes-17151-valid = tt , refl

-- The empty bitmap is valid and decodes to the empty model list.
decodes-empty-valid : Decodes [] []
decodes-empty-valid = tt , refl
