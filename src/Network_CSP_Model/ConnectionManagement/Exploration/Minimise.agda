{-# OPTIONS --guardedness #-}

-- Greedy event deletion over dictionary offsets. Every proposed deletion is
-- re-imported from the SAME initializer; no endpoint or actor state is forged.
open import Data.Maybe using (Maybe)
open import Data.List using (List)
open import Data.Bool using (Bool)
module ConnectionManagement.Exploration.Minimise
  (State Action : Set) (advance : Action → State → Maybe State)
  (dictionary : List Action) (initial : State) (violation : State → Bool) where

open import Data.Bool using (true; false)
open import Data.Char using (Char)
open import Data.List using ([]; _∷_; _++_; map; concat; length; take; drop)
open import Data.Nat using (ℕ; zero; suc; ⌊_/2⌋)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import ConnectionManagement.Exploration.Text as Text
module Codec = Text State Action advance dictionary

-- A canonical token uses unary offsets; the existing parser also accepts ':'.
token : ℕ → List Char
token zero = '.' ∷ '\n' ∷ []
token (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n)))))))))) = ':' ∷ token n
token (suc n) = '+' ∷ token n
wire : List ℕ → List Char
wire ns = concat (map token ns)

valid : List ℕ → Bool
valid ns with Codec.check initial (length ns) (wire ns)
... | nothing = false
... | just (_ , t) = violation t

-- This is the monitored property, including exact parser/dispatcher acceptance.
Accepted : List ℕ → Set
Accepted ns = Σ (List Action) λ as → Σ State λ t →
  Codec.check initial (length ns) (wire ns) ≡ just (as , t) ×
  (Codec.Raw.Executes initial as t × violation t ≡ true)

valid-sound : ∀ ns → valid ns ≡ true → Accepted ns
valid-sound ns eq with Codec.check initial (length ns) (wire ns) in checked
... | nothing with eq
... | ()
valid-sound ns eq | just (as , t) = as , t , refl , Codec.check-sound initial (length ns) (wire ns) checked , eq

-- All single-event deletions, in left-to-right order. Repetition of this pass
-- can remove every event belonging to an irrelevant actor, without renaming IDs.
deletions : List ℕ → List (List ℕ)
deletions [] = []
deletions (n ∷ ns) = ns ∷ map (n ∷_) (deletions ns)

pick : List (List ℕ) → List ℕ → List ℕ
pick [] old = old
pick (ns ∷ rest) old with valid ns
... | true = ns
... | false = pick rest old

pick-preserves : ∀ choices old → valid old ≡ true → valid (pick choices old) ≡ true
pick-preserves [] old ok = ok
pick-preserves (ns ∷ rest) old ok with valid ns in checked
... | true = checked
... | false = pick-preserves rest old ok

-- Fuel bounds accepted deletions. length(input) suffices for a complete greedy
-- descent; no claim of globally shortest traces follows from greedy deletion.
reduce : ℕ → List ℕ → List ℕ
reduce zero ns = ns
reduce (suc fuel) ns = reduce fuel (pick (deletions ns) ns)

preserves : ∀ fuel ns → valid ns ≡ true → valid (reduce fuel ns) ≡ true
preserves zero ns ok = ok
preserves (suc fuel) ns ok = preserves fuel (pick (deletions ns) ns)
  (pick-preserves (deletions ns) ns ok)

-- Proved preservation of initialization, real execution and the SAME violation.
reduction-sound : ∀ fuel ns → valid ns ≡ true → Accepted (reduce fuel ns)
reduction-sound fuel ns ok = valid-sound (reduce fuel ns) (preserves fuel ns ok)

-- Chunk deletion removes irrelevant actor histories without testing every
-- individual PC first. The last short chunk is also offered; offsets and IDs
-- are retained verbatim. Width zero supplies no proposals.
chunks : ℕ → List ℕ → List (List ℕ)
chunks zero ns = []
chunks (suc width) ns = go (length ns) [] ns
  where
  go : ℕ → List ℕ → List ℕ → List (List ℕ)
  go zero pre rest = []
  go (suc fuel) pre [] = []
  go (suc fuel) pre rest@(_ ∷ _) =
    (pre ++ drop (suc width) rest) ∷
      go fuel (pre ++ take (suc width) rest) (drop (suc width) rest)

-- A bounded coarse-to-fine QuickCheck pass. Each width is tried once; the
-- final single-event pass is available separately. No global minimum claim.
coarse : ℕ → ℕ → List ℕ → List ℕ
coarse zero width ns = ns
coarse (suc fuel) width ns = coarse fuel ⌊ width /2⌋ (pick (chunks width ns) ns)

coarse-preserves : ∀ fuel width ns → valid ns ≡ true → valid (coarse fuel width ns) ≡ true
coarse-preserves zero width ns ok = ok
coarse-preserves (suc fuel) width ns ok = coarse-preserves fuel ⌊ width /2⌋
  (pick (chunks width ns) ns) (pick-preserves (chunks width ns) ns ok)

coarse-sound : ∀ fuel width ns → valid ns ≡ true → Accepted (coarse fuel width ns)
coarse-sound fuel width ns ok = valid-sound (coarse fuel width ns)
  (coarse-preserves fuel width ns ok)
