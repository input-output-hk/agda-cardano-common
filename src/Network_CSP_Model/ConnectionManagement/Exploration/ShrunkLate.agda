{-# OPTIONS --guardedness #-}

-- Literal exports and initialized importer/violation certificates.
module ConnectionManagement.Exploration.ShrunkLate where
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; _≤_; _≤?_; suc)
open import Data.String using (toList)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import ConnectionManagement.Exploration.MinimiseCandidates as C
module M = C.LateCase.M

original shrunk : List ℕ
original = 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ 11 ∷ 12 ∷ 13 ∷ 14 ∷ 15 ∷ 16 ∷ 17 ∷ 18 ∷ 19 ∷ 20 ∷ 21 ∷ 22 ∷ 23 ∷ 24 ∷ 25 ∷ 26 ∷ 27 ∷ 28 ∷ 29 ∷ 30 ∷ 31 ∷ 32 ∷ 33 ∷ 34 ∷ 35 ∷ 36 ∷ 37 ∷ 38 ∷ 39 ∷ 40 ∷ 41 ∷ 42 ∷ 43 ∷ 44 ∷ 45 ∷ 46 ∷ 47 ∷ 48 ∷ 49 ∷ []
shrunk = 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 9 ∷ 10 ∷ 11 ∷ 12 ∷ 13 ∷ 14 ∷ 15 ∷ 16 ∷ 17 ∷ 18 ∷ 19 ∷ 23 ∷ 24 ∷ 25 ∷ 26 ∷ 27 ∷ 28 ∷ 29 ∷ 30 ∷ 31 ∷ 32 ∷ 33 ∷ 34 ∷ 35 ∷ 36 ∷ 37 ∷ 38 ∷ 39 ∷ 40 ∷ 41 ∷ 42 ∷ 43 ∷ 44 ∷ 45 ∷ 46 ∷ 47 ∷ 48 ∷ 49 ∷ []

original-export : M.wire original ≡ toList ".\n+.\n++.\n+++.\n++++.\n+++++.\n++++++.\n+++++++.\n++++++++.\n+++++++++.\n:.\n:+.\n:++.\n:+++.\n:++++.\n:+++++.\n:++++++.\n:+++++++.\n:++++++++.\n:+++++++++.\n::.\n::+.\n::++.\n::+++.\n::++++.\n::+++++.\n::++++++.\n::+++++++.\n::++++++++.\n::+++++++++.\n:::.\n:::+.\n:::++.\n:::+++.\n:::++++.\n:::+++++.\n:::++++++.\n:::+++++++.\n:::++++++++.\n:::+++++++++.\n::::.\n::::+.\n::::++.\n::::+++.\n::::++++.\n::::+++++.\n::::++++++.\n::::+++++++.\n::::++++++++.\n::::+++++++++.\n"
original-export = refl
shrunk-export : M.wire shrunk ≡ toList ".\n+.\n++.\n+++.\n++++.\n+++++.\n++++++.\n+++++++.\n+++++++++.\n:.\n:+.\n:++.\n:+++.\n:++++.\n:+++++.\n:++++++.\n:+++++++.\n:++++++++.\n:+++++++++.\n::+++.\n::++++.\n::+++++.\n::++++++.\n::+++++++.\n::++++++++.\n::+++++++++.\n:::.\n:::+.\n:::++.\n:::+++.\n:::++++.\n:::+++++.\n:::++++++.\n:::+++++++.\n:::++++++++.\n:::+++++++++.\n::::.\n::::+.\n::::++.\n::::+++.\n::::++++.\n::::+++++.\n::::++++++.\n::::+++++++.\n::::++++++++.\n::::+++++++++.\n"
shrunk-export = refl

-- Each refl executes the stage-2 parser and actual dispatcher, from the same
-- initializer, and tests the identical endpoint predicate. No state is supplied.
original-valid : M.valid original ≡ true
original-valid = refl
shrunk-valid : M.valid shrunk ≡ true
shrunk-valid = refl
original-accepted : M.Accepted original
original-accepted = M.valid-sound original original-valid
shrunk-accepted : M.Accepted shrunk
shrunk-accepted = M.valid-sound shrunk shrunk-valid
strictly-shorter : suc (length shrunk) ≤ length original
strictly-shorter = toWitness {a? = suc (length shrunk) ≤? length original} tt
