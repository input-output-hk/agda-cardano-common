{-# OPTIONS --guardedness #-}

-- Policies.hs:126-142,179-221: rank, take requested count, Set.fromList.
-- For unique inputs, address sorting renders that set's ascending enumeration.
-- Comparator quantification includes every RNG/metric/tepid/failure ranking;
-- it does not implement their random-state updates or transaction history.
module ConnectionManagement.SourceInputs.Ranking where
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; take)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain using (PeerAddr; remote)
open import ConnectionManagement.ConnectionOrder using (lexLess; addressCode)
open import ConnectionManagement.Rules.Pruning using (sortBy)
import ConnectionManagement.Scenarios.Admission as A

pick : (PeerAddr → PeerAddr → Bool) → ℕ → List PeerAddr → List PeerAddr
pick less count available = sortBy (λ p q → lexLess (addressCode p) (addressCode q))
  (take count (sortBy less available))

firstPeers : List PeerAddr
firstPeers = remote A.key₀ ∷ remote A.key₁ ∷ []

-- Every comparison, including ties, leads to the same selected set.
all-two : ∀ less → pick less 2 firstPeers ≡ firstPeers
all-two less with less (remote A.key₁) (remote A.key₀)
... | false = refl
... | true = refl
singleton : ∀ less p → pick less 1 (p ∷ []) ≡ p ∷ []
singleton less p = refl
