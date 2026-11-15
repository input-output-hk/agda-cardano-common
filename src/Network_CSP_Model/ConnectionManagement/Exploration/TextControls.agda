{-# OPTIONS --guardedness #-}

-- Syntax, dictionary aliases, dispatcher refusal and disabled-suffix controls.
module ConnectionManagement.Exploration.TextControls where
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (toList)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import ConnectionManagement.Exploration.Text as Text

advance : ℕ → ℕ → Maybe ℕ
advance zero s = just (suc s)
advance (suc _) s = nothing
module C = Text ℕ ℕ advance (0 ∷ 1 ∷ 0 ∷ [])

malformed : C.parse 2 (toList ".\n?\n") ≡ nothing
malformed = refl
truncated : C.parse 1 (toList ".") ≡ nothing
truncated = refl
out-of-dictionary : C.parse 1 (toList "+++.\n") ≡ nothing
out-of-dictionary = refl
empty-line : C.parse 1 (toList "\n") ≡ nothing
empty-line = refl
no-fuel : C.parse 0 (toList ".\n") ≡ nothing
no-fuel = refl
alias : C.parse 1 (toList "++.\n") ≡ just (0 ∷ [])
alias = refl
accepted : C.check 0 1 (toList ".\n") ≡ just ((0 ∷ []) , 1)
accepted = refl
disabled-label : C.check 0 1 (toList "+.\n") ≡ nothing
disabled-label = refl
disabled-suffix : C.check 0 2 (toList ".\n+.\n") ≡ nothing
disabled-suffix = refl
