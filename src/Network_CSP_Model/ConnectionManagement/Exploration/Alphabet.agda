{-# OPTIONS --guardedness #-}

-- Finite typed event alphabets are decoded by the existing raw bridge, including
-- its rejection of tick. No parser, scheduler, or enabledness heuristic is added.
open import Data.Maybe using (Maybe)
module ConnectionManagement.Exploration.Alphabet
  (State Action : Set) (advance : Action → State → Maybe State) where

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Unit using (⊤)
open import Process_Trees using (ExtI)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import ConnectionManagement.CSP.Dispatcher as Dispatcher
module Raw = Dispatcher State Action advance
open import Semantics.LTS {E = Raw.Channel} {I = ExtI Raw.Channel} using (Event√)

decodeAlphabet : List (Event√ ⊤) → List Action
decodeAlphabet [] = []
decodeAlphabet (e ∷ es) with Raw.decode e
... | nothing = decodeAlphabet es
... | just a = a ∷ decodeAlphabet es
encoded-alphabet : ∀ as → decodeAlphabet (map Raw.label as) ≡ as
encoded-alphabet [] = refl
encoded-alphabet (a ∷ as) = cong (a ∷_) (encoded-alphabet as)
