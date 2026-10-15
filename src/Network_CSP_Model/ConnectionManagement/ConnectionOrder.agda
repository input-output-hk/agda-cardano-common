{-# OPTIONS --guardedness #-}

-- ConnectionId.hs orders remote address BEFORE local address. The address
-- order remains the model's explicit family/host/port abstraction.
module ConnectionManagement.ConnectionOrder where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _<?_)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Nullary using (yes; no)
open import ConnectionManagement.Domain

lexLess : List ℕ → List ℕ → Bool
lexLess [] _ = false
lexLess (_ ∷ _) [] = false
lexLess (x ∷ xs) (y ∷ ys) with x <? y | y <? x
... | yes _ | _ = true
... | no _ | yes _ = false
... | no _ | no _ = lexLess xs ys
addressCode : PeerAddr → List ℕ
addressCode (addr ipv4 h p) = 0 ∷ h ∷ p ∷ []
addressCode (addr ipv6 h p) = 1 ∷ h ∷ p ∷ []
keyLess : ConnectionKey → ConnectionKey → Bool
keyLess x y = lexLess (addressCode (remote x) ++ addressCode (local x))
                     (addressCode (remote y) ++ addressCode (local y))
