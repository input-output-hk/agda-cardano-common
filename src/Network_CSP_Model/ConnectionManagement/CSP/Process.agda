{-# OPTIONS --guardedness #-}

-- An open diagnostic CSP process, directly unfolded from Machine.advance.
-- All scheduling labels are visible here. There is no successful termination,
-- boundary self-loop, independent component semantics, or finite-state cutoff.
module ConnectionManagement.CSP.Process where

open import Data.Unit using (⊤)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open PTree
open import ConnectionManagement.Machine

data Channel : Set → Set where
  action : Channel Action

-- Operators compare channel indices, not action payloads.
channel-≟ : (x y : AnyTypes Channel) → Dec (x ≡ y)
channel-≟ (_ , action) (_ , action) = yes refl

Proc : Set₁
Proc = PTree Channel (ExtI Channel) ⊤

Process : Configuration → Proc
force (Process c) = react
  (λ where (_ , action) a → case advance a c of λ where
    nothing → nothing
    (just c′) → just (Process c′))
  (λ _ _ → nothing)

open import Semantics.LTS {E = Channel} {I = ExtI Channel}

label : Action → Event√ ⊤
label a = evl (evLabel Action action a)
