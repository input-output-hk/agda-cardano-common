{-# OPTIONS --safe #-}

-- Natural-number selectors let a fixed tree channel index a state-dependent menu.
module Cardano_network.LeiosNotifyPipeLookahead.Selection where

open import Level using (Level)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map; length; lookup)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Product using (Σ-syntax; _,_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

-- Out-of-range selectors enable no branch and cannot fabricate a successor.
select : ∀ {ℓ} {A : Set ℓ} → List A → ℕ → Maybe A
select [] n = nothing
select (x ∷ xs) zero = just x
select (x ∷ xs) (suc n) = select xs n

-- Every erased menu target has a concrete selector, without proof-identity assumptions.
select-complete : ∀ {ℓa ℓb} {A : Set ℓa} {B : Set ℓb} {f : A → B} {b xs} →
  b ∈ map f xs → Σ[ n ∈ ℕ ] Maybe.map f (select xs n) ≡ just b
select-complete {xs = []} ()
select-complete {xs = x ∷ xs} (here refl) = zero , refl
select-complete {f = f} {xs = x ∷ xs} (there mem) with select-complete {f = f} {xs = xs} mem
... | n , eq = suc n , eq

-- A menu target also has a bounded index suitable for native ExtI.fin branches.
index-complete : ∀ {ℓa ℓb} {A : Set ℓa} {B : Set ℓb} {f : A → B} {b xs} →
  b ∈ map f xs → Σ[ i ∈ Fin (length xs) ] f (lookup xs i) ≡ b
index-complete {xs = []} ()
index-complete {xs = x ∷ xs} (here eq) = fzero , sym eq
index-complete {f = f} {xs = x ∷ xs} (there mem) with index-complete {f = f} {xs = xs} mem
... | i , eq = fsuc i , eq
