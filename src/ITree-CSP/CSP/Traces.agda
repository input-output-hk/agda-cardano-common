{-# OPTIONS --guardedness #-}

open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
open import Data.Empty using (⊥)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; _×_)
open import Relation.Unary using (∅)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no)
-- open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; _++_; _∷_; []; length; reverse; map; foldr; downFrom)

open import Interaction_Trees
open import CSP.Basic_Processes
open import ITree_Relations.LTS

module CSP.Traces where
open ITree
open Traces

Stop-no-steps : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi}
    {s : List (EvLabel E)} {t′ : ITree E I (⊤ {ℓr})}
  → Stop ═⟨ s ⟩═► t′
  → s ≡ []


