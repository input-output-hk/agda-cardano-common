{-# OPTIONS --guardedness #-}

-- Small computed controls exercise the reducer without normalizing a model.
module ConnectionManagement.Exploration.MinimiseControls where
open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import ConnectionManagement.Exploration.Minimise as Minimise

advance : Bool → Bool → Maybe Bool
advance false s = just s
advance true false = just true
advance true true = nothing
module M = Minimise Bool Bool advance (true ∷ false ∷ []) false (λ s → s)

-- False actions are irrelevant; the one state-changing action must remain.
shrinks : M.reduce 3 (1 ∷ 0 ∷ 1 ∷ []) ≡ (0 ∷ [])
shrinks = refl
preserved : M.Accepted (M.reduce 3 (1 ∷ 0 ∷ 1 ∷ []))
preserved = M.reduction-sound 3 (1 ∷ 0 ∷ 1 ∷ []) refl
coarse-preserved : M.Accepted (M.coarse 3 2 (1 ∷ 0 ∷ 1 ∷ []))
coarse-preserved = M.coarse-sound 3 2 (1 ∷ 0 ∷ 1 ∷ []) refl
missing-violation : M.valid (1 ∷ []) ≡ false
missing-violation = refl
disabled-suffix : M.valid (0 ∷ 0 ∷ []) ≡ false
disabled-suffix = refl
out-of-dictionary : M.valid (2 ∷ []) ≡ false
out-of-dictionary = refl
