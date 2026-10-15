{-# OPTIONS --guardedness #-}

-- Certificates check every state, including both endpoints, of an existing
-- execution. They do not change the process or assert an inductive invariant.
module ConnectionManagement.CSP.CheckedExecution where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (_∷_)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Machine

checkAlong : (Configuration → Bool) → ∀ {c as c′} → Executes c as c′ → Bool
checkAlong p {c} done = p c
checkAlong p {c} (next eq rest) = p c ∧ checkAlong p rest

Along : (Configuration → Bool) → ∀ {c as c′} → Executes c as c′ → Set
Along p {c} done = p c ≡ true
Along p {c} (next eq rest) = (p c ≡ true) × Along p rest

-- A successful executable check yields per-state evidence, not just a check
-- of the final state. No additional premises on advance are introduced.
checked : ∀ p {c as c′} (run : Executes c as c′) → checkAlong p run ≡ true → Along p run
checked p done ok = ok
checked p {c} (next eq rest) ok with p c in found
... | false = ⊥-elim (caseFalse ok)
  where
  caseFalse : false ≡ true → ⊥
  caseFalse ()
... | true = refl , checked p rest ok

-- Remove an explicit attachment prefix while preserving its actual successor.
successor : ∀ {c c′ a as} → Executes c (a ∷ as) c′ → Configuration
successor (next {c₁ = c₁} eq rest) = c₁
tailRun : ∀ {c c′ a as} (run : Executes c (a ∷ as) c′) → Executes (successor run) as c′
tailRun (next eq rest) = rest
