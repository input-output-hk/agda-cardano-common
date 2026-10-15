{-# OPTIONS --guardedness #-}

-- Supply bounds hold along every finite model execution from the accepted-socket
-- start, including the existing race and exception-path witnesses.
module ConnectionManagement.Scenarios.SupplyInvariant where

open import Data.List using ([])
open import Data.List.Relation.Unary.All using ([])
open import Data.Bool using (false)
open import Data.Bool.ListAction using (any)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (does; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.State
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.Freshness using (supply-absent)
open import ConnectionManagement.Properties.SupplyBounds
open import ConnectionManagement.Properties.SupplyInvariant
open import ConnectionManagement.CSP.SupplyInvariant
open import ConnectionManagement.CSP.Fixtures using (start)
open import ConnectionManagement.CSP.Scenarios using
  (raceEnd; race-path; cleanupFirstEnd; cleanup-first-path; lockEnd; lock-trace-path;
   duplicateEnd; duplicate-path)
open import ConnectionManagement.Scenarios.Admission using (fixture)
open import ConnectionManagement.Negative.Freshness using (futureEntry; future-not-bounded)

initial-bounded : SupplyBounds (world start)
initial-bounded = [] , []

from-start : ∀ {actions c′} → Executes start actions c′ → SupplyBounds (world c′)
from-start = exec-preserves {c = start} initial-bounded

race-bounded : SupplyBounds (world raceEnd)
race-bounded = from-start race-path

cleanup-first-bounded : SupplyBounds (world cleanupFirstEnd)
cleanup-first-bounded = from-start cleanup-first-path

lock-bounded : SupplyBounds (world lockEnd)
lock-bounded = from-start lock-trace-path

duplicate-bounded : SupplyBounds (world duplicateEnd)
duplicate-bounded = from-start duplicate-path

-- In any reachable state the next allocation identities have not been allocated.
next-entry-unused : ∀ {actions c′} → Executes start actions c′ →
  lookup (ident (nextEntry (cm (world c′)))) (entries (cm (world c′))) ≡ nothing
next-entry-unused {c′ = c′} path = supply-absent (nextEntry (cm (world c′)))
  (entries (cm (world c′))) (proj₁ (from-start path))

next-promise-unused : ∀ {actions c′} → Executes start actions c′ →
  any (λ p → does (p ≟ ident (nextPromise (world c′)))) (promises (world c′)) ≡ false
next-promise-unused {c′ = c′} path = promise-next-absent (nextPromise (world c′))
  (promises (world c′)) (proj₂ (from-start path))

-- The earlier one-allocation-then-collision fixture cannot arise from this start.
future-entry-unreachable : ∀ mode actions → ¬ Executes start actions (initial mode (fixture futureEntry))
future-entry-unreachable mode actions path = future-not-bounded (proj₁ (from-start path))
