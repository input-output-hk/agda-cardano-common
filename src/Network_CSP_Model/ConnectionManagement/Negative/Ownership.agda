{-# OPTIONS --guardedness #-}

-- Positive snapshots and malformed-state controls for exact lease ownership.
-- These controls do not assert that the malformed states are source reachable.
module ConnectionManagement.Negative.Ownership where

open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.Ownership
open import ConnectionManagement.Properties.OwnershipSteps
open import ConnectionManagement.CSP.Fixtures
open import ConnectionManagement.CSP.Ownership
open import ConnectionManagement.Scenarios.Admission using (w₀; child₀)
import ConnectionManagement.Rules.Cleanup as Cleanup

initial-owned : Ownership (world start)
initial-owned = refl

waiting-owned : Ownership (world waiting)
waiting-owned = refl

beforeClose : Configuration
beforeClose = snapshot (terminated nothing) (taken child₀) (awaitHandshake promise₀ entry₀)
  (handling child₀) [] [] (cleanupStore (cleanupClose childLease [] countImmediately))

afterClose : Configuration
afterClose = snapshot (terminated nothing) (taken child₀) (awaitHandshake promise₀ entry₀)
  closed [] [] (cleanupStore (cleanupPublish childLease [] countImmediately))

afterFailure : Configuration
afterFailure = snapshot (terminated nothing) (taken child₀) (awaitHandshake promise₀ entry₀)
  (closeUncertain (errorId 0)) [] [] (cleanupStore (cleanupRestore childLease (errorId 0)))

before-owned : Ownership (world beforeClose)
before-owned = childLease , refl , refl

close-step : advance (cleanupStep child₀ Cleanup.closeHandlerSocket) beforeClose ≡ just afterClose
close-step = refl

failure-step : advance (cleanupStep child₀ (Cleanup.failSocketClose (errorId 0))) beforeClose ≡ just afterFailure
failure-step = refl

close-owned : Ownership (world afterClose)
close-owned = close-advance child₀ beforeClose close-step before-owned

failure-owned : Ownership (world afterFailure)
failure-owned = fail-advance child₀ (errorId 0) beforeClose failure-step before-owned

-- Taken map without a continuation holding its lease.
orphan : State
orphan = record (world waiting) { cm = cmStore (taken child₀) ((entry₀ , unneg) ∷ []) 1 }

orphan-invalid : ¬ Ownership orphan
orphan-invalid (l , () , ownerEq)

-- A lease cannot coexist with a full global map, even if its owner matches.
fullWithLease : State
fullWithLease = record (world beforeClose) { cm = cmStore (full binding) ((entry₀ , unneg) ∷ []) 1 }

full-with-lease-invalid : ¬ Ownership fullWithLease
full-with-lease-invalid ()

-- Two claims with the same worker still violate exclusive ownership.
doubleClaim : State
doubleClaim = record (world beforeClose)
  { cleanups = (child₀ , cleanupSelect childLease) ∷ (child₀ , cleanupSelect childLease) ∷ [] }

double-claim-invalid : ¬ Ownership doubleClaim
double-claim-invalid (l , () , ownerEq)

-- The continuation's worker and the captured lease owner must agree.
wrongOwner : State
wrongOwner = record (world beforeClose)
  { cleanups = cleanupStore (cleanupSelect (lease w₀ binding)) }

wrong-owner-invalid : ¬ Ownership wrongOwner
wrong-owner-invalid (. (lease w₀ binding) , refl , ())
