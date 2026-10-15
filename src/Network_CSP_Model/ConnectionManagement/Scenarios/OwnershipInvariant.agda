{-# OPTIONS --guardedness #-}

-- Reachability consequences of the full invariant, using existing checked paths
-- instead of normalizing the combined machine over an entire trace.
module ConnectionManagement.Scenarios.OwnershipInvariant where

open import Data.List using (List)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (refl)
open import ConnectionManagement.State using (ResponderMode)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.Ownership
open import ConnectionManagement.Properties.OwnershipInvariant
open import ConnectionManagement.CSP.OwnershipInvariant
open import ConnectionManagement.CSP.Fixtures using (start)
open import ConnectionManagement.CSP.Scenarios using
  (raceEnd; race-path; cleanupFirstEnd; cleanup-first-path; lockEnd; lock-trace-path;
   duplicateEnd; duplicate-path)
open import ConnectionManagement.Negative.Ownership using
  (orphan; orphan-invalid; fullWithLease; full-with-lease-invalid;
   doubleClaim; double-claim-invalid; wrongOwner; wrong-owner-invalid)

-- Universal over endpoints and finite action sequences, not just the examples.
from-start : ∀ {actions c′} → Executes start actions c′ → Ownership (world c′)
from-start = exec-preserves {c = start} refl

race-owned : Ownership (world raceEnd)
race-owned = from-start race-path

cleanup-first-owned : Ownership (world cleanupFirstEnd)
cleanup-first-owned = from-start cleanup-first-path

lock-owned : Ownership (world lockEnd)
lock-owned = from-start lock-trace-path

duplicate-owned : Ownership (world duplicateEnd)
duplicate-owned = from-start duplicate-path

-- Negative fixtures are unreachable in this machine from the accepted-socket
-- start state, for every finite action sequence and either responder mode.
orphan-unreachable : ∀ mode actions → ¬ Executes start actions (initial mode orphan)
orphan-unreachable mode actions path = orphan-invalid (from-start path)

full-lease-unreachable : ∀ mode actions → ¬ Executes start actions (initial mode fullWithLease)
full-lease-unreachable mode actions path = full-with-lease-invalid (from-start path)

duplicate-claim-unreachable : ∀ mode actions → ¬ Executes start actions (initial mode doubleClaim)
duplicate-claim-unreachable mode actions path = double-claim-invalid (from-start path)

wrong-owner-unreachable : ∀ mode actions → ¬ Executes start actions (initial mode wrongOwner)
wrong-owner-unreachable mode actions path = wrong-owner-invalid (from-start path)
