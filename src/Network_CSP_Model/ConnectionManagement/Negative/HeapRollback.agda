{-# OPTIONS --guardedness #-}

-- Intentional bad operation: rolls the heap back with the map. This falsifies
-- a tempting implementation shortcut, not a property of the Haskell source.
module ConnectionManagement.Negative.HeapRollback where

open import Data.List using ([])
open import Data.Maybe using (Maybe; just; map)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import ConnectionManagement.State
open import ConnectionManagement.Rules.CM using (restoreMap)
open import ConnectionManagement.Store using (put)
open import ConnectionManagement.Domain using (ident; Provenance)
open Provenance using (inbound)
open import ConnectionManagement.Scenarios.Admission using (withOld; w₀; key₀; child₀)

-- The transaction has overwritten the entry while its original map is held.
original : CMStore
original = withOld reservedOutbound

heldMap : ConnMap
heldMap = insertConnection key₀ (ident 0) []

heldLease : Lease
heldLease = lease w₀ heldMap

written : CMStore
written = record original
  { mapCell = taken w₀
  ; entries = put (ident 0) (unnegotiated inbound key₀ child₀) (entries original) }

correct : Maybe CMStore
correct = restoreMap heldLease written

-- Deliberately wrong: mutable cells are restored to their old contents.
rollbackHeap : Maybe CMStore
rollbackHeap = map (λ c → record c { entries = entries original }) correct

restoration-is-not-heap-rollback : correct ≢ rollbackHeap
restoration-is-not-heap-rollback ()
