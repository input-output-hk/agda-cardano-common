{-# OPTIONS --guardedness #-}

-- Intentional bad model: exposes TIME_WAIT's entry write before the same STM
-- transaction can acquire the map. This refutes a modeling shortcut, not code.
module ConnectionManagement.Negative.CleanupAtomicity where

open import Data.Maybe using (map; nothing)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import ConnectionManagement.Domain using (ident)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.State
open import ConnectionManagement.Scenarios.Cleanup using
  (blockedFinalizer; finalizer-blocked; blocked-entry-still-terminating)

-- Deliberately wrong: commit the write while mapCell is still taken.
writeBeforeMap : State → State
writeBeforeMap s = record s { cm = record (cm s)
  { entries = put (ident 0) (terminated nothing) (entries (cm s)) } }

early-write-is-observable :
  map (λ s → lookup (ident 0) (entries (cm s))) blockedFinalizer ≢
  map (λ s → lookup (ident 0) (entries (cm s))) (map writeBeforeMap blockedFinalizer)
early-write-is-observable ()
