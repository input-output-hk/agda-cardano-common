{-# OPTIONS --guardedness #-}

-- G1 local primitive controls, not initialized source histories. A failed
-- lease operation returns no candidate state; restoring a map keeps the heap.
module ConnectionManagement.Negative.PrimitiveMap where

open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
import ConnectionManagement.Rules.CM as CM
import ConnectionManagement.Negative.HeapRollback as H
open import ConnectionManagement.Scenarios.Admission using (w₀; w₁)

-- Empty TMVar retry and owner checking complement the existing success paths.
empty : CMStore
empty = cmStore (full []) [] 0
held : CMStore
held = cmStore (taken w₀) [] 0
take-enabled : CM.takeMap w₀ empty ≡ just (lease w₀ [] , held)
take-enabled = refl
take-empty-refused : CM.takeMap w₁ held ≡ nothing
take-empty-refused = refl
put-enabled : CM.putMap (lease w₀ []) [] held ≡ just empty
put-enabled = refl
put-full-refused : CM.putMap (lease w₀ []) [] empty ≡ nothing
put-full-refused = refl
foreign-put-refused : CM.putMap (lease w₁ []) [] held ≡ nothing
foreign-put-refused = refl
restore-enabled : CM.restoreMap H.heldLease H.written ≡
  just (record H.written { mapCell = full H.heldMap })
restore-enabled = refl
foreign-restore-refused : CM.restoreMap (lease w₁ H.heldMap) H.written ≡ nothing
foreign-restore-refused = refl
