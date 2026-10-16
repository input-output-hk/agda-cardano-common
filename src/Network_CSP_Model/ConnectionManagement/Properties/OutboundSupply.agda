{-# OPTIONS --guardedness #-}

-- The missing premise for reservation cleanup is a bound on its captured
-- entry, not just the current heap. Establishing that premise for reachable
-- outbound frames is a separate invariant obligation.
module ConnectionManagement.Properties.OutboundSupply where

open import Data.Nat using (_<_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Function using (case_of_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Properties.Stores using (put-keys)
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)
import ConnectionManagement.Rules.OutboundAcquire as A

-- No heap lookup is required by this source-derived rule: a valid capture
-- supplies the bound even if its map binding has already disappeared.
remove-reservation-preserves : ∀ caller mode req e err s {f′ s′} →
  serial e < nextEntry (cm s) →
  A.step caller mode A.removeReservation (A.frame req (A.removeError e err)) s ≡ just (f′ , s′) →
  SupplyBounds s → SupplyBounds s′
remove-reservation-preserves caller mode req e err s captured eq (heap , promises)
  with mapCell (cm s)
... | taken _ = case eq of λ ()
... | full m = subst (λ result → SupplyBounds (Data.Product.proj₂ result))
  (just-injective eq)
  (put-keys (λ k → serial k < nextEntry (cm s)) e (terminated nothing)
    (entries (cm s)) captured heap , promises)
