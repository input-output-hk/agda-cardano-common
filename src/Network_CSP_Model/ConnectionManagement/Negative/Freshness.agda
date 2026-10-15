{-# OPTIONS --guardedness #-}

-- A malformed supply can pass one allocation and then collide. These fixtures
-- refute a weak modeling invariant; they do not describe source-reachable bugs.
module ConnectionManagement.Negative.Freshness where

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.Nat using (s≤s; z≤n)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.State
open import ConnectionManagement.Rules.CM using (freshInbound; selected)
open import ConnectionManagement.Properties.Stores
open import ConnectionManagement.Properties.Freshness
open import ConnectionManagement.Properties.MapUniqueness
open import ConnectionManagement.Properties.Counters using (CounterReferences)
open import ConnectionManagement.Properties.Entries using (MapReferences)
open import ConnectionManagement.CSP.Fixtures using (entry₀; binding; unneg)
open import ConnectionManagement.Negative.CounterValidity using (shadowed)
open import ConnectionManagement.Scenarios.Admission using (r₀; w₀)

-- Uniqueness of keys does not impose any freshness bound on their serials.
futureEntry : CMStore
futureEntry = cmStore (taken w₀) ((ident 1 , reservedOutbound) ∷ []) 0

future-unique : UniqueKeys (entries futureEntry)
future-unique = [] ∷ []

next-unused : lookup (ident (nextEntry futureEntry)) (entries futureEntry) ≡ nothing
next-unused = refl

future-not-bounded : ¬ BelowSupply (nextEntry futureEntry) (entries futureEntry)
future-not-bounded (() ∷ _)

afterFirst : CMStore
afterFirst = cmStore (taken w₀)
  ((ident 1 , reservedOutbound) ∷ (entry₀ , unneg) ∷ []) 1

first-allocation-succeeds : freshInbound r₀ futureEntry ≡ just (selected entry₀ afterFirst)
first-allocation-succeeds = refl

second-allocation-collides : freshInbound r₀ afterFirst ≡ nothing
second-allocation-collides = refl

-- The maintained singleton map/heap satisfy the stronger premises.
binding-unique : MapUnique binding
binding-unique = ([] ∷ []) , ([] ∷ []) ∷ []

heap-unique : UniqueKeys ((entry₀ , unneg) ∷ [])
heap-unique = [] ∷ []

heap-bounded : BelowSupply 1 ((entry₀ , unneg) ∷ [])
heap-bounded = s≤s z≤n ∷ []

-- The counter-negative fixture also fails outer-key uniqueness, as intended.
shadowed-not-unique : ¬ MapUnique shadowed
shadowed-not-unique ((neq ∷ _) ∷ _ , _) = neq refl
