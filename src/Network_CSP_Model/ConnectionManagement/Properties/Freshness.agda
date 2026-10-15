{-# OPTIONS --guardedness #-}

-- A monotone supply bound is stronger than absence of just the next token.
-- These are allocation lemmas, not reachability or resource-bound assumptions.
module ConnectionManagement.Properties.Freshness where

open import Data.Nat using (ℕ; suc; _<_)
open import Data.Nat.Properties using (<-irrefl; <-trans; n<1+n)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; Σ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (Store; lookup; put)
open import ConnectionManagement.State
open import ConnectionManagement.Rules.CM using (freshInbound; Selection; selected)
open import ConnectionManagement.Properties.Stores

BelowSupply : ∀ {kind V} → ℕ → Store (Id kind) V → Set
BelowSupply n = KeysSatisfy (λ k → serial k < n)

-- Every allocated identity is strictly below the next supply value.
supply-absent : ∀ {kind V} n (xs : Store (Id kind) V) →
  BelowSupply n xs → lookup (ident n) xs ≡ nothing
supply-absent n xs bounded = apart-lookup (ident n) xs
  (map (λ { {x = k , v} lt eq → <-irrefl (sym (cong serial eq)) lt }) bounded)

supply-step : ∀ {kind V} n (v : V) (xs : Store (Id kind) V) →
  BelowSupply n xs → BelowSupply (suc n) (put (ident n) v xs)
supply-step n v xs bounded = put-keys (λ k → serial k < suc n) (ident n) v xs
  (n<1+n n) (map (λ lt → <-trans lt (n<1+n n)) bounded)

-- Fresh allocation is enabled under the bound and preserves uniqueness and the
-- incremented bound. No finite carrier/cutoff is introduced into the semantics.
fresh-inbound-valid : ∀ request c → UniqueKeys (entries c) →
  BelowSupply (nextEntry c) (entries c) →
  Σ CMStore (λ c′ →
    freshInbound request c ≡ just (selected (ident (nextEntry c)) c′) ×
    UniqueKeys (entries c′) × BelowSupply (nextEntry c′) (entries c′))
fresh-inbound-valid request c unique bounded
  rewrite supply-absent (nextEntry c) (entries c) bounded =
  record c { entries = put (ident (nextEntry c)) st (entries c)
           ; nextEntry = suc (nextEntry c) } ,
  refl , put-unique (ident (nextEntry c)) st (entries c) unique ,
  supply-step (nextEntry c) st (entries c) bounded
  where
  st = unnegotiated inbound (key request) (child request)
