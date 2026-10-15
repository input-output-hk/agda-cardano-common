{-# OPTIONS --guardedness #-}

-- Allocated entry/promise identities lie strictly below their next supplies.
-- This says nothing about worker/handle freshness or validity of references.
module ConnectionManagement.Properties.SupplyBounds where

open import Data.Nat using (ℕ; suc; _<_)
open import Data.Nat.Properties using (<-trans; n<1+n; <-irrefl)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import Function using (case_of_)
open import Class.DecEq using (DecEq; _≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (Store; lookup; put)
open import ConnectionManagement.State
open import ConnectionManagement.Properties.Stores using (KeysSatisfy; put-keys)
open import ConnectionManagement.Properties.Freshness using (BelowSupply; supply-step; supply-absent)
import ConnectionManagement.Rules.CM as CM

PromiseBound : ℕ → List PromiseId → Set
PromiseBound n = All (λ p → serial p < n)

SupplyBounds : State → Set
SupplyBounds s = BelowSupply (nextEntry (cm s)) (entries (cm s)) × PromiseBound (nextPromise s) (promises s)

-- Retrieve a key predicate through exact lookup, without uniqueness premises.
lookup-key : ∀ {K V} ⦃ _ : DecEq K ⦄ (P : K → Set) k (xs : Store K V) {v} →
  KeysSatisfy P xs → lookup k xs ≡ just v → P k
lookup-key P k [] [] ()
lookup-key P k ((q , old) ∷ xs) (p ∷ ps) eq with k ≟ q
... | yes refl = p
... | no _ = lookup-key P k xs ps eq

-- Every entry update in the current machine is preceded by a successful lookup.
overwrite-bound : ∀ n (e : EntryId) (st : ConnectionState) (heap : EntryHeap) {old} → BelowSupply n heap → lookup e heap ≡ just old →
  BelowSupply n (put e st heap)
overwrite-bound n e st heap bounded found =
  put-keys (λ e → serial e < n) e st heap (lookup-key (λ e → serial e < n) e heap bounded found) bounded

promise-step : ∀ n ps → PromiseBound n ps → PromiseBound (suc n) (ident n ∷ ps)
promise-step n ps bounded = n<1+n n ∷ map (λ lt → <-trans lt (n<1+n n)) bounded

-- Primitive allocation and replacement preserve the entry supply bound.
fresh-bound : ∀ r c {e c′} → CM.freshInbound r c ≡ just (CM.selected e c′) →
  BelowSupply (nextEntry c) (entries c) → BelowSupply (nextEntry c′) (entries c′)
fresh-bound r c eq bounded with lookup (ident (nextEntry c)) (entries c)
... | just _ = case eq of λ ()
... | nothing with eq
...   | refl = supply-step (nextEntry c) (unnegotiated inbound (key r) (child r)) (entries c) bounded

existing-bound : ∀ e st r c {e′ c′} → lookup e (entries c) ≡ just st →
  CM.existingInbound e st r c ≡ just (CM.selected e′ c′) →
  BelowSupply (nextEntry c) (entries c) → BelowSupply (nextEntry c′) (entries c′)
existing-bound e reservedOutbound r c found refl bounded =
  overwrite-bound (nextEntry c) e (unnegotiated inbound (key r) (child r)) (entries c) bounded found
existing-bound e (unnegotiated p k w) r c found refl bounded =
  overwrite-bound (nextEntry c) e (unnegotiated inbound (key r) (child r)) (entries c) bounded found
existing-bound e (terminating _ _ _) r c found eq bounded = fresh-bound r c eq bounded
existing-bound e (terminated _) r c found eq bounded = fresh-bound r c eq bounded
existing-bound e (outboundUni _ _ _) r c found () bounded
existing-bound e (outboundDup _ _ _ _) r c found () bounded
existing-bound e (outboundIdle _ _ _ _) r c found () bounded
existing-bound e (inboundIdle _ _ _ _) r c found () bounded
existing-bound e (inboundActive _ _ _ _) r c found () bounded
existing-bound e (duplexActive _ _ _) r c found () bounded

selected-bound : ∀ l r c {e c′} → CM.selectInbound l r c ≡ just (CM.selected e c′) →
  BelowSupply (nextEntry c) (entries c) → BelowSupply (nextEntry c′) (entries c′)
selected-bound l r c eq bounded with mapCell c
... | full _ = case eq of λ ()
... | taken w with owner l ≟ w
...   | no _ = case eq of λ ()
...   | yes _ with lookupConnection (key r) (savedMap l)
...     | nothing = fresh-bound r c eq bounded
...     | just e with lookup e (entries c) in found
...       | nothing = case eq of λ ()
...       | just st = existing-bound e st r c found eq bounded

-- Map take/put do not alter the entry heap or its supply.
take-bound : ∀ w c {l c′} → CM.takeMap w c ≡ just (l , c′) →
  BelowSupply (nextEntry c) (entries c) → BelowSupply (nextEntry c′) (entries c′)
take-bound w c eq bounded with mapCell c
... | taken _ = case eq of λ ()
... | full m with eq
...   | refl = bounded

put-bound : ∀ l m c {c′} → CM.putMap l m c ≡ just c′ →
  BelowSupply (nextEntry c) (entries c) → BelowSupply (nextEntry c′) (entries c′)
put-bound l m c eq bounded with mapCell c
... | full _ = case eq of λ ()
... | taken w with owner l ≟ w
...   | no _ = case eq of λ ()
...   | yes _ with eq
...     | refl = bounded

-- The next promise ID is absent from the allocated-promise list. The source's
-- prepend allocation needs this stronger invariant to avoid eventual collisions.
open import Data.Bool using (false)
open import Data.Bool.ListAction using (any)
open import Relation.Nullary using (does)
open import Data.Empty using (⊥-elim)

promise-next-absent : ∀ n ps → PromiseBound n ps →
  any (λ p → does (p ≟ ident n)) ps ≡ false
promise-next-absent n [] [] = refl
promise-next-absent n (p ∷ ps) (lt ∷ bounded) with p ≟ ident n
... | yes eq = ⊥-elim (<-irrefl (cong serial eq) lt)
... | no _ = promise-next-absent n ps bounded
