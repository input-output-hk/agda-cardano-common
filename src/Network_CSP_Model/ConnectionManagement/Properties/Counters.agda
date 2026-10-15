{-# OPTIONS --guardedness #-}

-- Structural reference validity follows the counter traversal, including shadowed
-- bindings. This is one validity obligation, not a whole-state invariant.
module ConnectionManagement.Properties.Counters where

open import Data.Nat using (ℕ; _+_)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _,_; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (Store; lookup; put)
open import ConnectionManagement.State
open import ConnectionManagement.Properties.Entries using
  (Present; MapReferences; put-preserves-present)

-- Quantify over stored bindings, rather than only successful lookups. Duplicate
-- keys can hide dangling references from lookup but not from countIncoming.
InnerReferences : EntryHeap → Store LocalKey EntryId → Set
InnerReferences heap = All (λ binding → Present (proj₂ binding) heap)

CounterReferences : EntryHeap → ConnMap → Set
CounterReferences heap = All (λ binding → InnerReferences heap (proj₂ binding))

inner-count-total : ∀ heap inner → InnerReferences heap inner →
  Σ ℕ (λ n → countInner heap inner ≡ just n)
inner-count-total heap [] [] = 0 , refl
inner-count-total heap ((local , e) ∷ xs) ((st , eq) ∷ valid)
  with inner-count-total heap xs valid
... | n , rest rewrite eq | rest = inboundCount st + n , refl

count-total : ∀ heap m → CounterReferences heap m →
  Σ ℕ (λ n → countIncoming heap m ≡ just n)
count-total heap [] [] = 0 , refl
count-total heap ((remote , inner) ∷ xs) (valid ∷ rest)
  with inner-count-total heap inner valid | count-total heap xs rest
... | n , eq | k , eq′ rewrite eq | eq′ = n + k , refl

-- Conversely, a successful count certifies every traversed entry reference.
inner-count-valid : ∀ heap inner {n} → countInner heap inner ≡ just n →
  InnerReferences heap inner
inner-count-valid heap [] eq = []
inner-count-valid heap ((local , e) ∷ xs) eq
  with lookup e heap in found | countInner heap xs in counted
... | nothing | _ = impossible eq
  where
  impossible : ∀ {n} → nothing ≡ just n → InnerReferences heap ((local , e) ∷ xs)
  impossible ()
... | just st | nothing = impossible eq
  where
  impossible : ∀ {n} → nothing ≡ just n → InnerReferences heap ((local , e) ∷ xs)
  impossible ()
... | just st | just n = (st , found) ∷ inner-count-valid heap xs counted

count-valid : ∀ heap m {n} → countIncoming heap m ≡ just n → CounterReferences heap m
count-valid heap [] eq = []
count-valid heap ((remote , inner) ∷ xs) eq
  with countInner heap inner in counted | countIncoming heap xs in rest
... | nothing | _ = impossible eq
  where
  impossible : ∀ {n} → nothing ≡ just n → CounterReferences heap ((remote , inner) ∷ xs)
  impossible ()
... | just n | nothing = impossible eq
  where
  impossible : ∀ {n} → nothing ≡ just n → CounterReferences heap ((remote , inner) ∷ xs)
  impossible ()
... | just n | just k = inner-count-valid heap inner counted ∷ count-valid heap xs rest

-- Structural validity implies the earlier lookup-based reference property.
lookup-all : ∀ {K V} ⦃ _ : DecEq K ⦄ (P : V → Set) (k : K) xs {v} →
  All (λ binding → P (proj₂ binding)) xs → lookup k xs ≡ just v → P v
lookup-all P k [] [] ()
lookup-all P k ((q , old) ∷ xs) (p ∷ ps) eq with k ≟ q
... | yes _ with eq
...   | refl = p
lookup-all P k ((q , old) ∷ xs) (p ∷ ps) eq | no _ = lookup-all P k xs ps eq

counter-map-references : ∀ heap m → CounterReferences heap m → MapReferences heap m
counter-map-references heap m valid remote inner local e outer innerEq =
  lookup-all (λ ref → Present ref heap) local inner
    (lookup-all (InnerReferences heap) remote m valid outer) innerEq

-- Captured-entry updates preserve both published and saved-map validity.
inner-update : ∀ e st heap inner → InnerReferences heap inner →
  InnerReferences (put e st heap) inner
inner-update e st heap [] [] = []
inner-update e st heap ((local , ref) ∷ xs) (p ∷ ps) =
  put-preserves-present e ref st heap p ∷ inner-update e st heap xs ps

counter-update : ∀ e st heap m → CounterReferences heap m →
  CounterReferences (put e st heap) m
counter-update e st heap [] [] = []
counter-update e st heap ((remote , inner) ∷ xs) (p ∷ ps) =
  inner-update e st heap inner p ∷ counter-update e st heap xs ps

-- At the correct admission continuation, a valid full map enables the counter
-- step. The statement is about stepWorker; worker lookup is a separate premise.
import ConnectionManagement.Rules.Server as Server

published-counter-enabled : ∀ w request p e s m → mapCell (cm s) ≡ full m →
  CounterReferences (entries (cm s)) m →
  Σ State (λ s′ → Server.stepWorker w (admissionWorker request (countPublished p e))
    Server.readCounters s ≡ just s′)
published-counter-enabled w request p e s m cell valid
  with count-total (entries (cm s)) m valid
... | n , eq rewrite cell | eq =
  Server.setPC w (admissionWorker request (countPublished p e)) (awaitHandshake p e) s , refl

published-counter-taken : ∀ w request p e s owner → mapCell (cm s) ≡ taken owner →
  Server.stepWorker w (admissionWorker request (countPublished p e)) Server.readCounters s ≡ nothing
published-counter-taken w request p e s owner eq rewrite eq = refl
