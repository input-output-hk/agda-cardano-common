{-# OPTIONS --safe #-}

-- Per-peer credit and outgoing-message queue transactions at consensus 2416493.
-- Eligible application notifications are explicit inputs; ledger/relay guards are external.
open import Data.Nat using (ℕ)
module Cardano_network.LeiosNotifyPipeLookahead.CreditModel
  (Notification : Set) (limit : ℕ) where

open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n)
open import Data.List using (List; []; _∷_; _∷ʳ_; _++_; length)
import Data.List.Properties as List
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Empty using (⊥-elim)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; trans)

-- Credits are unallocated response slots, not all unanswered wire requests.
record State : Set where
  constructor credits
  field
    free : ℕ
    queued : List Notification
open State public

-- The pinned node initializes both resources empty.
initial : State
initial = credits 0 []

-- Each action represents one successful source STM transaction or eligible input.
data Action : Set where
  admitAccepted admitExcessive : Action
  offer take : Notification → Action

-- Equality with the limit, rather than an invented greater-than guard, selects failure.
data Step : State → Action → State → Set where
  admitted : ∀ {c qs} → c ≢ limit →
    Step (credits c qs) admitAccepted (credits (suc c) qs)
  excessive : ∀ {c qs} → c ≡ limit →
    Step (credits c qs) admitExcessive (credits c qs)
  enqueued : ∀ {c qs m} →
    Step (credits (suc c) qs) (offer m) (credits c (qs ∷ʳ m))
  dropped : ∀ {qs m} → Step (credits 0 qs) (offer m) (credits 0 qs)
  dequeued : ∀ {c qs m} → Step (credits c (m ∷ qs)) (take m) (credits c qs)

-- Sequential transactions preserve exact outgoing queue order.
data Run : State → List Action → State → Set where
  stop : ∀ {s} → Run s [] s
  step : ∀ {s t u a es} → Step s a t → Run t es u → Run s (a ∷ es) u

-- Append source transactions without discarding queue operations.
append : ∀ {s t u es fs} → Run s es t → Run t fs u → Run s (es ++ fs) u
append stop q = q
append (step st run) q = step st (append run q)

-- Below-or-equal and unequal is sufficient for the exact equality-based admission guard.
strict-next : ∀ {m n} → m ≤ n → m ≢ n → suc m ≤ n
strict-next {zero} {zero} pr neq = ⊥-elim (neq refl)
strict-next {zero} {suc n} pr neq = Data.Nat.s≤s Data.Nat.z≤n
strict-next {suc m} {suc n} (Data.Nat.s≤s pr) neq =
  Data.Nat.s≤s (strict-next pr (λ eq → neq (cong suc eq)))

-- The free counter is bounded on all transactions starting within its bound.
step-bounded : ∀ {s a t} → Step s a t → free s ≤ limit → free t ≤ limit
step-bounded (admitted neq) bound = strict-next bound neq
step-bounded (excessive _) bound = bound
step-bounded (enqueued {c = c}) bound = ≤-trans (n≤1+n c) bound
step-bounded dropped bound = bound
step-bounded dequeued bound = bound

-- This bound does not by itself bound the queued-message count.
run-bounded : ∀ {s es t} → Run s es t → free s ≤ limit → free t ≤ limit
run-bounded stop bound = bound
run-bounded (step st run) bound = run-bounded run (step-bounded st bound)

-- A queue family makes its append order explicit in constructive witnesses.
queueOf : Notification → ℕ → List Notification
queueOf m zero = []
queueOf m (suc n) = queueOf m n ∷ʳ m

-- The explicit queue family contains exactly the requested number of messages.
queueOf-length : (m : Notification) (n : ℕ) → length (queueOf m n) ≡ n
queueOf-length m zero = refl
queueOf-length m (suc n) = trans (List.length-++-sucʳ (queueOf m n) m [])
  (cong suc (trans (cong length (List.++-identityʳ (queueOf m n))) (queueOf-length m n)))

-- One admitted request can immediately reserve a queued message and free the counter.
reserve-cycle : (m : Notification) (qs : List Notification) → limit ≢ 0 →
  Run (credits 0 qs) (admitAccepted ∷ offer m ∷ []) (credits 0 (qs ∷ʳ m))
reserve-cycle m qs nonzero = step (admitted (λ eq → nonzero (sym eq))) (step enqueued stop)

-- Arbitrarily many reservations can pass the free-credit guard without any dequeue.
queued-reachable : (m : Notification) → limit ≢ 0 → (n : ℕ) →
  Σ[ es ∈ List Action ] Run initial es (credits 0 (queueOf m n))
queued-reachable m nonzero zero = [] , stop
queued-reachable m nonzero (suc n) with queued-reachable m nonzero n
... | es , run = es ++ (admitAccepted ∷ offer m ∷ []) , append run (reserve-cycle m _ nonzero)
