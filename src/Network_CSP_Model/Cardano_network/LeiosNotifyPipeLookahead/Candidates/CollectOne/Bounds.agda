{-# OPTIONS --safe #-}

-- History-independent bounds require an explicit bound on unfinished work at poll misses.
module Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Bounds
  (Notification : Set) where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-pred; +-suc; m≤n+m)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Model Notification
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Accounting Notification as A

-- The current request has a reserved slot only after the mandatory poll/zero test.
limit : ℕ → Reader → ℕ
limit bound register = bound
limit bound _ = suc bound

-- Registration needs the stronger bound; every other phase may retain one extra job.
Invariant : ℕ → State → Set
Invariant bound s = registeredJobs s ≤ limit bound (reader s)

-- The only environmental premise used is unfinished old work at a zero-token miss.
MissBound : ∀ {s t} → ℕ → Tau s t → Set
MissBound bound (pollMiss {w = w} {sender = sender} _) = w + activeJob sender ≤ bound
MissBound _ _ = ⊤

-- This predicate exposes every required miss premise along the supplied finite run.
Budgeted : ∀ {p s actions t} → ℕ → Run p s actions t → Set
Budgeted bound stop = ⊤
Budgeted bound (internal pr run) = MissBound bound pr × Budgeted bound run
Budgeted bound (visible _ run) = Budgeted bound run

-- Two adjacent budgeted schedules retain exactly their separately supplied miss premises.
budget-append : ∀ {p s t u actions more bound} (prefix : Run p s actions t) (suffix : Run p t more u) →
  Budgeted bound prefix → Budgeted bound suffix → Budgeted bound (append prefix suffix)
budget-append stop suffix _ budget = budget
budget-append (internal pr run) suffix (miss , rest) budget = miss , budget-append run suffix rest budget
budget-append (visible pr run) suffix budget more = budget-append run suffix budget more

-- Sender selection/send does not change the registered inventory or its phase limit.
step-invariant : ∀ {p s a t bound} → Step p s a t → Invariant bound s → Invariant bound t
step-invariant (receiveRequest atFirst) inv = inv
step-invariant (receiveRequest atNext) inv = inv
step-invariant (receiveQuit atFirst) inv = inv
step-invariant (receiveQuit atNext) inv = inv
step-invariant (choose _ _) inv = inv
step-invariant (send _) inv = inv
step-invariant finish inv = z≤n

-- A guarded hit reserves one slot; a guarded miss uses precisely its unfinished-work premise.
tau-invariant : ∀ {s t bound} (pr : Tau s t) → MissBound bound pr →
  Invariant bound s → Invariant bound t
tau-invariant admitted _ inv = inv
tau-invariant excessive _ inv = inv
tau-invariant (inspectZero empty) _ inv rewrite empty = z≤n
tau-invariant (inspectPositive _) _ inv = inv
tau-invariant (pollHit {w = w} {sender = sender} {c = c}) _ inv
  rewrite +-suc (activeJob sender) c | +-suc w (activeJob sender + c) = ≤-pred inv
tau-invariant (pollMiss {sender = sender} _) bound inv
  rewrite Data.Nat.Properties.+-identityʳ (activeJob sender) = bound
tau-invariant registered _ inv = s≤s inv
tau-invariant setQuit _ inv = inv
tau-invariant {bound = bound} (claim {r = r} {w = w} {c = c} _) _ inv =
  subst (_≤ limit bound r) (sym (+-suc w c)) inv
tau-invariant (cancel _) _ inv = inv
tau-invariant (retire _) _ inv = inv
tau-invariant (flush {w = w} {sender = sender} {c = c}) _ inv
  rewrite +-suc (activeJob sender) c | +-suc w (activeJob sender + c) =
  ≤-trans (Data.Nat.Properties.n≤1+n _) inv
tau-invariant drained _ inv = z≤n
tau-invariant abort _ inv = inv

-- The resource bound survives every interleaving of independent reader/sender operations.
run-invariant : ∀ {p s actions t bound} (run : Run p s actions t) →
  Budgeted bound run → Invariant bound s → Invariant bound t
run-invariant stop _ inv = inv
run-invariant (internal pr run) (miss , rest) inv =
  run-invariant run rest (tau-invariant pr miss inv)
run-invariant (visible pr run) budget inv = run-invariant run budget (step-invariant pr inv)

-- Every phase's limit is at most the single history-independent envelope.
limit-bound : ∀ bound r → limit bound r ≤ suc bound
limit-bound bound register = Data.Nat.Properties.n≤1+n bound
limit-bound bound first = ≤-refl
limit-bound bound admit = ≤-refl
limit-bound bound inspect = ≤-refl
limit-bound bound poll = ≤-refl
limit-bound bound awaitNext = ≤-refl
limit-bound bound signalQuit = ≤-refl
limit-bound bound flushing = ≤-refl
limit-bound bound doneReady = ≤-refl
limit-bound bound closed = ≤-refl
limit-bound bound raising = ≤-refl
limit-bound bound failed = ≤-refl

-- Fresh runs with the stated miss premises retain at most B+1 registered jobs.
initial-bound : ∀ {p actions t bound} (run : Run p initial actions t) →
  Budgeted bound run → registeredJobs t ≤ suc bound
initial-bound {t = t} {bound = bound} run budget =
  ≤-trans (run-invariant run budget z≤n) (limit-bound bound (reader t))

-- Completed tokens are one component of the same bounded registered inventory.
completed-bound : ∀ {p actions t bound} (run : Run p initial actions t) →
  Budgeted bound run → completed t ≤ suc bound
completed-bound {t = t} run budget =
  ≤-trans (≤-trans (m≤n+m (completed t) (activeJob (sender t)))
    (m≤n+m (activeJob (sender t) + completed t) (waiting t))) (initial-bound run budget)
