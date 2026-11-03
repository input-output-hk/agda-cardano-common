{-# OPTIONS --safe #-}

-- Resource statements for the unchanged node callback/server composition.
-- Queue-growth witnesses assume each displayed application offer is eligible;
-- they do not assert that a concrete ledger supplies those inputs.
open import Data.Nat using (ℕ)
module Cardano_network.LeiosNotifyPipeLookahead.NodeProperties
  (Notification : Set) (limit : ℕ) where

open import Data.Nat using (zero; suc; _≤_; _<_; z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Data.Bool using (false)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.CreditModel Notification limit as Q
open import Cardano_network.LeiosNotifyPipeLookahead.NodeModel Notification limit

-- Visible application inputs cannot violate the free-credit bound.
step-free-bounded : ∀ {s a t} → Step s a t → Q.free (queue s) ≤ limit →
  Q.free (queue t) ≤ limit
step-free-bounded (peerRecord _ _) bound = bound
step-free-bounded (applicationOffer _ pr) bound = Q.step-bounded pr bound

-- Admission and queue selection preserve the same invariant atomically.
tau-free-bounded : ∀ {s t} → Tau s t → Q.free (queue s) ≤ limit →
  Q.free (queue t) ≤ limit
tau-free-bounded (schedule _ _) bound = bound
tau-free-bounded (admitAccepted pr) bound = Q.step-bounded pr bound
tau-free-bounded (admitExcessive pr) bound = Q.step-bounded pr bound
tau-free-bounded (nextQueued pr _) bound = Q.step-bounded pr bound

-- Every joint execution preserves its starting free-credit bound.
run-free-bounded : ∀ {s es t} → Run s es t → Q.free (queue s) ≤ limit →
  Q.free (queue t) ≤ limit
run-free-bounded stop bound = bound
run-free-bounded (internal pr run) bound = run-free-bounded run (tau-free-bounded pr bound)
run-free-bounded (visible pr run) bound = run-free-bounded run (step-free-bounded pr bound)

-- In particular the pinned zero-credit initialization satisfies the bound.
initial-free-bounded : ∀ {es t} → Run initial es t → Q.free (queue t) ≤ limit
initial-free-bounded run = run-free-bounded run z≤n

-- Before the first request the reader uses ordinary Await; later it uses lookahead.
readerAt : ℕ → S.Reader
readerAt zero = S.first
readerAt (suc _) = S.awaitNext

-- Both reader phases admit the next request without scheduling the sender.
readingAt : (n : ℕ) → S.Reading (readerAt n)
readingAt zero = S.atFirst
readingAt (suc _) = S.atNext

-- All requests are registered and all supplied notifications remain queued.
backlog : Notification → ℕ → State
backlog m n = node (S.state (readerAt n) n S.idle 0 false)
  (Q.credits 0 (Q.queueOf m n))

-- One request plus an eligible input restores free credits to zero while growing work.
reserve-step : (m : Notification) (n : ℕ) → limit ≢ 0 →
  Run (backlog m n) (wire S.recvRequest ∷ offer m ∷ []) (backlog m (suc n))
reserve-step m n nonzero =
  visible (peerRecord request (S.receiveRequest (readingAt n))) $
  internal (admitAccepted (Q.admitted (λ eq → nonzero (sym eq)))) $
  internal (schedule S.registered refl) $
  visible (applicationOffer refl Q.enqueued) stop

-- Any finite number of these cycles is reachable without a reply selection/send.
backlog-reachable : (m : Notification) → limit ≢ 0 → (n : ℕ) →
  Σ[ es ∈ List Action ] Run initial es (backlog m n)
backlog-reachable m nonzero zero = [] , stop
backlog-reachable m nonzero (suc n) with backlog-reachable m nonzero n
... | es , run = es ++ (wire S.recvRequest ∷ offer m ∷ []) ,
  append run (reserve-step m n nonzero)

-- Sender jobs and queue entries grow together even though the guarded counter is zero.
backlog-counts : (m : Notification) (n : ℕ) →
  (S.waiting (peer (backlog m n)) ≡ n) ×
  (length (Q.queued (queue (backlog m n))) ≡ n) ×
  (Q.free (queue (backlog m n)) ≡ 0)
backlog-counts m n = refl , Q.queueOf-length m n , refl

-- The admission limit alone therefore cannot bound deferred jobs or outgoing messages.
admission-bound-counterexample : (m : Notification) → limit ≢ 0 → (bound : ℕ) →
  Σ[ es ∈ List Action ]
    (Run initial es (backlog m (suc bound)) ×
     (bound < S.waiting (peer (backlog m (suc bound)))) ×
     (bound < length (Q.queued (queue (backlog m (suc bound))))))
admission-bound-counterexample m nonzero bound with backlog-reachable m nonzero (suc bound)
... | es , run rewrite Q.queueOf-length m (suc bound) = es , run , ≤-refl , ≤-refl
