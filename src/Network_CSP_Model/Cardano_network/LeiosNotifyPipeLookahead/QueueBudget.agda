{-# OPTIONS --safe #-}

-- Credit plus eligible-queue accounting before Quit; a frozen envelope afterwards.
module Cardano_network.LeiosNotifyPipeLookahead.QueueBudget (Notification : Set) where

open import Data.Bool using (Bool; true; false)
open import Data.List using (length)
open import Data.Nat using (ℕ; _+_; _≤_; suc; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-mono-≤; +-suc; suc-injective; m≤m+n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.CreditModel Notification 1000 as Q
import Cardano_network.LeiosNotifyPipeLookahead.ClientAccounting Notification Notification as ListCount
import Cardano_network.LeiosNotifyPipeLookahead.ServerPhase Notification as Phase
open import Cardano_network.LeiosNotifyPipeLookahead.NodeModel Notification 1000

-- A successful admission owns a credit before its sender registration completes.
admitted : S.Reader → ℕ
admitted S.register = 1
admitted _ = 0

-- Claimed work still needs a queued notification until selection or cancellation.
claimed : S.Sender → ℕ
claimed S.claimed = 1
claimed _ = 0

-- These obligations have not yet consumed a normal notification from the queue.
unassigned : S.State → ℕ
unassigned s = admitted (S.reader s) + (S.waiting s + claimed (S.sender s))

-- Application enqueue transfers one free credit into one stored notification.
total : Q.State → ℕ
total q = Q.free q + length (Q.queued q)

-- Before publication the equality is exact; cancellation may leave unused credits afterwards.
Budget : S.State → Q.State → Set
Budget (S.state r w sender c false) q = total q ≡ unassigned (S.state r w sender c false)
Budget (S.state r w sender c true) q = total q ≤ 1003

-- Accepted registration is included in the source's unregistered request correction.
admitted≤unregistered : ∀ r → admitted r ≤ S.unregistered r
admitted≤unregistered S.first = z≤n
admitted≤unregistered S.admit = z≤n
admitted≤unregistered S.register = ≤-refl
admitted≤unregistered S.awaitNext = z≤n
admitted≤unregistered S.signalQuit = z≤n
admitted≤unregistered S.flushing = z≤n
admitted≤unregistered S.doneReady = z≤n
admitted≤unregistered S.closed = z≤n
admitted≤unregistered S.raising = z≤n
admitted≤unregistered S.failed = z≤n

-- Only a claimed sender needs a notification; selected replies are already assigned.
claimed≤unsent : ∀ sender → claimed sender ≤ S.unsent sender
claimed≤unsent S.idle = z≤n
claimed≤unsent S.claimed = ≤-refl
claimed≤unsent (S.selected _) = z≤n
claimed≤unsent S.sent = z≤n

-- Unassigned notification slots are a subset of the live server reply obligations.
unassigned≤owed : ∀ s → unassigned s ≤ S.owed s
unassigned≤owed s = +-mono-≤ (admitted≤unregistered (S.reader s))
  (+-mono-≤ ≤-refl (claimed≤unsent (S.sender s)))

-- All eligible offers preserve total credit-plus-queue inventory, including dropped offers.
offer-total : ∀ {q q′ m} → Q.Step q (Q.offer m) q′ → total q ≡ total q′
offer-total (Q.enqueued {c = c} {qs = qs}) =
  trans (sym (+-suc c (length qs))) (sym (cong (c +_) (ListCount.snoc-length qs _)))
offer-total Q.dropped = refl

-- Wire records neither create nor consume an unassigned normal notification.
step : ∀ {s a t} → Step s a t → Budget (peer s) (queue s) → Budget (peer t) (queue t)
step (peerRecord request (S.receiveRequest S.atFirst)) budget = budget
step (peerRecord request (S.receiveRequest S.atNext)) budget = budget
step (peerRecord quit (S.receiveQuit S.atFirst)) budget = budget
step (peerRecord quit (S.receiveQuit S.atNext)) budget = budget
step (peerRecord reply (S.send {q = false} _)) budget = budget
step (peerRecord reply (S.send {q = true} _)) budget = budget
step (peerRecord done S.finish) budget = budget
step (applicationOffer {s = S.state r w sender c false} _ pr) budget = trans (sym (offer-total pr)) budget
step (applicationOffer {s = S.state r w sender c true} _ pr) budget = subst (_≤ 1003) (offer-total pr) budget

-- Fresh phase control prevents admission after the Quit flag has been published.
admission-false : ∀ {w sender c flag} → Phase.Phase (S.state S.admit w sender c flag) → flag ≡ false
admission-false (Phase.before _) = refl
admission-false (Phase.after ())

-- Claiming transfers one waiting slot to the current sender without changing its meaning.
claim-eq : ∀ r w c q → unassigned (S.state r (suc w) S.idle c q) ≡
  unassigned (S.state r w S.claimed c q)
claim-eq r w c q = cong (admitted r +_) (sym (+-suc w 0))

-- Selecting a notification removes exactly one unit from the unassigned side.
selection-eq : ∀ r w c q m → unassigned (S.state r w S.claimed c q) ≡
  suc (unassigned (S.state r w (S.selected (S.normal m)) c q))
selection-eq r w c q m = trans (cong (admitted r +_) (+-suc w 0))
  (+-suc (admitted r) (w + 0))

-- Every server transaction preserves the budget given a bound on its current owed work.
tau : ∀ {s t} → Tau s t → Phase.Phase (peer s) → S.owed (peer s) ≤ 1003 →
  Budget (peer s) (queue s) → Budget (peer t) (queue t)
tau (schedule S.admitted ()) phase owed budget
tau (schedule S.excessive ()) phase owed budget
tau (schedule (S.registered {q = false}) _) phase owed budget = budget
tau (schedule (S.registered {q = true}) _) phase owed budget = budget
tau (schedule (S.setQuit {w = w} {s = sender} {c = c}) _) phase owed budget =
  subst (_≤ 1003) (sym budget) (≤-trans (unassigned≤owed (S.state S.signalQuit w sender c false)) owed)
tau (schedule (S.claim {r = r} {w = w} {c = c} {q = false} _) _) phase owed budget =
  trans budget (claim-eq r w c false)
tau (schedule (S.claim {q = true} _) _) phase owed budget = budget
tau (schedule (S.cancel _) _) phase owed budget = budget
tau (schedule (S.retire {q = false} _) _) phase owed budget = budget
tau (schedule (S.retire {q = true} _) _) phase owed budget = budget
tau (schedule (S.flush {q = false}) _) phase owed budget = budget
tau (schedule (S.flush {q = true}) _) phase owed budget = budget
tau (schedule S.drained _) phase owed budget = budget
tau (schedule (S.abort {q = false}) _) phase owed budget = budget
tau (schedule (S.abort {q = true}) _) phase owed budget = budget
tau (admitAccepted {flag = flag} (Q.admitted _)) phase owed budget
  rewrite admission-false phase = cong suc budget
tau (admitExcessive {flag = flag} (Q.excessive _)) phase owed budget
  rewrite admission-false phase = budget
tau (nextQueued (Q.dequeued {c = free} {qs = qs})
  (S.choose {r = r} {w = w} {c = c} {m = S.normal m} _ _)) phase owed budget =
  suc-injective (trans (sym (+-suc free (length qs)))
    (trans budget (selection-eq r w c false m)))

-- The budget bounds the actual notification queue as well as unallocated credits.
queue-bound : ∀ {s q} → S.owed s ≤ 1003 → Budget s q → total q ≤ 1003
queue-bound {S.state r w sender c false} owed budget =
  subst (_≤ 1003) (sym budget) (≤-trans (unassigned≤owed (S.state r w sender c false)) owed)
queue-bound {S.state r w sender c true} owed budget = budget
