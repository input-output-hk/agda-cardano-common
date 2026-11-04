{-# OPTIONS --safe #-}

-- The added guarded inspection/polling consumes finite internal work without a polling loop.
module Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Rank
  (Notification : Set) where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; m≤n⇒m≤1+n; +-suc; +-monoʳ-<;
  +-mono-≤; +-monoʳ-≤; *-distribʳ-+; m≤m*n; ≤-trans)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Model Notification
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Safety Notification as S

-- Five units cover claim, select/cancel, Send, retirement and final collection.
five : ℕ → ℕ
five n = n * 5

-- Registration reserves five waiting-job units; inspection/polling each gets its own unit.
readerCost : Reader → ℕ
readerCost admit = 9
readerCost inspect = 8
readerCost poll = 7
readerCost register = 6
readerCost signalQuit = 3
readerCost flushing = 2
readerCost doneReady = 1
readerCost raising = 1
readerCost _ = 0

-- A selected send remains real work; a sent reply still needs retirement and collection.
senderCost : Sender → ℕ
senderCost idle = 0
senderCost claimed = 4
senderCost (selected _) = 3
senderCost sent = 2

-- This potential is on the candidate's independent state, not the baseline simulation.
rank : State → ℕ
rank (state r w sender c q) = readerCost r + (five w + (senderCost sender + c))

-- Every candidate hidden operation strictly decreases this natural potential.
decreases : ∀ {s t} → Tau s t → rank t < rank s
decreases admitted = ≤-refl
decreases excessive = m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n
  (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl))))))
decreases (inspectZero _) = m≤n⇒m≤1+n ≤-refl
decreases (inspectPositive _) = ≤-refl
decreases (pollHit {w = w} {sender = sender} {c = c})
  rewrite +-suc (senderCost sender) c | +-suc (five w) (senderCost sender + c) =
  m≤n⇒m≤1+n ≤-refl
decreases (pollMiss _) = ≤-refl
decreases registered = ≤-refl
decreases setQuit = ≤-refl
decreases (claim {r = r} {w = w} {c = c} _)
  rewrite +-suc (five w) (suc (suc (suc c))) | +-suc (five w) (suc (suc c)) |
    +-suc (five w) (suc c) | +-suc (five w) c =
  +-monoʳ-< (readerCost r) ≤-refl
decreases (cancel {r = r} {w = w} _) =
  +-monoʳ-< (readerCost r) (+-monoʳ-< (five w) ≤-refl)
decreases (retire {r = r} {w = w} _) =
  +-monoʳ-< (readerCost r) (+-monoʳ-< (five w) ≤-refl)
decreases (flush {w = w} {sender = sender} {c = c})
  rewrite +-suc (senderCost sender) c | +-suc (five w) (senderCost sender + c) = ≤-refl
decreases drained = ≤-refl
decreases abort = ≤-refl

-- Ranking accessibility rules out infinite hidden paths even outside fresh reachable states.
from-rank : (s : State) → Acc _<_ (rank s) → Acc (λ t s → Tau s t) s
from-rank s (acc smaller) = acc λ {t} pr → from-rank t (smaller (decreases pr))

-- No resource bound or callback readiness assumption is required for internal accessibility.
tau-accessible : ∀ s → Acc (λ t s → Tau s t) s
tau-accessible s = from-rank s (<-wellFounded (rank s))

-- During shutdown even visible selection/Send/Done operations strictly decrease the potential.
step-decreases : ∀ {p s a t} → Step p s a t → S.Stopping s → rank t < rank s
step-decreases (receiveRequest atFirst) ()
step-decreases (receiveRequest atNext) ()
step-decreases (receiveQuit atFirst) ()
step-decreases (receiveQuit atNext) ()
step-decreases (choose {r = r} {w = w} _ _) _ =
  +-monoʳ-< (readerCost r) (+-monoʳ-< (five w) ≤-refl)
step-decreases (send {r = r} {w = w} _) _ =
  +-monoʳ-< (readerCost r) (+-monoʳ-< (five w) ≤-refl)
step-decreases finish _ = ≤-refl

-- Every active sender costs at most five units irrespective of the selected payload.
sender-bound : ∀ sender → senderCost sender ≤ five (activeJob sender)
sender-bound idle = z≤n
sender-bound claimed = s≤s (s≤s (s≤s (s≤s z≤n)))
sender-bound (selected _) = s≤s (s≤s (s≤s z≤n))
sender-bound sent = s≤s (s≤s z≤n)

-- Distribute the resource coefficient without normalizing any operational execution.
inventory-bound : ∀ w sender c → five w + (senderCost sender + c) ≤ five (w + (activeJob sender + c))
inventory-bound w sender c rewrite *-distribʳ-+ 5 w (activeJob sender + c) |
  *-distribʳ-+ 5 (activeJob sender) c =
  +-monoʳ-≤ (five w) (+-mono-≤ (sender-bound sender) (m≤m*n c 5))

-- At actual Quit and later, three reader units suffice on top of five per retained job.
shutdown-bound : ∀ {s} → S.Stopping s → rank s ≤ 3 + five (registeredJobs s)
shutdown-bound (S.publishing {w = w} {sender = sender} {c = c}) =
  +-mono-≤ ≤-refl (inventory-bound w sender c)
shutdown-bound (S.flushing {w = w} {sender = sender} {c = c}) =
  +-mono-≤ (s≤s (s≤s z≤n)) (inventory-bound w sender c)
shutdown-bound S.ready = s≤s z≤n
shutdown-bound S.closed = z≤n
