{-# OPTIONS --safe #-}

-- Scheduling terminates between observations; callback waiting is not a tau loop.
module Cardano_network.LeiosNotifyPipeLookahead.Rank
  (Notification : Set) where

open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.Nat.Properties using (≤-refl; m≤n⇒m≤1+n; +-suc; +-monoʳ-<)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Cardano_network.LeiosNotifyPipeLookahead.Model Notification

-- Count three units for every registered, unclaimed sender job.
triple : ℕ → ℕ
triple zero = 0
triple (suc n) = suc (suc (suc (triple n)))

-- Reader costs pay for registration, publication, flushing and exception cancellation.
readerCost : Reader → ℕ
readerCost admit = 5
readerCost register = 4
readerCost signalQuit = 2
readerCost flushing = 1
readerCost raising = 1
readerCost _ = 0

-- A retired send trades cost three for a completion token of cost one.
senderCost : Sender → ℕ
senderCost idle = 0
senderCost claimed = 2
senderCost (selected _) = 1
senderCost sent = 3

-- The measure counts internal work without bounding visible connection history.
rank : State → ℕ
rank (state r w s c q) = readerCost r + (triple w + (senderCost s + c))

-- Every independent hidden rule strictly consumes the available internal work.
decreases : ∀ {s t} → Tau s t → rank t < rank s
decreases admitted = ≤-refl
decreases excessive = m≤n⇒m≤1+n (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl))
decreases registered = ≤-refl
decreases setQuit = ≤-refl
decreases (claim {r = r} {w = w} {c = c} _)
  rewrite +-suc (triple w) (suc c) | +-suc (triple w) c =
  +-monoʳ-< (readerCost r) ≤-refl
decreases (cancel {r = r} {w = w} _) =
  +-monoʳ-< (readerCost r) (+-monoʳ-< (triple w) ≤-refl)
decreases (retire {r = r} {w = w} _) =
  +-monoʳ-< (readerCost r) (+-monoʳ-< (triple w) (m≤n⇒m≤1+n ≤-refl))
decreases (flush {w = w} {s = s} {c = c})
  rewrite +-suc (senderCost s) c | +-suc (triple w) (senderCost s + c) = ≤-refl
decreases drained = ≤-refl
decreases abort = ≤-refl

-- Accessibility converts a natural-number ranking into the reverse-step relation.
from-rank : (s : State) → Acc _<_ (rank s) → Acc (λ t s → Tau s t) s
from-rank s (acc smaller) = acc λ {t} step → from-rank t (smaller (decreases step))

-- All operational states have finite hidden paths, including failure paths.
tau-accessible : ∀ s → Acc (λ t s → Tau s t) s
tau-accessible s = from-rank s (<-wellFounded (rank s))
