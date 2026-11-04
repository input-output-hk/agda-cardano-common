{-# OPTIONS --safe #-}

-- Exact request/reply accounting for every finite operational server execution.
module Cardano_network.LeiosNotifyPipeLookahead.ServerConservation
  (Notification : Set) where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc; _+_; _≤_)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; m≤m+n)
open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Cardano_network.LeiosNotifyPipeLookahead.Model Notification

-- Only RequestNext adds one unanswered request; Quit does not.
request : Action → ℕ
request recvRequest = 1
request _ = 0

-- Normal and Canceled each discharge one request; Done is a separate acknowledgment.
reply : Action → ℕ
reply (sendReply _) = 1
reply _ = 0

-- Count wire requests without counting callback/readiness actions.
requests : List Action → ℕ
requests [] = 0
requests (a ∷ actions) = request a + requests actions

-- Count every response occurrence, including repeated equal payloads.
replies : List Action → ℕ
replies [] = 0
replies (a ∷ actions) = reply a + replies actions

-- Moving the single unsent job into the sent phase removes exactly one obligation.
finish-job : (prefix waiting : ℕ) → prefix + (waiting + 1) ≡ suc (prefix + (waiting + 0))
finish-job prefix waiting = trans (cong (prefix +_) (+-suc waiting 0)) (+-suc prefix (waiting + 0))

-- Each visible step has its exact request/reply delta, at either callback contract.
step-balance : ∀ {p s a t} → Step p s a t → owed s + request a ≡ reply a + owed t
step-balance (receiveRequest {w = w} {s = sender} atFirst) =
  trans (+-suc (w + unsent sender) 0) (cong suc (+-identityʳ (w + unsent sender)))
step-balance (receiveRequest {w = w} {s = sender} atNext) =
  trans (+-suc (w + unsent sender) 0) (cong suc (+-identityʳ (w + unsent sender)))
step-balance (receiveQuit atFirst) = +-identityʳ _
step-balance (receiveQuit atNext) = +-identityʳ _
step-balance (choose _ _) = +-identityʳ _
step-balance (send {r = r} {w = w} _) =
  trans (+-identityʳ _) (finish-job (unregistered r) w)
step-balance finish = refl

-- Admission, registration, selection, retirement and flushing never lose owed work.
tau-balance : ∀ {s t} → Tau s t → owed s ≡ owed t
tau-balance admitted = refl
tau-balance excessive = refl
tau-balance registered = refl
tau-balance setQuit = refl
tau-balance (claim {r = r} {w = w} _) = cong (unregistered r +_) (sym (+-suc w 0))
tau-balance (cancel _) = refl
tau-balance (retire _) = refl
tau-balance flush = refl
tau-balance drained = refl
tau-balance abort = refl

-- Arbitrary starting obligations are retained through every finite prefix, even faults.
run-balance : ∀ {p s actions t} → Run p s actions t →
  owed s + requests actions ≡ replies actions + owed t
run-balance stop = +-identityʳ _
run-balance (internal {es = actions} step run) =
  trans (cong (_+ requests actions) (tau-balance step)) (run-balance run)
run-balance (visible {s = s} {t = t} {u = u} {a = a} {es = actions} step run) =
  trans (sym (+-assoc (owed s) (request a) (requests actions)))
    (trans (cong (_+ requests actions) (step-balance step))
      (trans (+-assoc (reply a) (owed t) (requests actions))
        (trans (cong (reply a +_) (run-balance run))
          (sym (+-assoc (reply a) (replies actions) (owed u))))))

-- Fresh sessions have no phantom initial obligations, independently of next's policy.
initial-balance : ∀ {p actions t} → Run p initial actions t →
  requests actions ≡ replies actions + owed t
initial-balance = run-balance

-- A fresh server cannot emit more reply occurrences than it received requests.
no-extra-replies : ∀ {p actions t} → Run p initial actions t → replies actions ≤ requests actions
no-extra-replies {actions = actions} {t = t} run =
  subst (replies actions ≤_) (sym (initial-balance run)) (m≤m+n (replies actions) (owed t))

-- A genuinely closed server has discharged all requests; EOF alone is not this premise.
closed-balance : ∀ {p actions} → Run p initial actions (state closed 0 idle 0 true) →
  requests actions ≡ replies actions
closed-balance run = trans (initial-balance run) (+-identityʳ _)
