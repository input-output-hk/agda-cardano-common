{-# OPTIONS --safe #-}

-- Exact resource accounting counts early collection and final drain separately from replies.
module Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Accounting
  (Notification : Set) where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc; _+_; _≤_)
open import Data.Nat.Properties using (+-identityʳ; +-suc; +-assoc; m≤m+n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Model Notification
import Cardano_network.LeiosNotifyPipeLookahead.ServerConservation Notification as Counts

-- A sent-but-unretired job still belongs to unfinished registered work.
unfinished : State → ℕ
unfinished s = waiting s + activeJob (sender s)

-- Add the current unregistered request to all registered, unflushed jobs.
work : State → ℕ
work s = unregistered (reader s) + registeredJobs s

-- Only the optional successful poll is normal-operation collection.
early-step : ∀ {s t} → Tau s t → ℕ
early-step pollHit = 1
early-step _ = 0

-- Blocking final-drain collection is a distinct source operation.
final-step : ∀ {s t} → Tau s t → ℕ
final-step flush = 1
final-step _ = 0

-- Both operations remove exactly one registered completion token.
collected-step : ∀ {s t} → Tau s t → ℕ
collected-step pr = early-step pr + final-step pr

-- Count all successful collections in a supplied source schedule.
collections : ∀ {p s actions t} → Run p s actions t → ℕ
collections stop = 0
collections (internal pr run) = collected-step pr + collections run
collections (visible _ run) = collections run

-- Count the same schedule's early, pre-registration collections.
early : ∀ {p s actions t} → Run p s actions t → ℕ
early stop = 0
early (internal pr run) = early-step pr + early run
early (visible _ run) = early run

-- Count only the final drain, without conflating its work with early collection.
final : ∀ {p s actions t} → Run p s actions t → ℕ
final stop = 0
final (internal pr run) = final-step pr + final run
final (visible _ run) = final run

-- Collection accounting composes over independently constructed source schedules.
early-append : ∀ {p s t u actions more} (prefix : Run p s actions t) (suffix : Run p t more u) →
  early (append prefix suffix) ≡ early prefix + early suffix
early-append stop suffix = refl
early-append (internal pr run) suffix =
  trans (cong (early-step pr +_) (early-append run suffix))
    (sym (+-assoc (early-step pr) (early run) (early suffix)))
early-append (visible pr run) suffix = early-append run suffix

-- A hidden operation preserves future collection work except when it collects a token.
tau-work : ∀ {s t} (pr : Tau s t) → work s ≡ collected-step pr + work t
tau-work admitted = refl
tau-work excessive = refl
tau-work (inspectZero _) = refl
tau-work (inspectPositive _) = refl
tau-work (pollHit {w = w} {sender = sender} {c = c})
  rewrite +-suc (activeJob sender) c | +-suc w (activeJob sender + c) = refl
tau-work (pollMiss _) = refl
tau-work registered = refl
tau-work setQuit = refl
tau-work (claim {r = r} {w = w} {c = c} _) =
  cong (unregistered r +_) (sym (+-suc w c))
tau-work (cancel _) = refl
tau-work (retire _) = refl
tau-work (flush {w = w} {sender = sender} {c = c})
  rewrite +-suc (activeJob sender) c | +-suc w (activeJob sender + c) = refl
tau-work drained = refl
tau-work abort = refl

-- Only RequestNext adds future collection work; Send does not retire the job.
step-work : ∀ {p s a t} → Step p s a t → work s + Counts.request a ≡ work t
step-work (receiveRequest {w = w} {sender = sender} {c = c} atFirst) =
  trans (+-suc (w + (activeJob sender + c)) 0) (cong suc (+-identityʳ _))
step-work (receiveRequest {w = w} {sender = sender} {c = c} atNext) =
  trans (+-suc (w + (activeJob sender + c)) 0) (cong suc (+-identityʳ _))
step-work (receiveQuit atFirst) = +-identityʳ _
step-work (receiveQuit atNext) = +-identityʳ _
step-work (choose _ _) = +-identityʳ _
step-work (send _) = +-identityʳ _
step-work finish = refl

-- This equality holds for all prefixes, including rejected admission and held sends.
run-balance : ∀ {p s actions t} (run : Run p s actions t) →
  work s + Counts.requests actions ≡ collections run + work t
run-balance stop = +-identityʳ _
run-balance (internal {t = t} {u = u} {es = actions} pr run) =
  trans (cong (_+ Counts.requests actions) (tau-work pr))
    (trans (+-assoc (collected-step pr) (work t) (Counts.requests actions))
      (trans (cong (collected-step pr +_) (run-balance run))
        (sym (+-assoc (collected-step pr) (collections run) (work u)))))
run-balance (visible {s = s} {a = a} {es = actions} pr run) =
  trans (sym (+-assoc (work s) (Counts.request a) (Counts.requests actions)))
    (trans (cong (_+ Counts.requests actions) (step-work pr)) (run-balance run))

-- A successful fresh session still collects exactly once per received request.
closed-collections : ∀ {p actions}
  (run : Run p initial actions (state closed 0 idle 0 true)) →
  collections run ≡ Counts.requests actions
closed-collections run = trans (sym (+-identityʳ _)) (sym (run-balance run))

-- Registration and polling never drop or invent an unanswered wire obligation.
tau-owed : ∀ {s t} → Tau s t → owed s ≡ owed t
tau-owed admitted = refl
tau-owed excessive = refl
tau-owed (inspectZero _) = refl
tau-owed (inspectPositive _) = refl
tau-owed pollHit = refl
tau-owed (pollMiss _) = refl
tau-owed registered = refl
tau-owed setQuit = refl
tau-owed (claim {r = r} {w = w} _) = cong (unregistered r +_) (sym (+-suc w 0))
tau-owed (cancel _) = refl
tau-owed (retire _) = refl
tau-owed flush = refl
tau-owed drained = refl
tau-owed abort = refl

-- Normal and Canceled Sends each consume exactly one unanswered request.
step-owed : ∀ {p s a t} → Step p s a t →
  owed s + Counts.request a ≡ Counts.reply a + owed t
step-owed (receiveRequest {w = w} {sender = sender} atFirst) =
  trans (+-suc (w + unsent sender) 0) (cong suc (+-identityʳ _))
step-owed (receiveRequest {w = w} {sender = sender} atNext) =
  trans (+-suc (w + unsent sender) 0) (cong suc (+-identityʳ _))
step-owed (receiveQuit atFirst) = +-identityʳ _
step-owed (receiveQuit atNext) = +-identityʳ _
step-owed (choose _ _) = +-identityʳ _
step-owed (send {r = r} {w = w} _) =
  trans (+-identityʳ _) (Counts.finish-job (unregistered r) w)
step-owed finish = refl

-- The wire ledger is independent of when completed jobs are collected.
reply-balance : ∀ {p s actions t} → Run p s actions t →
  owed s + Counts.requests actions ≡ Counts.replies actions + owed t
reply-balance stop = +-identityʳ _
reply-balance (internal {es = actions} pr run) =
  trans (cong (_+ Counts.requests actions) (tau-owed pr)) (reply-balance run)
reply-balance (visible {s = s} {t = t} {u = u} {a = a} {es = actions} pr run) =
  trans (sym (+-assoc (owed s) (Counts.request a) (Counts.requests actions)))
    (trans (cong (_+ Counts.requests actions) (step-owed pr))
      (trans (+-assoc (Counts.reply a) (owed t) (Counts.requests actions))
        (trans (cong (Counts.reply a +_) (reply-balance run))
          (sym (+-assoc (Counts.reply a) (Counts.replies actions) (owed u))))))

-- Every fresh prefix has no more normal/Canceled replies than RequestNext occurrences.
no-extra-replies : ∀ {p actions t} → Run p initial actions t →
  Counts.replies actions ≤ Counts.requests actions
no-extra-replies {actions = actions} {t = t} run =
  subst (Counts.replies actions ≤_) (sym (reply-balance run)) (m≤m+n _ (owed t))
