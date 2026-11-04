{-# OPTIONS --safe #-}

-- Server cancellation selects after flag publication; final states retain no owed work.
module Cardano_network.LeiosNotifyPipeLookahead.ServerShutdown
  (Notification : Set) where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.LeiosNotifyPipeLookahead.Model Notification

-- Visible operations never reset a published Quit flag.
step-flag : ∀ {p s a t} → Step p s a t → quitFlag s ≡ true → quitFlag t ≡ true
step-flag (receiveRequest _) ()
step-flag (receiveQuit _) ()
step-flag (choose _ _) ()
step-flag (send _) published = published
step-flag finish _ = refl

-- Hidden scheduling and completion bookkeeping never reset it either.
tau-flag : ∀ {s t} → Tau s t → quitFlag s ≡ true → quitFlag t ≡ true
tau-flag admitted published = published
tau-flag excessive published = published
tau-flag registered published = published
tau-flag setQuit ()
tau-flag (claim _) published = published
tau-flag (cancel _) _ = refl
tau-flag (retire _) published = published
tau-flag flush published = published
tau-flag drained _ = refl
tau-flag abort published = published

-- Publication remains true at every later finite source prefix.
run-flag : ∀ {p s actions t} → Run p s actions t → quitFlag s ≡ true → quitFlag t ≡ true
run-flag stop published = published
run-flag (internal pr run) published = run-flag run (tau-flag pr published)
run-flag (visible pr run) published = run-flag run (step-flag pr published)

-- The queue callback cannot select a new result after the true Quit flag.
no-callback-after-flag : ∀ {p s msg t} → Step p s (nextReply msg) t → quitFlag s ≡ true → ⊥
no-callback-after-flag (choose _ _) ()

-- A newly selected reply from claimed control after flag publication is exactly Canceled.
tau-new-selection : ∀ {s t msg} → Tau s t → quitFlag s ≡ true →
  sender s ≡ claimed → sender t ≡ selected msg → msg ≡ canceled
tau-new-selection admitted _ refl ()
tau-new-selection excessive _ refl ()
tau-new-selection registered _ refl ()
tau-new-selection setQuit () _ _
tau-new-selection (claim _) _ () _
tau-new-selection (cancel _) _ _ refl = refl
tau-new-selection (retire _) _ () _
tau-new-selection flush _ refl ()
tau-new-selection drained _ () _
tau-new-selection abort _ refl ()

-- Both phases have flushed completions and no queued, active or unregistered reply work.
data Final : State → Set where
  ready-final : Final (state doneReady 0 idle 0 true)
  closed-final : Final (state closed 0 idle 0 true)

-- Only the final Done wire operation can advance either final phase.
step-final : ∀ {p s a t} → Step p s a t → Final s → Final t
step-final (receiveRequest _) ()
step-final (receiveQuit _) ()
step-final (choose _ _) ()
step-final (send _) ()
step-final finish _ = closed-final

-- No source scheduling operation remains enabled in a final phase.
tau-final : ∀ {s t} → Tau s t → Final s → Final t
tau-final admitted ()
tau-final excessive ()
tau-final registered ()
tau-final setQuit ()
tau-final (claim _) ()
tau-final (cancel _) ()
tau-final (retire _) ()
tau-final flush ()
tau-final drained ()
tau-final abort ()

-- Final server status persists throughout every finite source continuation.
run-final : ∀ {p s actions t} → Run p s actions t → Final s → Final t
run-final stop final = final
run-final (internal pr run) final = run-final run (tau-final pr final)
run-final (visible pr run) final = run-final run (step-final pr final)

-- Final status implies zero owed replies without counting old completion tokens as work.
final-owed-zero : ∀ {s} → Final s → owed s ≡ 0
final-owed-zero ready-final = refl
final-owed-zero closed-final = refl
