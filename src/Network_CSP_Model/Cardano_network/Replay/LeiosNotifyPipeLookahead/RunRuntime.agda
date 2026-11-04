{-# OPTIONS --safe #-}

-- Concrete successful runs yield inhabited runtime witnesses, not production fairness evidence.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.RunRuntime
  (Notification Return : Set) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownProgress Notification Return as P
import Cardano_network.LeiosNotifyPipeLookahead.RuntimeProgress Notification Return as R

-- Each time index consumes one actual move; after the path ends the source state is fixed.
state : ∀ {p s rows t} → ℕ → D.Run p s rows t → D.State
state {s = s} zero run = s
state {s = s} (suc n) D.stop = s
state (suc n) (D.internal pr run) = state n run
state (suc n) (D.visible pr run) = state n run

-- A nonempty path advances by its exact operation; a completed path waits indefinitely.
tick : ∀ {p s rows t} (n : ℕ) (run : D.Run p s rows t) → R.Tick p (state n run)
tick zero D.stop = R.waiting
tick zero (D.internal pr run) = R.advance (P.internal pr)
tick zero (D.visible pr run) = R.advance (P.wire pr)
tick (suc n) D.stop = R.waiting
tick (suc n) (D.internal pr run) = tick n run
tick (suc n) (D.visible pr run) = tick n run

-- Runtime successor states retain the exact target of each source transition.
link : ∀ {p s rows t} n (run : D.Run p s rows t) → state (suc n) run ≡ R.after (tick n run)
link zero D.stop = refl
link zero (D.internal pr run) = refl
link zero (D.visible pr run) = refl
link (suc n) D.stop = refl
link (suc n) (D.internal pr run) = link n run
link (suc n) (D.visible pr run) = link n run

-- This is one explicitly constructed runtime schedule for the supplied successful path.
execution : ∀ {p s rows t} → D.Run p s rows t → R.Execution p
R.state (execution run) n = state n run
R.tick (execution run) n = tick n run
R.link (execution run) n = link n run

-- Shift response evidence across one exact hidden operation at the front of a witness.
shift-internal : ∀ {p s t rows u} (pr : D.Tau p s t) (run : D.Run p t rows u) n →
  R.Response (execution run) n → R.Response (execution (D.internal pr run)) (suc n)
shift-internal pr run n (R.now returned) = R.now returned
shift-internal pr run n (R.later eq response) = R.later eq (shift-internal pr run (suc n) response)

-- The same index shift retains visible operation witnesses.
shift-visible : ∀ {p s row t rows u} (pr : D.Step p s row t) (run : D.Run p t rows u) n →
  R.Response (execution run) n → R.Response (execution (D.visible pr run)) (suc n)
shift-visible pr run n (R.now returned) = R.now returned
shift-visible pr run n (R.later eq response) = R.later eq (shift-visible pr run (suc n) response)

-- This chosen schedule is responsive until its already proved target; no external IO is inferred.
responsive : ∀ {p s rows t} (Target : D.State → Set) (run : D.Run p s rows t) →
  Target t → R.Responsive Target (execution run)
responsive Target D.stop reached zero unfinished = ⊥-elim (unfinished reached)
responsive Target D.stop reached (suc n) unfinished = ⊥-elim (unfinished reached)
responsive Target (D.internal pr run) reached zero unfinished = R.now R.advanced
responsive Target (D.visible pr run) reached zero unfinished = R.now R.advanced
responsive Target (D.internal pr run) reached (suc n) unfinished =
  shift-internal pr run n (responsive Target run reached n unfinished)
responsive Target (D.visible pr run) reached (suc n) unfinished =
  shift-visible pr run n (responsive Target run reached n unfinished)

-- The constructed execution contains successful operations and waiting, with no faults.
no-failure : ∀ {p s rows t} (run : D.Run p s rows t) → R.NoFailure (execution run)
no-failure D.stop zero fault ()
no-failure D.stop (suc n) fault ()
no-failure (D.internal pr run) zero fault ()
no-failure (D.visible pr run) zero fault ()
no-failure (D.internal pr run) (suc n) fault eq = no-failure run n fault eq
no-failure (D.visible pr run) (suc n) fault eq = no-failure run n fault eq

-- There is no terminal observation, so this constructed schedule cannot halt prematurely.
maximal : ∀ {p s rows t} (run : D.Run p s rows t) → R.Maximal (execution run)
maximal D.stop zero ()
maximal D.stop (suc n) ()
maximal (D.internal pr run) zero ()
maximal (D.visible pr run) zero ()
maximal (D.internal pr run) (suc n) eq = maximal run n eq
maximal (D.visible pr run) (suc n) eq = maximal run n eq
