{-# OPTIONS --safe #-}

-- Reachable server reader phases retain the flag and exact final-state shape.
module Cardano_network.LeiosNotifyPipeLookahead.ServerPhase
  (Notification : Set) where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.Properties Notification as Control
import Cardano_network.LeiosNotifyPipeLookahead.ServerProgress Notification as Shutdown

-- These reader phases precede a successful Quit receive, including the fault path.
data Before : S.Reader → Set where
  first : Before S.first
  admit : Before S.admit
  register : Before S.register
  awaitNext : Before S.awaitNext
  raising : Before S.raising
  failed : Before S.failed

-- Before Quit the flag is false; after Quit the existing exact shutdown invariant applies.
data Phase : S.State → Set where
  before : ∀ {r w sender c} → Before r → Phase (S.state r w sender c false)
  after : ∀ {s} → Shutdown.Stopping s → Phase s

-- Source wire/callback operations preserve the reader-phase structure.
step-phase : ∀ {p s a t} → S.Step p s a t → Phase s → Phase t
step-phase pr (after stopping) = after (Shutdown.step-stays pr stopping)
step-phase (S.receiveRequest _) (before _) = before admit
step-phase (S.receiveQuit _) (before _) = after Shutdown.publishing
step-phase (S.choose _ _) (before pre) = before pre
step-phase (S.send _) (before pre) = before pre

-- Scheduling changes the phase only at its corresponding source program point.
tau-phase : ∀ {s t} → S.Tau s t → Phase s → Phase t
tau-phase pr (after stopping) = after (Shutdown.tau-stays pr stopping)
tau-phase S.admitted (before _) = before register
tau-phase S.excessive (before _) = before raising
tau-phase S.registered (before _) = before awaitNext
tau-phase S.setQuit (before ())
tau-phase (S.claim _) (before pre) = before pre
tau-phase (S.retire _) (before pre) = before pre
tau-phase S.flush (before ())
tau-phase S.abort (before _) = before failed

-- Every finite source execution preserves this structural phase invariant.
run-phase : ∀ {p s actions t} → S.Run p s actions t → Phase s → Phase t
run-phase S.stop phase = phase
run-phase (S.internal pr run) phase = run-phase run (tau-phase pr phase)
run-phase (S.visible pr run) phase = run-phase run (step-phase pr phase)

-- The initial source state is in its ordinary pre-Quit phase.
initial-phase : ∀ {p actions t} → S.Run p S.initial actions t → Phase t
initial-phase run = run-phase run (before first)

-- The fault reader phases do not satisfy the successful shutdown control predicate.
before-not-stopping : ∀ {r} → Before r → Control.stopping r ≡ true → ⊥
before-not-stopping first ()
before-not-stopping admit ()
before-not-stopping register ()
before-not-stopping awaitNext ()
before-not-stopping raising ()
before-not-stopping failed ()

-- Reachability plus the shutdown control predicate supplies the exact post-Quit shape.
shutdown-shape : ∀ {s} → Phase s → Control.stopping (S.reader s) ≡ true → Shutdown.Stopping s
shutdown-shape (before pre) stopping = ⊥-elim (before-not-stopping pre stopping)
shutdown-shape (after shape) stopping = shape
