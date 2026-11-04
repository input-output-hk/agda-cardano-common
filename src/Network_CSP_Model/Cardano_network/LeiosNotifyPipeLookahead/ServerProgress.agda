{-# OPTIONS --safe #-}

-- Quit removes the server's dependence on a future application next-result.
module Cardano_network.LeiosNotifyPipeLookahead.ServerProgress
  (Notification : Set) where

open import Data.Bool using (true; false)
open import Data.Nat using (zero; suc)
open import Data.Product using (Σ-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import Cardano_network.LeiosNotifyPipeLookahead.Model Notification

-- This phase invariant is established by an actual Quit receive, not by fairness.
data Stopping : State → Set where
  publishing : ∀ {w s c} → Stopping (state signalQuit w s c false)
  flushing : ∀ {w s c} → Stopping (state flushing w s c true)
  ready : Stopping (state doneReady 0 idle 0 true)
  closed : Stopping (state closed 0 idle 0 true)

-- Successful source completion includes the exact drained shape.
data Closed : State → Set where
  closed : Closed (state closed 0 idle 0 true)

-- A constructive progress witness names one real source operation.
data Move (p : Contract) : State → State → Set where
  internal : ∀ {s t} → Tau s t → Move p s t
  visible : ∀ {s a t} → Step p s a t → Move p s t

-- Every legal Quit receive establishes the structural shutdown region.
quit-starts : ∀ {p s t} → Step p s recvQuit t → Stopping t
quit-starts (receiveQuit _) = publishing

-- Visible source operations preserve the region, including a previously selected normal.
step-stays : ∀ {p s a t} → Step p s a t → Stopping s → Stopping t
step-stays (receiveRequest atFirst) ()
step-stays (receiveRequest atNext) ()
step-stays (receiveQuit atFirst) ()
step-stays (receiveQuit atNext) ()
step-stays (choose _ _) publishing = publishing
step-stays (send _) publishing = publishing
step-stays (send _) flushing = flushing
step-stays finish ready = closed

-- The flag transition and every flush/retirement preserve the same region.
tau-stays : ∀ {s t} → Tau s t → Stopping s → Stopping t
tau-stays admitted ()
tau-stays excessive ()
tau-stays registered ()
tau-stays setQuit publishing = flushing
tau-stays (claim _) publishing = publishing
tau-stays (claim _) flushing = flushing
tau-stays (cancel _) flushing = flushing
tau-stays (retire _) publishing = publishing
tau-stays (retire _) flushing = flushing
tau-stays flush flushing = flushing
tau-stays drained flushing = ready
tau-stays abort ()

-- Arbitrary finite continuations of the actual Quit remain in this region.
run-stays : ∀ {p s actions t} → Run p s actions t → Stopping s → Stopping t
run-stays stop stopping = stopping
run-stays (internal pr run) stopping = run-stays run (tau-stays pr stopping)
run-stays (visible pr run) stopping = run-stays run (step-stays pr stopping)

-- After Quit, either completion holds or there is an operation requiring no next callback.
progress : ∀ {p s} → Stopping s → Closed s ⊎ (Σ[ t ∈ State ] Move p s t)
progress publishing = inj₂ (_ , internal setQuit)
progress (flushing {c = suc c}) = inj₂ (_ , internal flush)
progress (flushing {s = claimed} {c = zero}) = inj₂ (_ , internal (cancel refl))
progress (flushing {s = selected m} {c = zero}) = inj₂ (_ , visible (send refl))
progress (flushing {s = sent} {c = zero}) = inj₂ (_ , internal (retire refl))
progress (flushing {w = suc w} {s = idle} {c = zero}) = inj₂ (_ , internal (claim refl))
progress (flushing {w = zero} {s = idle} {c = zero}) = inj₂ (_ , internal drained)
progress ready = inj₂ (_ , visible finish)
progress closed = inj₁ closed
