{-# OPTIONS --safe #-}

-- Pinned node client policy around the generic pipelined client control model.
-- A permitted forecast, successful normal handler and requested stop are inputs.
module Cardano_network.LeiosNotifyPipeLookahead.NodeClientModel
  (Notification Return : Set) where

open import Data.Bool using (true)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C

-- Unexpected cancellation is an abnormal driver exit, distinct from wire Done.
data State : Set where
  running unexpectedCancel : C.State → State

-- The source installs the same empty client state before consulting its forecast.
initial : State
initial = running C.initial

-- Wire records cannot impersonate application decisions or successful handlers.
data Wire : C.Action → Set where
  request : Wire C.sendRequest
  quit : Wire C.sendQuit
  reply : ∀ {m} → Wire (C.recvReply m)
  done : Wire C.recvDone

-- Forecast readiness and callback success remain explicit external contracts.
data Action : Set where
  wire : C.Action → Action
  forecastAllows : Action
  stopRequested : Return → Action
  handledNormal : Notification → Action
  handlerRejectedCancel : Action

-- The production depth is fixed at 1000; an undrained Canceled handler throws.
data Step : State → Action → State → Set where
  wireRecord : ∀ {c c′ a} → Wire a → C.Step c a c′ →
    Step (running c) (wire a) (running c′)
  continueAtDepth : ∀ {c c′} → C.Step c (C.continue (+ 1000)) c′ →
    Step (running c) forecastAllows (running c′)
  terminate : ∀ {c c′ x} → C.Step c (C.terminate x) c′ →
    Step (running c) (stopRequested x) (running c′)
  handled : ∀ {c c′ m} → C.Step c (C.handled (S.normal m)) c′ →
    Step (running c) (handledNormal m) (running c′)
  rejectedCancel : ∀ {c} → C.active (C.main c) ≡ true →
    C.receiver c ≡ C.handling S.canceled →
    Step (running c) handlerRejectedCancel (unexpectedCancel c)

-- Generic internal transitions retain the flag-read/handler race without repairing it.
data Tau : State → State → Set where
  schedule : ∀ {c c′} → C.Tau c c′ → Tau (running c) (running c′)

-- Fault states have no continuation; successful termination still needs wire Done.
data Run : State → List Action → State → Set where
  stop : ∀ {s} → Run s [] s
  internal : ∀ {s t u es} → Tau s t → Run t es u → Run s es u
  visible : ∀ {s t u a es} → Step s a t → Run t es u → Run s (a ∷ es) u
