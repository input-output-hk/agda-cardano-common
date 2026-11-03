{-# OPTIONS --safe #-}

-- Source-schedule witnesses and negative controls for the new pipelined client.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ClientTests where

open import Data.Bool using (Bool; false; true)
open import Data.Integer using (ℤ; +_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing; just)
open import Data.Empty using (⊥)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.LeiosNotifyPipeLookahead.Model Bool using (normal)
open import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Bool Bool

-- A receiver is registered before the request Send record is emitted.
reply-before-send-record : Run initial
  (continue (+ 1) ∷ recvReply (normal true) ∷ handled (normal true) ∷ sendRequest ∷ [])
  (client poll idle [] (responseToken ∷ []) 1 (+ 1) false nothing)
reply-before-send-record =
  visible continueZero $
  internal registerResponse $
  internal (startResponse refl) $
  visible (receivedReply refl) $
  internal (keepReply refl) $
  visible (delivered refl) $
  internal (countArrival refl) $
  internal (publishResponse refl) $
  visible sentRequest stop

-- Termination can win at a full pipeline even when no result has arrived.
terminate-at-full : Step
  (client poll awaiting [] [] 1 (+ 0) false nothing) (terminate true)
  (client stopPending awaiting [] [] 1 (+ 0) false (just true))
terminate-at-full = stopRequested

-- Continuing at that same full state cannot bypass the STM arrived guard.
full-without-arrival : ∀ {t} → Step
  (client poll awaiting [] [] 1 (+ 0) false nothing) (continue (+ 1)) t → ⊥
full-without-arrival (continueBelow ())
full-without-arrival (continueFull _ ())

-- A positive arrived count does not mean the driver has published a result yet.
arrived-before-publication : Step
  (client poll (publish false) [] [] 1 (+ 1) false nothing) (continue (+ 1))
  (client collectingWait (publish false) [] [] 1 (+ 1) false nothing)
arrived-before-publication = continueFull refl refl

-- The independent receiver then publishes the token needed by the blocking collect.
publish-then-collect : Run
  (client collectingWait (publish false) [] [] 1 (+ 1) false nothing) []
  (client poll idle [] [] 0 (+ 0) false nothing)
publish-then-collect =
  internal (publishResponse refl) $
  internal blockingResult $
  internal adjustArrival stop

-- The Zero branch issues its first request even when the supplied bound is zero.
zero-bound-first-request : Step initial (continue (+ 0))
  (client issue idle [] [] 0 (+ 0) false nothing)
zero-bound-first-request = continueZero

-- Normal collection subtracts arrived, while drainThePipe deliberately does not.
drain-keeps-arrived : Run
  (client poll idle [] (responseToken ∷ []) 1 (+ 1) false nothing)
  (terminate true ∷ sendQuit ∷ recvDone ∷ [])
  (client closed idle [] [] 0 (+ 1) true (just true))
drain-keeps-arrived =
  visible stopRequested $
  internal setStopBusy $
  internal registerMarker $
  internal (startMarker refl) $
  internal (publishMarker refl) $
  visible sentQuitBusy $
  internal drainResult $
  internal drainResult $
  internal drained $
  visible receivedDone stop

-- A handler already selected by a false flag may finish after the Quit record.
handler-finishes-after-quit : Run initial
  (continue (+ 1) ∷ sendRequest ∷ recvReply (normal true) ∷
   terminate true ∷ sendQuit ∷ handled (normal true) ∷ recvDone ∷ [])
  (client closed idle [] [] 0 (+ 1) true (just true))
handler-finishes-after-quit =
  visible continueZero $
  internal registerResponse $
  internal (startResponse refl) $
  visible sentRequest $
  visible (receivedReply refl) $
  internal (keepReply refl) $
  visible stopRequested $
  internal setStopBusy $
  internal registerMarker $
  visible sentQuitBusy $
  visible (delivered refl) $
  internal (countArrival refl) $
  internal (publishResponse refl) $
  internal (startMarker refl) $
  internal (publishMarker refl) $
  internal drainResult $
  internal drainResult $
  internal drained $
  visible receivedDone stop

-- If the receiver sees the true flag instead, it skips the application handler.
discard-during-drain : Run
  (client draining awaiting (quitMarker ∷ []) [] 2 (+ 0) true (just true))
  (recvReply (normal true) ∷ recvDone ∷ [])
  (client closed idle [] [] 0 (+ 1) true (just true))
discard-during-drain =
  visible (receivedReply refl) $
  internal (discardReply refl) $
  internal (countArrival refl) $
  internal (publishResponse refl) $
  internal (startMarker refl) $
  internal (publishMarker refl) $
  internal drainResult $
  internal drainResult $
  internal drained $
  visible receivedDone stop

-- Successful Done returns the exact value selected by checkDone's Left branch.
return-value-retained : ∀ {r js rs a x t} →
  Step (client awaitDone r js rs 0 a true (just x)) recvDone t →
  returnValue t ≡ just x
return-value-retained receivedDone = refl
