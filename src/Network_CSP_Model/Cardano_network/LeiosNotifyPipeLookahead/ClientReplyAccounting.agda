{-# OPTIONS --safe #-}

-- Reply obligations exclude the Quit marker and already received unpublished results.
module Cardano_network.LeiosNotifyPipeLookahead.ClientReplyAccounting
  (Notification Return : Set) where

open import Data.List using (List; []; _∷_; _∷ʳ_)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Nat.Properties using (+-suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return

-- Only response jobs await a wire reply; the dummy Quit receiver consumes no packet.
responses : List Job → ℕ
responses [] = 0
responses (responseJob ∷ js) = suc (responses js)
responses (quitMarker ∷ js) = responses js

-- A claimed response remains owed until its Receive record, before handling/publication.
awaitingReply : Receiver → ℕ
awaitingReply awaiting = 1
awaitingReply _ = 0

-- Registration-before-Send correction counts requests only, never the Quit marker.
registeredRequest : Main → ℕ
registeredRequest writingRequest = 1
registeredRequest _ = 0

-- These are the client resources that still require an actual reply Receive.
owed : State → ℕ
owed c = responses (jobs c) + awaitingReply (receiver c)

-- Two historical counts retain the exact number of request Sends and reply Receives.
record Counts : Set where
  constructor counts
  field
    requests replies : ℕ
open Counts public

-- Source callbacks, Quit and Done contribute no request/reply count.
advance : Action → Counts → Counts
advance sendRequest (counts req rep) = counts (suc req) rep
advance (recvReply _) (counts req rep) = counts req (suc rep)
advance _ past = past

-- This equation relates wire observations to the exact outstanding response jobs.
Balanced : Counts → State → Set
Balanced (counts req rep) c = req + registeredRequest (main c) ≡ rep + owed c

-- FIFO append adds one reply obligation precisely when the appended job is a response.
snoc-response : ∀ js → responses (js ∷ʳ responseJob) ≡ suc (responses js)
snoc-response [] = refl
snoc-response (responseJob ∷ js) = cong suc (snoc-response js)
snoc-response (quitMarker ∷ js) = snoc-response js

-- Appending the Quit marker adds receiver work but no reply obligation.
snoc-marker : ∀ js → responses (js ∷ʳ quitMarker) ≡ responses js
snoc-marker [] = refl
snoc-marker (responseJob ∷ js) = cong suc (snoc-marker js)
snoc-marker (quitMarker ∷ js) = snoc-marker js

-- Registration adds matching units on the correction and obligation sides.
register : ∀ req rep js r → req + 0 ≡ rep + (responses js + awaitingReply r) →
  req + 1 ≡ rep + (suc (responses js) + awaitingReply r)
register req rep js r accounted = trans (+-suc req 0)
  (trans (cong suc accounted) (sym (+-suc rep (responses js + awaitingReply r))))

-- Wire records transfer one registration or one pending reply into history.
step-balanced : ∀ {s a t past} (pr : Step s a t) → Balanced past s → Balanced (advance a past) t
step-balanced continueZero accounted = accounted
step-balanced (continueBelow _) accounted = accounted
step-balanced (continueFull _ _) accounted = accounted
step-balanced stopRequested accounted = accounted
step-balanced sentQuitIdle accounted = accounted
step-balanced sentQuitBusy accounted = accounted
step-balanced {past = counts req rep} sentRequest accounted = trans (sym (+-suc req 0)) accounted
step-balanced {past = counts req rep} (receivedReply {js = js} _) accounted =
  trans accounted (trans (cong (rep +_) (+-suc (responses js) 0)) (+-suc rep (responses js + 0)))
step-balanced (delivered _) accounted = accounted
step-balanced receivedDone accounted = accounted

-- Internal receiver/result/marker work preserves the reply equation at every phase.
tau-balanced : ∀ {s t past} → Tau s t → Balanced past s → Balanced past t
tau-balanced {past = counts req rep} (registerResponse {r = r} {js = js}) accounted
  rewrite snoc-response js = register req rep js r accounted
tau-balanced setStopIdle accounted = accounted
tau-balanced setStopBusy accounted = accounted
tau-balanced (registerMarker {js = js}) accounted rewrite snoc-marker js = accounted
tau-balanced optionalEmpty accounted = accounted
tau-balanced optionalResult accounted = accounted
tau-balanced blockingResult accounted = accounted
tau-balanced adjustArrival accounted = accounted
tau-balanced drainResult accounted = accounted
tau-balanced drained accounted = accounted
tau-balanced {past = counts req rep} (startResponse {js = js} _) accounted =
  trans accounted (cong (rep +_) (sym (+-suc (responses js) 0)))
tau-balanced (startMarker _) accounted = accounted
tau-balanced (keepReply _) accounted = accounted
tau-balanced (discardReply _) accounted = accounted
tau-balanced (countArrival _) accounted = accounted
tau-balanced (publishResponse _) accounted = accounted
tau-balanced (publishMarker _) accounted = accounted

-- Fold source observations in their original order, without treating callbacks as packets.
observe : List Action → Counts → Counts
observe [] past = past
observe (a ∷ actions) past = observe actions (advance a past)

-- Every finite source run preserves the equation from any balanced initial history.
run-balanced : ∀ {s actions t past} → Run s actions t → Balanced past s → Balanced (observe actions past) t
run-balanced stop accounted = accounted
run-balanced {past = past} (internal pr run) accounted = run-balanced run (tau-balanced {past = past} pr accounted)
run-balanced {past = past} (visible pr run) accounted = run-balanced run (step-balanced {past = past} pr accounted)

-- Fresh clients invent neither requests nor replies before their first operation.
initial-balanced : ∀ {actions t} → Run initial actions t → Balanced (observe actions (counts 0 0)) t
initial-balanced run = run-balanced run refl
