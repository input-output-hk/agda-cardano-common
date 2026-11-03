{-# OPTIONS --guardedness #-}

-- Native client witnesses for callback erasure, independent receivers and shutdown.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ClientNetworkTests where

open import Data.Nat using (ℕ)
open import Data.Integer using (+_; -[1+_])
open import Data.Bool using (true; false)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing; map)
open import Data.Product using (_,_; proj₁)
open import Data.Unit using (tt)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees using (PTree; ret)
open import Cardano_network.Base using (hi; FromInitiator; FromResponder)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.Data exactParams
open import Cardano_network.LeiosNotifyP exactParams using (apiLPev; receiveLNP)
open import Cardano_network.Net exactParams using (lnpSendRequestNext; lnpRecvBlockOffer)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification ℕ as C
import Cardano_network.LeiosNotifyPipeLookahead.ClientNetwork exactParams ℕ as N
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ClientNetworkBridge exactParams ℕ as Bridge
module B = Bridge.At fzero hi
open N.At fzero hi
open N using (module LTS; module Traces)

-- This nontrivial native payload retains hash, slot and size through the receiver.
sample : Notification
sample = offer (43 , 47) 53

-- A registered receiver can complete before the request's delayed Send record.
reply-before-send-source : C.Run C.initial
  (C.continue (+ 1) ∷ C.recvReply (S.normal sample) ∷ C.handled (S.normal sample) ∷ C.sendRequest ∷ [])
  (C.client C.poll C.idle [] (C.responseToken ∷ []) 1 (+ 1) false nothing)
reply-before-send-source =
  C.visible C.continueZero $
  C.internal C.registerResponse $
  C.internal (C.startResponse refl) $
  C.visible (C.receivedReply refl) $
  C.internal (C.keepReply refl) $
  C.visible (C.delivered refl) $
  C.internal (C.countArrival refl) $
  C.internal (C.publishResponse refl) $
  C.visible C.sentRequest C.stop

-- The exact source schedule is a real native network/API trace with checkDone erased.
reply-before-send-native : tree C.initial Traces.⟹∖√⟨
  project (C.continue (+ 1) ∷ C.recvReply (S.normal sample) ∷ C.handled (S.normal sample) ∷ C.sendRequest ∷ []) ⟩
  tree (C.client C.poll C.idle [] (C.responseToken ∷ []) 1 (+ 1) false nothing)
reply-before-send-native = B.realize reply-before-send-source

-- A handler that observed the false stop flag can finish after Quit is logged.
handler-after-quit-source : C.Run C.initial
  (C.continue (+ 1) ∷ C.sendRequest ∷ C.recvReply (S.normal sample) ∷ C.terminate 73 ∷
    C.sendQuit ∷ C.handled (S.normal sample) ∷ C.recvDone ∷ [])
  (C.client C.closed C.idle [] [] 0 (+ 1) true (just 73))
handler-after-quit-source =
  C.visible C.continueZero $
  C.internal C.registerResponse $
  C.internal (C.startResponse refl) $
  C.visible C.sentRequest $
  C.visible (C.receivedReply refl) $
  C.internal (C.keepReply refl) $
  C.visible C.stopRequested $
  C.internal C.setStopBusy $
  C.internal C.registerMarker $
  C.visible C.sentQuitBusy $
  C.visible (C.delivered refl) $
  C.internal (C.countArrival refl) $
  C.internal (C.publishResponse refl) $
  C.internal (C.startMarker refl) $
  C.internal (C.publishMarker refl) $
  C.internal C.drainResult $
  C.internal C.drainResult $
  C.internal C.drained $
  C.visible C.receivedDone C.stop

-- Native shutdown preserves that delivery and returns the exact chosen value.
handler-after-quit-native : tree C.initial Traces.⟹∖√⟨
  project (C.continue (+ 1) ∷ C.sendRequest ∷ C.recvReply (S.normal sample) ∷ C.terminate 73 ∷
    C.sendQuit ∷ C.handled (S.normal sample) ∷ C.recvDone ∷ []) ⟩
  tree (C.client C.closed C.idle [] [] 0 (+ 1) true (just 73))
handler-after-quit-native = B.realize handler-after-quit-source

-- The native return keeps 73 and permits the source's residual arrived value of one.
return-value-retained : PTree.force (tree (C.client C.closed C.idle [] [] 0 (+ 1) true (just 73))) ≡ ret 73
return-value-retained = refl

-- Cancellation during draining skips the application callback and still completes the pipe.
canceled-drain-source : C.Run C.initial
  (C.continue (+ 1) ∷ C.sendRequest ∷ C.terminate 73 ∷ C.sendQuit ∷ C.recvReply S.canceled ∷ C.recvDone ∷ [])
  (C.client C.closed C.idle [] [] 0 (+ 1) true (just 73))
canceled-drain-source =
  C.visible C.continueZero $
  C.internal C.registerResponse $
  C.internal (C.startResponse refl) $
  C.visible C.sentRequest $
  C.visible C.stopRequested $
  C.internal C.setStopBusy $
  C.internal C.registerMarker $
  C.visible C.sentQuitBusy $
  C.visible (C.receivedReply refl) $
  C.internal (C.discardReply refl) $
  C.internal (C.countArrival refl) $
  C.internal (C.publishResponse refl) $
  C.internal (C.startMarker refl) $
  C.internal (C.publishMarker refl) $
  C.internal C.drainResult $
  C.internal C.drainResult $
  C.internal C.drained $
  C.visible C.receivedDone C.stop

-- Canceled remains a visible wire record even though callback decisions are hidden.
canceled-drain-native : tree C.initial Traces.⟹∖√⟨
  project (C.continue (+ 1) ∷ C.sendRequest ∷ C.terminate 73 ∷ C.sendQuit ∷ C.recvReply S.canceled ∷ C.recvDone ∷ []) ⟩
  tree (C.client C.closed C.idle [] [] 0 (+ 1) true (just 73))
canceled-drain-native = B.realize canceled-drain-source

-- The source Zero branch still permits a first request at a negative callback bound.
negative-bound-first : map proj₁ (N.hidden C.initial (N.callbackValue (C.continue (-[1+ 0 ])))) ≡
  just (C.client C.issue C.idle [] [] 0 (+ 0) false nothing)
negative-bound-first = refl

-- At a full pipeline, continue cannot bypass arrived's positive guard.
full-without-arrival : N.hidden
  (C.client C.poll C.awaiting [] [] 1 (+ 0) false nothing) (N.callbackValue (C.continue (+ 1))) ≡ nothing
full-without-arrival = refl

-- Termination remains possible in that same full state and stores its exact value.
terminate-at-full : map proj₁ (N.hidden
  (C.client C.poll C.awaiting [] [] 1 (+ 0) false nothing) (N.callbackValue (C.terminate 73))) ≡
  just (C.client C.stopPending C.awaiting [] [] 1 (+ 0) false (just 73))
terminate-at-full = refl

-- A wire Send can never be substituted for an internal callback operation.
no-hidden-send : N.hidden (C.client C.writingRequest C.idle [] [] 0 (+ 0) false nothing)
  (N.callbackValue C.sendRequest) ≡ nothing
no-hidden-send = refl

-- A normal delivery likewise remains an observable API event rather than a silent callback.
no-hidden-normal-delivery : N.hidden
  (C.client C.poll (C.handling (S.normal sample)) [] [] 1 (+ 0) false nothing)
  (N.callbackValue (C.handled (S.normal sample))) ≡ nothing
no-hidden-normal-delivery = refl

-- The old unit API cannot impersonate the dynamic-depth and return-valued checkDone callback.
no-unit-checkDone-api : decode (LTS.evLabel _ (apiLPev fzero hi lnpSendRequestNext) tt) ≡ nothing
no-unit-checkDone-api = refl

-- A normal API handoff cannot change the payload received by the selected handler.
wrong-delivery-payload : next
  (C.client C.poll (C.handling (S.normal sample)) [] [] 1 (+ 0) false nothing)
  (LTS.evLabel _ (apiLPev fzero hi lnpRecvBlockOffer) ((43 , 48) , 53)) ≡ nothing
wrong-delivery-payload = refl

-- Done cannot be received until the source client reaches its final await phase.
no-early-done : next C.initial
  (LTS.evLabel _ (receiveLNP fzero hi)
    (tt , FromResponder , tt , leiosNotifyP MsgLNPDone)) ≡ nothing
no-early-done = refl
