{-# OPTIONS --safe #-}

-- Local selector regressions cover fixed depth, exact values, failure and races.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeClientExecutionTests where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.Integer using (+_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (_≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model ℕ as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel ℕ ℕ as C
import Cardano_network.LeiosNotifyPipeLookahead.NodeClientModel ℕ ℕ as N
import Cardano_network.LeiosNotifyPipeLookahead.NodeClientExecution ℕ ℕ _≟_ as E
import Cardano_network.LeiosNotifyPipeLookahead.NodeClientExecution ℕ ⊥ _≟_ as EmptyReturn
import Cardano_network.LeiosNotifyPipeLookahead.NodeClientModel ℕ ⊥ as EmptyNode

-- The selectors require no inhabitant of the generic return carrier.
empty-return-menu : EmptyReturn.targets EmptyNode.initial ≡ []
empty-return-menu = refl

-- Zero takes the source's special continue branch with the fixed production depth.
forecast-zero : E.next N.initial N.forecastAllows ≡
  just (N.running (C.client C.issue C.idle [] [] 0 (+ 0) false nothing))
forecast-zero = refl

-- Below depth 1000, forecasting chooses optional collection rather than blocking.
forecast-below : E.next (N.running (C.client C.poll C.idle [] [] 999 (+ 0) false nothing)) N.forecastAllows ≡
  just (N.running (C.client C.collectingMaybe C.idle [] [] 999 (+ 0) false nothing))
forecast-below = refl

-- At depth 1000, an arrival enables the distinct blocking-collection control.
forecast-full : E.next (N.running (C.client C.poll C.idle [] [] 1000 (+ 1) false nothing)) N.forecastAllows ≡
  just (N.running (C.client C.collectingWait C.idle [] [] 1000 (+ 1) false nothing))
forecast-full = refl

-- A full pipe without an arrival cannot borrow the generic arbitrary-depth branch.
forecast-blocked : E.next (N.running (C.client C.poll C.idle [] [] 1000 (+ 0) false nothing)) N.forecastAllows ≡ nothing
forecast-blocked = refl

-- The node's generic return carrier retains the caller's exact successful result.
terminate-value : ∀ value → E.next N.initial (N.stopRequested value) ≡
  just (N.running (C.client C.stopPending C.idle [] [] 0 (+ 0) false (just value)))
terminate-value value = refl

-- A valid generic continue cannot impersonate a captured node wire record.
wire-whitelist : E.next N.initial (N.wire (C.continue (+ 2))) ≡ nothing
wire-whitelist = refl

-- Sending a request retains all unrelated receiver resources and stored values.
request-state : E.next (N.running (C.client C.writingRequest C.awaiting [] [] 3 (+ 2) false (just 73)))
  (N.wire C.sendRequest) ≡
  just (N.running (C.client C.poll C.awaiting [] [] 4 (+ 2) false (just 73)))
request-state = refl

-- Exact reply payloads pass through the node wrapper without changing sender control.
reply-value : ∀ value → E.next (N.running (C.client C.poll C.awaiting [] [] 1 (+ 0) false nothing))
  (N.wire (C.recvReply (S.normal value))) ≡
  just (N.running (C.client C.poll (C.inspect (S.normal value)) [] [] 1 (+ 0) false nothing))
reply-value value = refl

-- The normal handler consumes only the value selected by the receiver.
normal-handler : E.next (N.running (C.client C.poll (C.handling (S.normal 5)) [] [] 1 (+ 0) false nothing))
  (N.handledNormal 5) ≡
  just (N.running (C.client C.poll C.bumpArrival [] [] 1 (+ 0) false nothing))
normal-handler = refl

-- A different normal payload cannot be substituted by the callback action.
wrong-handler : E.next (N.running (C.client C.poll (C.handling (S.normal 5)) [] [] 1 (+ 0) false nothing))
  (N.handledNormal 6) ≡ nothing
wrong-handler = refl

-- Cancel selected for handling remains an abnormal exit with the exact prior control.
cancel-handler : ∀ flag → E.next
  (N.running (C.client C.poll (C.handling S.canceled) [] [] 1 (+ 0) flag nothing))
  N.handlerRejectedCancel ≡
  just (N.unexpectedCancel (C.client C.poll (C.handling S.canceled) [] [] 1 (+ 0) flag nothing))
cancel-handler flag = refl

-- A selected Cancel cannot be reinterpreted as successful normal delivery.
no-normal-cancel : E.next (N.running (C.client C.poll (C.handling S.canceled) [] [] 1 (+ 0) false nothing))
  (N.handledNormal 5) ≡ nothing
no-normal-cancel = refl

-- Inspecting a Cancel after the stop flag is set still uses the inherited discard rule.
draining-cancel : E.targets (N.running (C.client C.draining (C.inspect S.canceled) [] [] 1 (+ 0) true (just 73))) ≡
  (N.running (C.client C.draining C.bumpArrival [] [] 1 (+ 0) true (just 73)) ∷ [])
draining-cancel = refl

-- Main registration and receiver work both remain present without an artificial priority.
concurrent-menu : E.targets
  (N.running (C.client C.issue C.idle (C.responseJob ∷ []) [] 1 (+ 0) false nothing)) ≡
  (N.running (C.client C.writingRequest C.idle (C.responseJob ∷ C.responseJob ∷ []) [] 1 (+ 0) false nothing) ∷
   N.running (C.client C.issue C.awaiting [] [] 1 (+ 0) false nothing) ∷ [])
concurrent-menu = refl

-- Faulted local drivers cannot be resumed by any operation or internal schedule.
failed-dead : ∀ c action → E.next (N.unexpectedCancel c) action ≡ nothing
failed-dead c action = refl

-- No scheduling target leaves an abnormal exit, irrespective of the stored generic state.
failed-empty : ∀ c → E.targets (N.unexpectedCancel c) ≡ []
failed-empty c = refl

-- The source theorem keeps its actual independent forecast rule, not just a computed Boolean.
forecast-certificate : E.next N.initial N.forecastAllows ≡
  just (N.running (C.client C.issue C.idle [] [] 0 (+ 0) false nothing))
forecast-certificate = E.next-complete (N.continueAtDepth C.continueZero)
