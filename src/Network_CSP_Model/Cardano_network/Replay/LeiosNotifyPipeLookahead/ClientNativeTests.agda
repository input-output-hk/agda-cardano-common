{-# OPTIONS --guardedness #-}

-- Inhabited PTree executions and executable negative controls for the client bridge.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ClientNativeTests where

open import Data.Bool using (Bool; true; false)
import Data.Bool.Properties as Bool
open import Data.Integer using (+_)
open import Data.List using ([]; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Process_Trees using (PTree; ret)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.LeiosNotifyPipeLookahead.Model Bool using (normal)
open import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Bool Bool
import Cardano_network.LeiosNotifyPipeLookahead.ClientTree Bool Bool Bool._≟_ as T
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ClientBridge Bool Bool Bool._≟_ as B
import Cardano_network.LeiosNotifyPipeLookahead.ClientExecution Bool Bool Bool._≟_ as X
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ClientTests as Tests
open T.Native

-- Receiver work can complete before the main thread emits its request Send record.
reply-before-send : tree initial Traces.⟹∖√⟨
  map event (continue (+ 1) ∷ recvReply (normal true) ∷ handled (normal true) ∷ sendRequest ∷ []) ⟩
  tree (client poll idle [] (responseToken ∷ []) 1 (+ 1) false nothing)
reply-before-send = B.complete Tests.reply-before-send-record

-- A handler selected before shutdown can finish after the actual Quit record.
handler-after-quit : tree initial Traces.⟹∖√⟨
  map event (continue (+ 1) ∷ sendRequest ∷ recvReply (normal true) ∷
    terminate true ∷ sendQuit ∷ handled (normal true) ∷ recvDone ∷ []) ⟩
  tree (client closed idle [] [] 0 (+ 1) true (just true))
handler-after-quit = B.complete Tests.handler-finishes-after-quit

-- Successful native shutdown returns the exact checkDone result despite residual arrived.
closed-result : PTree.force (tree (client closed idle [] [] 0 (+ 1) true (just false))) ≡ ret false
closed-result = refl

-- A pending handler cannot successfully deliver a different reply payload.
wrong-handler-payload : X.next
  (client poll (handling (normal true)) [] [] 1 (+ 0) false nothing)
  (handled (normal false)) ≡ nothing
wrong-handler-payload = refl

-- The fresh state cannot accept Done before termination was requested and drained.
no-early-done : X.next initial recvDone ≡ nothing
no-early-done = refl
