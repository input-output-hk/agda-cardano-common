{-# OPTIONS --guardedness #-}

-- An actual paired PTree witness for Receive records preceding delayed Send records.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverNativeTests where

open import Data.Bool using (Bool; false; true)
import Data.Bool.Properties as Bool
open import Data.Integer using (+_)
open import Data.List using ([]; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Bool Bool as C
open import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool Bool
import Cardano_network.LeiosNotifyPipeLookahead.DriverExecution Bool Bool Bool._≟_ as X
import Cardano_network.LeiosNotifyPipeLookahead.DriverTree Bool Bool Bool._≟_ as T
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverBridge Bool Bool Bool._≟_ as B
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverTests as Tests
open T.Native S.nodeNext

-- These records participate in one fresh native execution with exact FIFO packets.
delayed-send-records : tree initial Traces.⟹∖√⟨
  map event (serverRecv request ∷ clientRecv (reply (S.normal false)) ∷
    clientSend request ∷ serverSend (reply (S.normal false)) ∷ []) ⟩
  tree (pair
    (C.client C.poll (C.inspect (S.normal false)) [] [] 1 (+ 0) false nothing)
    (S.state S.awaitNext 0 S.sent 0 false)
    [] [] nothing nothing nothing nothing)
delayed-send-records = B.For.complete S.nodeNext Tests.delayed-send-records

-- A Send record requires an earlier successful channel commit.
no-uncommitted-send : X.next S.nodeNext initial (clientSend request) ≡ nothing
no-uncommitted-send = refl

-- A delayed Send cannot be relabeled with a different selected payload.
wrong-pending-payload : X.next S.nodeNext
  (pair C.initial (S.state S.awaitNext 0 (S.selected (S.normal true)) 0 false)
    [] [] nothing (just (reply (S.normal true))) nothing nothing)
  (serverSend (reply (S.normal false))) ≡ nothing
wrong-pending-payload = refl

-- A committed client call cannot commit another packet before its Send record.
no-second-commit : X.hidden S.nodeNext
  (pair C.initial S.initial [] [] (just request) nothing nothing nothing)
  (X.writeClient request) ≡ nothing
no-second-commit = refl

-- Empty transport cannot synthesize a received request, even as hidden work.
no-empty-decode : X.hidden S.nodeNext initial X.readServer ≡ nothing
no-empty-decode = refl
