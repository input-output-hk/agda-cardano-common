{-# OPTIONS --guardedness #-}

-- Explicit local node-control reports retain the shared status and input-line conventions.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeClientReport where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (suc)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String using (String; _++_; lines)
open import Cardano_network.Replay.LeiosFetchParse using (parseRole)
import Cardano_network.Replay.LeiosNotifySession as Log
import Cardano_network.Replay.LeiosNotifyParse as Parse
import Cardano_network.Replay.LeiosNotifyPipeLookahead.LookaheadReport as Base
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.NodeClientAdapter as Client
open Base public using (Status; acceptedPrefix; protocolRejected; invalidInput;
  Result; result; status; detail; render)

-- External decision witnesses and EOF do not certify forecast truth or a fault-free close.
profile : String
profile = "observation=driver-log; client=node-client-control; depth=1000; return=unit; forecast/stop=external-witnesses\ninitial=fresh (asserted); eof=prefix (pending handler/fault permitted); fields=normalized summaries; scope=local-client-control"

-- Failed parsing remains in the row list and keeps the original normalized line offset.
localRows : List (Maybe Log.E) → Result
localRows input with Client.check Log.client input
... | Client.invalidInput failure _ = result invalidInput
  (profile ++ "\ninput line " ++ showℕ (suc (suc (Client.position failure))) ++ ": " ++ Base.clientReason (Client.reason failure))
... | Client.protocolRejected _ _ _ _ = result protocolRejected
  (profile ++ "\nno compatible local node-client prefix (" ++ showℕ (length input) ++ " events)")
... | Client.accepted _ = result acceptedPrefix
  (profile ++ "\nlocal node-client prefix (" ++ showℕ (length input) ++ " events)")

-- The same role-header validation fixes the endpoint before any policy search is attempted.
local : String → Result
local text with lines text
... | [] = result invalidInput (profile ++ "\ninput line 1: missing role header")
... | header ∷ rest with parseRole header
...   | nothing = result invalidInput (profile ++ "\ninput line 1: expected role client or role server")
...   | just actual with Base.sameRole Log.client actual
...     | false = result invalidInput (profile ++ "\ninput line 1: role differs from declared client")
...     | true = localRows (map Parse.parseEvent rest)
