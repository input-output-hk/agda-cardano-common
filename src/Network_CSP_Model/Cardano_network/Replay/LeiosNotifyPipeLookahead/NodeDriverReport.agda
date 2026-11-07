{-# OPTIONS --guardedness #-}

-- Explicit full node-policy reports share the existing paired syntax and status classes.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverReport where

open import Data.List using (map; length)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product using (_,_; proj₂)
open import Data.String using (String; _++_)
open import Data.Sum using (inj₁; inj₂)
import Cardano_network.Replay.LeiosNotifySession as Log
import Cardano_network.Replay.LeiosNotifyPipeLookahead.LookaheadReport as Base
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.NodePairedAdapter as Paired
open Base public using (Status; acceptedPrefix; protocolRejected; invalidInput;
  Result; result; status; detail; render)

-- The report states the modeled policy and the remaining external-input and capture obligations.
profile : String
profile = "observation=driver-log; node-policy=full-node; depth=1000; return=unit; server-contract=node-next; queue=credit-fifo\ninitial=fresh (asserted); eof=prefix; fields=normalized summaries; inputs=existential forecast/governor/eligibility/handler witnesses; scope=paired-full-node-policy"

-- Source coordinates and per-endpoint order are reused from the existing validated paired capture.
pairedInput : Base.PairFile.Input → Result
pairedInput capture with Paired.check-normalized Log.client
  (map proj₂ (Base.PairFile.clientRows capture)) Log.server
  (map proj₂ (Base.PairFile.serverRows capture))
... | Paired.invalidInput failure _ = result invalidInput
  (profile ++ "\n" ++ Base.pairContext capture ++ "\n" ++ Base.pairFailure capture failure)
... | Paired.protocolRejected _ _ _ _ _ = result protocolRejected
  (profile ++ "\n" ++ Base.pairContext capture ++ "\nno compatible full node-policy execution for the supplied endpoint prefixes")
... | Paired.accepted _ = result acceptedPrefix
  (profile ++ "\n" ++ Base.pairContext capture ++ "\nfull node-policy paired prefixes (client " ++
    showℕ (length (Base.PairFile.clientRows capture)) ++ ", server " ++
    showℕ (length (Base.PairFile.serverRows capture)) ++ " events)")

-- Parser failure remains an input error rather than a counterexample to the source policy.
paired : String → Result
paired text with Base.PairFile.parseFile text
... | inj₁ (line , message) = result invalidInput (profile ++ "\npaired input line " ++ showℕ line ++ ": " ++ message)
... | inj₂ capture = pairedInput capture
