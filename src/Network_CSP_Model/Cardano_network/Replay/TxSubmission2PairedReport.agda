{-# OPTIONS --safe #-}

-- Source-mapped TxSubmission2 pairs retain blocking and ID-reply emptiness.
module Cardano_network.Replay.TxSubmission2PairedReport where

open import Data.Nat using (ℕ)
open import Data.String using (String)
import Cardano_network.Replay.TxSubmission2Session as T
import Cardano_network.Replay.TxSubmission2Parse as Parse
import Cardano_network.Replay.PairedReport as Shared

-- The capacity bounds the server/requester; the client/submitter is sequential.
report : ℕ → String → String
report k = Shared.report T.St T.Kind T.kindEq (T.next k)
  T.initial T.initial "TxSubmission2" "TxSubmission2 control, blocking and ID-reply emptiness"
  Parse.parseEvent Parse.showEvent
