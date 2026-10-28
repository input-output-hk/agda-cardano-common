{-# OPTIONS --safe #-}

-- Source-mapped paired replay for the prototype Notify protocol.
module Cardano_network.Replay.LeiosNotifyPairedReport where
open import Data.Nat using (ℕ)
open import Data.String using (String)
import Cardano_network.Replay.LeiosNotifyPipeline as N
import Cardano_network.Replay.LeiosNotifyPairedSession as Pair
import Cardano_network.Replay.LeiosNotifyParse as Local
import Cardano_network.Replay.PairedReport as Shared

-- Exact retained notification fields are compared across the FIFO channels.
report : ℕ → String → String
report k = Shared.report N.St N.Msg N.msgEq (Pair.next k)
  N.idle N.idle "LeiosNotifyP" "LeiosNotifyP retained message fields" Local.parseEvent Local.showEvent
