{-# OPTIONS --safe #-}

-- Paired prototype Fetch reports retain every parsed message field.
module Cardano_network.Replay.LeiosFetchPairedReport where
open import Data.Nat using (ℕ)
open import Data.String using (String)
import Cardano_network.Replay.LeiosFetchSession as F
import Cardano_network.Replay.LeiosFetchPairedLocal as Wire
import Cardano_network.Replay.LeiosFetchParse as Local
import Cardano_network.Replay.PairedReport as Shared

-- Only the client uses k; the responder remains sequential.
report : ℕ → String → String
report k = Shared.report F.St F.Msg F._≟M_ (Wire.next k)
  F.client₀ F.server₀ "LeiosFetchP" "LeiosFetchP retained message fields" Local.parseEvent Local.showEvent
