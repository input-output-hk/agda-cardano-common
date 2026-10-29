{-# OPTIONS --safe #-}

-- Source-mapped BlockFetch paired replay; range and block payloads are erased.
module Cardano_network.Replay.BlockFetchPairedReport where

open import Data.Nat using (ℕ)
open import Data.String using (String)
import Cardano_network.Replay.BlockFetchClientSession as C
import Cardano_network.Replay.BlockFetchServerSession as S
import Cardano_network.Replay.BlockFetchPairedLocal as Local
import Cardano_network.Replay.BlockFetchReport as Parse
import Cardano_network.Replay.PairedReport as Shared

-- Compare message kinds using the existing client and server control machines.
report : ℕ → String → String
report k = Shared.report (Local.St k) C.Kind C.kindEq (Local.next k)
  (Local.clientS C.initial) (Local.serverS S.idle)
  "BlockFetch" "BlockFetch control only" Parse.parseEvent Parse.showEvent
