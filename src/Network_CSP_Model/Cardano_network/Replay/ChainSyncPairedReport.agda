{-# OPTIONS --safe #-}

-- Preserve the ChainSync CLI using the common source-mapped paired reporter.
module Cardano_network.Replay.ChainSyncPairedReport where
open import Data.Nat using (ℕ)
open import Data.String using (String)
import Cardano_network.Replay.ChainSyncSession as CS
import Cardano_network.Replay.ChainSyncParse as Local
import Cardano_network.Replay.PairedReport as Shared

-- The control-only ChainSync observation remains unchanged.
report : ℕ → String → String
report k = Shared.report CS.St CS.Kind CS.kindEq (CS.next k)
  CS.initial CS.initial "ChainSync" "ChainSync control only" Local.parseEvent Local.showEvent
