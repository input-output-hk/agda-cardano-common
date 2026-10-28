{-# OPTIONS --safe #-}

-- ChainSync instance of the common fresh-pair input grammar.
module Cardano_network.Replay.ChainSyncPairedParse where
import Cardano_network.Replay.ChainSyncSession as CS
import Cardano_network.Replay.ChainSyncParse as Local
open import Cardano_network.Replay.PairedParse CS.E "ChainSync" Local.parseEvent public
