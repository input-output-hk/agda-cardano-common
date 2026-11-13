{-# OPTIONS --guardedness #-}

-- Operational correspondence for the client/FIFO/store-backed-server product.
-- Server legality accepts the exact decoded-bitmap observation under explicit wire checks.
module Cardano_network.Replay.LeiosFetchPairedStoreTrace where
open import Process_Trees using (ExtI)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Data replayParams using (Payload)
open import Cardano_network.Net replayParams using (Net_Api)
open import Cardano_network.LeiosFetchP replayParams using (Rr)
open import Cardano_network.Replay.LeiosFetchPairedStoreModel using (packetEq; flow; PairEv; PairI)
open import CSP.AsyncPair.Trace (Net_Api Payload) (ExtI (Net_Api Payload)) Rr Payload packetEq flow public

open import Data.Nat using (ℕ)
open import Data.List using (List)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Cardano_network.Net replayParams using (Link)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Replay.LeiosFetchPairedStoreModel using (system; pipelinedClient; empty)
open import Cardano_network.Replay.LeiosFetchServerModel using (Bodies; serverModel)
import Cardano_network.Replay.LeiosFetchServerSound as Server
import Cardano_network.Replay.LeiosFetchSession as F
import Semantics.Replay as Replay
open import Cardano_network.Replay.LeiosFetchWireOK using (WireOK)
open import Cardano_network.Replay.LeiosFetchObs using (ObsS)
import Semantics.LTS {E = PairEv} {I = PairI} as Pair
import Semantics.Deadlock {E = PairEv} {I = PairI} as PairTrace
open import Data.Unit using (⊤)
open import Process_Trees using (PTree)

-- Projected server runs accept every exact decoded-bitmap observation satisfying WireOK.
server-legal : ∀ (k : ℕ) (l : Link) (d : Dir) (bs : Bodies)
  {events : List Pair.Event} {end : PTree PairEv PairI ⊤} {es} →
  system k l d bs PairTrace.⟹∖√⟨ events ⟩ end →
  ObsS (projectServer events) es → WireOK es →
  Replay.Traces.HasTrace (F.Spec.leiosFetch k) F.server₀ es
server-legal k l d bs run obs wire with sound {start = state (pipelinedClient k l d) (serverModel bs) empty} run
... | residual , components , _ = Server.server-sound k bs (server-projection components) obs wire
