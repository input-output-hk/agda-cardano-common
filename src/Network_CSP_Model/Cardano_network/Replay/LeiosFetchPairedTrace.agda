{-# OPTIONS --guardedness #-}

-- Protocol instance of the generic exact-packet finite-trace correspondence.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosFetchPairedTrace (p : Params) where
open import Process_Trees using (ExtI)
open import Cardano_network.Data p using (Payload)
open import Cardano_network.LeiosFetchP p using (LFPEv; Rr)
open import Cardano_network.Replay.LeiosFetchPairedModel p using (packetEq; flow)
open import CSP.AsyncPair.Trace LFPEv (ExtI LFPEv) Rr Payload packetEq flow public
