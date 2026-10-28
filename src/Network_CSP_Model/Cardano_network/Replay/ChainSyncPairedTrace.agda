{-# OPTIONS --guardedness #-}

-- Existing ChainSync API backed by the protocol-independent composition proofs.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.ChainSyncPairedTrace (p : Params) where
open import Process_Trees using (ExtI)
open import Cardano_network.Data p using (Payload)
open import Cardano_network.ChainSync p using (CSEv; Rr)
open import Cardano_network.Replay.ChainSyncPairedModel p using (packetEq; flow)
open import CSP.AsyncPair.Trace CSEv (ExtI CSEv) Rr Payload packetEq flow public
