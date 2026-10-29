{-# OPTIONS --guardedness #-}

-- Protocol-specific instance of the protocol-independent composition proofs.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.BlockFetchPairedParts (p : Params) where
open import Process_Trees using (ExtI)
open import Cardano_network.Data p using (Payload)
open import Cardano_network.BlockFetch p using (BFEv; Rr)
open import Cardano_network.Replay.BlockFetchPairedModel p using (packetEq; flow)
open import CSP.AsyncPair.Parts BFEv (ExtI BFEv) Rr Payload packetEq flow public
