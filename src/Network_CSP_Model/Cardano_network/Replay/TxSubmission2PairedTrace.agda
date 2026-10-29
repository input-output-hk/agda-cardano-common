{-# OPTIONS --guardedness #-}

-- Protocol-specific instance of the protocol-independent composition proofs.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.TxSubmission2PairedTrace (p : Params) where
open import Process_Trees using (ExtI)
open import Cardano_network.Data p using (Payload)
open import Cardano_network.TxSubmission p using (TSEv; Rr)
open import Cardano_network.Replay.TxSubmission2PairedModel p using (packetEq; flow)
open import CSP.AsyncPair.Trace TSEv (ExtI TSEv) Rr Payload packetEq flow public
