{-# OPTIONS --guardedness #-}

-- Protocol instance of the generic exact-packet step correspondence.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosNotifyPairedParts (p : Params) where
open import Process_Trees using (ExtI)
open import Cardano_network.Data p using (Payload)
open import Cardano_network.LeiosNotifyP p using (LNPEv; Rr)
open import Cardano_network.Replay.LeiosNotifyPairedModel p using (packetEq; flow)
open import CSP.AsyncPair.Parts LNPEv (ExtI LNPEv) Rr Payload packetEq flow public
