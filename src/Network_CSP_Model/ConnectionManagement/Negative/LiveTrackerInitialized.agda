{-# OPTIONS --guardedness #-}

-- Apply full CM-I4c validity to the actual initialized scheduled-close history.
module ConnectionManagement.Negative.LiveTrackerInitialized where
open import ConnectionManagement.Negative.ServerPeers using (module Protocols)
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.GovernorPool as Prior
open import ConnectionManagement.Properties.LiveTrackerInitialized using (module Frontend)
open Protocols using (capability; initializer)
open Protocols.StartTrace.ScopedCM.Completion using (serverFinished; initialized-server-finish)
open Frontend I.bearerClosed Prior.classify capability using (FullValidity; from-initial)

scheduled-full-validity : FullValidity serverFinished
scheduled-full-validity = from-initial _ _ initializer initialized-server-finish
