{-# OPTIONS --guardedness #-}

-- Apply the joint frontend certificate to the existing initialized close run.
module ConnectionManagement.Negative.LiveTrackerAuxFrontend where
open import ConnectionManagement.Negative.ServerPeers using (module Protocols)
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.GovernorPool as Prior
open import ConnectionManagement.Properties.LiveTrackerAuxFrontend using (module Frontend)
open Protocols using (capability; initializer)
open Protocols.StartTrace.ScopedCM.Completion using (serverFinished; initialized-server-finish)
open Frontend I.bearerClosed Prior.classify capability using (Valid; from-initial; calls-from-initial)

scheduled-core-pcs-calls : Valid serverFinished
scheduled-core-pcs-calls = from-initial _ _ initializer initialized-server-finish
