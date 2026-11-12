{-# OPTIONS --guardedness #-}

-- Apply the initialized reference certificate to the same completed inner run
-- used by IGPendingQuiet's scheduled close. The run contains a real handler
-- birth, negotiated mux, cleanup and physical result, not an empty registry.
module ConnectionManagement.Negative.LiveTrackerReferencesInitialized where

open import ConnectionManagement.Negative.ServerPeers using (module Protocols)
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.GovernorPool as Prior
open import ConnectionManagement.Properties.LiveTrackerOwnersInitialized using (module Frontend)
open Protocols using (capability; initializer)
open Protocols.StartTrace.ScopedCM.Completion using
  (serverFinished; initialized-server-finish)
open Frontend I.bearerClosed Prior.classify capability using (Validity; from-initial)

-- The universal theorem supplies all references at this existing endpoint.
scheduled-close : Validity serverFinished
scheduled-close = from-initial _ _ initializer initialized-server-finish
