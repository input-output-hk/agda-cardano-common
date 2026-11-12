{-# OPTIONS --guardedness #-}

-- Separate scheduled-close application for publication-failure snapshot
-- references, keeping the concrete fixture checks in small import closures.
module ConnectionManagement.Negative.LiveTrackerFailuresInitialized where

open import ConnectionManagement.Negative.ServerPeers using (module Protocols)
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.GovernorPool as Prior
open import ConnectionManagement.Properties.LiveTrackerFailuresInitialized using (module Frontend)
open Protocols using (capability; initializer)
open Protocols.StartTrace.ScopedCM.Completion using (serverFinished; initialized-server-finish)
open Frontend I.bearerClosed Prior.classify capability using (Validity; from-initial)

scheduled-failure-snapshots : Validity serverFinished
scheduled-failure-snapshots = from-initial _ _ initializer initialized-server-finish
