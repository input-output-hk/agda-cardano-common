{-# OPTIONS --guardedness #-}

-- Split extension of the initialized scheduled-close fixture: the universal
-- current-frame result is applied without adding more concrete normalization
-- obligations to LiveTrackerReferencesInitialized.
module ConnectionManagement.Negative.LiveTrackerChainsInitialized where

open import ConnectionManagement.Negative.ServerPeers using (module Protocols)
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.GovernorPool as Prior
open import ConnectionManagement.Properties.LiveTrackerChainsInitialized using (module Frontend)
open Protocols using (capability; initializer)
open Protocols.StartTrace.ScopedCM.Completion using (serverFinished; initialized-server-finish)
open Frontend I.bearerClosed Prior.classify capability using (Validity; from-initial)

scheduled-current-frames : Validity serverFinished
scheduled-current-frames = from-initial _ _ initializer initialized-server-finish
