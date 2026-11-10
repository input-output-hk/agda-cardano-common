{-# OPTIONS --guardedness #-}

-- SI5b on an actual run: the same initialized scheduled-node close as
-- Negative/ServerShutdownComplete also has a closed, drained CM coordinator
-- closed by a physical result wait. Nothing about the run is asserted by hand.
module ConnectionManagement.Negative.ServerShutdownCoordinator where

open import Data.Bool using (true)
open import Data.Maybe using (just)
open import ConnectionManagement.Negative.ServerPeers using (module Protocols)
import ConnectionManagement.Negative.PoolRelays as Relays
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.GovernorPool as Prior
import ConnectionManagement.Rules.PoolRelays as RR
import ConnectionManagement.Properties.ServerShutdownCoordinator as SI5
private
  module Done = Protocols.StartTrace.ScopedCM.Completion
  module Shutdown = SI5 I.bearerClosed Prior.classify
  module Certificate = Shutdown.Protocols Protocols.capability

scheduled-close : Certificate.Complete true Done.serverFinished (just RR.joined)
scheduled-close = Certificate.complete Protocols.initializer Relays.Initialized.initialized-relays-close
