{-# OPTIONS --guardedness #-}

-- SI5a on an actual run: the initialized scheduled-node close of
-- Negative/PoolRelays (the accepted server-return run lifted inside the relays
-- scope, then relays cancel, join and owner return) satisfies the general
-- shutdown certificate. Nothing about the run is asserted by hand.
module ConnectionManagement.Negative.ServerShutdownComplete where

open import Data.Bool using (true)
open import Data.Maybe using (just)
open import ConnectionManagement.Negative.ServerPeers using (module Protocols)
import ConnectionManagement.Negative.PoolRelays as Relays
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.GovernorPool as Prior
import ConnectionManagement.Rules.PoolRelays as RR
import ConnectionManagement.Properties.ServerShutdownComplete as SI5
private
  module Done = Protocols.StartTrace.ScopedCM.Completion
  module Shutdown = SI5 I.bearerClosed Prior.classify
  module Certificate = Shutdown.Protocols Protocols.capability

scheduled-close : Certificate.Complete true Done.serverFinished (just RR.joined)
scheduled-close = Certificate.complete Protocols.initializer Relays.Initialized.initialized-relays-close
