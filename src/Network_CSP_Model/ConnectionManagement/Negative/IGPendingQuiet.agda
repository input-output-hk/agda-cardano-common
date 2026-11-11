{-# OPTIONS --guardedness #-}

-- Residue c1 on an actual run: at the end of the initialized scheduled-node
-- close of Negative/ServerShutdownComplete, the inbound governor is exited and
-- deactivated with no pending CM call. Nothing about the run is asserted by hand.
module ConnectionManagement.Negative.IGPendingQuiet where

open import ConnectionManagement.Negative.ServerPeers using (module Protocols)
import ConnectionManagement.Negative.PoolRelays as Relays
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.GovernorPool as Prior
import ConnectionManagement.Properties.IGPendingQuiet as C1
import ConnectionManagement.Rules.PoolRelays as RR
open import Data.Bool using (true)
open import Data.Maybe using (just)
private
  module Done = Protocols.StartTrace.ScopedCM.Completion
  module Residue = C1 I.bearerClosed Prior.classify
  module Certificate = Residue.Protocols Protocols.capability

scheduled-close : Certificate.IGQuiet Done.serverFinished
scheduled-close = Certificate.ig-quiet {scheduled = true} {t = just RR.joined} Protocols.initializer Relays.Initialized.initialized-relays-close
