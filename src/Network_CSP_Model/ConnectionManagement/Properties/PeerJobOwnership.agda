{-# OPTIONS --guardedness #-}

-- Peer jobs preserve the same exact map-lease ownership statement.
module ConnectionManagement.Properties.PeerJobOwnership where

import ConnectionManagement.Properties.PeerJobInvariant as Jobs
import ConnectionManagement.Properties.OutboundRuntimeOwnership as Ownership

-- No capture-validity or allocation-bound premise is added to ownership.
open Jobs.Lift Ownership.RuntimeValid Ownership.advance-preserves public
