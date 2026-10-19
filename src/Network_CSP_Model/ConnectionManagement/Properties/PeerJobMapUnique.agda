{-# OPTIONS --guardedness #-}

-- All peer-job actions preserve current, saved and prospective map uniqueness.
module ConnectionManagement.Properties.PeerJobMapUnique where

import ConnectionManagement.Properties.PeerJobInvariant as Jobs
import ConnectionManagement.Properties.OutboundRuntimeMapUnique as Maps

open Jobs.Lift Maps.RuntimeValid Maps.advance-preserves public
