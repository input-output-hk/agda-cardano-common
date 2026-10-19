{-# OPTIONS --guardedness #-}

-- All peer-job actions preserve current, saved and prospective map references.
module ConnectionManagement.Properties.PeerJobMapReferences where

import ConnectionManagement.Properties.PeerJobInvariant as Jobs
import ConnectionManagement.Properties.OutboundRuntimeMapReferences as Maps

open Jobs.Lift Maps.RuntimeValid Maps.advance-preserves public
