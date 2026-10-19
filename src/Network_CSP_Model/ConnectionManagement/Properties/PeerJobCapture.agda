{-# OPTIONS --guardedness #-}

-- Every peer-job action preserves all acquisition captures.
module ConnectionManagement.Properties.PeerJobCapture where

import ConnectionManagement.Properties.PeerJobInvariant as Jobs
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture

-- Preserve the original public proof API by instantiating the shared lift.
open Jobs.Lift Capture.RuntimeValid Capture.advance-preserves public
