{-# OPTIONS --guardedness #-}

-- Acceptance endpoint for selected caller-run CM interruption and nonempty IG
-- final tracing. Conditional pruning/order controls stay labelled as such.
module ConnectionManagement.Negative.ServerIGExit where

import ConnectionManagement.Negative.ServerIGExitRelease
import ConnectionManagement.Negative.ServerIGExitProtocolPrefix
import ConnectionManagement.Negative.ServerIGExitCases
import ConnectionManagement.Negative.ServerIGExitControls
import ConnectionManagement.Negative.ServerIGExitSend
