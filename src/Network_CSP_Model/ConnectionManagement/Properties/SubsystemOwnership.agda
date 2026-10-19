{-# OPTIONS --guardedness #-}

-- Exclusive map-lease ownership through all combined-subsystem interleavings.
module ConnectionManagement.Properties.SubsystemOwnership where

import ConnectionManagement.Machine as I
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
open import ConnectionManagement.Properties.Ownership using (Ownership)
import ConnectionManagement.Properties.OutboundRuntimeOwnership as Runtime
import ConnectionManagement.Properties.SubsystemInvariant as Invariant

-- Same lease census, lifted over every successful job/monitor/governor action.
open Invariant.Lift Runtime.RuntimeValid Runtime.advance-preserves public

-- Initialization retains the shared world's ownership proposition exactly.
initial-valid : ∀ c s → Ownership (I.world c) → Valid (Sub.initial (O.initial c) s)
initial-valid c s own = own

-- All finite interleavings preserve ownership from an initially owned world.
from-initial : ∀ {c s actions c′} → Ownership (I.world c) →
  Sub.Executes (Sub.initial (O.initial c) s) actions c′ → Valid c′
from-initial {c} {s} own = exec-preserves (initial-valid c s own)
