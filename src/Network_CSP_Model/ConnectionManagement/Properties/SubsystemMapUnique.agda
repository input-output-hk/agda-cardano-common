{-# OPTIONS --guardedness #-}

-- Unique nested maps through every finite combined-subsystem interleaving.
module ConnectionManagement.Properties.SubsystemMapUnique where

import ConnectionManagement.Machine as I
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Properties.StateMapUniqueness as StateMaps
import ConnectionManagement.Properties.OutboundRuntimeMapUnique as Runtime
import ConnectionManagement.Properties.SubsystemInvariant as Invariant

-- No ownership, capture-validity, supply or store-key uniqueness premise.
open Invariant.Lift Runtime.RuntimeValid Runtime.advance-preserves public

-- The nested initializer preserves the shared state's map certificates.
initial-valid : ∀ c s → StateMaps.Valid (I.world c) → Valid (Sub.initial (O.initial c) s)
initial-valid c s maps = maps

-- Every current and captured map stays unique from initially unique maps.
from-initial : ∀ {c s actions c′} → StateMaps.Valid (I.world c) →
  Sub.Executes (Sub.initial (O.initial c) s) actions c′ → Valid c′
from-initial {c} {s} maps = exec-preserves (initial-valid c s maps)
