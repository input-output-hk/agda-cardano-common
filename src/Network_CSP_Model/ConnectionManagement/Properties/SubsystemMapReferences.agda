{-# OPTIONS --guardedness #-}

-- Valid entry references through every finite combined-subsystem interleaving.
module ConnectionManagement.Properties.SubsystemMapReferences where

import ConnectionManagement.Machine as I
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Properties.StateMapReferences as StateMaps
import ConnectionManagement.Properties.OutboundRuntimeMapReferences as Runtime
import ConnectionManagement.Properties.SubsystemInvariant as Invariant

-- No separate ownership, outbound-capture, supply or uniqueness premise.
open Invariant.Lift Runtime.RuntimeValid Runtime.advance-preserves public

-- The nested initializer preserves the shared state's map certificates.
initial-valid : ∀ c s → StateMaps.Valid (I.world c) → Valid (Sub.initial (O.initial c) s)
initial-valid c s maps = maps

-- Every stored map retains references to present entries from a valid initial world.
from-initial : ∀ {c s actions c′} → StateMaps.Valid (I.world c) →
  Sub.Executes (Sub.initial (O.initial c) s) actions c′ → Valid c′
from-initial {c} {s} maps = exec-preserves (initial-valid c s maps)

import ConnectionManagement.Properties.MapReferencesCounters as Counters
import ConnectionManagement.Properties.CounterState as CounterState
import ConnectionManagement.Rules.PeerJobs as Jobs

-- Project to the pre-existing counter predicate; the inductive certificate
-- additionally covers entries waiting for admission publication.
counter-state-valid : ∀ c → Valid c →
  CounterState.CounterStateValid (I.world (O.core (Jobs.cm (Sub.world c))))
counter-state-valid c valid = Counters.counter-state-valid (I.world (O.core (Jobs.cm (Sub.world c)))) valid

from-initial-counter-valid : ∀ {c s actions c′} → StateMaps.Valid (I.world c) →
  Sub.Executes (Sub.initial (O.initial c) s) actions c′ →
  CounterState.CounterStateValid (I.world (O.core (Jobs.cm (Sub.world c′))))
from-initial-counter-valid {c′ = c′} valid path =
  counter-state-valid c′ (from-initial valid path)
