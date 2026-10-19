{-# OPTIONS --guardedness #-}

-- Acquisition captures remain allocated throughout every subsystem execution.
module ConnectionManagement.Properties.SubsystemCapture where

import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.SubsystemInvariant as Invariant

-- Inherit the exhaustive action proof and finite-execution induction.
open Invariant.Lift Capture.RuntimeValid Capture.advance-preserves public
  renaming (Valid to Captures)

-- The nested initializer starts with no pending acquisition frames.
initial-valid : ∀ c s → Captures (Sub.initial (O.initial c) s)
initial-valid c s = Capture.initial-valid c

-- Initial heap contents need no supply premise for this capture-only theorem.
from-initial : ∀ {c s actions c′} →
  Sub.Executes (Sub.initial (O.initial c) s) actions c′ → Captures c′
from-initial {c} {s} = exec-preserves (initial-valid c s)
