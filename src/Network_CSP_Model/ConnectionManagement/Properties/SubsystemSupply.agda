{-# OPTIONS --guardedness #-}

-- Entry/promise bounds for every finite combined-subsystem interleaving.
module ConnectionManagement.Properties.SubsystemSupply where

open import Data.Product using (_,_; proj₂)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_)
import ConnectionManagement.Machine as I
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)
import ConnectionManagement.Properties.OutboundRuntimeSupply as Runtime
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.SubsystemCapture as Captures
import ConnectionManagement.Properties.SubsystemInvariant as Invariant

-- The closed induction invariant includes capture validity as well as heap bounds.
open Invariant.Lift Runtime.RuntimeValid Runtime.advance-preserves public

-- Observe the same shared world as the existing inbound supply invariant.
Bounded : Sub.Configuration → Set
Bounded c = SupplyBounds (I.world (O.core (J.cm (Sub.world c))))

-- Arbitrary injected frames require the separately proved capture certificate.
advance-bounds : ∀ a c {c′} → Sub.advance a c ≡ just c′ →
  Captures.Captures c → Bounded c → Bounded c′
advance-bounds a c eq captured bounded = proj₂ (advance-preserves a c eq (captured , bounded))

-- No action-family, caller, job or monitor scheduling restriction.
exec-bounds : ∀ {c actions c′} → Captures.Captures c → Bounded c →
  Sub.Executes c actions c′ → Bounded c′
exec-bounds captured bounded path = proj₂ (exec-preserves (captured , bounded) path)

-- The real initializer discharges runtime validity; heap bounds remain explicit.
initial-valid : ∀ c s → SupplyBounds (I.world c) → Valid (Sub.initial (O.initial c) s)
initial-valid c s bounded = Capture.initial-valid c , bounded

-- Reachable executions inherit both invariant components.
from-initial-valid : ∀ {c s actions c′} → SupplyBounds (I.world c) →
  Sub.Executes (Sub.initial (O.initial c) s) actions c′ → Valid c′
from-initial-valid {c} {s} bounded = exec-preserves (initial-valid c s bounded)

-- All allocated entry and promise IDs stay below their current supplies.
from-initial : ∀ {c s actions c′} → SupplyBounds (I.world c) →
  Sub.Executes (Sub.initial (O.initial c) s) actions c′ → Bounded c′
from-initial bounded path = proj₂ (from-initial-valid bounded path)
