{-# OPTIONS --guardedness #-}

-- Full CM-I4c reference validity in the explicitly empty-continuation profile.
-- The unrestricted-initializer counterexample remains a separate statement.
module ConnectionManagement.Properties.LiveTrackerInitialized where
open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ConnectionManagement.Domain using (ErrorId; HandleId)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.ServerPeers as Model
import ConnectionManagement.Properties.LiveTrackerChainsInitialized as Chains
import ConnectionManagement.Properties.LiveTrackerFailuresInitialized as Failures
import ConnectionManagement.Properties.LiveTrackerAuxCoverageFrontend as Auxiliary
import ConnectionManagement.Properties.LiveTrackerAuxContent as Content

module Frontend (b io : ErrorId → Bool) (capability : HandleId → ℕ → Bool) where
 open Model.Protocols b io capability using (Runtime; Runs; initialize; base)
 open Auxiliary.Frontend b io capability using (Valid; delta; coverage-from-initial)
 record FullValidity (s : Runtime) : Set where
  field chains : Chains.Frontend.Validity b io capability s
        publication-failures : Failures.Frontend.Validity b io capability s
        references : Content.Coverage b (delta (base s))
        auxiliary : Valid s
 from-initial : ∀ c₀ g {start events s} → initialize (O.initial c₀) g ≡ just start →
   Runs start events s → FullValidity s
 from-initial c₀ g initialized path = record
   { chains = Chains.Frontend.from-initial b io capability c₀ g initialized path
   ; publication-failures = Failures.Frontend.from-initial b io capability c₀ g initialized path
   ; references = coverage-from-initial c₀ g initialized path
   ; auxiliary = Auxiliary.Frontend.from-initial b io capability c₀ g initialized path }
