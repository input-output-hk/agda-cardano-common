{-# OPTIONS --guardedness #-}

-- Preserve existing handler descriptors and stored entry/socket identities
-- through every combined interleaving. Historical presence is not live ownership.
module ConnectionManagement.Properties.SubsystemResources where

open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ConnectionManagement.Domain using (WorkerId)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as I
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
open import ConnectionManagement.Properties.HandlerResources using (Resources; original)
open import ConnectionManagement.Properties.HandlerResourceFacts
import ConnectionManagement.Properties.SubsystemInvariant as Invariant
import ConnectionManagement.Properties.OutboundRuntimeResources as Runtime

-- Keep the descriptor fixed throughout the induction, rather than merely
-- preserving existence of some handler at the same worker ID.
module For (q : WorkerId) (captured : S.HandlerStart) where
  open Invariant.Lift (Runtime.For.RuntimeValid q captured) (Runtime.For.advance-preserves q captured) public

-- Public wrappers use the unchanged Resources predicate, with no supply,
-- ownership, uniqueness or scheduling premise.
resources-step : ∀ a c {c′ q} → Sub.advance a c ≡ just c′ →
  Resources q (I.world (O.core (J.cm (Sub.world c)))) →
  Resources q (I.world (O.core (J.cm (Sub.world c′))))
resources-step a c {q = q} eq resources = to-resources
  (For.advance-preserves q (original resources) a c eq (from-resources resources))

resources-exec : ∀ {c actions c′ q} → Sub.Executes c actions c′ →
  Resources q (I.world (O.core (J.cm (Sub.world c)))) →
  Resources q (I.world (O.core (J.cm (Sub.world c′))))
resources-exec {q = q} path resources = to-resources
  (For.exec-preserves q (original resources) (from-resources resources) path)
