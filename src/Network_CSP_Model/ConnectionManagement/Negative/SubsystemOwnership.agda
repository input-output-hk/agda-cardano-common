{-# OPTIONS --guardedness #-}

-- Exercise exact ownership over ordinary executions, an outbound action while
-- an inbound cleanup holds the map, and malformed lease-census endpoints.
module ConnectionManagement.Negative.SubsystemOwnership where

open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
import ConnectionManagement.State as S
import ConnectionManagement.Machine as I
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundCases as Cases
import ConnectionManagement.CSP.Fixtures as Fixture
import ConnectionManagement.CSP.GovernorLifecycle as Lifecycle
import ConnectionManagement.CSP.GovernorFailureLimit as Failures
import ConnectionManagement.Negative.Subsystem as Race
import ConnectionManagement.Negative.Ownership as Malformed
import ConnectionManagement.Negative.OutboundSupply as Forged
import ConnectionManagement.Properties.SubsystemOwnership as Own
import ConnectionManagement.Properties.OutboundRuntimeOwnership as OutboundOwn
open import ConnectionManagement.Properties.Ownership using (Ownership)

-- These certificates use the full preservation theorem, not final-state refl.
lifecycle-owned : Own.Valid Lifecycle.final
lifecycle-owned = Own.from-initial refl Lifecycle.path

child-before-registration-owned : Own.Valid (Race.held Lifecycle.c41)
child-before-registration-owned = Own.from-initial refl Race.racePath

failure-limit-owned : Own.Valid Failures.c211
failure-limit-owned = Own.from-initial refl Failures.path

-- A forged captured entry can violate supply bounds while preserving ownership.
-- The ownership theorem therefore must not require a capture certificate.
forged-cleanup-owned : OutboundOwn.Valid Forged.after
forged-cleanup-owned = OutboundOwn.advance-preserves
  (O.acquire (ident 10) A.removeReservation) Forged.before
  Forged.removal-step Forged.before-owned

-- Conditional fixture: an inbound cleanup owns the map while an outbound caller
-- is opening its socket. The fixture's source reachability is not asserted.
heldRequest : A.Request
heldRequest = record Forged.request { socketRef = ident 20 }

heldBefore : O.Configuration
heldBefore = record (O.initial Malformed.beforeClose)
  { acquiring = (ident 10 , A.frame heldRequest (A.openSocket (ident 0) (ident 0))) ∷ [] }

heldAfter : O.Configuration
heldAfter = record heldBefore
  { acquiring = (ident 10 , A.frame heldRequest
      (A.complete (Cases.raised (Cases.ioFailure (errorId 0))))) ∷ [] }

held-source-step : O.advance (O.acquire (ident 10) (A.failIO (errorId 0))) heldBefore ≡ just heldAfter
held-source-step = refl

heldSubsystem : Sub.Configuration
heldSubsystem = Sub.initial heldBefore Lifecycle.settings

heldSubsystemAfter : Sub.Configuration
heldSubsystemAfter = record heldSubsystem { world = J.world heldAfter [] }

held-subsystem-step : Sub.advance
  (Sub.core (O.acquire (ident 10) (A.failIO (errorId 0)))) heldSubsystem ≡ just heldSubsystemAfter
held-subsystem-step = refl

-- The actual caller error leaves the inbound cleanup's unique lease intact.
held-map-owned : Own.Valid heldSubsystemAfter
held-map-owned = Own.advance-preserves
  (Sub.core (O.acquire (ident 10) (A.failIO (errorId 0)))) heldSubsystem
  held-subsystem-step Malformed.before-owned

-- Merely supplying a selecting frame cannot bypass the held-map guard.
selection-while-held : O.advance (O.acquire (ident 10) (A.select nothing))
  (record heldBefore { acquiring = (ident 10 , A.frame heldRequest A.selecting) ∷ [] }) ≡ nothing
selection-while-held = refl

-- Lift the existing malformed shared worlds into the actual subsystem shape.
invalidFixture : S.State → Sub.Configuration
invalidFixture s = Sub.initial (O.initial (I.initial S.responderMode s)) Lifecycle.settings

orphan-invalid : ¬ Own.Valid (invalidFixture Malformed.orphan)
orphan-invalid = Malformed.orphan-invalid
full-with-lease-invalid : ¬ Own.Valid (invalidFixture Malformed.fullWithLease)
full-with-lease-invalid = Malformed.full-with-lease-invalid
double-claim-invalid : ¬ Own.Valid (invalidFixture Malformed.doubleClaim)
double-claim-invalid = Malformed.double-claim-invalid
wrong-owner-invalid : ¬ Own.Valid (invalidFixture Malformed.wrongOwner)
wrong-owner-invalid = Malformed.wrong-owner-invalid

-- The general theorem excludes every unowned endpoint from initially owned runs.
unowned-unreachable : ∀ target → ¬ Own.Valid target → ∀ c s actions →
  Ownership (I.world c) → ¬ Sub.Executes (Sub.initial (O.initial c) s) actions target
unowned-unreachable target invalid c s actions own path = invalid (Own.from-initial own path)

orphan-unreachable : ∀ c s actions → Ownership (I.world c) →
  ¬ Sub.Executes (Sub.initial (O.initial c) s) actions (invalidFixture Malformed.orphan)
orphan-unreachable = unowned-unreachable (invalidFixture Malformed.orphan) orphan-invalid

full-with-lease-unreachable : ∀ c s actions → Ownership (I.world c) →
  ¬ Sub.Executes (Sub.initial (O.initial c) s) actions (invalidFixture Malformed.fullWithLease)
full-with-lease-unreachable = unowned-unreachable (invalidFixture Malformed.fullWithLease) full-with-lease-invalid

double-claim-unreachable : ∀ c s actions → Ownership (I.world c) →
  ¬ Sub.Executes (Sub.initial (O.initial c) s) actions (invalidFixture Malformed.doubleClaim)
double-claim-unreachable = unowned-unreachable (invalidFixture Malformed.doubleClaim) double-claim-invalid

wrong-owner-unreachable : ∀ c s actions → Ownership (I.world c) →
  ¬ Sub.Executes (Sub.initial (O.initial c) s) actions (invalidFixture Malformed.wrongOwner)
wrong-owner-unreachable = unowned-unreachable (invalidFixture Malformed.wrongOwner) wrong-owner-invalid
