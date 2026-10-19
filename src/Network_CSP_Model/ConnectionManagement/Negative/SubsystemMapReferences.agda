{-# OPTIONS --guardedness #-}

-- Reachable reference certificates and an injected missing-publication control.
module ConnectionManagement.Negative.SubsystemMapReferences where

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
import ConnectionManagement.State as S
import ConnectionManagement.Machine as I
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Properties.StateMapReferences as Maps
import ConnectionManagement.Properties.StateMapUniqueness as UniqueMaps
import ConnectionManagement.Properties.SubsystemMapReferences as References
import ConnectionManagement.Properties.MapReferencesCounters as Bridge
open import ConnectionManagement.Properties.CounterState using (CounterStateValid)
open import ConnectionManagement.Properties.Ownership using (Ownership)
import ConnectionManagement.CSP.Fixtures as Fixture
import ConnectionManagement.CSP.GovernorLifecycle as Lifecycle
import ConnectionManagement.CSP.GovernorFailureLimit as Failures
import ConnectionManagement.Negative.Subsystem as Race
import ConnectionManagement.Negative.CounterValidity as Controls
open import ConnectionManagement.Scenarios.Admission using (w₀; r₀; child₀; key₀)

-- Empty map and workers with no captured maps or pending publications.
initial-references : Maps.Valid (I.world Fixture.start)
initial-references = [] , (tt ∷ tt ∷ []) , []

lifecycle-references : References.Valid Lifecycle.final
lifecycle-references = References.from-initial initial-references Lifecycle.path
race-references : References.Valid (Race.held Lifecycle.c41)
race-references = References.from-initial initial-references Race.racePath
failure-limit-references : References.Valid Failures.c211
failure-limit-references = References.from-initial initial-references Failures.path

lifecycle-counter-valid : CounterStateValid (I.world (O.core (J.cm (Sub.world Lifecycle.final))))
lifecycle-counter-valid = References.from-initial-counter-valid initial-references Lifecycle.path
failure-limit-counter-valid : CounterStateValid (I.world (O.core (J.cm (Sub.world Failures.c211))))
failure-limit-counter-valid = References.from-initial-counter-valid initial-references Failures.path

-- The existing malformed current/saved-map controls also fail the stronger
-- certificate. These are injected states, not source-reachable defects.
bad-current-invalid : ¬ Maps.Valid (I.world Controls.bad)
bad-current-invalid valid = Controls.bad-invalid (Bridge.counter-state-valid (I.world Controls.bad) valid)
bad-saved-invalid : ¬ Maps.Valid Controls.badSaved
bad-saved-invalid valid = Controls.bad-saved-invalid (Bridge.counter-state-valid Controls.badSaved valid)

-- A valid empty saved map alone says nothing about the entry about to be
-- inserted. Forge a publication frame without allocating its captured entry.
before : I.Configuration
before = I.initial S.responderMode (record (I.world Fixture.start)
  { cm = S.cmStore (S.taken w₀) [] 0
  ; admissions = (w₀ , S.admissionWorker r₀
      (S.publish Fixture.parentLease Fixture.promise₀ Fixture.entry₀)) ∷ [] })
after : I.Configuration
after = record before { world = record (I.world before)
  { cm = S.cmStore (S.full Fixture.binding) [] 0
  ; admissions = (w₀ , S.admissionWorker r₀
      (S.countPublished Fixture.promise₀ Fixture.entry₀)) ∷ [] } }
beforeSubsystem : Sub.Configuration
beforeSubsystem = Sub.initial (O.initial before) Lifecycle.settings
afterSubsystem : Sub.Configuration
afterSubsystem = Sub.initial (O.initial after) Lifecycle.settings

-- The actual combined dispatcher publishes the captured ID without a lookup.
publish-step : Sub.advance (Sub.core (O.inbound (I.admissionStep w₀ Server.putMapBack)))
  beforeSubsystem ≡ just afterSubsystem
publish-step = refl
before-counter-valid : CounterStateValid (I.world before)
before-counter-valid = [] ∷ []
before-owned : Ownership (I.world before)
before-owned = Fixture.parentLease , refl , refl
before-unique : UniqueMaps.Valid (I.world before)
before-unique = tt , (([] , []) ∷ []) , []
after-counter-invalid : ¬ CounterStateValid (I.world after)
after-counter-invalid ((((st , ()) ∷ _) ∷ _) ∷ _)

-- Refute preservation from the unchanged map-only predicate on arbitrary frames.
no-map-only-preservation : ¬ (∀ a c {c′} → Sub.advance a c ≡ just c′ →
  CounterStateValid (I.world (O.core (J.cm (Sub.world c)))) →
  CounterStateValid (I.world (O.core (J.cm (Sub.world c′)))))
no-map-only-preservation preserve = after-counter-invalid
  (preserve (Sub.core (O.inbound (I.admissionStep w₀ Server.putMapBack)))
    beforeSubsystem publish-step before-counter-valid)

-- The new certificate rejects the forged capture before it can be published.
before-certificate-invalid : ¬ References.Valid beforeSubsystem
before-certificate-invalid (_ , ((_ , (st , ())) ∷ _) , _)
after-certificate-invalid : ¬ References.Valid afterSubsystem
after-certificate-invalid valid = after-counter-invalid (References.counter-state-valid afterSubsystem valid)

-- Every initialized interleaving from a reference-valid world excludes both.
invalid-unreachable : ∀ target → ¬ References.Valid target → ∀ c s actions →
  Maps.Valid (I.world c) → ¬ Sub.Executes (Sub.initial (O.initial c) s) actions target
invalid-unreachable target invalid c s actions valid path = invalid (References.from-initial valid path)
forged-capture-unreachable : ∀ c s actions → Maps.Valid (I.world c) →
  ¬ Sub.Executes (Sub.initial (O.initial c) s) actions beforeSubsystem
forged-capture-unreachable = invalid-unreachable beforeSubsystem before-certificate-invalid
dangling-publication-unreachable : ∀ c s actions → Maps.Valid (I.world c) →
  ¬ Sub.Executes (Sub.initial (O.initial c) s) actions afterSubsystem
dangling-publication-unreachable = invalid-unreachable afterSubsystem after-certificate-invalid

-- A cleanup output map is separate from its good, empty saved lease map.
-- Its references must be checked even while the global map is taken.
pendingLease : S.Lease
pendingLease = S.lease child₀ []
pendingBefore : I.Configuration
pendingBefore = record Controls.locked { world = record (I.world Controls.locked)
  { cm = S.cmStore (S.taken child₀) [] 0
  ; admissions = []
  ; cleanups = (child₀ , S.cleanupPublish pendingLease Fixture.binding S.countImmediately) ∷ [] } }
pendingAfter : I.Configuration
pendingAfter = record pendingBefore { world = record (I.world pendingBefore)
  { cm = S.cmStore (S.full Fixture.binding) [] 0
  ; cleanups = (child₀ , S.cleanupCount S.cleanupNormal) ∷ [] } }
pendingSubsystem : Sub.Configuration
pendingSubsystem = Sub.initial (O.initial pendingBefore) Lifecycle.settings
pendingSubsystemAfter : Sub.Configuration
pendingSubsystemAfter = Sub.initial (O.initial pendingAfter) Lifecycle.settings
pending-publish-step : Sub.advance (Sub.core (O.inbound (I.cleanupStep child₀ Cleanup.publishCleanupMap)))
  pendingSubsystem ≡ just pendingSubsystemAfter
pending-publish-step = refl
pending-saved-valid : Maps.CleanupReferences [] (S.cleanupSelect pendingLease)
pending-saved-valid = []
pending-certificate-invalid : ¬ References.Valid pendingSubsystem
pending-certificate-invalid (_ , _ , ((_ , (((st , ()) ∷ _) ∷ _)) ∷ _))
pending-after-invalid : ¬ CounterStateValid (I.world pendingAfter)
pending-after-invalid ((((st , ()) ∷ _) ∷ _) ∷ _)
pending-capture-unreachable : ∀ c s actions → Maps.Valid (I.world c) →
  ¬ Sub.Executes (Sub.initial (O.initial c) s) actions pendingSubsystem
pending-capture-unreachable = invalid-unreachable pendingSubsystem pending-certificate-invalid
