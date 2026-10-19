{-# OPTIONS --guardedness #-}

-- Reachable-map certificates and injected restoration/publication controls.
module ConnectionManagement.Negative.SubsystemMapUnique where

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
import ConnectionManagement.State as S
import ConnectionManagement.Machine as I
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Properties.StateMapUniqueness as Maps
import ConnectionManagement.Properties.SubsystemMapUnique as Unique
open import ConnectionManagement.Properties.MapUniqueness using (MapUnique; insert-unique)
open import ConnectionManagement.Properties.Ownership using (Ownership; claims)
import ConnectionManagement.CSP.Fixtures as Fixture
import ConnectionManagement.CSP.GovernorLifecycle as Lifecycle
import ConnectionManagement.CSP.GovernorFailureLimit as Failures
import ConnectionManagement.Negative.Subsystem as Race
import ConnectionManagement.Negative.Ownership as OwnershipControls
open import ConnectionManagement.Scenarios.Admission using (key₀; child₀)

-- Unique empty current map; both admission workers start without saved maps.
initial-unique : Maps.Valid (I.world Fixture.start)
initial-unique = ([] , []) , (tt ∷ tt ∷ []) , []

-- The full theorem, rather than a final-state inspection, certifies each path.
lifecycle-unique : Unique.Valid Lifecycle.final
lifecycle-unique = Unique.from-initial initial-unique Lifecycle.path
child-before-registration-unique : Unique.Valid (Race.held Lifecycle.c41)
child-before-registration-unique = Unique.from-initial initial-unique Race.racePath
failure-limit-unique : Unique.Valid Failures.c211
failure-limit-unique = Unique.from-initial initial-unique Failures.path

-- Duplicate remote keys and duplicate local keys are distinct failures.
duplicateRemote : S.ConnMap
duplicateRemote = (remote key₀ , []) ∷ (remote key₀ , []) ∷ []
duplicateLocal : S.ConnMap
duplicateLocal = (remote key₀ , (unknownLocal , ident 0) ∷ (unknownLocal , ident 1) ∷ []) ∷ []

duplicate-remote-invalid : ¬ MapUnique duplicateRemote
duplicate-remote-invalid ((neq ∷ _) ∷ _ , _) = neq refl
duplicate-local-invalid : ¬ MapUnique duplicateLocal
duplicate-local-invalid (_ , ((neq ∷ _) ∷ _) ∷ _) = neq refl

-- Build an owned taken-map fixture with a malformed saved map. Neither this
-- state nor its injected maps are claimed to arise from source execution.
badLease : S.Lease
badLease = S.lease child₀ duplicateRemote
savedBefore : I.Configuration
savedBefore = record OwnershipControls.beforeClose
  { world = record (I.world OwnershipControls.beforeClose)
      { cleanups = (child₀ , S.cleanupRestore badLease (errorId 0)) ∷ [] } }
savedAfter : I.Configuration
savedAfter = record savedBefore { world = record (I.world savedBefore)
  { cm = record (S.cm (I.world savedBefore)) { mapCell = S.full duplicateRemote }
  ; cleanups = (child₀ , S.cleanupDone (S.cleanupError (errorId 0))) ∷ [] } }

savedSubsystem : Sub.Configuration
savedSubsystem = Sub.initial (O.initial savedBefore) Lifecycle.settings
savedSubsystemAfter : Sub.Configuration
savedSubsystemAfter = Sub.initial (O.initial savedAfter) Lifecycle.settings

-- The actual dispatcher restores the captured map without sanitizing it.
restore-step : Sub.advance (Sub.core (O.inbound (I.cleanupStep child₀ Cleanup.restoreCleanupMap)))
  savedSubsystem ≡ just savedSubsystemAfter
restore-step = refl

current-before-unique : Maps.CellUnique (S.mapCell (S.cm (I.world savedBefore)))
current-before-unique = tt
owned-before-restore : Ownership (I.world savedBefore)
owned-before-restore = badLease , refl , refl
current-after-nonunique : ¬ Maps.CellUnique (S.mapCell (S.cm (I.world savedAfter)))
current-after-nonunique = duplicate-remote-invalid

-- Even an exclusive, correctly owned lease does not validate its saved map.
no-current-and-ownership-only-preservation : ¬ (∀ a c {c′} → Sub.advance a c ≡ just c′ →
  Ownership (I.world (O.core (J.cm (Sub.world c)))) →
  Maps.CellUnique (S.mapCell (S.cm (I.world (O.core (J.cm (Sub.world c)))))) →
  Maps.CellUnique (S.mapCell (S.cm (I.world (O.core (J.cm (Sub.world c′)))))))
no-current-and-ownership-only-preservation preserve = current-after-nonunique
  (preserve (Sub.core (O.inbound (I.cleanupStep child₀ Cleanup.restoreCleanupMap)))
    savedSubsystem restore-step owned-before-restore current-before-unique)

saved-certificate-invalid : ¬ Unique.Valid savedSubsystem
saved-certificate-invalid (_ , _ , captured ∷ _) = duplicate-remote-invalid captured

-- A separate control uses a GOOD saved map but a BAD prospective output map.
pendingBefore : I.Configuration
pendingBefore = record OwnershipControls.beforeClose
  { world = record (I.world OwnershipControls.beforeClose)
      { cleanups = (child₀ , S.cleanupPublish Fixture.childLease duplicateLocal S.countImmediately) ∷ [] } }
pendingAfter : I.Configuration
pendingAfter = record pendingBefore { world = record (I.world pendingBefore)
  { cm = record (S.cm (I.world pendingBefore)) { mapCell = S.full duplicateLocal }
  ; cleanups = (child₀ , S.cleanupCount S.cleanupNormal) ∷ [] } }
pendingSubsystem : Sub.Configuration
pendingSubsystem = Sub.initial (O.initial pendingBefore) Lifecycle.settings
pendingSubsystemAfter : Sub.Configuration
pendingSubsystemAfter = Sub.initial (O.initial pendingAfter) Lifecycle.settings

publish-step : Sub.advance (Sub.core (O.inbound (I.cleanupStep child₀ Cleanup.publishCleanupMap)))
  pendingSubsystem ≡ just pendingSubsystemAfter
publish-step = refl
saved-lease-unique : MapUnique (S.savedMap Fixture.childLease)
saved-lease-unique = insert-unique (remote key₀) (knownLocal (local key₀)) Fixture.entry₀ [] ([] , [])
owned-before-publish : Ownership (I.world pendingBefore)
owned-before-publish = Fixture.childLease , refl , refl
pending-certificate-invalid : ¬ Unique.Valid pendingSubsystem
pending-certificate-invalid (_ , _ , (saved , pending) ∷ _) = duplicate-local-invalid pending
pending-output-nonunique : ¬ Maps.CellUnique (S.mapCell (S.cm (I.world pendingAfter)))
pending-output-nonunique = duplicate-local-invalid

-- Checking the full map and EVERY lease's saved map still misses the pending map.
LeaseOnly : S.State → Set
LeaseOnly s = Maps.CellUnique (S.mapCell (S.cm s)) ×
  All (λ claim → MapUnique (S.savedMap (proj₂ claim))) (claims s)

pending-before-lease-only : LeaseOnly (I.world pendingBefore)
pending-before-lease-only = tt , saved-lease-unique ∷ []
pending-after-not-lease-only : ¬ LeaseOnly (I.world pendingAfter)
pending-after-not-lease-only (current , captured) = duplicate-local-invalid current

no-lease-only-preservation : ¬ (∀ a c {c′} → Sub.advance a c ≡ just c′ →
  LeaseOnly (I.world (O.core (J.cm (Sub.world c)))) →
  LeaseOnly (I.world (O.core (J.cm (Sub.world c′)))))
no-lease-only-preservation preserve = pending-after-not-lease-only
  (preserve (Sub.core (O.inbound (I.cleanupStep child₀ Cleanup.publishCleanupMap)))
    pendingSubsystem publish-step pending-before-lease-only)

-- All initialized subsystem interleavings exclude the injected bad captures.
nonunique-unreachable : ∀ target → ¬ Unique.Valid target → ∀ c s actions →
  Maps.Valid (I.world c) → ¬ Sub.Executes (Sub.initial (O.initial c) s) actions target
nonunique-unreachable target invalid c s actions maps path = invalid (Unique.from-initial maps path)
saved-capture-unreachable : ∀ c s actions → Maps.Valid (I.world c) →
  ¬ Sub.Executes (Sub.initial (O.initial c) s) actions savedSubsystem
saved-capture-unreachable = nonunique-unreachable savedSubsystem saved-certificate-invalid
pending-capture-unreachable : ∀ c s actions → Maps.Valid (I.world c) →
  ¬ Sub.Executes (Sub.initial (O.initial c) s) actions pendingSubsystem
pending-capture-unreachable = nonunique-unreachable pendingSubsystem pending-certificate-invalid
