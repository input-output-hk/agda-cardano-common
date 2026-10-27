{-# OPTIONS --guardedness #-}

-- Caller detachment preserves the shared CM/IG core. Subsequent cleanup uses
-- an actual acquisition writer; it is not a stutter on the complete machine.
module ConnectionManagement.Properties.CallerCancellation where

open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Inbound
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Properties.StateMapUniqueness as Maps
import ConnectionManagement.Properties.Ownership as Lease
import ConnectionManagement.Properties.OutboundAcquireMapUnique as AcquireMaps
import ConnectionManagement.Properties.OutboundAcquireOwnership as AcquireLease

-- Both shared world and IG/lifecycle configuration survive caller detachment.
-- Acquiring/releasing bookkeeping is intentionally outside this equality.
start-core : ∀ w err context c {f c′} →
  Cancel.start w err context c ≡ just (f , c′) → CM.core c′ ≡ CM.core c
start-core w err Cancel.protectedCleanup c ()
start-core w err Cancel.ordinary c eq with lookup w (CM.acquiring c) | lookup w (CM.releasing c)
... | just active | nothing with Cancel.plan Cancel.ordinary (A.pc active)
...   | nothing = case eq of λ ()
...   | just chosen = case just-injective eq of λ { refl → refl }
start-core w err Cancel.ordinary c eq | nothing | just active =
  case just-injective eq of λ { refl → refl }
start-core w err Cancel.ordinary c eq | nothing | nothing =
  case just-injective eq of λ { refl → refl }
start-core w err Cancel.ordinary c eq | just _ | just _ = case eq of λ ()
start-core w err Cancel.forkedBeforeHandoff c eq with lookup w (CM.acquiring c) | lookup w (CM.releasing c)
... | just active | nothing with Cancel.plan Cancel.forkedBeforeHandoff (A.pc active)
...   | nothing = case eq of λ ()
...   | just chosen = case just-injective eq of λ { refl → refl }
start-core w err Cancel.forkedBeforeHandoff c eq | nothing | nothing = case eq of λ ()
start-core w err Cancel.forkedBeforeHandoff c eq | nothing | just _ = case eq of λ ()
start-core w err Cancel.forkedBeforeHandoff c eq | just _ | just _ = case eq of λ ()
start-core w err Cancel.interruptibleOpen c eq with lookup w (CM.acquiring c) | lookup w (CM.releasing c)
... | just active | nothing with Cancel.plan Cancel.interruptibleOpen (A.pc active)
...   | nothing = case eq of λ ()
...   | just chosen = case just-injective eq of λ { refl → refl }
start-core w err Cancel.interruptibleOpen c eq | nothing | nothing = case eq of λ ()
start-core w err Cancel.interruptibleOpen c eq | nothing | just _ = case eq of λ ()
start-core w err Cancel.interruptibleOpen c eq | just _ | just _ = case eq of λ ()

-- This certificate exposes the exact body-cleanup writer and reconstructed
-- machine. Original caller continuations remain detached throughout cleanup.
record StepWriter (a : Cancel.Action) (f : Cancel.Frame) (c : CM.Configuration)
  (f′ : Cancel.Frame) (c′ : CM.Configuration) : Set where
  constructor writer
  field
    active active′ : A.Frame
    shared′ : S.State
    cleaning-before : Cancel.pc f ≡ Cancel.cleaning active
    source-step : A.step (Cancel.caller f) (Inbound.responder (CM.core c))
      (Cancel.acquireAction a) active (Inbound.world (CM.core c)) ≡ just (active′ , shared′)
    frame-after : f′ ≡ record f { pc = Cancel.after a active′ }
    machine-after : c′ ≡ record c { core = Inbound.replaceWorld (CM.core c) shared′ }

-- The witness is obtained from the successful source computation itself.
step-writer : ∀ a f c {f′ c′} → Cancel.step a f c ≡ just (f′ , c′) → StepWriter a f c f′ c′
step-writer a f c eq with Cancel.pc f in before
... | Cancel.finished _ = case eq of λ ()
... | Cancel.cleaning active with A.step (Cancel.caller f) (Inbound.responder (CM.core c))
    (Cancel.acquireAction a) active (Inbound.world (CM.core c)) in source
...   | nothing = case eq of λ ()
...   | just (active′ , shared′) = case just-injective eq of λ { refl →
  writer active active′ shared′ before source refl refl }

-- Detachment changes neither current/saved maps nor the map-lease census.
start-map-unique : ∀ w err context c {f c′} →
  Cancel.start w err context c ≡ just (f , c′) →
  Maps.Valid (Inbound.world (CM.core c)) → Maps.Valid (Inbound.world (CM.core c′))
start-map-unique w err context c eq valid = subst
  (λ core → Maps.Valid (Inbound.world core)) (sym (start-core w err context c eq)) valid

start-ownership : ∀ w err context c {f c′} →
  Cancel.start w err context c ≡ just (f , c′) →
  Lease.Ownership (Inbound.world (CM.core c)) → Lease.Ownership (Inbound.world (CM.core c′))
start-ownership w err context c eq owned = subst
  (λ core → Lease.Ownership (Inbound.world core)) (sym (start-core w err context c eq)) owned

-- These acquisition writer theorems require no captured-frame validity premise.
-- Reuse them for actual cleanup rather than treating its shared writes as stutter.
step-map-unique : ∀ a f c {f′ c′} → Cancel.step a f c ≡ just (f′ , c′) →
  Maps.Valid (Inbound.world (CM.core c)) → Maps.Valid (Inbound.world (CM.core c′))
step-map-unique a f c eq valid with step-writer a f c eq
... | writer active active′ shared′ before source frameEq machineEq = subst
  (λ out → Maps.Valid (Inbound.world (CM.core out))) (sym machineEq)
  (AcquireMaps.step-preserves (Cancel.caller f) (Inbound.responder (CM.core c))
    (Cancel.acquireAction a) active (Inbound.world (CM.core c)) valid source)

step-ownership : ∀ a f c {f′ c′} → Cancel.step a f c ≡ just (f′ , c′) →
  Lease.Ownership (Inbound.world (CM.core c)) → Lease.Ownership (Inbound.world (CM.core c′))
step-ownership a f c eq owned with step-writer a f c eq
... | writer active active′ shared′ before source frameEq machineEq = subst
  (λ out → Lease.Ownership (Inbound.world (CM.core out))) (sym machineEq)
  (AcquireLease.step-preserves (Cancel.caller f) (Inbound.responder (CM.core c))
    (Cancel.acquireAction a) active (Inbound.world (CM.core c)) owned source)

-- Supply bounds use the separate detached-frame certificate in
-- CallerCancellationCapture and the combined GovernorPoolSupply invariant.
