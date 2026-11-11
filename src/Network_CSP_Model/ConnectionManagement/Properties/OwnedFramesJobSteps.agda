{-# OPTIONS --guardedness #-}

-- Actual jobStep adapters, including physical noteReturn, preserve full Reach.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesJobSteps
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import ConnectionManagement.Store as Store
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.ProductionPolicy as Policy
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesReach as FullReach
import ConnectionManagement.Properties.OwnedFramesCancellation as Cancellation
import ConnectionManagement.Properties.OwnedFramesContext as ContextFacts
import ConnectionManagement.Properties.OwnedFramesJobStep as JobFacts
import ConnectionManagement.Properties.OwnedFramesJobNames as NameFacts
import ConnectionManagement.Properties.OwnedFramesPoolReturn as ReturnFacts
open Frames isBearerClosed isIOManagerError
private
  module R = FullReach isBearerClosed isIOManagerError
  module D = Cancellation isBearerClosed isIOManagerError
  module F = JobFacts isBearerClosed isIOManagerError
  module N = NameFacts isBearerClosed isIOManagerError
  module V = ContextFacts isBearerClosed isIOManagerError
  module B = ReturnFacts isBearerClosed isIOManagerError
  module X = Auxiliary isBearerClosed isIOManagerError

-- Decode the existing Boolean running guard to its exact handle lookup.
running-sound : ∀ j p → GP.running j p ≡ true → Store.lookup j (GP.Pool.handles p) ≡ just GP.Pool.bodyRunning
running-sound j p eq with Store.lookup j (GP.Pool.handles p) in found
... | just GP.Pool.bodyRunning = refl
... | nothing = case eq of λ ()
... | just GP.Pool.bodyUnwinding = case eq of λ ()
... | just (GP.Pool.bodyReturned _) = case eq of λ ()
... | just (GP.Pool.deregisterPending _) = case eq of λ ()
... | just (GP.Pool.deregistered _) = case eq of λ ()
... | just (GP.Pool.resultAvailable _) = case eq of λ ()

-- Production erasure, the logical frame theorem, and physical body return
-- compose without normalizing an entire shared Server transition.
governor-job-step : ∀ j a s {g′} → GP.step (GP.run (Sub.jobStep j a)) (PS.governor s) ≡ just g′ →
  D.Held s → D.Held (record s { governor = g′ })
governor-job-step j a s eq (inv , unique , aux) with GP.running j (GP.pool (PS.governor s)) in running
... | false = case eq of λ ()
... | true with GP.Production.step (Policy.dispatch (Sub.jobStep j a)) (GP.source (PS.governor s)) in dispatched
...   | nothing = case eq of λ ()
...   | just (Policy.observed c′ stage′) with GP.noteReturn (Sub.jobStep j a) c′ (GP.pool (PS.governor s)) in noted
...     | nothing = case eq of λ ()
...     | just p′ with GP.Production.step-projects (Policy.dispatch (Sub.jobStep j a)) (GP.source (PS.governor s)) dispatched
...       | Sub.next advanced Sub.done with Store.lookup j (Sub.jobs (PS.machine s)) in found
...         | nothing = case advanced of λ ()
...         | just jf with Sub.queued jf | J.step a (Sub.execution jf) (Sub.world (PS.machine s)) in stepped
...           | false | just (next , w′) = case just-injective advanced of λ { refl → case just-injective eq of λ { refl →
  V.copy-inv (J.cm w′) after-return target-context (proj₁ (returned noted)) , proj₁ (proj₂ preserved) ,
  V.copy-aux after-return target-context (proj₂ (returned noted)) } }
  where
  preserved = F.job-step-preserves (PS.cm s) (C.capture s) j jf a (J.peers (Sub.world (PS.machine s)))
    found (running-sound j (GP.pool (PS.governor s)) running) stepped inv unique aux
  next-context = N.job-context (C.capture s) (Store.put j (record jf { execution = next }) (Sub.jobs (PS.machine s)))
  machine′ = record (PS.machine s) { world = w′; jobs = Store.put j (record jf { execution = next }) (Sub.jobs (PS.machine s)) }
  returned : GP.noteReturn (Sub.jobStep j a) machine′ (C.governorPool next-context) ≡ just p′ →
    Inv (J.cm w′) (B.pool-context next-context p′) × X.Aux (B.pool-context next-context p′)
  returned note = B.note-return (J.cm w′) next-context j a machine′ refl note (proj₁ preserved) (proj₂ (proj₂ preserved))
  after-return = B.pool-context next-context p′
  target-context = C.capture (record s { governor = GP.supervised (Policy.observed machine′ stage′)
    p′ (GP.regions (PS.governor s)) (GP.unwinding (PS.governor s)) })
...           | true | _ = case advanced of λ ()
...           | false | nothing = case advanced of λ ()

-- The PS permission check remains explicit and cannot create an extra step.
job-step : ∀ j a s {t} → PS.step (PS.run (GP.run (Sub.jobStep j a))) s ≡ just t → D.Held s → D.Held t
job-step j a s stepped held with PS.governorAllowed (GP.run (Sub.jobStep j a)) s
... | false = case stepped of λ ()
... | true with GP.step (GP.run (Sub.jobStep j a)) (PS.governor s) in advanced
...   | nothing = case stepped of λ ()
...   | just g′ = case just-injective stepped of λ { refl → governor-job-step j a s advanced held }

-- This covers the concrete K jobStep constructor for every J.Action label.
k-job-step : ∀ j a s {t} → K.step (K.peerStep (PS.run (GP.run (Sub.jobStep j a)))) s ≡ just t → R.Reach s → R.Reach t
k-job-step j a s stepped held with K.peerOpen s ∧ K.peerAllowed (PS.run (GP.run (Sub.jobStep j a))) s
... | false = case stepped of λ ()
... | true with PS.step (PS.run (GP.run (Sub.jobStep j a))) (K.peers s) in advanced
...   | nothing = case stepped of λ ()
...   | just p = case just-injective stepped of λ { refl → job-step j a (K.peers s) advanced held }
