{-# OPTIONS --guardedness #-}

-- The actual GP/PS/K monitorStep adapters preserve full Reach. Protocol-start
-- permissions and production-policy guards retain their existing meanings.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesMonitorSteps
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import ConnectionManagement.Store as Store
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.ProductionPolicy as Policy
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesReach as FullReach
import ConnectionManagement.Properties.OwnedFramesCancellation as Cancellation
import ConnectionManagement.Properties.OwnedFramesContext as ContextFacts
import ConnectionManagement.Properties.OwnedFramesFollowStep as FollowFacts
open Frames isBearerClosed isIOManagerError
private
  module R = FullReach isBearerClosed isIOManagerError
  module D = Cancellation isBearerClosed isIOManagerError
  module F = FollowFacts isBearerClosed isIOManagerError
  module V = ContextFacts isBearerClosed isIOManagerError

-- Production erasure exposes the actual successful logical followup step;
-- monitor actions leave the governor pool and its detached calls unchanged.
governor-monitor-step : ∀ ref a s {g′} →
  GP.step (GP.run (Sub.monitorStep ref a)) (PS.governor s) ≡ just g′ →
  D.Held s → D.Held (record s { governor = g′ })
governor-monitor-step ref a s eq (inv , unique , aux) with
  GP.Production.step (Policy.dispatch (Sub.monitorStep ref a)) (GP.source (PS.governor s)) in dispatched
... | nothing = case eq of λ ()
... | just (Policy.observed c′ stage′) with
  GP.Production.step-projects (Policy.dispatch (Sub.monitorStep ref a)) (GP.source (PS.governor s)) dispatched
...   | Sub.next advanced Sub.done with Store.lookup ref (Sub.monitors (PS.machine s)) in found
...     | nothing = case advanced of λ ()
...     | just f with J.step a f (Sub.world (PS.machine s)) in stepped
...       | nothing = case advanced of λ ()
...       | just (next , w′) = case just-injective advanced of λ { refl → case just-injective eq of λ { refl →
  V.copy-inv (J.cm w′) next-context target-context (proj₁ preserved) , proj₁ (proj₂ preserved) ,
  V.copy-aux next-context target-context (proj₂ (proj₂ preserved)) } }
  where
  preserved = F.follow-step-preserves (PS.cm s) (C.capture s) ref f a (J.peers (Sub.world (PS.machine s))) found stepped inv unique aux
  next-context = F.follow-context (C.capture s) ref next
  target-context = C.capture (record s { governor = GP.supervised
    (Policy.observed (record (PS.machine s) { world = w′; monitors = Store.put ref next (Sub.monitors (PS.machine s)) }) stage′)
    (GP.pool (PS.governor s)) (GP.regions (PS.governor s)) (GP.unwinding (PS.governor s)) })

-- Every successful PS monitorStep keeps its real permission check.
monitor-step : ∀ ref a s {t} → PS.step (PS.run (GP.run (Sub.monitorStep ref a))) s ≡ just t → D.Held s → D.Held t
monitor-step ref a s stepped held with PS.governorAllowed (GP.run (Sub.monitorStep ref a)) s
... | false = case stepped of λ ()
... | true with GP.step (GP.run (Sub.monitorStep ref a)) (PS.governor s) in advanced
...   | nothing = case stepped of λ ()
...   | just g′ = case just-injective stepped of λ { refl → governor-monitor-step ref a s advanced held }

-- This is the concrete K constructor for all J.Action followup labels.
k-monitor-step : ∀ ref a s {t} → K.step (K.peerStep (PS.run (GP.run (Sub.monitorStep ref a)))) s ≡ just t → R.Reach s → R.Reach t
k-monitor-step ref a s stepped held with K.peerOpen s ∧ K.peerAllowed (PS.run (GP.run (Sub.monitorStep ref a))) s
... | false = case stepped of λ ()
... | true with PS.step (PS.run (GP.run (Sub.monitorStep ref a))) (K.peers s) in advanced
...   | nothing = case stepped of λ ()
...   | just p = case just-injective stepped of λ { refl → monitor-step ref a (K.peers s) advanced held }
