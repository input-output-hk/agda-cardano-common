{-# OPTIONS --guardedness #-}

-- Logical followup completion removes no owner of a live source frame.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesMonitorFinished
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Store using (lookup; delete)
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.ProductionPolicy as Policy
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesCancellation as Cancellation
import ConnectionManagement.Properties.OwnedFramesFollowDelete as DeleteFacts
import ConnectionManagement.Properties.OwnedFramesContext as ContextFacts
import ConnectionManagement.Properties.OwnedFramesLifts as Lifts
import ConnectionManagement.Properties.OwnedFramesReach as FullReach
open Frames isBearerClosed isIOManagerError
private
  module D = Cancellation isBearerClosed isIOManagerError
  module F = DeleteFacts isBearerClosed isIOManagerError
  module V = ContextFacts isBearerClosed isIOManagerError
  module L = Lifts isBearerClosed isIOManagerError
  module R = FullReach isBearerClosed isIOManagerError

-- The real production adapter exposes the original completed followup row.
governor-finished : ∀ ref s {g′} → GP.step (GP.run (Sub.monitorFinished ref)) (PS.governor s) ≡ just g′ →
  D.Held s → D.Held (record s { governor = g′ })
governor-finished ref s eq (inv , unique , aux) with GP.Production.step (Policy.dispatch (Sub.monitorFinished ref)) (GP.source (PS.governor s)) in dispatched
... | nothing = case eq of λ ()
... | just (Policy.observed c′ stage′) with GP.Production.step-projects (Policy.dispatch (Sub.monitorFinished ref)) (GP.source (PS.governor s)) dispatched
...   | Sub.next advanced Sub.done with lookup ref (Sub.monitors (PS.machine s)) in saved
...     | nothing = case advanced of λ ()
...     | just f with J.pc f in complete
...       | J.complete result = case just-injective advanced of λ { refl → case just-injective eq of λ { refl →
  V.copy-inv (PS.cm s) next-context target-context (F.complete-inv (PS.cm s) (C.capture s) ref f result saved complete inv) , unique ,
  V.copy-aux next-context target-context (F.delete-aux (C.capture s) ref aux) } }
  where
  next-context = F.delete-context (C.capture s) ref
  machine′ = record (PS.machine s) { monitors = delete ref (Sub.monitors (PS.machine s)) }
  target-context = C.capture (record s { governor = GP.supervised (Policy.observed machine′ stage′)
    (GP.pool (PS.governor s)) (GP.regions (PS.governor s)) (GP.unwinding (PS.governor s)) })
governor-finished ref s eq held | just (Policy.observed c′ stage′) | Sub.next advanced Sub.done | just f | J.begin = case advanced of λ ()
governor-finished ref s eq held | just (Policy.observed c′ stage′) | Sub.next advanced Sub.done | just f | J.awaitAcquire = case advanced of λ ()
governor-finished ref s eq held | just (Policy.observed c′ stage′) | Sub.next advanced Sub.done | just f | (J.startBundle t ns) = case advanced of λ ()
governor-finished ref s eq held | just (Policy.observed c′ stage′) | Sub.next advanced Sub.done | just f | (J.publishBundle t) = case advanced of λ ()
governor-finished ref s eq held | just (Policy.observed c′ stage′) | Sub.next advanced Sub.done | just f | J.markWarm = case advanced of λ ()
governor-finished ref s eq held | just (Policy.observed c′ stage′) | Sub.next advanced Sub.done | just f | J.forkMonitor = case advanced of λ ()
governor-finished ref s eq held | just (Policy.observed c′ stage′) | Sub.next advanced Sub.done | just f | J.finishActivation = case advanced of λ ()
governor-finished ref s eq held | just (Policy.observed c′ stage′) | Sub.next advanced Sub.done | just f | J.awaitHot = case advanced of λ ()
governor-finished ref s eq held | just (Policy.observed c′ stage′) | Sub.next advanced Sub.done | just f | J.awaitAll = case advanced of λ ()
governor-finished ref s eq held | just (Policy.observed c′ stage′) | Sub.next advanced Sub.done | just f | J.callRelease = case advanced of λ ()
governor-finished ref s eq held | just (Policy.observed c′ stage′) | Sub.next advanced Sub.done | just f | J.awaitRelease = case advanced of λ ()
governor-finished ref s eq held | just (Policy.observed c′ stage′) | Sub.next advanced Sub.done | just f | J.delayFailure = case advanced of λ ()
governor-finished ref s eq held | just (Policy.observed c′ stage′) | Sub.next advanced Sub.done | just f | (J.awaitCold result) = case advanced of λ ()
governor-finished ref s eq held | just (Policy.observed c′ stage′) | Sub.next advanced Sub.done | just f | (J.acquirePolicy fault) = case advanced of λ ()
governor-finished ref s eq held | just (Policy.observed c′ stage′) | Sub.next advanced Sub.done | just f | (J.nodeDelivery fault) = case advanced of λ ()
governor-finished ref s eq held | just (Policy.observed c′ stage′) | Sub.next advanced Sub.done | just f | (J.nodeRethrow fault) = case advanced of λ ()

-- The PSA and shared adapters keep their original completion permissions.
ps-finished : ∀ ref s {t} → PS.step (PS.run (GP.run (Sub.monitorFinished ref))) s ≡ just t → D.Held s → D.Held t
ps-finished ref s = L.governor-lift (GP.run (Sub.monitorFinished ref)) s (governor-finished ref s) (λ after → refl)
k-finished : ∀ ref s {t} → K.step (K.peerStep (PS.run (GP.run (Sub.monitorFinished ref)))) s ≡ just t → R.Reach s → R.Reach t
k-finished ref = L.peer-lift (PS.run (GP.run (Sub.monitorFinished ref))) (ps-finished ref)
