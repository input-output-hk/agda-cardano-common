{-# OPTIONS --guardedness #-}

-- All pool cursor, registry and Async-publication actions covered here preserve
-- running/non-running status; caller cancellation/return have separate proofs.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesPoolActions
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import ConnectionManagement.Rules.AsyncScope as Scope
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesCancellation as Cancellation
import ConnectionManagement.Properties.OwnedFramesPoolTransport as Transport
import ConnectionManagement.Properties.OwnedFramesLifts as Lifts
import ConnectionManagement.Properties.OwnedFramesReach as FullReach
open Frames isBearerClosed isIOManagerError
private
  module D = Cancellation isBearerClosed isIOManagerError
  module P = Transport isBearerClosed isIOManagerError
  module L = Lifts isBearerClosed isIOManagerError
  module R = FullReach isBearerClosed isIOManagerError

-- This selection lists the governor actions that only write its pool.
gov-pool : GP.Action → Bool
gov-pool (GP.beginClose _) = true
gov-pool GP.requestCancel = true
gov-pool GP.join = true
gov-pool GP.finishClose = true
gov-pool (GP.publishAsyncResult _) = true
gov-pool _ = false

-- The actual kernel transition supplies the stable-handle certificate.
governor-pool : ∀ a s {g′} → gov-pool a ≡ true → GP.step a (PS.governor s) ≡ just g′ →
  D.Held s → D.Held (record s { governor = g′ })
governor-pool (GP.beginClose order) s permit eq held with GP.Pool.step (GP.Pool.beginClose order) (GP.pool (PS.governor s)) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → P.gov-held s p′ (P.G.step-stable (GP.Pool.beginClose order) (GP.pool (PS.governor s)) refl advanced) held }
governor-pool GP.requestCancel s permit eq held with GP.Pool.step GP.Pool.requestCancel (GP.pool (PS.governor s)) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → P.gov-held s p′ (P.G.step-stable GP.Pool.requestCancel (GP.pool (PS.governor s)) refl advanced) held }
governor-pool GP.join s permit eq held with GP.Pool.step GP.Pool.join (GP.pool (PS.governor s)) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → P.gov-held s p′ (P.G.step-stable GP.Pool.join (GP.pool (PS.governor s)) refl advanced) held }
governor-pool GP.finishClose s permit eq held with GP.Pool.step GP.Pool.finishClose (GP.pool (PS.governor s)) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → P.gov-held s p′ (P.G.step-stable GP.Pool.finishClose (GP.pool (PS.governor s)) refl advanced) held }
governor-pool (GP.publishAsyncResult j) s permit eq held with GP.Pool.step (GP.Pool.publishAsyncResult j) (GP.pool (PS.governor s)) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → P.gov-held s p′ (P.G.step-stable (GP.Pool.publishAsyncResult j) (GP.pool (PS.governor s)) refl advanced) held }
governor-pool (GP.run action) s () eq held
governor-pool (GP.handoff w) s () eq held
governor-pool (GP.deliverCancellation err) s () eq held
governor-pool (GP.deliverOpenCancellation err) s () eq held
governor-pool (GP.cleanup j action) s () eq held
governor-pool (GP.bodyUnwound j) s () eq held
governor-pool (GP.recoverCloseFailure j) s () eq held
governor-pool (GP.deregisterCancelled j) s () eq held

-- The noteGovernor wrapper is the identity for each selected pool action.
ps-governor-pool : ∀ a s {t} → gov-pool a ≡ true → PS.step (PS.run a) s ≡ just t → D.Held s → D.Held t
ps-governor-pool (GP.beginClose order) s permit = L.governor-lift (GP.beginClose order) s (governor-pool (GP.beginClose order) s refl) (λ after → refl)
ps-governor-pool GP.requestCancel s permit = L.governor-lift GP.requestCancel s (governor-pool GP.requestCancel s refl) (λ after → refl)
ps-governor-pool GP.join s permit = L.governor-lift GP.join s (governor-pool GP.join s refl) (λ after → refl)
ps-governor-pool GP.finishClose s permit = L.governor-lift GP.finishClose s (governor-pool GP.finishClose s refl) (λ after → refl)
ps-governor-pool (GP.publishAsyncResult j) s permit = L.governor-lift (GP.publishAsyncResult j) s (governor-pool (GP.publishAsyncResult j) s refl) (λ after → refl)
ps-governor-pool (GP.run action) s () eq held
ps-governor-pool (GP.handoff w) s () eq held
ps-governor-pool (GP.deliverCancellation err) s () eq held
ps-governor-pool (GP.deliverOpenCancellation err) s () eq held
ps-governor-pool (GP.cleanup j action) s () eq held
ps-governor-pool (GP.bodyUnwound j) s () eq held
ps-governor-pool (GP.recoverCloseFailure j) s () eq held
ps-governor-pool (GP.deregisterCancelled j) s () eq held

-- Every selected governor pool action also preserves the full K predicate.
k-governor-pool : ∀ a s {t} → gov-pool a ≡ true → K.step (K.peerStep (PS.run a)) s ≡ just t → R.Reach s → R.Reach t
k-governor-pool a s permit = L.peer-lift (PS.run a) (λ p → ps-governor-pool a p permit) s

-- The independent monitor pool has the same stable cursor/publication actions.
monitor-pool : PS.Action → Bool
monitor-pool (PS.beginMonitorClose _) = true
monitor-pool PS.requestMonitorCancel = true
monitor-pool PS.joinMonitor = true
monitor-pool PS.finishMonitorClose = true
monitor-pool (PS.deregisterMonitor _) = true
monitor-pool (PS.publishMonitorResult _) = true
monitor-pool _ = false

-- Source tables and thread rows are unchanged by these exact PS writers.
ps-monitor-pool : ∀ a s {t} → monitor-pool a ≡ true → PS.step a s ≡ just t → D.Held s → D.Held t
ps-monitor-pool (PS.beginMonitorClose order) s permit eq held with Scope.closed (PS.scopes s)
... | false = case eq of λ ()
... | true with PS.Pool.step (PS.Pool.beginClose order) (PS.monitorPool s) in advanced
...   | nothing = case eq of λ ()
...   | just p′ = case just-injective eq of λ { refl → P.bg-held s p′ (P.B.step-stable (PS.Pool.beginClose order) (PS.monitorPool s) refl advanced) held }
ps-monitor-pool PS.requestMonitorCancel s permit eq held with PS.Pool.step PS.Pool.requestCancel (PS.monitorPool s) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → P.bg-held s p′ (P.B.step-stable PS.Pool.requestCancel (PS.monitorPool s) refl advanced) held }
ps-monitor-pool PS.joinMonitor s permit eq held with PS.Pool.step PS.Pool.join (PS.monitorPool s) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → P.bg-held s p′ (P.B.step-stable PS.Pool.join (PS.monitorPool s) refl advanced) held }
ps-monitor-pool PS.finishMonitorClose s permit eq held with PS.Pool.step PS.Pool.finishClose (PS.monitorPool s) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → P.bg-held s p′ (P.B.step-stable PS.Pool.finishClose (PS.monitorPool s) refl advanced) held }
ps-monitor-pool (PS.deregisterMonitor j) s permit eq held with PS.Pool.step (PS.Pool.deregister j) (PS.monitorPool s) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → P.bg-held s p′ (P.B.step-stable (PS.Pool.deregister j) (PS.monitorPool s) refl advanced) held }
ps-monitor-pool (PS.publishMonitorResult j) s permit eq held with PS.Pool.step (PS.Pool.publishAsyncResult j) (PS.monitorPool s) in advanced
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → P.bg-held s p′ (P.B.step-stable (PS.Pool.publishAsyncResult j) (PS.monitorPool s) refl advanced) held }
ps-monitor-pool (PS.run action) s () eq held
ps-monitor-pool (PS.forkMonitor j w) s () eq held
ps-monitor-pool (PS.registerMonitor j) s () eq held
ps-monitor-pool (PS.returnEstablishment j) s () eq held
ps-monitor-pool (PS.finishEstablishment j) s () eq held
ps-monitor-pool (PS.monitorException j err) s () eq held
ps-monitor-pool (PS.commitMonitorError j) s () eq held
ps-monitor-pool (PS.finishMonitorError j) s () eq held
ps-monitor-pool (PS.finishMonitor j) s () eq held
ps-monitor-pool (PS.scope action) s () eq held
ps-monitor-pool (PS.deliverMonitorCancellation err) s () eq held
ps-monitor-pool (PS.deliverBlockedMonitorCancellation err) s () eq held
ps-monitor-pool (PS.monitorBodyUnwound j) s () eq held

-- The K wrapper retains its actual peerOpen and peerAllowed checks.
k-monitor-pool : ∀ a s {t} → monitor-pool a ≡ true → K.step (K.peerStep a) s ≡ just t → R.Reach s → R.Reach t
k-monitor-pool a s permit = L.peer-lift a (λ p → ps-monitor-pool a p permit) s
