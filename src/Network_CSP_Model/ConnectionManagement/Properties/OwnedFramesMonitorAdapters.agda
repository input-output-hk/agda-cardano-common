{-# OPTIONS --guardedness #-}

-- Concrete monitor lifecycle adapters at the shared K boundary.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesMonitorAdapters
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import ConnectionManagement.Store using (lookup; put)
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesMonitorLifecycle as Lifecycle
import ConnectionManagement.Properties.OwnedFramesCancellation as Cancellation
import ConnectionManagement.Properties.OwnedFramesLifts as Lifts
import ConnectionManagement.Properties.OwnedFramesReach as FullReach
open Frames isBearerClosed isIOManagerError
private
  module D = Cancellation isBearerClosed isIOManagerError
  module M = Lifecycle isBearerClosed isIOManagerError
  module L = Lifts isBearerClosed isIOManagerError
  module R = FullReach isBearerClosed isIOManagerError

-- Committing the error handler updates a non-observing thread and peer status.
commit-error : ∀ tid s {t} → PS.step (PS.commitMonitorError tid) s ≡ just t → D.Held s → D.Held t
commit-error tid s eq held with lookup tid (PS.monitors s) in saved
... | nothing = case eq of λ ()
... | just old with PS.pc old in phase | lookup (PS.peerRef old) (J.peers (Sub.world (PS.machine s)))
...   | PS.errorWait err | just peer with Peer.demoted (Peer.key peer) (PS.shared s)
...     | false = case eq of λ ()
...     | true = case just-injective eq of λ { refl → M.stopped-write before tid old (PS.errorFinishing err) (PS.monitorPool s) saved
  (λ equal → case trans (sym phase) equal of λ ()) (λ uid apart → refl) (M.peer-rows-held s rows held) }
  where
  rows = put (PS.peerRef old) (record peer { status = Peer.peerCold }) (J.peers (Sub.world (PS.machine s)))
  before = PS.setMachine (record (PS.machine s) { world = record (Sub.world (PS.machine s)) { peers = rows } }) s
commit-error tid s eq held | just t | PS.observing | peer = case eq of λ ()
commit-error tid s eq held | just t | PS.normalFinishing | peer = case eq of λ ()
commit-error tid s eq held | just t | PS.cancelling | peer = case eq of λ ()
commit-error tid s eq held | just t | PS.exited | peer = case eq of λ ()
commit-error tid s eq held | just t | (PS.errorFinishing err) | peer = case eq of λ ()
commit-error tid s eq held | just t | PS.errorWait err | nothing = case eq of λ ()

-- Each K theorem retains the real shared peer permissions.
k-register-monitor : ∀ tid s {t} → K.step (K.peerStep (PS.registerMonitor tid)) s ≡ just t → R.Reach s → R.Reach t
k-register-monitor tid = L.peer-lift (PS.registerMonitor tid) (M.register-monitor tid)
k-commit-error : ∀ tid s {t} → K.step (K.peerStep (PS.commitMonitorError tid)) s ≡ just t → R.Reach s → R.Reach t
k-commit-error tid = L.peer-lift (PS.commitMonitorError tid) (commit-error tid)
k-finish-monitor : ∀ tid s {t} → K.step (K.peerStep (PS.finishMonitor tid)) s ≡ just t → R.Reach s → R.Reach t
k-finish-monitor tid = L.peer-lift (PS.finishMonitor tid) (M.finish-monitor tid)
k-finish-error : ∀ tid s {t} → K.step (K.peerStep (PS.finishMonitorError tid)) s ≡ just t → R.Reach s → R.Reach t
k-finish-error tid = L.peer-lift (PS.finishMonitorError tid) (M.finish-monitor-error tid)
k-monitor-body-unwound : ∀ tid s {t} → K.step (K.peerStep (PS.monitorBodyUnwound tid)) s ≡ just t → R.Reach s → R.Reach t
k-monitor-body-unwound tid = L.peer-lift (PS.monitorBodyUnwound tid) (M.monitor-body-unwound tid)
